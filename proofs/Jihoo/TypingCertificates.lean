import Jihoo.GraphCertificates
import Jihoo.CoreBridgeBetaTyping

/-! A proof-producing, executable checker for DATA-only derivation certificates.
No input field contains a proof. Every accepted premise is constructed by a
previous invocation of the checker, and the final claim is closed and bound to
exact roots in the complete graph. This is not a refinement of `Core.infer`. -/
namespace Jihoo.GraphCertificates.Typing
open CoreBridge
open CoreBridge.Raw

instance rawDecidableEq : DecidableEq Raw := fun a b =>
  if h : rawEqual a b = true then isTrue ((rawEqual_iff a b).mp h)
  else isFalse (fun he => h ((rawEqual_iff a b).mpr he))

/-- Newest declaration first. Each annotation is written in the scope BEFORE
its binder; `extend` performs the required weakening at lookup time. -/
def context : List Raw → Raw.Context
  | [] => fun _ => none
  | A :: Γ => (context Γ).extend A

structure Step where
  rule : Nat
  context : List Nat
  subject : Nat
  target : Nat
  premises : List Nat
  deriving DecidableEq, Repr

structure Certificate where
  graph : Graph
  termRoot : Nat
  typeRoot : Nat
  typingStep : Nat
  formationStep : Nat
  steps : List Step
  deriving DecidableEq, Repr

def stepLimit : Nat := 4096

inductive Claim where
  | formation : List Raw → Raw → Claim
  | typing : List Raw → Raw → Raw → Claim
  | conversion : Raw → Raw → Claim
  deriving DecidableEq

def Claim.Valid : Claim → Prop
  | .formation Γ A => Beta.IsType (context Γ) A
  | .typing Γ t A => Beta.HasType (context Γ) t A
  | .conversion A B' => Beta.Conv A B'

/-- This is a checker OUTPUT, never a serialized certificate field. -/
abbrev Checked := { c : Claim // c.Valid }

def Claim.right : Claim → Raw
  | .formation _ A | .typing _ _ A | .conversion _ A => A

private def need (prior : Array Checked) (id : Nat) (goal : Claim) :
    Option (PLift goal.Valid) := do
  let previous ← prior[id]?
  if h : previous.val = goal then
    some ⟨h ▸ previous.property⟩
  else none

/-- Structural cost before capture-avoiding substitution. These conservative
runtime guards are not a claimed complexity theorem about the Lean runtime. -/
def rawSize : Raw → Nat
  | .var _ | .natural _ | .integer _ | .u64 | .i64 => 1
  | .array a | .refl a | .zeroLe a => 1 + rawSize a
  | .lt a b | .eq a b | .pi _ a b | .lam _ a b | .app a b |
      .decide a b | .uadd a b => 1 + rawSize a + rawSize b
  | .index a b c | .usub a b c => 1 + rawSize a + rawSize b + rawSize c
  | .elements xs => 1 + (xs.map rawSize).sum

def rawDepth : Raw → Nat
  | .var _ | .natural _ | .integer _ | .u64 | .i64 => 1
  | .array a | .refl a | .zeroLe a => 1 + rawDepth a
  | .lt a b | .eq a b | .pi _ a b | .lam _ a b | .app a b |
      .decide a b | .uadd a b => 1 + max (rawDepth a) (rawDepth b)
  | .index a b c | .usub a b c => 1 + max (rawDepth a) (max (rawDepth b) (rawDepth c))
  | .elements xs => 1 + (xs.map rawDepth).foldl max 0

def substitutionSafe (body arg : Raw) : Bool :=
  decide (rawSize body * (rawSize arg + 1) ≤ treeLimit ∧
    rawDepth body + rawDepth arg ≤ depthLimit)

private def needElements (prior : Array Checked) (Γ : List Raw) :
    (xs : List Raw) → List Nat → Option (PLift (∀ x ∈ xs, Beta.HasType (context Γ) x .i64))
  | [], [] => some ⟨by simp⟩
  | x :: xs, p :: ps => do
      let hx ← need prior p (.typing Γ x .i64)
      let hxs ← needElements prior Γ xs ps
      pure ⟨by intro y hy; rcases List.mem_cons.mp hy with rfl | hy
               · exact hx.down
               · exact hxs.down y hy⟩
  | _, _ => none

private def needConversions (prior : Array Checked) :
    (xs ys : List Raw) → List Nat → Option (PLift (Beta.ListRel Beta.Conv xs ys))
  | [], [], [] => some ⟨.nil⟩
  | x :: xs, y :: ys, p :: ps => do
      let hxy ← need prior p (.conversion x y)
      let hxs ← needConversions prior xs ys ps
      pure ⟨.cons hxy.down hxs.down⟩
  | _, _, _ => none

/-- All supported rules are explicit. Unrecognized rules, wrong arity, wrong
contexts, forward references and even convertible-but-unequal premises fail. -/
def derive (prior : Array Checked) (goal : Claim) (rule : Nat)
    (premises : List Nat) : Option (PLift goal.Valid) :=
  match goal, rule, premises with
  | .formation _ .u64, 0, [] => some ⟨.u64⟩
  | .formation _ .i64, 1, [] => some ⟨.i64⟩
  | .formation Γ (.array n), 2, [p] => do
      let h ← need prior p (.typing Γ n .u64)
      pure ⟨.array h.down⟩
  | .formation Γ (.lt a b), 3, [p, q] => do
      let ha ← need prior p (.typing Γ a .u64)
      let hb ← need prior q (.typing Γ b .u64)
      pure ⟨.lt ha.down hb.down⟩
  | .formation Γ (.eq a b), 4, [p, q] => do
      let ha ← need prior p (.typing Γ a .u64)
      let hb ← need prior q (.typing Γ b .u64)
      pure ⟨.eq ha.down hb.down⟩
  | .formation Γ (.pi e A B'), 5, [p, q] => do
      if he : e = A.proposition then
        let hA ← need prior p (.formation Γ A)
        let hB ← need prior q (.formation (A :: Γ) B')
        pure ⟨.pi hA.down he hB.down⟩
      else none
  | .typing Γ (.var x) A, 10, [] =>
      if h : context Γ x = some A then some ⟨.var h⟩ else none
  | .typing _ (.natural n) .u64, 11, [] =>
      if h : n < wordBound then some ⟨.natural h⟩ else none
  | .typing _ (.integer n) .i64, 12, [] =>
      if h : -signedBound ≤ n ∧ n < signedBound then some ⟨.integer h.1 h.2⟩ else none
  | .typing Γ (.uadd a b) .u64, 13, [p, q] => do
      let ha ← need prior p (.typing Γ a .u64)
      let hb ← need prior q (.typing Γ b .u64)
      pure ⟨.uadd ha.down hb.down⟩
  | .typing Γ (.usub a b proof) .u64, 14, [p, q, r] => do
      let ha ← need prior p (.typing Γ a .u64)
      let hb ← need prior q (.typing Γ b .u64)
      let hp ← need prior r (.typing Γ proof (.lt b (.uadd a (.natural 1))))
      pure ⟨.usub ha.down hb.down hp.down⟩
  | .typing Γ (.elements xs) A, 15, ps => do
      if he : A = .array (.natural xs.length) then
        if hn : xs.length < wordBound then
          let hs ← needElements prior Γ xs ps
          pure ⟨he ▸ Beta.HasType.elements hs.down hn⟩
        else none
      else none
  | .typing _ (.decide (.natural a) (.natural b)) A, 16, [] =>
      if he : A = .lt (.natural a) (.natural b) then
        if h : a < wordBound ∧ b < wordBound ∧ a < b then
          some ⟨he ▸ Beta.HasType.decide h.1 h.2.1 h.2.2⟩
        else none
      else none
  | .typing Γ (.refl a) A, 17, [p] => do
      if he : A = .eq a a then
        let ha ← need prior p (.typing Γ a .u64)
        pure ⟨he ▸ Beta.HasType.refl ha.down⟩
      else none
  | .typing Γ (.index a i proof) .i64, 18, [p, q, r] => do
      let previous ← prior[p]?
      match previous.val.right with
      | .array n =>
          let ha ← need prior p (.typing Γ a (.array n))
          let hi ← need prior q (.typing Γ i .u64)
          let hp ← need prior r (.typing Γ proof (.lt i n))
          pure ⟨.index ha.down hi.down hp.down⟩
      | _ => none
  | .typing Γ (.lam e A body) T, 19, [p, q] => do
      let previous ← prior[q]?
      let B' := previous.val.right
      if he : e = A.proposition then
        if ht : T = .pi e A B' then
          let hA ← need prior p (.formation Γ A)
          let hb ← need prior q (.typing (A :: Γ) body B')
          pure ⟨ht ▸ Beta.HasType.lam hA.down he hb.down⟩
        else none
      else none
  | .typing Γ (.app f a) T, 20, [p, q] => do
      let previous ← prior[p]?
      match previous.val.right with
      | .pi e A B' =>
          if !substitutionSafe B' a then none else do
            if ht : T = B'.subst (single a) then
              let hf ← need prior p (.typing Γ f (.pi e A B'))
              let ha ← need prior q (.typing Γ a A)
              pure ⟨ht ▸ Beta.HasType.app hf.down ha.down⟩
            else none
      | _ => none
  | .typing Γ t A, 21, [p, q] => do
      let previous ← prior[p]?
      let B' := previous.val.right
      let ht ← need prior p (.typing Γ t B')
      let hc ← need prior q (.conversion B' A)
      pure ⟨.convert ht.down hc.down⟩
  | .conversion A B', 30, [] =>
      if h : A = B' then some ⟨h ▸ Beta.Conv.refl A⟩ else none
  | .conversion A B', 31, [p] => do
      let h ← need prior p (.conversion B' A)
      pure ⟨.symm h.down⟩
  | .conversion A C, 32, [p, q] => do
      let previous ← prior[p]?
      let B' := previous.val.right
      let h₁ ← need prior p (.conversion A B')
      let h₂ ← need prior q (.conversion B' C)
      pure ⟨.trans h₁.down h₂.down⟩
  | .conversion (.app (.lam e A body) a) T, 33, [] =>
      if !substitutionSafe body a then none else
      if h : T = body.subst (single a) then
        some ⟨h ▸ Beta.Conv.beta e A body a⟩ else none
  | .conversion (.uadd (.natural a) (.natural b)) T, 34, [] =>
      if h : a + b < wordBound then
        if he : T = .natural (a + b) then some ⟨he ▸ Beta.Conv.add a b h⟩ else none
      else none
  | .conversion (.array a) (.array a'), 35, [p] => do
      let ha ← need prior p (.conversion a a')
      pure ⟨.array ha.down⟩
  | .conversion (.lt a b) (.lt a' b'), 36, [p, q] => do
      let ha ← need prior p (.conversion a a')
      let hb ← need prior q (.conversion b b')
      pure ⟨.lt ha.down hb.down⟩
  | .conversion (.eq a b) (.eq a' b'), 37, [p, q] => do
      let ha ← need prior p (.conversion a a')
      let hb ← need prior q (.conversion b b')
      pure ⟨.eq ha.down hb.down⟩
  | .conversion (.pi e a b) (.pi e' a' b'), 38, [p, q] => do
      if he : e = e' then
        let ha ← need prior p (.conversion a a')
        let hb ← need prior q (.conversion b b')
        pure ⟨he ▸ Beta.Conv.pi ha.down hb.down⟩
      else none
  | .conversion (.lam e a b) (.lam e' a' b'), 39, [p, q] => do
      if he : e = e' then
        let ha ← need prior p (.conversion a a')
        let hb ← need prior q (.conversion b b')
        pure ⟨he ▸ Beta.Conv.lam ha.down hb.down⟩
      else none
  | .conversion (.app a b) (.app a' b'), 40, [p, q] => do
      let ha ← need prior p (.conversion a a')
      let hb ← need prior q (.conversion b b')
      pure ⟨.app ha.down hb.down⟩
  | .conversion (.index a b c) (.index a' b' c'), 42, [p, q, r] => do
      let ha ← need prior p (.conversion a a')
      let hb ← need prior q (.conversion b b')
      let hc ← need prior r (.conversion c c')
      pure ⟨.index ha.down hb.down hc.down⟩
  | .conversion (.refl a) (.refl a'), 43, [p] => do
      let ha ← need prior p (.conversion a a')
      pure ⟨.reflTerm ha.down⟩
  | .conversion (.zeroLe a) (.zeroLe a'), 44, [p] => do
      let ha ← need prior p (.conversion a a')
      pure ⟨.zeroLe ha.down⟩
  | .conversion (.decide a b) (.decide a' b'), 45, [p, q] => do
      let ha ← need prior p (.conversion a a')
      let hb ← need prior q (.conversion b b')
      pure ⟨.decide ha.down hb.down⟩
  | .conversion (.uadd a b) (.uadd a' b'), 46, [p, q] => do
      let ha ← need prior p (.conversion a a')
      let hb ← need prior q (.conversion b b')
      pure ⟨.uadd ha.down hb.down⟩
  | .conversion (.usub a b c) (.usub a' b' c'), 47, [p, q, r] => do
      let ha ← need prior p (.conversion a a')
      let hb ← need prior q (.conversion b b')
      let hc ← need prior r (.conversion c c')
      pure ⟨.usub ha.down hb.down hc.down⟩
  | .conversion (.elements xs) (.elements ys), 41, ps => do
      let h ← needConversions prior xs ys ps
      pure ⟨.elements h.down⟩
  | _, _, _ => none

/-- Only graph-root references occur in external step data. -/
def stepClaim (g : Graph) (s : Step) : Option Claim := do
  let Γ ← traverse (unfoldGraph depthLimit g) s.context
  let t ← unfoldGraph depthLimit g s.subject
  let A ← unfoldGraph depthLimit g s.target
  if s.rule ≤ 5 then
    if s.subject = s.target then some (.formation Γ t) else none
  else if s.rule < 30 then some (.typing Γ t A)
  else if s.context = [] then some (.conversion t A) else none

def checkStep (g : Graph) (prior : Array Checked) (s : Step) : Option Checked := do
  if s.context.length > depthLimit ∨ s.premises.length > stepLimit then none else do
    let goal ← stepClaim g s
    let h ← derive prior goal s.rule s.premises
    pure ⟨goal, h.down⟩

/-- Aggregate expanded-node budget, counting repeated references separately.
This check runs before any root is unfolded. It also covers unused derivations
and repeated telescope entries, not just the two selected output roots.
Every premise occurrence additionally pays for comparing its entire claim. -/
def expansionBudget : Nat := 2000000

private def addRootWork (ms : Array Measure) (used root : Nat) : Option Nat := do
  let m ← ms[root]?
  let total := used + m.size
  if total ≤ expansionBudget then some total else none

private def addStepWork (ms : Array Measure) (used : Nat) (s : Step) : Option Nat := do
  let used ← addRootWork ms used s.subject
  let used ← addRootWork ms used s.target
  s.context.foldlM (addRootWork ms) used

def workSafe (c : Certificate) : Bool := (do
  let ms ← measureGraph c.graph
  let used ← addRootWork ms 0 c.termRoot
  let used ← addRootWork ms used c.typeRoot
  let steps := c.steps.toArray
  c.steps.foldlM (fun (used : Nat) (s : Step) => do
    let used ← addStepWork ms used s
    s.premises.foldlM (fun used premise => do
      let previous ← steps[premise]?
      addStepWork ms used previous) used) used).isSome

/-- This closed result mentions independently decoded roots and the original
judgments. It contains no source/checker typing hypothesis. -/
def Sound (c : Certificate) : Prop :=
  ∃ t A, decode c.graph c.termRoot = some t ∧ decode c.graph c.typeRoot = some A ∧
    Beta.HasType (fun _ => none) t A ∧ Beta.IsType (fun _ => none) A

def check (c : Certificate) : Option (PLift (Sound c)) := do
  if c.steps.length > stepLimit then none else do
    if !c.steps.all (fun s => decide (s.context.length ≤ depthLimit ∧
      s.premises.length ≤ stepLimit)) then none else do
    if !graphValid c.graph || !workSafe c then none else do
    let prior ← c.steps.foldlM (fun prior s => do
      let checked ← checkStep c.graph prior s
      pure (prior.push checked)) #[]
    match ht : decode c.graph c.termRoot, hA : decode c.graph c.typeRoot with
    | some t, some A =>
        let typed ← need prior c.typingStep (.typing [] t A)
        let formed ← need prior c.formationStep (.formation [] A)
        pure ⟨⟨t, A, ht, hA, typed.down, formed.down⟩⟩
    | _, _ => none

def validate (c : Certificate) : Bool := (check c).isSome

theorem validate_sound {c : Certificate} (h : validate c = true) : Sound c := by
  unfold validate at h
  cases hc : check c with
  | none => simp [hc] at h
  | some proof => exact proof.down

theorem validate_exact_roots {c : Certificate} (h : validate c = true) :
    ∃ t A, Represents c.graph c.termRoot t ∧ Represents c.graph c.typeRoot A ∧
      Beta.HasType (fun _ => none) t A ∧ Beta.IsType (fun _ => none) A := by
  obtain ⟨t, A, ht, hA, typed, formed⟩ := validate_sound h
  exact ⟨t, A, decode_sound ht, decode_sound hA, typed, formed⟩

end Jihoo.GraphCertificates.Typing
