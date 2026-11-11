import Jihoo.SizedMirLinearCompiler

/-! Static representation typing for the complete compact syntax. These rules
mention neither compilation nor evaluation. They are not ownership typing. -/
namespace Jihoo.SizedMir.Structural
open BoundedMir Linear

inductive NatTyped : List Kind → SizedErasure.NatTerm → Prop where
  | literal : n < wordBound → NatTyped ks (.literal n)
  | var : ks[k]? = some .natural → NatTyped ks (.var k)
  | letE : NatTyped ks a → NatTyped (.natural :: ks) b → NatTyped ks (.letE a b)

inductive ScalarTyped : List Kind → SizedErasure.ScalarTerm → Prop where
  | literal : v < scalarBound → ScalarTyped ks (.literal v)
  | var : ks[k]? = some .scalar → ScalarTyped ks (.var k)

inductive Typed : List Kind → SizedErasure.Term → Kind → Prop where
  | scalar : v < scalarBound → Typed ks (.scalar v) .scalar
  | natural : n < wordBound → Typed ks (.natural n) .natural
  | var : ks[k]? = some kind → Typed ks (.var k) kind
  | allocate : NatTyped ks n → ScalarTyped ks v → Typed ks (.allocate n v) .pointer
  | app : Typed ks a ka → Typed (ka :: ks) b kb → Typed ks (.app a b) kb
  | free : ks[k]? = some .pointer → Typed ks b kind → Typed ks (.free k b) kind
  | lend : ks[k]? = some .pointer → NatTyped (.pointer :: ks) i →
      Typed (.pointer :: .scalar :: ks) b kind → Typed ks (.lend k i b) kind
  | ownedLend : ks[k]? = some .pointer → NatTyped (.pointer :: ks) n →
      NatTyped (.pointer :: ks) i → Typed (.pointer :: .pointer :: ks) b kind →
      Typed ks (.ownedLend k n i b) kind
  | ifLt : NatTyped ks l → NatTyped ks r → Typed ks y kind → Typed ks n kind →
      Typed ks (.ifLt l r y n) kind

theorem Typed.infer (h : Typed ks t kind) : inferKind ks t = some kind := by
  induction h <;> simp_all [inferKind]

private theorem lookup_exists {inputs : List Operand} {ks : List Kind} {k : Nat} {kind : Kind} (same : inputs.length = ks.length)
    (h : ks[k]? = some kind) : ∃ op, inputs[k]? = some op := by
  have bound := (List.getElem?_eq_some_iff.mp h).1
  have hi : k < inputs.length := by omega
  exact ⟨inputs[k], List.getElem?_eq_getElem hi⟩

theorem NatTyped.total (h : NatTyped ks t) (same : inputs.length = ks.length) :
    ∃ op, lowerNat inputs t = some op := by
  induction h generalizing inputs with
  | literal bound => exact ⟨_, by simp [lowerNat, bound]; rfl⟩
  | var lookup => exact lookup_exists same lookup
  | letE _ _ first last =>
    obtain ⟨a, ha⟩ := first same
    obtain ⟨b, hb⟩ := last (inputs := a :: inputs) (by simpa using same)
    exact ⟨b, by simp [lowerNat, ha, hb]⟩

theorem ScalarTyped.total (h : ScalarTyped ks t) (same : inputs.length = ks.length) :
    ∃ op, lowerScalar inputs t = some op := by
  cases h with
  | literal bound => exact ⟨_, by simp [lowerScalar, bound]; rfl⟩
  | var lookup => exact lookup_exists same lookup

/-- Every constructor is covered, including both branches irrespective of the
runtime test. No compiler-success or execution premise occurs. -/
theorem Typed.total (h : Typed ks t kind) (same : inputs.length = ks.length)
    (l b exit : Nat) : ∃ fragment, compile inputs ks l b exit t = some fragment := by
  induction h generalizing inputs l b exit with
  | scalar bound => exact ⟨_, by simp [compile, bound]; rfl⟩
  | natural bound => exact ⟨_, by simp [compile, bound]; rfl⟩
  | var lookup =>
    obtain ⟨op, ho⟩ := lookup_exists same lookup
    exact ⟨_, by simp [compile, ho]; rfl⟩
  | allocate hn hv =>
    obtain ⟨n, hn⟩ := hn.total same
    obtain ⟨v, hv⟩ := hv.total same
    exact ⟨_, by simp [compile, hn, hv]; rfl⟩
  | @app ks arg ak body bk ha hb first last =>
    obtain ⟨a, hc⟩ := first same l b (entry (b + blockCost arg) exit body)
    obtain ⟨z, hz⟩ := last (inputs := a.result :: inputs) (by simpa using same) (l + localCost arg) (b + blockCost arg) exit
    exact ⟨_, by simp [compile, ha.infer, hc, hz]; rfl⟩
  | free lookup _ ih =>
    obtain ⟨owner, ho⟩ := lookup_exists same lookup
    obtain ⟨z, hz⟩ := ih same (l + 1) (b + 1) exit
    exact ⟨_, by simp [compile, ho, hz]; rfl⟩
  | lend lookup hi _ ih =>
    obtain ⟨owner, ho⟩ := lookup_exists same lookup
    obtain ⟨i, hi⟩ := hi.total (inputs := owner :: inputs) (by simpa using same)
    obtain ⟨z, hz⟩ := ih (inputs := owner :: .copy ⟨l + 1, false⟩ :: inputs)
      (by simpa using same) (l + 2) (b + 1) exit
    exact ⟨_, by simp [compile, ho, hi, hz]; rfl⟩
  | ownedLend lookup hn hi _ ih =>
    obtain ⟨owner, ho⟩ := lookup_exists same lookup
    obtain ⟨n, hn⟩ := hn.total (inputs := owner :: inputs) (by simpa using same)
    obtain ⟨i, hi⟩ := hi.total (inputs := owner :: inputs) (by simpa using same)
    obtain ⟨z, hz⟩ := ih (inputs := owner :: .copy ⟨l + 6, false⟩ :: inputs)
      (by simpa using same) (l + 12) (b + 7) exit
    exact ⟨_, by simp [compile, ho, hn, hi, hz]; rfl⟩
  | @ifLt ks lt rt yt kind nt hl hr hy hn yes no =>
    obtain ⟨left, hl⟩ := hl.total same
    obtain ⟨right, hr⟩ := hr.total same
    obtain ⟨y, hyc⟩ := yes same (l + 2) (b + 3) (b + 1)
    obtain ⟨n, hnc⟩ := no same (l + 2 + localCost yt) (b + 3 + blockCost yt) (b + 2)
    exact ⟨_, by simp [compile, hl, hr, hy.infer, hn.infer, hyc, hnc]; rfl⟩

/-- The same derivation yields exact syntactic storage costs. -/
theorem Typed.total_cost (h : Typed ks t kind) (same : inputs.length = ks.length)
    (l b exit : Nat) : ∃ fragment, compile inputs ks l b exit t = some fragment ∧
      fragment.locals.size = localCost t ∧ fragment.blocks.size = blockCost t := by
  obtain ⟨fragment, success⟩ := h.total same l b exit
  exact ⟨fragment, success, (compile_sound success).sizes⟩

end Jihoo.SizedMir.Structural
