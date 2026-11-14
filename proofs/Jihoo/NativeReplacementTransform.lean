import Jihoo.NativeTransform

/-! Direct native-style arena substitution and no-removal rewriting. Matched
variables invoke the proved direct graph shift on the replacement reference;
constructor children are processed in order in the growing arena. -/
namespace Jihoo.NativeKernel.NativeTransform

open NativeArena

inductive ReplacementMode where
  | substitute
  | rewrite (target : Nat)
  deriving DecidableEq, Repr

def ReplacementMode.target : ReplacementMode → Nat → Nat
  | .substitute, depth => depth
  | .rewrite target, depth => target + depth

def ReplacementMode.other : ReplacementMode → Nat → Nat → Nat
  | .substitute, depth, x => if depth < x then x - 1 else x
  | .rewrite _, _, x => x

def ReplacementMode.environment : ReplacementMode → Term → Nat → Term
  | .substitute, value => single value
  | .rewrite target, value => PartialRenaming.replaceIndex target value

private theorem liftSub_single_at (value : Term) (depth x : Nat) :
    liftSub depth (single value) x =
      if x = depth then value.rename (fun x => x + depth)
      else .var (if depth < x then x - 1 else x) := by
  induction depth generalizing x with
  | zero =>
      cases x with
      | zero =>
          simp only [liftSub, single, ↓reduceIte, Nat.add_zero]
          exact (Term.rename_id value).symm
      | succ x => simp [liftSub, single]
  | succ depth ih =>
      cases x with
      | zero => simp [liftSub, liftSubOne]
      | succ x =>
          simp only [liftSub, liftSubOne, ih]
          by_cases equal : x = depth
          · subst x
            simp [Term.rename_comp, Nat.add_assoc]
          · by_cases above : depth < x
            · simp [equal, above, show depth + 1 < x + 1 from by omega, Term.rename,
                Nat.sub_add_cancel (show 1 ≤ x from by omega)]
            · simp [equal, above, show ¬depth + 1 < x + 1 from by omega, Term.rename]

theorem replacement_environment_at (mode : ReplacementMode) (value : Term) (depth x : Nat) :
    liftSub depth (mode.environment value) x =
      if x = mode.target depth then value.rename (fun x => x + depth)
      else .var (mode.other depth x) := by
  cases mode with
  | substitute => exact liftSub_single_at value depth x
  | rewrite target =>
      simp only [ReplacementMode.environment, ReplacementMode.target, ReplacementMode.other]
      rw [PartialRenaming.liftSub_replaceIndex]
      rfl

/-- Direct replacement traversal. The matched-variable case shifts the actual
replacement graph reference and never expands a replacement into a tree. -/
def replace : Nat → Nat → Nat → Arena → Nat → Nat → ReplacementMode → Nat → Option Result
  | 0, _, _, _, _, _, _, _ => none
  | _ + 1, 0, _, _, _, _, _, _ => none
  | depth + 1, work + 1, limit, g, root, value, mode, binders => do
      if g.size ≤ limit ∧ mode.target binders < indexLimit then
        let n ← g[root]?
        match n with
        | .var k =>
            if k < indexLimit then
              if k = mode.target binders then shift depth work limit g value (binders : Int) 0
              else
                match mode with
                | .rewrite _ => some ⟨g, root, work⟩
                | .substitute => allocateChecked limit g (.var (mode.other binders k)) work
            else none
        | .node op refs =>
            if refs.length = op.arity then do
              let children ← traverse (fun i arena remaining child =>
                replace depth remaining limit arena child value mode (binders + op.binders i))
                  0 g work refs
              allocateChecked limit children.arena (.node op children.roots) children.remaining
            else none
      else none

def Replaced (g : Arena) (work limit : Nat) (expected : Term) (result : Result) : Prop :=
  Prefix g result.arena ∧ Represents result.arena result.root expected ∧
    VariablesBounded expected ∧ result.remaining < work ∧ result.arena.size ≤ limit

private theorem traverse_replacement_sound {f : Nat → Arena → Nat → Nat → Option Result}
    (step : ∀ offset g work root t result, Represents g root t → Represents g value a →
      f offset g work root = some result →
      Replaced g work limit (t.subst (liftSub (op.binders offset) σ)) result)
    (representation : RepresentsList g refs ts) (argument : Represents g value a)
    (cap : g.size ≤ limit) (success : traverse f offset g work refs = some result) :
    Prefix g result.arena ∧
      RepresentsList result.arena result.roots (substArgs op σ offset ts) ∧
      (∀ u ∈ substArgs op σ offset ts, VariablesBounded u) ∧
      result.remaining ≤ work ∧ result.arena.size ≤ limit := by
  induction refs generalizing g ts offset work result with
  | nil =>
      cases representation
      simp [traverse] at success
      subst result
      exact ⟨Prefix.refl _, by simpa [substArgs] using RepresentsList.nil (g := g),
        by simp [substArgs], Nat.le_refl _, cap⟩
  | cons root refs ih =>
      cases representation with
      | cons hr hrs =>
          cases hh : f offset g work root with
          | none => simp [traverse, hh] at success
          | some head =>
              cases ht : traverse f (offset + 1) head.arena head.remaining refs with
              | none => simp [traverse, hh, ht] at success
              | some tail =>
                  simp [traverse, hh, ht] at success
                  subst result
                  obtain ⟨hp, rep, bounded, remaining, limit'⟩ := step offset g work root _ head hr argument hh
                  obtain ⟨hpt, reps, bounds, rem, lim⟩ := ih (hrs.frame hp) (argument.frame hp) limit' ht
                  refine ⟨hp.trans hpt, ?_, ?_, Nat.le_trans rem (Nat.le_of_lt remaining), lim⟩
                  · simpa only [substArgs] using RepresentsList.cons (rep.frame hpt) reps
                  · simp only [substArgs]
                    intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact bounded
                    · exact bounds x hx

private theorem replacement_list_length (h : RepresentsList g ids ts) : ids.length = ts.length := by
  induction h using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var => trivial
  | node => trivial
  | nil => rfl
  | cons h hs ih ihs => exact congrArg Nat.succ ihs

/-- Direct reference traversal performs capture-avoiding simultaneous
substitution. A matched variable invokes direct arena shifting; the argument's
meaning is transported through every arena extension between siblings. -/
theorem replace_sound (representation : Represents g root t) (argument : Represents g value a)
    (success : replace depth work limit g root value mode binders = some result) :
    Replaced g work limit (t.subst (liftSub binders (mode.environment a))) result := by
  induction depth generalizing work g root t a binders result with
  | zero => simp [replace] at success
  | succ depth ih =>
      cases work with
      | zero => simp [replace] at success
      | succ work =>
          by_cases cap : g.size ≤ limit ∧ mode.target binders < indexLimit
          · cases hn : g[root]? with
            | none => simp [replace, cap, hn] at success
            | some n =>
                cases n with
                | var k =>
                    have et : t = .var k := representation.unique (.var hn)
                    subst t
                    by_cases kb : k < indexLimit
                    · by_cases matched : k = mode.target binders
                      · have shifted : shift depth work limit g value (binders : Int) 0 = some result := by
                          simpa [replace, cap, hn, kb, matched] using success
                        obtain ⟨u, hu, hp, hr, bounded, remaining, limit'⟩ := shift_sound argument shifted
                        simp [PartialRenaming.shift] at hu
                        subst u
                        have expected : (Term.var k).subst (liftSub binders (mode.environment a)) =
                            a.rename (fun x => x + binders) := by
                          simp only [Term.subst, replacement_environment_at, matched, ↓reduceIte]
                        rw [expected]
                        exact ⟨hp, hr, bounded, Nat.lt_trans remaining (Nat.lt_succ_self _), limit'⟩
                      · cases mode with
                        | rewrite target =>
                            simp [replace, cap, hn, kb, matched] at success
                            subst result
                            have expected : (Term.var k).subst
                                (liftSub binders ((ReplacementMode.rewrite target).environment a)) = .var k := by
                              simp only [Term.subst, replacement_environment_at,
                                matched, ↓reduceIte, ReplacementMode.other]
                            rw [expected]
                            exact ⟨Prefix.refl _, .var hn, by simpa [VariablesBounded] using kb,
                              Nat.lt_succ_self _, cap.1⟩
                        | substitute =>
                            have allocated : allocateChecked limit g
                                (.var (ReplacementMode.substitute.other binders k)) work = some result := by
                              simpa [replace, cap, hn, kb, matched] using success
                            obtain ⟨hp, limit', lookup, remaining⟩ := allocateChecked_sound allocated
                            have expected : (Term.var k).subst
                                (liftSub binders (ReplacementMode.substitute.environment a)) =
                                  .var (ReplacementMode.substitute.other binders k) := by
                              simp only [Term.subst, replacement_environment_at, matched, ↓reduceIte]
                            have bound : ReplacementMode.substitute.other binders k < indexLimit := by
                              simp only [ReplacementMode.other]
                              split <;> omega
                            rw [expected]
                            exact ⟨hp, .var lookup, by simpa [VariablesBounded] using bound,
                              by rw [remaining]; exact Nat.lt_succ_self _, limit'⟩
                    · simp [replace, cap, hn, kb] at success
                | node op refs =>
                    cases representation with
                    | var lookup => rw [hn] at lookup; cases lookup
                    | node lookup arity represented =>
                        have same := Option.some.inj (hn.symm.trans lookup)
                        cases same
                        let f := fun i arena remaining child =>
                          replace depth remaining limit arena child value mode (binders + op.binders i)
                        cases hc : traverse f 0 g work refs with
                        | none =>
                            dsimp only [f] at hc
                            simp [replace, cap, hn, arity, hc] at success
                        | some children =>
                            dsimp only [f] at hc
                            have allocated : allocateChecked limit children.arena
                                (.node op children.roots) children.remaining = some result := by
                              simpa [replace, cap, hn, arity, hc] using success
                            have step : ∀ offset arena remaining child v output,
                                Represents arena child v → Represents arena value a →
                                f offset arena remaining child = some output →
                                Replaced arena remaining limit
                                  (v.subst (liftSub (op.binders offset)
                                    (liftSub binders (mode.environment a)))) output := by
                              intro offset arena remaining child v output rep arg checked
                              simpa only [PartialRenaming.liftSub_add] using ih rep arg checked
                            obtain ⟨hp, reps, bounded, remaining, _⟩ :=
                              traverse_replacement_sound step represented argument cap.1 hc
                            obtain ⟨hp', limit', lookup', remaining'⟩ := allocateChecked_sound allocated
                            have outArity : children.roots.length = op.arity := by
                              calc
                                children.roots.length = _ := replacement_list_length reps
                                _ = _ := substArgs_length op _ 0 _
                                _ = _ := (replacement_list_length represented).symm
                                _ = _ := arity
                            simp only [Term.subst]
                            exact ⟨hp.trans hp', .node lookup' outArity (reps.frame hp'),
                              by simpa only [VariablesBounded] using bounded,
                              by rw [remaining']; exact Nat.lt_succ_of_le remaining, limit'⟩
          · simp [replace, cap] at success

def substitute (depth work limit : Nat) (g : Arena) (body value : Nat) : Option Result :=
  replace depth work limit g body value .substitute 0

def rewrite (depth work limit : Nat) (g : Arena) (body target value : Nat) : Option Result :=
  replace depth work limit g body value (.rewrite target) 0

theorem substitute_sound (body : Represents g root t) (argument : Represents g value a)
    (success : substitute depth work limit g root value = some result) :
    Replaced g work limit (t.subst (single a)) result := by
  simpa only [ReplacementMode.environment, liftSub] using replace_sound body argument success

theorem rewrite_sound (body : Represents g root t) (argument : Represents g value a)
    (success : rewrite depth work limit g root target value = some result) :
    Replaced g work limit (PartialRenaming.rewrite target a t) result := by
  simpa only [PartialRenaming.rewrite_eq_subst, ReplacementMode.environment, liftSub]
    using replace_sound body argument success

theorem substitute_decodes (body : decode inputFuel g root = some t)
    (argument : decode valueFuel g value = some a)
    (success : substitute depth work limit g root value = some result) :
    ∃ bound, (∀ fuel, bound ≤ fuel →
      decode fuel result.arena result.root = some (t.subst (single a))) ∧
      Prefix g result.arena ∧ VariablesBounded (t.subst (single a)) ∧
      result.remaining < work ∧ result.arena.size ≤ limit := by
  obtain ⟨hp, rep, bounded, remaining, cap⟩ := substitute_sound (decode_sound body) (decode_sound argument) success
  obtain ⟨bound, complete⟩ := rep.decode_complete
  exact ⟨bound, complete, hp, bounded, remaining, cap⟩

theorem rewrite_decodes (body : decode inputFuel g root = some t)
    (argument : decode valueFuel g value = some a)
    (success : rewrite depth work limit g root target value = some result) :
    ∃ bound, (∀ fuel, bound ≤ fuel →
      decode fuel result.arena result.root = some (PartialRenaming.rewrite target a t)) ∧
      Prefix g result.arena ∧ VariablesBounded (PartialRenaming.rewrite target a t) ∧
      result.remaining < work ∧ result.arena.size ≤ limit := by
  obtain ⟨hp, rep, bounded, remaining, cap⟩ := rewrite_sound (decode_sound body) (decode_sound argument) success
  obtain ⟨bound, complete⟩ := rep.decode_complete
  exact ⟨bound, complete, hp, bounded, remaining, cap⟩

theorem substitute_frame (body : Represents g root t) (argument : Represents g value a)
    (success : substitute depth work limit g root value = some result)
    (old : decode oldFuel g oldRoot = some oldTerm) :
    decode oldFuel result.arena oldRoot = some oldTerm := by
  have hp := (substitute_sound body argument success).1
  exact decode_frame_exact old hp

theorem rewrite_frame (body : Represents g root t) (argument : Represents g value a)
    (success : rewrite depth work limit g root target value = some result)
    (old : decode oldFuel g oldRoot = some oldTerm) :
    decode oldFuel result.arena oldRoot = some oldTerm := by
  have hp := (rewrite_sound body argument success).1
  exact decode_frame_exact old hp

theorem substitute_scoped (body : Represents g root t) (argument : Represents g value a)
    (scope : t.Scoped (scopeDepth + 1)) (argumentScope : a.Scoped scopeDepth)
    (success : substitute depth work limit g root value = some result) :
    ∃ u, Represents result.arena result.root u ∧ u.Scoped scopeDepth := by
  exact ⟨_, (substitute_sound body argument success).2.1, scope.instantiate argumentScope⟩

theorem rewrite_scoped (body : Represents g root t) (argument : Represents g value a)
    (scope : t.Scoped scopeDepth) (argumentScope : a.Scoped scopeDepth)
    (success : rewrite depth work limit g root target value = some result) :
    ∃ u, Represents result.arena result.root u ∧ u.Scoped scopeDepth := by
  exact ⟨_, (rewrite_sound body argument success).2.1, PartialRenaming.rewrite_scoped scope argumentScope⟩

@[simp] theorem replace_zero_depth : replace 0 work limit g root value mode binders = none := rfl

@[simp] theorem replace_zero_work : replace depth 0 limit g root value mode binders = none := by
  cases depth <;> rfl

end Jihoo.NativeKernel.NativeTransform
