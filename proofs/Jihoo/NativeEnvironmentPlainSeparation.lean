import Jihoo.NativeEnvironmentTyping
import Jihoo.NativeACUFullConfluence

/-! Representation separation for the actual environment-free ACU theory.
Plainness is transported forward, not assumed invariant under symmetric
conversion. Globals remain rigid here; checked delta is a separate layer. -/
namespace Jihoo.NativeKernel.Environment
set_option linter.unusedSimpArgs false

private theorem relMap (h : Conversion.ListRel R xs ys)
    (f : ∀ a b, R a b → S a b) : Conversion.ListRel S xs ys := by
  induction h with
  | nil => exact .nil
  | cons h hs ih => exact .cons (f _ _ h) ih

private theorem boolEq (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem familyPlainArgs_mono
    (related : Conversion.ListRel (fun a b => familyPlain env a = true → familyPlain env b = true) xs ys)
    (plain : familyPlainArgs env xs = true) : familyPlainArgs env ys = true := by
  induction related with
  | nil => simp only [familyPlainArgs]
  | cons head tail ih =>
    simp only [familyPlainArgs] at plain ⊢
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp plain
    exact Bool.and_eq_true_iff.mpr ⟨head first,ih rest⟩

theorem familyPlain_node_mono
    (related : Conversion.ListRel (fun a b => familyPlain env a = true → familyPlain env b = true) xs ys)
    (plain : familyPlain env (.node op xs) = true) : familyPlain env (.node op ys) = true := by
  cases op with
  | lam erased =>
    cases related with
    | nil => simpa only [familyPlain] using plain
    | cons domain tail => cases tail with
      | nil => simpa only [familyPlain] using plain
      | cons body rest => cases rest with
        | nil => simpa only [familyPlain] using body (by simpa only [familyPlain] using plain)
        | cons _ _ => simpa only [familyPlain] using plain
  | ind family count =>
    simp only [familyPlain] at plain ⊢
    obtain ⟨head,args⟩ := Bool.and_eq_true_iff.mp plain
    exact Bool.and_eq_true_iff.mpr ⟨head,familyPlainArgs_mono related args⟩
  | _ =>
    simp only [familyPlain] at plain ⊢
    first | exact plain | exact familyPlainArgs_mono related plain

theorem familyPlain_node_eq
    (related : Conversion.ListRel (fun a b => familyPlain env a = familyPlain env b) xs ys) :
    familyPlain env (.node op xs) = familyPlain env (.node op ys) := by
  apply boolEq
  constructor
  · exact familyPlain_node_mono (relMap related (fun _ _ h p => h ▸ p))
  · have reverse : Conversion.ListRel (fun b a => familyPlain env b = familyPlain env a) ys xs := by
      induction related with
      | nil => exact .nil
      | cons h hs ih => exact .cons h.symm ih
    exact familyPlain_node_mono (relMap reverse (fun _ _ h p => h ▸ p))

theorem familyPlain_rename (term : Term) (ρ : Nat → Nat) :
    familyPlain env (term.rename ρ) = familyPlain env term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ op offset ρ,
      Conversion.ListRel (fun a b => familyPlain env a = familyPlain env b)
        terms (renameArgs op ρ offset terms)) generalizing ρ with
  | var => simp only [Term.rename,familyPlain]
  | node op args ih => simpa only [Term.rename] using (familyPlain_node_eq (op := op) (ih op 0 ρ)).symm
  | nil => simp only [renameArgs]; exact .nil
  | cons term terms ih iht => simp only [renameArgs]; exact .cons (ih _).symm (iht _ _ _)

private theorem liftSub_plain (n : Nat) (σ : Nat → Term)
    (plain : ∀ x,familyPlain env (σ x) = true) : ∀ x,familyPlain env (liftSub n σ x) = true := by
  induction n with
  | zero => exact plain
  | succ n ih =>
    intro x
    cases x with
    | zero => simp only [liftSub,liftSubOne,familyPlain]
    | succ x => simpa only [liftSub,liftSubOne,familyPlain_rename] using ih x

theorem familyPlain_subst (term : Term) (plain : familyPlain env term = true)
    (σ : Nat → Term) (values : ∀ x,familyPlain env (σ x) = true) :
    familyPlain env (term.subst σ) = true := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ op offset σ,
      (∀ x,familyPlain env (σ x) = true) →
      Conversion.ListRel (fun a b => familyPlain env a = true → familyPlain env b = true)
        terms (substArgs op σ offset terms)) generalizing σ with
  | var x => simpa only [Term.subst] using values x
  | node op args ih => simpa only [Term.subst] using familyPlain_node_mono (ih op 0 σ values) plain
  | nil => simp only [substArgs]; exact .nil
  | cons term terms ih iht =>
    rename_i op offset σ values
    simp only [substArgs]
    exact .cons (fun p => ih p _ (liftSub_plain _ _ values)) (iht op (offset + 1) σ values)

private theorem familyPlainArgs_of_pure (args : List Term)
    (children : ∀ a ∈ args,Jihoo.NativeKernel.plain a = true → familyPlain env a = true)
    (plain : Jihoo.NativeKernel.plainArgs args = true) : familyPlainArgs env args = true := by
  induction args with
  | nil => simp only [familyPlainArgs]
  | cons a args ih =>
    simp only [Jihoo.NativeKernel.plainArgs,familyPlainArgs] at plain ⊢
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp plain
    exact Bool.and_eq_true_iff.mpr ⟨children a (by simp) head,
      ih (fun a member => children a (by simp [member])) tail⟩

theorem familyPlain_of_pure (term : Term) (plain : Jihoo.NativeKernel.plain term = true) :
    familyPlain env term = true := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ t ∈ terms,Jihoo.NativeKernel.plain t = true → familyPlain env t = true) with
  | var => simp only [familyPlain]
  | node op args ih =>
    cases op with
    | lam erased =>
      cases args with
      | nil => simpa only [Jihoo.NativeKernel.plain,familyPlain] using plain
      | cons domain args => cases args with
        | nil => simpa only [Jihoo.NativeKernel.plain,familyPlain] using plain
        | cons body args => cases args with
          | nil => simpa only [familyPlain] using
              (ih body (by simp) (by simpa only [Jihoo.NativeKernel.plain] using plain))
          | cons _ _ => simpa only [Jihoo.NativeKernel.plain,familyPlain] using plain
    | ind family count => simp [Jihoo.NativeKernel.plain] at plain
    | _ =>
      simp only [Jihoo.NativeKernel.plain,familyPlain] at plain ⊢
      first | exact plain | exact familyPlainArgs_of_pure args ih plain
  | nil => rename_i t member _; simp at member
  | cons term terms ih iht =>
    rename_i t member p
    rcases List.mem_cons.mp member with rfl | member
    · exact ih p
    · exact iht t member p

theorem plain_familyPlain (plain : Environment.plain env term = true) : familyPlain env term = true := by
  obtain ⟨_,body⟩ := Bool.and_eq_true_iff.mp plain
  rcases Bool.or_eq_true_iff.mp body with pure | family
  · exact familyPlain_of_pure term pure
  · exact family

theorem familyPlainArgs_all (args : List Term) :
    familyPlainArgs env args = true ↔ ∀ t ∈ args,familyPlain env t = true := by
  induction args with
  | nil => simp [familyPlainArgs]
  | cons a args ih => simp only [familyPlainArgs,Bool.and_eq_true_iff,List.mem_cons,forall_eq_or_imp,ih]

theorem familyPlain_arithmetic (h : ACU.Arithmetic a b) : familyPlain env a = familyPlain env b := by
  induction h using ACU.Arithmetic.rec
    (motive_2 := fun xs ys _ => Conversion.ListRel (fun a b => familyPlain env a = familyPlain env b) xs ys) with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | node op _ ih => exact familyPlain_node_eq ih
  | assoc => simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_assoc]
  | comm => simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.true_and,Bool.and_comm]
  | zero => simp only [familyPlain,familyPlainArgs,Bool.and_true]
  | add => simp only [familyPlain,familyPlainArgs,Bool.and_true]
  | nil => exact .nil
  | cons _ _ ih ik => exact .cons ih ik

theorem familyPlain_arithmetic_forward (h : ACU.Arithmetic a b) (plain : familyPlain env a = true) :
    familyPlain env b = true := by rw [← familyPlain_arithmetic h]; exact plain

theorem familyPlain_sumTerms (terms : List Term) :
    familyPlain env (ACU.sumTerms terms) = true ↔ ∀ t ∈ terms,familyPlain env t = true := by
  induction terms with
  | nil => simp [ACU.sumTerms,familyPlain,familyPlainArgs]
  | cons a terms ih =>
    simp only [ACU.sumTerms,familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff,
      List.mem_cons,forall_eq_or_imp,ih]

theorem familyPlain_arithmeticFlatten (term : Term) :
    familyPlain env term = true ↔ ∀ atom ∈ ACU.arithmeticFlatten term,familyPlain env atom = true := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ t ∈ terms,familyPlain env t = true ↔
      ∀ atom ∈ ACU.arithmeticFlatten t,familyPlain env atom = true) with
  | var => simp only [ACU.arithmeticFlatten,List.mem_singleton,forall_eq]
  | node op args ih =>
    cases op with
    | uadd =>
      cases args with
      | nil => simp only [ACU.arithmeticFlatten,List.mem_singleton,forall_eq]
      | cons a args => cases args with
        | nil => simp only [ACU.arithmeticFlatten,List.mem_singleton,forall_eq]
        | cons b args => cases args with
          | cons _ _ => simp only [ACU.arithmeticFlatten,List.mem_singleton,forall_eq]
          | nil =>
            simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff,
              ACU.arithmeticFlatten,List.mem_append]
            constructor
            · intro pair atom member
              rcases member with left | right
              · exact (ih a (by simp)).mp pair.1 atom left
              · exact (ih b (by simp)).mp pair.2 atom right
            · intro all
              exact ⟨(ih a (by simp)).mpr (fun atom member => all atom (Or.inl member)),
                (ih b (by simp)).mpr (fun atom member => all atom (Or.inr member))⟩
    | natural n =>
      cases args with
      | cons _ _ => simp only [ACU.arithmeticFlatten,List.mem_singleton,forall_eq]
      | nil =>
        by_cases valid : n < AffineSum.wordLimit
        · simp only [familyPlain,familyPlainArgs,ACU.arithmeticFlatten,valid,ite_true,
            List.mem_replicate,true_iff]
          intro atom member
          obtain ⟨_,rfl⟩ := member
          simp only [familyPlain,familyPlainArgs]
        · simp only [ACU.arithmeticFlatten,valid,ite_false,List.mem_singleton,forall_eq]
    | _ => simp only [ACU.arithmeticFlatten,List.mem_singleton,forall_eq]
  | nil => rename_i t member; simp at member
  | cons t ts ih iht =>
    rename_i term member
    rcases List.mem_cons.mp member with rfl | member
    · exact ih
    · exact iht term member

theorem familyPlain_single (plainBody : familyPlain env body = true) (plainArgument : familyPlain env argument = true) :
    familyPlain env (body.subst (single argument)) = true := by
  apply familyPlain_subst body plainBody
  intro x
  cases x with
  | zero => exact plainArgument
  | succ x => simp only [single,familyPlain]

theorem familyPlain_qpar (h : ACU.QPar a b) (plain : familyPlain env a = true) : familyPlain env b = true := by
  induction h using ACU.QPar.rec
    (motive_2 := fun a b _ => familyPlain env a = true → familyPlain env b = true)
    (motive_3 := fun xs ys _ => Conversion.ListRel
      (fun a b => familyPlain env a = true → familyPlain env b = true) xs ys)
    (motive_4 := fun xs ys _ => Conversion.ListRel
      (fun a b => familyPlain env a = true → familyPlain env b = true) xs ys) with
  | intro permutation children output ih =>
    have atoms := (familyPlain_arithmeticFlatten _).mp plain
    have source : familyPlainArgs env _ = true := (familyPlainArgs_all _).mpr
      (fun atom member => atoms atom (permutation.mem_iff.mpr member))
    have target := familyPlainArgs_mono ih source
    have sum := (familyPlain_sumTerms _).mpr ((familyPlainArgs_all _).mp target)
    exact familyPlain_arithmetic_forward output.symm sum
  | var x => simp only [familyPlain]
  | node op children ih => rename_i plain; exact familyPlain_node_mono ih plain
  | beta erased domain body view bodyStep argumentStep bodyIH argumentIH =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at plain
    have lambda := familyPlain_arithmetic_forward view plain.1
    simp only [familyPlain] at lambda
    exact familyPlain_single (bodyIH lambda) (argumentIH plain.2)
  | sub => simp only [familyPlain,familyPlainArgs]
  | read count index proof arrayView indexView children selected ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at plain
    have array := familyPlain_arithmetic_forward arrayView plain.1
    simp only [familyPlain] at array
    have values := familyPlainArgs_mono ih array
    exact (familyPlainArgs_all _).mp values _ (List.mem_of_getElem? selected)
  | witnessPack predicate value proof view valueStep ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true] at plain
    have packed := familyPlain_arithmetic_forward view plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at packed
    exact ih packed.2.1
  | proofPack predicate value proof view proofStep ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true] at plain
    have packed := familyPlain_arithmetic_forward view plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at packed
    exact ih packed.2.2
  | derefBorrow value view valueStep ih | borrowDeref value view valueStep ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true] at plain
    have exposed := familyPlain_arithmetic_forward view plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true] at exposed
    exact ih exposed
  | transportRefl value view proofStep ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at plain
    exact ih plain.2.2
  | ifLtTrue m n no left right bound step ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at plain
    exact familyPlain_single (ih plain.2.2.1) (by simp only [familyPlain,familyPlainArgs,Bool.and_true])
  | ifLtFalse m n yes left right bound step ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at plain
    exact ih plain.2.2.2
  | ifEqTrue n no left right step ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at plain
    exact familyPlain_single (ih plain.2.2.1) (by simp only [familyPlain,familyPlainArgs,Bool.and_true])
  | ifEqFalse m n yes left right bound step ih =>
    rename_i plain
    simp only [familyPlain,familyPlainArgs,Bool.and_true,Bool.and_eq_true_iff] at plain
    exact ih plain.2.2.2
  | nil => exact .nil
  | cons _ _ ih it => exact .cons ih it
  | _ => first | exact .nil | apply Jihoo.NativeKernel.Conversion.ListRel.cons <;> assumption

theorem familyPlain_qstar (h : ACU.QStar a b) (plain : familyPlain env a = true) : familyPlain env b = true := by
  induction h with
  | refl => exact plain
  | cons step rest ih => exact ih (familyPlain_qpar step plain)

/-- A rigid unplain head cannot share a forward reduct with a plain term.
This uses proved full conversion confluence, not symmetric plain invariance. -/
theorem plain_rigid_separate (plain : Environment.plain env term = true)
    (rigid : ACU.fullRigid op = true) (forbidden : ∀ arguments,familyPlain env (.node op arguments) = false) :
    ¬ Conversion.Conv term (.node op arguments) := by
  intro converted
  obtain ⟨common,left,right⟩ := converted.church_rosser_modulo_arithmetic
  have commonPlain := familyPlain_qstar left (plain_familyPlain plain)
  obtain ⟨children,shape,_⟩ := right.rigid_shape rigid (.refl _)
  have headPlain := familyPlain_arithmetic_forward shape commonPlain
  rw [forbidden children] at headPlain
  contradiction

theorem plain_not_buffer (plain : Environment.plain env term = true) : ¬ Conversion.Conv term (.buffer n) :=
  plain_rigid_separate plain rfl (fun _ => by simp only [familyPlain])

theorem plain_not_ref (plain : Environment.plain env term = true) : ¬ Conversion.Conv term (.ref owner) :=
  plain_rigid_separate plain rfl (fun _ => by simp only [familyPlain])

theorem plain_nonFunction (plain : Environment.plain env term = true) : nonFunction term :=
  fun _ _ _ => plain_rigid_separate plain rfl (fun _ => by simp only [familyPlain])

theorem plain_not_back (plain : Environment.plain env term = true) : ¬ Conversion.Conv term (.back erased owner motive) :=
  plain_rigid_separate plain rfl (fun _ => by simp only [familyPlain])

theorem plain_not_boxed_family (plain : Environment.plain env term = true)
    (found : env.families[family]? = some entry) (boxed : entry.boxed = true) :
    ¬ Conversion.Conv term (.node (.ind family count) indices) :=
  plain_rigid_separate plain rfl (fun _ => by
    simp only [familyPlain,found,Option.any_some,boxed,Bool.not_true,Bool.false_and])

end Jihoo.NativeKernel.Environment
