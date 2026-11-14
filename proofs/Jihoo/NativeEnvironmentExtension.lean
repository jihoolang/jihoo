import Jihoo.NativeEnvironmentTyping

/-! Extending a checked prefix preserves every already available lookup and
all unified typing rules. This theorem does not assume external signatures. -/
namespace Jihoo.NativeKernel.Environment

structure Extends (before after : Environment) : Prop where
  globals : ∀ (index : Nat) declaration, before.globals[index]? = some declaration →
    after.globals[index]? = some declaration
  families : ∀ (index : Nat) entry, before.families[index]? = some entry →
    after.families[index]? = some entry

theorem Extends.refl (env : Environment) : Extends env env := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Extends.trans (first : Extends before middle) (second : Extends middle after) :
    Extends before after :=
  ⟨fun i d h => second.globals i d (first.globals i d h),
    fun i e h => second.families i e (first.families i e h)⟩

theorem Extends.pushGlobal (env : Environment) (declaration : GlobalDeclaration) :
    Extends env ⟨env.globals.push declaration, env.families⟩ := by
  constructor
  · intro index existing found
    obtain ⟨inside, value⟩ := Array.getElem?_eq_some_iff.mp found
    rw [Array.getElem?_push_lt inside, value]
  · exact fun _ _ h => h

theorem Extends.pushFamily (env : Environment) (entry : CheckedFamily) :
    Extends env ⟨env.globals, env.families.push entry⟩ := by
  constructor
  · exact fun _ _ h => h
  · intro index existing found
    obtain ⟨inside, value⟩ := Array.getElem?_eq_some_iff.mp found
    rw [Array.getElem?_push_lt inside, value]

theorem dataBinderAllowed.extend (extension : Extends before after)
    (allowed : dataBinderAllowed before domain) : dataBinderAllowed after domain := by
  obtain ⟨family, count, indices, entry, found, data, converted⟩ := allowed
  exact ⟨family, count, indices, entry, extension.families _ _ found, data, converted⟩

theorem binderAllowed.extend (extension : Extends before after)
    (allowed : binderAllowed before erased domain sort) : binderAllowed after erased domain sort := by
  rcases allowed with old | ⟨erased, data⟩
  · exact Or.inl old
  · exact Or.inr ⟨erased, data.extend extension⟩

theorem Owned.extend (extension : Extends before after) (owned : Owned before term) : Owned after term := by
  cases owned with
  | buffer converted => exact .buffer converted
  | family found boxed converted => exact .family (extension.families _ _ found) boxed converted

theorem fixedRepresentation.extend (extension : Extends before after)
    (certificate : fixedRepresentation before term = true) : fixedRepresentation after term = true := by
  cases term with
  | var x => exact certificate
  | node op args =>
      cases op <;> try exact certificate
      case ind family count =>
        cases found : before.families[family]? with
        | none => simp [fixedRepresentation,found] at certificate
        | some entry =>
            have boxed : entry.boxed = true := by simpa only [fixedRepresentation,found,Option.any_some] using certificate
            simpa only [fixedRepresentation,extension.families _ _ found,Option.any_some] using boxed
      all_goals
        cases args with
        | nil => exact certificate
        | cons a args => cases args with
          | nil => exact certificate
          | cons b args => cases args <;> exact certificate

theorem BackRepresentation.extend (extension : Extends before after)
    (represented : BackRepresentation before ghost erased motive) : BackRepresentation after ghost erased motive := by
  rcases represented with hg | he | ⟨flag,domain,body,converted,fixed⟩
  · exact Or.inl hg
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr ⟨flag,domain,body,converted,fixedRepresentation.extend extension fixed⟩)

mutual
  theorem familyPlain.extend (extension : Extends before after)
      (plain : familyPlain before term = true) : familyPlain after term = true := by
    cases term with
    | var => simp only [familyPlain]
    | node op args =>
        cases op with
        | ind family count =>
            simp only [familyPlain] at plain ⊢
            obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp plain
            cases found : before.families[family]? with
            | none => simp [found] at head
            | some entry =>
                have same := extension.families _ _ found
                simpa only [familyPlain, same, Option.any_some,
                  familyPlainArgs.extend extension tail, Bool.and_true] using
                  (show Bool.not entry.boxed = true by simpa only [found, Option.any_some] using head)
        | lam erased =>
            cases args with
            | nil => simp [familyPlain] at plain
            | cons annotation rest =>
                cases rest with
                | nil => simp [familyPlain] at plain
                | cons body rest =>
                    cases rest with
                    | nil => simpa only [familyPlain] using
                        familyPlain.extend extension (by simpa only [familyPlain] using plain)
                    | cons _ _ => simp [familyPlain] at plain
        | _ =>
            simp only [familyPlain] at plain ⊢
            first | exact familyPlainArgs.extend extension plain | contradiction
    termination_by sizeOf term

  theorem familyPlainArgs.extend (extension : Extends before after)
      (plain : familyPlainArgs before terms = true) : familyPlainArgs after terms = true := by
    cases terms with
    | nil => simp only [familyPlainArgs]
    | cons term rest =>
        simp only [familyPlainArgs] at plain ⊢
        obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp plain
        exact Bool.and_eq_true_iff.mpr
          ⟨familyPlain.extend extension head, familyPlainArgs.extend extension tail⟩
    termination_by sizeOf terms
end

theorem plain.extend (extension : Extends before after)
    (certificate : plain before term = true) : plain after term = true := by
  obtain ⟨free,certificate⟩ := Bool.and_eq_true_iff.mp certificate
  apply Bool.and_eq_true_iff.mpr
  refine ⟨free,?_⟩
  rcases Bool.or_eq_true_iff.mp certificate with old | family
  · exact Bool.or_eq_true_iff.mpr (Or.inl old)
  · exact Bool.or_eq_true_iff.mpr (Or.inr (familyPlain.extend extension family))

theorem applicationAllowed.extend (extension : Extends before after)
    (allowed : applicationAllowed before ghost domain argument) :
    applicationAllowed after ghost domain argument := by
  rcases allowed with ghost | ⟨free,kind | ⟨firstOrder,normal,converted,certificate⟩⟩
  · exact Or.inl ghost
  · exact Or.inr ⟨free,Or.inl kind⟩
  · exact Or.inr ⟨free,Or.inr ⟨firstOrder,normal,converted,plain.extend extension certificate⟩⟩

mutual
  theorem iterationMemoryFree.extend (extension : Extends before after)
      (free : iterationMemoryFree before term = true) : iterationMemoryFree after term = true := by
    cases term with
    | var => simp only [iterationMemoryFree]
    | node op args =>
        cases op with
        | con family constructor count | elim family count =>
            cases found : before.families[family]? with
            | none => simp [iterationMemoryFree, found] at free
            | some entry =>
                simp only [iterationMemoryFree, found, Bool.and_eq_true] at free
                obtain ⟨unboxed, argsFree⟩ := free
                simp only [iterationMemoryFree, extension.families _ _ found, Bool.and_eq_true]
                exact ⟨unboxed, iterationMemoryFreeArgs.extend extension argsFree⟩
        | _ =>
            simp only [iterationMemoryFree] at free ⊢ <;>
              first | contradiction | exact iterationMemoryFreeArgs.extend extension free
    termination_by sizeOf term

  theorem iterationMemoryFreeArgs.extend (extension : Extends before after)
      (free : iterationMemoryFreeArgs before op offset terms = true) :
      iterationMemoryFreeArgs after op offset terms = true := by
    cases terms with
    | nil => simp only [iterationMemoryFreeArgs]
    | cons term rest =>
        simp only [iterationMemoryFreeArgs, Bool.and_eq_true] at free ⊢
        refine ⟨?_, iterationMemoryFreeArgs.extend extension free.2⟩
        rcases Bool.or_eq_true_iff.mp free.1 with erased | termFree
        · exact Bool.or_eq_true_iff.mpr (Or.inl erased)
        · exact Bool.or_eq_true_iff.mpr (Or.inr (iterationMemoryFree.extend extension termFree))
    termination_by sizeOf terms
end

theorem IterationBodyAllowed.extend (extension : Extends before after)
    (allowed : IterationBodyAllowed before ghost body) : IterationBodyAllowed after ghost body := by
  rcases allowed with ghost | leading | free
  · exact Or.inl ghost
  · exact Or.inr (Or.inl leading)
  · exact Or.inr (Or.inr (iterationMemoryFree.extend extension free))

theorem IterationMotiveAllowed.extend (extension : Extends before after)
    (allowed : IterationMotiveAllowed before ghost proof motive) : IterationMotiveAllowed after ghost proof motive := by
  rcases allowed with ghost | proof | scalar | ⟨flag, domain, body, converted, owned⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr (Or.inl scalar))
  · exact Or.inr (Or.inr (Or.inr ⟨flag, domain, body, converted, owned.extend extension⟩))

/-- Appending declarations cannot invalidate a previously typed native term. -/
theorem HasType.extend (extension : Extends before after)
    (typed : HasType before ctx ghost term type) : HasType after ctx ghost term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun ctx e A s _ => Binder after ctx e A s)
    (motive_2 := fun ctx ghost term type _ => HasType after ctx ghost term type)
    (motive_3 := fun ctx ghost data telescope arguments result _ =>
      Arguments after ctx ghost data telescope arguments result)
    (motive_4 := fun ctx motive signatures branches _ => Cases after ctx motive signatures branches)
    (motive_5 := fun ctx ghost types branches _ => BranchTypes after ctx ghost types branches)
  all_goals intros
  all_goals first
    | solve | apply Binder.intro <;> first | assumption | exact binderAllowed.extend extension (by assumption)
    | solve | apply HasType.var <;> first | assumption
    | solve | apply HasType.univ <;> first | assumption
    | solve | apply HasType.prop <;> first | assumption
    | solve | apply HasType.u64 <;> first | assumption
    | solve | apply HasType.i64 <;> first | assumption
    | solve | apply HasType.natural <;> first | assumption
    | solve | apply HasType.integer <;> first | assumption
    | solve | apply HasType.array <;> first | assumption
    | solve | apply HasType.lt <;> first | assumption
    | solve | apply HasType.eq <;> first | assumption
    | solve | apply HasType.pi <;> first | assumption
    | solve | apply HasType.lam <;> first | assumption
    | solve | apply HasType.app <;> first | assumption | exact applicationAllowed.extend extension (by assumption)
    | solve | apply HasType.uadd <;> first | assumption
    | solve | apply HasType.usub <;> first | assumption
    | solve | apply HasType.refl <;> first | assumption
    | solve | apply HasType.zeroLe <;> first | assumption
    | solve | apply HasType.decide <;> first | assumption
    | solve | apply HasType.decideConverted <;> first | assumption
    | solve | apply HasType.elements <;> first | assumption
    | solve | apply HasType.index <;> first | assumption
    | solve | apply HasType.arith <;> first | assumption
    | solve | apply HasType.strict <;> first | assumption
    | solve | apply HasType.ltAdd <;> first | assumption
    | solve | apply HasType.ltCancel <;> first | assumption
    | solve | apply HasType.ltLe <;> first | assumption
    | solve | apply HasType.transport <;> first | assumption
    | solve | apply HasType.refine <;> first | assumption
    | solve | apply HasType.pack <;> first | assumption
    | solve | apply HasType.witness <;> first | assumption
    | solve | apply HasType.proof <;> first | assumption
    | solve | apply HasType.ifLt <;> first | assumption
    | solve | apply HasType.ifEq <;> first | assumption
    | solve | apply HasType.absurd <;> first | assumption
    | solve | apply HasType.foldI64 <;> first | assumption | exact IterationBodyAllowed.extend extension (by assumption)
    | solve | apply HasType.foldOwned <;> first | assumption | exact Owned.extend extension (by assumption) | exact IterationBodyAllowed.extend extension (by assumption)
    | solve | apply HasType.loop <;> first | assumption | exact IterationMotiveAllowed.extend extension (by assumption) | exact IterationBodyAllowed.extend extension (by assumption)
    | solve | apply HasType.global <;> first | assumption | exact extension.globals _ _ (by assumption)
    | solve | apply HasType.ind <;> first | assumption | exact extension.families _ _ (by assumption)
    | solve | apply HasType.con <;> first | assumption | exact extension.families _ _ (by assumption)
    | solve | apply HasType.propElim <;> first | assumption | exact extension.families _ _ (by assumption)
    | solve | apply HasType.buffer <;> first | assumption
    | solve | apply HasType.alloc <;> first | assumption
    | solve | apply HasType.store <;> first | assumption
    | solve | apply HasType.load <;> first | assumption
    | solve | apply HasType.free <;> first | assumption
    | solve | apply HasType.refBuffer <;> first | assumption
    | solve | apply HasType.ghostBorrow <;> first | assumption
    | solve | apply HasType.ghostDeref <;> first | assumption
    | solve | apply HasType.borrowedIndex <;> first | assumption
    | solve | apply HasType.back <;> first | assumption | exact Owned.extend extension (by assumption) | exact BackRepresentation.extend extension (by assumption)
    | solve | apply HasType.give <;> first | assumption | exact Owned.extend extension (by assumption) | exact BackRepresentation.extend extension (by assumption)
    | solve | apply HasType.take <;> assumption
    | solve | apply HasType.dataElim <;> first | assumption | exact extension.families _ _ (by assumption)
    | solve | apply HasType.drop <;> first | assumption | exact extension.families _ _ (by assumption)
    | solve | apply HasType.refOwned <;> first | assumption | exact Owned.extend extension (by assumption)
    | solve | apply HasType.ghostBorrowOwned <;> first | assumption | exact Owned.extend extension (by assumption)
    | solve | apply HasType.ghostDerefOwned <;> assumption
    | solve | apply HasType.convert <;> first | assumption
    | solve | apply Arguments.nil <;> assumption
    | solve | apply Arguments.cons <;> assumption
    | solve | apply Cases.nil
    | solve | apply Cases.cons <;> assumption
    | solve | apply BranchTypes.nil
    | solve | apply BranchTypes.cons <;> assumption

theorem HasType.pushGlobal (typed : HasType env ctx ghost term type) (declaration : GlobalDeclaration) :
    HasType ⟨env.globals.push declaration, env.families⟩ ctx ghost term type :=
  typed.extend (Extends.pushGlobal env declaration)

theorem HasType.pushFamily (typed : HasType env ctx ghost term type) (entry : CheckedFamily) :
    HasType ⟨env.globals, env.families.push entry⟩ ctx ghost term type :=
  typed.extend (Extends.pushFamily env entry)

theorem Binder.extend (extension : Extends before after)
    (binding : Binder before ctx erased domain sort) : Binder after ctx erased domain sort := by
  cases binding with
  | intro formed allowed => exact .intro (formed.extend extension) (allowed.extend extension)

end Jihoo.NativeKernel.Environment
