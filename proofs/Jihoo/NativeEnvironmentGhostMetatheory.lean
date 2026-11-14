import Jihoo.NativeUnifiedProgram
import Jihoo.NativeEnvironmentBindingAlgebra
import Jihoo.NativeGhostMetatheory
import Jihoo.NativeResourceSyntax
import Jihoo.NativeBackMetatheory

/-! Ghost metatheory for the same unified environment-indexed judgment.
Environment closure is required when moving contexts or substituting variables;
mode promotion alone preserves the existing context and needs no such premise. -/
namespace Jihoo.NativeKernel.Environment

/-- All code derivations may also be read as ghost derivations. -/
theorem HasType.ghost (typed : HasType env ctx mode term type) : HasType env ctx true term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun ctx erased domain sort _ => Binder env ctx erased domain sort)
    (motive_2 := fun ctx _ term type _ => HasType env ctx true term type)
    (motive_3 := fun ctx _ data telescope arguments result _ => Arguments env ctx true data telescope arguments result)
    (motive_4 := fun ctx motive signatures branches _ => Cases env ctx motive signatures branches)
  all_goals intros
  all_goals first
    | solve | apply Binder.intro <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.var <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.univ <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.prop <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.u64 <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.i64 <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.natural <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.integer <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.array <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.lt <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.eq <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.pi <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.lam <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.app <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.uadd <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.usub <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.refl <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.zeroLe <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.decide <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.decideConverted <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.elements <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.index <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.arith <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.strict <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ltAdd <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ltCancel <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ltLe <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.transport <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.refine <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.pack <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.witness <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.proof <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ifLt <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ifEq <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.absurd <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.foldI64 <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.loop <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.global <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ind <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.con <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.propElim <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.buffer <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.alloc <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.store <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.load <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.free <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.refBuffer <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ghostBorrow <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ghostDeref <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.borrowedIndex <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.back <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.give <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.take <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.convert <;> first | assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply Arguments.nil <;> assumption
    | solve | apply Arguments.cons <;> first | assumption | simpa only [Bool.true_or]
    | solve | apply Cases.nil
    | solve | apply Cases.cons <;> assumption

@[simp] theorem renameArgs_ind (family count : Nat) (ρ : Nat → Nat) (offset : Nat) (terms : List Term) :
    renameArgs (.ind family count) ρ offset terms = terms.map (Term.rename ρ) := by
  induction terms generalizing offset with
  | nil => simp only [renameArgs, List.map_nil]
  | cons term rest ih => simp only [renameArgs, Op.binders, liftRenaming, ih, List.map_cons]

@[simp] theorem substArgs_ind (family count : Nat) (σ : Nat → Term) (offset : Nat) (terms : List Term) :
    substArgs (.ind family count) σ offset terms = terms.map (Term.subst σ) := by
  induction terms generalizing offset with
  | nil => simp only [substArgs, List.map_nil]
  | cons term rest ih => simp only [substArgs, Op.binders, liftSub, ih, List.map_cons]

/-- Environment-aware erased-data policy is natural in ambient variables. -/
theorem binderAllowed_renaming (allowed : binderAllowed env erased domain sort) (ρ : Nat → Nat) :
    binderAllowed env erased (domain.rename ρ) sort := by
  rcases allowed with pure | ⟨erased, family, count, indices, entry, found, data, converted⟩
  · exact Or.inl (pureBinderAllowed_renaming pure ρ)
  · exact Or.inr ⟨erased, family, count, indices.map (Term.rename ρ), entry, found, data,
      by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ⟩

theorem binderAllowed_substitution (allowed : binderAllowed env erased domain sort) (substitution : Nat → Term) :
    binderAllowed env erased (domain.subst substitution) sort := by
  rcases allowed with pure | ⟨erased, family, count, indices, entry, found, data, converted⟩
  · exact Or.inl (pureBinderAllowed_substitution pure substitution)
  · exact Or.inr ⟨erased, family, count, indices.map (Term.subst substitution), entry, found, data,
      by simpa [Term.subst, substArgs, Op.binders, liftSub] using converted.substitution substitution⟩

namespace Ghost
abbrev Renaming := Jihoo.NativeKernel.Ghost.Renaming
end Ghost

@[simp] theorem renameArgs_con (family constructor count : Nat) (ρ : Nat → Nat) (offset : Nat) (terms : List Term) :
    renameArgs (.con family constructor count) ρ offset terms = terms.map (Term.rename ρ) := by
  induction terms generalizing offset with
  | nil => simp only [renameArgs, List.map_nil]
  | cons term rest ih => simp only [renameArgs, Op.binders, liftRenaming, ih, List.map_cons]

@[simp] theorem renameArgs_elim (family count : Nat) (ρ : Nat → Nat) (offset : Nat) (terms : List Term) :
    renameArgs (.elim family count) ρ offset terms = terms.map (Term.rename ρ) := by
  induction terms generalizing offset with
  | nil => simp only [renameArgs, List.map_nil]
  | cons term rest ih => simp only [renameArgs, Op.binders, liftRenaming, ih, List.map_cons]

private theorem rename_shift_one (term : Term) (ρ : Nat → Nat) :
    (term.rename Nat.succ).rename (Indexed.liftRenaming ρ) = (term.rename ρ).rename Nat.succ := by
  rw [Term.rename_comp, Term.rename_comp]
  rfl

set_option linter.unusedSimpArgs false in
private theorem renaming_rule (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) :
    ∀ Δ ρ, Ghost.Renaming ctx Δ ρ → HasType env Δ true (term.rename ρ) (type.rename ρ) := by
  apply HasType.rec (t := typed)
    (motive_1 := fun ctx erased domain sort _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ → Binder env Δ erased (domain.rename ρ) sort)
    (motive_2 := fun ctx _ term type _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ → HasType env Δ true (term.rename ρ) (type.rename ρ))
    (motive_3 := fun ctx _ data telescope arguments result _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ →
      Arguments env Δ true data (telescope.rename ρ) (arguments.map (Term.rename ρ)) (result.rename ρ))
    (motive_4 := fun ctx motive signatures branches _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ →
      (∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature) →
      Cases env Δ (motive.rename ρ) signatures (branches.map (Term.rename ρ)))
  all_goals intros
  case intro =>
    rename_i typed allowed ih_typed Δ ρ hρ
    exact .intro (by simpa using ih_typed Δ ρ hρ) (binderAllowed_renaming allowed ρ)
  case var =>
    rename_i hx _ Δ ρ hρ
    simpa only [Term.rename] using HasType.var (hρ _ _ hx) (Or.inl rfl)
  case univ =>
    rename_i bound Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.univ (ctx := Δ) (ghost := true) bound)
  case prop =>
    rename_i Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.prop (ctx := Δ) (ghost := true))
  case u64 =>
    rename_i Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.u64 (ctx := Δ) (ghost := true))
  case i64 =>
    rename_i Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.i64 (ctx := Δ) (ghost := true))
  case natural =>
    rename_i bound Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.natural (ctx := Δ) (ghost := true) bound)
  case integer =>
    rename_i lo hi Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.integer (ctx := Δ) (ghost := true) lo hi)
  case array =>
    rename_i hn ih_hn Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.array (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hn Δ ρ hρ)
  case lt =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.lt (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case eq =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.eq (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case pi =>
    rename_i hA hB ih_hA ih_hB Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.pi (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (by simpa using ih_hB _ _ (hρ.lift _ _))
  case lam =>
    rename_i hA hb ih_hA ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.lam (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (ih_hb _ _ (hρ.lift _ _))
  case app =>
    rename_i ctx mode f e A B a hf ha allowed ih_hf ih_ha Δ ρ hρ
    change HasType env Δ true ((Term.app f a).rename ρ) ((B.subst (single a)).rename ρ)
    rw [Term.rename_instantiate]
    simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
    have hf' : HasType env Δ true (f.rename ρ)
        (.pi e (A.rename ρ) (B.rename (Indexed.liftRenaming ρ))) := by
      simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ih_hf Δ ρ hρ
    have ha' : HasType env Δ (true || e) (a.rename ρ) (A.rename ρ) := by
      simpa using ih_ha Δ ρ hρ
    exact HasType.app hf' ha' (Or.inl rfl)
  case uadd =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.uadd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case usub =>
    rename_i ha hb hp ih_ha ih_hb ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.usub (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case refl =>
    rename_i ha ih_ha Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.refl (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
  case zeroLe =>
    rename_i ha ih_ha Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.zeroLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
  case decide =>
    rename_i ha hb hab Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      (HasType.decide (ctx := Δ) (ghost := true) ha hb hab)
  case decideConverted =>
    rename_i ha hb ca cb hm hn hmn ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.decideConverted (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
        (by simpa [Term.rename, renameArgs] using ca.renaming ρ)
        (by simpa [Term.rename, renameArgs] using cb.renaming ρ) hm hn hmn
  case elements =>
    rename_i n xs Γ mode hn hb hs ih_hs Δ ρ hρ
    have ht := HasType.elements (ctx := Δ) (ghost := true)
      (xs := xs.map (Term.rename ρ)) (n := n) (by simpa using hn) (by simpa using hb)
      (fun y hy => by
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
        simpa [Term.rename,renameArgs] using ih_hs x hx Δ ρ hρ)
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ht
  case index =>
    rename_i ha hi hp ih_ha ih_hi ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.index (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hi Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case arith =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.arith (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case strict =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.strict (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case ltAdd =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltAdd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case ltCancel =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltCancel (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case ltLe =>
    rename_i ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)
  case transport =>
    rename_i hf he hp ih_hf ih_he ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.transport
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hf Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_he Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case refine =>
    rename_i hp ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.refine (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case pack =>
    rename_i hp ha hq ih_hp ih_ha ih_hq Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.pack
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)
  case witness =>
    rename_i hs ih_hs Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.witness (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)
  case proof =>
    rename_i hs ih_hs Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.proof (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)
  case ifLt =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using
      HasType.ifLt (by simpa [Term.rename,renameArgs] using iha Δ ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihb Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using ihy _ _ (hρ.lift _ true))
        (ihn Δ ρ hρ)
  case ifEq =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using
      HasType.ifEq (by simpa [Term.rename,renameArgs] using iha Δ ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihb Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using ihy _ _ (hρ.lift _ true))
        (ihn Δ ρ hρ)
  case absurd =>
    rename_i hT hp allowed ihT ihp Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.absurd (by simpa using ihT Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihp Δ ρ hρ)
        (Or.inl rfl)
  case foldI64 =>
    rename_i hn hi hb allowed ihn ihi ihb Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.foldI64 (by simpa [Term.rename,renameArgs] using ihn Δ ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihi Δ ρ hρ)
        (by simpa only [foldBodyType_rename] using ihb Δ ρ hρ) (Or.inl rfl)
  case loop =>
    rename_i hm motivePolicy hn hi hb bodyPolicy ihm ihn ihi ihb Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.loop
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihm Δ ρ hρ)
        (Or.inl rfl)
        (by simpa [Term.rename,renameArgs] using ihn Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihi Δ ρ hρ)
        (by simpa only [loopBodyType_rename,Bool.true_or] using ihb Δ ρ hρ)
        (Or.inl rfl)
  case back =>
    rename_i formed owned motive allowed iho ihm Δ ρ hρ
    have target := HasType.back (ghost := true)
      (by simpa [Term.rename, renameArgs] using iho Δ ρ hρ) (owned.renaming ρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihm Δ ρ hρ) (Or.inl rfl)
    simpa only [rename_back, Term.rename, renameArgs] using target
  case give =>
    rename_i owner owned motive allowed result iho ihm ihr Δ ρ hρ
    have target := HasType.give (ghost := true)
      (iho Δ ρ hρ) (owned.renaming ρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihm Δ ρ hρ) (Or.inl rfl)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ ρ hρ)
    simpa only [rename_give, rename_back] using target
  case take =>
    rename_i value continuation owner result converted lowered allowed ihv ihk Δ ρ hρ
    have cv := owner.renaming ρ
    have cp := result.renaming (liftRenaming 1 ρ)
    rw [rename_takeResultType] at cp
    have cr := converted.renaming (liftRenaming 2 ρ)
    rw [load_result_rename ρ lowered] at cr
    have target := HasType.take (ghost := true)
      (by simpa only [rename_back] using ihv Δ ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihk Δ ρ hρ)
      cv (by simpa only [rename_takeResultType, liftRenaming] using cp)
      cr (load_result_shifted _) (Or.inl rfl)
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using target
  case convert =>
    rename_i ht hc ih_ht Δ ρ hρ
    exact .convert (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ht Δ ρ hρ) (hc.renaming ρ)
  case global =>
    rename_i found Δ ρ hρ
    have closed := (wellFormed.globals _ _ found).1
    simpa only [Term.rename, renameArgs, closed_rename closed] using
      (HasType.global (ctx := Δ) (ghost := true) found)
  case ind =>
    rename_i family entry count fields ctx mode found arity size typedIndices ih Δ ρ hρ
    have lifted := HasType.ind (ctx := Δ) (ghost := true) (xs := fields.map (Term.rename ρ)) found arity
      (by simpa only [List.length_map] using size)
      (fun index member => by
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        simpa only [Term.rename, renameArgs] using ih old oldMember Δ ρ hρ)
    simpa only [Term.rename, renameArgs_ind, apply_ite, renameArgs] using lifted
  case con =>
    rename_i family entry constructor signature count ctx mode fields arity indices found signatureFound size arguments ih Δ ρ hρ
    have signatureScope := wellFormed.signatures _ _ found signature (List.mem_of_getElem? signatureFound)
    have closed := signatureScope.signatureTerm_scoped family
    have lifted := ih Δ ρ hρ
    have arguments' : Arguments env Δ true entry.declaration.data
        ((signatureTerm family signature).rename (fun x => x + Δ.length))
        (fields.map (Term.rename ρ)) (.node (.ind family arity) (indices.map (Term.rename ρ))) := by
      simpa only [closed_rename closed, Term.rename, renameArgs_ind] using lifted
    have result := HasType.con found signatureFound (by simpa only [List.length_map] using size) arguments'
    simpa only [Term.rename, renameArgs_con, renameArgs_ind] using result
  case propElim =>
    rename_i found isProp motiveTyped casesTyped scrutineeTyped ihm ihc ihs Δ ρ hρ
    have result := HasType.propElim (ghost := true) found isProp
      (by simpa only [propMotiveType_rename] using ihm Δ ρ hρ)
      (ihc Δ ρ hρ (wellFormed.signatures _ _ found))
      (by simpa only [Term.rename, renameArgs_ind] using ihs Δ ρ hρ)
    simpa only [Term.rename, renameArgs_elim, List.map_cons, List.map_append, List.map_singleton, List.map_nil,
      List.length_map, applications_rename] using result
  case buffer =>
    rename_i typed ih Δ ρ hρ
    simpa only [rename_buffer, Term.rename, renameArgs] using HasType.buffer ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case alloc =>
    rename_i count value ihc ihv Δ ρ hρ
    simpa only [rename_alloc, rename_buffer, Term.rename, renameArgs] using HasType.alloc ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihc Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihv Δ ρ hρ))
  case store =>
    rename_i buffer index value proof ihb ihi ihv ihp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.store ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ ρ hρ))
      ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihi Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihv Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ ρ hρ))
  case load =>
    rename_i buffer index proof continuation value owner converted lowered allowed ihb ihi ihp ihk Δ ρ hρ
    have hk := ihk Δ ρ hρ
    have cv := value.renaming ρ
    have co := owner.renaming (Indexed.liftRenaming ρ)
    have cr := converted.renaming (liftRenaming 2 ρ)
    rw [load_result_rename ρ lowered] at cr
    have result := HasType.load (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ ρ hρ)
      (by simpa [Term.rename, renameArgs] using ihi Δ ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using hk)
      (by simpa [Term.rename, renameArgs] using cv)
      (by simpa only [rename_buffer, rename_shift_one] using co)
      cr (load_result_shifted _) (Or.inl rfl)
    simpa only [rename_load] using result
  case free =>
    rename_i buffer rest ihb ihr Δ ρ hρ
    simpa only [rename_free, rename_buffer] using HasType.free ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ ρ hρ))
  case refBuffer =>
    rename_i count ih Δ ρ hρ
    simpa only [rename_ref, rename_buffer, Term.rename, renameArgs] using HasType.refBuffer ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case ghostBorrow =>
    rename_i buffer ih Δ ρ hρ
    simpa only [rename_borrow, rename_ref, rename_buffer] using HasType.ghostBorrow ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case ghostDeref =>
    rename_i reference ih Δ ρ hρ
    simpa only [rename_deref, rename_ref, rename_buffer] using HasType.ghostDeref ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case borrowedIndex =>
    rename_i reference index proof ihr ihi ihp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.borrowedIndex ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ ρ hρ))
      ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihi Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ ρ hρ))
  case nil =>
    rename_i converted Δ ρ hρ
    simpa only [List.map_nil] using Arguments.nil (ctx := Δ) (ghost := true) (converted.renaming ρ)
  case cons =>
    rename_i telescope erased domain rest ctx mode data argument arguments result converted typed argumentsTyped iht iha Δ ρ hρ
    have tail := iha Δ ρ hρ
    change Arguments env Δ true data ((rest.subst (single argument)).rename ρ)
      (arguments.map (Term.rename ρ)) (result.rename ρ) at tail
    rw [Term.rename_instantiate] at tail
    have result := Arguments.cons (env := env) (ctx := Δ) (ghost := true) (data := data) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ)
      (by simpa only [Bool.true_or] using iht Δ ρ hρ)
      tail
    simpa only [List.map_cons] using result
  case nil =>
    exact Cases.nil
  case cons =>
    rename_i typed branches iht ihb Δ ρ hρ scopes
    have branch := iht Δ ρ hρ
    rw [propCaseType_rename (scopes _ (by simp))] at branch
    exact Cases.cons branch (ihb Δ ρ hρ (fun signature member => scopes signature (by simp [member])))

theorem HasType.ghostRenaming (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) {Δ : Context} {ρ : Nat → Nat}
    (renamed : Ghost.Renaming ctx Δ ρ) : HasType env Δ true (term.rename ρ) (type.rename ρ) :=
  renaming_rule wellFormed typed Δ ρ renamed

theorem HasType.ghostWeaken (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) (domain : Term) (erased : Bool) :
    HasType env (⟨domain, erased⟩ :: ctx) true (term.rename Nat.succ) (type.rename Nat.succ) :=
  typed.ghostRenaming wellFormed (Jihoo.NativeKernel.Ghost.Renaming.shift ctx domain erased)

/-- Binder annotations are transported through the same checked environment. -/
theorem Binder.ghostRenaming (wellFormed : UnifiedProgram.EnvWellFormed env)
    (binding : Binder env ctx erased domain sort) {Δ : Context} {ρ : Nat → Nat}
    (renamed : Ghost.Renaming ctx Δ ρ) : Binder env Δ erased (domain.rename ρ) sort := by
  cases binding with
  | intro formed allowed =>
      exact .intro (by simpa only [SortTag.rename_term] using formed.ghostRenaming wellFormed renamed)
        (binderAllowed_renaming allowed ρ)

@[simp] theorem substArgs_con (family constructor count : Nat) (σ : Nat → Term) (offset : Nat) (terms : List Term) :
    substArgs (.con family constructor count) σ offset terms = terms.map (Term.subst σ) := by
  induction terms generalizing offset with
  | nil => simp only [substArgs, List.map_nil]
  | cons term rest ih => simp only [substArgs, Op.binders, liftSub, ih, List.map_cons]

@[simp] theorem substArgs_elim (family count : Nat) (σ : Nat → Term) (offset : Nat) (terms : List Term) :
    substArgs (.elim family count) σ offset terms = terms.map (Term.subst σ) := by
  induction terms generalizing offset with
  | nil => simp only [substArgs, List.map_nil]
  | cons term rest ih => simp only [substArgs, Op.binders, liftSub, ih, List.map_cons]

private theorem shift_subst_lift (term : Term) (σ : Nat → Term) :
    (term.rename Nat.succ).subst (liftSubOne σ) = (term.subst σ).rename Nat.succ := by
  rw [Term.subst_rename, Term.rename_subst]
  rfl

namespace Ghost
/-- Each substituted variable is independently typed at its transformed
actual lookup annotation. No output term derivation is supplied. -/
def Substitution (env : Environment) (Γ Δ : Context) (σ : Nat → Term) : Prop :=
  ∀ x binding, lookup Γ x = some binding → HasType env Δ true (σ x) (binding.ty.subst σ)

theorem Substitution.lift (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : Substitution env Γ Δ σ) (domain : Term) (erased : Bool) :
    Substitution env (⟨domain, erased⟩ :: Γ) (⟨domain.subst σ, erased⟩ :: Δ) (liftSubOne σ) := by
  intro x binding found
  cases x with
  | zero =>
      simp only [lookup, Option.some.injEq] at found
      cases found
      simp only [liftSubOne, shift_subst_lift]
      exact HasType.var (b := ⟨(domain.subst σ).rename Nat.succ, erased⟩) rfl (Or.inl rfl)
  | succ x =>
      simp only [lookup] at found
      obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst binding
      simpa only [liftSubOne, shift_subst_lift] using
        (typed x original selected).ghostWeaken wellFormed (domain.subst σ) erased
end Ghost

set_option linter.unusedSimpArgs false in
private theorem substitution_rule (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) :
    ∀ Δ σ, Ghost.Substitution env ctx Δ σ → HasType env Δ true (term.subst σ) (type.subst σ) := by
  apply HasType.rec (t := typed)
    (motive_1 := fun ctx erased domain sort _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ → Binder env Δ erased (domain.subst σ) sort)
    (motive_2 := fun ctx _ term type _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ → HasType env Δ true (term.subst σ) (type.subst σ))
    (motive_3 := fun ctx _ data telescope arguments result _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ →
      Arguments env Δ true data (telescope.subst σ) (arguments.map (Term.subst σ)) (result.subst σ))
    (motive_4 := fun ctx motive signatures branches _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ →
      (∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature) →
      Cases env Δ (motive.subst σ) signatures (branches.map (Term.subst σ)))
  all_goals intros
  case intro =>
    rename_i typed allowed ih_typed Δ σ hσ
    exact .intro (by simpa using ih_typed Δ σ hσ) (binderAllowed_substitution allowed σ)
  case var =>
    rename_i hx _ Δ σ hσ
    simpa only [Term.subst] using hσ _ _ hx
  case univ =>
    rename_i bound Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.univ (ctx := Δ) (ghost := true) bound)
  case prop =>
    rename_i Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.prop (ctx := Δ) (ghost := true))
  case u64 =>
    rename_i Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.u64 (ctx := Δ) (ghost := true))
  case i64 =>
    rename_i Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.i64 (ctx := Δ) (ghost := true))
  case natural =>
    rename_i bound Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.natural (ctx := Δ) (ghost := true) bound)
  case integer =>
    rename_i lo hi Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.integer (ctx := Δ) (ghost := true) lo hi)
  case array =>
    rename_i hn ih_hn Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.array (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hn Δ σ hσ)
  case lt =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.lt (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case eq =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.eq (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case pi =>
    rename_i hA hB ih_hA ih_hB Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.pi (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (by simpa using ih_hB _ _ (hσ.lift wellFormed _ _))
  case lam =>
    rename_i hA hb ih_hA ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.lam (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (ih_hb _ _ (hσ.lift wellFormed _ _))
  case app =>
    rename_i ctx mode f e A B a hf ha allowed ih_hf ih_ha Δ σ hσ
    change HasType env Δ true ((Term.app f a).subst σ) ((B.subst (single a)).subst σ)
    rw [Term.subst_instantiate]
    simp only [Term.subst, substArgs, Op.binders, liftSub]
    have hf' : HasType env Δ true (f.subst σ)
        (.pi e (A.subst σ) (B.subst (liftSubOne σ))) := by
      simpa [Term.subst,substArgs,Op.binders,liftSub] using ih_hf Δ σ hσ
    have ha' : HasType env Δ (true || e) (a.subst σ) (A.subst σ) := by
      simpa using ih_ha Δ σ hσ
    exact HasType.app hf' ha' (Or.inl rfl)
  case uadd =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.uadd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case usub =>
    rename_i ha hb hp ih_ha ih_hb ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.usub (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case refl =>
    rename_i ha ih_ha Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.refl (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
  case zeroLe =>
    rename_i ha ih_ha Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.zeroLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
  case decide =>
    rename_i ha hb hab Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      (HasType.decide (ctx := Δ) (ghost := true) ha hb hab)
  case decideConverted =>
    rename_i ha hb ca cb hm hn hmn ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.decideConverted (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
        (by simpa [Term.subst, substArgs] using ca.substitution σ)
        (by simpa [Term.subst, substArgs] using cb.substitution σ) hm hn hmn
  case elements =>
    rename_i n xs Γ mode hn hb hs ih_hs Δ σ hσ
    have ht := HasType.elements (ctx := Δ) (ghost := true)
      (xs := xs.map (Term.subst σ)) (n := n) (by simpa using hn) (by simpa using hb)
      (fun y hy => by
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
        simpa [Term.subst,substArgs] using ih_hs x hx Δ σ hσ)
    simpa [Term.subst,substArgs,Op.binders,liftSub] using ht
  case index =>
    rename_i ha hi hp ih_ha ih_hi ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.index (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hi Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case arith =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.arith (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case strict =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.strict (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case ltAdd =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.ltAdd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case ltCancel =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.ltCancel (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case ltLe =>
    rename_i ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.ltLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)
  case transport =>
    rename_i hf he hp ih_hf ih_he ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.transport
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hf Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_he Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case refine =>
    rename_i hp ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.refine (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case pack =>
    rename_i hp ha hq ih_hp ih_ha ih_hq Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.pack
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)
  case witness =>
    rename_i hs ih_hs Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.witness (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)
  case proof =>
    rename_i hs ih_hs Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.proof (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)
  case ifLt =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using
      HasType.ifLt (by simpa [Term.subst,substArgs] using iha Δ σ hσ)
        (by simpa [Term.subst,substArgs] using ihb Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using ihy _ _ (hσ.lift wellFormed _ true))
        (ihn Δ σ hσ)
  case ifEq =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using
      HasType.ifEq (by simpa [Term.subst,substArgs] using iha Δ σ hσ)
        (by simpa [Term.subst,substArgs] using ihb Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using ihy _ _ (hσ.lift wellFormed _ true))
        (ihn Δ σ hσ)
  case absurd =>
    rename_i hT hp allowed ihT ihp Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub] using
      HasType.absurd (by simpa using ihT Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub] using ihp Δ σ hσ)
        (Or.inl rfl)
  case foldI64 =>
    rename_i hn hi hb allowed ihn ihi ihb Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub] using
      HasType.foldI64 (by simpa [Term.subst,substArgs] using ihn Δ σ hσ)
        (by simpa [Term.subst,substArgs] using ihi Δ σ hσ)
        (by simpa only [foldBodyType_subst] using ihb Δ σ hσ) (Or.inl rfl)
  case loop =>
    rename_i hm motivePolicy hn hi hb bodyPolicy ihm ihn ihi ihb Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub] using
      HasType.loop
        (by simpa [Term.subst,substArgs,Op.binders,liftSub] using ihm Δ σ hσ)
        (Or.inl rfl)
        (by simpa [Term.subst,substArgs] using ihn Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub] using ihi Δ σ hσ)
        (by simpa only [loopBodyType_subst,Bool.true_or] using ihb Δ σ hσ)
        (Or.inl rfl)
  case back =>
    rename_i formed owned motive allowed iho ihm Δ σ hσ
    have target := HasType.back (ghost := true)
      (by simpa [Term.subst, substArgs] using iho Δ σ hσ) (owned.substitution σ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihm Δ σ hσ) (Or.inl rfl)
    simpa only [subst_back, Term.subst, substArgs] using target
  case give =>
    rename_i owner owned motive allowed result iho ihm ihr Δ σ hσ
    have target := HasType.give (ghost := true)
      (iho Δ σ hσ) (owned.substitution σ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihm Δ σ hσ) (Or.inl rfl)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihr Δ σ hσ)
    simpa only [subst_give, subst_back] using target
  case take =>
    rename_i value continuation owner result converted lowered allowed ihv ihk Δ σ hσ
    have cv := owner.substitution σ
    have cp := result.substitution (liftSub 1 σ)
    rw [subst_takeResultType] at cp
    have cr := converted.substitution (liftSub 2 σ)
    rw [load_result_subst σ lowered] at cr
    have target := HasType.take (ghost := true)
      (by simpa only [subst_back] using ihv Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihk Δ σ hσ)
      cv (by simpa only [subst_takeResultType, liftSub] using cp)
      cr (load_result_shifted _) (Or.inl rfl)
    simpa [Term.subst, substArgs, Op.binders, liftSub] using target
  case convert =>
    rename_i ht hc ih_ht Δ σ hσ
    exact .convert (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ht Δ σ hσ) (hc.substitution σ)
  case global =>
    rename_i found Δ σ hσ
    have closed := (wellFormed.globals _ _ found).1
    simpa only [Term.subst, substArgs, closed_rename closed, closed_subst closed] using
      (HasType.global (ctx := Δ) (ghost := true) found)
  case ind =>
    rename_i family entry count fields ctx mode found arity size typedIndices ih Δ σ hσ
    have lifted := HasType.ind (ctx := Δ) (ghost := true) (xs := fields.map (Term.subst σ)) found arity
      (by simpa only [List.length_map] using size)
      (fun index member => by
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        simpa only [Term.subst, substArgs] using ih old oldMember Δ σ hσ)
    simpa only [Term.subst, substArgs_ind, apply_ite, substArgs] using lifted
  case con =>
    rename_i family entry constructor signature count ctx mode fields arity indices found signatureFound size arguments ih Δ σ hσ
    have signatureScope := wellFormed.signatures _ _ found signature (List.mem_of_getElem? signatureFound)
    have closed := signatureScope.signatureTerm_scoped family
    have lifted := ih Δ σ hσ
    have arguments' : Arguments env Δ true entry.declaration.data
        ((signatureTerm family signature).rename (fun x => x + Δ.length))
        (fields.map (Term.subst σ)) (.node (.ind family arity) (indices.map (Term.subst σ))) := by
      simpa only [closed_rename closed, closed_subst closed, Term.subst, substArgs_ind] using lifted
    have result := HasType.con found signatureFound (by simpa only [List.length_map] using size) arguments'
    simpa only [Term.subst, substArgs_con, substArgs_ind] using result
  case propElim =>
    rename_i found isProp motiveTyped casesTyped scrutineeTyped ihm ihc ihs Δ σ hσ
    have result := HasType.propElim (ghost := true) found isProp
      (by simpa only [propMotiveType_subst] using ihm Δ σ hσ)
      (ihc Δ σ hσ (wellFormed.signatures _ _ found))
      (by simpa only [Term.subst, substArgs_ind] using ihs Δ σ hσ)
    simpa only [Term.subst, substArgs_elim, List.map_cons, List.map_append, List.map_singleton, List.map_nil,
      List.length_map, applications_subst] using result
  case buffer =>
    rename_i typed ih Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.buffer
      (by simpa [Term.subst, substArgs] using ih Δ σ hσ)
  case alloc =>
    rename_i count value ihc ihv Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.alloc
      (by simpa [Term.subst, substArgs] using ihc Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihv Δ σ hσ)
  case store =>
    rename_i buffer index value proof ihb ihi ihv ihp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.store
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihb Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihi Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihv Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihp Δ σ hσ)
  case load =>
    rename_i buffer index proof continuation value owner converted lowered allowed ihb ihi ihp ihk Δ σ hσ
    have hk := ihk Δ σ hσ
    have cv := value.substitution σ
    have co := owner.substitution (liftSubOne σ)
    have cr := converted.substitution (liftSub 2 σ)
    rw [load_result_subst σ lowered] at cr
    have result := HasType.load (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihb Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihi Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihp Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using hk)
      (by simpa [Term.subst, substArgs] using cv)
      (by simpa only [subst_buffer, shift_subst_lift] using co)
      cr (load_result_shifted _) (Or.inl rfl)
    simpa only [subst_load] using result
  case free =>
    rename_i buffer rest ihb ihr Δ σ hσ
    simpa only [subst_free, subst_buffer] using HasType.free
      (by simpa only [subst_buffer] using ihb Δ σ hσ) (ihr Δ σ hσ)
  case refBuffer =>
    rename_i count ih Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.refBuffer
      (by simpa [Term.subst, substArgs] using ih Δ σ hσ)
  case ghostBorrow =>
    rename_i buffer ih Δ σ hσ
    simpa only [subst_borrow, subst_ref, subst_buffer] using HasType.ghostBorrow
      (by simpa only [subst_buffer] using ih Δ σ hσ)
  case ghostDeref =>
    rename_i reference ih Δ σ hσ
    simpa only [subst_deref, subst_ref, subst_buffer] using HasType.ghostDeref
      (by simpa only [subst_ref, subst_buffer] using ih Δ σ hσ)
  case borrowedIndex =>
    rename_i reference index proof ihr ihi ihp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.borrowedIndex
      (by simpa only [subst_ref, subst_buffer] using ihr Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihi Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihp Δ σ hσ)
  case nil =>
    rename_i converted Δ σ hσ
    simpa only [List.map_nil] using Arguments.nil (ctx := Δ) (ghost := true) (converted.substitution σ)
  case cons =>
    rename_i telescope erased domain rest ctx mode data argument arguments result converted typed argumentsTyped iht iha Δ σ hσ
    have tail := iha Δ σ hσ
    change Arguments env Δ true data ((rest.subst (single argument)).subst σ)
      (arguments.map (Term.subst σ)) (result.subst σ) at tail
    rw [Term.subst_instantiate] at tail
    have result := Arguments.cons (env := env) (ctx := Δ) (ghost := true) (data := data)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using converted.substitution σ)
      (by simpa only [Bool.true_or] using iht Δ σ hσ) tail
    simpa only [List.map_cons] using result
  case nil => exact Cases.nil
  case cons =>
    rename_i typed branches iht ihb Δ σ hσ scopes
    have branch := iht Δ σ hσ
    rw [propCaseType_subst (scopes _ (by simp))] at branch
    exact Cases.cons branch (ihb Δ σ hσ (fun signature member => scopes signature (by simp [member])))

theorem HasType.ghostSubstitution (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) {Δ : Context} {σ : Nat → Term}
    (substituted : Ghost.Substitution env ctx Δ σ) : HasType env Δ true (term.subst σ) (type.subst σ) :=
  substitution_rule wellFormed typed Δ σ substituted

theorem Binder.ghostSubstitution (wellFormed : UnifiedProgram.EnvWellFormed env)
    (binding : Binder env ctx erased domain sort) {Δ : Context} {σ : Nat → Term}
    (substituted : Ghost.Substitution env ctx Δ σ) : Binder env Δ erased (domain.subst σ) sort := by
  cases binding with
  | intro formed allowed =>
      exact .intro (by simpa only [SortTag.subst_term] using formed.ghostSubstitution wellFormed substituted)
        (binderAllowed_substitution allowed σ)

namespace Ghost
theorem Substitution.single (erased : Bool) (typed : HasType env ctx true argument domain) :
    Substitution env (⟨domain, erased⟩ :: ctx) ctx (single argument) := by
  intro x binding found
  cases x with
  | zero =>
      simp only [lookup, Option.some.injEq] at found
      cases found
      simpa only [NativeKernel.single, Term.shift_subst_single] using typed
  | succ x =>
      simp only [lookup] at found
      obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst binding
      simp only [NativeKernel.single, Term.shift_subst_single]
      exact .var selected (Or.inl rfl)
end Ghost

theorem HasType.ghostInstantiate (wellFormed : UnifiedProgram.EnvWellFormed env)
    (bodyTyped : HasType env (⟨domain, erased⟩ :: ctx) mode body result)
    (argumentTyped : HasType env ctx true argument domain) :
    HasType env ctx true (body.subst (single argument)) (result.subst (single argument)) :=
  bodyTyped.ghostSubstitution wellFormed (Ghost.Substitution.single erased argumentTyped)

theorem HasType.checkedGhostSubstitution
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term type) (substituted : Ghost.Substitution env ctx Δ σ) :
    HasType env Δ true (term.subst σ) (type.subst σ) := typed.ghostSubstitution history.wellFormed substituted

end Jihoo.NativeKernel.Environment
