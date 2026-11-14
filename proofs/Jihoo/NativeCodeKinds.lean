import Jihoo.NativeEnvironmentCheckerSoundness

/-! Runtime kind certificates are derived from the same normalized annotations
used by the native checker. They are not caller-supplied plainness flags. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds

/-- Semantic type separation is broader than the checker's durable head witness. -/
def PiSeparated (env : Environment) (term : Term) : Prop :=
  ∀ erased domain body, ¬ Conversion.Conv env term (.pi erased domain body)

/-- The only runtime type-family inputs admitted by Core.first_order_kind. -/
inductive Kind where
  | type (level : Nat)
  | index (erased : Bool) (result : Kind)
  deriving Repr, DecidableEq

def Kind.term : Kind → Term
  | .type level => .univ level
  | .index erased rest => .pi erased .u64 rest.term

def Kind.arity : Kind → Nat
  | .type _ => 0
  | .index _ rest => rest.arity + 1

def read : Nat → Term → Option Kind
  | 0 => fun _ => none
  | fuel + 1 => fun term => match term with
      | .univ level => some (.type level)
      | .pi erased .u64 result => (read fuel result).map (Kind.index erased)
      | _ => none

theorem read_sound (h : read fuel term = some kind) : term = kind.term := by
  induction fuel generalizing term kind with
  | zero => simp [read] at h
  | succ fuel ih =>
      simp only [read] at h
      split at h
      · cases h; rfl
      · rename_i erased result
        obtain ⟨rest, found, same⟩ := Option.map_eq_some_iff.mp h
        cases same
        exact congrArg (Term.pi erased .u64) (ih found)
      · contradiction

@[simp] theorem Kind.kindOf (kind : Kind) : Jihoo.NativeKernel.kindOf kind.term = true := by
  induction kind with
  | type => rfl
  | index erased rest ih => exact ih

@[simp] theorem Kind.firstOrder (kind : Kind) : firstOrderKind kind.term = true := by
  induction kind with
  | type => rfl
  | index erased rest ih => exact ih

@[simp] theorem Kind.rename (kind : Kind) (ρ : Nat → Nat) : kind.term.rename ρ = kind.term := by
  induction kind generalizing ρ with
  | type => simp [Kind.term, Term.rename, renameArgs]
  | index erased rest ih => simp [Kind.term, Term.rename, renameArgs, Op.binders, liftRenaming, ih]

@[simp] theorem Kind.subst (kind : Kind) (σ : Nat → Term) : kind.term.subst σ = kind.term := by
  induction kind generalizing σ with
  | type => simp [Kind.term, Term.subst, substArgs]
  | index erased rest ih => simp [Kind.term, Term.subst, substArgs, Op.binders, liftSub, ih]

/-- A checked lookup, not an unrelated kind flag, witnesses an abstract family. -/
def LookupKind (env : Environment) (ctx : Context) (index : Nat) (kind : Kind) : Prop :=
  ∃ binding, lookup ctx index = some binding ∧
    Conversion.Conv env binding.ty kind.term ∧
    HasType env ctx true (.var index) kind.term

/-- Recompute a local kind from the actual lookup annotation and certified
normalizer. Malformed, unknown and higher-order kinds fail explicitly. -/
def lookupKind (fuel : Nat) (env : Environment) (ctx : Context) (index : Nat) : Option Kind := do
  let binding ← lookup ctx index
  let normal ← Conversion.normalize? env fuel binding.ty
  read fuel normal

theorem lookupKind_sound (h : lookupKind fuel env ctx index = some kind) :
    LookupKind env ctx index kind := by
  unfold lookupKind at h
  cases found : lookup ctx index with
  | none => simp [found] at h
  | some binding =>
      simp only [found, Bind.bind, Option.bind] at h
      cases normalized : Conversion.normalize? env fuel binding.ty with
      | none => simp [normalized] at h
      | some normal =>
          simp only [normalized] at h
          have same := read_sound h
          have converted : Conversion.Conv env binding.ty kind.term :=
            same ▸ Conversion.normalize?_sound normalized
          exact ⟨binding, found, converted, .convert (.var found (Or.inl rfl)) converted⟩

/-- A context is admitted by replaying every binder from the empty context.
This rejects forged local annotations before kind or signature lookup. -/
inductive ContextFormed (env : Environment) : Context → Prop where
  | nil : ContextFormed env []
  | cons : ContextFormed env ctx → Binder env ctx erased domain sort →
      ContextFormed env (⟨domain, erased⟩ :: ctx)

def contextOK (fuel : Nat) (env : Environment) : Context → Bool
  | [] => true
  | binding :: rest => contextOK fuel env rest &&
      (Checker.binder fuel env rest binding.erased binding.ty).isSome

theorem contextOK_sound (h : contextOK fuel env ctx = true) : ContextFormed env ctx := by
  induction ctx with
  | nil => exact .nil
  | cons binding rest ih =>
      simp only [contextOK, Bool.and_eq_true] at h
      cases checked : Checker.binder fuel env rest binding.erased binding.ty with
      | none => simp [checked] at h
      | some sort => exact .cons (ih h.1) (Checker.binder_sound checked)

end Jihoo.NativeKernel.Environment.CodeKinds
