import Jihoo.NativeKindSpine
import Jihoo.NativeQuantity

/-! Candidate binder representations are reconstructed from source contexts.
The distinction between a concrete head and an abstract first-order kind is
retained in the certificate; interpretation soundness is proved separately. -/
namespace Jihoo.NativeKernel.Environment.ContextModes
open Jihoo.Quantity NativeQuantity CodeKinds

def head (env : Environment) (domain : Term) : Option BinderMode :=
  match domain with
  | .univ _ => some .unrestricted
  | .node (.ind family _) _ =>
      (env.families[family]?).map fun entry => if entry.boxed then .linear else .unrestricted
  | _ => binderMode false domain

inductive Resolved (env : Environment) (ctx : Context) : Bool → Term → BinderMode → Prop where
  | erased : Resolved env ctx true domain .erased
  | head : Conversion.normalize? env fuel domain = some normal →
      ContextModes.head env normal = some mode → Resolved env ctx false domain mode
  | abstract : Conversion.normalize? env fuel domain = some normal →
      CodeKinds.Spine env ctx normal (.type level) → Resolved env ctx false domain .unrestricted

def resolve (fuel : Nat) (env : Environment) (ctx : Context) (erased : Bool)
    (domain : Term) : Option BinderMode :=
  if erased then some .erased else do
    let normal ← Conversion.normalize? env fuel domain
    match head env normal with
    | some mode => some mode
    | none => if abstractType fuel env ctx normal then some .unrestricted else none

theorem resolve_sound (h : resolve fuel env ctx erased domain = some mode) :
    Resolved env ctx erased domain mode := by
  unfold resolve at h
  split at h
  · rename_i erasedTrue
    cases erasedTrue
    cases h
    exact .erased
  · have erasedFalse : erased = false := by cases erased <;> simp_all
    subst erased
    cases normalized : Conversion.normalize? env fuel domain with
    | none => simp [normalized] at h
    | some normal =>
        simp only [normalized, Bind.bind, Option.bind] at h
        cases known : head env normal with
        | some knownMode =>
            simp only [known, Option.some.injEq] at h
            cases h
            exact .head normalized known
        | none =>
            simp only [known] at h
            split at h
            · rename_i isAbstract
              cases h
              obtain ⟨level, spine, _⟩ := abstractType_sound isAbstract
              exact .abstract normalized spine
            · contradiction

theorem Resolved.abstract_kind (resolved : Resolved env ctx false domain mode) :
    (∃ normal, Conversion.Conv env domain normal ∧ ContextModes.head env normal = some mode) ∨
    (mode = .unrestricted ∧ ∃ normal level,
      Conversion.Conv env domain normal ∧ CodeKinds.Spine env ctx normal (.type level) ∧
        HasType env ctx true normal (.univ level)) := by
  cases resolved with
  | head normalized known => exact Or.inl ⟨_,Conversion.normalize?_sound normalized,known⟩
  | abstract normalized spine => exact Or.inr ⟨rfl,_,_,Conversion.normalize?_sound normalized,spine,spine.typed⟩

end Jihoo.NativeKernel.Environment.ContextModes
