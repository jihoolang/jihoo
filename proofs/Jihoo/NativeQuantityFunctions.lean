import Jihoo.NativeQuantityAtoms

/-! Exact shape laws for the same native resource projector. Leading lambdas
form one function telescope; callback opening consumes exactly its promised
front and keeps any returned function behind a closure boundary. -/
namespace Jihoo.NativeKernel.NativeQuantity

open Jihoo.Quantity

/-- Full leading native lambda telescope, including every declared mode. -/
inductive LambdaTelescope : Term → List BinderMode → Term → Prop where
  | stop : lambdaHead t = false → LambdaTelescope t [] t
  | lam : binderMode erased domain = some mode → LambdaTelescope body modes rest →
      LambdaTelescope (.node (.lam erased) [domain, body]) (mode :: modes) rest

theorem LambdaTelescope.head (h : LambdaTelescope t modes body) :
    lambdaHead t = !modes.isEmpty := by
  cases h with
  | stop stopped => exact stopped
  | lam => rfl

/-- This representation adds a closure only when at least one lambda exists. -/
def telescopeControl (modes : List BinderMode) (body : Control) : Control :=
  match modes with
  | [] => body
  | _ :: _ => .closure (.scopes modes body)

/-- The actual projector emits one closure enclosing the complete telescope.
Every lambda consumes one fuel unit, exactly as in the native-tree traversal. -/
theorem LambdaTelescope.project_shape (h : LambdaTelescope t modes body) (fuel : Nat) :
    project (fuel + modes.length) t = (project fuel body).map (telescopeControl modes) := by
  induction h with
  | stop stopped =>
      simp only [List.length_nil, Nat.add_zero]
      cases project fuel _ <;> rfl
  | @lam erased domain mode source modes rest resolved telescope ih =>
      have head := telescope.head
      simp only [List.length_cons, Nat.add_succ, project, List.length_cons, List.length_nil,
        Op.arity,
        List.getElem?_cons_zero, List.getElem?_cons_succ, resolved, bind, pure, Option.bind]
      rw [ih]
      cases modes with
      | nil =>
          simp only [List.isEmpty_nil, Bool.not_true] at head
          cases project fuel rest <;> simp [functionTail, head, telescopeControl, Control.scopes]
      | cons next modes =>
          simp only [List.isEmpty_cons, Bool.not_false] at head
          cases project fuel rest <;> simp [functionTail, head, telescopeControl, unclose, Control.scopes]

/-- Exact callback prefixes consume scopes, then reclose any residual telescope. -/
theorem openScopes_prefix (front suffix : List BinderMode) (body : Control) :
    openScopes front.length (Control.scopes (front ++ suffix) body) =
      some (Control.scopes front (reclose (Control.scopes suffix body))) := by
  induction front with
  | nil => rfl
  | cons mode front ih =>
      change (openScopes front.length (Control.scopes (front ++ suffix) body)).map (Control.scope mode) =
        some (Control.scope mode (Control.scopes front (reclose (Control.scopes suffix body))))
      rw [ih]
      rfl

/-- Opening every argument removes the sole function closure, while a further
returned telescope remains closed. -/
theorem openFunctions_prefix (mode : BinderMode) (front suffix : List BinderMode) (body : Control) :
    openFunctions (front.length + 1)
      (.closure (Control.scopes ((mode :: front) ++ suffix) body)) =
      some (Control.scopes (mode :: front) (reclose (Control.scopes suffix body))) := by
  exact openScopes_prefix (mode :: front) suffix body

/-- Too few declared lambdas retain the original ordinary closure checks. -/
theorem caseBody_insufficient (h : openFunctions count c = none) : caseBody count c = c := by
  simp only [caseBody, h, Option.getD_none]

end Jihoo.NativeKernel.NativeQuantity
