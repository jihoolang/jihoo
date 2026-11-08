import Jihoo.QuantityAliases

namespace Jihoo.Quantity.AliasExamples

-- Unrestricted use may differ between branches. Requiring even a defined
-- local demand would incorrectly reject this scope.
def varying : Control := .branch (.use 0) (.seq (.use 0) (.use 0))
example : varying.demand 0 = none := by decide
example : (Control.scope .unrestricted varying).demand 0 = some 0 := by decide
example : (Control.scope .borrowed varying).demand 0 = some 0 := by decide
example : (Control.scope .linear varying).demand 0 = none := by decide
example : (Control.scope .erased varying).demand 0 = none := by decide

-- Every binder shifts outer owner slots, even when its value is erased.
def mixed : Control := .scopes [.unrestricted, .erased, .borrowed, .linear]
  (.seq (.use 0) (.use 4))
example : mixed.demand 0 = some 1 := by decide
example : mixed.demand 1 = some 0 := by decide
example : (Control.scopes [.unrestricted, .erased] (.use 0)).demand 0 = none := by decide
example : (Control.scope .erased (.erased (.use 0))).demand 0 = some 0 := by decide

theorem mixed_run : Finishes mixed [0] :=
  .bind (.bind (.bind (.bind (.seq .use .use))))

theorem mixed_prefix_once (run : Prefix mixed xs) : xs.count 0 ≤ 1 :=
  run.count_le (by decide)

-- Slot 0 is the returned owner and slot 1 is its original name.
def eitherName : Control := .branch (.use 0) (.use 1)
def bothNames : Control := .seq (.use 0) (.use 1)
example : eitherName.demand 0 = none := by decide
example : (Control.alias 0 eitherName).demand 0 = some 1 := by decide
example : (Control.alias 0 bothNames).demand 0 = some 2 := by decide
example : (Control.alias 0 .pure).demand 0 = some 0 := by decide
example : (Control.alias 0 (.closure (.use 0))).demand 0 = none := by decide
example : (Control.alias 0 (.repeat (.use 1))).demand 0 = none := by decide

theorem either_name_once (run : Finishes eitherName xs) :
    (xs.map (openOwner 0)).count 0 = 1 := alias_finished (by decide) run

theorem both_names_twice : Finishes bothNames [0, 1] ∧
    ([0, 1].map (openOwner 0)).count 0 = 2 := ⟨.seq .use .use, by decide⟩

-- Under another binder, the local slot stays local; owner aliases shift.
def belowScope : Control := .scope .unrestricted (.branch (.use 1) (.use 2))
example : (Control.alias 0 belowScope).demand 0 = some 1 := by decide
example : lift (openOwner 0) 0 = 0 := rfl
example : lift (openOwner 0) 1 = 1 := rfl
example : lift (openOwner 0) 2 = 1 := rfl

theorem below_scope_run : Finishes belowScope [1] := .bind (.right .use)
theorem below_scope_alias_once :
    (([1] : List Nat).map (openOwner 0)).count 0 = 1 :=
  alias_finished (show (Control.alias 0 belowScope).demand 0 = some 1 by decide) below_scope_run

-- An alias map is not proof that two physical owners are identical. Authenticity
-- must come from typed lends; merging distinct owners could hide an omission.
example : (Control.use 0).demand 1 = some 0 := by decide
example : AliasLinear (fun _ => 0) [0] (.use 0) := by
  intro owner h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  subst owner
  rfl

-- Borrowed mode does not establish non-escape or prevent future use-after-free.
-- These examples prove counting facts only, never validity of a borrow lease.
end Jihoo.Quantity.AliasExamples
