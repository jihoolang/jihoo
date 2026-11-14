import Jihoo.NativeKernelEnvironment

/-! Syntax-only checked-prefix lookup preservation. The names are shared with
the unified typing and conversion layers without introducing an import cycle. -/
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

end Jihoo.NativeKernel.Environment
