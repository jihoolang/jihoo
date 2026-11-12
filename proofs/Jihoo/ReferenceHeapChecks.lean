import Jihoo.ReferenceHeap
namespace Jihoo.ReferenceHeap

-- Null is initialized data; an absent cell is not a null reference.
example : loadRef #[⟨true, #[some (.reference .null), none]⟩] (.object 0 0) = some .null := by decide
example : loadRef #[⟨true, #[some (.reference .null), none]⟩] (.object 0 1) = none := by decide
example : loadRef #[nilObject] (.object 0 0) = none := by decide
example : loadScalar #[node .null .null] (.object 0 1) = none := by decide
-- One-past pointers, dead/absent containers and nonbase/double releases fail.
example : loadRef #[node .null .null] (.object 0 3) = none := by decide
example : store #[⟨false, #[none]⟩] (.object 0 0) (.reference .null) = none := by decide
example : loadRef #[] (.object 0 0) = none := by decide
example : release #[nilObject] (.object 0 1) = none := by decide
example : release #[{nilObject with alive := false}] (.object 0 0) = none := by decide
example : store #[⟨true, #[none]⟩] (.object 0 0) (.scalar BoundedMir.scalarBound) = none := by decide
-- Transporting a dangling child preserves its identity without making it live.
example : nodeCycle #[nilObject] (.object 99 0) .null =
    some (#[nilObject, {node (.object 99 0) .null with alive := false}], .object 99 0, .null) := by decide
example : execute #[] (.nullTest (.object 99 0)) = some (#[], .boolean false) := by decide
example : allocate #[] 0 = none := by decide
example : allocate #[] 7 = none := by decide

#print axioms execute_iff
#print axioms step_deterministic
#print axioms scalar_load_compatible
#print axioms scalar_write_compatible
#print axioms allocate_compatible
#print axioms release_compatible
#print axioms pointer_roundtrip
#print axioms no_scalar_forgery
#print axioms node_cycle
#print axioms external_frame
#print axioms released_node_unreadable
end Jihoo.ReferenceHeap
