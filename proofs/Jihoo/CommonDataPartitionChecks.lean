import Jihoo.CommonDataSourceChecks
import Jihoo.CommonDataFrameSafety

namespace Jihoo.CommonDataPartitionChecks
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields RecursiveBodyProjection CommonData

/-- Regression syntax only: the soundness theorems quantify over arbitrary
CommonData derivations and arbitrary represented finite input trees. -/
def graph : CommonData.Graph := #[
  .ind 0 [], .core (.var 0), .core (.var 1), .core (.var 2),
  .core (.var 3), .core (.var 4), .core (.integer 99), .core .i64,
  .empty, .construct 2 1, .caseTree 1 8 9 0,
  .construct 1 3, .core (.lam false 0 11), .core (.app 12 10),
  .drop 0 3 6, .drop 0 1 14, .core (.lam false 0 15), .core (.app 16 10),
  .core (.free 3 6), .core (.lam false 7 2), .core (.app 19 18),
  .core (.free 5 6), .embedded 21, .drop 0 3 22, .drop 0 1 23,
  .core (.lam false 0 24), .core (.app 25 20),
  .core (.lam false 0 1), .core (.app 27 8),
  .caseTree 2 8 9 0, .construct 1 2, .core (.lam false 0 30),
  .core (.app 31 29), .caseTree 1 28 32 0, .core (.app 31 8)]

theorem graph_valid : validGraph graph = true := by decide

private theorem rebuild (selected : ctx[0]? = some (.data 0)) :
    Typing graph ctx 1 [] 10 .data :=
  .caseTree (count := 0) rfl rfl selected (.empty rfl)
    (.construct rfl rfl rfl rfl rfl)

/-- Reconstructed argument and retained recursive capture can form one result. -/
theorem reassemble_typed : Typing graph [.data 0,.data 1] 2 [] 13 .data :=
  .dataLetSplit (activeCount := 1) (retainedCount := 1) (usedSizes := []) (savedSizes := [])
    rfl rfl rfl rfl rfl (rebuild rfl) (.construct rfl rfl rfl rfl rfl)

/-- The continuation reads and recursively destroys both actual trees. -/
theorem consume_captures_typed : Typing graph [.data 0,.data 1] 2 [] 17 .scalar :=
  .dataLetSplit (activeCount := 1) (retainedCount := 1) (usedSizes := []) (savedSizes := [])
    rfl rfl rfl rfl rfl (rebuild rfl)
    (.drop (count := 1) rfl rfl rfl (.drop (count := 0) rfl rfl rfl (.literal rfl (by decide))))

/-- One Buffer is consumed by the argument; another stays available with its
original dynamic size to the continuation after both trees are consumed. -/
theorem mixed_captures_typed (firstSize savedSize : Nat) :
    Typing graph [.data 0,.data 1,.buffer 2,.buffer 3] 2 [firstSize,savedSize] 26 .scalar := by
  apply Typing.dataLetSplit (activeCount := 1) (retainedCount := 1)
    (usedSizes := [firstSize]) (savedSizes := [savedSize]) rfl rfl rfl rfl rfl
  · apply Typing.bufferLet rfl rfl rfl
    · exact .free (owner := 3) (body := 6) (k := 2) (slot := 0)
        (by rw [core_at]; rfl) (by rw [core_at]; rfl) rfl (by simp)
        (.literal (v := 99) (by rw [core_at]; rfl) (by decide))
    · exact .dataVar rfl rfl
  · apply Typing.drop (count := 1) rfl rfl rfl
    apply Typing.drop (count := 0) rfl rfl rfl
    exact .core rfl (.free (owner := 5) (body := 6) (k := 4) (slot := 0)
      (by rw [core_at]; rfl) (by rw [core_at]; rfl) rfl (by simp)
      (.literal (v := 99) (by rw [core_at]; rfl) (by decide)))

/-- The new application rule works under Case's pending parent shell. -/
theorem pending_parent_typed : Typing graph [.data 0] 1 [] 33 .data :=
  .caseTree (count := 0) rfl rfl rfl
    (.dataLet rfl rfl rfl (.empty rfl) (.dataVar rfl rfl))
    (.dataLetSplit (activeCount := 1) (retainedCount := 1) (usedSizes := []) (savedSizes := [])
      rfl rfl rfl rfl rfl
      (.caseTree (count := 0) rfl rfl rfl (.empty rfl) (.construct rfl rfl rfl rfl rfl))
      (.construct rfl rfl rfl rfl rfl))

/-- All aliases are changed, while scalar/natural/ghost positions survive. -/
theorem alias_partition :
    argumentContext 1 1 1 [.data 0,.data 1,.buffer 2,.buffer 3,.data 0,.buffer 2,.nat 4,.scalar,.ghost] =
      [.data 0,.dead,.buffer 1,.dead,.data 0,.buffer 1,.nat 4,.scalar,.ghost] ∧
    capturedContext 1 1 1 [.data 0,.data 1,.buffer 2,.buffer 3,.data 0,.buffer 2,.nat 4,.scalar,.ghost] =
      [.data 0,.dead,.data 1,.dead,.buffer 2,.dead,.dead,.nat 4,.scalar,.ghost] := by decide

/-- Empty trees still occupy distinct logical slots, even though both have an
empty allocation footprint. The partition never duplicates a slot. -/
theorem empty_slots_partition :
    argumentContext 1 1 0 [.data 0,.data 1] = [.data 0,.dead] ∧
    capturedContext 1 1 0 [.data 0,.data 1] = [.data 0,.dead,.data 1] ∧
    footprint (caps [Tree.empty,Tree.empty] []) = [] := by decide

private theorem dead_variable (shape : nodeAt g term = .core (.var index))
    (dead : ctx[index]? = some .dead) : ¬ Typing g ctx count sizes term kind := by
  intro typed
  cases typed <;> simp_all

/-- Reserved aliases cannot be used by the argument, regardless of counts. -/
theorem reserved_alias_rejected :
    ¬ Typing graph (argumentContext 1 1 0 [.data 0,.data 1]) count sizes 2 kind :=
  dead_variable rfl rfl

/-- The old argument alias stays in the runtime environment but loses authority. -/
theorem consumed_alias_rejected :
    ¬ Typing graph (capturedContext 1 1 0 [.data 0,.data 1]) count sizes 2 kind :=
  dead_variable rfl rfl

/-- Totality covers arbitrary finite trees, sizes, actual stored fields and an
external frame; neither a successful run nor preserved captures are premises. -/
theorem mixed_captures_total (length : trees.length = 2)
    (agreement : Agrees (caps trees owners) [.data 0,.data 1,.buffer 2,.buffer 3] env)
    (layout : SizedBufferContext.Layout s.buffers owners [firstSize,savedSize])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval graph env 26 s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ Post .scalar t v frame ∧
      (∀ x ∈ frame, t.cells x = s.cells x ∧ t.buffers.length x = s.buffers.length x) :=
  (mixed_captures_typed firstSize savedSize).total_preserving length agreement layout valid owned fields

/-- Zero selected Data/Buffer slots still retain an independently owned tree. -/
theorem empty_producer_retains : Typing graph [.data 0] 1 [] 34 .data :=
  .dataLetSplit (activeCount := 0) (retainedCount := 1) (usedSizes := []) (savedSizes := [])
    rfl rfl rfl rfl rfl (.empty rfl) (.construct rfl rfl rfl rfl rfl)

open CommonDataExamples (start)
open RecursiveFieldOwnershipExamples (leaf)
open RecursiveFieldRuntimeExamples (rightTree)

def rebuilt := finish (allocate start none none) 1
def combined := allocate rebuilt (some 7) (some 2)

theorem nonempty_captures_run : Eval graph [.data (some 1),.data (some 2)] 13 start
    (.data (some 8)) [.alloc 7 0,.free 1,.alloc 8 0] combined :=
  .dataLet rfl rfl rfl
    (.nodeCase rfl rfl rfl (.construct rfl rfl rfl rfl rfl))
    (.construct rfl rfl rfl rfl rfl)

private theorem input_owned :
    Owns start.buffers.heap (footprint (caps [leaf 1,rightTree] []) ++ [0,4,5,6]) := by
  apply owns_permute CommonDataExamples.owns_start
  decide

private theorem input_fields : Fields start.cells (caps [leaf 1,rightTree] []) := by
  intro c member
  simp [caps] at member
  rcases member with rfl | rfl
  · exact RecursiveFieldRuntimeExamples.fields_fixture.2.1
  · exact RecursiveFieldRuntimeExamples.fields_fixture.2.2

/-- Both input trees are nonempty. Actual execution reconstructs the first,
retains the second, and returns a tree containing both. External cells and
Buffer lengths are obtained from the general strengthened theorem. -/
theorem nonempty_captures_safe :
    Steps start.buffers.heap [.alloc 7 0,.free 1,.alloc 8 0] combined.buffers.heap ∧
    Valid combined.buffers.heap ∧ Post .data combined (.data (some 8)) [0,4,5,6] ∧
    (∀ x ∈ [0,4,5,6], combined.cells x = start.cells x ∧
      combined.buffers.length x = start.buffers.length x) :=
  reassemble_typed.every_run_preserving (trees := [leaf 1,rightTree]) (owners := []) rfl
    (.cons ⟨leaf 1,rfl,rfl⟩ (.cons ⟨rightTree,rfl,rfl⟩ .nil)) empty_layout
    CommonDataExamples.valid_start input_owned input_fields nonempty_captures_run

/-- The retained recursive field and a framed Buffer length are concrete
store observations, while the safety conclusion comes from typing. -/
theorem retained_store_observations :
    Represents combined.cells rightTree ∧ combined.buffers.length 5 = 2 := by
  constructor
  · exact ⟨rfl,⟨rfl,trivial,trivial⟩,trivial⟩
  · exact (nonempty_captures_safe.2.2.2 5 (by simp)).2

end Jihoo.CommonDataPartitionChecks
