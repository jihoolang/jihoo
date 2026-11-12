import Jihoo.CommonDataDropExamples

namespace Jihoo.CommonDataApplicationExamples
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields CommonData
open CommonDataExamples (start parent)

def graph : CommonData.Graph := #[
  .ind 0 [], .core (.var 0), .core (.var 1), .core (.var 2), .empty,
  .construct 2 1, .caseTree 1 4 5 0, .core (.integer 99), .embedded 7,
  .drop 0 1 8, .core (.lam false 0 9), .core (.app 10 6),
  .core (.lam false 0 6), .core (.app 12 6),
  .core (.lam false 0 1), .core (.app 14 11),
  .core (.lam false 0 2), .core (.app 16 6),
  .core (.lam true 0 1), .core (.app 18 6),
  .ind 1 [], .core (.lam false 20 1), .core (.app 21 6),
  .ind 0 [7], .core (.lam false 23 1), .core (.app 24 6),
  .core (.app 14 6), .core (.app 14 4),
  .core .i64, .core (.free 2 7), .core (.lam false 28 2),
  .core (.app 30 29), .core (.app 10 31), .core (.app 10 4), .core (.app 10 13)]

theorem graph_valid : validGraph graph = true := by decide

theorem rebuild_typed (selected : ctx[0]? = some (.data 0)) :
    Typing graph ctx 1 [] 6 .data :=
  .caseTree (count := 0) rfl rfl selected (.empty rfl)
    (.construct rfl rfl rfl rfl rfl)

theorem drop_typed (selected : ctx[0]? = some (.data 0)) :
    Typing graph ctx 1 [] 9 .scalar :=
  .drop (count := 0) rfl rfl selected
    (.core rfl (.literal (v := 99) (by rw [core_at]; rfl) (by decide)))

theorem rebuild_then_drop_typed : Typing graph [.data 0] 1 [] 11 .scalar :=
  .dataLet rfl rfl rfl (rebuild_typed rfl) (drop_typed rfl)

theorem rebuild_twice_typed : Typing graph [.data 0] 1 [] 13 .data :=
  .dataLet rfl rfl rfl (rebuild_typed rfl) (rebuild_typed rfl)

def first := finish (allocate start (some 1) (some 2)) 0
def second := finish (allocate first (some 1) (some 2)) 7
def dropped := finish (finish (finish (finish first 7) 1) 2) 3

theorem producer_run : Eval graph [.data (some 0)] 6 start (.data (some 7))
    [.alloc 7 0,.free 0] first :=
  .nodeCase rfl rfl rfl (.construct rfl rfl rfl rfl rfl)

theorem twice_run : Eval graph [.data (some 0)] 13 start (.data (some 8))
    [.alloc 7 0,.free 0,.alloc 8 0,.free 7] second :=
  .dataLet rfl rfl rfl producer_run
    (.nodeCase rfl rfl rfl (.construct rfl rfl rfl rfl rfl))

theorem computed_destroy : Destroy (some 7) first [.free 7,.free 1,.free 2,.free 3] dropped :=
  .node (left := [.free 1]) (right := [.free 2,.free 3]) rfl
    (.node (left := []) (right := []) rfl .empty .empty)
    (.node (left := [.free 3]) (right := []) rfl
      (.node (left := []) (right := []) rfl .empty .empty) .empty)

theorem drop_run : Eval graph [.data (some 0)] 11 start (.scalar 99)
    [.alloc 7 0,.free 0,.free 7,.free 1,.free 2,.free 3] dropped :=
  .dataLet rfl rfl rfl producer_run (.drop rfl rfl rfl computed_destroy
    (.core rfl (.scalar (v := 99) (by rw [core_at]; rfl))))

theorem twice_safe : Steps start.buffers.heap [.alloc 7 0,.free 0,.alloc 8 0,.free 7] second.buffers.heap ∧
    Valid second.buffers.heap ∧ Post .data second (.data (some 8)) [4,5,6] :=
  rebuild_twice_typed.every_run (trees := [parent]) (owners := []) rfl
    (.cons ⟨parent,rfl,rfl⟩ .nil) empty_layout CommonDataExamples.valid_start
    CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields twice_run

theorem drop_safe : Steps start.buffers.heap [.alloc 7 0,.free 0,.free 7,.free 1,.free 2,.free 3]
    dropped.buffers.heap ∧ Valid dropped.buffers.heap ∧ Owns dropped.buffers.heap [4,5,6] := by
  have result := rebuild_then_drop_typed.every_run (trees := [parent]) (owners := []) rfl
    (.cons ⟨parent,rfl,rfl⟩ .nil) empty_layout CommonDataExamples.valid_start
    CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields drop_run
  exact ⟨result.1,result.2.1,result.2.2.2⟩

theorem empty_argument_typed : Typing graph [] 0 [] 27 .data :=
  .dataLet rfl rfl rfl (.empty rfl) (.dataVar rfl rfl)

theorem empty_argument_run : Eval graph [] 27 start (.data none) [] start :=
  .dataLet rfl rfl rfl (.empty rfl) (.dataVar rfl rfl)

theorem aliases_retired : dataContinuation [.data 0,.data 0,.buffer 1,.nat 3,.scalar,.ghost] =
    [.data 0,.dead,.dead,.dead,.nat 3,.scalar,.ghost] := rfl

private theorem application_domain (typed : Typing g ctx count sizes term kind)
    (shape : nodeAt g term = .core (.app fn arg)) :
    ∃ ty body, nodeAt g fn = .core (.lam false ty body) ∧
      (nodeAt g ty = .core .i64 ∨ nodeAt g ty = .ind 0 [] ∨
        ∃ len, nodeAt g ty = .core (.buffer len)) := by
  cases typed <;> simp_all
  all_goals first
    | exact ⟨_,_,by assumption,Or.inl (by assumption)⟩
    | exact ⟨_,_,by assumption,Or.inr (Or.inl (by assumption))⟩
    | exact ⟨_,_,by assumption,Or.inr (Or.inr ⟨_,by assumption⟩)⟩

theorem erased_lambda_rejected : ¬ Typing graph [.data 0] 1 [] 19 .data := by
  intro typed
  obtain ⟨ty,body,lam,_⟩ := application_domain typed (fn := 18) (arg := 6) rfl
  change Node.core (.lam true 0 1) = .core (.lam false ty body) at lam
  cases lam

theorem wrong_family_rejected : ¬ Typing graph [.data 0] 1 [] 22 .data := by
  intro typed
  obtain ⟨ty,body,lam,domain⟩ := application_domain typed (fn := 21) (arg := 6) rfl
  change Node.core (.lam false 20 1) = .core (.lam false ty body) at lam
  cases lam
  simp [nodeAt,graph] at domain

theorem indexed_domain_rejected : ¬ Typing graph [.data 0] 1 [] 25 .data := by
  intro typed
  obtain ⟨ty,body,lam,domain⟩ := application_domain typed (fn := 24) (arg := 6) rfl
  change Node.core (.lam false 23 1) = .core (.lam false ty body) at lam
  cases lam
  simp [nodeAt,graph] at domain

theorem stale_alias_rejected : ¬ Typing graph (dataContinuation [.data 0]) 1 [] 2 .data := by
  intro typed
  cases typed <;> simp_all [nodeAt,graph,dataContinuation,retireAll]
  all_goals subst_vars; contradiction

theorem ind_projects_opaque : ScopedLend.Graph.nodeAt (coreGraph graph) 0 = .opaque := by
  rw [core_at]; rfl

theorem empty_then_drop_typed : Typing graph [] 0 [] 33 .scalar :=
  .dataLet rfl rfl rfl (.empty rfl) (drop_typed rfl)

theorem empty_then_drop_run : Eval graph [] 33 start (.scalar 99) [] start :=
  .dataLet rfl rfl rfl (.empty rfl) (.drop rfl rfl rfl .empty
    (.core rfl (.scalar (v := 99) (by rw [core_at]; rfl))))

theorem buffer_argument_typed : Typing graph [.data 0,.buffer 1] 1 [1] 31 .data := by
  apply Typing.bufferLet rfl rfl rfl
  · exact .free (owner := 2) (body := 7) (k := 1) (slot := 0)
      (by rw [core_at]; rfl) (by rw [core_at]; rfl) rfl (by decide)
      (.literal (v := 99) (by rw [core_at]; rfl) (by decide))
  · exact .dataVar rfl rfl

theorem buffer_application_typed : Typing graph [.data 0,.buffer 1] 1 [1] 32 .scalar :=
  .dataLet rfl rfl rfl buffer_argument_typed (drop_typed rfl)

def bufferMiddle : CommonData.State := ⟨SizedBufferHeap.release start.buffers 4,start.cells⟩
def bufferFinal := finish (finish (finish (finish bufferMiddle 0) 1) 2) 3

theorem buffer_argument_run : Eval graph [.data (some 0),.buffer 4] 31 start (.data (some 0))
    [.free 4] bufferMiddle :=
  .bufferLet rfl rfl rfl
    (.free (owner := 2) (body := 7) (k := 1) (by rw [core_at]; rfl)
      (by rw [core_at]; rfl) rfl (.scalar (v := 99) (by rw [core_at]; rfl)))
    (.dataVar rfl rfl)

theorem buffer_application_run : Eval graph [.data (some 0),.buffer 4] 32 start (.scalar 99)
    [.free 4,.free 0,.free 1,.free 2,.free 3] bufferFinal :=
  .dataLet rfl rfl rfl buffer_argument_run
    (.drop (before := [.free 0,.free 1,.free 2,.free 3]) rfl rfl rfl
      (.node (left := [.free 1]) (right := [.free 2,.free 3]) rfl
        (.node (left := []) (right := []) rfl .empty .empty)
        (.node (left := [.free 3]) (right := []) rfl
          (.node (left := []) (right := []) rfl .empty .empty) .empty))
      (.core rfl (.scalar (v := 99) (by rw [core_at]; rfl))))

theorem nested_application_typed : Typing graph [.data 0] 1 [] 34 .scalar :=
  .dataLet rfl rfl rfl rebuild_twice_typed (drop_typed rfl)

def nestedFinal := finish (finish (finish (finish second 8) 1) 2) 3

theorem nested_application_run : Eval graph [.data (some 0)] 34 start (.scalar 99)
    [.alloc 7 0,.free 0,.alloc 8 0,.free 7,.free 8,.free 1,.free 2,.free 3] nestedFinal :=
  .dataLet rfl rfl rfl twice_run
    (.drop (before := [.free 8,.free 1,.free 2,.free 3]) rfl rfl rfl
      (.node (left := [.free 1]) (right := [.free 2,.free 3]) rfl
        (.node (left := []) (right := []) rfl .empty .empty)
        (.node (left := [.free 3]) (right := []) rfl
          (.node (left := []) (right := []) rfl .empty .empty) .empty))
      (.core rfl (.scalar (v := 99) (by rw [core_at]; rfl))))

theorem scalar_argument_rejected : ¬ Typing graph [] 0 [] 8 .data := by
  intro typed
  cases typed <;> simp_all [nodeAt,graph]

end Jihoo.CommonDataApplicationExamples
