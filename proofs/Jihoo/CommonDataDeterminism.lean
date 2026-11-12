import Jihoo.CommonDataSafety

namespace Jihoo.CommonData
open RecursiveFieldRuntime RecursiveLexicalFields

/-- Determinism is inherited by embedded Core and extended over actual
empty/node branch selection, field reads and final pending-shell release. -/
theorem Eval.deterministic (a : Eval g env term s v es t)
    (b : Eval g env term s w fs u) : v = w ∧ es = fs ∧ t = u := by
  induction a generalizing w fs u with
  | core shape first =>
    cases b <;> simp_all
    rename_i otherRun
    obtain ⟨eq, rfl, rfl⟩ := first.deterministic otherRun
    cases eq
    exact ⟨rfl, rfl, rfl⟩
  | literal shape => cases b <;> simp_all
  | empty shape =>
    cases b <;> simp_all
  | dataVar shape lookup =>
    cases b <;> simp_all
  | construct shape leftVar left rightVar right =>
    cases b <;> simp_all
  | bufferLet shape lam ty first second ih | allocate shape lam ty first second ih =>
    cases b <;> simp_all
    rename_i otherFirst otherSecond
    obtain ⟨eq, rfl, rfl⟩ := first.deterministic otherFirst
    cases eq
    obtain ⟨rfl, rfl, rfl⟩ := ih otherSecond
    exact ⟨rfl, rfl, rfl⟩
  | dataLet shape lam domain first second argIH bodyIH =>
    cases b <;> simp_all
    rename_i otherFirst otherSecond
    obtain ⟨eq,rfl,rfl⟩ := argIH otherFirst
    cases eq
    obtain ⟨rfl,rfl,rfl⟩ := bodyIH otherSecond
    exact ⟨rfl,rfl,rfl⟩
  | freeBuffer shape owner lookup body ih =>
    cases b <;> simp_all
    exact ih (by assumption)
  | drop shape owner lookup destroyed branch ih =>
    cases b <;> simp_all
    rename_i otherDestroyed otherBranch
    obtain ⟨rfl,rfl⟩ := destroyed.deterministic otherDestroyed
    obtain ⟨rfl,rfl,rfl⟩ := ih otherBranch
    exact ⟨rfl,rfl,rfl⟩
  | emptyCase shape scrutinee lookup branch ih =>
    cases b <;> simp_all
    case emptyCase => exact ih (by assumption)
    case nodeCase => simp_all [enter]
  | nodeCase shape scrutinee entered branch ih =>
    cases b <;> simp_all
    case emptyCase => simp_all [enter]
    case nodeCase =>
      obtain ⟨rfl, rfl, rfl⟩ := ih (by assumption)
      exact ⟨rfl, rfl, rfl⟩

/-- The common typing theorem covers every admitted execution, including
actual branch selection and parent release after the typed branch body. -/
theorem Typing.every_run (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : HeapLeases.Valid s.buffers.heap)
    (owned : LinearHeapPrograms.Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) (observed : Eval g env term s v es t) :
    HeapLeases.Steps s.buffers.heap es t.buffers.heap ∧ HeapLeases.Valid t.buffers.heap ∧
      Post kind t v frame := by
  obtain ⟨w, fs, u, canonical, steps, vu, post⟩ :=
    typed.total length agreement layout valid owned fields
  obtain ⟨rfl, rfl, rfl⟩ := observed.deterministic canonical
  exact ⟨steps, vu, post⟩

end Jihoo.CommonData
