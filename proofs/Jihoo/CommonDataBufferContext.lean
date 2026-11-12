import Jihoo.CommonDataSyntax

/-! Buffer operations preserve the Data pre and lexical positions. -/
namespace Jihoo.CommonData
open RecursiveLexicalFields RecursiveFieldOwnership RecursiveFieldRuntime

def freshBufferEntry : Entry → Entry
  | .buffer k => .buffer (k+1)
  | e => e

def freshBuffer (count : Nat) (ctx : List Entry) :=
  Entry.buffer count :: ctx.map freshBufferEntry

def consumeBufferEntry (slot : Nat) : Entry → Entry
  | .buffer k => if k = slot then .dead else .buffer (if slot < k then k-1 else k)
  | e => e

def consumeBuffer (slot : Nat) (ctx : List Entry) := ctx.map (consumeBufferEntry slot)

theorem consumeBuffer_alias : consumeBufferEntry slot (.buffer slot) = .dead := by
  simp [consumeBufferEntry]

theorem consumeBuffer_data : consumeBufferEntry slot (.data k) = .data k := rfl

variable {k x slot : Nat} {tree : Tree}

theorem caps_data {trees : List Tree} {owners : List Nat}
    (h : (caps trees owners)[k]? = some (.data tree)) :
    trees[k]? = some tree := by
  simp only [caps, List.getElem?_append, List.length_map, List.getElem?_map] at h
  split at h
  · cases found : trees[k]? <;> simp_all
  · cases found : owners[k-trees.length]? <;> simp_all

theorem caps_buffer {trees : List Tree} {owners : List Nat}
    (h : (caps trees owners)[k]? = some (.buffer x)) :
    trees.length ≤ k ∧ owners[k-trees.length]? = some x := by
  simp only [caps, List.getElem?_append, List.length_map, List.getElem?_map] at h
  split at h
  · cases found : trees[k]? <;> simp_all
  · constructor
    · omega
    · cases found : owners[k-trees.length]? <;> simp_all

theorem data_in_caps {trees : List Tree} (h : trees[k]? = some tree) :
    (caps trees owners)[k]? = some (.data tree) := by
  have bound := List.getElem?_eq_some_iff.mp h |>.1
  simpa only [caps, List.getElem?_append, List.length_map, bound, ite_true, List.getElem?_map, Option.map_some] using congrArg (Option.map Capability.data) h

theorem buffer_in_caps {trees : List Tree} {owners : List Nat}
    (bound : trees.length ≤ k) (h : owners[k-trees.length]? = some x) :
    (caps trees owners)[k]? = some (.buffer x) := by
  simp [caps, List.getElem?_append, show ¬ k < trees.length by omega, h]

theorem rel_freshBuffer (h : Rel (caps trees owners) e v) :
    Rel (caps trees (x :: owners)) (freshBufferEntry e) v := by
  cases e with
  | buffer k =>
    obtain ⟨y,lookup,eq⟩ := h
    obtain ⟨bound,lookup⟩ := caps_buffer lookup
    refine ⟨y, buffer_in_caps (by omega) ?_, eq⟩
    simpa [show k+1-trees.length = (k-trees.length)+1 by omega] using lookup
  | data k =>
    obtain ⟨tree,lookup,eq⟩ := h
    exact ⟨tree,data_in_caps (caps_data lookup),eq⟩
  | nat _ | scalar | ghost | dead => exact h

theorem agrees_freshBuffer (h : Agrees (caps trees owners) ctx env) :
    Agrees (caps trees (x :: owners)) (freshBuffer trees.length ctx) (.buffer x :: env) := by
  refine .cons ⟨x,buffer_in_caps (by omega) (by simp),rfl⟩ ?_
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (rel_freshBuffer head) ih

theorem rel_consumeBuffer (h : Rel (caps trees owners) e v)
    (selected : LinearHeapPrograms.Select owners slot x rest) :
    Rel (caps trees rest) (consumeBufferEntry (trees.length+slot) e) v := by
  cases e with
  | buffer k =>
    by_cases eq : k = trees.length+slot
    · simp [consumeBufferEntry,eq,Rel]
    · obtain ⟨y,lookup,value⟩ := h
      obtain ⟨bound,lookup⟩ := caps_buffer lookup
      simp only [consumeBufferEntry,eq,ite_false,Rel]
      have ne : k-trees.length ≠ slot := by omega
      have other := (LinearCoreCallers.Select.lookup_other selected ne).trans lookup
      refine ⟨y,buffer_in_caps (by split <;> omega) ?_,value⟩
      by_cases lt : trees.length+slot < k
      · simpa [lt,show slot < k-trees.length by omega,
          show k-1-trees.length = k-trees.length-1 by omega] using other
      · simpa [lt,show ¬ slot < k-trees.length by omega] using other
  | data k =>
    obtain ⟨tree,lookup,eq⟩ := h
    exact ⟨tree,data_in_caps (caps_data lookup),eq⟩
  | nat _ | scalar | ghost | dead => exact h

theorem agrees_consumeBuffer (h : Agrees (caps trees owners) ctx env)
    (selected : LinearHeapPrograms.Select owners slot x rest) :
    Agrees (caps trees rest) (consumeBuffer (trees.length+slot) ctx) env := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (rel_consumeBuffer head selected) ih

theorem select_frame (selected : LinearHeapPrograms.Select owners slot x rest)
    (pre suffix : List Nat) :
    LinearHeapPrograms.Select (pre ++ (owners ++ suffix)) (pre.length+slot) x
      (pre ++ (rest ++ suffix)) := by
  have right : LinearHeapPrograms.Select (owners ++ suffix) slot x (rest ++ suffix) := by
    induction selected with
    | here => exact .here
    | there h ih => exact .there ih
  induction pre with
  | nil => simpa using right
  | cons y ys ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using LinearHeapPrograms.Select.there ih

/-- Retire the consumed Buffer prefix while preserving every Data slot. The
returned owner occupies the first Buffer slot and a new lexical binder. -/
def bufferCallEntry (count p : Nat) : Entry → Entry
  | .buffer k => if count + p ≤ k then .buffer (k-p+1) else .dead
  | e => e

def bufferCall (count p : Nat) (ctx : List Entry) :=
  Entry.buffer count :: ctx.map (bufferCallEntry count p)

theorem bufferCall_consumed (h : k < count+p) :
    bufferCallEntry count p (.buffer k) = .dead := by
  simp [bufferCallEntry, show ¬ count+p ≤ k by omega]

theorem rel_bufferCall (h : Rel (caps trees owners) e v) :
    Rel (caps trees (x :: owners.drop p)) (bufferCallEntry trees.length p e) v := by
  cases e with
  | buffer k =>
    by_cases bound : trees.length+p ≤ k
    · obtain ⟨y,lookup,eq⟩ := h
      obtain ⟨_,lookup⟩ := caps_buffer lookup
      simp only [bufferCallEntry,bound,ite_true]
      refine ⟨y, ?_, eq⟩
      apply buffer_in_caps (by omega)
      simpa [show k-p+1-trees.length = (k-trees.length-p)+1 by omega,
        List.getElem?_drop, show p+(k-trees.length-p) = k-trees.length by omega] using lookup
    · simp [bufferCallEntry,bound,Rel]
  | data k =>
    obtain ⟨tree,lookup,eq⟩ := h
    exact ⟨tree,data_in_caps (caps_data lookup),eq⟩
  | nat _ | scalar | ghost | dead => exact h

theorem agrees_bufferCall (h : Agrees (caps trees owners) ctx env) :
    Agrees (caps trees (x :: owners.drop p))
      (bufferCall trees.length p ctx) (.buffer x :: env) := by
  refine .cons ⟨x,buffer_in_caps (by omega) (by simp),rfl⟩ ?_
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (rel_bufferCall head) ih

end Jihoo.CommonData
