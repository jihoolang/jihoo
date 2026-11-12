import Jihoo.ReferenceHeap

/-! Object-granular frame rules for the abstract, append-only ReferenceHeap.
No native layout, reuse, recursive Drop or CommonData representation is assumed.
Ownership below is a logical assertion, not a runtime permission check. -/
namespace Jihoo.ReferenceHeap
namespace Frame

/-- Exact agreement includes absence, liveness, size, initialization, contents,
and reference provenance. It does not follow references transitively. -/
def Agree (F : Nat → Prop) (H K : Heap) : Prop :=
  ∀ j, F j → K[j]? = H[j]?

def Outside (j : Nat) : Nat → Prop := fun k => k ≠ j

/-- A frame assertion may observe only the named object footprint. -/
def Supported (F : Nat → Prop) (P : Heap → Prop) : Prop :=
  ∀ H K, Agree F H K → (P H ↔ P K)

theorem agree_refl : Agree F H H := fun _ _ => rfl

theorem agree_symm (h : Agree F H K) : Agree F K H :=
  fun j hj => (h j hj).symm

theorem agree_trans (h : Agree F H K) (h' : Agree F K L) : Agree F H L :=
  fun j hj => (h' j hj).trans (h j hj)

theorem agree_mono (h : Agree F H K) (sub : ∀ j, G j → F j) : Agree G H K :=
  fun j hj => h j (sub j hj)

theorem supported_preserved (support : Supported F P) (h : Agree F H K)
    (hp : P H) : P K := (support H K h).mp hp

theorem set_other (H : Heap) (obj : Object) (different : k ≠ j) :
    (H.set! j obj)[k]? = H[k]? := by
  unfold Array.set! Array.setIfInBounds
  split <;> simp [Ne.symm different]

/-- Success exposes object existence, liveness and bounds, but does not require
initialization. The stored scalar must be bounded; reference targets need not
be live, in bounds, or disjoint from the modified object. -/
theorem store_success_iff : store H (.object j i) v = some K ↔
    ∃ obj, H[j]? = some obj ∧ obj.alive = true ∧ i < obj.cells.size ∧
      validCell v = true ∧ K = H.set! j {obj with cells := obj.cells.set! i (some v)} := by
  simp only [store, address]
  cases ho : H[j]? with
  | none => simp
  | some obj =>
    by_cases live : obj.alive = true
    · by_cases bound : i < obj.cells.size
      · simp [live, bound]
        intro _
        exact eq_comm
      · simp [live, bound]
    · simp [live]

/-- Free requires a live existing base; it does not require a nonempty object. -/
theorem release_success_iff : release H (.object j i) = some K ↔
    ∃ obj, H[j]? = some obj ∧ obj.alive = true ∧ i = 0 ∧
      K = H.set! j {obj with alive := false} := by
  simp only [release]
  cases ho : H[j]? with
  | none => simp
  | some obj =>
    by_cases live : obj.alive = true
    · by_cases base : i = 0
      · simp [live, base]
        exact eq_comm
      · simp [base]
    · simp [live]

theorem store_agree (h : store H (.object j i) v = some K) :
    Agree (Outside j) H K := by
  obtain ⟨obj, _, _, _, _, rfl⟩ := store_success_iff.mp h
  exact fun _ hk => set_other H _ hk

theorem release_agree (h : release H (.object j i) = some K) :
    Agree (Outside j) H K := by
  obtain ⟨obj, _, _, _, rfl⟩ := release_success_iff.mp h
  exact fun _ hk => set_other H _ hk

theorem address_eq (h : Agree F H K) (hk : F k) :
    address K (.object k i) = address H (.object k i) := by
  simp [address, h k hk]

/-- Address validity requires a live in-bounds container, but no initialized cell. -/
def Valid (H : Heap) (p : Ref) : Prop := ∃ loc, address H p = some loc

/-- Initialization requires successful untyped loading; payload kind is separate. -/
def Initialized (H : Heap) (p : Ref) : Prop := ∃ v, load H p = some v

theorem valid_iff (h : Agree F H K) (hk : F k) :
    Valid K (.object k i) ↔ Valid H (.object k i) := by
  simp [Valid, address_eq h hk]

theorem load_eq (h : Agree F H K) (hk : F k) :
    load K (.object k i) = load H (.object k i) := by
  simp [load, address_eq h hk]

theorem initialized_iff (h : Agree F H K) (hk : F k) :
    Initialized K (.object k i) ↔ Initialized H (.object k i) := by
  simp [Initialized, load_eq h hk]

theorem loadRef_eq (h : Agree F H K) (hk : F k) :
    loadRef K (.object k i) = loadRef H (.object k i) := by
  simp [loadRef, load_eq h hk]

theorem loadScalar_eq (h : Agree F H K) (hk : F k) :
    loadScalar K (.object k i) = loadScalar H (.object k i) := by
  simp [loadScalar, load_eq h hk]

theorem liveBase_iff (h : Agree F H K) (hk : F k) :
    LiveBase K (.object k i) ↔ LiveBase H (.object k i) := by
  simp [LiveBase, h k hk]

/-- Exact successful load contract: bounds/liveness are separate from
initialization, and initialized null is a value. -/
theorem load_success_iff : load H (.object j i) = some v ↔
    ∃ obj, H[j]? = some obj ∧ obj.alive = true ∧ i < obj.cells.size ∧
      obj.cells[i]? = some (some v) := by
  simp only [load, address]
  cases ho : H[j]? with
  | none => simp
  | some obj =>
    by_cases live : obj.alive = true
    · by_cases bound : i < obj.cells.size
      · simp [live, bound]
      · simp [live, bound]
    · simp [live]

/-- Reads return the identical heap, so all footprints (even aliases) survive. -/
theorem read_frame (h : execute H (.read p) = some (K, r)) : K = H := by
  simp only [execute] at h
  cases hl : loadRef H p <;> simp [hl] at h
  exact h.1.symm

theorem store_frame (h : store H (.object j i) v = some K)
    (disjoint : ∀ k, F k → k ≠ j) (support : Supported F P) (hp : P H) : P K :=
  supported_preserved support (agree_mono (store_agree h) disjoint) hp

theorem release_frame (h : release H (.object j i) = some K)
    (disjoint : ∀ k, F k → k ≠ j) (support : Supported F P) (hp : P H) : P K :=
  supported_preserved support (agree_mono (release_agree h) disjoint) hp

/-- Object ownership is an exclusive logical claim of an exact live object.
A higher-level representation must additionally specify reachable children. -/
def Own (H : Heap) (j : Nat) (cells : Array (Option Cell)) : Prop :=
  H[j]? = some ⟨true, cells⟩

inductive Kind where
  | buffer
  | data
  deriving DecidableEq

structure Claim where
  id : Nat
  kind : Kind
  cells : Array (Option Cell)

/-- Buffer claims allow uninitialized slots but only bounded scalar values.
Data claims permit arbitrary provenance cells; no Tree representation is imposed. -/
def Shape (c : Claim) : Prop :=
  match c.kind with
  | .buffer => ∀ (i : Nat) (v : Cell), c.cells[i]? = some (some v) →
      ∃ n, v = Cell.scalar n ∧ n < BoundedMir.scalarBound
  | .data => ∀ (i : Nat) (v : Cell), c.cells[i]? = some (some v) → validCell v = true

def Footprint (cs : List Claim) (j : Nat) : Prop := ∃ c ∈ cs, c.id = j

/-- No duplicate object owners, even at different cell indices or across kinds.
This does not forbid pointer aliases in contents: these do not confer ownership. -/
def OwnMixed (cs : List Claim) (H : Heap) : Prop :=
  (cs.map Claim.id).Nodup ∧ ∀ c ∈ cs, Shape c ∧ Own H c.id c.cells

theorem own_iff (h : Agree F H K) (hj : F j) : Own H j cells ↔ Own K j cells := by
  simp [Own, h j hj]

theorem mixed_supported : Supported (Footprint cs) (OwnMixed cs) := by
  intro H K h
  have he : ∀ c ∈ cs, Own H c.id c.cells ↔ Own K c.id c.cells :=
    fun c hc => own_iff h ⟨c, hc, rfl⟩
  constructor <;> rintro ⟨unique, owned⟩
  · exact ⟨unique, fun c hc => ⟨(owned c hc).1, (he c hc).mp (owned c hc).2⟩⟩
  · exact ⟨unique, fun c hc => ⟨(owned c hc).1, (he c hc).mpr (owned c hc).2⟩⟩

theorem store_mixed (h : store H (.object j i) v = some K)
    (disjoint : ∀ c ∈ cs, c.id ≠ j) (owned : OwnMixed cs H) : OwnMixed cs K := by
  apply store_frame h (F := Footprint cs) _ mixed_supported owned
  rintro k ⟨c, hc, rfl⟩
  exact disjoint c hc

theorem release_mixed (h : release H (.object j i) = some K)
    (disjoint : ∀ c ∈ cs, c.id ≠ j) (owned : OwnMixed cs H) : OwnMixed cs K := by
  apply release_frame h (F := Footprint cs) _ mixed_supported owned
  rintro k ⟨c, hc, rfl⟩
  exact disjoint c hc


/-- The exact updated object, including unchanged liveness and slot count. -/
theorem store_object (h : store H (.object j i) v = some K) :
    ∃ obj, H[j]? = some obj ∧ obj.alive = true ∧ i < obj.cells.size ∧
      K[j]? = some {obj with cells := obj.cells.set! i (some v)} := by
  obtain ⟨obj, ho, live, bound, _, rfl⟩ := store_success_iff.mp h
  refine ⟨obj, ho, live, bound, ?_⟩
  have hj : j < H.size := Array.getElem?_eq_some_iff.mp ho |>.1
  simp [Array.set!, Array.setIfInBounds, hj]

theorem store_load_self (h : store H (.object j i) v = some K) :
    load K (.object j i) = some v := by
  obtain ⟨obj, _, live, bound, hk⟩ := store_object h
  simp [load, address, hk, live, Array.set!, Array.setIfInBounds, bound]

/-- Distinct slots of the same object retain their values, but do not constitute
separate exclusive object owners. Equality covers uninitialized/OOB failures. -/
theorem store_load_other_slot (h : store H (.object j i) v = some K)
    (different : t ≠ i) : load K (.object j t) = load H (.object j t) := by
  obtain ⟨obj, ho, live, bound, hk⟩ := store_object h
  by_cases ht : t < obj.cells.size <;>
    simp [load, address, hk, ho, live, Array.set!, Array.setIfInBounds, bound, ht,
      Ne.symm different]

theorem release_object (h : release H (.object j i) = some K) :
    ∃ obj, H[j]? = some obj ∧ obj.alive = true ∧ i = 0 ∧
      K[j]? = some {obj with alive := false} := by
  obtain ⟨obj, ho, live, base, rfl⟩ := release_success_iff.mp h
  refine ⟨obj, ho, live, base, ?_⟩
  have hj : j < H.size := Array.getElem?_eq_some_iff.mp ho |>.1
  simp [Array.set!, Array.setIfInBounds, hj]

theorem release_load_none (h : release H (.object j i) = some K) :
    load K (.object j t) = none := by
  obtain ⟨obj, _, _, _, hk⟩ := release_object h
  exact load_dead hk rfl

theorem release_not_live (h : release H (.object j i) = some K) :
    ¬ LiveBase K (.object j t) := by
  obtain ⟨obj, _, _, _, hk⟩ := release_object h
  simp [LiveBase, hk]

/-- Stores preserve the target object's live-base validity, even when its
contents cease to satisfy a higher-level ownership/representation assertion. -/
theorem store_liveBase (h : store H (.object j i) v = some K) :
    LiveBase K (.object j 0) := by
  obtain ⟨obj, _, live, _, hk⟩ := store_object h
  exact ⟨rfl, _, hk, live⟩

/-- Local write rule; initialization is unnecessary. This consumes the old
logical contents and produces the new contents without claiming alias freedom. -/
theorem own_store (owned : Own H j cells) (bound : i < cells.size)
    (value : validCell v = true) :
    ∃ K, store H (.object j i) v = some K ∧
      Own K j (cells.set! i (some v)) := by
  let K := H.set! j ⟨true, cells.set! i (some v)⟩
  have hs : store H (.object j i) v = some K :=
    store_success_iff.mpr ⟨⟨true, cells⟩, owned, rfl, bound, value, rfl⟩
  refine ⟨K, hs, ?_⟩
  have hj : j < H.size := Array.getElem?_eq_some_iff.mp owned |>.1
  simp [Own, K, Array.set!, Array.setIfInBounds, hj]

theorem own_release (owned : Own H j cells) :
    ∃ K, release H (.object j 0) = some K ∧
      K[j]? = some ⟨false, cells⟩ ∧ ¬ LiveBase K (.object j 0) := by
  let K := H.set! j ⟨false, cells⟩
  have hs : release H (.object j 0) = some K :=
    release_success_iff.mpr ⟨⟨true, cells⟩, owned, rfl, rfl, rfl⟩
  refine ⟨K, hs, ?_, release_not_live hs⟩
  have hj : j < H.size := Array.getElem?_eq_some_iff.mp owned |>.1
  simp [K, Array.setIfInBounds, hj]

/-- Local ownership plus the external frame yields a total successful write
under explicit bounds/value premises, not merely a conditional postcondition. -/
theorem own_store_mixed (owned : Own H j cells) (bound : i < cells.size)
    (value : validCell v = true) (frame : OwnMixed cs H)
    (disjoint : ∀ c ∈ cs, c.id ≠ j) :
    ∃ K, store H (.object j i) v = some K ∧
      Own K j (cells.set! i (some v)) ∧ OwnMixed cs K := by
  obtain ⟨K, hs, ho⟩ := own_store owned bound value
  exact ⟨K, hs, ho, store_mixed hs disjoint frame⟩

theorem own_release_mixed (owned : Own H j cells) (frame : OwnMixed cs H)
    (disjoint : ∀ c ∈ cs, c.id ≠ j) :
    ∃ K, release H (.object j 0) = some K ∧
      K[j]? = some ⟨false, cells⟩ ∧ ¬ LiveBase K (.object j 0) ∧ OwnMixed cs K := by
  obtain ⟨K, hs, ho, dead⟩ := own_release owned
  exact ⟨K, hs, ho, dead, release_mixed hs disjoint frame⟩

/-- A successful typed read preserves every supported assertion, without any
separation requirement because it performs no mutation. -/
theorem read_supported {P : Heap → Prop} (h : execute H (.read p) = some (K, r))
    (hp : P H) : P K := by
  simpa [read_frame h] using hp

end Frame
end Jihoo.ReferenceHeap
