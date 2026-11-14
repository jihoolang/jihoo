import Jihoo.NativeSubstitution

/-! Append-only arenas over the complete native constructor vocabulary. The
decoder checks constructor arities and follows references with a depth budget.
These are definitions and proofs about the Lean arena model; correspondence to
the native mutable arena, machine integers and resource accounting is separate. -/
namespace Jihoo.NativeKernel.NativeArena

inductive Node where
  | var (index : Nat)
  | node (op : Op) (references : List Nat)
  deriving Repr, DecidableEq

abbrev Arena := Array Node

/-- Extending an arena preserves every existing node and its index. -/
structure Prefix (before after : Arena) : Prop where
  size_le : before.size ≤ after.size
  lookup : ∀ {id : Nat} {n : Node}, before[id]? = some n → after[id]? = some n

variable {g after : Arena} {id fuel : Nat} {t : Term}
  {ids : List Nat} {ts : List Term}

theorem Prefix.refl (g : Arena) : Prefix g g := ⟨Nat.le_refl _, fun h => h⟩

theorem Prefix.trans (h : Prefix g h') (k : Prefix h' j) : Prefix g j :=
  ⟨Nat.le_trans h.size_le k.size_le, fun lookup => k.lookup (h.lookup lookup)⟩

theorem Prefix.push (g : Arena) (n : Node) : Prefix g (g.push n) := by
  refine ⟨by simp, ?_⟩
  intro id node lookup
  obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp lookup
  simpa only [he] using Array.getElem?_push_lt (x := n) hi

theorem Prefix.append (g suffix : Arena) : Prefix g (g ++ suffix) := by
  refine ⟨by simp, ?_⟩
  intro id node lookup
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp lookup
  rw [Array.getElem?_append_left hi]
  exact lookup

/-- A raw arena may contain forward references or cycles. Fuel makes decoding
total and unsuccessful decoding makes no assertion about such a node. -/
def decode : Nat → Arena → Nat → Option Term
  | 0, _, _ => none
  | fuel + 1, g, id => do
      let n ← g[id]?
      match n with
      | .var k => some (.var k)
      | .node op refs => do
          if refs.length = op.arity then
            let children ← refs.mapM (decode fuel g)
            some (.node op children)
          else none

mutual
  /-- Structural graph meaning, independent of decoder execution. -/
  inductive Represents (g : Arena) : Nat → Term → Prop where
    | var {id k : Nat} : g[id]? = some (.var k) → Represents g id (.var k)
    | node {id : Nat} {op : Op} {refs : List Nat} {children : List Term} :
        g[id]? = some (.node op refs) → refs.length = op.arity →
        RepresentsList g refs children → Represents g id (.node op children)

  inductive RepresentsList (g : Arena) : List Nat → List Term → Prop where
    | nil : RepresentsList g [] []
    | cons {id : Nat} {t : Term} {ids : List Nat} {ts : List Term} :
        Represents g id t → RepresentsList g ids ts →
        RepresentsList g (id :: ids) (t :: ts)
end

private theorem frames :
    (∀ g id t, Represents g id t → ∀ after, Prefix g after → Represents after id t) ∧
    (∀ g ids ts, RepresentsList g ids ts → ∀ after, Prefix g after →
      RepresentsList after ids ts) := by
  constructor
  · intro g id t h
    induction h using Represents.rec
      (motive_2 := fun ids ts _ => ∀ after, Prefix g after → RepresentsList after ids ts)
    case var lookup => intro after hp; exact .var (hp.lookup lookup)
    case node lookup arity children ih =>
      intro after hp; exact .node (hp.lookup lookup) arity (ih after hp)
    case nil => exact .nil
    case cons ih ihs after hp => exact .cons (ih after hp) (ihs after hp)
  · intro g ids ts h
    induction h using RepresentsList.rec
      (motive_1 := fun id t _ => ∀ after, Prefix g after → Represents after id t)
    case var lookup after hp => exact .var (hp.lookup lookup)
    case node lookup arity children ih after hp =>
      exact .node (hp.lookup lookup) arity (ih after hp)
    case nil => intro after _; exact .nil
    case cons h hs ih ihs => intro after hp; exact .cons (ih after hp) (ihs after hp)

theorem Represents.frame (h : Represents g id t) (hp : Prefix g after) :
    Represents after id t := frames.1 g id t h after hp

theorem RepresentsList.frame (h : RepresentsList g ids ts) (hp : Prefix g after) :
    RepresentsList after ids ts := frames.2 g ids ts h after hp

private theorem mapM_represents (f : Nat → Option Term)
    (hf : ∀ id t, f id = some t → Represents g id t)
    (h : ids.mapM f = some ts) : RepresentsList g ids ts := by
  induction ids generalizing ts with
  | nil => simp only [List.mapM_nil, pure, Pure.pure] at h; cases h; exact .nil
  | cons id ids ih =>
      cases ht : f id with
      | none => simp [List.mapM_cons, ht] at h
      | some t =>
          cases hs : ids.mapM f with
          | none => simp [List.mapM_cons, ht, hs] at h
          | some rest =>
              simp only [List.mapM_cons, ht, hs, bind, Option.bind, pure, Pure.pure] at h
              cases h
              exact .cons (hf id t ht) (ih hs)

/-- Successful bounded decoding has the independently defined graph meaning. -/
theorem decode_sound (h : decode fuel g id = some t) : Represents g id t := by
  induction fuel generalizing id t with
  | zero => simp [decode] at h
  | succ fuel ih =>
      cases hn : g[id]? with
      | none => simp [decode, hn] at h
      | some n =>
          cases n with
          | var k => simp [decode, hn] at h; cases h; exact .var hn
          | node op refs =>
              by_cases arity : refs.length = op.arity
              · cases hc : refs.mapM (decode fuel g) with
                | none => simp [decode, hn, arity, hc] at h
                | some children =>
                    simp [decode, hn, arity, hc] at h
                    cases h
                    exact .node hn arity (mapM_represents _ (fun _ _ h => ih h) hc)
              · simp [decode, hn, arity] at h

private theorem completes :
    (∀ g id t, Represents g id t → ∃ bound, ∀ fuel, bound ≤ fuel →
      decode fuel g id = some t) ∧
    (∀ g ids ts, RepresentsList g ids ts → ∃ bound, ∀ fuel, bound ≤ fuel →
      ids.mapM (decode fuel g) = some ts) := by
  constructor
  · intro g id t h
    induction h using Represents.rec
      (motive_2 := fun ids ts _ => ∃ bound, ∀ fuel, bound ≤ fuel →
        ids.mapM (decode fuel g) = some ts)
    case var lookup =>
      refine ⟨1, ?_⟩
      intro fuel bound
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode, lookup]
    case node lookup arity children ih =>
      obtain ⟨bound, ih⟩ := ih
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode, lookup, arity, ih fuel (by omega)]
    case nil => exact ⟨0, fun _ _ => rfl⟩
    case cons h hs ih ihs =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨c, hc⟩ := ihs
      exact ⟨max b c, fun fuel enough => by
        simp [List.mapM_cons, hb fuel (by omega), hc fuel (by omega)]⟩
  · intro g ids ts h
    induction h using RepresentsList.rec
      (motive_1 := fun id t _ => ∃ bound, ∀ fuel, bound ≤ fuel →
        decode fuel g id = some t)
    case var lookup =>
      refine ⟨1, ?_⟩
      intro fuel bound
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode, lookup]
    case node lookup arity children ih =>
      obtain ⟨bound, ih⟩ := ih
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode, lookup, arity, ih fuel (by omega)]
    case nil => exact ⟨0, fun _ _ => rfl⟩
    case cons h hs ih ihs =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨c, hc⟩ := ihs
      exact ⟨max b c, fun fuel enough => by
        simp [List.mapM_cons, hb fuel (by omega), hc fuel (by omega)]⟩

theorem Represents.decode_complete (h : Represents g id t) :
    ∃ bound, ∀ fuel, bound ≤ fuel → decode fuel g id = some t :=
  completes.1 g id t h

theorem RepresentsList.decode_complete (h : RepresentsList g ids ts) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ids.mapM (decode fuel g) = some ts :=
  completes.2 g ids ts h

/-- A graph reference has a single tree meaning, independently of the fuel
used by successful decoders. -/
theorem Represents.unique (h : Represents g id t) (h' : Represents g id u) : t = u := by
  obtain ⟨a, ha⟩ := h.decode_complete
  obtain ⟨b, hb⟩ := h'.decode_complete
  exact Option.some.inj ((ha (max a b) (by omega)).symm.trans
    (hb (max a b) (by omega)))

theorem decode_unique (h : decode fuel g id = some t)
    (h' : decode fuel' g id = some u) : t = u :=
  (decode_sound h).unique (decode_sound h')

/-- Every represented tree has exactly the native constructor's declared
number of children, recursively. This does not impose payload or typing rules. -/
theorem Represents.wellFormed (h : Represents g id t) : t.WellFormed := by
  induction h using Represents.rec
    (motive_2 := fun ids ts _ => ids.length = ts.length ∧ ∀ t ∈ ts, t.WellFormed)
  case var => simp [Term.WellFormed]
  case node lookup arity children ih =>
    simp only [Term.WellFormed]
    exact ⟨ih.1.symm.trans arity, ih.2⟩
  case nil => exact ⟨rfl, by simp⟩
  case cons h hs ih ihs =>
    exact ⟨by simpa only [List.length_cons] using congrArg Nat.succ ihs.1,
      fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ih
        · exact ihs.2 x hx⟩

theorem decode_wellFormed (h : decode fuel g id = some t) : t.WellFormed :=
  (decode_sound h).wellFormed

private theorem mapM_transport {f h : Nat → Option Term}
    (each : ∀ id t, f id = some t → h id = some t)
    (success : ids.mapM f = some ts) : ids.mapM h = some ts := by
  induction ids generalizing ts with
  | nil => simpa only [List.mapM_nil] using success
  | cons id ids ih =>
      cases ht : f id with
      | none => simp [List.mapM_cons, ht] at success
      | some t =>
          cases hs : ids.mapM f with
          | none => simp [List.mapM_cons, ht, hs] at success
          | some rest =>
              simp [List.mapM_cons, ht, hs] at success
              cases success
              simp [List.mapM_cons, each id t ht, ih hs]

/-- Appending nodes preserves success at the exact same depth budget. -/
theorem decode_frame_exact (h : decode fuel g id = some t) (hp : Prefix g after) :
    decode fuel after id = some t := by
  induction fuel generalizing id t with
  | zero => simp [decode] at h
  | succ fuel ih =>
      cases hn : g[id]? with
      | none => simp [decode, hn] at h
      | some n =>
          cases n with
          | var k =>
              simp [decode, hn] at h
              cases h
              simp [decode, hp.lookup hn]
          | node op refs =>
              by_cases arity : refs.length = op.arity
              · cases hc : refs.mapM (decode fuel g) with
                | none => simp [decode, hn, arity, hc] at h
                | some children =>
                    simp [decode, hn, arity, hc] at h
                    cases h
                    have mapped := mapM_transport (fun _ _ h => ih h) hc
                    simp [decode, hp.lookup hn, arity, mapped]
              · simp [decode, hn, arity] at h

/-- Old decoded roots keep their exact tree meanings after append-only work. -/
theorem decode_frame (h : decode fuel g id = some t) (hp : Prefix g after) :
    ∃ bound, ∀ fuel', bound ≤ fuel' → decode fuel' after id = some t :=
  ((decode_sound h).frame hp).decode_complete

/-- Executable graph allocation, with an unchanged prefix and a fresh root. -/
def allocate (g : Arena) (n : Node) : Arena × Nat := (g.push n, g.size)

theorem allocate_prefix (g : Arena) (n : Node) : Prefix g (allocate g n).1 :=
  Prefix.push g n

theorem allocate_fresh (g : Arena) (n : Node) :
    (allocate g n).2 = g.size ∧ (allocate g n).1.size = g.size + 1 := by
  simp [allocate]

mutual
  /-- Emit a tree in postorder. Every edge allocated by this operation points
  backwards; shared input arena nodes keep their original indices. No native
  LIMIT or machine-index truncation is modeled by this pure allocator. -/
  def emit (t : Term) (g : Arena) : Arena × Nat :=
    match t with
    | .var k => allocate g (.var k)
    | .node op args =>
        let result := emitArgs args g
        allocate result.1 (.node op result.2)

  def emitArgs (ts : List Term) (g : Arena) : Arena × List Nat :=
    match ts with
    | [] => (g, [])
    | t :: rest =>
        let head := emit t g
        let tail := emitArgs rest head.1
        (tail.1, head.2 :: tail.2)
end

private theorem emits_prefix :
    (∀ t g, Prefix g (emit t g).1) ∧
    (∀ ts g, Prefix g (emitArgs ts g).1) := by
  constructor
  · intro t
    induction t using Term.rec (motive_2 := fun ts => ∀ g, Prefix g (emitArgs ts g).1)
    case var k => intro g; exact allocate_prefix g (.var k)
    case node op args ih =>
      intro g
      exact (ih g).trans (allocate_prefix _ _)
    case nil => exact Prefix.refl _
    case cons t ts iht ihts g =>
      exact (iht g).trans (ihts _)
  · intro ts
    induction ts using List.rec
    case nil => intro g; exact Prefix.refl _
    case cons t ts ih =>
      intro g
      have head : Prefix g (emit t g).1 := by
        induction t using Term.rec
          (motive_2 := fun ts => ∀ g, Prefix g (emitArgs ts g).1) generalizing g
        case var k => exact allocate_prefix g (.var k)
        case node op args ih => exact (ih g).trans (allocate_prefix _ _)
        case nil => exact Prefix.refl _
        case cons t ts iht ihts g => exact (iht g).trans (ihts _)
      exact head.trans (ih _)

theorem emit_prefix (t : Term) (g : Arena) : Prefix g (emit t g).1 :=
  emits_prefix.1 t g

theorem emitArgs_prefix (ts : List Term) (g : Arena) : Prefix g (emitArgs ts g).1 :=
  emits_prefix.2 ts g

theorem emitArgs_length (ts : List Term) (g : Arena) :
    (emitArgs ts g).2.length = ts.length := by
  induction ts generalizing g with
  | nil => rfl
  | cons t ts ih => simpa only [emitArgs, List.length_cons] using congrArg Nat.succ (ih _)

private theorem emits_sound :
    (∀ t, t.WellFormed → ∀ g, Represents (emit t g).1 (emit t g).2 t) ∧
    (∀ ts, (∀ t ∈ ts, t.WellFormed) → ∀ g,
      RepresentsList (emitArgs ts g).1 (emitArgs ts g).2 ts) := by
  let M := fun t : Term => t.WellFormed → ∀ g,
    Represents (emit t g).1 (emit t g).2 t
  let N := fun ts : List Term => (∀ t ∈ ts, t.WellFormed) → ∀ g,
    RepresentsList (emitArgs ts g).1 (emitArgs ts g).2 ts
  have hv : ∀ k, M (.var k) := by
    intro k _ g
    exact .var Array.getElem?_push_size
  have hn : ∀ op args, N args → M (.node op args) := by
    intro op args ih wf g
    simp only [Term.WellFormed] at wf
    exact .node Array.getElem?_push_size ((emitArgs_length args g).trans wf.1)
      ((ih wf.2 g).frame (Prefix.push _ _))
  have hnil : N [] := fun _ _ => .nil
  have hc : ∀ t ts, M t → N ts → N (t :: ts) := by
    intro t ts iht ihts wf g
    exact .cons ((iht (wf t (by simp)) g).frame (emitArgs_prefix ts _))
      (ihts (fun x hx => wf x (by simp [hx])) _)
  exact ⟨fun t => Term.rec (motive_1 := M) (motive_2 := N) hv hn hnil hc t,
    fun ts => Term.rec_1 (motive_1 := M) (motive_2 := N) hv hn hnil hc ts⟩

theorem emit_sound (wf : t.WellFormed) (g : Arena) :
    Represents (emit t g).1 (emit t g).2 t := emits_sound.1 t wf g

theorem emit_decode (wf : t.WellFormed) (g : Arena) :
    ∃ bound, ∀ fuel, bound ≤ fuel → decode fuel (emit t g).1 (emit t g).2 = some t :=
  (emit_sound wf g).decode_complete

def Node.references : Node → List Nat
  | .var _ => []
  | .node _ refs => refs

/-- All references point to earlier arena entries. This is independent of
variable scoping and constructor arity. -/
def Backward (g : Arena) : Prop :=
  ∀ (id : Nat) (n : Node), g[id]? = some n → ∀ ref ∈ n.references, ref < id

theorem allocate_backward {n : Node} (hg : Backward g)
    (hn : ∀ ref ∈ n.references, ref < g.size) : Backward (allocate g n).1 := by
  intro id node lookup ref member
  simp only [allocate, Array.getElem?_push] at lookup
  by_cases he : id = g.size
  · simp only [he, ↓reduceIte, Option.some.injEq] at lookup
    subst node
    simpa only [he] using hn ref member
  · simp only [he, ↓reduceIte] at lookup
    exact hg id node lookup ref member

theorem emit_root_lt (t : Term) (g : Arena) :
    (emit t g).2 < (emit t g).1.size := by
  cases t <;> simp [emit, allocate]

theorem emitArgs_roots_lt (ts : List Term) (g : Arena) :
    ∀ ref ∈ (emitArgs ts g).2, ref < (emitArgs ts g).1.size := by
  induction ts generalizing g with
  | nil => simp [emitArgs]
  | cons t ts ih =>
      intro ref member
      simp only [emitArgs, List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.lt_of_lt_of_le (emit_root_lt t g) (emitArgs_prefix ts _).size_le
      · exact ih _ ref member

private theorem emits_backward :
    (∀ t g, Backward g → Backward (emit t g).1) ∧
    (∀ ts g, Backward g → Backward (emitArgs ts g).1) := by
  let M := fun t : Term => ∀ g, Backward g → Backward (emit t g).1
  let N := fun ts : List Term => ∀ g, Backward g → Backward (emitArgs ts g).1
  have hv : ∀ k, M (.var k) := by
    intro k g hg
    exact allocate_backward hg (by simp [Node.references])
  have hn : ∀ op args, N args → M (.node op args) := by
    intro op args ih g hg
    exact allocate_backward (ih g hg) (emitArgs_roots_lt args g)
  have hnil : N [] := fun _ hg => hg
  have hc : ∀ t ts, M t → N ts → N (t :: ts) := by
    intro t ts iht ihts g hg
    exact ihts _ (iht g hg)
  exact ⟨fun t => Term.rec (motive_1 := M) (motive_2 := N) hv hn hnil hc t,
    fun ts => Term.rec_1 (motive_1 := M) (motive_2 := N) hv hn hnil hc ts⟩

theorem emit_backward (t : Term) (hg : Backward g) : Backward (emit t g).1 :=
  emits_backward.1 t g hg

/-- Executable tree-mediated arena renaming. It unfolds the selected graph,
uses the full binding-aware tree operation, then appends its result. This is
not asserted to reproduce Core.transform's allocation order or work budget. -/
def rename (fuel : Nat) (g : Arena) (root : Nat) (ρ : Nat → Nat) :
    Option (Arena × Nat) := do
  let t ← decode fuel g root
  some (emit (t.rename ρ) g)

/-- Instantiate variable zero with an arena term and remove its binder.
Capture avoidance includes Lam/Pi bodies and IfLt/IfEq true branches. -/
def substitute (fuel : Nat) (g : Arena) (body value : Nat) : Option (Arena × Nat) := do
  let t ← decode fuel g body
  let a ← decode fuel g value
  some (emit (t.subst (single a)) g)

/-- Nonnegative weakening above a cutoff. Negative native shifts and native
rewrite's no-removal mode are not represented by this particular entry point. -/
def shift (fuel : Nat) (g : Arena) (root amount cutoff : Nat) : Option (Arena × Nat) :=
  rename fuel g root (fun k => if k < cutoff then k else k + amount)

theorem rename_sound {root out : Nat} {ρ : Nat → Nat}
    (h : rename fuel g root ρ = some (after, out)) :
    ∃ t, decode fuel g root = some t ∧ Prefix g after ∧
      Represents after out (t.rename ρ) := by
  cases ht : decode fuel g root with
  | none => simp [rename, ht] at h
  | some t =>
      have he : emit (t.rename ρ) g = (after, out) := by simpa [rename, ht] using h
      have hp := emit_prefix (t.rename ρ) g
      have hr := emit_sound ((decode_wellFormed ht).rename ρ) g
      rw [he] at hp hr
      exact ⟨t, rfl, hp, hr⟩

theorem substitute_sound {body value out : Nat}
    (h : substitute fuel g body value = some (after, out)) :
    ∃ t a, decode fuel g body = some t ∧ decode fuel g value = some a ∧
      Prefix g after ∧ Represents after out (t.subst (single a)) := by
  cases ht : decode fuel g body with
  | none => simp [substitute, ht] at h
  | some t =>
      cases ha : decode fuel g value with
      | none => simp [substitute, ht, ha] at h
      | some a =>
          have he : emit (t.subst (single a)) g = (after, out) := by
            simpa [substitute, ht, ha] using h
          have hp := emit_prefix (t.subst (single a)) g
          have hr := emit_sound ((decode_wellFormed ht).instantiate (decode_wellFormed ha)) g
          rw [he] at hp hr
          exact ⟨t, a, rfl, rfl, hp, hr⟩

theorem shift_sound {root amount cutoff out : Nat}
    (h : shift fuel g root amount cutoff = some (after, out)) :
    ∃ t, decode fuel g root = some t ∧ Prefix g after ∧
      Represents after out (t.rename (fun k => if k < cutoff then k else k + amount)) :=
  rename_sound h

/-- Graph transformation preserves every old root's decoded meaning at its
original depth budget, including the original body and argument. -/
theorem substitute_frame {body value out old : Nat} {oldFuel : Nat} {oldTerm : Term}
    (h : substitute fuel g body value = some (after, out))
    (hold : decode oldFuel g old = some oldTerm) :
    decode oldFuel after old = some oldTerm := by
  obtain ⟨_, _, _, _, hp, _⟩ := substitute_sound h
  exact decode_frame_exact hold hp

theorem rename_frame {root out old : Nat} {ρ : Nat → Nat} {oldFuel : Nat} {oldTerm : Term}
    (h : rename fuel g root ρ = some (after, out))
    (hold : decode oldFuel g old = some oldTerm) :
    decode oldFuel after old = some oldTerm := by
  obtain ⟨_, _, hp, _⟩ := rename_sound h
  exact decode_frame_exact hold hp

theorem substitute_scoped {body value out depth : Nat} {t a : Term}
    (h : substitute fuel g body value = some (after, out))
    (ht : decode fuel g body = some t) (ha : decode fuel g value = some a)
    (hb : t.Scoped (depth + 1)) (hv : a.Scoped depth) :
    ∃ u, Represents after out u ∧ u.Scoped depth := by
  obtain ⟨t', a', ht', ha', _, hr⟩ := substitute_sound h
  have et : t' = t := Option.some.inj (ht'.symm.trans ht)
  have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst t'; subst a'
  exact ⟨_, hr, hb.instantiate hv⟩

theorem rename_scoped {root out source target : Nat} {ρ : Nat → Nat} {t : Term}
    (h : rename fuel g root ρ = some (after, out))
    (ht : decode fuel g root = some t) (hs : t.Scoped source)
    (hρ : Within source target ρ) :
    ∃ u, Represents after out u ∧ u.Scoped target := by
  obtain ⟨t', ht', _, hr⟩ := rename_sound h
  have et : t' = t := Option.some.inj (ht'.symm.trans ht)
  subst t'
  exact ⟨_, hr, hs.rename hρ⟩

theorem substitute_backward {body value out : Nat}
    (h : substitute fuel g body value = some (after, out)) (hg : Backward g) :
    Backward after := by
  cases ht : decode fuel g body with
  | none => simp [substitute, ht] at h
  | some t =>
      cases ha : decode fuel g value with
      | none => simp [substitute, ht, ha] at h
      | some a =>
          have he : emit (t.subst (single a)) g = (after, out) := by
            simpa [substitute, ht, ha] using h
          have hb := emit_backward (t.subst (single a)) hg
          rwa [he] at hb

theorem rename_backward {root out : Nat} {ρ : Nat → Nat}
    (h : rename fuel g root ρ = some (after, out)) (hg : Backward g) :
    Backward after := by
  cases ht : decode fuel g root with
  | none => simp [rename, ht] at h
  | some t =>
      have he : emit (t.rename ρ) g = (after, out) := by simpa [rename, ht] using h
      have hb := emit_backward (t.rename ρ) hg
      rwa [he] at hb

end Jihoo.NativeKernel.NativeArena
