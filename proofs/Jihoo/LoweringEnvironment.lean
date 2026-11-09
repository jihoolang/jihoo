import Jihoo.QuantityRuntimeSlots

/-! Capture layout used when lowering a recursion into a generated function.
The native implementation is trusted to supply the right descriptor and order.
This models ghost holes, scalar operands and a recursive hypothesis's nonempty
node-plus-extra operand block. Types, function IDs and lease validity are absent. -/
namespace Jihoo.LoweringEnvironment

inductive Shape where
  | ghost | value | hypothesis (extra : Nat)
  deriving DecidableEq, Repr

inductive Slot (α : Type u) where
  | ghost | value (a : α) | hypothesis (node : α) (extra : List α)
  deriving DecidableEq, Repr

def Slot.shape : Slot α → Shape
  | .ghost => .ghost
  | .value _ => .value
  | .hypothesis _ extra => .hypothesis extra.length

def Slot.operands : Slot α → List α
  | .ghost => []
  | .value a => [a]
  | .hypothesis node extra => node :: extra

def layout (env : List (Slot α)) : List Shape := env.map Slot.shape

def pack (env : List (Slot α)) : List α := env.flatMap Slot.operands

/-- Consume exactly n operands, rejecting a truncated block. -/
def readBlock : Nat → List α → Option (List α × List α)
  | 0, input => some ([], input)
  | _ + 1, [] => none
  | n + 1, a :: input => do
      let (xs, rest) ← readBlock n input
      return (a :: xs, rest)

/-- Rebuild original slots while consuming consecutive runtime operands.
A hypothesis always consumes a node before its extra capture operands. -/
def rebuild : List Shape → List α → Option (List (Slot α) × List α)
  | [], input => some ([], input)
  | .ghost :: shapes, input => do
      let (env, rest) ← rebuild shapes input
      return (.ghost :: env, rest)
  | .value :: _, [] => none
  | .value :: shapes, a :: input => do
      let (env, rest) ← rebuild shapes input
      return (.value a :: env, rest)
  | .hypothesis _ :: _, [] => none
  | .hypothesis n :: shapes, node :: input => do
      let (extra, next) ← readBlock n input
      let (env, rest) ← rebuild shapes next
      return (.hypothesis node extra :: env, rest)

theorem readBlock_append (xs tail : List α) :
    readBlock xs.length (xs ++ tail) = some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [readBlock, ih]

theorem readBlock_sound (h : readBlock n input = some (xs, tail)) :
    xs.length = n ∧ input = xs ++ tail := by
  induction n generalizing input xs with
  | zero => simp [readBlock] at h; rcases h with ⟨rfl, rfl⟩; simp
  | succ n ih =>
      cases input with
      | nil => simp [readBlock] at h
      | cons a input =>
          cases hb : readBlock n input with
          | none => simp [readBlock, hb] at h
          | some pair =>
              rcases pair with ⟨ys, rest⟩
              simp [readBlock, hb] at h
              rcases h with ⟨rfl, rfl⟩
              obtain ⟨hl, he⟩ := ih hb
              simp [hl, he]

/-- The unconsumed suffix is retained exactly, so applied arguments are not
mistaken for capture operands. -/
theorem rebuild_pack (env : List (Slot α)) (tail : List α) :
    rebuild (layout env) (pack env ++ tail) = some (env, tail) := by
  induction env with
  | nil => rfl
  | cons slot env ih =>
      simp only [layout, pack] at ih
      cases slot <;> simp [layout, pack, Slot.shape, Slot.operands, rebuild,
        List.append_assoc, readBlock_append, ih]

/-- Successful decoding consumes exactly the payload described by the supplied
layout and produces that layout, not an equivalent or guessed one. -/
theorem rebuild_sound (h : rebuild shapes input = some (env, tail)) :
    layout env = shapes ∧ input = pack env ++ tail := by
  induction shapes generalizing input env with
  | nil => simp [rebuild] at h; rcases h with ⟨rfl, rfl⟩; simp [layout, pack]
  | cons shape shapes ih =>
      cases shape with
      | ghost =>
          cases hb : rebuild shapes input with
          | none => simp [rebuild, hb] at h
          | some pair =>
              rcases pair with ⟨es, rest⟩
              simp [rebuild, hb] at h
              rcases h with ⟨rfl, rfl⟩
              simpa [layout, pack, Slot.shape, Slot.operands] using ih hb
      | value =>
          cases input with
          | nil => simp [rebuild] at h
          | cons a input =>
              cases hb : rebuild shapes input with
              | none => simp [rebuild, hb] at h
              | some pair =>
                  rcases pair with ⟨es, rest⟩
                  simp [rebuild, hb] at h
                  rcases h with ⟨rfl, rfl⟩
                  obtain ⟨hl, he⟩ := ih hb
                  simp only [layout] at hl
                  simp [layout, pack, Slot.shape, Slot.operands, hl, he]
      | hypothesis n =>
          cases input with
          | nil => simp [rebuild] at h
          | cons node input =>
              cases hx : readBlock n input with
              | none => simp [rebuild, hx] at h
              | some pair =>
                  rcases pair with ⟨extra, next⟩
                  cases hb : rebuild shapes next with
                  | none => simp [rebuild, hx, hb] at h
                  | some pair =>
                      rcases pair with ⟨es, rest⟩
                      simp [rebuild, hx, hb] at h
                      rcases h with ⟨rfl, rfl⟩
                      obtain ⟨hn, hx⟩ := readBlock_sound hx
                      obtain ⟨hl, he⟩ := ih hb
                      simp only [layout] at hl
                      simp [layout, pack, Slot.shape, Slot.operands, hn, hl, hx, he,
                        List.append_assoc]

/-- Recovering an environment requires its authentic layout; flattening alone
is not injective (ghost slots and hypothesis boundaries would be lost). -/
theorem pack_injective (hl : layout a = layout b) (hp : pack a = pack b) : a = b := by
  have ha := rebuild_pack a []
  have hb := rebuild_pack b []
  rw [hl, hp] at ha
  have same := ha.symm.trans hb
  exact (Prod.mk.inj (Option.some.inj same)).1

/-- The recursion's own node occupies the first call argument; captures occupy
the following prefix, leaving all explicitly applied arguments untouched. -/
theorem call_frame (node : α) (env : List (Slot α)) (applied : List α) :
    rebuild (layout env) (List.tail (node :: (pack env ++ applied))) = some (env, applied) :=
  rebuild_pack env applied



/-- A complete capture frame must neither truncate nor append operands. -/
def decode (shapes : List Shape) (input : List α) : Option (List (Slot α)) := do
  let (env, tail) ← rebuild shapes input
  if tail.isEmpty then some env else none

theorem decode_iff : decode shapes input = some env ↔
    layout env = shapes ∧ pack env = input := by
  constructor
  · intro h
    cases hr : rebuild shapes input with
    | none => simp [decode, hr] at h
    | some pair =>
        rcases pair with ⟨out, tail⟩
        cases tail with
        | cons a tail => simp [decode, hr] at h
        | nil =>
            simp [decode, hr] at h
            subst out
            obtain ⟨hl, he⟩ := rebuild_sound hr
            exact ⟨hl, by simpa using he.symm⟩
  · rintro ⟨hl, hp⟩
    subst shapes
    subst input
    have hr := rebuild_pack env []
    simp only [List.append_nil] at hr
    simp [decode, hr]

def Shape.width : Shape → Nat
  | .ghost => 0 | .value => 1 | .hypothesis n => n + 1

theorem operand_count (env : List (Slot α)) :
    (pack env).length = ((layout env).map Shape.width).sum := by
  induction env with
  | nil => rfl
  | cons slot env ih =>
      simp only [pack, layout] at ih
      cases slot <;> simp [pack, layout, Slot.operands, Slot.shape, Shape.width, ih,
        Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

theorem decode_count (h : decode shapes input = some env) :
    input.length = (shapes.map Shape.width).sum := by
  obtain ⟨hl, hp⟩ := decode_iff.mp h
  rw [← hp, operand_count, hl]

/-- Native storage is oldest-binder first and includes ghost holes. -/
def nativeLookup (env : List (Slot α)) (k : Nat) : Option (Slot α) :=
  if k < env.length then env[env.length - 1 - k]? else none

/-- The native subtraction is guarded: out-of-range indices cannot saturate
at zero and accidentally read the oldest binding. -/
theorem native_lookup_reverse (env : List (Slot α)) (k : Nat) :
    nativeLookup env k = env.reverse[k]? := by
  by_cases hk : k < env.length
  · simp only [nativeLookup, hk, ↓reduceIte]
    exact (List.getElem?_reverse hk).symm
  · have ho : env.reverse.length ≤ k := by simp only [List.length_reverse]; omega
    simp only [nativeLookup, hk, ↓reduceIte]
    exact (List.getElem?_eq_none ho).symm

theorem native_lookup_newest (env : List (Slot α)) (slot : Slot α) :
    nativeLookup (env ++ [slot]) 0 = some slot := by
  simp [native_lookup_reverse]

theorem native_lookup_outer (env : List (Slot α)) (slot : Slot α) (k : Nat) :
    nativeLookup (env ++ [slot]) (k + 1) = nativeLookup env k := by
  simp [native_lookup_reverse]

/-- An authentic capture layout and complete operand frame recover every
original slot, including hypothesis grouping and ghost holes. -/
theorem decoded_lookup (h : decode (layout original) (pack original) = some restored) :
    nativeLookup restored k = nativeLookup original k := by
  obtain ⟨hl, hp⟩ := decode_iff.mp h
  have same : restored = original := pack_injective hl hp
  rw [same]



/-- Interpreting a callee's parameter references preserves hypothesis grouping. -/
def Slot.map (f : α → β) : Slot α → Slot β
  | .ghost => .ghost
  | .value a => .value (f a)
  | .hypothesis node extra => .hypothesis (f node) (extra.map f)

theorem layout_map (env : List (Slot α)) (f : α → β) :
    layout (env.map (Slot.map f)) = layout env := by
  induction env with
  | nil => rfl
  | cons slot env ih =>
      change (Slot.shape (Slot.map f slot)) :: layout (env.map (Slot.map f)) =
        slot.shape :: layout env
      rw [ih]
      cases slot <;> simp [Slot.map, Slot.shape]

theorem pack_map (env : List (Slot α)) (f : α → β) :
    pack (env.map (Slot.map f)) = (pack env).map f := by
  induction env with
  | nil => rfl
  | cons slot env ih =>
      simp only [pack] at ih
      cases slot <;> simp [pack, Slot.map, Slot.operands, ih]

/-- The generated callee may use fresh parameter references. If its layout is
correct and positional parameter assignment delivers the caller operands, then
interpreting its reconstructed slots recovers the entire caller environment.
No native allocator, type observer or MIR call semantics is assumed verified. -/
theorem callee_environment (decoded : decode (layout caller) references = some callee)
    (assigned : references.map evaluate = pack caller) :
    callee.map (Slot.map evaluate) = caller := by
  obtain ⟨hl, hp⟩ := decode_iff.mp decoded
  apply pack_injective
  · rw [layout_map, hl]
  · rw [pack_map, hp, assigned]

theorem callee_lookup (decoded : decode (layout caller) references = some callee)
    (assigned : references.map evaluate = pack caller) :
    nativeLookup (callee.map (Slot.map evaluate)) k = nativeLookup caller k := by
  rw [callee_environment decoded assigned]

end Jihoo.LoweringEnvironment
