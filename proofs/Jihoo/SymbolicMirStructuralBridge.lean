import Jihoo.SymbolicCoreCompactionTotality
import Jihoo.SizedMirStructuralTotality

/-! Symbolic typing preserves representation types through computed compaction.
Dead aliases remain unconstrained; proof slots disappear. No execution or
compiler-success premise is used. -/
namespace Jihoo.SymbolicMirStructuralBridge
open SymbolicCoreContext SymbolicCoreTyping SymbolicCoreCompaction SizedErasure
open SizedMir SizedMir.Structural

def entryKind : Entry → Option Kind
  | .nat => some .natural
  | .scalar => some .scalar
  | .owner _ => some .pointer
  | _ => none

def resultKind : Result → Kind
  | .scalar => .scalar
  | .owner _ => .pointer

@[simp] theorem resultKind_rename : resultKind (r.rename f) = resultKind r := by
  cases r <;> rfl
@[simp] theorem resultKind_subst : resultKind (r.subst f) = resultKind r := by
  cases r <;> rfl

/-- Live source slots have their representation at the computed lexical rank.
This permits stale dead slots without assigning them a new runtime type. -/
def KindsSupport (ctx : Context) (mask : Mask) (ks : List Kind) : Prop :=
  ∀ k e kind, ctx[k]? = some e → entryKind e = some kind →
    ks[rank mask k]? = some kind

theorem KindsSupport.mapOwners (h : KindsSupport ctx mask ks) :
    KindsSupport (SymbolicCoreContext.mapOwners f ctx) mask ks := by
  intro k e kind lookup typed
  simp only [SymbolicCoreContext.mapOwners, List.getElem?_map] at lookup
  cases he : ctx[k]? with
  | none => simp [he] at lookup
  | some old =>
      simp only [he, Option.map_some, Option.some.injEq] at lookup
      subst e
      apply h k old kind he
      cases old <;> try exact typed
      case owner slot =>
        cases hf : f slot with
        | none => simp [Entry.mapOwner, hf, entryKind] at typed
        | some j => simpa [Entry.mapOwner, hf, entryKind] using typed

theorem KindsSupport.push (h : KindsSupport ctx mask ks)
    (head : ∀ kind, entryKind e = some kind → kind = newKind) :
    KindsSupport (SymbolicCoreContext.push e ctx) (true :: mask) (newKind :: ks) := by
  intro k old kind lookup typed
  cases k with
  | zero =>
      simp only [SymbolicCoreContext.push, List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst old
      have eq : entryKind e = some kind := by cases e <;> exact typed
      simp [head kind eq]
  | succ k =>
      simp only [SymbolicCoreContext.push, List.getElem?_cons_succ, List.getElem?_map] at lookup
      cases he : ctx[k]? with
      | none => simp [he] at lookup
      | some old =>
          simp only [he, Option.map_some, Option.some.injEq] at lookup
          subst_vars
          exact h k old kind he (by cases old <;> exact typed)

theorem KindsSupport.proof (h : KindsSupport ctx mask ks) :
    KindsSupport (SymbolicCoreContext.push (.bound a b) ctx) (false :: mask) ks := by
  intro k old kind lookup typed
  cases k with
  | zero => simp [SymbolicCoreContext.push] at lookup; subst old; contradiction
  | succ k =>
      simp only [SymbolicCoreContext.push, List.getElem?_cons_succ, List.getElem?_map] at lookup
      cases he : ctx[k]? with
      | none => simp [he] at lookup
      | some old =>
          simp only [he, Option.map_some, Option.some.injEq] at lookup
          subst_vars
          exact h k old kind he (by cases old <;> exact typed)

theorem index_typed (rep : DependentBufferIndices.Represents g root e)
    (available : DependentBufferIndices.Available slots e)
    (kept : ∀ k, slots k → mask[k]? = some true)
    (kinds : ∀ k, slots k → ks[rank mask k]? = some .natural) :
    ∃ nt tt, NatErases g mask root nt ∧ NatTyped ks nt ∧
      Erases g mask root tt ∧ Typed ks tt .natural := by
  induction rep generalizing slots mask ks with
  | literal shape bound =>
      exact ⟨_, _, ⟨_, .literal shape bound, .literal⟩, .literal bound,
        .natural shape, .natural bound⟩
  | var shape =>
      cases available with
      | var present => exact ⟨_, _, ⟨_, .var shape, .var (kept _ present)⟩,
          .var (kinds _ present), .var shape (kept _ present), .var (kinds _ present)⟩
  | letE shape lam ty a b ia ib =>
      cases available with
      | letE aa ab =>
          obtain ⟨na, ta, ⟨ea, ra, ca⟩, nta, eta, tta⟩ := ia aa kept kinds
          obtain ⟨nb, tb, ⟨eb, rb, cb⟩, ntb, etb, ttb⟩ := ib ab
            (mask := true :: mask) (ks := .natural :: ks)
            (by intro k hk; cases k with | zero => rfl | succ k => exact kept k hk)
            (by intro k hk; cases k with | zero => rfl | succ k => exact kinds k hk)
          exact ⟨_, _, ⟨_, .letE shape lam ty ra rb, .letE ca cb⟩,
            .letE nta ntb, .app shape lam eta etb, .app tta ttb⟩

theorem Index.typed (h : SymbolicCoreTyping.Index g ctx root e)
    (maskOK : MaskSupports ctx mask) (kinds : KindsSupport ctx mask ks) :
    ∃ nt tt, NatErases g mask root nt ∧ NatTyped ks nt ∧
      Erases g mask root tt ∧ Typed ks tt .natural :=
  index_typed h.represents h.available maskOK.nats (fun k hk => kinds k .nat .natural hk rfl)

theorem Scalar.typed (h : SymbolicCoreTyping.Scalar g ctx root)
    (maskOK : MaskSupports ctx mask) (kinds : KindsSupport ctx mask ks) :
    ∃ term, ScalarErases g mask root term ∧ ScalarTyped ks term := by
  cases h with
  | literal shape bound => exact ⟨_, .literal shape, .literal bound⟩
  | var shape lookup => exact ⟨_, .var shape (maskOK.retained lookup (by simp [EntrySupports])),
      .var (kinds _ _ _ lookup rfl)⟩

theorem typing_erases_typed (typing : Typing g ctx sizes root kind)
    (maskOK : MaskSupports ctx mask) (kinds : KindsSupport ctx mask ks) :
    ∃ term, Erases g mask root term ∧ Typed ks term (resultKind kind) := by
  induction typing generalizing mask ks with
  | literal shape bound => exact ⟨_, .scalar shape, .scalar bound⟩
  | scalar shape lookup => exact ⟨_, .var shape (maskOK.retained lookup (by simp [EntrySupports])),
      .var (kinds _ _ _ lookup rfl)⟩
  | owner shape lookup => exact ⟨_, .var shape (maskOK.retained lookup (by simp [EntrySupports])),
      .var (kinds _ _ _ lookup rfl)⟩
  | ownedLet shape lam arg lookup _ _ body ih =>
      obtain ⟨eb, hb, tb⟩ := ih (maskOK.mapOwners.push (by rfl))
        (kinds.mapOwners.push (newKind := .pointer) (by simp [entryKind]))
      exact ⟨_, .app shape lam (.var arg (maskOK.retained lookup (by simp [EntrySupports]))) hb,
        .app (.var (kinds _ _ _ lookup rfl)) (by simpa using tb)⟩
  | framedApp shape lam _ _ argument body ia ib =>
      obtain ⟨ea, ha, ta⟩ := ia maskOK.mapOwners kinds.mapOwners
      obtain ⟨eb, hb, tb⟩ := ib (maskOK.mapOwners.push (by rfl))
        (kinds.mapOwners.push (newKind := .pointer) (by simp [entryKind]))
      exact ⟨_, .app shape lam ha hb, .app (show Typed ks ea .pointer from ta) (by simpa only [resultKind_rename] using tb)⟩
  | naturalLet shape lam ty arg body ih =>
      obtain ⟨_, ta, _, _, ha, hta⟩ := Index.typed arg maskOK kinds
      obtain ⟨tb, hb, htb⟩ := ih (maskOK.push (by rfl)) (kinds.push (newKind := .natural) (by simp [entryKind]))
      exact ⟨_, .app shape lam ha hb, by simpa using Typed.app hta htb⟩
  | allocate shape lam _ alloc length init body ih =>
      obtain ⟨en, _, hn, tn, _, _⟩ := Index.typed length maskOK kinds
      obtain ⟨ev, hv, tv⟩ := Scalar.typed init maskOK kinds
      obtain ⟨eb, hb, tb⟩ := ih (maskOK.mapOwners.push (by rfl))
        (kinds.mapOwners.push (newKind := .pointer) (by simp [entryKind]))
      exact ⟨_, .app shape lam (.allocate alloc hn hv) hb,
        .app (.allocate tn tv) (by simpa using tb)⟩
  | allocation shape length init =>
      obtain ⟨en, _, hn, tn, _, _⟩ := Index.typed length maskOK kinds
      obtain ⟨ev, hv, tv⟩ := Scalar.typed init maskOK kinds
      exact ⟨_, .allocate shape hn hv, .allocate tn tv⟩
  | free shape owner lookup _ body ih =>
      obtain ⟨eb, hb, tb⟩ := ih maskOK.mapOwners kinds.mapOwners
      exact ⟨_, .free shape owner (maskOK.retained lookup (by simp [EntrySupports])) hb,
        .free (kinds _ _ _ lookup rfl) tb⟩
  | branch shape left right yes no iy ino =>
      obtain ⟨el, _, hl, tl, _, _⟩ := Index.typed left maskOK kinds
      obtain ⟨er, _, hr, tr, _, _⟩ := Index.typed right maskOK kinds
      obtain ⟨ey, hy, ty⟩ := iy (maskOK.push (by rfl)) kinds.proof
      obtain ⟨en, hn, tn⟩ := ino maskOK kinds
      exact ⟨_, .branch shape hl hr hy hn, .ifLt tl tr (by simpa using ty) tn⟩
  | lend shape owner lookup _ _ _ index _ body ih =>
      obtain ⟨ei, _, hi, ti, _, _⟩ := Index.typed index (maskOK.push (bit := true) trivial)
        (kinds.push (newKind := .pointer) (by simp [entryKind]))
      obtain ⟨eb, hb, tb⟩ := ih ((maskOK.push (entry := .scalar) rfl).push (by rfl))
        ((kinds.push (newKind := .scalar) (by simp [entryKind])).push (newKind := .pointer) (by simp [entryKind]))
      exact ⟨_, .lend shape owner (maskOK.retained lookup (by simp [EntrySupports])) hi hb,
        .lend (kinds _ _ _ lookup rfl) ti (by simpa using tb)⟩
  | ownedLend shape owner lookup _ _ length _ _ index _ body ih =>
      obtain ⟨en, _, hn, tn, _, _⟩ := Index.typed length (maskOK.push (bit := true) trivial)
        (kinds.push (newKind := .pointer) (by simp [entryKind]))
      obtain ⟨ei, _, hi, ti, _, _⟩ := Index.typed index (maskOK.push (bit := true) trivial)
        (kinds.push (newKind := .pointer) (by simp [entryKind]))
      obtain ⟨eb, hb, tb⟩ := ih ((maskOK.mapOwners.push (by rfl)).push (by rfl))
        ((kinds.mapOwners.push (newKind := .pointer) (by simp [entryKind])).push
          (newKind := .pointer) (by simp [entryKind]))
      exact ⟨_, .ownedLend shape owner (maskOK.retained lookup (by simp [EntrySupports])) hn hi hb,
        .ownedLend (kinds _ _ _ lookup rfl) tn ti (by simpa using tb)⟩

/-- The same fixed compact term is produced by every sufficient compactor fuel,
and structurally lowers for every local/block base and exit. -/
theorem typing_compiles_structurally (typing : Typing g ctx sizes root kind)
    (maskOK : MaskSupports ctx mask) (kinds : KindsSupport ctx mask ks)
    (same : inputs.length = ks.length) :
    ∃ term bound, Typed ks term (resultKind kind) ∧
      (∀ fuel, bound ≤ fuel → compileTarget g fuel mask root = some term) ∧
      ∀ l b exit, ∃ fragment, SizedMir.Linear.compile inputs ks l b exit term = some fragment := by
  obtain ⟨term, erased, typed⟩ := typing_erases_typed typing maskOK kinds
  obtain ⟨bound, complete⟩ := erased.compileTarget_complete
  exact ⟨term, bound, typed, complete, fun l b exit => typed.total same l b exit⟩

/-- Runtime agreement derives compact representation kinds, including stale
aliases, rather than assuming a new source typing judgment. -/
theorem KindsSupport.of_closing_agrees (closing : Closes ctx closed)
    (agrees : SizedBufferContext.Agrees closed owners env) :
    KindsSupport ctx (compactEnv env).1 ((compactEnv env).2.map kindOf) := by
  intro k e kind lookup typed
  have rel := compactEnv_related env
  have ek : EnvKinds (compactEnv env).2 ((compactEnv env).2.map kindOf) := rfl
  cases e with
  | nat =>
      cases typed
      obtain ⟨n, hn, _⟩ := closing.nat_lookup lookup
      exact ek.lookup (rel.nat_lookup (agrees.nat_lookup _ _ hn))
  | scalar =>
      cases typed
      obtain ⟨v, hv⟩ := agrees.scalar_lookup _ (closing.scalar_lookup lookup)
      exact ek.lookup (rel.scalar_lookup hv)
  | owner slot =>
      cases typed
      obtain ⟨x, _, hx⟩ := agrees.owner_lookup _ _ (closing.owner_lookup lookup)
      exact ek.lookup (rel.owner_lookup hx)
  | bound _ _ => contradiction
  | dead => contradiction

/-- A closing source environment supplies both mask and representation kinds.
Only operand-list length is needed for structural construction; this theorem
does not claim the operands have valid MIR types or that the ABI admits them. -/
theorem typing_compiles_closed (typing : Typing g ctx sizes root kind)
    (closing : Closes ctx closed) (agrees : SizedBufferContext.Agrees closed owners env)
    (same : inputs.length = (compactEnv env).2.length) :
    ∃ term bound, Typed ((compactEnv env).2.map kindOf) term (resultKind kind) ∧
      (∀ fuel, bound ≤ fuel → compileTarget g fuel (compactEnv env).1 root = some term) ∧
      ∀ l b exit, ∃ fragment,
        SizedMir.Linear.compile inputs ((compactEnv env).2.map kindOf) l b exit term = some fragment ∧
        fragment.locals.size = SizedMir.Linear.localCost term ∧
        fragment.blocks.size = SizedMir.Linear.blockCost term := by
  obtain ⟨term, erased, typed⟩ := typing_erases_typed typing
    (MaskSupports.of_closing_agrees closing agrees) (KindsSupport.of_closing_agrees closing agrees)
  obtain ⟨bound, complete⟩ := erased.compileTarget_complete
  exact ⟨term, bound, typed, complete, fun l b exit => typed.total_cost (by simpa using same) l b exit⟩

end Jihoo.SymbolicMirStructuralBridge
