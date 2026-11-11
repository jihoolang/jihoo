import Jihoo.SymbolicCoreTyping
import Jihoo.SizedCoreErasure

/-! Structural compaction coverage for symbolic Buffer typing. Dead source
slots may still be retained runtime aliases, so their mask bit is unconstrained. -/
namespace Jihoo.SymbolicCoreCompaction
open ScopedLend SymbolicCoreContext SymbolicCoreTyping SizedErasure
open DependentBufferIndices (Expr Available)

def EntrySupports : Entry → Option Bool → Prop
  | .dead, _ => True
  | .bound _ _, keep => keep = some false
  | _, keep => keep = some true

/-- Only observable lexical slots constrain the mask. Agreement deliberately
places no length or existence requirement on dead slots. -/
def MaskSupports (ctx : Context) (mask : Mask) : Prop :=
  ∀ (k : Nat) entry, ctx[k]? = some entry → EntrySupports entry mask[k]?

theorem MaskSupports.retained {k : Nat} (h : MaskSupports ctx mask)
    (lookup : ctx[k]? = some entry) (live : ∀ bit, EntrySupports entry bit → bit = some true) :
    mask[k]? = some true := live _ (h k entry lookup)

theorem MaskSupports.push (h : MaskSupports ctx mask) (head : EntrySupports entry (some bit)) :
    MaskSupports (SymbolicCoreContext.push entry ctx) (bit :: mask) := by
  intro k e lookup
  cases k with
  | zero =>
      simp only [SymbolicCoreContext.push, List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst e
      cases entry <;> exact head
  | succ k =>
      simp only [SymbolicCoreContext.push, List.getElem?_cons_succ, List.getElem?_map] at lookup
      cases he : ctx[k]? with
      | none => simp [he] at lookup
      | some old =>
          simp only [he, Option.map_some, Option.some.injEq] at lookup
          subst e
          have hold := h k old he
          cases old <;> exact hold

theorem MaskSupports.mapOwners (h : MaskSupports ctx mask) :
    MaskSupports (mapOwners f ctx) mask := by
  intro k e lookup
  simp only [SymbolicCoreContext.mapOwners, List.getElem?_map] at lookup
  cases he : ctx[k]? with
  | none => simp [he] at lookup
  | some old =>
      simp only [he, Option.map_some, Option.some.injEq] at lookup
      subst e
      have hold := h k old he
      cases old <;> try exact hold
      simp only [Entry.mapOwner]
      cases f _ <;> simp_all [EntrySupports]

theorem MaskSupports.nats (h : MaskSupports ctx mask) :
    ∀ k, natSlots ctx k → mask[k]? = some true := by
  intro k hk
  exact h.retained hk (by simp [EntrySupports])

private def retainedValue : SizedBufferContext.Value → Bool
  | .ghost => false
  | _ => true

private theorem compactEnv_lookup {env : SizedBufferContext.Env} {k : Nat}
    (lookup : env[k]? = some value) :
    (compactEnv env).1[k]? = some (retainedValue value) := by
  induction env generalizing k with
  | nil => simp at lookup
  | cons v rest ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst value
          cases v <;> rfl
      | succ k =>
          have tail := ih lookup
          cases v <;> exact tail

/-- Existing closing and runtime agreement suffice, including stale aliases
and unconstrained dead slots; no compiler-success or execution premise. -/
theorem MaskSupports.of_closing_agrees (closing : Closes ctx closed)
    (agrees : SizedBufferContext.Agrees closed owners env) :
    MaskSupports ctx (compactEnv env).1 := by
  intro k entry lookup
  obtain ⟨value, hv, hc⟩ := closing.lookup lookup
  cases entry with
  | dead => trivial
  | nat =>
      cases value <;> simp only [Entry.Closes] at hc
      all_goals try contradiction
      exact compactEnv_lookup (agrees.nat_lookup _ _ hv)
  | scalar =>
      cases value <;> simp only [Entry.Closes] at hc
      all_goals try contradiction
      obtain ⟨v, he⟩ := agrees.scalar_lookup _ hv
      exact compactEnv_lookup he
  | owner slot =>
      cases value <;> simp only [Entry.Closes] at hc
      all_goals try contradiction
      obtain ⟨x, _, he⟩ := agrees.owner_lookup _ _ hv
      exact compactEnv_lookup he
  | bound a b =>
      cases value <;> simp only [Entry.Closes] at hc
      all_goals try contradiction
      exact compactEnv_lookup (agrees.bound_lookup _ _ hv)

theorem available_erases (available : Available slots e)
    (kept : ∀ k, slots k → mask[k]? = some true) : ∃ term, EraseNat mask e term := by
  induction available generalizing mask with
  | literal => exact ⟨_, .literal⟩
  | var hk => exact ⟨_, .var (kept _ hk)⟩
  | letE a b ia ib =>
      obtain ⟨ea, ha⟩ := ia kept
      obtain ⟨eb, hb⟩ := ib (mask := true :: mask) (by
        intro k hk
        cases k with
        | zero => rfl
        | succ k => exact kept k hk)
      exact ⟨_, .letE ha hb⟩

theorem index_erases (index : SymbolicCoreTyping.Index g ctx root e)
    (supported : MaskSupports ctx mask) : ∃ term, NatErases g mask root term := by
  obtain ⟨term, erased⟩ := available_erases index.available supported.nats
  exact ⟨term, e, index.represents, erased⟩

theorem scalar_erases (scalar : Scalar g ctx root) (supported : MaskSupports ctx mask) :
    ∃ term, ScalarErases g mask root term := by
  cases scalar with
  | literal shape _ => exact ⟨_, .literal shape⟩
  | var shape lookup => exact ⟨_, .var shape (supported.retained lookup (by simp [EntrySupports]))⟩

/-- A compact natural expression is also covered by ordinary term erasure. -/
theorem nat_term_erases (h : NatErases g mask root term) : ∃ target, Erases g mask root target := by
  obtain ⟨e, represented, erased⟩ := h
  induction represented generalizing mask term with
  | literal shape _ => exact ⟨_, .natural shape⟩
  | var shape => cases erased with | var kept => exact ⟨_, .var shape kept⟩
  | letE shape lam ty a b ia ib =>
      cases erased with
      | letE ea eb =>
          obtain ⟨ta, ha⟩ := ia ea
          obtain ⟨tb, hb⟩ := ib eb
          exact ⟨_, .app shape lam ha hb⟩

theorem typing_erases (typing : Typing g ctx sizes root kind)
    (supported : MaskSupports ctx mask) : ∃ term, Erases g mask root term := by
  induction typing generalizing mask with
  | literal shape _ => exact ⟨_, .scalar shape⟩
  | scalar shape lookup => exact ⟨_, .var shape (supported.retained lookup (by simp [EntrySupports]))⟩
  | owner shape lookup => exact ⟨_, .var shape (supported.retained lookup (by simp [EntrySupports]))⟩
  | ownedLet shape lam arg lookup _ _ body ih =>
      obtain ⟨eb, hb⟩ := ih (supported.mapOwners.push (by rfl))
      exact ⟨_, .app shape lam (.var arg (supported.retained lookup (by simp [EntrySupports]))) hb⟩
  | naturalLet shape lam ty arg body ih =>
      obtain ⟨ea, ha⟩ := index_erases arg supported
      obtain ⟨ta, hta⟩ := nat_term_erases ha
      obtain ⟨tb, htb⟩ := ih (supported.push (by rfl))
      exact ⟨_, .app shape lam hta htb⟩
  | allocate shape lam _ alloc length init body ih =>
      obtain ⟨en, hn⟩ := index_erases length supported
      obtain ⟨ev, hv⟩ := scalar_erases init supported
      obtain ⟨eb, hb⟩ := ih (supported.mapOwners.push (by rfl))
      exact ⟨_, .app shape lam (.allocate alloc hn hv) hb⟩
  | allocation shape length init =>
      obtain ⟨en, hn⟩ := index_erases length supported
      obtain ⟨ev, hv⟩ := scalar_erases init supported
      exact ⟨_, .allocate shape hn hv⟩
  | free shape owner lookup _ body ih =>
      obtain ⟨eb, hb⟩ := ih supported.mapOwners
      exact ⟨_, .free shape owner (supported.retained lookup (by simp [EntrySupports])) hb⟩
  | branch shape left right yes no iy ino =>
      obtain ⟨el, hl⟩ := index_erases left supported
      obtain ⟨er, hr⟩ := index_erases right supported
      obtain ⟨ey, hy⟩ := iy (supported.push (by rfl))
      obtain ⟨en, hn⟩ := ino supported
      exact ⟨_, .branch shape hl hr hy hn⟩
  | lend shape owner lookup _ _ _ index _ body ih =>
      obtain ⟨ei, hi⟩ := index_erases index (supported.push (bit := true) trivial)
      obtain ⟨eb, hb⟩ := ih ((supported.push (by rfl)).push (by rfl))
      exact ⟨_, .lend shape owner (supported.retained lookup (by simp [EntrySupports])) hi hb⟩

end Jihoo.SymbolicCoreCompaction
