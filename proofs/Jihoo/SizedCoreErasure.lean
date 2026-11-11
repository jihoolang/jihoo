import Jihoo.SizedErasureIndices
import Jihoo.SizedCoreAccounting

/-! Structural erasure of the supported graph grammar. The mask is lexical:
consumed owner aliases are still runtime slots; only proof binders disappear.
Both conditional branches must have structural coverage independently of the
semantic closing-instance typing judgment. -/
namespace Jihoo.SizedErasure
open ScopedLend

inductive Erases (g : Graph.Graph) : Mask → Nat → Term → Prop where
  | scalar : Graph.nodeAt g root = .integer v → Erases g mask root (.scalar v)
  | natural : Graph.nodeAt g root = .natural n → Erases g mask root (.natural n)
  | var : Graph.nodeAt g root = .var k → mask[k]? = some true →
      Erases g mask root (.var (rank mask k))
  | app : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Erases g mask argument ea → Erases g (true :: mask) body eb →
      Erases g mask root (.app ea eb)
  | allocate : Graph.nodeAt g root = .alloc length init →
      NatErases g mask length en → ScalarErases g mask init ev →
      Erases g mask root (.allocate en ev)
  | free : Graph.nodeAt g root = .free owner body →
      Graph.nodeAt g owner = .var k → mask[k]? = some true →
      Erases g mask body eb → Erases g mask root (.free (rank mask k) eb)
  | branch : Graph.nodeAt g root = .ifLt left right yes no →
      NatErases g mask left el → NatErases g mask right er →
      Erases g (false :: mask) yes ey → Erases g mask no en →
      Erases g mask root (.ifLt el er ey en)
  | lend : SizedCoreExecution.ReadLend g root owner refTy index proof ownerTy body →
      Graph.nodeAt g owner = .var k → mask[k]? = some true →
      NatErases g (true :: mask) index ei →
      Erases g (true :: true :: mask) body eb →
      Erases g mask root (.lend (rank mask k) ei eb)
  | ownedLend : SizedCoreExecution.OwnedReadLend g root owner refTy length index proof resultTy ownerTy body →
      Graph.nodeAt g owner = .var k → mask[k]? = some true →
      NatErases g (true :: mask) length en → NatErases g (true :: mask) index ei →
      Erases g (true :: true :: mask) body eb →
      Erases g mask root (.ownedLend (rank mask k) en ei eb)

/-- Compact execution reconstructs an execution of the original graph with
exactly the same dynamic lengths, events and heap. No source run is assumed. -/
theorem Erases.backward (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) (run : Eval runtime term s value events t) :
    SizedCoreExecution.Eval g env root s value.embed events t := by
  induction erased generalizing env runtime s value events t with
  | scalar shape => cases run; exact .scalar shape
  | natural shape => cases run; exact .natural shape
  | var shape retained =>
      cases run with
      | var lookup => exact .var shape ((related.retained_lookup_iff retained).mpr lookup)
  | app shape lam first last ihf ihl =>
      cases run with
      | app argument body =>
          exact .app shape lam (ihf related argument) (ihl (related.consKeep _) body)
  | allocate shape length init =>
      cases run with
      | allocate lengthRun initRun =>
          exact .allocate shape (length.backward related lengthRun) (init.backward related initRun)
  | free shape variableShape retained body ih =>
      cases run with
      | free lookup suffix =>
          exact .free shape variableShape ((related.retained_lookup_iff retained).mpr lookup) (ih related suffix)
  | branch shape left right yes no iy ino =>
      cases run with
      | yes a b bound suffix =>
          exact .yes shape (left.backward related a) (right.backward related b) bound (iy related.consGhost suffix)
      | no a b bound suffix =>
          exact .no shape (left.backward related a) (right.backward related b) bound (ino related suffix)
  | lend shape variableShape retained index body ih =>
      cases run with
      | lend lookup indexRun suffix =>
          exact .lend shape variableShape ((related.retained_lookup_iff retained).mpr lookup)
            (index.backward (related.consKeep (.borrow _)) indexRun) (ih ((related.consKeep (.scalar _)).consKeep (.owner _)) suffix)
  | ownedLend shape variableShape retained length index body ih =>
      cases run with
      | ownedLend lookup indexRun lengthRun suffix =>
          exact .ownedLend shape variableShape ((related.retained_lookup_iff retained).mpr lookup)
            (index.backward (related.consKeep (.borrow _)) indexRun) (length.backward (related.consKeep (.borrow _)) lengthRun)
            (ih ((related.consKeep (.owner _)).consKeep (.owner _)) suffix)

end Jihoo.SizedErasure
