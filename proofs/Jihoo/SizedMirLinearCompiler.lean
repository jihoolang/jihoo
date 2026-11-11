import Jihoo.SizedMirAllocation
import Jihoo.SizedMirBranchSteps
import Jihoo.SizedMirKinds

/-! Structural construction of branching compact programs. Pure values are
operand aliases; applications concatenate generated fragments and Free retains
its lexical environment. Lends generate pointer reads; owned lends additionally
allocate and fill a fresh buffer. Conditionals use typed common-result locals. -/
namespace Jihoo.SizedMir.Linear
open BoundedMir
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure Fragment where
  locals : Array Ty
  blocks : Array Block
  result : Operand
  deriving DecidableEq, Repr

def localCost : SizedErasure.Term → Nat
  | .ifLt _ _ yes no => 2 + localCost yes + localCost no
  | .allocate _ _ => 10
  | .app argument body => localCost argument + localCost body
  | .free _ body => 1 + localCost body
  | .lend _ _ body => 2 + localCost body
  | .ownedLend _ _ _ body => 12 + localCost body
  | _ => 0

def blockCost : SizedErasure.Term → Nat
  | .ifLt _ _ yes no => 3 + blockCost yes + blockCost no
  | .allocate _ _ => 6
  | .app argument body => blockCost argument + blockCost body
  | .free _ body => 1 + blockCost body
  | .lend _ _ body => 1 + blockCost body
  | .ownedLend _ _ _ body => 7 + blockCost body
  | _ => 0

def entry (base exit : Nat) (term : SizedErasure.Term) : Nat :=
  if blockCost term = 0 then exit else base

def pureFragment (op : Operand) : Fragment := ⟨#[], #[], op⟩
def allocationFragment (localBase blockBase exit : Nat) (length fill : Operand) : Fragment :=
  ⟨Allocation.roleTypes, Allocation.fragmentBlocks localBase blockBase exit length fill,
    .copy ⟨localBase + 4, false⟩⟩
def appendFragment (first last : Fragment) : Fragment :=
  ⟨first.locals ++ last.locals, first.blocks ++ last.blocks, last.result⟩
def freeBlock (localBase : Nat) (owner : Operand) (next : Nat) : Block :=
  ⟨#[], .free owner ⟨localBase, false⟩ next⟩
def freeFragment (localBase : Nat) (owner : Operand) (next : Nat) (body : Fragment) : Fragment :=
  ⟨#[.unit] ++ body.locals, #[freeBlock localBase owner next] ++ body.blocks, body.result⟩

/-- Read one cell through a fresh pointer, leaving the owner's operand intact. -/
def readBlock (localBase : Nat) (owner index : Operand) (next : Nat) : Block :=
  ⟨#[⟨⟨localBase, false⟩, .offset owner index⟩,
      ⟨⟨localBase + 1, false⟩, .use (.copy ⟨localBase, true⟩)⟩], .goto next⟩
def readFragment (localBase : Nat) (owner index : Operand) (next : Nat) : Fragment :=
  ⟨#[.ptr, .i64], #[readBlock localBase owner index next], .copy ⟨localBase + 1, false⟩⟩
def lendFragment (l : Nat) (owner index : Operand) (next : Nat) (body : Fragment) : Fragment :=
  appendFragment (readFragment l owner index next) body
def ownedLendFragment (l b : Nat) (owner length index : Operand) (next : Nat)
    (body : Fragment) : Fragment :=
  appendFragment (readFragment l owner index (b + 1))
    (appendFragment (allocationFragment (l + 2) (b + 1) next length (.copy ⟨l + 1, false⟩)) body)

def branchFragment (l _b exit : Nat) (kind : Kind) (left right : Operand)
    (yesEntry noEntry : Nat) (yes no : Fragment) : Fragment :=
  ⟨(#[.bool, kind.ty] ++ yes.locals) ++ no.locals,
    (#[Branch.decisionBlock l left right yesEntry noEntry,
       Branch.joinBlock (l + 1) yes.result exit,
       Branch.joinBlock (l + 1) no.result exit] ++ yes.blocks) ++ no.blocks,
    .copy ⟨l + 1, false⟩⟩

def compile (inputs : List Operand) (kinds : List Kind) (localBase blockBase exit : Nat) :
    SizedErasure.Term → Option Fragment
  | .scalar v => if v < scalarBound then some (pureFragment (.constant (.i64 v))) else none
  | .natural n => if n < wordBound then some (pureFragment (.constant (.u64 n))) else none
  | .var k => (inputs[k]?).map pureFragment
  | .allocate length fill => do
      let lengthOp ← lowerNat inputs length
      let fillOp ← lowerScalar inputs fill
      return allocationFragment localBase blockBase exit lengthOp fillOp
  | .app argument body => do
      let argumentKind ← inferKind kinds argument
      let first ← compile inputs kinds localBase blockBase
        (entry (blockBase + blockCost argument) exit body) argument
      let last ← compile (first.result :: inputs) (argumentKind :: kinds) (localBase + localCost argument)
        (blockBase + blockCost argument) exit body
      return appendFragment first last
  | .free k body => do
      let owner ← inputs[k]?
      let last ← compile inputs kinds (localBase + 1) (blockBase + 1) exit body
      return freeFragment localBase owner (entry (blockBase + 1) exit body) last
  | .lend k index body => do
      let owner ← inputs[k]?
      let indexOp ← lowerNat (owner :: inputs) index
      let last ← compile (owner :: .copy ⟨localBase + 1, false⟩ :: inputs) (.pointer :: .scalar :: kinds)
        (localBase + 2) (blockBase + 1) exit body
      return lendFragment localBase owner indexOp (entry (blockBase + 1) exit body) last
  | .ownedLend k length index body => do
      let owner ← inputs[k]?
      let lengthOp ← lowerNat (owner :: inputs) length
      let indexOp ← lowerNat (owner :: inputs) index
      let last ← compile (owner :: .copy ⟨localBase + 6, false⟩ :: inputs) (.pointer :: .pointer :: kinds)
        (localBase + 12) (blockBase + 7) exit body
      return ownedLendFragment localBase blockBase owner lengthOp indexOp
        (entry (blockBase + 7) exit body) last
  | .ifLt left right yes no => do
      let leftOp ← lowerNat inputs left
      let rightOp ← lowerNat inputs right
      let kind ← inferKind kinds yes
      let noKind ← inferKind kinds no
      if kind = noKind then do
        let yesCode ← compile inputs kinds (localBase + 2) (blockBase + 3) (blockBase + 1) yes
        let noCode ← compile inputs kinds (localBase + 2 + localCost yes)
          (blockBase + 3 + blockCost yes) (blockBase + 2) no
        return branchFragment localBase blockBase exit kind leftOp rightOp
          (entry (blockBase + 3) (blockBase + 1) yes)
          (entry (blockBase + 3 + blockCost yes) (blockBase + 2) no) yesCode noCode
      else none

inductive Compiles : List Operand → List Kind → Nat → Nat → Nat → SizedErasure.Term → Fragment → Prop where
  | scalar : v < scalarBound → Compiles inputs kinds l b exit (.scalar v) (pureFragment (.constant (.i64 v)))
  | natural : n < wordBound → Compiles inputs kinds l b exit (.natural n) (pureFragment (.constant (.u64 n)))
  | var : inputs[k]? = some op → Compiles inputs kinds l b exit (.var k) (pureFragment op)
  | allocate : lowerNat inputs length = some lengthOp → lowerScalar inputs fill = some fillOp →
      Compiles inputs kinds l b exit (.allocate length fill) (allocationFragment l b exit lengthOp fillOp)
  | app : inferKind kinds argument = some argumentKind → Compiles inputs kinds l b (entry (b + blockCost argument) exit body) argument first →
      Compiles (first.result :: inputs) (argumentKind :: kinds) (l + localCost argument) (b + blockCost argument) exit body last →
      Compiles inputs kinds l b exit (.app argument body) (appendFragment first last)
  | free : inputs[k]? = some owner → Compiles inputs kinds (l + 1) (b + 1) exit body last →
      Compiles inputs kinds l b exit (.free k body) (freeFragment l owner (entry (b + 1) exit body) last)
  | lend : inputs[k]? = some owner → lowerNat (owner :: inputs) index = some indexOp →
      Compiles (owner :: .copy ⟨l + 1, false⟩ :: inputs) (.pointer :: .scalar :: kinds) (l + 2) (b + 1) exit body last →
      Compiles inputs kinds l b exit (.lend k index body)
        (lendFragment l owner indexOp (entry (b + 1) exit body) last)
  | ownedLend : inputs[k]? = some owner → lowerNat (owner :: inputs) length = some lengthOp →
      lowerNat (owner :: inputs) index = some indexOp →
      Compiles (owner :: .copy ⟨l + 6, false⟩ :: inputs) (.pointer :: .pointer :: kinds) (l + 12) (b + 7) exit body last →
      Compiles inputs kinds l b exit (.ownedLend k length index body)
        (ownedLendFragment l b owner lengthOp indexOp (entry (b + 7) exit body) last)
  | ifLt : lowerNat inputs left = some leftOp → lowerNat inputs right = some rightOp →
      inferKind kinds yes = some kind → inferKind kinds no = some kind →
      Compiles inputs kinds (l + 2) (b + 3) (b + 1) yes yesCode →
      Compiles inputs kinds (l + 2 + localCost yes) (b + 3 + blockCost yes) (b + 2) no noCode →
      Compiles inputs kinds l b exit (.ifLt left right yes no)
        (branchFragment l b exit kind leftOp rightOp (entry (b + 3) (b + 1) yes)
          (entry (b + 3 + blockCost yes) (b + 2) no) yesCode noCode)

theorem compile_sound (success : compile inputs kinds l b exit term = some fragment) :
    Compiles inputs kinds l b exit term fragment := by
  induction term generalizing inputs kinds l b exit fragment with
  | scalar v =>
    simp only [compile] at success
    split at success
    · cases success; exact .scalar ‹_›
    · contradiction
  | natural n =>
    simp only [compile] at success
    split at success
    · cases success; exact .natural ‹_›
    · contradiction
  | var k =>
    cases h : inputs[k]? with
    | none => simp [compile, h] at success
    | some op => simp [compile, h] at success; subst fragment; exact .var h
  | allocate length fill =>
    cases hn : lowerNat inputs length with
    | none => simp [compile, hn] at success
    | some lengthOp =>
      cases hf : lowerScalar inputs fill with
      | none => simp [compile, hn, hf] at success
      | some fillOp => simp [compile, hn, hf] at success; subst fragment; exact .allocate hn hf
  | app argument body firstIH lastIH =>
    cases hk : inferKind kinds argument with
    | none => simp [compile, hk] at success
    | some argumentKind =>
      cases hf : compile inputs kinds l b (entry (b + blockCost argument) exit body) argument with
      | none => simp [compile, hk, hf] at success
      | some first =>
        cases hl : compile (first.result :: inputs) (argumentKind :: kinds) (l + localCost argument) (b + blockCost argument) exit body with
        | none => simp [compile, hk, hf, hl] at success
        | some last =>
          simp [compile, hk, hf, hl] at success
          subst fragment
          exact .app hk (firstIH hf) (lastIH hl)
  | free k body ih =>
    cases ho : inputs[k]? with
    | none => simp [compile, ho] at success
    | some owner =>
      cases hl : compile inputs kinds (l + 1) (b + 1) exit body with
      | none => simp [compile, ho, hl] at success
      | some last => simp [compile, ho, hl] at success; subst fragment; exact .free ho (ih hl)
  | lend k index body ih =>
    cases ho : inputs[k]? with
    | none => simp [compile, ho] at success
    | some owner =>
      cases hi : lowerNat (owner :: inputs) index with
      | none => simp [compile, ho, hi] at success
      | some indexOp =>
        cases hl : compile (owner :: .copy ⟨l + 1, false⟩ :: inputs) (.pointer :: .scalar :: kinds) (l + 2) (b + 1) exit body with
        | none => simp [compile, ho, hi, hl] at success
        | some last =>
          simp [compile, ho, hi, hl] at success
          subst fragment
          exact .lend ho hi (ih hl)
  | ownedLend k length index body ih =>
    cases ho : inputs[k]? with
    | none => simp [compile, ho] at success
    | some owner =>
      cases hn : lowerNat (owner :: inputs) length with
      | none => simp [compile, ho, hn] at success
      | some lengthOp =>
        cases hi : lowerNat (owner :: inputs) index with
        | none => simp [compile, ho, hn, hi] at success
        | some indexOp =>
          cases hl : compile (owner :: .copy ⟨l + 6, false⟩ :: inputs) (.pointer :: .pointer :: kinds) (l + 12) (b + 7) exit body with
          | none => simp [compile, ho, hn, hi, hl] at success
          | some last =>
            simp [compile, ho, hn, hi, hl] at success
            subst fragment
            exact .ownedLend ho hn hi (ih hl)
  | ifLt left right yes no yesIH noIH =>
    cases hl : lowerNat inputs left with
    | none => simp [compile, hl] at success
    | some leftOp =>
      cases hr : lowerNat inputs right with
      | none => simp [compile, hl, hr] at success
      | some rightOp =>
        cases hy : inferKind kinds yes with
        | none => simp [compile, hl, hr, hy] at success
        | some kind =>
          cases hn : inferKind kinds no with
          | none => simp [compile, hl, hr, hy, hn] at success
          | some noKind =>
            by_cases eq : kind = noKind
            · subst noKind
              cases yc : compile inputs kinds (l + 2) (b + 3) (b + 1) yes with
              | none => simp [compile, hl, hr, hy, hn, yc] at success
              | some yesCode =>
                cases nc : compile inputs kinds (l + 2 + localCost yes)
                    (b + 3 + blockCost yes) (b + 2) no with
                | none => simp [compile, hl, hr, hy, hn, yc, nc] at success
                | some noCode =>
                  simp [compile, hl, hr, hy, hn, yc, nc] at success
                  subst fragment
                  exact .ifLt hl hr hy hn (yesIH yc) (noIH nc)
            · simp [compile, hl, hr, hy, hn, eq] at success

theorem Compiles.complete (run : Compiles inputs kinds l b exit term fragment) :
    compile inputs kinds l b exit term = some fragment := by
  induction run with
  | scalar h => simp [compile, h]
  | natural h => simp [compile, h]
  | var h => simp [compile, h]
  | allocate hn hf => simp [compile, hn, hf]
  | app hk _ _ first last => simp [compile, hk, first, last]
  | free ho _ ih => simp [compile, ho, ih]
  | lend ho hi _ ih => simp [compile, ho, hi, ih]
  | ownedLend ho hn hi _ ih => simp [compile, ho, hn, hi, ih]
  | ifLt hl hr hy hn _ _ yes no => simp [compile, hl, hr, hy, hn, yes, no]

theorem Compiles.sizes (run : Compiles inputs kinds l b exit term fragment) :
    fragment.locals.size = localCost term ∧ fragment.blocks.size = blockCost term := by
  induction run with
  | scalar | natural | var => simp [pureFragment, localCost, blockCost]
  | allocate => simp [allocationFragment, Allocation.roleTypes, Allocation.fragmentBlocks, localCost, blockCost]
  | app _ _ _ first last => simp [appendFragment, localCost, blockCost, first, last]
  | free _ _ ih => simp [freeFragment, localCost, blockCost, ih]
  | lend _ _ _ ih => simp [lendFragment, appendFragment, readFragment, localCost, blockCost, ih]
  | ownedLend _ _ _ _ ih =>
    simp [ownedLendFragment, appendFragment, readFragment, allocationFragment,
      Allocation.roleTypes, Allocation.fragmentBlocks, localCost, blockCost, ih, ← Nat.add_assoc]

  | ifLt _ _ _ _ _ _ yes no => simp [branchFragment, localCost, blockCost, yes, no, Nat.add_assoc]

theorem Compiles.result_before (run : Compiles inputs kinds l b exit term fragment)
    (before : InputsBefore l inputs) : Before (l + localCost term) fragment.result := by
  induction run with
  | scalar | natural => trivial
  | var lookup => simpa [pureFragment, localCost] using before _ (List.mem_of_getElem? lookup)
  | allocate => simp [allocationFragment, Before, localCost]
  | @app kinds argument argumentKind inputs l b exit body first last hk arg bodyRun firstIH lastIH =>
    have firstBound := firstIH before
    have args : InputsBefore (l + localCost argument) (first.result :: inputs) := by
      intro op member
      rcases List.mem_cons.mp member with rfl | old
      · exact firstBound
      · exact (before op old).mono (by omega)
    simpa [appendFragment, localCost, Nat.add_assoc] using lastIH args
  | @free inputs k owner kinds l b exit body last lookup run ih =>
    simpa [freeFragment, localCost, Nat.add_assoc] using ih (before.mono (by omega))
  | @lend inputs k owner index indexOp l kinds b exit body last lookup _ run ih =>
    have args : InputsBefore (l + 2) (owner :: .copy ⟨l + 1, false⟩ :: inputs) := by
      intro op member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | old
      · exact (before _ (List.mem_of_getElem? lookup)).mono (by omega)
      · simp [Before]
      · exact (before _ old).mono (by omega)
    simpa [lendFragment, appendFragment, localCost, Nat.add_assoc] using ih args
  | @ownedLend inputs k owner length lengthOp index indexOp l kinds b exit body last lookup _ _ run ih =>
    have args : InputsBefore (l + 12) (owner :: .copy ⟨l + 6, false⟩ :: inputs) := by
      intro op member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | old
      · exact (before _ (List.mem_of_getElem? lookup)).mono (by omega)
      · simp [Before]
      · exact (before _ old).mono (by omega)
    simpa [ownedLendFragment, appendFragment, localCost, Nat.add_assoc] using ih args

  | ifLt => simp [branchFragment, Before, localCost]; omega

/-- A fragment occupies exact slices of the final declarations and block array.
This contains only structural facts, not an execution or safety premise. -/
structure Embedded (code : Code) (localBase blockBase : Nat) (fragment : Fragment) : Prop where
  locals : ∀ i, i < fragment.locals.size → code.locals[localBase + i]? = fragment.locals[i]?
  blocks : ∀ i, i < fragment.blocks.size → code.blocks[blockBase + i]? = fragment.blocks[i]?
  localBound : localBase + fragment.locals.size ≤ code.locals.size
  blockBound : blockBase + fragment.blocks.size ≤ code.blocks.size

theorem entry_app :
    entry b exit (.app argument body) =
      entry b (entry (b + blockCost argument) exit body) argument := by
  by_cases first : blockCost argument = 0
  · simp [entry, blockCost, first]
  · simp [entry, blockCost, first]

@[simp] theorem entry_ifLt : entry b exit (.ifLt left right yes no) = b := by
  simp [entry, blockCost]

@[simp] theorem entry_free : entry b exit (.free k body) = b := by
  simp [entry, blockCost]

@[simp] theorem entry_allocate : entry b exit (.allocate length fill) = b := by
  simp [entry, blockCost]

@[simp] theorem entry_lend : entry b exit (.lend k index body) = b := by
  simp [entry, blockCost]

@[simp] theorem entry_ownedLend : entry b exit (.ownedLend k length index body) = b := by
  simp [entry, blockCost]

theorem Embedded.append_left (embedded : Embedded code l b (appendFragment first last)) :
    Embedded code l b first := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := embedded.locals i (by simp [appendFragment]; omega)
    simpa [appendFragment, Array.getElem?_append_left hi] using h
  · intro i hi
    have h := embedded.blocks i (by simp [appendFragment]; omega)
    simpa [appendFragment, Array.getElem?_append_left hi] using h

  · have h := embedded.localBound; simp only [appendFragment, Array.size_append] at h; omega
  · have h := embedded.blockBound; simp only [appendFragment, Array.size_append] at h; omega

theorem Embedded.append_right (embedded : Embedded code l b (appendFragment first last)) :
    Embedded code (l + first.locals.size) (b + first.blocks.size) last := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := embedded.locals (first.locals.size + i) (by simp [appendFragment]; omega)
    simpa [appendFragment, Nat.add_assoc, Array.getElem?_append_right (by omega : first.locals.size ≤ first.locals.size + i)] using h
  · intro i hi
    have h := embedded.blocks (first.blocks.size + i) (by simp [appendFragment]; omega)
    simpa [appendFragment, Nat.add_assoc, Array.getElem?_append_right (by omega : first.blocks.size ≤ first.blocks.size + i)] using h

  · have h := embedded.localBound; simpa [appendFragment, Nat.add_assoc] using h
  · have h := embedded.blockBound; simpa [appendFragment, Nat.add_assoc] using h

theorem Embedded.read_type (embedded : Embedded code l b (readFragment l owner index target)) :
    code.locals[l]? = some .ptr ∧ code.locals[l + 1]? = some .i64 := by
  constructor
  · simpa [readFragment] using embedded.locals 0 (by simp [readFragment])
  · simpa [readFragment] using embedded.locals 1 (by simp [readFragment])

theorem Embedded.read_ptr_type (embedded : Embedded code l b (readFragment l owner index target)) :
    code.locals[l]? = some .ptr := embedded.read_type.1

theorem Embedded.read_scalar_type (embedded : Embedded code l b (readFragment l owner index target)) :
    code.locals[l + 1]? = some .i64 := embedded.read_type.2

theorem Embedded.read_block (embedded : Embedded code l b (readFragment l owner index target)) :
    code.blocks[b]? = some (readBlock l owner index target) := by
  simpa [readFragment] using embedded.blocks 0 (by simp [readFragment])

theorem Embedded.lend_read (embedded : Embedded code l b (lendFragment l owner index target body)) :
    Embedded code l b (readFragment l owner index target) :=
  embedded.append_left

theorem Embedded.lend_tail (embedded : Embedded code l b (lendFragment l owner index target body)) :
    Embedded code (l + 2) (b + 1) body := by
  simpa [readFragment] using embedded.append_right

theorem Embedded.ownedLend_read
    (embedded : Embedded code l b (ownedLendFragment l b owner length index target body)) :
    Embedded code l b (readFragment l owner index (b + 1)) :=
  embedded.append_left

theorem Embedded.ownedLend_allocation
    (embedded : Embedded code l b (ownedLendFragment l b owner length index target body)) :
    Embedded code (l + 2) (b + 1)
      (allocationFragment (l + 2) (b + 1) target length (.copy ⟨l + 1, false⟩)) := by
  have h := embedded.append_right.append_left
  simpa [readFragment] using h

theorem Embedded.ownedLend_tail
    (embedded : Embedded code l b (ownedLendFragment l b owner length index target body)) :
    Embedded code (l + 12) (b + 7) body := by
  have h := embedded.append_right.append_right
  simpa [readFragment, allocationFragment, Allocation.roleTypes, Allocation.fragmentBlocks,
    ← Nat.add_assoc] using h

theorem Embedded.free_tail (embedded : Embedded code l b (freeFragment l owner target body)) :
    Embedded code (l + 1) (b + 1) body := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := embedded.locals (1 + i) (by simp [freeFragment]; omega)
    simpa [freeFragment, Nat.add_assoc, Array.getElem?_append] using h
  · intro i hi
    have h := embedded.blocks (1 + i) (by simp [freeFragment]; omega)
    simpa [freeFragment, Nat.add_assoc, Array.getElem?_append] using h

  · have h := embedded.localBound; simpa [freeFragment, Nat.add_assoc] using h
  · have h := embedded.blockBound; simpa [freeFragment, Nat.add_assoc] using h

theorem Embedded.free_type (embedded : Embedded code l b (freeFragment l owner target body)) :
    code.locals[l]? = some .unit := by
  have h := embedded.locals 0 (by simp [freeFragment]; omega)
  simpa [freeFragment, Array.getElem?_append] using h

theorem Embedded.free_block (embedded : Embedded code l b (freeFragment l owner target body)) :
    code.blocks[b]? = some (freeBlock l owner target) := by
  have h := embedded.blocks 0 (by simp [freeFragment]; omega)
  simpa [freeFragment, Array.getElem?_append] using h

theorem Embedded.branch_type
    (embedded : Embedded code l b (branchFragment l b exit kind left right yt nt yes no)) :
    code.locals[l]? = some .bool ∧ code.locals[l + 1]? = some kind.ty := by
  constructor
  · have h := embedded.locals 0 (by simp [branchFragment]; omega)
    simpa [branchFragment, Array.getElem?_append] using h
  · have h := embedded.locals 1 (by simp [branchFragment]; omega)
    simpa [branchFragment, Array.getElem?_append] using h

theorem Embedded.branch_decision
    (embedded : Embedded code l b (branchFragment l b exit kind left right yt nt yes no)) :
    code.blocks[b]? = some (Branch.decisionBlock l left right yt nt) := by
  have h := embedded.blocks 0 (by simp [branchFragment]; omega)
  simpa [branchFragment, Array.getElem?_append] using h

theorem Embedded.branch_yes_join
    (embedded : Embedded code l b (branchFragment l b exit kind left right yt nt yes no)) :
    code.blocks[b + 1]? = some (Branch.joinBlock (l + 1) yes.result exit) := by
  have h := embedded.blocks 1 (by simp [branchFragment]; omega)
  simpa [branchFragment, Array.getElem?_append] using h

theorem Embedded.branch_no_join
    (embedded : Embedded code l b (branchFragment l b exit kind left right yt nt yes no)) :
    code.blocks[b + 2]? = some (Branch.joinBlock (l + 1) no.result exit) := by
  have h := embedded.blocks 2 (by simp [branchFragment]; omega)
  simpa [branchFragment, Array.getElem?_append] using h

theorem Embedded.branch_yes
    (embedded : Embedded code l b (branchFragment l b exit kind left right yt nt yes no)) :
    Embedded code (l + 2) (b + 3) yes := by
  let admin : Fragment := ⟨#[.bool, kind.ty],
    #[Branch.decisionBlock l left right yt nt,
      Branch.joinBlock (l + 1) yes.result exit,
      Branch.joinBlock (l + 1) no.result exit], .copy ⟨l + 1, false⟩⟩
  have e : Embedded code l b (appendFragment (appendFragment admin yes) no) := by
    exact ⟨embedded.locals, embedded.blocks, embedded.localBound, embedded.blockBound⟩
  simpa [admin] using e.append_left.append_right

theorem Embedded.branch_no
    (embedded : Embedded code l b (branchFragment l b exit kind left right yt nt yes no)) :
    Embedded code (l + 2 + yes.locals.size) (b + 3 + yes.blocks.size) no := by
  let admin : Fragment := ⟨#[.bool, kind.ty],
    #[Branch.decisionBlock l left right yt nt,
      Branch.joinBlock (l + 1) yes.result exit,
      Branch.joinBlock (l + 1) no.result exit], .copy ⟨l + 1, false⟩⟩
  have e : Embedded code l b (appendFragment (appendFragment admin yes) no) := by
    exact ⟨embedded.locals, embedded.blocks, embedded.localBound, embedded.blockBound⟩
  simpa [admin, appendFragment, ← Nat.add_assoc] using e.append_right

theorem Embedded.entry_bound (embedded : Embedded code l b fragment)
    (compiled : Compiles inputs kinds l b exit term fragment) (exitBound : exit < code.blocks.size) :
    entry b exit term < code.blocks.size := by
  have size := compiled.sizes.2
  have bound := embedded.blockBound
  by_cases zero : blockCost term = 0
  · simpa [entry, zero] using exitBound
  · simp only [entry, ite_eq_right zero]
    omega

end Jihoo.SizedMir.Linear
