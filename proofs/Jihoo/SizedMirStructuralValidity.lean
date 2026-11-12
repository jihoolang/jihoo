import Jihoo.SizedMirStructuralBudgets

namespace Jihoo.SizedMir.Structural
open BoundedMir Linear
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def OperandTyped (c : Code) (op : Operand) (kind : Kind) : Prop :=
  BoundedMir.operandValid c op = true ∧ operandType c op = some kind.ty

inductive InputsTyped (c : Code) : List Operand → List Kind → Prop where
  | nil : InputsTyped c [] []
  | cons : OperandTyped c op kind → InputsTyped c inputs ks → InputsTyped c (op :: inputs) (kind :: ks)

theorem InputsTyped.lookup {k : Nat} (h : InputsTyped c inputs ks) (hk : ks[k]? = some kind)
    (hi : inputs[k]? = some op) : OperandTyped c op kind := by
  induction h generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases k with
      | zero => cases hk; cases hi; exact head
      | succ k => exact ih hk hi

theorem OperandTyped.copy (h : c.locals[k]? = some kind.ty) :
    OperandTyped c (.copy ⟨k,false⟩) kind := by
  have bound := (Array.getElem?_eq_some_iff.mp h).1
  exact ⟨by simp [BoundedMir.operandValid, placeValid, bound], by simpa [operandType] using h⟩

theorem NatTyped.valid (h : NatTyped ks term) (inputsOK : InputsTyped c inputs ks)
    (compiled : lowerNat inputs term = some op) : OperandTyped c op .natural := by
  induction h generalizing inputs op with
  | literal bound =>
      simp [lowerNat, bound] at compiled
      subst op
      simp [OperandTyped, BoundedMir.operandValid, operandType, constant, bound, Kind.ty]
  | var lookup => exact inputsOK.lookup lookup compiled
  | @letE ks a b ha hb ia ib =>
      cases he : lowerNat inputs a with
      | none => simp [lowerNat, he] at compiled
      | some a =>
          exact ib (.cons (ia inputsOK he) inputsOK) (by simpa [lowerNat, he] using compiled)

theorem ScalarTyped.valid (h : ScalarTyped ks term) (inputsOK : InputsTyped c inputs ks)
    (compiled : lowerScalar inputs term = some op) : OperandTyped c op .scalar := by
  cases h with
  | literal bound =>
      simp [lowerScalar, bound] at compiled
      subst op
      simp [OperandTyped, BoundedMir.operandValid, operandType, constant, bound, Kind.ty]
  | var lookup => exact inputsOK.lookup lookup compiled

def BlockValid (c : Code) (block : Block) : Prop :=
  (∀ s ∈ block.statements, stmtValid c s = true) ∧ termValid c block.term = true

def BlocksValid (c : Code) (blocks : Array Block) : Prop :=
  ∀ block ∈ blocks, BlockValid c block

@[simp] theorem blocksValid_append : BlocksValid c (a ++ b) ↔ BlocksValid c a ∧ BlocksValid c b := by
  simp [BlocksValid, or_imp, forall_and]

theorem copy_stmt_valid (slot : c.locals[k]? = some kind.ty) (op : OperandTyped c arg kind) :
    stmtValid c ⟨⟨k,false⟩, .use arg⟩ = true := by
  have bound := (Array.getElem?_eq_some_iff.mp slot).1
  simp [stmtValid, placeValid, rvalueValid, rvalueType, destinationType, slot, op.1, op.2]
  exact bound

theorem read_valid {next : Nat} (placed : Embedded c l b (readFragment l owner index next))
    (ho : OperandTyped c owner .pointer) (hi : OperandTyped c index .natural)
    (out : next < c.blocks.size) : BlocksValid c (readFragment l owner index next).blocks ∧
      OperandTyped c (readFragment l owner index next).result .scalar := by
  have pt := placed.read_ptr_type
  have st := placed.read_scalar_type
  have pb := (Array.getElem?_eq_some_iff.mp pt).1
  have sb := (Array.getElem?_eq_some_iff.mp st).1
  constructor
  · simp_all [OperandTyped, BlocksValid, BlockValid, readFragment, readBlock, stmtValid, placeValid,
      rvalueValid, rvalueType, operandType, destinationType, BoundedMir.operandValid,
      pt, st, pb, sb, ho.1, ho.2, hi.1, hi.2, Kind.ty, termValid, out]
  · exact OperandTyped.copy st

theorem allocation_valid (placed : Embedded c l b (allocationFragment l b exit length fill))
    (hn : OperandTyped c length .natural) (hv : OperandTyped c fill .scalar)
    (out : exit < c.blocks.size) : BlocksValid c (allocationFragment l b exit length fill).blocks ∧
      OperandTyped c (allocationFragment l b exit length fill).result .pointer := by
  have types (i : Fin 10) : c.locals[l + i.val]? = some (MirBuffer.roleType i) := by
    simpa [allocationFragment, Allocation.roleTypes] using placed.locals i.val (by simp [allocationFragment, Allocation.roleTypes])
  have t0 : c.locals[l + 0]? = some .u64 := types 0
  have t1 : c.locals[l + 1]? = some .i64 := types 1
  have t2 : c.locals[l + 2]? = some .u64 := types 2
  have t3 : c.locals[l + 3]? = some .u64 := types 3
  have t4 : c.locals[l + 4]? = some .ptr := types 4
  have t5 : c.locals[l + 5]? = some .u64 := types 5
  have t6 : c.locals[l + 6]? = some .bool := types 6
  have t7 : c.locals[l + 7]? = some .u64 := types 7
  have t8 : c.locals[l + 8]? = some .bool := types 8
  have t9 : c.locals[l + 9]? = some .ptr := types 9
  clear types
  simp only [Nat.add_zero] at t0
  have lb := placed.localBound
  have bb := placed.blockBound
  simp [allocationFragment, Allocation.roleTypes, Allocation.fragmentBlocks] at lb bb
  clear placed
  constructor
  · simp_all [OperandTyped, BlocksValid, BlockValid, allocationFragment, Allocation.fragmentBlocks,
      Allocation.inputBlock, MirBuffer.entryBlock, MirBuffer.guardBlock, MirBuffer.initBlock,
      MirBuffer.testBlock, MirBuffer.bodyBlock, Allocation.layout, Allocation.labels,
      MirBuffer.slotPlace, MirBuffer.copy, stmtValid, placeValid, rvalueValid, rvalueType,
      operandType, destinationType, BoundedMir.operandValid, constant, termValid,
      t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, hn.1, hn.2, hv.1, hv.2,
      Kind.ty, Fin.val_ofNat, wordBound, scalarBound, out]
    simp only [show ((3 : MirBuffer.Role) : Nat) = 3 from rfl, show ((4 : MirBuffer.Role) : Nat) = 4 from rfl, show ((5 : MirBuffer.Role) : Nat) = 5 from rfl, show ((6 : MirBuffer.Role) : Nat) = 6 from rfl, show ((7 : MirBuffer.Role) : Nat) = 7 from rfl, show ((8 : MirBuffer.Role) : Nat) = 8 from rfl, show ((9 : MirBuffer.Role) : Nat) = 9 from rfl, t3, t4, t5, t6, t7, t8, t9]
    simp only [ite_true, and_self, true_and, and_true, true_or]
    omega
  · exact OperandTyped.copy t4

theorem typed_fragment_valid (compiled : Compiles inputs ks l b exit term fragment)
    (typed : Typed ks term kind) (inputsOK : InputsTyped c inputs ks)
    (placed : Embedded c l b fragment) (out : exit < c.blocks.size) :
    BlocksValid c fragment.blocks ∧ OperandTyped c fragment.result kind := by
  induction compiled generalizing kind with
  | scalar bound =>
      cases typed
      simp [BlocksValid, pureFragment, OperandTyped, BoundedMir.operandValid,
        operandType, constant, bound, Kind.ty]
  | natural bound =>
      cases typed
      simp [BlocksValid, pureFragment, OperandTyped, BoundedMir.operandValid,
        operandType, constant, bound, Kind.ty]
  | var lookup =>
      cases typed with
      | var hk => exact ⟨by simp [BlocksValid, pureFragment], inputsOK.lookup hk lookup⟩
  | allocate hn hv =>
      cases typed with
      | allocate tn tv => exact allocation_valid placed (tn.valid inputsOK hn) (tv.valid inputsOK hv) out
  | app hk ca cb ia ib =>
      cases typed with
      | app ta tb =>
          cases Option.some.inj (ta.infer.symm.trans hk)
          have ep := placed.append_left
          have eb := placed.append_right
          rw [ca.sizes.1, ca.sizes.2] at eb
          obtain ⟨va, ra⟩ := ia ta inputsOK ep (eb.entry_bound cb out)
          obtain ⟨vb, rb⟩ := ib tb (.cons ra inputsOK) eb out
          exact ⟨blocksValid_append.mpr ⟨va,vb⟩, rb⟩
  | free lookup cb ib =>
      cases typed with
      | free hk tb =>
          have eb := placed.free_tail
          obtain ⟨vb, rb⟩ := ib tb inputsOK eb out
          have target := eb.entry_bound cb out
          have ho := inputsOK.lookup hk lookup
          have slot := placed.free_type
          have bound := (Array.getElem?_eq_some_iff.mp slot).1
          refine ⟨?_, rb⟩
          simp only [freeFragment, blocksValid_append]
          refine ⟨?_, vb⟩
          simp_all [BlocksValid, BlockValid, freeBlock, termValid, OperandTyped, Kind.ty]
  | lend lookup hi cb ib =>
      cases typed with
      | lend hk ti tb =>
          have ho := inputsOK.lookup hk lookup
          have eb := placed.lend_tail
          have target := eb.entry_bound cb out
          obtain ⟨vr, rr⟩ := read_valid placed.lend_read ho (ti.valid (.cons ho inputsOK) hi) target
          obtain ⟨vb, rb⟩ := ib tb (.cons ho (.cons rr inputsOK)) eb out
          exact ⟨blocksValid_append.mpr ⟨vr,vb⟩, rb⟩
  | ownedLend lookup hn hi cb ib =>
      cases typed with
      | ownedLend hk tn ti tb =>
          have ho := inputsOK.lookup hk lookup
          have eb := placed.ownedLend_tail
          have ea := placed.ownedLend_allocation
          have bb := ea.blockBound
          obtain ⟨vr, rr⟩ := read_valid placed.ownedLend_read ho (ti.valid (.cons ho inputsOK) hi)
            (by simp [allocationFragment, Allocation.fragmentBlocks] at bb; omega)
          obtain ⟨va, ra⟩ := allocation_valid ea (tn.valid (.cons ho inputsOK) hn) rr (eb.entry_bound cb out)
          obtain ⟨vb, rb⟩ := ib tb (.cons ho (.cons ra inputsOK)) eb out
          exact ⟨blocksValid_append.mpr ⟨vr, blocksValid_append.mpr ⟨va,vb⟩⟩, rb⟩
  | ifLt hl hr hy hn cy cn iy ino =>
      cases typed with
      | ifLt tl tr ty tn =>
          cases Option.some.inj (ty.infer.symm.trans hy)
          have ey := placed.branch_yes
          have en := placed.branch_no
          rw [cy.sizes.1, cy.sizes.2] at en
          have bb := placed.blockBound
          have yout := placed.branch_yes_join
          have nout := placed.branch_no_join
          have ybound := (Array.getElem?_eq_some_iff.mp yout).1
          have nbound := (Array.getElem?_eq_some_iff.mp nout).1
          obtain ⟨vy, ry⟩ := iy ty inputsOK ey ybound
          obtain ⟨vn, rn⟩ := ino tn inputsOK en nbound
          have yt := ey.entry_bound cy ybound
          have nt := en.entry_bound cn nbound
          have hleft := tl.valid inputsOK hl
          have hright := tr.valid inputsOK hr
          have bt := placed.branch_type.1
          have rt := placed.branch_type.2
          have bound := (Array.getElem?_eq_some_iff.mp bt).1
          have jy := copy_stmt_valid rt ry
          have jn := copy_stmt_valid rt rn
          refine ⟨?_, OperandTyped.copy rt⟩
          simp only [branchFragment, blocksValid_append]
          refine ⟨⟨?_, vy⟩, vn⟩
          simp_all [BlocksValid, BlockValid, Branch.decisionBlock, Branch.joinBlock,
            OperandTyped, stmtValid, rvalueValid, rvalueType, placeValid, destinationType,
            operandType, BoundedMir.operandValid, termValid, Kind.ty, wordBound]

theorem InputsTyped.length (h : InputsTyped c inputs ks) : inputs.length = ks.length := by
  induction h <;> simp_all

theorem InputsTyped.infer (h : InputsTyped ⟨types, #[]⟩ inputs ks) :
    inputKinds types inputs = some ks := by
  induction h with
  | nil => rfl
  | @cons op kind inputs ks head tail ih =>
      have hk : toKind kind.ty = some kind := by cases kind <;> rfl
      simp [inputKinds, head.2, hk, inputKinds] at ih ⊢
      simp [ih]

theorem InputsTyped.extend (h : InputsTyped ⟨types, #[]⟩ inputs ks)
    (before : InputsBefore types.size inputs) :
    InputsTyped ⟨types ++ extra, blocks⟩ inputs ks := by
  induction h with
  | nil => exact .nil
  | @cons op kind inputs ks head tail ih =>
      apply InputsTyped.cons
      · have hb := before op (by simp)
        cases op with
        | constant v => cases v <;> exact head
        | copy p =>
            have htype : types[p.slot]? = some kind.ty := by
              simpa [operandType, hb.1] using head.2
            have enlarged : (types ++ extra)[p.slot]? = some kind.ty := by
              rw [Array.getElem?_append_left hb.2]; exact htype
            have cp := OperandTyped.copy (c := ⟨types ++ extra, blocks⟩) enlarged
            cases p with
            | mk slot deref =>
                have eq : deref = false := hb.1
                subst deref
                exact cp
      · exact ih (fun op member => before op (by simp [member]))

theorem blocksValid_all (h : BlocksValid c bs) :
    bs.all (fun b => b.statements.all (stmtValid c) && termValid c b.term) = true := by
  rw [Array.all_eq_true]
  intro i hi
  obtain ⟨stmts, term⟩ := h bs[i] (by simp)
  simp only [Bool.and_eq_true]
  refine ⟨?_, term⟩
  rw [Array.all_eq_true]
  intro j hj
  exact stmts _ (by simp)

/-- Checked-entry construction from representation typing and explicit static
input/ABI/storage conditions. No compiler or validator success is assumed. -/
theorem Typed.entry_total (typed : Typed ks term .scalar)
    (inputTypesOK : InputsTyped ⟨types, #[]⟩ (Entry.operands abi.argumentSlots.toList) ks)
    (before : InputsBefore types.size (Entry.operands abi.argumentSlots.toList))
    (zero : types[0]? = some .i64)
    (locals : types.size + localCost term ≤ 512) (blocks : 2 + blockCost term ≤ 512)
    (distinct : abi.argumentSlots.toList.Nodup)
    (slots : ∀ slot ∈ abi.argumentSlots.toList, slot ≠ 0 ∧
      ∃ ty, types[slot]? = some ty ∧ argumentTypeSupported ty = true) :
    ∃ fragment, Entry.lowerProgram types abi term = some fragment := by
  obtain ⟨fragment, success⟩ := typed.total inputTypesOK.length types.size 2 1
  have compiled := compile_sound success
  let code := Entry.program types term fragment
  have placed : Embedded code types.size 2 fragment := Entry.program_embedded
  have exitBound : 1 < code.blocks.size := by simp [code, Entry.program]; omega
  obtain ⟨bv, result⟩ := typed_fragment_valid compiled typed (inputTypesOK.extend before) placed exitBound
  have zeroBound := (Array.getElem?_eq_some_iff.mp zero).1
  have czero : code.locals[0]? = some .i64 := by
    simp [code, Entry.program, Array.getElem?_append_left zeroBound, zero]
  have entryBound := placed.entry_bound compiled exitBound
  have wrapper : BlocksValid code #[Entry.entryBlock term, returnBlock fragment.result] := by
    have ret := copy_stmt_valid czero result
    simp [BlocksValid, BlockValid, Entry.entryBlock, returnBlock, termValid]
    exact ⟨entryBound, ret⟩
  have allBlocks : BlocksValid code code.blocks := blocksValid_append.mpr ⟨wrapper, bv⟩
  have localSize : code.locals.size ≤ 512 := by
    simpa [code, Entry.program, compiled.sizes.1] using locals
  have blockSize : code.blocks.size ≤ 512 := by
    simpa [code, Entry.program, compiled.sizes.2] using blocks
  have statementSize := entry_statement_bound compiled locals
  have codeValid : valid code = true := by
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨localSize, czero⟩, by omega⟩, blockSize⟩, statementSize⟩, blocksValid_all allBlocks⟩
  have signature := entry_signature_valid (term := term) (fragment := fragment) distinct slots
  refine ⟨fragment, ?_⟩
  simp [Entry.lowerProgram, inputTypesOK.infer, success, zero,
    inputsValid_iff.mpr before, localSize, blockSize, codeValid, signature, code] at *

theorem bindArguments_total
    (args : ArgumentsRel (fun slot value => c.locals[slot]? = some (valueType value) ∧
      argumentValueValid value = true) slots values)
    (size : f.locals.size = c.locals.size) : ∃ final, bindArguments c slots values f = some final := by
  induction args generalizing f with
  | nil => exact ⟨f,rfl⟩
  | @cons slot value slots values head tail ih =>
      have bound : slot < f.locals.size := by
        rw [size]; exact (Array.getElem?_eq_some_iff.mp head.1).1
      obtain ⟨final, success⟩ := ih (f := { f with locals := f.locals.set! slot (some value) })
        (by simpa using size)
      refine ⟨final, ?_⟩
      simp only [bindArguments, head.1, head.2, beq_self_eq_true, Bool.true_and,
        decide_eq_true bound, ↓reduceIte]
      exact success

/-- Actual argument admission follows from explicit value-width/type facts.
This relation checks input declarations and values, not generated code. -/
theorem Typed.entry_admission_total (typed : Typed ks term .scalar)
    (inputTypesOK : InputsTyped ⟨types, #[]⟩ (Entry.operands abi.argumentSlots.toList) ks)
    (before : InputsBefore types.size (Entry.operands abi.argumentSlots.toList))
    (zero : types[0]? = some .i64)
    (locals : types.size + localCost term ≤ 512) (blocks : 2 + blockCost term ≤ 512)
    (distinct : abi.argumentSlots.toList.Nodup)
    (slots : ∀ slot ∈ abi.argumentSlots.toList, slot ≠ 0 ∧
      ∃ ty, types[slot]? = some ty ∧ argumentTypeSupported ty = true)
    (args : ArgumentsRel (fun slot value => types[slot]? = some (valueType value) ∧
      argumentValueValid value = true) abi.argumentSlots.toList values) :
    ∃ fragment f, Entry.lowerProgram types abi term = some fragment ∧
      entryFrame (Entry.program types term fragment) abi values = some f := by
  obtain ⟨fragment, lowered⟩ := typed.entry_total inputTypesOK before zero locals blocks distinct slots
  have extended : ArgumentsRel (fun slot value =>
      (Entry.program types term fragment).locals[slot]? = some (valueType value) ∧
      argumentValueValid value = true) abi.argumentSlots.toList values := by
    apply args.imp
    intro slot value head
    have bound := (Array.getElem?_eq_some_iff.mp head.1).1
    exact ⟨(Array.getElem?_append_left bound).trans head.1, head.2⟩
  obtain ⟨f, admitted⟩ := bindArguments_total extended (f := initial (Entry.program types term fragment)) (by simp [initial])
  exact ⟨fragment, f, lowered, by simp [entryFrame, Entry.lowerProgram_entryValid lowered, admitted]⟩

end Jihoo.SizedMir.Structural
