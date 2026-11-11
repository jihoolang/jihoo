import Jihoo.SizedCoreErasure

/-! Fuel-bounded structural compaction. Successful results carry a kernel-
checked erasure derivation. Fuel limits traversal depth, including cyclic or
unsupported inputs; shared subgraphs may expand at each occurrence. It does not authorize memory operations or assume a run. -/
namespace Jihoo.SizedErasure
open ScopedLend

def compileNat (g : Graph.Graph) : (fuel : Nat) → (mask : Mask) → (root : Nat) →
    Option { term : NatTerm // NatErases g mask root term }
  | 0, _, _ => none
  | fuel+1, mask, root =>
    match shape : Graph.nodeAt g root with
    | .natural n =>
      if bound : n < 2^64 then
        some ⟨.literal n, ⟨_, .literal shape bound, .literal⟩⟩
      else none
    | .var k =>
      if retained : mask[k]? = some true then
        some ⟨.var (rank mask k), ⟨_, .var shape, .var retained⟩⟩
      else none
    | .app fn arg =>
      match lam : Graph.nodeAt g fn with
      | .lam false ty body =>
        match tyShape : Graph.nodeAt g ty with
        | .u64 => do
          let a ← compileNat g fuel mask arg
          let b ← compileNat g fuel (true :: mask) body
          return ⟨.letE a.val b.val, by
            obtain ⟨ea, ha, ca⟩ := a.property
            obtain ⟨eb, hb, cb⟩ := b.property
            exact ⟨_, .letE shape lam tyShape ha hb, .letE ca cb⟩⟩
        | _ => none
      | _ => none
    | _ => none

def compileScalar (g : Graph.Graph) (mask : Mask) (root : Nat) :
    Option { term : ScalarTerm // ScalarErases g mask root term } :=
  match shape : Graph.nodeAt g root with
  | .integer v => some ⟨.literal v, .literal shape⟩
  | .var k =>
    if retained : mask[k]? = some true then some ⟨.var (rank mask k), .var shape retained⟩
    else none
  | _ => none

def compile (g : Graph.Graph) : (fuel : Nat) → (mask : Mask) → (root : Nat) →
    Option { term : Term // Erases g mask root term }
  | 0, _, _ => none
  | fuel+1, mask, root =>
    match shape : Graph.nodeAt g root with
    | .integer v => some ⟨.scalar v, .scalar shape⟩
    | .natural n => some ⟨.natural n, .natural shape⟩
    | .var k =>
      if retained : mask[k]? = some true then some ⟨.var (rank mask k), .var shape retained⟩
      else none
    | .app fn arg =>
      match lam : Graph.nodeAt g fn with
      | .lam false _ty body => do
        let a ← compile g fuel mask arg
        let b ← compile g fuel (true :: mask) body
        return ⟨.app a.val b.val, .app shape lam a.property b.property⟩
      | _ => none
    | .alloc length init => do
      let n ← compileNat g fuel mask length
      let v ← compileScalar g mask init
      return ⟨.allocate n.val v.val, .allocate shape n.property v.property⟩
    | .free owner body =>
      match variableShape : Graph.nodeAt g owner with
      | .var k =>
        if retained : mask[k]? = some true then do
          let b ← compile g fuel mask body
          return ⟨.free (rank mask k) b.val, .free shape variableShape retained b.property⟩
        else none
      | _ => none
    | .ifLt left right yes no => do
      let l ← compileNat g fuel mask left
      let r ← compileNat g fuel mask right
      let y ← compile g fuel (false :: mask) yes
      let n ← compile g fuel mask no
      return ⟨.ifLt l.val r.val y.val n.val, .branch shape l.property r.property y.property n.property⟩
    | .lend owner reader cont =>
      match variableShape : Graph.nodeAt g owner with
      | .var k =>
        if retained : mask[k]? = some true then
          match readerShape : Graph.nodeAt g reader, contShape : Graph.nodeAt g cont with
          | .lam false _refTy readRoot, .lam false resultTy inner =>
            match innerShape : Graph.nodeAt g inner with
            | .lam false _ownerTy body =>
              match readShape : Graph.nodeAt g readRoot with
              | .index operand index _proof =>
                match operandShape : Graph.nodeAt g operand, resultShape : Graph.nodeAt g resultTy with
                | .var 0, .i64 => do
                  let i ← compileNat g fuel (true :: mask) index
                  let b ← compile g fuel (true :: true :: mask) body
                  return ⟨.lend (rank mask k) i.val b.val,
                    .lend (.intro shape readerShape readShape operandShape contShape resultShape innerShape)
                      variableShape retained i.property b.property⟩
                | _, _ => none
              | .alloc length element =>
                match elementShape : Graph.nodeAt g element with
                | .index operand index _proof =>
                  match operandShape : Graph.nodeAt g operand with
                  | .var 0 => do
                    let n ← compileNat g fuel (true :: mask) length
                    let i ← compileNat g fuel (true :: mask) index
                    let b ← compile g fuel (true :: true :: mask) body
                    return ⟨.ownedLend (rank mask k) n.val i.val b.val,
                      .ownedLend (.intro shape readerShape readShape elementShape operandShape contShape innerShape)
                        variableShape retained n.property i.property b.property⟩
                  | _ => none
                | _ => none
              | _ => none
            | _ => none
          | _, _ => none
        else none
      | _ => none
    | _ => none

/-- The executable target projection discards the construction's proof object. -/
def compileTarget (g : Graph.Graph) (fuel : Nat) (mask : Mask) (root : Nat) : Option Term :=
  (compile g fuel mask root).map Subtype.val

theorem compileTarget_correct (success : compileTarget g fuel mask root = some term) :
    Erases g mask root term := by
  unfold compileTarget at success
  cases result : compile g fuel mask root with
  | none => simp [result] at success
  | some certified =>
      simp [result] at success
      subst term
      exact certified.property

end Jihoo.SizedErasure
