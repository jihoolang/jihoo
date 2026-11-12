import Jihoo.CommonDataCoreErasure
import Jihoo.SizedErasureCompiler

/-! A fuel-bounded executable traversal of the entire common lowering grammar.
Certificates are outputs, never inputs. Fuel bounds recursive descent, not graph
size; unsupported shapes and unavailable slots fail. No global DAG or native
compiler refinement claim is made. -/
namespace Jihoo.CommonDataCoreErasure
open CommonDataErasure CommonDataSourceRules

def compile (g : CommonDataSource.Graph) : (fuel : Nat) → (slots : Slots) →
    (mask : SizedErasure.Mask) → (root : Nat) → Option { t : Term // Lower g slots mask root t }
  | 0, _, _, _ => none
  | fuel+1, slots, mask, root =>
    match shape : CommonDataSource.nodeAt g root with
    | .core (.integer n) => some ⟨.literal n, .literal shape⟩
    | .con 0 0 [] => some ⟨.empty, .empty shape⟩
    | .core (.var k) =>
      match pos : position slots k with
      | some j => some ⟨.var j, .var shape pos⟩
      | none => none
    | .con 0 1 [l,r] =>
      match left : CommonDataSource.nodeAt g l, right : CommonDataSource.nodeAt g r with
      | .core (.var li), .core (.var ri) =>
        match lp : position slots li, rp : position slots ri with
        | some lj, some rj => some ⟨.construct lj rj, .construct shape left lp right rp⟩
        | _, _ => none
      | _, _ => none
    | .core (.app fn arg) =>
      match lam : CommonDataSource.nodeAt g fn with
      | .core (.lam false ty body) =>
        match domain : CommonDataSource.nodeAt g ty with
        | .core .i64 => do
          let a ← SizedErasure.compile (CommonDataSourceExecution.sourceCore g) fuel mask arg
          let b ← compile g fuel (true :: slots) (true :: mask) body
          return ⟨.scalarLet a.val b.val, .scalarLet shape lam domain a.property b.property⟩
        | .core (.buffer _) => do
          let a ← SizedErasure.compile (CommonDataSourceExecution.sourceCore g) fuel mask arg
          let b ← compile g fuel (true :: slots) (true :: mask) body
          return ⟨.ownerLet a.val b.val, .ownerLet shape lam domain a.property b.property⟩
        | .ind 0 [] => do
          let a ← compile g fuel slots mask arg
          let b ← compile g fuel (true :: slots) (false :: mask) body
          return ⟨.letData a.val b.val, .letData shape lam domain a.property b.property⟩
        | _ => none
      | _ => none
    | .drop 0 owner body =>
      match variableShape : CommonDataSource.nodeAt g owner with
      | .core (.var k) =>
        match pos : position slots k with
        | some j => do
          let b ← compile g fuel slots mask body
          return ⟨.drop j b.val, .drop shape variableShape pos b.property⟩
        | none => none
      | _ => none
    | .core (.free owner body) =>
      match variableShape : CommonDataSource.nodeAt g owner with
      | .core (.var k) =>
        match pos : position slots k with
        | some j => do
          let b ← compile g fuel slots mask body
          return ⟨.freeBuffer j b.val, .freeBuffer shape variableShape pos b.property⟩
        | none => none
      | _ => none
    | .caseOf 0 motive [nil,node] scrutinee =>
      match motiveShape : motiveKind g motive, branch : CommonDataSource.branchBody g node with
      | some _, some body =>
        match variableShape : CommonDataSource.nodeAt g scrutinee with
        | .core (.var k) =>
          match pos : position slots k with
          | some j => do
            let a ← compile g fuel slots mask nil
            let b ← compile g fuel (true :: true :: slots) (false :: false :: mask) body
            return ⟨.caseTree j a.val b.val, .caseTree shape motiveShape branch variableShape pos a.property b.property⟩
          | none => none
        | _ => none
      | _, _ => none
    | _ => none

def compileTarget (g : CommonDataSource.Graph) (fuel : Nat) (slots : Slots)
    (mask : SizedErasure.Mask) (root : Nat) : Option Term :=
  (compile g fuel slots mask root).map Subtype.val

theorem compileTarget_sound (success : compileTarget g fuel slots mask root = some target) :
    Lower g slots mask root target := by
  unfold compileTarget at success
  cases result : compile g fuel slots mask root with
  | none => simp [result] at success
  | some certified =>
    simp [result] at success
    subst target
    exact certified.property

end Jihoo.CommonDataCoreErasure
