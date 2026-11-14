import Jihoo.NativeEnvironmentTyping
import Jihoo.NativeEnvironmentExtension
import Jihoo.NativeOwnership
import Jihoo.NativeFamilyEnvironment
import Jihoo.NativeEnvironmentCaseQuantity

/-! Resource projection derived from the actual checked family table.
Constructors retain exactly their relevant fields; family binder annotations
retain their derived ownership mode. The resulting safety statement concerns
the projected control tree and does not assert a native heap semantics. -/
namespace Jihoo.NativeKernel.EnvironmentQuantity

open Environment

def relevantFields (data : Bool) : List Field → List Term → Option (List Term)
  | [], [] => some []
  | field :: fields, argument :: arguments => do
      let rest ← relevantFields data fields arguments
      pure (if data && !field.erased then argument :: rest else rest)
  | _, _ => none

def ordinary : Op → Bool
  | .global _ | .ind _ _ | .con _ _ _ | .elim _ _ | .caseOf _ _ | .view _ _ _ | .lend | .lam _ => false
  | _ => true

def caseFamily : Op → Option Nat
  | .elim family _ | .caseOf family _ | .view _ family _ => some family
  | _ => none

inductive Skeleton (env : Environment) : Term → Term → Prop where
  | var (x : Nat) : Skeleton env (.var x) (.var x)
  | node : ordinary op = true → Conversion.ListRel (Skeleton env) arguments projected →
      Skeleton env (.node op arguments) (.node op projected)
  | lam : Environment.Conversion.Conv domain normal → Skeleton env normal projectedDomain →
      Skeleton env body projectedBody →
      Skeleton env (.lam erased domain body) (.lam erased projectedDomain projectedBody)
  | familyType : env.families[family]? = some entry →
      Skeleton env (.node (.ind family count) indices)
        (if entry.boxed then .buffer (.natural 0) else .u64)
  | constructor : env.families[family]? = some entry → entry.signatures[constructor]? = some signature →
      count = arguments.length → relevantFields entry.declaration.data signature.fields arguments = some relevant →
      Conversion.ListRel (Skeleton env) relevant projected →
      Skeleton env (.node (.con family constructor count) arguments) (.elements projected.length projected)
  | propositionElimination : env.families[family]? = some entry → entry.declaration.data = false →
      Skeleton env (.node (.elim family count) arguments) (.natural 0)
  | familyCases : caseFamily op = some family → env.families[family]? = some entry →
      entry.declaration.data = true → Conversion.ListRel (Skeleton env) arguments projected →
      Skeleton env (.node op arguments) (.node op projected)

def caseSkeleton (visit : Term → Option Term) (env : Environment) (op : Op)
    (arguments : List Term) : Option Term := do
  let family ← caseFamily op
  let entry ← env.families[family]?
  if entry.declaration.data then
    let projected ← FamilyEnvironment.mapChecked visit arguments
    pure (.node op projected)
  else none

def skeleton : Nat → Environment → Term → Option Term
  | 0, _, _ => none
  | fuel + 1, env, term =>
      match term with
      | .var x => some (.var x)
      | .node op arguments =>
          match op with
          | .ind family _ => do
              let entry ← env.families[family]?
              pure (if entry.boxed then .buffer (.natural 0) else .u64)
          | .con family constructor count => do
              let entry ← env.families[family]?
              let signature ← entry.signatures[constructor]?
              if count = arguments.length then
                let relevant ← relevantFields entry.declaration.data signature.fields arguments
                let projected ← FamilyEnvironment.mapChecked (skeleton fuel env) relevant
                pure (.elements projected.length projected)
              else none
          | .elim family count => do
              let entry ← env.families[family]?
              if entry.declaration.data = false then some (.natural 0)
              else caseSkeleton (skeleton fuel env) env (.elim family count) arguments
          | .lam erased =>
              match arguments with
              | [domain, body] => do
                  let normal ← Environment.Conversion.normalize? fuel domain
                  let projectedDomain ← skeleton fuel env normal
                  let projectedBody ← skeleton fuel env body
                  pure (.lam erased projectedDomain projectedBody)
              | _ => none
          | _ =>
              if ordinary op then do
                let projected ← FamilyEnvironment.mapChecked (skeleton fuel env) arguments
                pure (.node op projected)
              else caseSkeleton (skeleton fuel env) env op arguments

private theorem map_sound {f : Term → Option Term}
    (sound : ∀ term projected, f term = some projected → Skeleton env term projected)
    (h : FamilyEnvironment.mapChecked f terms = some projected) :
    Conversion.ListRel (Skeleton env) terms projected := by
  induction terms generalizing projected with
  | nil => simp only [FamilyEnvironment.mapChecked, Option.some.injEq] at h; cases h; exact .nil
  | cons term rest ih =>
      simp only [FamilyEnvironment.mapChecked] at h
      cases head : f term with
      | none => simp [head] at h
      | some value =>
          simp only [head, Bind.bind, Option.bind] at h
          cases tail : FamilyEnvironment.mapChecked f rest with
          | none => simp [tail] at h
          | some values =>
              simp only [tail] at h
              cases h
              exact .cons (sound _ _ head) (ih tail)

private theorem caseSkeleton_sound
    (sound : ∀ t p, visit t = some p → Skeleton env t p)
    (h : caseSkeleton visit env op arguments = some projected) :
    Skeleton env (.node op arguments) projected := by
  unfold caseSkeleton at h
  cases familyFound : caseFamily op with
  | none => simp [familyFound] at h
  | some family =>
    simp only [familyFound, Bind.bind, Option.bind] at h
    cases found : env.families[family]? with
    | none => simp [found] at h
    | some entry =>
      simp only [found] at h
      split at h
      · rename_i isData
        cases mapped : FamilyEnvironment.mapChecked visit arguments with
        | none => simp [mapped] at h
        | some values =>
          simp only [mapped, pure, Option.some.injEq] at h
          cases h
          exact .familyCases familyFound found isData (map_sound sound mapped)
      · contradiction

theorem skeleton_sound (h : skeleton fuel env term = some projected) : Skeleton env term projected := by
  induction fuel generalizing term projected with
  | zero => simp [skeleton] at h
  | succ fuel ih =>
      cases term with
      | var x => simp only [skeleton, Option.some.injEq] at h; cases h; exact .var x
      | node op arguments =>
          simp only [skeleton] at h
          split at h
          · rename_i family count
            cases found : env.families[family]? with
            | none => simp [found] at h
            | some entry =>
                simp only [found, Bind.bind, Option.bind] at h
                cases h
                exact .familyType found
          · rename_i family constructor count
            cases found : env.families[family]? with
            | none => simp [found] at h
            | some entry =>
                simp only [found, Bind.bind, Option.bind] at h
                cases signatureFound : entry.signatures[constructor]? with
                | none => simp [signatureFound] at h
                | some signature =>
                    simp only [signatureFound] at h
                    split at h
                    · rename_i countOK
                      cases relevant : relevantFields entry.declaration.data signature.fields arguments with
                      | none => simp [relevant] at h
                      | some fields =>
                          simp only [relevant] at h
                          cases mapped : FamilyEnvironment.mapChecked (skeleton fuel env) fields with
                          | none => simp [mapped] at h
                          | some values =>
                              simp only [mapped] at h
                              cases h
                              exact .constructor found signatureFound countOK relevant (map_sound (fun _ _ h => ih h) mapped)
                    · contradiction
          · rename_i family count
            cases found : env.families[family]? with
            | none => simp [found] at h
            | some entry =>
                simp only [found, Bind.bind, Option.bind] at h
                split at h
                · rename_i proof
                  cases h
                  exact .propositionElimination found proof
                · exact caseSkeleton_sound (fun _ _ h => ih h) h
          · rename_i erased
            cases arguments with
            | nil => contradiction
            | cons domain rest =>
                cases rest with
                | nil => contradiction
                | cons body rest =>
                    cases rest with
                    | cons _ _ => contradiction
                    | nil =>
                        cases normalized : Environment.Conversion.normalize? fuel domain with
                        | none => simp [normalized] at h
                        | some normal =>
                            simp only [normalized, Bind.bind, Option.bind] at h
                            cases domainProjected : skeleton fuel env normal with
                            | none => simp [domainProjected] at h
                            | some projectedDomain =>
                                simp only [domainProjected] at h
                                cases bodyProjected : skeleton fuel env body with
                                | none => simp [bodyProjected] at h
                                | some projectedBody =>
                                    simp only [bodyProjected] at h
                                    cases h
                                    exact .lam (Environment.Conversion.normalize?_sound normalized)
                                      (ih domainProjected) (ih bodyProjected)
          · split at h
            · rename_i ordinaryOp
              cases mapped : FamilyEnvironment.mapChecked (skeleton fuel env) arguments with
              | none => simp [mapped] at h
              | some values =>
                  simp only [mapped, Bind.bind, Option.bind] at h
                  cases h
                  exact .node ordinaryOp (map_sound (fun _ _ h => ih h) mapped)
            · exact caseSkeleton_sound (fun _ _ h => ih h) h

def check (fuel : Nat) (env : Environment) (term : Term) : Bool :=
  match skeleton fuel env term with
  | none => false
  | some projected => EnvironmentCaseQuantity.checkClosed fuel
      (EnvironmentCaseQuantity.compileTable env) projected

/-- Every resource table entry has the exact lookup in the same environment.
The control certificate uses the existing finite Control demand semantics. -/
def Safe (env : Environment) (term : Term) : Prop :=
  ∃ projected table, Skeleton env term projected ∧
    EnvironmentCaseQuantity.TableValid env table ∧
    EnvironmentCaseQuantity.ClosedSafe table projected

theorem check_sound (h : check fuel env term = true) : Safe env term := by
  cases projected : skeleton fuel env term with
  | none => simp [check, projected] at h
  | some result =>
      exact ⟨result, EnvironmentCaseQuantity.compileTable env, skeleton_sound projected,
        EnvironmentCaseQuantity.compileTable_valid,
        EnvironmentCaseQuantity.checkClosed_sound (by simpa only [check, projected] using h)⟩

theorem Skeleton.extend (extension : Environment.Extends before after)
    (projected : Skeleton before source target) : Skeleton after source target := by
  induction projected using Skeleton.rec
    (motive_2 := fun terms projected _ => Conversion.ListRel (Skeleton after) terms projected) with
  | var index => exact .var index
  | node ordinary terms ih => exact .node ordinary ih
  | lam converted _ _ domain body => exact .lam converted domain body
  | familyType found => exact .familyType (extension.families _ _ found)
  | constructor found signature count relevant terms ih =>
      exact .constructor (extension.families _ _ found) signature count relevant ih
  | propositionElimination found proof => exact .propositionElimination (extension.families _ _ found) proof
  | familyCases shape found data terms ih => exact .familyCases shape (extension.families _ _ found) data ih
  | nil => exact .nil
  | cons head tail ih iht => exact .cons ih iht

theorem Safe.extend (extension : Environment.Extends before after) (safe : Safe before term) : Safe after term := by
  obtain ⟨target, table, projected, valid, closed⟩ := safe
  exact ⟨target, table, projected.extend extension, valid.extend extension, closed⟩

end Jihoo.NativeKernel.EnvironmentQuantity
