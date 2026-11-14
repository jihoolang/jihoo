import Jihoo.NativeTyping
import Jihoo.NativeKernelEnvironment
import Jihoo.NativeBackSyntax

/-! Concrete native data telescopes. Parameters are substituted out of the
closed checked constructor signature; every remaining field retains its own
scope. Recursive hypotheses follow all fields, exactly as in Core. -/
namespace Jihoo.NativeKernel.Environment

@[simp] theorem dataCaseOp_arity (analysis : Bool) (family count : Nat) :
    (if analysis then Op.caseOf family count else Op.elim family count).arity = count + 2 := by
  cases analysis <;> rfl

@[simp] theorem dataCaseOp_binders (analysis : Bool) (family count i : Nat) :
    (if analysis then Op.caseOf family count else Op.elim family count).binders i = 0 := by
  cases analysis <;> rfl

/-- Apply arguments in declaration order. -/
def applications (f : Term) (xs : List Term) : Term := xs.foldl Term.app f

/-- The checked, expanded constructor telescope, independent of raw aliases. -/
def signatureTerm (family : Nat) (signature : Signature) : Term :=
  signature.fields.foldr (fun field rest => .pi field.erased field.domain rest)
    (.node (.ind family signature.result.length) signature.result)

def recursiveFields (fields : List Field) : List (Nat × List Term) :=
  fields.zipIdx.filterMap fun (field, j) => field.recursive.map fun xs => (j, xs)

/-- Substitute leading parameters, dropping exactly their binders. -/
def instantiateParameters : List Term → Term → Option Term
  | [], t => some t
  | p :: ps, .pi _ _ rest =>
      instantiateParameters ps (rest.subst (fun | 0 => p | n + 1 => .var n))
  | _ :: _, _ => none

/-- Peel the known field count; never consume a function returned by a motive. -/
def peelDataFields : Nat → Term → Option (List (Bool × Term) × Term)
  | 0, t => some ([], t)
  | n + 1, .pi erased domain rest => do
      let (fields, result) ← peelDataFields n rest
      pure ((erased, domain) :: fields, result)
  | _ + 1, _ => none

def closeDataFields (fields : List (Bool × Term)) (result : Term) : Term :=
  fields.foldr (fun field body => .pi field.1 field.2 body) result

def u64Telescope : Nat → Term → Term
  | 0, result => result
  | n + 1, result => .pi false .u64 (u64Telescope n result)

/-- The motive takes nonparameter indices and then the actual family value. -/
def dataMotiveType (family params arity : Nat) (ps : List Term) (proof : Bool) : Term :=
  let r := arity - params
  let domain := Term.node (.ind family arity)
    (ps.map (Term.rename (fun x => x + r)) ++
      (List.range r).map (fun j => Term.var (r - 1 - j)))
  u64Telescope r (.pi false domain (loopSortTerm proof))

/-- Core.data_case_type and Core.recursion_case_type on admitted metadata.
The context depth weakens the closed signature before parameter substitution. -/
def dataCaseTypeSource (family constructor params depth : Nat) (signature : Signature)
    (ps : List Term) (motive : Term) (recursion proof : Bool) : Option Term := do
  if ps.length != params || params > signature.fields.length then none else
  let telescope ← instantiateParameters ps
    ((signatureTerm family signature).rename (fun x => x + depth))
  let (fields, terminal) ← peelDataFields (signature.fields.length - params) telescope
  let .node (.ind resultFamily _) indices := terminal | none
  if resultFamily != family then none else
  let m := fields.length
  let values := ps.map (Term.rename (fun x => x + m)) ++
    (List.range m).map (fun j => Term.var (m - 1 - j))
  let base := Term.app
    (applications (motive.rename (fun x => x + m)) (indices.drop params))
    (.node (.con family constructor values.length) values)
  if !recursion then some (closeDataFields fields base) else
  let recursive := fields.zipIdx.filterMap fun ((_, domain), j) =>
    match domain with
    | .node (.ind g _) xs => if g == family then some (j, xs) else none
    | _ => none
  let r := recursive.length
  let mut result := base.rename (fun x => x + r)
  for ((position, xs), q) in recursive.zipIdx.reverse do
    let ih := Term.app
      (applications (motive.rename (fun x => x + m + q))
        ((xs.drop params).map (Term.rename (fun x => x + (m + q - position)))))
      (.var (m - 1 - position + q))
    result := .pi proof ih result
  let annotated := fields.map fun (erased, domain) =>
    match domain with
    | .node (.ind g _) _ => (if g == family then true else erased, domain)
    | _ => (erased, domain)
  some (closeDataFields annotated result)

/-- Substitute the actual parameter values beneath `locals` retained fields.
The last branch concerns only malformed free variables of a closed signature. -/
def parameterAt (depth locals : Nat) (ps : List Term) (x : Nat) : Term :=
  if x < locals then .var x else
    ((ps.reverse[x - locals]?).map (Term.rename (fun i => i + locals))).getD
      (.var (x - ps.length + depth))

def instantiatedFields (depth : Nat) (ps : List Term) (recursion : Bool) :
    Nat → List Field → List (Bool × Term)
  | _, [] => []
  | position, field :: fields =>
      (if recursion && field.recursive.isSome then true else field.erased,
        field.domain.subst (parameterAt depth position ps)) ::
      instantiatedFields depth ps recursion (position + 1) fields

def instantiatedRecursive (depth : Nat) (ps : List Term) (fields : List Field) : List (Nat × List Term) :=
  (recursiveFields fields).map fun (position, indices) =>
    (position, indices.map (Term.subst (parameterAt depth position ps)))

def dataHypothesisType (params fields : Nat) (motive : Term)
    (recursive : Nat × List Term) (q : Nat) : Term :=
  .app (applications (motive.rename (fun x => x + fields + q))
    ((recursive.2.drop params).map (Term.rename (fun x => x + (fields + q - recursive.1)))))
    (.var (fields - 1 - recursive.1 + q))

def dataHypothesisTelescope (params fields offset : Nat) (recursive : List (Nat × List Term))
    (proof : Bool) (motive body : Term) : Term :=
  (recursive.zipIdx offset).foldr (fun (field, q) rest =>
    .pi proof (dataHypothesisType params fields motive field q) rest) body

def dataCaseResult (family constructor params fields hypotheses : Nat)
    (ps : List Term) (motive : Term) (indices : List Term) : Term :=
  let values := ps.map (Term.rename (fun x => x + fields + hypotheses)) ++
    (List.range fields).map (fun j => Term.var (fields - 1 - j + hypotheses))
  .app (applications (motive.rename (fun x => x + fields + hypotheses))
    ((indices.drop params).map (Term.rename (fun x => x + hypotheses))))
    (.node (.con family constructor values.length) values)

/-- The same native telescope written directly from checked field positions.
Recursive erasure is determined by the checked recursive marker, never by
inspecting an arbitrary substituted type head. -/
def dataCaseType (family constructor params depth : Nat) (signature : Signature)
    (ps : List Term) (motive : Term) (recursion proof : Bool) : Option Term :=
  if ps.length != params || params > signature.fields.length then none else
  let fields := signature.fields.drop params
  let m := fields.length
  let recursive := if recursion then instantiatedRecursive depth ps fields else []
  let r := recursive.length
  let result := dataCaseResult family constructor params m r ps motive
    (signature.result.map (Term.subst (parameterAt depth m ps)))
  some (closeDataFields (instantiatedFields depth ps recursion 0 fields)
    (dataHypothesisTelescope params m 0 recursive proof motive result))

/-- One concrete expected type for every checked constructor, with its true id. -/
def dataCaseTypes (family params depth : Nat) (signatures : List Signature)
    (ps : List Term) (motive : Term) (recursion proof : Bool) : Option (List Term) :=
  signatures.zipIdx.mapM fun (signature, constructor) =>
    dataCaseType family constructor params depth signature ps motive recursion proof

/-- Parameter substitution and field peeling have an exact structural witness. -/
inductive ParametersInstantiated : List Term → Term → Term → Prop where
  | nil : ParametersInstantiated [] t t
  | cons : ParametersInstantiated ps
      (rest.subst (fun | 0 => p | n + 1 => .var n)) result →
      ParametersInstantiated (p :: ps) (.pi erased domain rest) result

 theorem instantiateParameters_sound (h : instantiateParameters ps telescope = some result) :
    ParametersInstantiated ps telescope result := by
  induction ps generalizing telescope with
  | nil => simp only [instantiateParameters, Option.some.injEq] at h; cases h; exact .nil
  | cons p ps ih =>
      cases telescope with
      | var x => simp [instantiateParameters] at h
      | node op args =>
          cases op <;> try simp [instantiateParameters] at h
          case pi erased =>
            cases args with
            | nil => simp [instantiateParameters] at h
            | cons domain args => cases args with
              | nil => simp [instantiateParameters] at h
              | cons rest args => cases args with
                | nil => exact .cons (ih h)
                | cons _ _ => simp [instantiateParameters] at h

 theorem peelDataFields_length
    (h : peelDataFields n telescope = some (fields, result)) : fields.length = n := by
  induction n generalizing telescope fields with
  | zero => simp only [peelDataFields, Option.some.injEq, Prod.mk.injEq] at h; simp [← h.1]
  | succ n ih =>
      cases telescope with
      | var x => simp [peelDataFields] at h
      | node op args =>
          cases op <;> try simp [peelDataFields] at h
          case pi erased =>
            cases args with
            | nil => simp [peelDataFields] at h
            | cons domain args => cases args with
              | nil => simp [peelDataFields] at h
              | cons rest args => cases args with
                | cons _ _ => simp [peelDataFields] at h
                | nil =>
                    cases peeled : peelDataFields n rest with
                    | none => simp [peelDataFields, peeled] at h
                    | some pair =>
                        rcases pair with ⟨tail, terminal⟩
                        simp only [peelDataFields, peeled, Bind.bind, Option.bind,
                          pure, Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simpa only [List.length_cons] using congrArg Nat.succ (ih peeled)

/-- Native reading preserves this binder, replacing its value by Deref(var0).
Unlike ordinary parameter substitution, higher variables are not decremented. -/
def reading (rest : Term) : Term :=
  rest.subst (fun | 0 => .deref (.var 0) | n + 1 => .var (n + 1))

@[simp] theorem reading_zero : reading (.var 0) = .deref (.var 0) := by simp only [reading, Term.subst]
@[simp] theorem reading_succ (n : Nat) : reading (.var (n + 1)) = .var (n + 1) := by simp only [reading, Term.subst]

end Jihoo.NativeKernel.Environment
