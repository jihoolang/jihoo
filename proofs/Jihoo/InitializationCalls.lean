import Jihoo.InitializationStore

/-! Interprocedural local-store safety. Calls save the caller, create a fresh
callee frame, and install the returned value only after return. This explicit
machine is not an asserted translation of native MIR or heap semantics. -/
namespace Jihoo.Initialization.Calls
open Store

inductive Argument where
  | slot (id : Nat)
  | constant (token : Nat)
  deriving Repr, DecidableEq

def argumentReads : List Argument → Facts
  | [] => []
  | .slot i :: rest => i :: argumentReads rest
  | .constant _ :: rest => argumentReads rest

def readArguments (constants : Nat → α) (memory : Memory α) : List Argument → Option (List α)
  | [] => some []
  | .slot i :: rest => do
      let value ← memory i
      let values ← readArguments constants memory rest
      pure (value :: values)
  | .constant token :: rest =>
      (readArguments constants memory rest).map (constants token :: ·)

theorem arguments_exist (covered : Covers (argumentReads args) memory) :
    ∃ values, readArguments constants memory args = some values := by
  induction args with
  | nil => exact ⟨[], rfl⟩
  | cons arg rest ih =>
      cases arg with
      | slot i =>
          obtain ⟨v, hv⟩ := covered i (by simp [argumentReads])
          obtain ⟨vs, hvs⟩ := ih (fun j hj => covered j (by simp [argumentReads, hj]))
          exact ⟨v :: vs, by simp [readArguments, hv, hvs]⟩
      | constant token =>
          obtain ⟨vs, hvs⟩ := ih covered
          exact ⟨constants token :: vs, by simp [readArguments, hvs]⟩

theorem arguments_length (h : readArguments constants memory args = some values) :
    values.length = args.length := by
  induction args generalizing values with
  | nil => simp [readArguments] at h; subst values; rfl
  | cons arg rest ih =>
      cases arg with
      | slot i =>
          cases hm : memory i with
          | none => simp [readArguments, hm] at h
          | some value =>
              cases hr : readArguments constants memory rest with
              | none => simp [readArguments, hm, hr] at h
              | some tail =>
                  simp [readArguments, hm, hr] at h
                  subst values
                  simp [ih hr]
      | constant token =>
          cases hr : readArguments constants memory rest with
          | none => simp [readArguments, hr] at h
          | some tail =>
              simp [readArguments, hr] at h
              subst values
              simp [ih hr]

inductive Instruction where
  | action (effect : Action) (next : Nat)
  | branch (reads : Facts) (targets : List Nat)
  | call (callee : Nat) (arguments : List Argument) (destination next : Nat)
  | ret
  | stop
  deriving Repr, DecidableEq

def Instruction.block : Instruction → Block
  | .action a next => ⟨[a], [next]⟩
  | .branch reads targets => ⟨[⟨reads, []⟩], targets⟩
  | .call _ args dest next => ⟨[⟨argumentReads args, [dest]⟩], [next]⟩
  | .ret => ⟨[⟨[0], []⟩], []⟩
  | .stop => ⟨[], []⟩

structure Function where
  parameters : Nat
  unitResult : Bool
  code : List (Nat × Instruction)
  certificate : Certificate

def Function.graph (f : Function) : Graph :=
  f.code.map (fun row => (row.1, row.2.block))

def Function.initial (f : Function) : Facts :=
  (if f.unitResult then [0] else []) ++ List.range' 1 f.parameters

def Function.entry (f : Function) (unit : α) (args : List α) : Memory α :=
  enter (if f.unitResult then some unit else none) args

abbrev Program := List Function

def Checked (p : Program) : Prop :=
  ∀ f ∈ p, check f.graph f.initial f.certificate = true

def callTargets (p : Program) (instruction : Instruction) : Bool :=
  match instruction with
  | .call callee args _ _ => match p[callee]? with
      | none => false
      | some target => args.length == target.parameters
  | _ => true

def validate (p : Program) : Bool :=
  p.all (fun f => check f.graph f.initial f.certificate) &&
    p.all (fun f => f.code.all (fun row => callTargets p row.2))

theorem validate_sound (h : validate p = true) : Checked p :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1

theorem validated_call (h : validate p = true) (hf : f ∈ p)
    (member : (pc, .call callee args dest next) ∈ f.code) :
    ∃ target, p[callee]? = some target ∧ args.length = target.parameters := by
  have hf' := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 f hf
  have hc := List.all_eq_true.mp hf' _ member
  simp only [callTargets] at hc
  cases ht : p[callee]? with
  | none => simp [ht] at hc
  | some target => exact ⟨target, rfl, by simpa [ht] using hc⟩

def Covered (p : Program) (fid pc : Nat) (memory : Memory α) : Prop :=
  ∃ f facts, p[fid]? = some f ∧ f.certificate pc = some facts ∧ Covers facts memory

structure Resume (α : Type) where
  caller : Nat
  next : Nat
  destination : Nat
  memory : Memory α

def StackSafe (p : Program) (stack : List (Resume α)) : Prop :=
  ∀ frame ∈ stack, ∀ value,
    Covered p frame.caller frame.next (write frame.memory frame.destination value)

inductive State (α : Type) where
  | active (function pc : Nat) (memory : Memory α) (stack : List (Resume α))
  | finished (value : Option α)
  | uninitialized

/-- No initialization or certificate premise appears in machine transitions.
Action traps and malformed results terminate without a returned value. Missing
code/callees or wrong arities have no transition: progress is not claimed. -/
inductive Step (p : Program) (unit : α) (constants : Nat → α) : State α → State α → Prop where
  | action : p[fid]? = some f → (pc, .action effect next) ∈ f.code →
      execute operation [effect] memory = .normal result →
      Step p unit constants (.active fid pc memory stack) (.active fid next result stack)
  | actionFault : p[fid]? = some f → (pc, .action effect next) ∈ f.code →
      execute operation [effect] memory = .uninitialized →
      Step p unit constants (.active fid pc memory stack) .uninitialized
  | actionTrap : p[fid]? = some f → (pc, .action effect next) ∈ f.code →
      execute operation [effect] memory = .trap →
      Step p unit constants (.active fid pc memory stack) (.finished none)
  | actionBadResult : p[fid]? = some f → (pc, .action effect next) ∈ f.code →
      execute operation [effect] memory = .badResult →
      Step p unit constants (.active fid pc memory stack) (.finished none)
  | branch : p[fid]? = some f → (pc, .branch reads targets) ∈ f.code →
      readMany memory reads = some values → next ∈ targets →
      Step p unit constants (.active fid pc memory stack) (.active fid next memory stack)
  | branchFault : p[fid]? = some f → (pc, .branch reads targets) ∈ f.code →
      readMany memory reads = none → Step p unit constants (.active fid pc memory stack) .uninitialized
  | call : p[fid]? = some f → (pc, .call callee args dest next) ∈ f.code →
      readArguments constants memory args = some values → p[callee]? = some target →
      values.length = target.parameters →
      Step p unit constants (.active fid pc memory stack)
        (.active callee 0 (target.entry unit values) (⟨fid, next, dest, memory⟩ :: stack))
  | callFault : p[fid]? = some f → (pc, .call callee args dest next) ∈ f.code →
      readArguments constants memory args = none → Step p unit constants (.active fid pc memory stack) .uninitialized
  | ret : p[fid]? = some f → (pc, .ret) ∈ f.code → memory 0 = some value →
      Step p unit constants (.active fid pc memory (frame :: stack))
        (.active frame.caller frame.next (write frame.memory frame.destination value) stack)
  | finish : p[fid]? = some f → (pc, .ret) ∈ f.code → memory 0 = some value →
      Step p unit constants (.active fid pc memory []) (.finished (some value))
  | returnFault : p[fid]? = some f → (pc, .ret) ∈ f.code → memory 0 = none →
      Step p unit constants (.active fid pc memory stack) .uninitialized
  | stop : p[fid]? = some f → (pc, .stop) ∈ f.code →
      Step p unit constants (.active fid pc memory stack) (.finished none)

def Invariant (p : Program) : State α → Prop
  | .active fid pc memory stack => Covered p fid pc memory ∧ StackSafe p stack
  | .finished _ => True
  | .uninitialized => False

private theorem checked_row (checked : Checked p) (hf : p[fid]? = some f)
    (member : (pc, instruction) ∈ f.code) (covered : Covered p fid pc memory) :
    ∃ facts out, Covers facts memory ∧
      run instruction.block.actions facts = some out ∧
      ∀ next, next ∈ instruction.block.successors →
        ∃ incoming, f.certificate next = some incoming ∧ Sub incoming out := by
  obtain ⟨f', facts, hf', hc, cover⟩ := covered
  have : f' = f := Option.some.inj (hf'.symm.trans hf)
  subst f'
  obtain ⟨out, hr, edges⟩ := check_block (checked f (List.mem_of_getElem? hf))
    (List.mem_map.mpr ⟨(pc, instruction), member, rfl⟩) hc
  exact ⟨facts, out, cover, hr, edges⟩

private theorem singleton_run (h : run [⟨reads, writes⟩] facts = some out) :
    Sub reads facts ∧ out = writes ++ facts := by
  simp only [run] at h
  split at h
  next hr => exact ⟨subset_sound hr, (Option.some.inj h).symm⟩
  next => contradiction

 theorem entry_covered (checked : Checked p) (hf : p[fid]? = some f)
    (arity : args.length = f.parameters) : Covered p fid 0 (f.entry unit args) := by
  obtain ⟨facts, hc, hs⟩ := check_entry (checked f (List.mem_of_getElem? hf))
  refine ⟨f, facts, hf, hc, covers_sub hs ?_⟩
  have eq : entryFacts (if f.unitResult then some unit else none) args = f.initial := by
    cases he : f.unitResult <;> simp [entryFacts, Function.initial, he, arity]
  rw [← eq]
  exact enter_covers

/-- Every return value is safe to install in the saved caller. This obligation
is derived at call time, and does not assume the callee terminates or succeeds. -/
theorem call_continuation (checked : Checked p) (hf : p[fid]? = some f)
    (member : (pc, .call callee args dest next) ∈ f.code)
    (covered : Covered p fid pc memory) :
    (∃ values, readArguments constants memory args = some values) ∧
      ∀ value, Covered p fid next (write memory dest value) := by
  obtain ⟨facts, out, cover, hr, edges⟩ := checked_row checked hf member covered
  obtain ⟨reads, rfl⟩ := singleton_run hr
  obtain ⟨incoming, hn, hs⟩ := edges next (by simp [Instruction.block])
  exact ⟨arguments_exist (covers_sub reads cover),
    fun value => ⟨f, incoming, hf, hn, covers_sub hs (covers_write cover)⟩⟩

/-- Accepted call targets and arities discharge the machine's call guards.
This is local call progress, not a global termination/progress theorem. -/
theorem validated_call_ready (accepted : validate p = true) (hf : p[fid]? = some f)
    (member : (pc, .call callee args dest next) ∈ f.code)
    (covered : Covered p fid pc memory) :
    ∃ target : Function, ∃ values, Step p unit constants (.active fid pc memory stack)
      (.active callee 0 (target.entry unit values) (⟨fid, next, dest, memory⟩ :: stack)) := by
  obtain ⟨target, ht, arity⟩ := validated_call accepted (List.mem_of_getElem? hf) member
  obtain ⟨⟨values, hv⟩, _⟩ := call_continuation (constants := constants)
    (validate_sound accepted) hf member covered
  exact ⟨target, values, .call hf member hv ht ((arguments_length hv).trans arity)⟩

/-- Caller memory is restored from the suspended frame, not from callee locals.
Recursion depth and repeated invocations are unrestricted in finite traces. -/
theorem preservation (checked : Checked p) (valid : Invariant p s)
    (step : Step p unit constants s t) : Invariant p t := by
  cases step with
  | action hf member executed =>
      obtain ⟨cover, stack⟩ := valid
      obtain ⟨facts, out, cover, hr, edges⟩ := checked_row checked hf member cover
      obtain ⟨incoming, hn, hs⟩ := edges _ (by exact List.mem_cons_self)
      exact ⟨⟨_, incoming, hf, hn,
        covers_sub hs (normal_result_covered hr cover executed)⟩, stack⟩
  | actionFault hf member failed =>
      rename_i fid f pc operation effect memory stack next
      obtain ⟨facts, out, cover, hr, _⟩ := checked_row checked hf member valid.1
      have h := execution_sound (operation := operation) hr cover
      simp only [Instruction.block] at h
      rw [failed] at h
      exact h
  | actionTrap | actionBadResult | finish | stop => trivial
  | branch hf member _ target =>
      obtain ⟨facts, out, cover, hr, edges⟩ := checked_row checked hf member valid.1
      obtain ⟨_, rfl⟩ := singleton_run hr
      obtain ⟨incoming, hn, hs⟩ := edges _ target
      exact ⟨⟨_, incoming, hf, hn, covers_sub hs cover⟩, valid.2⟩
  | branchFault hf member failed =>
      obtain ⟨facts, out, cover, hr, _⟩ := checked_row checked hf member valid.1
      obtain ⟨reads, _⟩ := singleton_run hr
      obtain ⟨values, hv⟩ := readMany_exists (covers_sub reads cover)
      rw [failed] at hv
      contradiction
  | call hf member _ target arity =>
      obtain ⟨_, continuation⟩ := call_continuation (constants := constants) checked hf member valid.1
      refine ⟨entry_covered checked target arity, ?_⟩
      intro frame hmem value
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact continuation value
      · exact valid.2 frame hmem value
  | callFault hf member failed =>
      obtain ⟨⟨values, hv⟩, _⟩ := call_continuation (constants := constants) checked hf member valid.1
      rw [failed] at hv
      contradiction
  | ret hf member returned =>
      exact ⟨valid.2 _ (by simp) _, fun frame hmem => valid.2 frame (by simp [hmem])⟩
  | returnFault hf member failed =>
      obtain ⟨facts, out, cover, hr, _⟩ := checked_row checked hf member valid.1
      obtain ⟨reads, _⟩ := singleton_run hr
      obtain ⟨value, hv⟩ := cover 0 (reads 0 (by simp))
      rw [failed] at hv
      contradiction

inductive Reaches (p : Program) (unit : α) (constants : Nat → α) (start : State α) : State α → Prop where
  | refl : Reaches p unit constants start start
  | next : Reaches p unit constants start s → Step p unit constants s t → Reaches p unit constants start t

 theorem reaches_invariant (checked : Checked p) (valid : Invariant p start)
    (reach : Reaches p unit constants start state) : Invariant p state := by
  induction reach with
  | refl => exact valid
  | next _ step ih => exact preservation checked ih step

/-- No precondition assumes safe calls, safe returns, a bound on recursion, or
normal completion. Arity is required only for the initial external invocation. -/
theorem no_uninitialized (checked : Checked p) (hf : p[fid]? = some f)
    (arity : args.length = f.parameters)
    (reach : Reaches p unit constants (.active fid 0 (f.entry unit args) []) state) :
    state ≠ .uninitialized := by
  have valid : Invariant p (.active fid 0 (f.entry unit args) []) :=
    ⟨entry_covered checked hf arity, by simp [StackSafe]⟩
  have result := reaches_invariant checked valid reach
  intro h
  rw [h] at result
  exact result

end Jihoo.Initialization.Calls
