import Std

/-! Executable invariant checking for finite local-read/write control flow.
The operational reachability relation does not assume reads are initialized.
Native MIR projection, value semantics and heap state remain outside this model. -/
namespace Jihoo.Initialization

abbrev Facts := List Nat

def Sub (a b : Facts) : Prop := ∀ x, x ∈ a → x ∈ b

def subset (a b : Facts) : Bool := a.all (fun x => b.contains x)

 theorem subset_sound (h : subset a b = true) : Sub a b := by
  intro x hx
  simpa using (List.all_eq_true.mp h) x hx

 theorem sub_trans (ab : Sub a b) (bc : Sub b c) : Sub a c :=
  fun x hx => bc x (ab x hx)

 theorem sub_append (h : Sub a b) : Sub (w ++ a) (w ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with hw | ha
  · exact List.mem_append_left _ hw
  · exact List.mem_append_right _ (h x ha)

structure Action where
  reads : Facts
  writes : Facts
  deriving Repr, DecidableEq

structure Block where
  actions : List Action
  successors : List Nat
  deriving Repr, DecidableEq

abbrev Graph := List (Nat × Block)
abbrev Certificate := Nat → Option Facts

def run : List Action → Facts → Option Facts
  | [], s => some s
  | a :: rest, s => if subset a.reads s then run rest (a.writes ++ s) else none

def evolve : List Action → Facts → Facts
  | [], s => s
  | a :: rest, s => evolve rest (a.writes ++ s)

def Safe : List Action → Facts → Prop
  | [], _ => True
  | a :: rest, s => Sub a.reads s ∧ Safe rest (a.writes ++ s)

/-- A successful abstract block check covers every concrete initialized set
containing its input facts, and checks reads before adding writes. -/
theorem run_sound (actions : List Action) (h : run actions facts = some out)
    (covered : Sub facts actual) :
    Safe actions actual ∧ Sub out (evolve actions actual) := by
  induction actions generalizing facts out actual with
  | nil =>
      simp [run] at h
      subst out
      exact ⟨True.intro, covered⟩
  | cons a rest ih =>
      simp only [run] at h
      split at h
      next hr =>
        obtain ⟨safe, result⟩ := ih h (sub_append covered)
        exact ⟨⟨sub_trans (subset_sound hr) covered, safe⟩, result⟩
      next => contradiction

def hasBlock (g : Graph) (pc : Nat) : Bool := g.any (fun row => row.1 == pc)

def edge (g : Graph) (cert : Certificate) (out : Facts) (next : Nat) : Bool :=
  hasBlock g next && match cert next with
    | none => false
    | some facts => subset facts out

def row (g : Graph) (cert : Certificate) (entry : Nat × Block) : Bool :=
  match cert entry.1 with
  | none => true
  | some facts => match run entry.2.actions facts with
    | none => false
    | some out => entry.2.successors.all (edge g cert out)

def check (g : Graph) (initial : Facts) (cert : Certificate) : Bool :=
  hasBlock g 0 &&
    (match cert 0 with | none => false | some facts => subset facts initial) &&
    g.all (row g cert)

 theorem check_entry (h : check g initial cert = true) :
    ∃ facts, cert 0 = some facts ∧ Sub facts initial := by
  simp only [check, Bool.and_eq_true] at h
  cases hc : cert 0 with
  | none => simp [hc] at h
  | some facts => exact ⟨facts, rfl, subset_sound (by simpa [hc] using h.1.2)⟩

 theorem check_block (h : check g initial cert = true)
    (member : (pc, b) ∈ g) (hc : cert pc = some facts) :
    ∃ out, run b.actions facts = some out ∧
      ∀ next, next ∈ b.successors →
        ∃ incoming, cert next = some incoming ∧ Sub incoming out := by
  simp only [check, Bool.and_eq_true] at h
  have hr := List.all_eq_true.mp h.2 (pc, b) member
  simp only [row, hc] at hr
  cases ho : run b.actions facts with
  | none => simp [ho] at hr
  | some out =>
      refine ⟨out, rfl, ?_⟩
      intro next hn
      have he := List.all_eq_true.mp (by simpa [ho] using hr) next hn
      simp only [edge, Bool.and_eq_true] at he
      have hs := he.2
      cases hncert : cert next with
      | none => simp [hncert] at hs
      | some incoming =>
          exact ⟨incoming, rfl, subset_sound (by simpa [hncert] using hs)⟩

/-- Nondeterministic CFG reachability, including loops. No read-safety premise
appears in either constructor. Calls' normal-return writes belong to actions. -/
inductive Reach (g : Graph) (initial : Facts) : Nat → Facts → Prop where
  | entry : Reach g initial 0 initial
  | step : Reach g initial pc state → (pc, b) ∈ g → next ∈ b.successors →
      Reach g initial next (evolve b.actions state)

/-- Accepted certificates cover every finite reachable state, irrespective of
predecessor order, cycles, or how the certificate was produced. -/
theorem reachable_covered (h : check g initial cert = true)
    (reach : Reach g initial pc state) :
    ∃ facts, cert pc = some facts ∧ Sub facts state := by
  induction reach with
  | entry => exact check_entry h
  | step prior member successor ih =>
      obtain ⟨facts, hc, cover⟩ := ih
      obtain ⟨out, hr, edges⟩ := check_block h member hc
      obtain ⟨incoming, hn, hs⟩ := edges _ successor
      exact ⟨incoming, hn, sub_trans hs (run_sound _ hr cover).2⟩

/-- Main safety endpoint: all reads in every reachable block are initialized
before its writes. Unreachable blocks cannot supply facts to reachable edges. -/
theorem accepted_reads_safe (h : check g initial cert = true)
    (reach : Reach g initial pc state) (member : (pc, b) ∈ g) :
    Safe b.actions state := by
  obtain ⟨facts, hc, cover⟩ := reachable_covered h reach
  obtain ⟨out, hr, _⟩ := check_block h member hc
  exact (run_sound _ hr cover).1

end Jihoo.Initialization
