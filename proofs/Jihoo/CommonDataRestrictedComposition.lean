import Jihoo.CommonCompositionContract

/-! Single-program placement for any finite forward list of Case fragments.
This proves installation, not source/compiler correctness. All fragments retain
function zero and the seven-local ABI of CommonDataCaseCfg. -/
set_option linter.unusedSimpArgs false
namespace Jihoo.CommonDataRestrictedComposition
open ReferenceCfg ReferenceCalls CommonDataCaseCfg CommonDataCaseRelocation
open CommonCompositionContract

structure Fragment where
  nilBody : Block
  nodeBody : Block
  src : Nat

def Fragment.blocks (f : Fragment) (base : Nat) : Array Block :=
  (body f.nilBody f.nodeBody).code.base.blocks.map (relocateBlock base) ++
    #[failure, ⟨#[⟨⟨0,false⟩, .use (arg f.src)⟩], .goto base⟩]

@[simp] theorem Fragment.size (f : Fragment) (base : Nat) :
    (f.blocks base).size = 7 := by simp [Fragment.blocks, body]

def installedProgram (blocks : Array Block) : Program :=
  #[⟨⟨⟨#[.ptr,.i64,.ptr,.i64,.ptr,.ptr,.unit], blocks⟩, #[]⟩, #[]⟩]

theorem linked_eq (pre post : Array Block) (f : Fragment) :
    linked pre post f.nilBody f.nodeBody f.src =
      installedProgram (pre ++ f.blocks pre.size ++ post) := by
  simp [linked, installedProgram, Fragment.blocks, body, Array.append_assoc]

/-- Syntactic installation in one fixed program; no execution is assumed. -/
structure Placement (p : Program) (f : Fragment) where
  pre : Array Block
  post : Array Block
  installed : p = installedProgram (pre ++ f.blocks pre.size ++ post)

theorem Placement.program (h : Placement p f) :
    p = linked h.pre h.post f.nilBody f.nodeBody f.src := by
  rw [linked_eq]; exact h.installed

/-- Each block edge is already relocated at its final address. -/
def assemble (base : Nat) : List Fragment → Array Block
  | [] => #[]
  | f :: fs => f.blocks base ++ assemble (base + 7) fs

@[simp] theorem assemble_size (fs : List Fragment) (base : Nat) :
    (assemble base fs).size = 7 * fs.length := by
  induction fs generalizing base with
  | nil => simp [assemble]
  | cons f fs ih => simp [assemble, ih, Nat.mul_add, Nat.add_comm]

/-- Arbitrarily many distinct fragments can be installed simultaneously.
The recursion is on the list tail, never on an execution hypothesis. -/
theorem assemble_placement (fs : List Fragment) (f : Fragment)
    (member : f ∈ fs) (pre post : Array Block) :
    Nonempty (Placement (installedProgram (pre ++ assemble pre.size fs ++ post)) f) := by
  induction fs generalizing pre with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨⟨pre, assemble (pre.size + 7) tail ++ post, by
        simp [assemble, Array.append_assoc]⟩⟩
    · obtain ⟨placed⟩ := ih member (pre ++ head.blocks pre.size)
      exact ⟨⟨placed.pre, placed.post, by
        simpa [assemble, Array.append_assoc] using placed.installed⟩⟩

/-- Reuse a prefix certificate by equality of the entire program, without
changing programs at a recursive seam. -/
theorem Placement.walk (h : Placement p f)
    (run : CommonDataCaseRelocation.walk
      (linked h.pre h.post f.nilBody f.nodeBody f.src) n limit s = some (t, es)) :
    CommonDataCaseRelocation.walk p n limit s = some (t, es) := by
  rw [h.program]; exact run

/-- Every installed fragment retains the copied Node prefix in the same p. -/
theorem Placement.node_entry (h : Placement p f)
    (found : H[j]? = some (ReferenceHeap.node (.object l 0) (.object r 0)))
    (selected : vs[f.src]? = some (some (.pointer j 0)))
    (space : 7 ≤ vs.size) (bound : ks.length ≤ limit) :
    CommonDataCaseRelocation.walk p 11 limit
      (stateAt H vs (h.pre.size + 6) ks) =
      some (stateAt H (nodeLocals (vs.set! 0 (some (.pointer j 0))) j l r)
        (h.pre.size + 4) ks, []) := by
  apply h.walk
  exact node_copied_entry (fuel := 11) h.pre h.post f.nilBody f.nodeBody f.src
    found selected space bound (by omega)

/-- Every installed fragment retains the copied Nil prefix in the same p. -/
theorem Placement.nil_entry (h : Placement p f)
    (found : H[j]? = some ReferenceHeap.nilObject)
    (selected : vs[f.src]? = some (some (.pointer j 0)))
    (space : 7 ≤ vs.size) (bound : ks.length ≤ limit) :
    CommonDataCaseRelocation.walk p 5 limit
      (stateAt H vs (h.pre.size + 6) ks) =
      some (stateAt (CommonDataReference.retired H j ReferenceHeap.nilObject)
        (nilLocals (vs.set! 0 (some (.pointer j 0))))
        (h.pre.size + 3) ks, [.free j]) := by
  apply h.walk
  exact nil_copied_entry (fuel := 5) h.pre h.post f.nilBody f.nodeBody f.src
    found selected space bound (by omega)

/-- A concrete two-fragment layout. Parent bodies may jump forward to the
child copied entry at relative address 13 (= seven blocks + six). -/
def forward : Block := ⟨#[], .goto 13⟩
def parent (src : Nat) : Fragment := ⟨forward, forward, src⟩

def nestedProgram (pre post : Array Block) (src : Nat) (child : Fragment) : Program :=
  installedProgram (pre ++ assemble pre.size [parent src, child] ++ post)

def parentPlacement (pre post : Array Block) (src : Nat) (child : Fragment) :
    Placement (nestedProgram pre post src child) (parent src) :=
  ⟨pre, child.blocks (pre.size + 7) ++ post, by
    simp [nestedProgram, assemble, Array.append_assoc]⟩

def childPlacement (pre post : Array Block) (src : Nat) (child : Fragment) :
    Placement (nestedProgram pre post src child) child :=
  ⟨pre ++ (parent src).blocks pre.size, post, by
    simp [nestedProgram, assemble, Array.append_assoc]⟩

set_option maxRecDepth 10000 in
/-- A branch trampoline really reaches the next copied entry in one tick,
with identical heap, locals and callers, in the fixed two-fragment program. -/
theorem nested_jump (pre post : Array Block) (src : Nat) (child : Fragment)
    (branch : b = 3 ∨ b = 4) (bound : ks.length ≤ limit) :
    CommonDataCaseRelocation.walk (nestedProgram pre post src child) 1 limit
      (stateAt H vs (pre.size + b) ks) =
      some (stateAt H vs (pre.size + 13) ks, []) := by
  rw [(parentPlacement pre post src child).program]
  rcases branch with rfl | rfl <;>
    simp [parentPlacement, parent, forward, CommonDataCaseRelocation.walk,
      linked, body, relocateBlock, relocateTerm, ReferenceCalls.tick,
      ReferenceCalls.extension, ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick,
      ReferenceCfg.fetch, ReferenceCfg.jump, ReferenceCalls.liftLegacy,
      stateAt, stackDepth, bound, Nat.not_lt.mpr bound,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- A placement-indexed structural theorem: the one program p is fixed outside
induction. Only smaller supported children are available to the step. This is
an eliminator, NOT an inhabitant of a body-correctness provider. -/
theorem placed_induction (g : CommonDataSource.Graph) (p : Program)
    (Layout : Program → Nat → Type) (P : (t : Nat) → Layout p t → Prop)
    (step : ∀ t, Supported g t → ∀ layout : Layout p t,
      (∀ child, child < t → Supported g child → ∀ lc : Layout p child, P child lc) →
      P t layout) (supported : Supported g term) (layout : Layout p term) :
    P term layout := by
  have all : ∀ l : Layout p term, P term l :=
    supported_induction g (fun t => ∀ l : Layout p t, P t l)
      (fun t hs ih l => step t hs l ih) supported
  exact all layout

end Jihoo.CommonDataRestrictedComposition
