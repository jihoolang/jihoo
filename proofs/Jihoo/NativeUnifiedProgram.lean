import Jihoo.NativeEnvironmentWellFormed
import Jihoo.NativeEnvironmentQuantity
import Jihoo.NativeUnifiedFamilies
import Jihoo.NativeEnvironmentExtension
import Jihoo.NativeFamilyEnvironment

/-! Unified mixed declaration admission. Every annotation and value is checked
against the actual earlier global/family prefix. Signatures are recomputed from
source constructor telescopes and never accepted as external evidence. -/
namespace Jihoo.NativeKernel.UnifiedProgram

open Environment

/-- Sort-derived declaration typing and metadata-derived runtime quantities. -/
def ExpandedValid (env : Environment) (declaration : GlobalDeclaration) : Prop :=
  ∃ sort : SortTag, Environment.HasType env [] true declaration.type sort.term ∧
    Environment.HasType env [] (Definitions.bodyMode sort) declaration.value declaration.type ∧
    (Definitions.bodyMode sort = false → EnvironmentQuantity.Safe env declaration.value)

def checkExpanded (fuel quantityFuel : Nat) (env : Environment) (declaration : GlobalDeclaration) : Bool :=
  match Environment.Checker.sort fuel env [] declaration.type with
  | none => false
  | some sort => Environment.Checker.check fuel env [] (Definitions.bodyMode sort) declaration.value declaration.type &&
      (Definitions.bodyMode sort || EnvironmentQuantity.check quantityFuel env declaration.value)

theorem checkExpanded_sound (accepted : checkExpanded fuel quantityFuel env declaration = true) :
    ExpandedValid env declaration := by
  cases sorted : Environment.Checker.sort fuel env [] declaration.type with
  | none => simp [checkExpanded, sorted] at accepted
  | some sort =>
      have both : Environment.Checker.check fuel env [] (Definitions.bodyMode sort) declaration.value declaration.type = true ∧
          (Definitions.bodyMode sort || EnvironmentQuantity.check quantityFuel env declaration.value) = true := by
        simpa only [checkExpanded, sorted, Bool.and_eq_true] using accepted
      refine ⟨sort, Environment.Checker.sort_sound sorted, Environment.Checker.check_sound both.1, ?_⟩
      intro code
      rcases Bool.or_eq_true_iff.mp both.2 with erased | checked
      · rw [code] at erased
        contradiction
      · exact EnvironmentQuantity.check_sound checked

/-- Transparent expansion is justified separately from unified typing and the
runtime resource gate. No caller chooses a declaration's body mode. -/
structure DeclarationChecked (env : Environment) (source expanded : GlobalDeclaration) : Prop where
  typeExpansion : GlobalEnvironment.Expansion env.globals source.type expanded.type
  valueExpansion : GlobalEnvironment.Expansion env.globals source.value expanded.value
  valid : ExpandedValid env expanded

def checkDeclaration (fuel quantityFuel : Nat) (env : Environment)
    (source : GlobalDeclaration) : Option GlobalDeclaration := do
  let type ← GlobalEnvironment.expand fuel env.globals source.type
  let value ← GlobalEnvironment.expand fuel env.globals source.value
  let expanded : GlobalDeclaration := ⟨type, value⟩
  if checkExpanded fuel quantityFuel env expanded then some expanded else none

theorem checkDeclaration_sound
    (accepted : checkDeclaration fuel quantityFuel env source = some expanded) :
    DeclarationChecked env source expanded := by
  unfold checkDeclaration at accepted
  cases typeExpanded : GlobalEnvironment.expand fuel env.globals source.type with
  | none => simp [typeExpanded] at accepted
  | some type =>
      simp only [typeExpanded, Bind.bind, Option.bind] at accepted
      cases valueExpanded : GlobalEnvironment.expand fuel env.globals source.value with
      | none => simp [valueExpanded] at accepted
      | some value =>
          simp only [valueExpanded] at accepted
          split at accepted
          · rename_i checked
            cases accepted
            exact ⟨GlobalEnvironment.expand_sound typeExpanded,
              GlobalEnvironment.expand_sound valueExpanded, checkExpanded_sound checked⟩
          · contradiction

/-- Independent mixed history: every step uses the same actual earlier table.
No legacy pure-prefix judgment or caller-supplied signature is a constructor. -/
inductive UnifiedProgramChecked : List GlobalDeclaration → List FamilyDeclaration → Environment → Prop where
  | empty : UnifiedProgramChecked [] [] Environment.empty
  | definition : UnifiedProgramChecked definitions familyDeclarations env → DeclarationChecked env source expanded →
      UnifiedProgramChecked (definitions ++ [source]) familyDeclarations ⟨env.globals.push expanded, env.families⟩
  | family : UnifiedProgramChecked definitions familyDeclarations env → Families.FamilyChecked env source entry →
      UnifiedProgramChecked definitions (familyDeclarations ++ [source]) ⟨env.globals, env.families.push entry⟩

def checkEvents (fuel quantityFuel : Nat) (env : Environment) : List FamilyEnvironment.Event → Option Environment
  | [] => some env
  | .definition source :: events => do
      let expanded ← checkDeclaration fuel quantityFuel env source
      checkEvents fuel quantityFuel ⟨env.globals.push expanded, env.families⟩ events
  | .family source :: events => do
      let entry ← Families.checkFamily fuel env source
      checkEvents fuel quantityFuel ⟨env.globals, env.families.push entry⟩ events

def checkProgram (fuel quantityFuel : Nat) (definitions : List GlobalDeclaration) (familyDeclarations : List FamilyDeclaration) :
    Option Environment := do
  let events ← FamilyEnvironment.schedule (definitions.length + familyDeclarations.length + 1) 0 definitions familyDeclarations
  checkEvents fuel quantityFuel Environment.empty events

theorem checkEvents_sound {familyDeclarations : List FamilyDeclaration} (history : UnifiedProgramChecked definitions familyDeclarations env)
    (accepted : checkEvents fuel quantityFuel env events = some result) :
    UnifiedProgramChecked (definitions ++ FamilyEnvironment.eventDefinitions events)
      (familyDeclarations ++ FamilyEnvironment.eventFamilies events) result := by
  induction events generalizing definitions familyDeclarations env with
  | nil => simp only [checkEvents, Option.some.injEq] at accepted; subst result; simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies, List.append_nil] using history
  | cons event events ih =>
      cases event with
      | definition source =>
          simp only [checkEvents] at accepted
          cases checked : checkDeclaration fuel quantityFuel env source with
          | none => simp [checked] at accepted
          | some expanded =>
              simp only [checked, Bind.bind, Option.bind] at accepted
              simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies,
                List.append_assoc, List.singleton_append] using
                ih (.definition history (checkDeclaration_sound checked)) accepted
      | family source =>
          simp only [checkEvents] at accepted
          cases checked : Families.checkFamily fuel env source with
          | none => simp [checked] at accepted
          | some entry =>
              simp only [checked, Bind.bind, Option.bind] at accepted
              simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies,
                List.append_assoc, List.singleton_append] using
                ih (.family history (Families.checkFamily_sound checked)) accepted

theorem checkProgram_sound {familyDeclarations : List FamilyDeclaration} (accepted : checkProgram fuel quantityFuel definitions familyDeclarations = some result) :
    UnifiedProgramChecked definitions familyDeclarations result := by
  unfold checkProgram at accepted
  cases scheduled : FamilyEnvironment.schedule (definitions.length + familyDeclarations.length + 1) 0 definitions familyDeclarations with
  | none => simp [scheduled] at accepted
  | some events =>
      simp only [scheduled, Bind.bind, Option.bind] at accepted
      obtain ⟨definitionOrder, familyOrder⟩ := FamilyEnvironment.schedule_sound scheduled
      simpa only [List.nil_append, definitionOrder, familyOrder] using
        checkEvents_sound UnifiedProgramChecked.empty accepted

theorem DeclarationChecked.closed (checked : DeclarationChecked env source expanded) :
    expanded.type.Scoped 0 ∧ expanded.value.Scoped 0 ∧ expanded.type.WellFormed ∧ expanded.value.WellFormed := by
  obtain ⟨_, typeFormed, valueTyped, _⟩ := checked.valid
  exact ⟨typeFormed.term_scoped, valueTyped.term_scoped, typeFormed.term_wellFormed, valueTyped.term_wellFormed⟩

private theorem lookup_push_cases {array : Array α} {added selected : α} {index : Nat}
    (found : (array.push added)[index]? = some selected) : array[index]? = some selected ∨ selected = added := by
  by_cases earlier : index < array.size
  · apply Or.inl
    rw [Array.getElem?_eq_getElem earlier]
    simpa only [Array.getElem?_push_lt earlier] using found
  · obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
    have last : index = array.size := by simp only [Array.size_push] at inside; omega
    subst index
    rw [Array.getElem?_push_size] at found
    exact Or.inr (Option.some.inj found).symm

theorem EnvWellFormed.empty : EnvWellFormed Environment.empty := by
  constructor
  · intro index declaration found
    obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
    exact False.elim (Nat.not_lt_zero index inside)
  · intro index declaration found
    obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
    exact False.elim (Nat.not_lt_zero index inside)
  · intro index entry found
    obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
    exact False.elim (Nat.not_lt_zero index inside)

theorem EnvWellFormed.pushGlobal (prior : EnvWellFormed env)
    (closed : declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
      declaration.type.WellFormed ∧ declaration.value.WellFormed)
    (transparent : GlobalEnvironment.GlobalFree declaration.type ∧ GlobalEnvironment.GlobalFree declaration.value) :
    EnvWellFormed ⟨env.globals.push declaration, env.families⟩ := by
  constructor
  · intro index selected found
    rcases lookup_push_cases found with old | rfl
    · exact prior.globals index selected old
    · exact closed
  · intro index selected found
    rcases lookup_push_cases found with old | rfl
    · exact prior.transparent index selected old
    · exact transparent
  · exact prior.signatures

theorem EnvWellFormed.pushFamily (prior : EnvWellFormed env)
    (scopes : ∀ signature ∈ entry.signatures, SignatureScoped signature) :
    EnvWellFormed ⟨env.globals, env.families.push entry⟩ := by
  constructor
  · exact prior.globals
  · exact prior.transparent
  · intro index selected found signature member
    rcases lookup_push_cases found with old | rfl
    · exact prior.signatures index selected old signature member
    · exact scopes signature member

theorem UnifiedProgramChecked.wellFormed (history : UnifiedProgramChecked definitions familyDeclarations env) :
    EnvWellFormed env := by
  induction history with
  | empty => exact EnvWellFormed.empty
  | definition history checked ih =>
      apply ih.pushGlobal checked.closed
      refine ⟨checked.typeExpansion.globalFree ?_, checked.valueExpansion.globalFree ?_⟩
      all_goals
        intro entry member
        obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
        exact (ih.transparent index entry (by simpa using selected)).2
  | family history checked ih => exact ih.pushFamily checked.signatures_scoped

theorem checkProgram_wellFormed
    (accepted : checkProgram fuel quantityFuel definitions familyDeclarations = some env) : EnvWellFormed env :=
  (checkProgram_sound accepted).wellFormed

theorem UnifiedProgramChecked.globalLength (history : UnifiedProgramChecked definitions familyDeclarations env) :
    env.globals.size = definitions.length := by
  induction history <;> simp_all [Environment.empty]

theorem UnifiedProgramChecked.familyLength (history : UnifiedProgramChecked definitions familyDeclarations env) :
    env.families.size = familyDeclarations.length := by
  induction history <;> simp_all [Environment.empty]

/-- Lookup provenance retains the exact validated earlier mixed prefix. -/
theorem UnifiedProgramChecked.global_prefix
    (history : UnifiedProgramChecked definitions familyDeclarations env)
    {index : Nat} {entry : GlobalDeclaration} (found : env.globals[index]? = some entry) :
    ∃ prefixDefinitions prefixFamilies earlierEnv source,
      UnifiedProgramChecked prefixDefinitions prefixFamilies earlierEnv ∧ earlierEnv.globals.size = index ∧
      DeclarationChecked earlierEnv source entry ∧ Environment.Extends earlierEnv env := by
  induction history with
  | empty =>
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      exact False.elim (Nat.not_lt_zero index inside)
  | @definition definitions families env source added history checked ih =>
      have bounded : index < env.globals.size + 1 := by
        obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
        simpa only [Array.size_push] using inside
      by_cases earlier : index < env.globals.size
      · have old : env.globals[index]? = some entry := by
          rw [Array.getElem?_eq_getElem earlier]
          simpa only [Array.getElem?_push_lt earlier] using found
        obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih old
        exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
          extension.trans (Environment.Extends.pushGlobal env added)⟩
      · have same : index = env.globals.size := by omega
        subst index
        rw [Array.getElem?_push_size] at found
        cases found
        exact ⟨definitions, families, env, source, history, rfl, checked,
          Environment.Extends.pushGlobal env entry⟩
  | @family definitions families env source added history checked ih =>
      obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih found
      exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
        extension.trans (Environment.Extends.pushFamily env added)⟩

theorem UnifiedProgramChecked.family_prefix
    (history : UnifiedProgramChecked definitions familyDeclarations env)
    {index : Nat} {entry : CheckedFamily} (found : env.families[index]? = some entry) :
    ∃ prefixDefinitions prefixFamilies earlierEnv source,
      UnifiedProgramChecked prefixDefinitions prefixFamilies earlierEnv ∧ earlierEnv.families.size = index ∧
      Families.FamilyChecked earlierEnv source entry ∧ Environment.Extends earlierEnv env := by
  induction history with
  | empty =>
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      exact False.elim (Nat.not_lt_zero index inside)
  | @definition definitions families env source added history checked ih =>
      obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih found
      exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
        extension.trans (Environment.Extends.pushGlobal env added)⟩
  | @family definitions families env source added history checked ih =>
      have bounded : index < env.families.size + 1 := by
        obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
        simpa only [Array.size_push] using inside
      by_cases earlier : index < env.families.size
      · have old : env.families[index]? = some entry := by
          rw [Array.getElem?_eq_getElem earlier]
          simpa only [Array.getElem?_push_lt earlier] using found
        obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih old
        exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
          extension.trans (Environment.Extends.pushFamily env added)⟩
      · have same : index = env.families.size := by omega
        subst index
        rw [Array.getElem?_push_size] at found
        cases found
        exact ⟨definitions, families, env, source, history, rfl, checked,
          Environment.Extends.pushFamily env entry⟩

theorem UnifiedProgramChecked.global_typing
    (history : UnifiedProgramChecked definitions familyDeclarations env)
    {index : Nat} {entry : GlobalDeclaration} (found : env.globals[index]? = some entry) :
    ∃ sort : SortTag, Environment.HasType env [] true entry.type sort.term ∧
      Environment.HasType env [] (Definitions.bodyMode sort) entry.value entry.type := by
  obtain ⟨_, _, _, _, _, _, checked, extension⟩ := history.global_prefix found
  obtain ⟨sort, typeFormed, valueTyped, _⟩ := checked.valid
  exact ⟨sort, typeFormed.extend extension, valueTyped.extend extension⟩

theorem ExpandedValid.extend (extension : Environment.Extends before after)
    (valid : ExpandedValid before declaration) : ExpandedValid after declaration := by
  obtain ⟨sort, typeFormed, valueTyped, quantities⟩ := valid
  exact ⟨sort, typeFormed.extend extension, valueTyped.extend extension,
    fun code => (quantities code).extend extension⟩

theorem UnifiedProgramChecked.global_valid
    (history : UnifiedProgramChecked definitions familyDeclarations env)
    {index : Nat} {entry : GlobalDeclaration} (found : env.globals[index]? = some entry) : ExpandedValid env entry := by
  obtain ⟨_, _, _, _, _, _, checked, extension⟩ := history.global_prefix found
  exact checked.valid.extend extension

end Jihoo.NativeKernel.UnifiedProgram
