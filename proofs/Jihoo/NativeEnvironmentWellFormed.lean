import Jihoo.NativeEnvironmentScope

namespace Jihoo.NativeKernel.UnifiedProgram
open Environment

structure SignatureScoped (signature : Signature) : Prop where
  domains : ∀ (j : Nat) field, signature.fields[j]? = some field → field.domain.Scoped j
  recursive : ∀ (j : Nat) field indices, signature.fields[j]? = some field →
    field.recursive = some indices → ∀ index ∈ indices, index.Scoped j
  result : ∀ index ∈ signature.result, index.Scoped signature.fields.length

structure EnvWellFormed (env : Environment) : Prop where
  globals : ∀ (g : Nat) declaration, env.globals[g]? = some declaration →
    declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
    declaration.type.WellFormed ∧ declaration.value.WellFormed
  signatures : ∀ (f : Nat) entry, env.families[f]? = some entry →
    ∀ signature ∈ entry.signatures, SignatureScoped signature

private theorem pi_scoped {depth : Nat} {domain body : Term}
    (domainScope : domain.Scoped depth) (bodyScope : body.Scoped (depth + 1)) :
    (Term.pi erased domain body).Scoped depth := by
  apply Term.Scoped.node
  intro index term found
  cases index with
  | zero => simpa only [Op.binders, Nat.add_zero] using (Option.some.inj found ▸ domainScope)
  | succ index =>
      cases index with
      | zero => simpa only [Op.binders] using (Option.some.inj found ▸ bodyScope)
      | succ _ => simp at found

private theorem telescope_scoped (fields : List Field) (depth : Nat) (result : Term)
    (domains : ∀ (index : Nat) field, fields[index]? = some field → field.domain.Scoped (depth + index))
    (resultScope : result.Scoped (depth + fields.length)) :
    (fields.foldr (fun field rest => Term.pi field.erased field.domain rest) result).Scoped depth := by
  induction fields generalizing depth with
  | nil => simpa only [List.foldr_nil, List.length_nil, Nat.add_zero] using resultScope
  | cons field fields ih =>
      apply pi_scoped
      · simpa only [Nat.add_zero] using domains 0 field rfl
      · apply ih (depth + 1)
        · intro index selected found
          have declared := domains (index + 1) selected found
          simpa only [Nat.add_assoc, Nat.add_comm 1 index] using declared
        · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 fields.length] using resultScope

theorem SignatureScoped.signatureTerm_scoped (checked : SignatureScoped signature) (family : Nat) :
    (Environment.signatureTerm family signature).Scoped 0 := by
  apply telescope_scoped signature.fields 0
  · intro index field found
    simpa only [Nat.zero_add] using checked.domains index field found
  · apply Term.Scoped.node
    intro index term found
    change term.Scoped (0 + signature.fields.length)
    simpa only [Nat.zero_add] using checked.result term (List.mem_of_getElem? found)

end Jihoo.NativeKernel.UnifiedProgram
