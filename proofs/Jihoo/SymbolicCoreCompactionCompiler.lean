import Jihoo.SizedErasureCompiler

/-! Completeness of the existing bounded compactor for structural erasure
witnesses. Bounds are on traversal depth, not graph size; cyclic graphs without
finite derivations do not acquire a termination claim. -/
namespace Jihoo.SizedErasure
open ScopedLend

local macro "compact_match " witness:term : tactic => `(tactic| (
  split
  all_goals
    try
      rename_i branchEq
      have equalNodes := ($witness).symm.trans branchEq
      first | contradiction | injection equalNodes
      try subst_vars
  all_goals try simp_all
  all_goals try contradiction
))

local macro "compact_pair " firstWitness:ident secondWitness:ident : tactic => `(tactic| (
  split
  all_goals
    try
      rename_i firstEq secondEq
      have firstNodes := ($firstWitness).symm.trans firstEq
      first | contradiction | injection firstNodes
      try subst_vars
      have secondNodes := ($secondWitness).symm.trans secondEq
      first | contradiction | injection secondNodes
      try subst_vars
  all_goals try simp_all
  all_goals try grind
))

theorem NatErases.compile_complete (erased : NatErases g mask root term) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      compileNat g fuel mask root = some ⟨term, erased⟩ := by
  obtain ⟨expr, represented, compacted⟩ := erased
  induction represented generalizing mask term with
  | literal shape limit =>
      cases compacted
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp only [compileNat]; compact_match shape
  | var shape =>
      cases compacted with
      | var kept =>
          refine ⟨1, ?_⟩
          intro fuel enough
          cases fuel with
          | zero => omega
          | succ fuel => simp only [compileNat]; compact_match shape
  | letE shape lam ty a b ia ib =>
      cases compacted with
      | letE ca cb =>
          obtain ⟨na, ha⟩ := ia ca
          obtain ⟨nb, hb⟩ := ib cb
          refine ⟨max na nb + 1, ?_⟩
          intro fuel enough
          cases fuel with
          | zero => omega
          | succ fuel =>
              have aa := ha fuel (by omega)
              have bb := hb fuel (by omega)
              simp only [compileNat]
              compact_match shape
              compact_match lam
              compact_match ty

theorem ScalarErases.compile_complete (erased : ScalarErases g mask root term) :
    compileScalar g mask root = some ⟨term, erased⟩ := by
  cases erased with
  | literal shape => simp only [compileScalar]; compact_match shape
  | var shape kept => simp only [compileScalar]; compact_match shape

theorem Erases.compile_complete (erased : Erases g mask root term) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      compile g fuel mask root = some ⟨term, erased⟩ := by
  induction erased with
  | scalar shape =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp only [compile]; compact_match shape
  | natural shape =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp only [compile]; compact_match shape
  | var shape kept =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp only [compile]; compact_match shape
  | app shape lam a b ia ib =>
      obtain ⟨na, ha⟩ := ia
      obtain ⟨nb, hb⟩ := ib
      refine ⟨max na nb + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have aa := ha fuel (by omega)
          have bb := hb fuel (by omega)
          simp only [compile]
          compact_match shape
          compact_match lam
  | allocate shape n v =>
      obtain ⟨nn, hn⟩ := n.compile_complete
      refine ⟨nn + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have en := hn fuel (by omega)
          have ev := v.compile_complete
          simp only [compile]; compact_match shape
  | free shape variableShape kept body ih =>
      obtain ⟨nb, hb⟩ := ih
      refine ⟨nb + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have eb := hb fuel (by omega)
          simp only [compile]
          compact_match shape
          compact_match variableShape
  | branch shape l r y n iy ino =>
      obtain ⟨nl, hl⟩ := l.compile_complete
      obtain ⟨nr, hr⟩ := r.compile_complete
      obtain ⟨ny, hy⟩ := iy
      obtain ⟨nn, hn⟩ := ino
      refine ⟨max (max nl nr) (max ny nn) + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have el := hl fuel (by omega)
          have er := hr fuel (by omega)
          have ey := hy fuel (by omega)
          have en := hn fuel (by omega)
          simp only [compile]; compact_match shape
          all_goals grind
  | lend shape variableShape kept i body ih =>
      obtain ⟨ni, hi⟩ := i.compile_complete
      obtain ⟨nb, hb⟩ := ih
      refine ⟨max ni nb + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have ei := hi fuel (by omega)
          have eb := hb fuel (by omega)
          cases shape with
          | intro root reader read operand cont result inner =>
              simp only [compile]
              compact_match root
              compact_match variableShape
              compact_pair reader cont
  | ownedLend shape variableShape kept n i body ih =>
      obtain ⟨nn, hn⟩ := n.compile_complete
      obtain ⟨ni, hi⟩ := i.compile_complete
      obtain ⟨nb, hb⟩ := ih
      refine ⟨max nn (max ni nb) + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have en := hn fuel (by omega)
          have ei := hi fuel (by omega)
          have eb := hb fuel (by omega)
          cases shape with
          | intro root reader alloc read operand cont inner =>
              simp only [compile]
              compact_match root
              compact_match variableShape
              compact_pair reader cont

theorem Erases.compileTarget_complete (erased : Erases g mask root term) :
    ∃ bound, ∀ fuel, bound ≤ fuel → compileTarget g fuel mask root = some term := by
  obtain ⟨bound, complete⟩ := erased.compile_complete
  exact ⟨bound, fun fuel enough => by simp [compileTarget, complete fuel enough]⟩

end Jihoo.SizedErasure
