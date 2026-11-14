import Jihoo.NativeFinitePi
set_option maxUniverseOffset 40
set_option autoImplicit false

/-! A concrete contextual model with finite semantic universes. Its dependent
substitutions and Pi/lambda/application are functions with proved equations.
The actual-HasType fundamental lemma is a subsequent obligation. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Contextual
open Finite

abbrev Context := Type 34
abbrev Ty (Γ : Context) (s : LevelSort) := Γ → Universe s
abbrev Tm {Γ : Context} {s : LevelSort} (A : Ty Γ s) := (γ : Γ) → Carrier (A γ)
abbrev Sub (Γ Δ : Context) := Γ → Δ

def empty : Context := ULift.{34} Unit
def extend (Γ : Context) {s : LevelSort} (A : Ty Γ s) : Context := (γ : Γ) × Carrier (A γ)
def identity {Γ : Context} : Sub Γ Γ := id
def compose {Γ Δ Θ : Context} (σ : Sub Γ Δ) (τ : Sub Δ Θ) : Sub Γ Θ := τ ∘ σ

def typeSubst {Γ Δ : Context} {s : LevelSort} (A : Ty Δ s) (σ : Sub Γ Δ) : Ty Γ s := A ∘ σ

def termSubst {Γ Δ : Context} {s : LevelSort} {A : Ty Δ s} (term : Tm A) (σ : Sub Γ Δ) :
    Tm (typeSubst A σ) := fun γ => term (σ γ)

def weaken {Γ : Context} {s : LevelSort} {A : Ty Γ s} : Sub (extend Γ A) Γ := Sigma.fst

def newest {Γ : Context} {s : LevelSort} {A : Ty Γ s} : Tm (typeSubst A (weaken (A := A))) := Sigma.snd

def pair {Γ Δ : Context} {s : LevelSort} {A : Ty Δ s}
    (σ : Sub Γ Δ) (term : Tm (typeSubst A σ)) : Sub Γ (extend Δ A) := fun γ => ⟨σ γ,term γ⟩

def lift {Γ Δ : Context} {s : LevelSort} {A : Ty Δ s} (σ : Sub Γ Δ) :
    Sub (extend Γ (typeSubst A σ)) (extend Δ A) := fun γ => ⟨σ γ.1,γ.2⟩

theorem type_identity {Γ : Context} {s : LevelSort} (A : Ty Γ s) : typeSubst A identity = A := rfl

theorem term_identity {Γ : Context} {s : LevelSort} {A : Ty Γ s} (term : Tm A) : termSubst term identity = term := rfl

theorem type_compose {Γ Δ Θ : Context} {s : LevelSort} (A : Ty Θ s) (σ : Sub Γ Δ) (τ : Sub Δ Θ) :
    typeSubst (typeSubst A τ) σ = typeSubst A (compose σ τ) := rfl

theorem term_compose {Γ Δ Θ : Context} {s : LevelSort} {A : Ty Θ s} (term : Tm A) (σ : Sub Γ Δ) (τ : Sub Δ Θ) :
    termSubst (termSubst term τ) σ = termSubst term (compose σ τ) := rfl

theorem newest_pair {Γ Δ : Context} {s : LevelSort} {A : Ty Δ s}
    (σ : Sub Γ Δ) (term : Tm (typeSubst A σ)) : termSubst (newest (A := A)) (pair σ term) = term := rfl

theorem weaken_pair {Γ Δ : Context} {s : LevelSort} {A : Ty Δ s}
    (σ : Sub Γ Δ) (term : Tm (typeSubst A σ)) : compose (pair σ term) weaken = σ := rfl

theorem pair_eta {Γ Δ : Context} {s : LevelSort} {A : Ty Δ s} (σ : Sub Γ (extend Δ A)) :
    pair (compose σ weaken) (termSubst (newest (A := A)) σ) = σ := rfl

def pi {Γ : Context} {s r : LevelSort} (A : Ty Γ s) (B : Ty (extend Γ A) r) : Ty Γ (s.pi r) :=
  fun γ => Finite.pi (A γ) r (fun argument => B ⟨γ,argument⟩)

def lam {Γ : Context} {s r : LevelSort} {A : Ty Γ s} {B : Ty (extend Γ A) r} (body : Tm B) : Tm (pi A B) :=
  fun γ => (Finite.piMeaning (A γ) r (fun argument => B ⟨γ,argument⟩)).lam (fun argument => body ⟨γ,argument⟩)

def app {Γ : Context} {s r : LevelSort} {A : Ty Γ s} {B : Ty (extend Γ A) r}
    (function : Tm (pi A B)) (argument : Tm A) : Tm (typeSubst B (pair identity argument)) :=
  fun γ => (Finite.piMeaning (A γ) r (fun argument => B ⟨γ,argument⟩)).app (function γ) (argument γ)

theorem beta {Γ : Context} {s r : LevelSort} {A : Ty Γ s} {B : Ty (extend Γ A) r}
    (body : Tm B) (argument : Tm A) :
    app (lam body) argument = termSubst body (pair identity argument) := by
  funext γ
  exact (Finite.piMeaning _ _ _).beta _ _

theorem eta {Γ : Context} {s r : LevelSort} {A : Ty Γ s} {B : Ty (extend Γ A) r}
    (function : Tm (pi A B)) :
    lam (A := A) (B := B)
      (app (A := typeSubst A (weaken (A := A)))
        (B := typeSubst B (lift (weaken (A := A))))
        (termSubst function (weaken (A := A))) (newest (A := A))) = function := by
  funext γ
  change (Finite.piMeaning (A γ) r (fun argument => B ⟨γ,argument⟩)).lam
    ((Finite.piMeaning (A γ) r (fun argument => B ⟨γ,argument⟩)).app (function γ)) = function γ
  exact (Finite.piMeaning _ _ _).eta _

theorem pi_substitution {Γ Δ : Context} {s r : LevelSort} (A : Ty Δ s) (B : Ty (extend Δ A) r) (σ : Sub Γ Δ) :
    typeSubst (pi A B) σ = pi (typeSubst A σ) (typeSubst B (lift σ)) := rfl

theorem lam_substitution {Γ Δ : Context} {s r : LevelSort} {A : Ty Δ s} {B : Ty (extend Δ A) r}
    (body : Tm B) (σ : Sub Γ Δ) :
    termSubst (lam body) σ = lam (A := typeSubst A σ) (B := typeSubst B (lift σ)) (termSubst body (lift σ)) := rfl

theorem app_substitution {Γ Δ : Context} {s r : LevelSort} {A : Ty Δ s} {B : Ty (extend Δ A) r}
    (function : Tm (pi A B)) (argument : Tm A) (σ : Sub Γ Δ) :
    termSubst (app function argument) σ =
      app (A := typeSubst A σ) (B := typeSubst B (lift σ)) (termSubst function σ) (termSubst argument σ) := rfl

def natural {Γ : Context} : Ty Γ (.type ⟨0,by decide⟩) := fun _ => Finite.natural

def numeral {Γ : Context} (value : Nat) : Tm (natural (Γ := Γ)) := fun _ => ⟨value⟩

def add {Γ : Context} (first second : Tm (natural (Γ := Γ))) : Tm (natural (Γ := Γ)) :=
  fun γ => ⟨(first γ).down + (second γ).down⟩

def subtract {Γ : Context} (first second : Tm (natural (Γ := Γ))) : Tm (natural (Γ := Γ)) :=
  fun γ => ⟨(first γ).down - (second γ).down⟩

def equal {Γ : Context} (first second : Tm (natural (Γ := Γ))) : Ty Γ .proposition :=
  fun γ => Finite.equal (first γ).down (second γ).down

def less {Γ : Context} (first second : Tm (natural (Γ := Γ))) : Ty Γ .proposition :=
  fun γ => Finite.less (first γ).down (second γ).down

def refl {Γ : Context} (value : Tm (natural (Γ := Γ))) : Tm (equal value value) := fun _ => ⟨⟨rfl⟩⟩

def zeroLe {Γ : Context} (value : Tm (natural (Γ := Γ))) : Tm (less (numeral 0) (add value (numeral 1))) :=
  fun _ => ⟨⟨Nat.zero_lt_succ _⟩⟩

theorem add_comm {Γ : Context} (first second : Tm (natural (Γ := Γ))) : add first second = add second first := by
  funext γ
  exact congrArg ULift.up (Nat.add_comm _ _)

theorem add_assoc {Γ : Context} (first second third : Tm (natural (Γ := Γ))) :
    add (add first second) third = add first (add second third) := by
  funext γ
  exact congrArg ULift.up (Nat.add_assoc _ _ _)

theorem add_zero {Γ : Context} (term : Tm (natural (Γ := Γ))) : add term (numeral 0) = term := by
  funext γ
  exact congrArg ULift.up (Nat.add_zero _)

theorem equal_false_empty (m n : Nat) (different : m ≠ n) :
    ¬ Nonempty (Tm (equal (numeral (Γ := empty) m) (numeral n))) := by
  intro realized
  obtain ⟨term⟩ := realized
  exact different (term ⟨()⟩).down.down

theorem less_false_empty (m n : Nat) (unordered : ¬ m < n) :
    ¬ Nonempty (Tm (less (numeral (Γ := empty) m) (numeral n))) := by
  intro realized
  obtain ⟨term⟩ := realized
  exact unordered (term ⟨()⟩).down.down

end Jihoo.NativeKernel.Environment.Semantics.Contextual
