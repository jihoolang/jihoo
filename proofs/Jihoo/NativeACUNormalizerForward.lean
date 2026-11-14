import Jihoo.NativeACUNormalizer

/-! Independent exact forward reachability of executable full-Term additive
canonicalization. The proof does not infer forward reachability from Conv. -/
namespace Jihoo.NativeKernel.ACU.Canonical

open AffineSum (wordLimit naturalSum)

private theorem fallback_flatten (t : Term)
    (noAdd : ∀ a b, t ≠ .node .uadd [a,b])
    (noNatural : ∀ n, t ≠ .node (.natural n) []) : arithmeticFlatten t = [t] := by
  fun_cases arithmeticFlatten t
  all_goals first
    | exact False.elim (noAdd _ _ rfl)
    | exact False.elim (noNatural _ rfl)
    | rfl

/-- Compact collection has exactly the same additive atom multiset as the
proof-model flattening, without executing the proof-model replica lists. -/
theorem collect_flatten (t : Term) : (arithmeticFlatten t).Perm
    ((collect t).atoms ++ List.replicate (collect t).constant (.node (.natural 1) [])) := by
  fun_induction collect t with
  | case1 a b ia ib =>
      simp only [arithmeticFlatten]
      apply (ia.append ib).trans
      simpa only [Pieces.append,List.replicate_append_replicate,List.append_assoc] using
        (((List.perm_append_comm (l₁ := List.replicate (collect a).constant (.node (.natural 1) []))
          (l₂ := (collect b).atoms)).append_right
          (List.replicate (collect b).constant (.node (.natural 1) []))).append_left (collect a).atoms)
  | case2 n bound => simp only [arithmeticFlatten,bound,↓reduceIte,List.nil_append]; exact .refl _
  | case3 n bound => simp only [arithmeticFlatten,bound,↓reduceIte,List.replicate_zero,List.append_nil]; exact .refl _
  | case4 t h₁ h₂ =>
      rw [fallback_flatten t h₁ h₂]
      exact .refl _

/-- Every collected opaque atom has a singleton additive flattening. -/
theorem collect_atoms (h : x ∈ (collect t).atoms) : arithmeticFlatten x = [x] := by
  fun_induction collect t with
  | case1 a b ia ib =>
      simp only [Pieces.append,List.mem_append] at h
      rcases h with ha | hb
      · exact ia ha
      · exact ib hb
  | case2 n bound => simp at h
  | case3 n bound =>
      simp only [List.mem_singleton] at h
      subst x
      simp only [arithmeticFlatten,bound,↓reduceIte]
  | case4 t h₁ h₂ =>
      simp only [List.mem_singleton] at h
      subst x
      exact fallback_flatten t h₁ h₂

private theorem split_compact (xs ys : List Term) (hx : xs ≠ []) (hy : ys ≠ []) :
    ArithmeticRed (compact (xs ++ ys)) (.node .uadd [compact xs,compact ys]) := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      induction xs generalizing x with
      | nil => cases ys with
        | nil => contradiction
        | cons y ys => exact .refl _
      | cons z xs ih =>
          have inner := ih z (by simp)
          exact (ArithmeticRed.addCong (.refl x) inner).trans (.assocLeft x (compact (z::xs)) (compact ys))

private theorem reversible_add (ha : ArithmeticRed (compact (arithmeticFlatten a)) a)
    (hb : ArithmeticRed (compact (arithmeticFlatten b)) b)
    (nonzeroA : arithmeticFlatten a ≠ []) (nonzeroB : arithmeticFlatten b ≠ []) :
    ArithmeticRed (compact (arithmeticFlatten (.node .uadd [a,b]))) (.node .uadd [a,b]) := by
  simp only [arithmeticFlatten]
  exact (split_compact _ _ nonzeroA nonzeroB).trans (ArithmeticRed.addCong ha hb)

theorem constantTree_flatten (n : Nat) :
    arithmeticFlatten (constantTree n) = List.replicate n (.node (.natural 1) []) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold constantTree
      rw [naturalSum]
      split
      · rename_i bound
        simp only [AffineSum.Expr.toTerm,arithmeticFlatten,bound,↓reduceIte]
      · rename_i large
        have low : 2 ≤ wordLimit := by decide
        change arithmeticFlatten (.node .uadd [constantTree (n/2),constantTree (n-n/2)]) = _
        rw [arithmeticFlatten,ih (n/2) (by omega),ih (n-n/2) (by omega),List.replicate_append_replicate]
        congr 1
        omega

private theorem constantTree_nonempty (positive : 0 < n) : arithmeticFlatten (constantTree n) ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  rw [constantTree_flatten,List.length_replicate,List.length_nil] at length
  omega

theorem constantTree_forward (n : Nat) :
    ArithmeticRed (compact (arithmeticFlatten (constantTree n))) (constantTree n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold constantTree
      rw [naturalSum]
      split
      · rename_i bound
        simpa only [AffineSum.Expr.toTerm,arithmeticFlatten,bound,↓reduceIte] using ArithmeticRed.ones_fold n bound
      · rename_i large
        have low : 2 ≤ wordLimit := by decide
        change ArithmeticRed (compact (arithmeticFlatten
          (.node .uadd [constantTree (n/2),constantTree (n-n/2)]))) _
        exact reversible_add (ih _ (by omega)) (ih _ (by omega))
          (constantTree_nonempty (by omega)) (constantTree_nonempty (by omega))

private theorem atomFold (rest : List Term) (acc : Term)
    (reversible : ArithmeticRed (compact (arithmeticFlatten acc)) acc)
    (nonzero : arithmeticFlatten acc ≠ [])
    (atoms : ∀ x ∈ rest, arithmeticFlatten x = [x]) :
    ArithmeticRed (compact (arithmeticFlatten (rest.foldl (fun a b => .node .uadd [a,b]) acc)))
      (rest.foldl (fun a b => .node .uadd [a,b]) acc) ∧
    arithmeticFlatten (rest.foldl (fun a b => .node .uadd [a,b]) acc) = arithmeticFlatten acc ++ rest := by
  induction rest generalizing acc with
  | nil => exact ⟨reversible,(List.append_nil _).symm⟩
  | cons x xs ih =>
      have atom := atoms x (by simp)
      have rx : ArithmeticRed (compact (arithmeticFlatten x)) x := by rw [atom]; exact .refl _
      have next := reversible_add reversible rx nonzero (by rw [atom]; simp)
      have nonzeroNext : arithmeticFlatten (.node .uadd [acc,x]) ≠ [] := by
        simp only [arithmeticFlatten,atom]
        intro empty
        have length := congrArg List.length empty
        simp only [List.length_append,List.length_singleton,List.length_nil] at length
        omega
      obtain ⟨hr,eq⟩ := ih (.node .uadd [acc,x]) next nonzeroNext (fun y hy => atoms y (by simp [hy]))
      exact ⟨hr,by simpa only [List.foldl_cons,arithmeticFlatten,atom,List.append_assoc,List.singleton_append] using eq⟩

private theorem atomTree_forward (atoms : ∀ x ∈ first::rest, arithmeticFlatten x = [x]) :
    ArithmeticRed (compact (arithmeticFlatten (atomTree first rest))) (atomTree first rest) ∧
      arithmeticFlatten (atomTree first rest) = first::rest := by
  have head := atoms first (by simp)
  have init : ArithmeticRed (compact (arithmeticFlatten first)) first := by rw [head]; exact .refl _
  have h := atomFold rest first init (by rw [head]; simp) (fun x hx => atoms x (by simp [hx]))
  simpa only [atomTree,head,List.singleton_append] using h

/-- Emission contains no removable additive zero wrapper. Its explicit
arithmetic flattening can therefore be folded forward back to the exact tree. -/
theorem emit_forward (p : Pieces) (atoms : ∀ x ∈ p.atoms, arithmeticFlatten x = [x]) :
    ArithmeticRed (compact (arithmeticFlatten p.emit)) p.emit ∧
      arithmeticFlatten p.emit = sortAtoms p.atoms ++ List.replicate p.constant (.node (.natural 1) []) := by
  cases sorted : sortAtoms p.atoms with
  | nil =>
      simp only [Pieces.emit,sorted,List.nil_append]
      exact ⟨constantTree_forward _,constantTree_flatten _⟩
  | cons x xs =>
      have sortedAtoms : ∀ t ∈ x::xs, arithmeticFlatten t = [t] := by
        intro t ht
        apply atoms t
        apply (sortAtoms_perm p.atoms).mem_iff.mp
        rw [sorted]
        exact ht
      obtain ⟨forward,flat⟩ := atomTree_forward sortedAtoms
      by_cases zero : p.constant = 0
      · simp only [Pieces.emit,sorted,zero,↓reduceIte,List.replicate_zero,List.append_nil]
        exact ⟨forward,flat⟩
      · simp only [Pieces.emit,sorted,zero,↓reduceIte]
        exact ⟨reversible_add forward (constantTree_forward _)
          (by rw [flat]; simp) (constantTree_nonempty (by omega)),
          by rw [arithmeticFlatten,flat,constantTree_flatten]⟩

/-- Exact independent forward derivation to the executable canonical output.
It does not appeal to sum_sound, full Church–Rosser, or a semantic oracle. -/
theorem sum_forward (t : Term) : ArithmeticRed t (sum t) := by
  obtain ⟨reverse,flat⟩ := emit_forward (collect t) (fun x hx => collect_atoms hx)
  have sorted : (arithmeticFlatten t).Perm (arithmeticFlatten (sum t)) := by
    rw [sum,flat]
    exact (collect_flatten t).trans (((sortAtoms_perm (collect t).atoms).symm).append_right _)
  exact (ArithmeticRed.flatten t).trans ((ArithmeticRed.compact_perm sorted).trans reverse)

end Jihoo.NativeKernel.ACU.Canonical
