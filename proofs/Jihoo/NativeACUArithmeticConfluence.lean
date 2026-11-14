import Jihoo.NativeACUArithmetic
import Jihoo.NativeACUConfluence

/-! Genuine forward Church–Rosser for ACU plus bounded literal arithmetic on
complete native syntax. Proof-oriented splitting expands only valid literals;
invalid payloads remain opaque. Beta and observing roots are separate. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

/-- Contextual reflexive-transitive forward ACU reduction. Associativity and
commutativity are reversible; zero is only eliminated, never inserted. -/
inductive ArithmeticRed : Term → Term → Prop where
  | refl (t : Term) : ArithmeticRed t t
  | trans : ArithmeticRed a b → ArithmeticRed b c → ArithmeticRed a c
  | node (op : Op) : ListRel ArithmeticRed xs ys → ArithmeticRed (.node op xs) (.node op ys)
  | assocRight (a b c : Term) :
      ArithmeticRed (.node .uadd [.node .uadd [a,b],c]) (.node .uadd [a,.node .uadd [b,c]])
  | assocLeft (a b c : Term) :
      ArithmeticRed (.node .uadd [a,.node .uadd [b,c]]) (.node .uadd [.node .uadd [a,b],c])
  | comm (a b : Term) : ArithmeticRed (.node .uadd [a,b]) (.node .uadd [b,a])
  | zeroRight (a : Term) : ArithmeticRed (.node .uadd [a,.node (.natural 0) []]) a
  | zeroLeft (a : Term) : ArithmeticRed (.node .uadd [.node (.natural 0) [],a]) a
  | literalSplit (n : Nat) : n < AffineSum.wordLimit →
      ArithmeticRed (.node (.natural n) []) (compact (List.replicate n (.node (.natural 1) [])))
  | literalAdd (m n : Nat) : m+n < AffineSum.wordLimit →
      ArithmeticRed (.node .uadd [.node (.natural m) [],.node (.natural n) []])
        (.node (.natural (m+n)) [])

private theorem sumTerms_compact (xs : List Term) : Arithmetic (sumTerms xs) (compact xs) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
      cases xs with
      | nil => exact .zero x
      | cons y xs => exact .addCong (.refl x) ih

theorem ArithmeticRed.toArithmetic (h : ArithmeticRed a b) : Arithmetic a b := by
  induction h using ArithmeticRed.rec (motive_2 := fun xs ys _ => ListRel Arithmetic xs ys) with
  | refl => exact .refl _
  | trans _ _ ia ib => exact ia.trans ib
  | node op _ ih => exact .node op ih
  | assocRight a b c => exact .assoc a b c
  | assocLeft a b c => exact (Arithmetic.assoc a b c).symm
  | comm a b => exact .comm a b
  | zeroRight a => exact .zero a
  | zeroLeft a => exact .zero_left a
  | literalSplit n bound => exact (Arithmetic.literal_ones n bound).trans (sumTerms_compact _)
  | literalAdd m n bound => exact .add m n bound
  | nil => exact .nil
  | cons _ _ ia ib => exact .cons ia ib

theorem ArithmeticRed.addCong (ha : ArithmeticRed a a') (hb : ArithmeticRed b b') :
    ArithmeticRed (.node .uadd [a,b]) (.node .uadd [a',b']) :=
  .node .uadd (.cons ha (.cons hb .nil))

theorem ArithmeticRed.compact_append (xs ys : List Term) :
    ArithmeticRed (.node .uadd [compact xs,compact ys]) (compact (xs ++ ys)) := by
  induction xs with
  | nil => exact .zeroLeft _
  | cons x xs ih =>
      cases xs with
      | nil => cases ys with
        | nil => exact .zeroRight _
        | cons y ys => exact .refl _
      | cons y xs =>
          cases ys with
          | nil => simpa only [List.append_nil, compact] using ArithmeticRed.zeroRight (compact (x::y::xs))
          | cons z ys =>
              exact (ArithmeticRed.assocRight x (compact (y::xs)) (compact (z::ys))).trans
                (.addCong (.refl x) ih)

theorem ArithmeticRed.compact_pointwise (h : ListRel ArithmeticRed xs ys) : ArithmeticRed (compact xs) (compact ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih =>
      cases hs with
      | nil => exact h
      | cons hb hs => exact .addCong h ih

theorem ArithmeticRed.compact_perm (p : xs.Perm ys) : ArithmeticRed (compact xs) (compact ys) := by
  induction p with
  | nil => exact .refl _
  | cons x p ih =>
      rename_i xs ys
      cases xs with
      | nil =>
          cases ys with
          | nil => exact .refl _
          | cons y ys => have := p.length_eq; simp at this
      | cons y xs =>
          cases ys with
          | nil => have := p.length_eq; simp at this
          | cons z ys => exact .addCong (.refl x) ih
  | swap a b xs =>
      cases xs with
      | nil => exact .comm _ _
      | cons x xs =>
          exact (ArithmeticRed.assocLeft b a (compact (x::xs))).trans
            ((ArithmeticRed.addCong (.comm b a) (.refl _)).trans (.assocRight a b (compact (x::xs))))
  | trans p q ia ib => exact ia.trans ib

theorem ArithmeticRed.flatten (t : Term) : ArithmeticRed t (compact (arithmeticFlatten t)) := by
  fun_induction arithmeticFlatten t with
  | case1 a b ia ib => exact (ArithmeticRed.addCong ia ib).trans (ArithmeticRed.compact_append _ _)
  | case2 n bound => exact .literalSplit n bound
  | case3 => exact .refl _
  | case4 => exact .refl _

def ArithmeticJoin (a b : Term) : Prop := ∃ c, ArithmeticRed a c ∧ ArithmeticRed b c

private theorem flatten_size {t a : Term} (h : a ∈ arithmeticFlatten t) : sizeOf a ≤ sizeOf t := by
  fun_induction arithmeticFlatten t with
  | case1 x y ix iy =>
      simp only [List.mem_append] at h
      rcases h with hx | hy
      · have := ix hx
        simp_wf
        omega
      · have := iy hy
        simp_wf
        omega
  | case2 n bound =>
      have mem := List.mem_replicate.mp h
      obtain ⟨nonzero, eq⟩ := mem
      subst a
      simp_wf
      omega
  | case3 n _ =>
      simp only [List.mem_singleton] at h
      subst a
      exact Nat.le_refl _
  | case4 t _ _ =>
      simp only [List.mem_singleton] at h
      subst a
      exact Nat.le_refl _

private theorem child_size (op : Op) (xs : List Term) (h : x ∈ xs) :
    sizeOf x < sizeOf (Term.node op xs) := by
  have := List.sizeOf_lt_of_mem h
  simp_wf
  omega

private theorem children_join (h : ListRel R xs ys)
    (j : ∀ a ∈ xs, ∀ b ∈ ys, R a b → ArithmeticJoin a b) :
    ∃ zs, ListRel ArithmeticRed xs zs ∧ ListRel ArithmeticRed ys zs := by
  induction h with
  | nil => exact ⟨[],.nil,.nil⟩
  | cons ha hs ih =>
      obtain ⟨c,hc,kc⟩ := j _ (by simp) _ (by simp) ha
      obtain ⟨zs,hz,kz⟩ := ih (fun a ha b hb hab => j a (by simp [ha]) b (by simp [hb]) hab)
      exact ⟨c::zs,.cons hc hz,.cons kc kz⟩

/-- The additive quotient has a genuine common-forward-reduct property on all
native terms. The proof recurses on displayed atom-child sizes, not on an
assumed normalization or an assumed interpretation's injectivity. -/
theorem Arithmetic.church_rosser (h : Arithmetic a b) : ArithmeticJoin a b := by
  have all : ∀ n, ∀ a b, sizeOf a + sizeOf b = n → ArithmeticModel a b → ArithmeticJoin a b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro a b measure hm
        obtain ⟨xs,hp,hr⟩ := hm.matching ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
        have pairs : ∀ x ∈ xs, ∀ y ∈ arithmeticFlatten b, ArithmeticAtom x y → ArithmeticJoin x y := by
          intro x hx y hy hab
          have xb : sizeOf x ≤ sizeOf a := flatten_size (hp.mem_iff.mpr hx)
          have yb : sizeOf y ≤ sizeOf b := flatten_size hy
          cases hab with
          | var i => exact ⟨_,.refl _,.refl _⟩
          | node op kids =>
              obtain ⟨zs,hz,kz⟩ := children_join kids (by
                intro p hp q hq hpq
                have ps := child_size op _ hp
                have qs := child_size op _ hq
                exact ih (sizeOf p + sizeOf q) (by omega) p q rfl hpq.model)
              exact ⟨_,.node op hz,.node op kz⟩
        have matchingArithmeticJoin := children_join hr pairs
        obtain ⟨zs,hz,kz⟩ := matchingArithmeticJoin
        exact ⟨compact zs,
          (ArithmeticRed.flatten a).trans ((ArithmeticRed.compact_perm hp).trans (ArithmeticRed.compact_pointwise hz)),
          (ArithmeticRed.flatten b).trans (ArithmeticRed.compact_pointwise kz)⟩
  exact all _ a b rfl h.model

theorem arithmetic_iff_join (a b : Term) : Arithmetic a b ↔ ArithmeticJoin a b := by
  constructor
  · exact Arithmetic.church_rosser
  · intro ⟨c,h,k⟩
    exact h.toArithmetic.trans k.toArithmetic.symm

/-- Any two genuine forward ACU computations from one source can be joined. -/
theorem ArithmeticRed.confluence (h : ArithmeticRed a b) (k : ArithmeticRed a c) : ArithmeticJoin b c :=
  (h.toArithmetic.symm.trans k.toArithmetic).church_rosser

end Jihoo.NativeKernel.ACU
