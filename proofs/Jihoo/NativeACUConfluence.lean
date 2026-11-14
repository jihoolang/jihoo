import Jihoo.NativeACUTheory

/-! Genuine forward Church–Rosser for the full-syntax pure ACU layer. Unit
insertion is not a forward rule. This layer excludes legacy beta/arithmetic;
combining its result with legacy reduction requires a further commutation proof. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

/-- Contextual reflexive-transitive forward ACU reduction. Associativity and
commutativity are reversible; zero is only eliminated, never inserted. -/
inductive Red : Term → Term → Prop where
  | refl (t : Term) : Red t t
  | trans : Red a b → Red b c → Red a c
  | node (op : Op) : ListRel Red xs ys → Red (.node op xs) (.node op ys)
  | assocRight (a b c : Term) :
      Red (.node .uadd [.node .uadd [a,b],c]) (.node .uadd [a,.node .uadd [b,c]])
  | assocLeft (a b c : Term) :
      Red (.node .uadd [a,.node .uadd [b,c]]) (.node .uadd [.node .uadd [a,b],c])
  | comm (a b : Term) : Red (.node .uadd [a,b]) (.node .uadd [b,a])
  | zeroRight (a : Term) : Red (.node .uadd [a,.node (.natural 0) []]) a
  | zeroLeft (a : Term) : Red (.node .uadd [.node (.natural 0) [],a]) a

theorem Red.toTheory (h : Red a b) : Theory a b := by
  induction h using Red.rec (motive_2 := fun xs ys _ => ListRel Theory xs ys) with
  | refl => exact .refl _
  | trans _ _ ia ib => exact ia.trans ib
  | node op _ ih => exact .node op ih
  | assocRight a b c => exact .assoc a b c
  | assocLeft a b c => exact (Theory.assoc a b c).symm
  | comm a b => exact .comm a b
  | zeroRight a => exact .zero a
  | zeroLeft a => exact .zero_left a
  | nil => exact .nil
  | cons _ _ ia ib => exact .cons ia ib

theorem Red.addCong (ha : Red a a') (hb : Red b b') :
    Red (.node .uadd [a,b]) (.node .uadd [a',b']) :=
  .node .uadd (.cons ha (.cons hb .nil))

/-- Compact spines contain no trailing zero; a singleton remains its atom. -/
def compact : List Term → Term
  | [] => .node (.natural 0) []
  | [a] => a
  | a :: b :: xs => .node .uadd [a, compact (b :: xs)]

theorem Red.compact_append (xs ys : List Term) :
    Red (.node .uadd [compact xs,compact ys]) (compact (xs ++ ys)) := by
  induction xs with
  | nil => exact .zeroLeft _
  | cons x xs ih =>
      cases xs with
      | nil => cases ys with
        | nil => exact .zeroRight _
        | cons y ys => exact .refl _
      | cons y xs =>
          cases ys with
          | nil => simpa only [List.append_nil, compact] using Red.zeroRight (compact (x::y::xs))
          | cons z ys =>
              exact (Red.assocRight x (compact (y::xs)) (compact (z::ys))).trans
                (.addCong (.refl x) ih)

theorem Red.compact_pointwise (h : ListRel Red xs ys) : Red (compact xs) (compact ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih =>
      cases hs with
      | nil => exact h
      | cons hb hs => exact .addCong h ih

theorem Red.compact_perm (p : xs.Perm ys) : Red (compact xs) (compact ys) := by
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
          exact (Red.assocLeft b a (compact (x::xs))).trans
            ((Red.addCong (.comm b a) (.refl _)).trans (.assocRight a b (compact (x::xs))))
  | trans p q ia ib => exact ia.trans ib

theorem Red.flatten (t : Term) : Red t (compact (ACU.flatten t)) := by
  fun_induction ACU.flatten t with
  | case1 a b ia ib => exact (Red.addCong ia ib).trans (Red.compact_append _ _)
  | case2 => exact .refl _
  | case3 => exact .refl _

def Join (a b : Term) : Prop := ∃ c, Red a c ∧ Red b c

private theorem flatten_size {t a : Term} (h : a ∈ flatten t) : sizeOf a ≤ sizeOf t := by
  fun_induction ACU.flatten t with
  | case1 x y ix iy =>
      simp only [List.mem_append] at h
      rcases h with hx | hy
      · have := ix hx
        simp_wf
        omega
      · have := iy hy
        simp_wf
        omega
  | case2 => simp at h
  | case3 t _ _ =>
      simp only [List.mem_singleton] at h
      subst a
      exact Nat.le_refl _

private theorem child_size (op : Op) (xs : List Term) (h : x ∈ xs) :
    sizeOf x < sizeOf (Term.node op xs) := by
  have := List.sizeOf_lt_of_mem h
  simp_wf
  omega

private theorem children_join (h : ListRel R xs ys)
    (j : ∀ a ∈ xs, ∀ b ∈ ys, R a b → Join a b) :
    ∃ zs, ListRel Red xs zs ∧ ListRel Red ys zs := by
  induction h with
  | nil => exact ⟨[],.nil,.nil⟩
  | cons ha hs ih =>
      obtain ⟨c,hc,kc⟩ := j _ (by simp) _ (by simp) ha
      obtain ⟨zs,hz,kz⟩ := ih (fun a ha b hb hab => j a (by simp [ha]) b (by simp [hb]) hab)
      exact ⟨c::zs,.cons hc hz,.cons kc kz⟩

/-- The additive quotient has a genuine common-forward-reduct property on all
native terms. The proof recurses on displayed atom-child sizes, not on an
assumed normalization or an assumed interpretation's injectivity. -/
theorem Theory.church_rosser (h : Theory a b) : Join a b := by
  have all : ∀ n, ∀ a b, sizeOf a + sizeOf b = n → Model a b → Join a b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro a b measure hm
        obtain ⟨xs,hp,hr⟩ := hm.matching AtomRel.refl AtomRel.symm AtomRel.trans
        have pairs : ∀ x ∈ xs, ∀ y ∈ ACU.flatten b, AtomRel x y → Join x y := by
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
        have matchingJoin := children_join hr pairs
        obtain ⟨zs,hz,kz⟩ := matchingJoin
        exact ⟨compact zs,
          (Red.flatten a).trans ((Red.compact_perm hp).trans (Red.compact_pointwise hz)),
          (Red.flatten b).trans (Red.compact_pointwise kz)⟩
  exact all _ a b rfl h.model

theorem theory_iff_join (a b : Term) : Theory a b ↔ Join a b := by
  constructor
  · exact Theory.church_rosser
  · intro ⟨c,h,k⟩
    exact h.toTheory.trans k.toTheory.symm

/-- Any two genuine forward ACU computations from one source can be joined. -/
theorem Red.confluence (h : Red a b) (k : Red a c) : Join b c :=
  (h.toTheory.symm.trans k.toTheory).church_rosser

end Jihoo.NativeKernel.ACU
