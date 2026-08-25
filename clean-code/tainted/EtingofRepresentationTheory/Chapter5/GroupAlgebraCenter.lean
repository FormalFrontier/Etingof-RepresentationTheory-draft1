import Mathlib

/-!
# The center of a finite group algebra and conjugacy classes

The classical bridge underlying "over `ℂ` the number of irreducible representations of a
finite group equals its number of conjugacy classes" has, as its group-algebra half, the
statement that the center of the group algebra `k[G]` is spanned by the *class sums* and
therefore has dimension equal to the number of conjugacy classes of `G`.

This file proves that half:

* `Etingof.GroupAlgebra.mem_center_iff_coeff` — an element of `k[G]` is central iff its
  coefficient function is constant on conjugacy classes (a *class function*).
* `Etingof.GroupAlgebra.centerEquivClassFun` — the resulting linear equivalence between the
  center of `k[G]` and the space of functions on conjugacy classes.
* `Etingof.GroupAlgebra.finrank_center_eq_card_conjClasses` — for a field `k` and a finite
  group `G`, `dim_k Z(k[G]) = #(ConjClasses G)`.

This is the Mathlib-missing input recorded in the Discussion after the `GL₂(𝔽_q)` completeness
summary; it is a general result about group algebras, independent of the field being `ℂ`.
-/

namespace Etingof.GroupAlgebra

open scoped MonoidAlgebra

open MonoidAlgebra

section General

variable {k G : Type*} [CommRing k] [Group G]

/-- An element `x` of the group algebra `k[G]` lies in the center iff its coefficient
function is invariant under conjugation, i.e. it is constant on conjugacy classes. -/
theorem mem_center_iff_coeff (x : MonoidAlgebra k G) :
    x ∈ Subalgebra.center k (MonoidAlgebra k G) ↔
      ∀ g h : G, x.coeff (g * h * g⁻¹) = x.coeff h := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · -- centrality ⇒ conjugation-invariance of coefficients
    intro hx g h
    have hcomm := hx (single g (1 : k))
    have h1 : (single g (1 : k) * x).coeff (g * h) = x.coeff h := by
      simp
    have h2 : (x * single g (1 : k)).coeff (g * h) = x.coeff (g * h * g⁻¹) := by
      simp
    rw [hcomm] at h1
    rw [h2] at h1
    exact h1
  · -- conjugation-invariance ⇒ commutes with every element
    intro hcoeff y
    -- it suffices that `x` commutes with every `single g c`
    have hsingle : ∀ (g : G) (c : k), single g c * x = x * single g c := by
      intro g c
      ext h
      rw [coeff_single_mul_apply, coeff_mul_single_apply, mul_comm]
      congr 1
      -- `x (g⁻¹ * h) = x (h * g⁻¹)`, conjugate of one another
      have := hcoeff g (g⁻¹ * h)
      rw [← mul_assoc, mul_inv_cancel, one_mul] at this
      exact this.symm
    -- extend from generators to all of `y` by linearity
    conv_lhs => rw [← y.sum_coeff_single]
    conv_rhs => rw [← y.sum_coeff_single]
    simp only [Finsupp.sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun g _ => hsingle g (y.coeff g)

variable [Fintype G]

omit [Group G] in
/-- The value at `h` of the "diagonal" element `∑ g, single g (c g)` is just `c h`. -/
private theorem apply_sum_single (c : G → k) (h : G) :
    (∑ g : G, single g (c g)).coeff h = c h := by
  classical
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single h]
  · simp
  · intro b _ hbh
    simp [hbh]
  · simp

/-- The canonical central group-algebra element attached to a class function `f` is central:
its coefficients are constant on conjugacy classes by construction. -/
private theorem sum_single_classFun_mem_center (f : ConjClasses G → k) :
    (∑ g : G, single g (f (ConjClasses.mk g))) ∈
      Subalgebra.center k (MonoidAlgebra k G) := by
  rw [mem_center_iff_coeff]
  intro g h
  rw [apply_sum_single (fun g => f (ConjClasses.mk g)),
    apply_sum_single (fun g => f (ConjClasses.mk g))]
  congr 1
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  exact ⟨g⁻¹, by group⟩

end General

section FieldCase

variable (k G : Type*) [Field k] [Group G] [Fintype G]

/-- The center of the finite group algebra `k[G]` is linearly equivalent to the space of
class functions `ConjClasses G → k`, via `x ↦ (c ↦ coefficient of x on the class c)`. -/
noncomputable def centerEquivClassFun :
    ↥(Subalgebra.center k (MonoidAlgebra k G)) ≃ₗ[k] (ConjClasses G → k) where
  toFun x c := Quotient.liftOn c (fun g => (x : MonoidAlgebra k G).coeff g)
    (fun a b hab => by
      obtain ⟨c, rfl⟩ := isConj_iff.mp hab
      exact ((mem_center_iff_coeff (x : MonoidAlgebra k G)).mp x.2 c a).symm)
  map_add' x y := by
    funext c
    induction c using Quotient.inductionOn with
    | h g => simp [AddMemClass.coe_add]
  map_smul' r x := by
    funext c
    induction c using Quotient.inductionOn with
    | h g => simp [SetLike.val_smul]
  invFun f := ⟨∑ g : G, single g (f (ConjClasses.mk g)), sum_single_classFun_mem_center f⟩
  left_inv x := by
    apply Subtype.ext
    ext h
    exact apply_sum_single (fun g => (x : MonoidAlgebra k G).coeff g) h
  right_inv f := by
    funext c
    induction c using Quotient.inductionOn with
    | h g => exact apply_sum_single (fun g => f (ConjClasses.mk g)) g

omit [Fintype G] in
/-- **The center of a finite group algebra has dimension equal to the number of conjugacy
classes.** For a field `k` and a finite group `G`,
`dim_k Z(k[G]) = #(ConjClasses G)`. This is the group-algebra half of the character-theoretic
identity `#(irreducible ℂ-reps of G) = #(ConjClasses G)`. -/
theorem finrank_center_eq_card_conjClasses [Finite G] :
    Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k G)) = Nat.card (ConjClasses G) := by
  haveI : Fintype G := Fintype.ofFinite _
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [(centerEquivClassFun k G).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end FieldCase

end Etingof.GroupAlgebra
