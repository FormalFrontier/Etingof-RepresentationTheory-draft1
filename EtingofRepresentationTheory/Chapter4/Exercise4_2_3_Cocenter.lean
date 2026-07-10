import Mathlib

/-!
# Cocenter of a finite group algebra (Exercise 4.2.3, counting deliverable 1)

This file computes the dimension of the **cocenter**
`C = k[G] / [k[G], k[G]]` of a finite group algebra:

  `Module.finrank k C = Nat.card (ConjClasses G)`.

The result is **field-general**: only `[Field k]` is assumed, with no `IsAlgClosed`
and no invertibility of `|G|`. This is the dual of the center computation
`finrank_center_monoidAlgebra` in `Chapter4/Corollary4_2_2.lean` (which shows
`finrank_k Z(k[G]) = #ConjClasses` via class sums), and it supplies **deliverable 1**
of the counting half of Exercise 4.2.3, namely the eventual bound
`#(simple k[G]-modules) ≤ Nat.card (ConjClasses G)`. (Deliverables 2 and 3 — the
trace form on the cocenter and the linear-independence argument giving the bound —
are tracked in sibling issues.)

## Proof strategy

The cocenter's linear dual is the space of trace-like (class) functionals, and the
images of conjugacy-class representatives form a `k`-basis of `C`. We prove the
dimension by squeezing between two bounds, each obtained from a surjective linear map:

* **Lower bound.** The *class-coefficient* map
  `φ : k[G] → (ConjClasses G → k)`, sending `single g c` to `c • Pi.single (mk g) 1`
  (equivalently, `φ a C' = ∑_{g ∈ C'} a g`), is a "trace": `φ (x*y) = φ (y*x)`. Hence
  it kills the commutator submodule and descends to a **surjection**
  `C ↠ (ConjClasses G → k)`, giving `#ConjClasses ≤ finrank C`.
* **Upper bound.** The images `[single (out C') 1]` of conjugacy-class representatives
  **span** `C` (conjugate group elements have equal image in `C`), so `#ConjClasses`
  of them suffice, giving `finrank C ≤ #ConjClasses`.
-/

open MonoidAlgebra

namespace Etingof

namespace CocenterMonoidAlgebra

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

variable (k G) in
/-- The commutator submodule `[k[G], k[G]]`: the `k`-span of all `x*y - y*x`. -/
noncomputable def commSubmodule : Submodule k (MonoidAlgebra k G) :=
  Submodule.span k (Set.range (fun p : MonoidAlgebra k G × MonoidAlgebra k G =>
    p.1 * p.2 - p.2 * p.1))

variable (k G) in
/-- The **cocenter** `C = k[G] / [k[G], k[G]]` of the group algebra. -/
noncomputable abbrev Cocenter : Type _ := MonoidAlgebra k G ⧸ commSubmodule k G

/-! ### The class-coefficient map `φ : k[G] → (ConjClasses G → k)` -/

variable (k G) in
/-- The **class-coefficient map**: `φ a C'` is the sum of the coefficients of `a` over the
conjugacy class `C'`. On a basis element, `φ (single g c) C' = if mk g = C' then c else 0`. -/
noncomputable def classCoeff : MonoidAlgebra k G →ₗ[k] (ConjClasses G → k) where
  toFun a := fun C' => ∑ g : G, if ConjClasses.mk g = C' then a g else 0
  map_add' a b := by
    funext C'
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by rw [Finsupp.add_apply]; split <;> simp
  map_smul' r a := by
    funext C'
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [Finsupp.smul_apply, smul_eq_mul]; split <;> simp

lemma classCoeff_single (g : G) (c : k) :
    classCoeff k G (single g c) = fun C' => if ConjClasses.mk g = C' then c else 0 := by
  funext C'
  simp only [classCoeff, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single g]
  · rw [Finsupp.single_apply, if_pos rfl]
  · intro b _ hbg
    rw [Finsupp.single_apply, if_neg (Ne.symm hbg), ite_self]
  · intro hg; exact absurd (Finset.mem_univ g) hg

/-- The class-coefficient map is a trace: `φ (x*y) = φ (y*x)`. This is the algebraic
heart of the descent to the cocenter. -/
lemma classCoeff_mul_comm (x y : MonoidAlgebra k G) :
    classCoeff k G (x * y) = classCoeff k G (y * x) := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    induction y using MonoidAlgebra.induction_on with
    | hM h =>
      rw [of_apply, of_apply, single_mul_single, single_mul_single,
        classCoeff_single, classCoeff_single,
        show ConjClasses.mk (g * h) = ConjClasses.mk (h * g) from
          ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)]
    | hadd y₁ y₂ h₁ h₂ => rw [mul_add, add_mul, map_add, map_add, h₁, h₂]
    | hsmul r y h => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_smul, map_smul, h]
  | hadd x₁ x₂ h₁ h₂ => rw [add_mul, mul_add, map_add, map_add, h₁, h₂]
  | hsmul r x h => rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smul, map_smul, h]

lemma commSubmodule_le_ker : commSubmodule k G ≤ LinearMap.ker (classCoeff k G) := by
  rw [commSubmodule, Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, classCoeff_mul_comm x y, sub_self]

/-- The class-coefficient map is surjective: it hits every indicator `Pi.single C' 1`. -/
lemma classCoeff_surjective : Function.Surjective (classCoeff k G) := by
  have hmk : ∀ C' : ConjClasses G, ConjClasses.mk (Quotient.out C') = C' := fun C' => by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  intro f
  refine ⟨∑ C' : ConjClasses G, f C' • single (Quotient.out C') 1, ?_⟩
  funext D
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, classCoeff_single, hmk, Pi.smul_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ D f]
  simp

variable (k G) in
/-- The descent of the class-coefficient map to the cocenter `C = k[G] / [k[G], k[G]]`. -/
noncomputable def classCoeffQ : Cocenter k G →ₗ[k] (ConjClasses G → k) :=
  Submodule.liftQ (commSubmodule k G) (classCoeff k G) commSubmodule_le_ker

lemma classCoeffQ_surjective : Function.Surjective (classCoeffQ k G) := by
  intro f
  obtain ⟨a, ha⟩ := classCoeff_surjective f
  exact ⟨Submodule.Quotient.mk a, by rw [classCoeffQ, Submodule.liftQ_apply, ha]⟩

/-! ### The spanning family of conjugacy-class representatives -/

variable (k G) in
/-- The image `[single (out C') 1]` in the cocenter of a representative of the conjugacy
class `C'`. These span the cocenter. -/
noncomputable def classRep : ConjClasses G → Cocenter k G :=
  fun C' => Submodule.mkQ (commSubmodule k G) (single (Quotient.out C') 1)

omit [Fintype G] [DecidableEq G] in
/-- If `a` and `b` are conjugate, then `single a 1 - single b 1` lies in the commutator
submodule. Indeed `b = c a c⁻¹` gives `single a 1 - single b 1 =
single c⁻¹ 1 * single (c*a) 1 - single (c*a) 1 * single c⁻¹ 1`. -/
lemma single_sub_single_conj_mem {a b : G} (h : IsConj a b) :
    single a (1 : k) - single b 1 ∈ commSubmodule k G := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hrw : single (c⁻¹) (1 : k) * single (c * a) 1 - single (c * a) 1 * single (c⁻¹) 1
      = single a 1 - single b 1 := by
    rw [single_mul_single, single_mul_single, one_mul,
      show c⁻¹ * (c * a) = a by group, show c * a * c⁻¹ = b from hc]
  rw [← hrw]
  exact Submodule.subset_span ⟨(single (c⁻¹) 1, single (c * a) 1), rfl⟩

omit [Fintype G] [DecidableEq G] in
/-- The image of `single g 1` in the cocenter equals the class representative `classRep (mk g)`. -/
lemma mkQ_single_eq_classRep (g : G) :
    Submodule.mkQ (commSubmodule k G) (single g 1) = classRep k G (ConjClasses.mk g) := by
  have hmk : ConjClasses.mk (Quotient.out (ConjClasses.mk g)) = ConjClasses.mk g := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  rw [classRep, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact single_sub_single_conj_mem (ConjClasses.mk_eq_mk_iff_isConj.mp hmk.symm)

omit [Fintype G] [DecidableEq G] in
/-- The elements `single g 1` span the whole group algebra `k[G]`. -/
lemma span_range_single_eq_top :
    Submodule.span k (Set.range (fun g : G => (single g 1 : MonoidAlgebra k G))) = ⊤ := by
  rw [eq_top_iff]
  rintro a -
  induction a using MonoidAlgebra.induction_on with
  | hM g => exact Submodule.subset_span ⟨g, rfl⟩
  | hadd x y hx hy => exact Submodule.add_mem _ hx hy
  | hsmul r x hx => exact Submodule.smul_mem _ r hx

omit [Fintype G] [DecidableEq G] in
/-- The class representatives span the cocenter. -/
lemma span_range_classRep_eq_top :
    Submodule.span k (Set.range (classRep k G)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← Submodule.range_mkQ (commSubmodule k G), LinearMap.range_eq_map,
    ← span_range_single_eq_top, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mkQ_single_eq_classRep g]
  exact Submodule.subset_span ⟨ConjClasses.mk g, rfl⟩

/-! ### The dimension of the cocenter -/

noncomputable instance : Module.Finite k (MonoidAlgebra k G) :=
  Module.Finite.of_basis (Finsupp.basisSingleOne (ι := G) (R := k))

noncomputable instance : Module.Finite k (Cocenter k G) :=
  Module.Finite.of_surjective (Submodule.mkQ (commSubmodule k G)) (Submodule.mkQ_surjective _)

/-- **Cocenter dimension (Exercise 4.2.3, deliverable 1).** The cocenter
`C = k[G] / [k[G], k[G]]` of a finite group algebra has `finrank` equal to the number
of conjugacy classes of `G`. Field-general: no `IsAlgClosed`, no invertibility of `|G|`. -/
theorem finrank_cocenter_eq_card_conjClasses :
    Module.finrank k (Cocenter k G) = Nat.card (ConjClasses G) := by
  have hle1 : Fintype.card (ConjClasses G) ≤ Module.finrank k (Cocenter k G) := by
    have h := LinearMap.finrank_le_finrank_of_surjective (classCoeffQ_surjective (k := k) (G := G))
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have hle2 : Module.finrank k (Cocenter k G) ≤ Fintype.card (ConjClasses G) := by
    have hv := finrank_range_le_card (R := k) (classRep k G)
    have heq : (Set.range (classRep k G)).finrank k = Module.finrank k (Cocenter k G) := by
      change Module.finrank k (Submodule.span k (Set.range (classRep k G))) = _
      rw [span_range_classRep_eq_top, finrank_top]
    rwa [heq] at hv
  rw [le_antisymm hle2 hle1, Nat.card_eq_fintype_card]

end CocenterMonoidAlgebra

end Etingof
