/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SymmetricPowerRepresentations
import RepresentationTheory.AsModuleEquivalences
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct DirectSum

set_option linter.unusedFintypeInType false

noncomputable section

namespace RepresentationTheory.RepresentationPolynomialFunctions







/-- Shows that a function subalgebra is top when it separates every pair of distinct points. -/
theorem subalgebra_eq_top_of_separatesPoints
    {α : Type*} [Fintype α] {𝕜 : Type*} [Field 𝕜] (A : Subalgebra 𝕜 (α → 𝕜))
    (hsep : ∀ x y : α, x ≠ y → ∃ f ∈ A, f x ≠ f y) : A = ⊤ := by
  classical

  have hsingle : ∀ i : α, Pi.single i (1 : 𝕜) ∈ A := by
    intro i

    have hg : ∀ j : {j : α // j ≠ i}, ∃ g ∈ A, g i = 1 ∧ g j.1 = 0 := by
      rintro ⟨j, hj⟩
      obtain ⟨fj, hfjA, hfj⟩ := hsep i j (Ne.symm hj)
      have hc0 : fj i - fj j ≠ 0 := sub_ne_zero.mpr hfj
      refine ⟨(fj i - fj j)⁻¹ • (fj - fj j • 1), ?_, ?_, ?_⟩
      · exact Subalgebra.smul_mem _
          (Subalgebra.sub_mem _ hfjA (Subalgebra.smul_mem _ (one_mem _) _)) _
      · simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
        rw [inv_mul_cancel₀ hc0]
      · simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one, sub_self,
          mul_zero]
    choose g hgA hgi hgj using hg

    have hmem : (∏ j : {j : α // j ≠ i}, g j) ∈ A := prod_mem (fun j _ => hgA j)
    have heq : (∏ j : {j : α // j ≠ i}, g j) = Pi.single i (1 : 𝕜) := by
      funext k
      rw [Finset.prod_apply]
      by_cases hk : k = i
      · subst hk
        simp only [hgi, Finset.prod_const_one, Pi.single_eq_same]
      · rw [Finset.prod_eq_zero (Finset.mem_univ (⟨k, hk⟩ : {j : α // j ≠ i})) (hgj ⟨k, hk⟩),
          Pi.single_eq_of_ne hk]
    rwa [heq] at hmem
  rw [eq_top_iff]
  intro f _
  have hf : f = ∑ i : α, f i • Pi.single i (1 : 𝕜) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ k f]
    simp
  rw [hf]
  exact Subalgebra.sum_mem _ (fun i _ => Subalgebra.smul_mem _ (hsingle i) _)



variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]



/-- Maps a dual vector to a linear functional on a tensor power. -/
def tensorPowerEvaluation (p : Module.Dual ℂ V) (n : ℕ) : (⨂[ℂ]^n V) →ₗ[ℂ] ℂ :=
  PiTensorProduct.dualDistrib (⨂ₜ[ℂ] (_ : Fin n), p)

/-- Evaluates a pure tensor as the product of its dual-vector values. -/
@[simp] lemma tensorPowerEvaluation_tprod (p : Module.Dual ℂ V) (n : ℕ) (v : Fin n → V) :
    tensorPowerEvaluation p n (PiTensorProduct.tprod ℂ v) = ∏ i, p (v i) := by
  simp only [tensorPowerEvaluation, PiTensorProduct.dualDistrib_apply]




/-- Maps a dual vector to a linear functional on a symmetric power. -/
def symmetricPowerEvaluation (p : Module.Dual ℂ V) (n : ℕ) : Sym[ℂ]^n V →ₗ[ℂ] ℂ where
  toFun := AddCon.lift _ (tensorPowerEvaluation p n).toAddMonoidHom (fun x y h => by
    induction h with
    | of x y h => cases h with
      | perm e f =>
        change tensorPowerEvaluation p n (PiTensorProduct.tprod ℂ f)
          = tensorPowerEvaluation p n (PiTensorProduct.tprod ℂ fun i => f (e i))
        rw [tensorPowerEvaluation_tprod, tensorPowerEvaluation_tprod]
        exact (Equiv.prod_comp e (fun i => p (f i))).symm
    | refl => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | add _ _ ih₁ ih₂ =>
        change tensorPowerEvaluation p n (_ + _) = tensorPowerEvaluation p n (_ + _)
        rw [map_add, map_add]
        exact congr_arg₂ (· + ·) ih₁ ih₂)
  map_add' x y := by
    refine AddCon.induction_on₂ x y (fun a b => ?_)
    change tensorPowerEvaluation p n (a + b) = tensorPowerEvaluation p n a + tensorPowerEvaluation p n b
    rw [map_add]
  map_smul' r x := by
    refine AddCon.induction_on x (fun a => ?_)
    change tensorPowerEvaluation p n (r • a) = r • tensorPowerEvaluation p n a
    rw [map_smul]

/-- Relates evaluation on a symmetric-power quotient to evaluation on a tensor power. -/
@[simp] lemma symmetricPowerEvaluation_mk (p : Module.Dual ℂ V) (n : ℕ) (x : ⨂[ℂ]^n V) :
    symmetricPowerEvaluation p n (SymmetricPower.mk ℂ (Fin n) V x) = tensorPowerEvaluation p n x := rfl

/-- Evaluates a pure symmetric tensor as the product of its dual-vector values. -/
@[simp] lemma symmetricPowerEvaluation_tprod (p : Module.Dual ℂ V) (n : ℕ) (v : Fin n → V) :
    symmetricPowerEvaluation p n (SymmetricPower.mk ℂ (Fin n) V (PiTensorProduct.tprod ℂ v)) = ∏ i, p (v i) := by
  rw [symmetricPowerEvaluation_mk, tensorPowerEvaluation_tprod]



/-- Describes evaluation after applying the induced map on a symmetric power. -/
lemma symmetricPowerEvaluation_map (p : Module.Dual ℂ V) (n : ℕ) (f : V →ₗ[ℂ] V) (x : Sym[ℂ]^n V) :
    symmetricPowerEvaluation p n (RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap f x) = symmetricPowerEvaluation (p ∘ₗ f) n x := by
  obtain ⟨y, rfl⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk ℂ (Fin n) V) x
  rw [RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap_mk, symmetricPowerEvaluation_mk, symmetricPowerEvaluation_mk]
  have key : tensorPowerEvaluation p n ∘ₗ PiTensorProduct.map (fun _ : Fin n => f) = tensorPowerEvaluation (p ∘ₗ f) n := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, tensorPowerEvaluation_tprod]
  exact LinearMap.congr_fun key y



variable {G : Type*} [Group G] [Fintype G] (ρ : Representation ℂ G V)



/-- Constructs a linear functional on the direct sum of symmetric powers. -/
def gradedSymmetricPowerEvaluation (q : Module.Dual ℂ V) : (⨁ n : ℕ, Sym[ℂ]^n V) →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ ℕ ℂ (fun n => symmetricPowerEvaluation q n)

/-- Computes the graded evaluation functional on a homogeneous summand. -/
@[simp] lemma gradedSymmetricPowerEvaluation_lof (q : Module.Dual ℂ V) (n : ℕ) (w : Sym[ℂ]^n V) :
    gradedSymmetricPowerEvaluation q (DirectSum.lof ℂ ℕ (fun n => Sym[ℂ]^n V) n w) = symmetricPowerEvaluation q n w := by
  simp only [gradedSymmetricPowerEvaluation, DirectSum.toModule_lof]

variable (u : Module.Dual ℂ V)


/-- Evaluates a dual vector along a group element to obtain another dual vector. -/
def dualOrbitEvaluation (g : G) : Module.Dual ℂ V := (Representation.dual ρ) g u

/-- Describes composition of an orbit evaluation with a representation action. -/
lemma dualOrbitEvaluation_comp (x g : G) :
    (dualOrbitEvaluation ρ u x) ∘ₗ ρ g = dualOrbitEvaluation ρ u (g⁻¹ * x) := by
  ext v
  change (dualOrbitEvaluation ρ u x) (ρ g v) = (dualOrbitEvaluation ρ u (g⁻¹ * x)) v
  simp only [dualOrbitEvaluation, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv]



/-- Constructs a linear map from graded symmetric powers to functions on the group. -/
@[source_ref "Chapter4/Problem4.12.10" (role := supporting)]
def gradedMatrixCoefficient : (⨁ n : ℕ, Sym[ℂ]^n V) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi (fun g => gradedSymmetricPowerEvaluation (dualOrbitEvaluation ρ u g))

/-- Computes the graded matrix coefficient at a group element. -/
@[simp] lemma gradedMatrixCoefficient_apply (t : ⨁ n : ℕ, Sym[ℂ]^n V) (g : G) :
    gradedMatrixCoefficient ρ u t g = gradedSymmetricPowerEvaluation (dualOrbitEvaluation ρ u g) t := rfl



/-- Relates the graded evaluation functional to the group action. -/
lemma gradedSymmetricPowerEvaluation_comp (g x : G) :
    gradedSymmetricPowerEvaluation (dualOrbitEvaluation ρ u x) ∘ₗ (Representation.directSum (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n)) g
      = gradedSymmetricPowerEvaluation (dualOrbitEvaluation ρ u (g⁻¹ * x)) := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, Representation.directSum_apply, DirectSum.lmap_lof,
    gradedSymmetricPowerEvaluation_lof, RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation_apply, symmetricPowerEvaluation_map, dualOrbitEvaluation_comp]





/-- Establishes injectivity of the orbit evaluation map from the stated stabilizer condition. -/
lemma dualOrbitEvaluation_injective (hρ : Function.Injective ρ)
    (hu : ∀ g : G, (Representation.dual ρ) g u = u → g = 1) :
    Function.Injective (dualOrbitEvaluation ρ u) := by
  intro x y hxy

  have h1 : (Representation.dual ρ) (y⁻¹ * x) u = u := by
    have : (Representation.dual ρ) (y⁻¹ * x) u
        = (Representation.dual ρ) y⁻¹ ((Representation.dual ρ) x u) := by
      rw [map_mul]; rfl
    rw [this, show (Representation.dual ρ) x u = dualOrbitEvaluation ρ u x from rfl, hxy]
    change (Representation.dual ρ) y⁻¹ ((Representation.dual ρ) y u) = u
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have := hu _ h1
  rw [inv_mul_eq_one] at this
  exact this.symm





/-- Establishes surjectivity of the graded matrix coefficient map from the stated hypotheses. -/
lemma gradedMatrixCoefficient_surjective (hρ : Function.Injective ρ)
    (hu : ∀ g : G, (Representation.dual ρ) g u = u → g = 1) :
    Function.Surjective (gradedMatrixCoefficient ρ u) := by
  classical
  rw [← LinearMap.range_eq_top]

  set ℓ : V → (G → ℂ) := fun v g => (dualOrbitEvaluation ρ u g) v with hℓ
  set S : Set (G → ℂ) := Set.range ℓ with hS

  have hmono : ∀ (m : ℕ) (v : Fin m → V),
      (fun g => ∏ i, (dualOrbitEvaluation ρ u g) (v i)) ∈ LinearMap.range (gradedMatrixCoefficient ρ u) := by
    intro m v
    refine ⟨DirectSum.lof ℂ ℕ (fun n => Sym[ℂ]^n V) m
      (SymmetricPower.mk ℂ (Fin m) V (PiTensorProduct.tprod ℂ v)), ?_⟩
    funext g
    rw [gradedMatrixCoefficient_apply, gradedSymmetricPowerEvaluation_lof, symmetricPowerEvaluation_tprod]

  have hclosure : ∀ f ∈ Submonoid.closure S, f ∈ LinearMap.range (gradedMatrixCoefficient ρ u) := by
    intro f hf
    have hex : ∃ (m : ℕ) (v : Fin m → V), f = fun g => ∏ i, (dualOrbitEvaluation ρ u g) (v i) := by
      induction hf using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨1, ![v], by funext g; simp [hℓ]⟩
      | one => exact ⟨0, ![], by funext g; simp⟩
      | mul x y _ _ ihx ihy =>
        obtain ⟨m, v, rfl⟩ := ihx
        obtain ⟨m', v', rfl⟩ := ihy
        refine ⟨m + m', Fin.append v v', ?_⟩
        funext g
        simp only [Pi.mul_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
    obtain ⟨m, v, rfl⟩ := hex
    exact hmono m v

  have htop : Algebra.adjoin ℂ S = ⊤ := by
    apply subalgebra_eq_top_of_separatesPoints
    intro x y hxy
    have hpxy : dualOrbitEvaluation ρ u x ≠ dualOrbitEvaluation ρ u y :=
      fun h => hxy (dualOrbitEvaluation_injective ρ u hρ hu h)
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hpxy
    exact ⟨ℓ v, Algebra.subset_adjoin ⟨v, rfl⟩, hv⟩

  have hle : (Algebra.adjoin ℂ S).toSubmodule ≤ LinearMap.range (gradedMatrixCoefficient ρ u) := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    exact hclosure
  rw [htop] at hle
  simpa using hle













/-- Produces a surjective equivariant map from graded symmetric powers under faithful action. -/
@[source_ref "Chapter4/Problem4.12.10" (role := primary)]
theorem exists_surjective_equivariant_graded_map (hρ : Function.Injective ρ) :
    ∃ φ : (⨁ n : ℕ, Sym[ℂ]^n V) →ₗ[ℂ] MonoidAlgebra ℂ G,
      Function.Surjective φ ∧
      ∀ g : G, φ ∘ₗ (Representation.directSum (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n)) g
        = (Representation.ofMulAction ℂ G G) g ∘ₗ φ := by
  classical

  obtain ⟨u, hu⟩ := RepresentationTheory.SymmetricPowerRepresentations.exists_dual_vector_trivial_stabilizer ρ hρ

  refine ⟨(MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
      (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm.toLinearMap ∘ₗ gradedMatrixCoefficient ρ u, ?_, ?_⟩
  ·
    exact (MonoidAlgebra.coeffLinearEquiv ℂ).symm.surjective.comp
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm.surjective.comp
        (gradedMatrixCoefficient_surjective ρ u hρ hu))
  ·
    intro g
    apply LinearMap.ext
    intro t
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro x

    change gradedMatrixCoefficient ρ u ((Representation.directSum (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n)) g t) x
      = ((Representation.ofMulAction ℂ G G) g
          (MonoidAlgebra.ofCoeff
            ((Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm (gradedMatrixCoefficient ρ u t)))).coeff x
    rw [Representation.ofMulAction_apply]
    change gradedMatrixCoefficient ρ u ((Representation.directSum (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n)) g t) x
      = gradedMatrixCoefficient ρ u t (g⁻¹ • x)
    rw [gradedMatrixCoefficient_apply, gradedMatrixCoefficient_apply, smul_eq_mul,
      ← LinearMap.congr_fun (gradedSymmetricPowerEvaluation_comp ρ u g x) t]
    rfl

end RepresentationTheory.RepresentationPolynomialFunctions

end

section MainTheorem

open scoped TensorProduct
open RepresentationTheory.RepresentationPolynomialFunctions


















/-- Produces a nonzero equivariant map into a symmetric-power representation under the stated hypotheses. -/
@[source_ref "Chapter4/Problem4.12.10" (role := supporting)]
theorem RepresentationTheory.RepresentationPolynomialFunctions.exists_nonzero_symmetric_power_intertwiner {G : Type*} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule) :
    ∃ (n : ℕ) (φ : W →ₗ[ℂ] (Sym[ℂ]^n V)),
      φ ≠ 0 ∧ ∀ g : G, φ ∘ₗ σ g = (RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n g) ∘ₗ φ := by
  classical
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

  obtain ⟨ι, hι_inj, hι_equiv⟩ := RepresentationTheory.SymmetricPowerRepresentations.exists_injective_regular_intertwiner σ hσ

  obtain ⟨E, hE_surj, hE_equiv⟩ := RepresentationTheory.RepresentationPolynomialFunctions.exists_surjective_equivariant_graded_map ρ hρ


  set F : (Representation.directSum (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n)).asModule
      →ₗ[MonoidAlgebra ℂ G] (Representation.ofMulAction ℂ G G).asModule :=
    RepresentationTheory.AsModuleEquivalences.linearMapAsModule E
      (fun g x => LinearMap.congr_fun (hE_equiv g) x) with hF
  have hF_surj : Function.Surjective F := hE_surj
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property (R := MonoidAlgebra ℂ G)
    (M := (Representation.directSum (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n)).asModule)
    (N := (Representation.ofMulAction ℂ G G).asModule)
    (P := (Representation.ofMulAction ℂ G G).asModule) F hF_surj (LinearMap.id)
  have hs_linv : Function.LeftInverse F s := fun x => by
    simpa using LinearMap.congr_fun hs x

  set sLin := RepresentationTheory.SymmetricPowerRepresentations.asModuleHomToLinearMap s with hsLin
  have hsLin_inj : Function.Injective sLin :=
    RepresentationTheory.SymmetricPowerRepresentations.asModuleHomToLinearMap_injective hs_linv.injective

  set Φ := sLin ∘ₗ ι with hΦ
  have hΦ_inj : Function.Injective Φ := hsLin_inj.comp hι_inj
  haveI : Nontrivial W := hσ.nontrivial
  have hΦ_ne : Φ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    intro h0
    apply hw
    apply hΦ_inj
    rw [h0]; simp
  have hΦ_equiv : ∀ g : G, Φ ∘ₗ σ g
      = (Representation.directSum (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n)) g ∘ₗ Φ := by
    intro g
    apply LinearMap.ext
    intro w
    have h1 : ι (σ g w) = (Representation.ofMulAction ℂ G G) g (ι w) :=
      LinearMap.congr_fun (hι_equiv g) w
    have h2 := RepresentationTheory.SymmetricPowerRepresentations.asModuleHomToLinearMap_commutes s g (ι w)
    simp only [hΦ, LinearMap.comp_apply]
    exact (congrArg (⇑sLin) h1).trans h2

  obtain ⟨n, ψ, hψ_ne, hψ_equiv⟩ :=
    RepresentationTheory.SymmetricPowerRepresentations.exists_nonzero_component_intertwiner (fun n => RepresentationTheory.SymmetricPowerRepresentations.symmetricPowerRepresentation ρ n) σ Φ hΦ_ne hΦ_equiv
  exact ⟨n, ψ, hψ_ne, hψ_equiv⟩

end MainTheorem
