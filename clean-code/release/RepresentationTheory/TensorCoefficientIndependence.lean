/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Representation.AlgebraDensity
import RepresentationTheory.Module.IndexedCoordinateProjections

/-!
# Tensor Coefficient Independence
-/

open scoped TensorProduct
open Module (End)

namespace RepresentationTheory.TensorCoefficientIndependence

noncomputable section

variable {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G]
variable {ι : Type*} [Fintype ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, Module.Finite k (V i)]
variable (ρ : ∀ i, Representation k G (V i))

omit [IsAlgClosed k] [∀ i, Module.Finite k (V i)] in
private theorem sum_contractions_eq_zero_monoidAlgebra
    (z : ∀ i, Module.Dual k (V i) ⊗[k] V i)
    (hz : ∀ g : G, ∑ i, contractLeft k (V i)
      (TensorProduct.map LinearMap.id (ρ i g) (z i)) = 0)
    (b : MonoidAlgebra k G) :
    ∑ i, contractLeft k (V i)
      (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom b) (z i)) = 0 := by
  induction b using MonoidAlgebra.induction_on with
  | hM g =>
    simp only [Representation.asAlgebraHom_of]
    exact hz g
  | hadd f₁ f₂ h₁ h₂ =>
    have step : ∀ i, contractLeft k (V i)
        (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom (f₁ + f₂)) (z i))
      = contractLeft k (V i) (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom f₁) (z i))
        + contractLeft k (V i) (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom f₂) (z i)) := by
      intro i
      rw [map_add, TensorProduct.map_add_right, LinearMap.add_apply, map_add]
    simp only [step]
    rw [Finset.sum_add_distrib, h₁, h₂, add_zero]
  | hsmul r f h =>
    have step : ∀ i, contractLeft k (V i)
        (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom (r • f)) (z i))
      = r • contractLeft k (V i) (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom f) (z i)) := by
      intro i
      rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul]
    simp only [step]
    rw [← Finset.smul_sum, h, smul_zero]

/-- For a finite pairwise nonisomorphic family of simple representations, if the sum of the contracted tensor coefficients vanishes at every monoid element, then every tensor is zero. -/
theorem tensor_eq_zero_of_sum_contractions_eq_zero
    (hsimp : ∀ i, IsSimpleModule (MonoidAlgebra k G) (ρ i).asModule)
    (hdist : Pairwise (fun i j =>
      ¬ Nonempty ((ρ i).asModule ≃ₗ[MonoidAlgebra k G] (ρ j).asModule)))
    (z : ∀ i, Module.Dual k (V i) ⊗[k] V i)
    (hz : ∀ g : G, ∑ i, contractLeft k (V i)
      (TensorProduct.map LinearMap.id (ρ i g) (z i)) = 0)
    (j : ι) : z j = 0 := by
  classical
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra k G) (ρ i).asModule := hsimp
  obtain ⟨a, ha⟩ := RepresentationTheory.Module.IndexedCoordinateProjections.exists_smul_eq_ite
    (𝕜 := k) (A := MonoidAlgebra k G) (fun i => (ρ i).asModule)
    (fun _ => inferInstance) hsimp hdist j
  have hsep : ∀ i (w : V i),
      (ρ i).asAlgebraHom a w = if i = j then w else (0 : V i) := by
    intro i w
    have hkey := congrArg (ρ i).asModuleEquiv (ha i ((ρ i).asModuleEquiv.symm w))
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] at hkey
    by_cases hij : i = j
    · subst hij; simpa using hkey
    · rw [if_neg hij] at hkey ⊢; simpa using hkey
  have hAj : (ρ j).asAlgebraHom a = 1 := by
    ext w; rw [hsep j w, if_pos rfl]; rfl
  have hAi : ∀ i, i ≠ j → (ρ i).asAlgebraHom a = 0 := by
    intro i hij; ext w; rw [hsep i w, if_neg hij]; rfl
  have hzj : ∀ g : G, contractLeft k (V j)
      (TensorProduct.map LinearMap.id (ρ j g) (z j)) = 0 := by
    intro g
    have hoff : ∀ i ∈ Finset.univ, i ≠ j → contractLeft k (V i)
        (TensorProduct.map LinearMap.id
          ((ρ i).asAlgebraHom (a * MonoidAlgebra.of k G g)) (z i)) = 0 := by
      intro i _ hij
      rw [map_mul, hAi i hij, zero_mul]
      simp
    have hext := sum_contractions_eq_zero_monoidAlgebra ρ z hz
      (a * MonoidAlgebra.of k G g)
    rw [Finset.sum_eq_single j hoff
      (fun h => absurd (Finset.mem_univ j) h)] at hext
    rw [map_mul, Representation.asAlgebraHom_of, hAj, one_mul] at hext
    exact hext
  haveI := hsimp j
  exact
    RepresentationTheory.Representation.AlgebraDensity.eq_zero_of_contractLeft_representation_map_eq_zero
      (ρ j) (z j) hzj

/-- For simple representations that are pairwise nonisomorphic on a finite set, vanishing of the summed contracted tensor coefficients forces every tensor indexed by that set to vanish. -/
theorem tensor_eq_zero_on_finset_of_sum_contractions_eq_zero {Λ : Type*}
    (V : Λ → Type*) [∀ lam, AddCommGroup (V lam)] [∀ lam, Module k (V lam)]
    [∀ lam, Module.Finite k (V lam)]
    (ρ : ∀ lam, Representation k G (V lam))
    (s : Finset Λ)
    (hsimp : ∀ lam, IsSimpleModule (MonoidAlgebra k G) (ρ lam).asModule)
    (hdist : ∀ lam ∈ s, ∀ mu ∈ s, lam ≠ mu →
      ¬ Nonempty ((ρ lam).asModule ≃ₗ[MonoidAlgebra k G] (ρ mu).asModule))
    (z : ∀ lam, Module.Dual k (V lam) ⊗[k] V lam)
    (hz : ∀ g : G, ∑ lam ∈ s, contractLeft k (V lam)
      (TensorProduct.map LinearMap.id (ρ lam g) (z lam)) = 0)
    (lam : Λ) (hlam : lam ∈ s) : z lam = 0 :=
  tensor_eq_zero_of_sum_contractions_eq_zero (k := k) (G := G) (ι := {lam // lam ∈ s})
    (fun i => ρ i.1)
    (fun i => hsimp i.1)
    (fun i j hij => hdist i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)))
    (fun i => z i.1)
    (fun g => by
      rw [Finset.sum_coe_sort s (fun lam => contractLeft k (V lam)
        (TensorProduct.map LinearMap.id (ρ lam g) (z lam)))]
      exact hz g)
    ⟨lam, hlam⟩

end

end RepresentationTheory.TensorCoefficientIndependence
