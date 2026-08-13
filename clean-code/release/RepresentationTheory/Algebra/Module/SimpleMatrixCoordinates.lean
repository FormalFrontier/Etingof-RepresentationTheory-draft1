/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.Algebra.Module.IsotypicDecomposition

/-!
# Matrix coordinates for simple modules
-/

open scoped DirectSum

namespace RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates

section General

variable {A : Type*} [Ring A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, IsSimpleModule A (V i)]

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- A submodule of the displayed direct sum is equivalent to one with bounded multiplicities. -/
@[source_ref "Chapter3/Remark3.1.5" (role := primary)]
theorem exists_equiv_directSum_fin (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (⨁ i, (Fin (n i) → V i))) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (↥W ≃ₗ[A] ⨁ i, (Fin (r i) → V i)) :=
  RepresentationTheory.Algebra.Module.IsotypicDecomposition.exists_equiv_directSum_fin n hd W

end General

section Matrix

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V]

/-- An additive equivalence between linear maps of finite function modules and matrices of module endomorphisms. -/
@[source_ref "Chapter3/Remark3.1.5" (role := primary)]
def linearMapAddEquivMatrix (r n : ℕ) :
    ((Fin r → V) →ₗ[A] (Fin n → V)) ≃+ Matrix (Fin r) (Fin n) (Module.End A V) where
  toFun f i j :=
    { toFun := fun x => f (Pi.single i x) j
      map_add' := fun x y => by simp [Pi.single_add]
      map_smul' := fun a x => by simp [Pi.single_smul] }
  invFun X :=
    { toFun := fun v j => ∑ i, X i j (v i)
      map_add' := fun v w => by ext j; simp [Finset.sum_add_distrib]
      map_smul' := fun a v => by ext j; simp [Finset.smul_sum] }
  left_inv f := by
    refine LinearMap.ext fun v => funext fun j => ?_
    change ∑ i, f (Pi.single i (v i)) j = f v j
    rw [← Fintype.sum_apply j (fun i => f (Pi.single i (v i))), ← map_sum,
      Finset.univ_sum_single]
  right_inv X := by
    ext i j x
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i]
    · simp [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  map_add' f g := by ext i j x; simp

/-- A matrix entry of a linear map is its value on the corresponding single-coordinate input. -/
@[source_ref "Chapter3/Remark3.1.5" (role := supporting), simp]
theorem linearMapAddEquivMatrix_apply (r n : ℕ)
    (f : (Fin r → V) →ₗ[A] (Fin n → V))
    (i : Fin r) (j : Fin n) (x : V) :
    linearMapAddEquivMatrix r n f i j x = f (Pi.single i x) j := rfl

/-- The inverse matrix equivalence acts by the displayed sum of matrix entries. -/
@[simp] theorem linearMapAddEquivMatrix_symm_apply (r n : ℕ)
    (X : Matrix (Fin r) (Fin n) (Module.End A V)) (v : Fin r → V) (j : Fin n) :
    (linearMapAddEquivMatrix r n).symm X v j = ∑ i, X i j (v i) := rfl

/-- A linear map between finite function modules is the sum of its displayed matrix entries applied to the input coordinates. -/
theorem apply_eq_sum_matrixEntries (r n : ℕ) (f : (Fin r → V) →ₗ[A] (Fin n → V))
    (w : Fin r → V) (j : Fin n) :
    f w j = ∑ i, linearMapAddEquivMatrix r n f i j (w i) := by
  conv_lhs => rw [← (linearMapAddEquivMatrix r n).symm_apply_apply f]
  rw [linearMapAddEquivMatrix_symm_apply]

end Matrix

section Injective

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V] [IsSimpleModule A V]

/-- For finite function modules over a simple module, injectivity is characterized by vanishing composites. -/
theorem injective_iff_comp_eq_zero (r n : ℕ) (f : (Fin r → V) →ₗ[A] (Fin n → V)) :
    Function.Injective f ↔
      ∀ g : V →ₗ[A] (Fin r → V), f ∘ₗ g = 0 → g = 0 := by
  constructor
  · intro hf g hg
    refine LinearMap.ext fun v => hf ?_
    have := LinearMap.congr_fun hg v
    simpa using this
  · intro H
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    obtain ⟨S, hSle, hSsimple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le (LinearMap.ker f)).resolve_left hne
    haveI := hSsimple
    obtain ⟨e⟩ :=
      RepresentationTheory.Algebra.Module.IsotypicDecomposition.isIsotypicOfType_fin_fun r S
    set g : V →ₗ[A] (Fin r → V) := S.subtype ∘ₗ (e.symm : V →ₗ[A] ↥S) with hg
    have hfg : f ∘ₗ g = 0 := by
      refine LinearMap.ext fun v => ?_
      have hmem : ((e.symm v : ↥S) : Fin r → V) ∈ LinearMap.ker f := hSle (e.symm v).2
      simpa [hg] using LinearMap.mem_ker.mp hmem
    have hg0 := H g hfg
    have hinj : Function.Injective g :=
      S.subtype_injective.comp (e.symm.injective)
    haveI : Nontrivial V := IsSimpleModule.nontrivial A V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hinj (by rw [hg0]; simp))

/-- For finite function modules over a simple module, injectivity is characterized by the displayed matrix relation. -/
@[source_ref "Chapter3/Remark3.1.5" (role := supporting)]
theorem injective_iff_matrix_relation (r n : ℕ)
    (f : (Fin r → V) →ₗ[A] (Fin n → V)) :
    Function.Injective f ↔
      ∀ c : Fin r → Module.End A V,
        (∀ j, ∑ i, linearMapAddEquivMatrix r n f i j * c i = 0) → ∀ i, c i = 0 := by
  rw [injective_iff_comp_eq_zero]
  constructor
  · intro H c hc
    have hg : f ∘ₗ LinearMap.pi c = 0 := by
      refine LinearMap.ext fun v => funext fun j => ?_
      have : f (LinearMap.pi c v) j = ∑ i, linearMapAddEquivMatrix r n f i j (c i v) := by
        rw [apply_eq_sum_matrixEntries]; simp [LinearMap.pi_apply]
      rw [LinearMap.comp_apply, this]
      have h0 := LinearMap.congr_fun (hc j) v
      simpa [LinearMap.sum_apply, Module.End.mul_apply] using h0
    have := H _ hg
    intro i
    have := congrArg (fun g : V →ₗ[A] (Fin r → V) => LinearMap.proj i ∘ₗ g) this
    simpa [LinearMap.proj_pi] using this
  · intro H g hg
    set c : Fin r → Module.End A V := fun i => LinearMap.proj i ∘ₗ g with hc
    have hcsum : ∀ j, ∑ i, linearMapAddEquivMatrix r n f i j * c i = 0 := by
      intro j
      refine LinearMap.ext fun v => ?_
      have hfg := LinearMap.congr_fun hg v
      have : (∑ i, linearMapAddEquivMatrix r n f i j * c i) v
          = ∑ i, linearMapAddEquivMatrix r n f i j (g v i) := by
        simp [LinearMap.sum_apply, Module.End.mul_apply, hc]
      rw [this, ← apply_eq_sum_matrixEntries]
      simpa using congrFun hfg j
    have hc0 := H c hcsum
    refine LinearMap.ext fun v => funext fun i => ?_
    have := hc0 i
    have h2 := LinearMap.congr_fun this v
    simpa [hc, LinearMap.proj_apply] using h2

omit [IsSimpleModule A V] in
/-- Linear independence of a matrix of endomorphisms is characterized by the displayed matrix relation. -/
@[source_ref "Chapter3/Remark3.1.5" (role := supporting)]
theorem linearIndependent_iff_matrix_relation (r n : ℕ)
    (X : Matrix (Fin r) (Fin n) (Module.End A V)) :
    LinearIndependent (Module.End A V)ᵐᵒᵖ X ↔
      ∀ c : Fin r → Module.End A V, (∀ j, ∑ i, X i j * c i = 0) → ∀ i, c i = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro H c hc i
    have hsum : (∑ i, MulOpposite.op (c i) • X i) = 0 := by
      funext j
      have := hc j
      simpa [Finset.sum_apply] using this
    simpa using H (fun i => MulOpposite.op (c i)) hsum i
  · intro H c hc i
    have hsum : ∀ j, ∑ i, X i j * (c i).unop = 0 := by
      intro j
      have := congrFun hc j
      simpa [Finset.sum_apply] using this
    have := H (fun i => (c i).unop) hsum i
    exact MulOpposite.unop_injective (by simpa using this)

end Injective

section Blocks

variable {A : Type*} [Ring A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, IsSimpleModule A (V i)]

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- A submodule of the displayed direct sum admits bounded multiplicities and injective coordinate data. -/
@[source_ref "Chapter3/Discussion_after_Lemma3.1.6/Derived4" (role := supporting),
  source_ref "Chapter3/Proposition3.1.4" (role := primary),
  source_ref "Chapter3/Remark3.1.5" (role := primary)]
theorem exists_injective_coordinates_directSum (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (⨁ i, (Fin (n i) → V i))) :
    ∃ (r : ι → ℕ) (φ : ∀ i, (Fin (r i) → V i) →ₗ[A] (Fin (n i) → V i))
      (e : ↥W ≃ₗ[A] ⨁ i, (Fin (r i) → V i)),
      (∀ i, r i ≤ n i) ∧
      (∀ i, Function.Injective (φ i)) ∧
      (∀ i, LinearIndependent (Module.End A (V i))ᵐᵒᵖ
        (linearMapAddEquivMatrix (r i) (n i) (φ i))) ∧
      ∀ (w : ↥W) (i : ι), (w : ⨁ k, (Fin (n k) → V k)) i = φ i (e w i) := by
  obtain ⟨r, X, e, hr, hli, hform⟩ :=
    RepresentationTheory.Algebra.Module.IsotypicDecomposition.exists_linearIndependent_coordinates_directSum
      n hd W
  refine ⟨r, fun i => (linearMapAddEquivMatrix (r i) (n i)).symm (X i), e, hr, ?_, ?_, ?_⟩
  · intro i
    rw [injective_iff_matrix_relation, ← linearIndependent_iff_matrix_relation]
    simpa using hli i
  · intro i
    simpa using hli i
  · intro w i
    funext l
    rw [hform w i]
    exact (linearMapAddEquivMatrix_symm_apply (r i) (n i) (X i) (e w i) l).symm

end Blocks

section DivisionRing

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V]
  [IsSimpleModule A V]

/-- The endomorphism ring of a simple module admits a division ring structure. -/
@[source_ref "Chapter3/Remark3.1.5" (role := primary)]
theorem nonempty_divisionRing_end : Nonempty (DivisionRing (Module.End A V)) := by
  classical exact ⟨inferInstance⟩

end DivisionRing

end RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates
