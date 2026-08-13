/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib

/-!
# Indexed Coordinate Projections
-/

open Module (End)

namespace RepresentationTheory.Module.IndexedCoordinateProjections

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]
variable {A : Type*} [Ring A] [Algebra 𝕜 A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  [∀ i, Module 𝕜 (M i)] [∀ i, IsScalarTower 𝕜 A (M i)] [∀ i, Module.Finite 𝕜 (M i)]

/-- An auxiliary type associated with a type family indexed by `ι`. -/
abbrev AuxiliaryIndexedFamily (N : ι → Type*) : Type _ := ∀ i, N i

/-- The linear endomorphism selecting one coordinate of an indexed module family. -/
def coordinateProjection (j : ι) : AuxiliaryIndexedFamily M →ₗ[A] AuxiliaryIndexedFamily M :=
  (LinearMap.single A M j).comp (LinearMap.proj j)

omit [Fintype ι] in
/-- Selecting coordinate `j` retains only the `j`-th value of the indexed element. -/
@[simp]
theorem coordinateProjection_apply (j : ι) (x : AuxiliaryIndexedFamily M) :
    coordinateProjection (A := A) M j x = Pi.single j (x j) := by
  simp [coordinateProjection]

variable {M}

omit [Fintype ι] in
/-- An endomorphism of a pairwise non-equivalent family of simple modules sends a vector supported at one index to zero at every distinct index. -/
theorem linearMap_single_apply_eq_zero
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j)))
    (f : AuxiliaryIndexedFamily M →ₗ[A] AuxiliaryIndexedFamily M) {i k : ι} (hik : i ≠ k)
    (m : M i) :
    (f (Pi.single i m)) k = 0 := by
  haveI := hsimp i
  haveI := hsimp k
  let g : M i →ₗ[A] M k :=
    (LinearMap.proj k).comp (f.comp (LinearMap.single A M i))
  have hg : g = 0 := by
    rcases g.bijective_or_eq_zero with hbij | hz
    · exact absurd ⟨LinearEquiv.ofBijective g hbij⟩ (hdist hik)
    · exact hz
  have : g m = 0 := by rw [hg]; rfl
  simpa [g] using this

/-- A finitely indexed element is the sum of the single-coordinate elements formed from all of its values. -/
theorem sum_single_apply_eq (x : AuxiliaryIndexedFamily M) : ∑ i, Pi.single i (x i) = x := by
  funext k
  rw [Finset.sum_apply, Finset.sum_pi_single]
  simp

/-- Coordinate selection commutes pointwise with any linear endomorphism of a finite pairwise non-equivalent family of simple modules. -/
theorem coordinateProjection_commutes
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j)))
    (j : ι) (f : AuxiliaryIndexedFamily M →ₗ[A] AuxiliaryIndexedFamily M)
    (x : AuxiliaryIndexedFamily M) :
    coordinateProjection (A := A) M j (f x) = f (coordinateProjection (A := A) M j x) := by
  classical
  have ha : ∀ m : M j, f (Pi.single j m) = Pi.single j ((f (Pi.single j m)) j) := by
    intro m
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk]
      exact linearMap_single_apply_eq_zero hsimp hdist f (Ne.symm hk) m
  have hb : (f x) j = (f (Pi.single j (x j))) j := by
    conv_lhs => rw [← sum_single_apply_eq x]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_eq_single j ?_ ?_
    · intro i _ hij
      exact linearMap_single_apply_eq_zero hsimp hdist f hij (x i)
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [coordinateProjection_apply, coordinateProjection_apply, ha (x j), hb]

variable (M)

omit [∀ i, Module.Finite 𝕜 (M i)] in
/-- For a finite pairwise non-equivalent family of simple modules, an algebra element acts as the identity on one selected member and as zero on every other member. -/
theorem exists_smul_eq_ite (hfin : ∀ i, Module.Finite 𝕜 (M i))
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j)))
    (j : ι) :
    ∃ a : A, ∀ (i : ι) (v : M i), a • v = if i = j then v else (0 : M i) := by
  classical
  haveI : ∀ i, IsSimpleModule A (M i) := hsimp
  haveI : ∀ i, IsSemisimpleModule A (M i) := fun i => inferInstance
  haveI : ∀ i, Module.Finite 𝕜 (M i) := hfin
  haveI : Module.Finite (End A (AuxiliaryIndexedFamily M)) (AuxiliaryIndexedFamily M) :=
    Module.Finite.of_restrictScalars_finite 𝕜 (End A (AuxiliaryIndexedFamily M))
      (AuxiliaryIndexedFamily M)
  let P : End (End A (AuxiliaryIndexedFamily M)) (AuxiliaryIndexedFamily M) :=
    { toFun := coordinateProjection (A := A) M j
      map_add' := (coordinateProjection (A := A) M j).map_add
      map_smul' := by
        intro f x
        simp only [RingHom.id_apply, Module.End.smul_def]
        exact coordinateProjection_commutes hsimp hdist j f x }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := A)
      (M := AuxiliaryIndexedFamily M) P
  refine ⟨a, fun i v => ?_⟩
  have key : ∀ x : AuxiliaryIndexedFamily M, a • x = coordinateProjection (A := A) M j x :=
    fun x => DFunLike.congr_fun ha x
  have h1 := congrFun (key (Pi.single i v)) i
  rw [coordinateProjection_apply] at h1
  rw [Pi.smul_apply, Pi.single_eq_same] at h1
  rw [h1]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij, Pi.single_eq_of_ne hij]

/-- The algebra homomorphism sending an algebra element to its scalar action on one member of an indexed module family. -/
def scalarActionAlgHom (i : ι) : A →ₐ[𝕜] Module.End 𝕜 (M i) := Algebra.lsmul 𝕜 𝕜 (M i)

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite 𝕜 (M i)] in
/-- Evaluating the scalar-action algebra homomorphism on an element and a vector agrees with scalar multiplication. -/
@[simp]
theorem scalarActionAlgHom_apply (i : ι) (a : A) (v : M i) :
    (scalarActionAlgHom M i a : M i →ₗ[𝕜] M i) v = a • v := rfl

/-- The linear functional on the algebra obtained from one member of an indexed module family. -/
def moduleTraceLinearMap (i : ι) : A →ₗ[𝕜] 𝕜 :=
  (LinearMap.trace 𝕜 (M i)).comp (scalarActionAlgHom M i).toLinearMap

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite 𝕜 (M i)] in
/-- The module trace functional evaluates an algebra element as the trace of its scalar-action endomorphism. -/
@[simp]
theorem moduleTraceLinearMap_apply (i : ι) (a : A) :
    moduleTraceLinearMap M i a = LinearMap.trace 𝕜 (M i) (scalarActionAlgHom M i a) := rfl

omit [DecidableEq ι] in
/-- The trace functionals of a finite pairwise non-equivalent family of finite-dimensional simple modules are linearly independent in characteristic zero. -/
theorem linearIndependent_moduleTraceLinearMap [CharZero 𝕜]
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j))) :
    LinearIndependent 𝕜 (fun i => (moduleTraceLinearMap M i : A →ₗ[𝕜] 𝕜)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  obtain ⟨a, ha⟩ := exists_smul_eq_ite (𝕜 := 𝕜) M (fun _ => inferInstance) hsimp hdist j
  have hact : ∀ i, (scalarActionAlgHom M i a : M i →ₗ[𝕜] M i) =
      if i = j then LinearMap.id else 0 := by
    intro i
    ext v
    rw [scalarActionAlgHom_apply]
    by_cases hij : i = j <;> simp [hij, ha i v]
  have htrace : ∀ i, moduleTraceLinearMap M i a =
      if i = j then (Module.finrank 𝕜 (M i) : 𝕜) else 0 := by
    intro i
    rw [moduleTraceLinearMap_apply, hact i]
    by_cases hij : i = j <;> simp [hij, LinearMap.trace_id]
  have happ : (∑ i, g i • (moduleTraceLinearMap M i : A →ₗ[𝕜] 𝕜)) a = 0 := by rw [hg]; rfl
  rw [LinearMap.sum_apply] at happ
  simp only [LinearMap.smul_apply, htrace, smul_eq_mul, mul_ite, mul_zero] at happ
  rw [Finset.sum_ite_eq' Finset.univ j] at happ
  simp only [Finset.mem_univ, if_true] at happ
  haveI := (hsimp j).nontrivial
  have hdim : (Module.finrank 𝕜 (M j) : 𝕜) ≠ 0 := by
    have : 0 < Module.finrank 𝕜 (M j) := Module.finrank_pos
    exact_mod_cast this.ne'
  exact (mul_eq_zero.mp happ).resolve_right hdim

end

end RepresentationTheory.Module.IndexedCoordinateProjections
