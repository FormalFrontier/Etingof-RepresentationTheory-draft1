/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# A basis-indexed symmetric-algebra chain complex
-/

universe u v w

open scoped TensorProduct

namespace RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]
variable {κ : Type w} [Fintype κ]

variable (k V) in
/-- The type assigned to each natural-number degree for a module over a commutative ring. -/
abbrev degreeIndexedType (i : ℕ) : Type max u v :=
  SymmetricAlgebra k V ⊗[k] (⋀[k]^i V)

/-- The linear map from degree i + 1 to degree i determined by a finite module basis. -/
noncomputable def basisSymmetricAlgebraComplexDifferential (b : Module.Basis κ k V) (i : ℕ) :
    degreeIndexedType k V (i + 1) →ₗ[SymmetricAlgebra k V] degreeIndexedType k V i :=
  ∑ a : κ, TensorProduct.AlgebraTensorModule.map
    (LinearMap.mulLeft (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V (b a)))
    (RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction
      k (b.coord a) i)

/-- The differential on a pure tensor is expressed as a finite sum over the given basis. -/
@[simp]
theorem basisSymmetricAlgebraComplexDifferential_tmul (b : Module.Basis κ k V) (i : ℕ)
    (s : SymmetricAlgebra k V) (w : ⋀[k]^(i + 1) V) :
    basisSymmetricAlgebraComplexDifferential b i (s ⊗ₜ[k] w) =
      ∑ a : κ, (SymmetricAlgebra.ι k V (b a) * s) ⊗ₜ[k]
        RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction
          k (b.coord a) i w := by
  simp [basisSymmetricAlgebraComplexDifferential]

omit [Fintype κ] in
private noncomputable def koszulDD (b : Module.Basis κ k V) (i : ℕ) (p : κ × κ) :
    degreeIndexedType k V (i + 2) →ₗ[SymmetricAlgebra k V] degreeIndexedType k V i :=
  (TensorProduct.AlgebraTensorModule.map
      (LinearMap.mulLeft (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V (b p.1)))
      (RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction
        k (b.coord p.1) i)).comp
    (TensorProduct.AlgebraTensorModule.map
      (LinearMap.mulLeft (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V (b p.2)))
      (RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction
        k (b.coord p.2) (i + 1)))

omit [Fintype κ] in
private theorem koszulDD_tmul (b : Module.Basis κ k V) (i : ℕ) (p : κ × κ)
    (s : SymmetricAlgebra k V) (w : ⋀[k]^(i + 2) V) :
    koszulDD b i p (s ⊗ₜ[k] w) =
      (SymmetricAlgebra.ι k V (b p.1) * (SymmetricAlgebra.ι k V (b p.2) * s)) ⊗ₜ[k]
        RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction
          k (b.coord p.1) i
            (RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction
              k (b.coord p.2) (i + 1) w) := by
  simp [koszulDD]

omit [Fintype κ] in
private theorem koszulDD_swap_add (b : Module.Basis κ k V) (i : ℕ) (p : κ × κ) :
    koszulDD b i p + koszulDD b i p.swap = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.zero_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
      rw [koszulDD_tmul, koszulDD_tmul]
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction_anticommute
          (u := b.coord p.1) (u' := b.coord p.2),
        TensorProduct.tmul_neg,
        show SymmetricAlgebra.ι k V (b p.2) * (SymmetricAlgebra.ι k V (b p.1) * s) =
          SymmetricAlgebra.ι k V (b p.1) * (SymmetricAlgebra.ι k V (b p.2) * s) by ring]
      exact neg_add_cancel _
  | add x y hx hy => rw [map_add, map_add, add_add_add_comm, hx, hy, add_zero]

omit [Fintype κ] in
private theorem koszulDD_diag (b : Module.Basis κ k V) (i : ℕ) (a : κ) :
    koszulDD b i (a, a) = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.zero_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w => rw [koszulDD_tmul]; simp
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- Two consecutive degree-lowering linear maps compose to zero. -/
theorem basisSymmetricAlgebraComplexDifferential_comp (b : Module.Basis κ k V) (i : ℕ) :
    (basisSymmetricAlgebraComplexDifferential b i).comp
      (basisSymmetricAlgebraComplexDifferential b (i + 1)) = 0 := by
  have hsum : (basisSymmetricAlgebraComplexDifferential b i).comp
      (basisSymmetricAlgebraComplexDifferential b (i + 1)) = ∑ p : κ × κ, koszulDD b i p := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, basisSymmetricAlgebraComplexDifferential, koszulDD,
      LinearMap.sum_apply, map_sum]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    exact Finset.sum_comm
  rw [hsum]
  refine Finset.sum_ninvolution Prod.swap (fun p => koszulDD_swap_add b i p) ?_
    (fun _ => Finset.mem_univ _) (fun p => Prod.swap_swap p)
  intro p hp hswap
  refine hp ?_
  have : p.1 = p.2 := congrArg Prod.snd hswap
  rw [show p = (p.1, p.1) from Prod.ext rfl this.symm]
  exact koszulDD_diag b i p.1

/-- The natural-number-indexed chain complex over a symmetric algebra attached to a finite module basis. -/
noncomputable def basisSymmetricAlgebraComplex (b : Module.Basis κ k V) :
    ChainComplex (ModuleCat.{max u v} (SymmetricAlgebra k V)) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of _ (degreeIndexedType k V i))
    (fun i => ModuleCat.ofHom (basisSymmetricAlgebraComplexDifferential b i))
    (fun i => by
      apply ModuleCat.hom_ext
      exact basisSymmetricAlgebraComplexDifferential_comp b i)

/-- The degree i object of the basis-indexed symmetric-algebra chain complex. -/
@[simp]
theorem basisSymmetricAlgebraComplex_X (b : Module.Basis κ k V) (i : ℕ) :
    (basisSymmetricAlgebraComplex b).X i = ModuleCat.of _ (degreeIndexedType k V i) :=
  rfl

/-- The differential from degree i + 1 to degree i in the basis-indexed chain complex. -/
theorem basisSymmetricAlgebraComplex_d (b : Module.Basis κ k V) (i : ℕ) :
    (basisSymmetricAlgebraComplex b).d (i + 1) i =
      ModuleCat.ofHom (basisSymmetricAlgebraComplexDifferential b i) :=
  by simp [basisSymmetricAlgebraComplex]

end RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex
