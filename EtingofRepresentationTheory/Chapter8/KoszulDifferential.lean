import EtingofRepresentationTheory.Chapter8.KoszulContraction
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The Koszul differential `d : SV ⊗ ⋀ⁱ⁺¹ V → SV ⊗ ⋀ⁱ V` of Problem 8.2.10

Problem 8.2.10(i) sets `Cᵢ = SV ⊗ ⋀ⁱ V`, views it as the space of polynomial functions on `V*`
with values in `⋀ⁱ V`, and defines `dᵢ(f)(u) = ιᵤ (f u)`. Written algebraically, and in terms of a
basis `x₁, …, x_n` of `V` with dual basis `x₁*, …, x_n*`, that differential is

`d = ∑ₐ (multiplication by xₐ) ⊗ ι_{xₐ*}`.

This file constructs `d` in that form and proves `d ∘ d = 0`. The proof is exactly the interplay
the contraction file (`Chapter8/KoszulContraction.lean`) was built for: in the double sum
`∑_{a,c} (xₐ x_c) ⊗ (ι_a ι_c)` the symmetric-algebra factors commute while the contractions
anticommute, so off-diagonal terms cancel in pairs and diagonal terms vanish outright. The
cancellation is done with `Finset.sum_ninvolution`, so the argument is characteristic-free (a
`2 • S = 0` argument would fail in characteristic 2).

## Main definitions

* `Etingof.koszulX k V i` — the degree-`i` term `SV ⊗[k] ⋀ⁱ V`, an `SV`-module.
* `Etingof.koszulD b i : koszulX k V (i + 1) →ₗ[SV] koszulX k V i` — the differential, for a
  chosen finite basis `b` of `V`.

## Main results

* `Etingof.koszulD_tmul` — the value of `d` on an elementary tensor.
* `Etingof.koszulD_comp_koszulD` — `d ∘ d = 0`.
* `Etingof.koszulComplex b : ChainComplex (ModuleCat SV) ℕ` — the assembled complex.

Exactness of the resulting complex (the "free resolution of `k`" half of Problem 8.2.10(i)) is
not proved here.
-/

universe u v w

open scoped TensorProduct

namespace Etingof

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]
variable {κ : Type w} [Fintype κ]

variable (k V) in
/-- The degree-`i` term `Cᵢ = SV ⊗ ⋀ⁱ V` of the Koszul complex, as an `SV`-module (the symmetric
algebra acts on the left factor). -/
abbrev koszulX (i : ℕ) : Type max u v :=
  SymmetricAlgebra k V ⊗[k] (⋀[k]^i V)

/-- **The Koszul differential.** For a finite basis `b` of `V`,
`d = ∑ₐ (multiplication by b a) ⊗ ι_{b a *}`, the algebraic form of the book's
`dᵢ(f)(u) = ιᵤ (f u)`. -/
noncomputable def koszulD (b : Module.Basis κ k V) (i : ℕ) :
    koszulX k V (i + 1) →ₗ[SymmetricAlgebra k V] koszulX k V i :=
  ∑ a : κ, TensorProduct.AlgebraTensorModule.map
    (LinearMap.mulLeft (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V (b a)))
    (exteriorContraction k (b.coord a) i)

@[simp]
theorem koszulD_tmul (b : Module.Basis κ k V) (i : ℕ) (s : SymmetricAlgebra k V)
    (w : ⋀[k]^(i + 1) V) :
    koszulD b i (s ⊗ₜ[k] w) =
      ∑ a : κ, (SymmetricAlgebra.ι k V (b a) * s) ⊗ₜ[k] exteriorContraction k (b.coord a) i w := by
  simp [koszulD]

omit [Fintype κ] in
/-- A single summand of `d ∘ d`: contracting twice and multiplying by two basis vectors. -/
private noncomputable def koszulDD (b : Module.Basis κ k V) (i : ℕ) (p : κ × κ) :
    koszulX k V (i + 2) →ₗ[SymmetricAlgebra k V] koszulX k V i :=
  (TensorProduct.AlgebraTensorModule.map
      (LinearMap.mulLeft (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V (b p.1)))
      (exteriorContraction k (b.coord p.1) i)).comp
    (TensorProduct.AlgebraTensorModule.map
      (LinearMap.mulLeft (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V (b p.2)))
      (exteriorContraction k (b.coord p.2) (i + 1)))

omit [Fintype κ] in
private theorem koszulDD_tmul (b : Module.Basis κ k V) (i : ℕ) (p : κ × κ)
    (s : SymmetricAlgebra k V) (w : ⋀[k]^(i + 2) V) :
    koszulDD b i p (s ⊗ₜ[k] w) =
      (SymmetricAlgebra.ι k V (b p.1) * (SymmetricAlgebra.ι k V (b p.2) * s)) ⊗ₜ[k]
        exteriorContraction k (b.coord p.1) i
          (exteriorContraction k (b.coord p.2) (i + 1) w) := by
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
      rw [exteriorContraction_comm (u := b.coord p.1) (u' := b.coord p.2),
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

/-- **The Koszul differential squares to zero.** -/
theorem koszulD_comp_koszulD (b : Module.Basis κ k V) (i : ℕ) :
    (koszulD b i).comp (koszulD b (i + 1)) = 0 := by
  have hsum : (koszulD b i).comp (koszulD b (i + 1)) = ∑ p : κ × κ, koszulDD b i p := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, koszulD, koszulDD, LinearMap.sum_apply, map_sum]
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

/-- **The Koszul complex** `C_• : ⋯ → SV ⊗ ⋀² V → SV ⊗ ⋀¹ V → SV ⊗ ⋀⁰ V` of
Problem 8.2.10(i), as a chain complex of `SV`-modules. Exactness (equivalently, that the
augmentation `C₀ = SV → k` makes this a free resolution of `k`) is not proved here. -/
noncomputable def koszulComplex (b : Module.Basis κ k V) :
    ChainComplex (ModuleCat.{max u v} (SymmetricAlgebra k V)) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of _ (koszulX k V i))
    (fun i => ModuleCat.ofHom (koszulD b i))
    (fun i => by
      apply ModuleCat.hom_ext
      exact koszulD_comp_koszulD b i)

@[simp]
theorem koszulComplex_X (b : Module.Basis κ k V) (i : ℕ) :
    (koszulComplex b).X i = ModuleCat.of _ (koszulX k V i) :=
  rfl

theorem koszulComplex_d (b : Module.Basis κ k V) (i : ℕ) :
    (koszulComplex b).d (i + 1) i = ModuleCat.ofHom (koszulD b i) :=
  by simp [koszulComplex]

end Etingof
