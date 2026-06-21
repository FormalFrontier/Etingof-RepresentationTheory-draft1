import Mathlib
import EtingofRepresentationTheory.Chapter5.CauchyCharacterRight

/-!
# Weight-space dimension of the right-`GL_N` polynomial representation `A_d`

This file computes the dimension of every torus weight space of the degree-`d`
homogeneous component `A_d = k[Xᵢⱼ]_d` under the right-`GL_N` action
(`polyRightDegreeFDRep`, `CauchyCharacterRight.lean`). This is sub-issue A of the
right-`GL_N` Cauchy character identity (#4944): the elementary, **weight-space
side**, requiring no Schur-Weyl theory.

The main result is

```
finrank k (glWeightSpace k N (polyRightDegreeFDRep k N d) μ)
  = if (∑ j, μ j) = d then ∏ j, Nat.choose (μ j + N - 1) (N - 1) else 0.
```

## Strategy

Every monomial `X^s` is a right-torus eigenvector
(`rTransAlgHom_diagonal_monomial`, `PolynomialGLRightAction.lean`): the diagonal
matrix `diagUnit k N i t` (which puts `t` at coordinate `i`, `1` elsewhere) scales
`X^s` by `t ^ (∑_l s (l, i))`, the `i`-th **column degree** of `s`. Hence the
weight space for `μ` is exactly the span of the degree-`d` monomials whose
column-degree vector is `μ`, and its dimension is the number of such monomials.
Choosing each column independently (stars and bars) gives
`∏_j C(μ_j + N − 1, N − 1)` monomials when `∑_j μ_j = d`, and none otherwise.
-/

namespace Etingof.CauchyWeightSpaceDimension

open _root_.MvPolynomial
open Etingof Etingof.PolynomialGLAction Etingof.PolyRightGrading
  Etingof.CauchyCharacterRight

variable {k : Type*} [Field k] {N : ℕ}

/-! ### The diagonal torus eigenvalue on a monomial -/

/-- The exponent product `∏_{(i',j')} (update 1 i t)_{j'}^{s(i',j')}` collapses to
the single power `t ^ (∑_l s(l,i))`: only the factors in column `i` carry `t`. -/
theorem prod_update_pow (i : Fin N) (t : kˣ) (s : (Fin N × Fin N) →₀ ℕ) :
    (s.prod fun p e => (Function.update (1 : Fin N → k) i (t : k)) p.2 ^ e)
      = (t : k) ^ (∑ l, s (l, i)) := by
  classical
  have key : ∀ p ∈ s.support,
      (Function.update (1 : Fin N → k) i (t : k)) p.2 ^ s p
        = (t : k) ^ (if p.2 = i then s p else 0) := by
    intro p _
    by_cases h : p.2 = i
    · rw [h, Function.update_self, if_pos rfl]
    · simp [h]
  rw [Finsupp.prod, Finset.prod_congr rfl key, Finset.prod_pow_eq_pow_sum]
  congr 1
  -- `∑ p ∈ support, (if p.2 = i then s p else 0) = ∑ l, s (l, i)`
  have hext : (∑ p ∈ s.support, (if p.2 = i then s p else 0))
      = ∑ p : Fin N × Fin N, (if p.2 = i then s p else 0) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp, ite_self]
  rw [hext, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ i (fun b => s (a, b))]
  simp

/-- **The diagonal torus acts on a monomial by its column-degree weight.** The
group element `diagUnit k N i t` scales `monomial s c` by `t ^ (∑_l s(l,i))`. -/
theorem polyRightRep_diagUnit_monomial (i : Fin N) (t : kˣ)
    (s : (Fin N × Fin N) →₀ ℕ) (c : k) :
    polyRightRep k N (diagUnit k N i t) (monomial s c)
      = (t : k) ^ (∑ l, s (l, i)) • monomial s c := by
  rw [polyRightRep_apply]
  show rTransAlgHom (Matrix.diagonal (Function.update 1 i (t : k))) (monomial s c) = _
  rw [rTransAlgHom_diagonal_monomial, prod_update_pow]

/-- **Coefficient extraction for the diagonal torus action.** Since `diagUnit k N i t`
acts diagonally in the monomial basis, the `s`-coefficient of `R_{diagUnit i t} x`
is the `s`-coefficient of `x` scaled by the eigenvalue `t ^ (∑_l s(l,i))`. -/
theorem coeff_polyRightRep_diagUnit (i : Fin N) (t : kˣ)
    (x : MvPolynomial (Fin N × Fin N) k) (s : (Fin N × Fin N) →₀ ℕ) :
    coeff s (polyRightRep k N (diagUnit k N i t) x)
      = (t : k) ^ (∑ l, s (l, i)) * coeff s x := by
  classical
  conv_lhs => rw [x.as_sum, map_sum]
  simp_rw [polyRightRep_diagUnit_monomial, coeff_sum, coeff_smul, coeff_monomial,
    smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' x.support s (fun s' => (t : k) ^ (∑ l, s' (l, i)) * coeff s' x)]
  split_ifs with hs
  · rfl
  · rw [notMem_support_iff.mp hs, mul_zero]

/-! ### The weight space as the span of column-degree-`μ` monomials -/

/-- The `k`-linear inclusion of the carrier `A_d` of `polyRightDegreeFDRep` into the
polynomial ring `k[Xᵢⱼ]`. It is the subtype map of the homogeneous component. -/
noncomputable def polyOf (d : ℕ) :
    polyRightDegreeFDRep k N d →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  (homogeneousSubmodule (Fin N × Fin N) k d).subtype

theorem polyOf_injective (d : ℕ) : Function.Injective (polyOf (k := k) (N := N) d) :=
  Subtype.coe_injective

theorem polyOf_mem (d : ℕ) (w : polyRightDegreeFDRep k N d) :
    polyOf d w ∈ homogeneousSubmodule (Fin N × Fin N) k d :=
  w.2

/-- The underlying polynomial of the right action on `A_d` is `polyRightRep`. -/
theorem polyOf_rho (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (w : polyRightDegreeFDRep k N d) :
    polyOf d ((polyRightDegreeFDRep k N d).ρ g w) = polyRightRep k N g (polyOf d w) :=
  rfl

variable [IsAlgClosed k]

/-- **Membership in the weight space, read on the underlying polynomial.** A vector
`w ∈ A_d` lies in the `μ`-weight space iff for every diagonal torus element the
right action multiplies `↑w` by the eigenvalue `t ^ μ i`. -/
theorem mem_glWeightSpace_polyRight_iff (d : ℕ) (μ : Fin N → ℕ)
    (w : polyRightDegreeFDRep k N d) :
    w ∈ glWeightSpace k N (polyRightDegreeFDRep k N d) μ
      ↔ ∀ (i : Fin N) (t : kˣ),
          polyRightRep k N (diagUnit k N i t) (polyOf d w)
            = (t : k) ^ μ i • polyOf d w := by
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun i => forall_congr' fun t => ?_
  rw [← polyOf_rho, ← map_smul]
  exact ⟨fun h => by rw [h], fun h => polyOf_injective d h⟩

end Etingof.CauchyWeightSpaceDimension
