import Mathlib

/-!
# Problem 6.1.1: Field embeddings

> Let `f : k[x₁,…,x_n] → k(y₁,…,y_m)` be an injective `k`-algebra homomorphism.
> Show that `m ≥ n`. Deduce that if `f : k(x₁,…,x_n) → k(y₁,…,y_m)` is a `k`-linear
> field embedding, then `m ≥ n`.

The book hints at the growth of `dim W_N` (polynomials of degree `≤ N`) under `f`.
The modern statement of that growth argument is exactly the transcendence-degree
inequality: an injective `k`-algebra map out of `k[x₁,…,x_n]` cannot lower the
number of algebraically independent elements. The images `f(xᵢ)` are
algebraically independent over `k` (Mathlib's `MvPolynomial.algebraicIndependent_X`
transported across the injection by `AlgebraicIndependent.map'`), so

`n = trdeg k k[x₁,…,x_n] ≤ trdeg k L`

for any domain `L` receiving an injection (`trdeg_le_of_injective`). Specialising
`L` to a field of transcendence degree `m` gives `n ≤ m`.

`k(y₁,…,y_m)` is modelled as `FractionRing (MvPolynomial (Fin m) k)`. Its
transcendence degree over `k` is `m`: the fraction field is algebraic over the
polynomial ring (`IsLocalization.isAlgebraic`, so `trdeg = 0` there), and the
tower formula `trdeg_add_eq` together with `MvPolynomial.trdeg_of_isDomain`
collapses to `m`.

All carriers are pinned to `Type` so that the index type `Fin n` and the
codomain live in the same universe, as required by `cardinalMk_le_trdeg`.
-/

open MvPolynomial Cardinal

namespace Etingof

variable {k : Type} [Field k]

/-- The transcendence degree of `k(y₁,…,y_m) = FractionRing (k[y₁,…,y_m])` over
`k` is `m`. The fraction field is algebraic over the polynomial ring, so by the
tower formula its transcendence degree equals that of `k[y₁,…,y_m]`, namely `m`. -/
theorem trdeg_fractionRing_mvPolynomial (m : ℕ) :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin m) k)) = (m : Cardinal) := by
  haveI halg : Algebra.IsAlgebraic (MvPolynomial (Fin m) k)
      (FractionRing (MvPolynomial (Fin m) k)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin m) k))
  have hz : Algebra.trdeg (MvPolynomial (Fin m) k)
      (FractionRing (MvPolynomial (Fin m) k)) = 0 := trdeg_eq_zero
  have htower := trdeg_add_eq k (MvPolynomial (Fin m) k)
      (A := FractionRing (MvPolynomial (Fin m) k))
  rw [hz, add_zero, MvPolynomial.trdeg_of_isDomain, mk_fin, lift_natCast] at htower
  exact htower.symm

/-- **Problem 6.1.1 (core).** An injective `k`-algebra homomorphism
`f : k[x₁,…,x_n] → L` into a domain `L` forces `n ≤ trdeg k L`. The images
`f(xᵢ)` are algebraically independent over `k`, so they span at least `n`
transcendence degrees in `L`. -/
theorem le_trdeg_of_injective {n : ℕ} {L : Type} [CommRing L] [IsDomain L] [Algebra k L]
    (f : MvPolynomial (Fin n) k →ₐ[k] L) (hf : Function.Injective f) :
    (n : Cardinal) ≤ Algebra.trdeg k L := by
  have h := trdeg_le_of_injective f hf
  rwa [MvPolynomial.trdeg_of_isDomain, mk_fin, lift_natCast] at h

/-- **Problem 6.1.1.** If `f : k[x₁,…,x_n] → L` is an injective `k`-algebra
homomorphism into a field `L` of transcendence degree `m` over `k`, then
`n ≤ m`. -/
theorem n_le_m_of_injective_of_trdeg {n m : ℕ} {L : Type} [Field L] [Algebra k L]
    (f : MvPolynomial (Fin n) k →ₐ[k] L) (hf : Function.Injective f)
    (htrdeg : Algebra.trdeg k L = (m : Cardinal)) : n ≤ m := by
  have h := le_trdeg_of_injective f hf
  rw [htrdeg] at h
  exact_mod_cast h

/-- **Problem 6.1.1, first deduction.** An injective `k`-algebra map
`k[x₁,…,x_n] → k(y₁,…,y_m)` forces `n ≤ m`. -/
theorem n_le_m_of_injective_to_rationalFunctions {n m : ℕ}
    (f : MvPolynomial (Fin n) k →ₐ[k] FractionRing (MvPolynomial (Fin m) k))
    (hf : Function.Injective f) : n ≤ m :=
  n_le_m_of_injective_of_trdeg f hf (trdeg_fractionRing_mvPolynomial m)

/-- **Problem 6.1.1, field-embedding deduction.** A `k`-linear field embedding
`k(x₁,…,x_n) → k(y₁,…,y_m)` forces `n ≤ m`. A `k`-algebra homomorphism out of a
field is automatically injective, and composing with the inclusion of the
polynomial ring into its fraction field reduces to the previous deduction. -/
theorem n_le_m_of_field_embedding {n m : ℕ}
    (g : FractionRing (MvPolynomial (Fin n) k) →ₐ[k]
      FractionRing (MvPolynomial (Fin m) k)) : n ≤ m := by
  have hg : Function.Injective g := g.toRingHom.injective
  have hι : Function.Injective
      (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))) :=
    IsFractionRing.injective _ _
  refine n_le_m_of_injective_to_rationalFunctions
    (g.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k)
      (FractionRing (MvPolynomial (Fin n) k)))) ?_
  exact hg.comp hι

end Etingof
