/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Polynomial and rational function fields
-/

open MvPolynomial Cardinal

namespace RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields

variable {k : Type} [Field k]

/-- The rational function field in `m` variables over a field has transcendence degree `m`. -/
theorem trdeg_fractionRing_mvPolynomial_fin (m : ℕ) :
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

/-- An injective algebra map from a polynomial ring in `n` variables into an integral domain
forces `n` to be at most the codomain's transcendence degree. -/
theorem natCast_le_trdeg_of_injective_mvPolynomial_algHom {n : ℕ} {L : Type} [CommRing L]
    [IsDomain L] [Algebra k L] (f : MvPolynomial (Fin n) k →ₐ[k] L) (hf : Function.Injective f) :
    (n : Cardinal) ≤ Algebra.trdeg k L := by
  have h := trdeg_le_of_injective f hf
  rwa [MvPolynomial.trdeg_of_isDomain, mk_fin, lift_natCast] at h

/-- If a field of transcendence degree `m` contains an injective image of a polynomial ring in
`n` variables, then `n ≤ m`. -/
theorem numVariables_le_of_injective_mvPolynomial_algHom_of_trdeg_eq {n m : ℕ} {L : Type}
    [Field L] [Algebra k L] (f : MvPolynomial (Fin n) k →ₐ[k] L) (hf : Function.Injective f)
    (htrdeg : Algebra.trdeg k L = (m : Cardinal)) : n ≤ m := by
  have h := natCast_le_trdeg_of_injective_mvPolynomial_algHom f hf
  rw [htrdeg] at h
  exact_mod_cast h

/-- An injective algebra map from the polynomial ring in `n` variables to the rational function
field in `m` variables forces `n ≤ m`. -/
@[source_ref "Chapter6/Problem6.1.1" (role := primary)]
theorem numVariables_le_of_injective_mvPolynomial_algHom_to_fractionRing {n m : ℕ}
    (f : MvPolynomial (Fin n) k →ₐ[k] FractionRing (MvPolynomial (Fin m) k))
    (hf : Function.Injective f) : n ≤ m :=
  numVariables_le_of_injective_mvPolynomial_algHom_of_trdeg_eq f hf
    (trdeg_fractionRing_mvPolynomial_fin m)

/-- A base-field algebra map between rational function fields in `n` and `m` variables can exist
only when `n ≤ m`. -/
@[source_ref "Chapter6/Problem6.1.1" (role := primary)]
theorem numVariables_le_of_fractionRing_mvPolynomial_algHom {n m : ℕ}
    (g : FractionRing (MvPolynomial (Fin n) k) →ₐ[k]
      FractionRing (MvPolynomial (Fin m) k)) : n ≤ m := by
  have hg : Function.Injective g := g.toRingHom.injective
  have hι : Function.Injective
      (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))) :=
    IsFractionRing.injective _ _
  refine numVariables_le_of_injective_mvPolynomial_algHom_to_fractionRing
    (g.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k)
      (FractionRing (MvPolynomial (Fin n) k)))) ?_
  exact hg.comp hι

end RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields
