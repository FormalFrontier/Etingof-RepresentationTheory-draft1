/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Bounds on the number of polynomial variables

Let `B` be a domain over a field `k` whose fraction field is equivalent over `k` to the
fraction field of a polynomial ring in `M` variables. An injective `k`-algebra homomorphism
from the polynomial ring in `N` variables to `B` forces `N ≤ M`.
-/

open MvPolynomial

namespace RepresentationTheory.Algebra.MvPolynomial.VariableCount

namespace MvPolynomial

/--
Suppose the fraction field of a domain over `k` is equivalent over `k` to the fraction field of the polynomial ring indexed by `Fin M`. An injective `k`-algebra homomorphism from the polynomial ring indexed by `Fin N` into the domain yields an embedding of `Fin N` into `Fin M` with injective underlying function.
-/
theorem exists_fin_embedding_of_injective_algHom_of_fractionRing_equiv
    {k : Type} [Field k] {N M : ℕ}
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {K : Type} [Field K] [Algebra k K] [Algebra B K] [IsScalarTower k B K]
    [IsFractionRing B K]
    (e : K ≃ₐ[k] FractionRing (MvPolynomial (Fin M) k))
    (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Injective φ) :
    ∃ f : MvPolynomial (Fin N) k →ₐ[k] FractionRing (MvPolynomial (Fin M) k),
      Function.Injective f := by
  refine ⟨e.toAlgHom.comp ((IsScalarTower.toAlgHom k B K).comp φ), ?_⟩
  have hBK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have : Function.Injective
      (⇑(e.toAlgHom.comp ((IsScalarTower.toAlgHom k B K).comp φ))) := by
    simp only [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom']
    exact e.injective.comp (hBK.comp hφ)
  exact this

/--
An injective `k`-algebra homomorphism from the polynomial ring indexed by `Fin N` to the polynomial ring indexed by `Fin M` gives an embedding of `Fin N` into `Fin M` with injective underlying function.
-/
theorem exists_fin_embedding_of_injective_algHom
    {k : Type} [Field k] {N M : ℕ}
    (φ : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin M) k) (hφ : Function.Injective φ) :
    ∃ f : MvPolynomial (Fin N) k →ₐ[k] FractionRing (MvPolynomial (Fin M) k),
      Function.Injective f :=
  exists_fin_embedding_of_injective_algHom_of_fractionRing_equiv (AlgEquiv.refl) φ hφ

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 400000 in
/--
For a domain obtained by localizing the polynomial ring over `k` indexed by `Fin M`, an injective `k`-algebra homomorphism from the polynomial ring indexed by `Fin N` produces an embedding of `Fin N` into `Fin M` whose underlying function is injective.
-/
theorem exists_fin_embedding_of_injective_algHom_of_isLocalization
    {k : Type} [Field k] {N M : ℕ}
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {S : Submonoid (MvPolynomial (Fin M) k)}
    [Algebra (MvPolynomial (Fin M) k) B] [IsLocalization S B]
    [IsScalarTower k (MvPolynomial (Fin M) k) B]
    (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Injective φ) :
    ∃ f : MvPolynomial (Fin N) k →ₐ[k] FractionRing (MvPolynomial (Fin M) k),
      Function.Injective f := by
  set P := MvPolynomial (Fin M) k
  set K := FractionRing P
  have hSle : S ≤ nonZeroDivisors P := by
    intro s hs
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    have : (0 : B) = 1 := by
      have := IsLocalization.map_units (M := S) B (⟨(0 : P), hs⟩ : S)
      simpa using this.ne_zero (by simp) |>.elim
    exact zero_ne_one this
  have hunit : ∀ y : S, IsUnit (algebraMap P K (y : P)) := fun y =>
    IsLocalization.map_units K (⟨(y : P), hSle y.2⟩ : nonZeroDivisors P)
  letI algBK : Algebra B K := (IsLocalization.lift (M := S) (g := algebraMap P K) hunit).toAlgebra
  letI smulBK : SMul B K := algBK.toSMul
  letI moduleBK : Module B K := algBK.toModule
  have hcomp : (algebraMap B K).comp (algebraMap P B) = algebraMap P K := by
    change (IsLocalization.lift (M := S) (g := algebraMap P K) hunit).comp (algebraMap P B)
      = algebraMap P K
    exact IsLocalization.lift_comp hunit
  haveI tower_PBK : IsScalarTower P B K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  haveI : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S B K
  haveI tower_kBK : IsScalarTower k B K := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    have h1 : algebraMap k K x = algebraMap P K (algebraMap k P x) :=
      IsScalarTower.algebraMap_apply k P K x
    have h2 : algebraMap k B x = algebraMap P B (algebraMap k P x) :=
      IsScalarTower.algebraMap_apply k P B x
    rw [h1, ← hcomp, RingHom.comp_apply, ← h2]
  exact exists_fin_embedding_of_injective_algHom_of_fractionRing_equiv (AlgEquiv.refl) φ hφ

/--
Let `B` be a domain over a field `k` whose fraction field is equivalent over `k` to the fraction field of a polynomial ring in `M` variables. If the polynomial ring over `k` in `N` variables admits an injective `k`-algebra homomorphism into `B`, then `N ≤ M`.
-/
theorem variable_count_le_of_injective_algHom_of_fractionRing_equiv
    {k : Type} [Field k] {N M : ℕ}
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {K : Type} [Field K] [Algebra k K] [Algebra B K] [IsScalarTower k B K]
    [IsFractionRing B K]
    (e : K ≃ₐ[k] FractionRing (MvPolynomial (Fin M) k))
    (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Injective φ) :
    N ≤ M := by
  obtain ⟨f, hf⟩ := exists_fin_embedding_of_injective_algHom_of_fractionRing_equiv e φ hφ
  exact RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields.numVariables_le_of_injective_mvPolynomial_algHom_to_fractionRing f hf

/--
If a domain is a localization of the polynomial ring over a field in `M` variables, then any injective algebra homomorphism from the polynomial ring in `N` variables into that domain forces `N ≤ M`.
-/
theorem variable_count_le_of_injective_algHom_of_isLocalization
    {k : Type} [Field k] {N M : ℕ}
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {S : Submonoid (MvPolynomial (Fin M) k)}
    [Algebra (MvPolynomial (Fin M) k) B] [IsLocalization S B]
    [IsScalarTower k (MvPolynomial (Fin M) k) B]
    (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Injective φ) :
    N ≤ M := by
  obtain ⟨f, hf⟩ := exists_fin_embedding_of_injective_algHom_of_isLocalization (M := M) (S := S) φ hφ
  exact RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields.numVariables_le_of_injective_mvPolynomial_algHom_to_fractionRing f hf

end MvPolynomial

end RepresentationTheory.Algebra.MvPolynomial.VariableCount
