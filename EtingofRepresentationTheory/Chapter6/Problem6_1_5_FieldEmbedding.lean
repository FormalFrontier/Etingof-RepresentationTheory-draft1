import EtingofRepresentationTheory.Chapter6.Problem6_1_1
import Mathlib

/-!
# Problem 6.1.5, Step 2(b): a Zariski-dense orbit gives a field embedding

This file is part of the orbit-counting redirect for the Chapter 6 infinite-type
direction (directive #4777). It closes **step 2(b)** of Etingof Problem 6.1.2,
the field-embedding bridge that connects step 2(a) (a Zariski-dense orbit) to
Problem 6.1.1 (the transcendence-degree inequality):

> Use a Zariski-dense `G`-orbit on `W` to construct a field embedding
> `k(x₁,…,x_N) ↪ k(g_{pq})`, then apply Problem 6.1.1.

## The book argument (6.1.2(b))

Fix a point `v₀` with a Zariski-dense `G`-orbit. The orbit map `φ : G → W`,
`g ↦ g · v₀`, has dense image, so its comorphism `φ* : k[W] → k[G]` is injective:
a regular function on `W` that pulls back to `0` vanishes on the (dense) orbit,
and the book's notion of Zariski-dense (6.1.2(a)) is *exactly* "a polynomial
vanishing on the set is zero coefficientwise", i.e. `φ*` injective. Writing
`k[W] = k[x₁,…,x_N]` (linear coordinates on the affine space `W = 𝔸^N`) and
`k[G] ⊆ k(g_{pq})` (`G` is a principal open in the `Σ mᵢ²`-dimensional matrix
space, so its coordinate ring is a localization of `k[g_{pq}]` and shares the
same fraction field), composing `φ*` with `k[G] ↪ k(g_{pq})` yields an injective
`k`-algebra hom

`k[x₁,…,x_N] → k(g_{pq})`,

which is exactly the hypothesis consumed by Problem 6.1.1
(`Etingof.n_le_m_of_injective_to_rationalFunctions`) to deduce `N ≤ M`.

## What this file provides

The reusable **field-embedding bridge**, phrased so that the genuinely geometric
input — injectivity of the comorphism, i.e. Zariski-density of the orbit — is the
hypothesis, and everything downstream of it (fraction-field lifting, the
principal-open identification, and the dimension bound via 6.1.1) is discharged:

* `exists_field_embedding_of_injective`: the general bridge. An injective
  `k`-algebra hom `k[x₁,…,x_N] → B` into any domain `B` whose fraction field is
  `k`-isomorphic to `k(g₁,…,g_M)` gives an injective `k[x₁,…,x_N] → k(g₁,…,g_M)`.
* `exists_field_embedding_of_injective_mvPolynomial`: the polynomial-action case
  (`B = k[g₁,…,g_M]`), where the orbit map is a genuine morphism and the
  comorphism lands in the polynomial ring directly (Problem 6.1.2 for a single
  `GLₘ` acting by an algebraic representation).
* `exists_field_embedding_of_injective_isLocalization`: the principal-open case
  (`B` a localization of `k[g₁,…,g_M]`, e.g. `k[g_{pq}, det⁻¹]`), where the
  base-change action `g_j · M · g_i⁻¹` forces `det⁻¹` into the comorphism. This
  is the form needed for `W(m)` with the `G(m)`-action of S0. The principal-open
  function-field identification is `isFractionRing_of_isDomain_of_isLocalization`.
* `dim_le_of_injective_comorphism` and its specialisations: the payoff `N ≤ M`,
  obtained by feeding the field embedding to Problem 6.1.1.

The remaining geometric input — constructing the concrete orbit-map comorphism
`φ*` on `repSpace`/`repGroup` and proving its injectivity from topological
density of the orbit (S2a's output) — is tracked as a follow-up; once it lands,
`exists_field_embedding_of_injective_isLocalization` consumes it directly.
-/

open MvPolynomial

namespace Etingof.Problem6_1_5

/-- **The field-embedding bridge (general form).** Let `B` be a domain `k`-algebra
whose fraction field `K` is `k`-isomorphic to `k(g₁,…,g_M) = FractionRing k[g₁,…,g_M]`.
An injective `k`-algebra hom `φ : k[x₁,…,x_N] → B` (the comorphism of a dominant
orbit map — injectivity is Zariski-density of the orbit) yields an injective
`k`-algebra hom `k[x₁,…,x_N] → k(g₁,…,g_M)`.

The map is `e ∘ (B ↪ K) ∘ φ`: `φ` is injective by hypothesis, `B ↪ K` is injective
because `B` is a domain (`IsFractionRing.injective`), and `e` is an equivalence. -/
theorem exists_field_embedding_of_injective
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
    simp only [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', AlgEquiv.toAlgHom_eq_coe]
    exact e.injective.comp (hBK.comp hφ)
  exact this

/-- **The field-embedding bridge (polynomial-action case).** If the comorphism lands
in the polynomial ring `k[g₁,…,g_M]` itself (the orbit map is a genuine morphism, as
for a single `GLₘ` acting by an algebraic representation — Problem 6.1.2 proper), an
injective `φ : k[x₁,…,x_N] → k[g₁,…,g_M]` gives an injective field embedding into
`k(g₁,…,g_M)`. -/
theorem exists_field_embedding_of_injective_mvPolynomial
    {k : Type} [Field k] {N M : ℕ}
    (φ : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin M) k) (hφ : Function.Injective φ) :
    ∃ f : MvPolynomial (Fin N) k →ₐ[k] FractionRing (MvPolynomial (Fin M) k),
      Function.Injective f :=
  exists_field_embedding_of_injective (AlgEquiv.refl) φ hφ

-- v4.29.0: typeclass and whnf searches (SMul/Module B K from the local Algebra B K) got slower; bump limits.
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 400000 in
/-- **The field-embedding bridge (principal-open case).** When the base-change action
`g_j · M · g_i⁻¹` forces inverses, the comorphism lands in a localization `B` of
`k[g₁,…,g_M]` (e.g. `k[g_{pq}, det⁻¹]`, the coordinate ring of the principal open
`G = {det ≠ 0}`). Since `B` is a localization of the domain `k[g₁,…,g_M]`, it shares
its fraction field (`isFractionRing_of_isDomain_of_isLocalization`), so an injective
`φ : k[x₁,…,x_N] → B` still yields a field embedding into `k(g₁,…,g_M)`. -/
theorem exists_field_embedding_of_injective_isLocalization
    {k : Type} [Field k] {N M : ℕ}
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {S : Submonoid (MvPolynomial (Fin M) k)}
    [Algebra (MvPolynomial (Fin M) k) B] [IsLocalization S B]
    [IsScalarTower k (MvPolynomial (Fin M) k) B]
    (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Injective φ) :
    ∃ f : MvPolynomial (Fin N) k →ₐ[k] FractionRing (MvPolynomial (Fin M) k),
      Function.Injective f := by
  -- abbreviations
  set P := MvPolynomial (Fin M) k
  set K := FractionRing P
  -- `S` avoids `0` (else `B` would be trivial, contradicting `IsDomain B`), so over the
  -- domain `P` we have `S ≤ nonZeroDivisors P`.
  have hSle : S ≤ nonZeroDivisors P := by
    intro s hs
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    have : (0 : B) = 1 := by
      have := IsLocalization.map_units (M := S) B (⟨(0 : P), hs⟩ : S)
      simpa using this.ne_zero (by simp) |>.elim
    exact zero_ne_one this
  -- the localization map `B → K = Frac P`: each `s ∈ S` is a nonzerodivisor, hence a
  -- unit in the fraction field.
  have hunit : ∀ y : S, IsUnit (algebraMap P K (y : P)) := fun y =>
    IsLocalization.map_units K (⟨(y : P), hSle y.2⟩ : nonZeroDivisors P)
  letI algBK : Algebra B K := (IsLocalization.lift (M := S) (g := algebraMap P K) hunit).toAlgebra
  -- v4.29.0: surface `SMul`/`Module B K` from `algBK` explicitly; otherwise typeclass search
  -- for these from the local `Algebra B K` loops and times out.
  letI smulBK : SMul B K := algBK.toSMul
  letI moduleBK : Module B K := algBK.toModule
  have hcomp : (algebraMap B K).comp (algebraMap P B) = algebraMap P K := by
    change (IsLocalization.lift (M := S) (g := algebraMap P K) hunit).comp (algebraMap P B)
      = algebraMap P K
    exact IsLocalization.lift_comp hunit
  haveI tower_PBK : IsScalarTower P B K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  -- `B` is a localization of the domain `P`, hence shares `P`'s fraction field.
  haveI : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S B K
  -- `k`-compatibility of the localization map.
  haveI tower_kBK : IsScalarTower k B K := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    have h1 : algebraMap k K x = algebraMap P K (algebraMap k P x) :=
      IsScalarTower.algebraMap_apply k P K x
    have h2 : algebraMap k B x = algebraMap P B (algebraMap k P x) :=
      IsScalarTower.algebraMap_apply k P B x
    rw [h1, ← hcomp, RingHom.comp_apply, ← h2]
  exact exists_field_embedding_of_injective (AlgEquiv.refl) φ hφ

/-! ## The dimension bound (combining with Problem 6.1.1) -/

/-- **Problem 6.1.2(b) payoff.** An injective comorphism `k[x₁,…,x_N] → B` into a domain
whose fraction field is `k(g₁,…,g_M)` forces `N ≤ M`. This is the chain
"Zariski-dense orbit ⟹ field embedding ⟹ transcendence-degree inequality", with the last
step supplied by Problem 6.1.1. -/
theorem dim_le_of_injective_comorphism
    {k : Type} [Field k] {N M : ℕ}
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {K : Type} [Field K] [Algebra k K] [Algebra B K] [IsScalarTower k B K]
    [IsFractionRing B K]
    (e : K ≃ₐ[k] FractionRing (MvPolynomial (Fin M) k))
    (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Injective φ) :
    N ≤ M := by
  obtain ⟨f, hf⟩ := exists_field_embedding_of_injective e φ hφ
  exact Etingof.n_le_m_of_injective_to_rationalFunctions f hf

/-- The dimension bound in the principal-open (localization) case: an injective comorphism
`k[x₁,…,x_N] → B` into a localization `B` of `k[g₁,…,g_M]` forces `N ≤ M`. This is the
form `W(m)` with the base-change `G(m)`-action delivers. -/
theorem dim_le_of_injective_comorphism_isLocalization
    {k : Type} [Field k] {N M : ℕ}
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {S : Submonoid (MvPolynomial (Fin M) k)}
    [Algebra (MvPolynomial (Fin M) k) B] [IsLocalization S B]
    [IsScalarTower k (MvPolynomial (Fin M) k) B]
    (φ : MvPolynomial (Fin N) k →ₐ[k] B) (hφ : Function.Injective φ) :
    N ≤ M := by
  obtain ⟨f, hf⟩ := exists_field_embedding_of_injective_isLocalization (M := M) (S := S) φ hφ
  exact Etingof.n_le_m_of_injective_to_rationalFunctions f hf

end Etingof.Problem6_1_5
