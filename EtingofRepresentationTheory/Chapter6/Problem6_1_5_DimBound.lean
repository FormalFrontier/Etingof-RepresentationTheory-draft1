import EtingofRepresentationTheory.Chapter6.Problem6_1_5_OrbitInjective
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_FieldEmbedding
import Mathlib

/-!
# Problem 6.1.5, Step 2(b)/(c): the dimension bound `N ≤ M`

This file is part of the orbit-counting redirect for the Chapter 6 infinite-type
direction (directive #4777). It assembles the **dimension bound**
`dim W(m) ≤ dim G(m)` for the dense-orbit base point, closing step 2(b)/(c) of
Etingof Problem 6.1.2 by feeding the injective orbit-map comorphism (#4807,
`injective_orbitComorphism_of_isAlgDense` / `exists_injective_orbitComorphism`,
constructed in `Problem6_1_5_OrbitInjective`) to the field-embedding bridge
(#4783, `dim_le_of_injective_comorphism_isLocalization` in
`Problem6_1_5_FieldEmbedding`).

## The two indexing conventions

The orbit-map comorphism `orbitComorphism m v₀ : k[W(m)] → B` is phrased over the
*structured* coordinate index types `WIdx m` (source) and `GIdx m` (the base ring
`k[gₚᵩ] = MvPolynomial (GIdx m) k`, of which `B` is the principal-open
localization at `detProd m`). The field-embedding bridge, resting on Problem 6.1.1,
is phrased over `Fin N` / `Fin M`. The cardinalities match the two dimensions:
`card (WIdx m) = N = dim W(m)` (`wIdx_card`) and `card (GIdx m) = M = dim G(m)`
(`gIdx_card`).

`dim_le_of_injective_comorphism_isLocalization_index` bridges the two conventions:
it generalises the field-embedding payoff to arbitrary finite index types `σ`, `τ`
and concludes `card σ ≤ card τ`. The source index is transported to `Fin (card σ)`
by `MvPolynomial.renameEquiv` (precomposition); the base index is transported to
`Fin (card τ)` by carrying the `IsLocalization` structure across the rename ring
equiv via `IsLocalization.isLocalization_of_base_ringEquiv`.

## What this file provides

* `dim_le_of_injective_comorphism_isLocalization_index`: the index-agnostic
  field-embedding payoff. An injective comorphism `k[xσ] → B` into a domain
  localization `B` of `k[xτ]` forces `card σ ≤ card τ`.
* `card_wIdx_le_card_gIdx`: over an infinite field with finitely many `G(m)`-orbits
  on `W(m)`, `card (WIdx m) ≤ card (GIdx m)`. Instantiates the index bridge at the
  concrete principal-open localization `B = k[gₚᵩ, detProd⁻¹]` with the injective
  comorphism of the dense-orbit base point.
* `repSpace_finrank_le_repGroup_ambient_finrank`: the S2/S3 interface
  `dim W(m) ≤ dim G(m)`, i.e. `∑ᵢⱼ bᵢⱼ mᵢ mⱼ ≤ ∑ᵢ mᵢ²`, ready for the `−1` strict
  refinement and `titsForm_posDef_of_cone` (`Problem6_1_5_PosDef`).
-/

open Matrix MvPolynomial MulAction

namespace Etingof.Problem6_1_5

/-! ## The index-agnostic dimension bound -/

/-- **Index-agnostic field-embedding payoff.** An injective `k`-algebra comorphism
`φ : k[xσ] → B` into a domain `B` that is a localization of `k[xτ]` at a submonoid
`S` forces `card σ ≤ card τ`.

This generalises `dim_le_of_injective_comorphism_isLocalization` (phrased over
`Fin N` / `Fin M`) to arbitrary finite index types, which is what the orbit-map
comorphism — naturally indexed by the structured types `WIdx m` / `GIdx m` —
requires. Both sides are transported to `Fin`-indexed polynomial rings by
`MvPolynomial.renameEquiv`: the source by precomposition, the base by carrying the
`IsLocalization` structure across the rename ring equiv
(`IsLocalization.isLocalization_of_base_ringEquiv`). -/
theorem dim_le_of_injective_comorphism_isLocalization_index
    {k : Type} [Field k] {σ τ : Type} [Fintype σ] [Fintype τ]
    {B : Type} [CommRing B] [IsDomain B] [Algebra k B]
    {S : Submonoid (MvPolynomial τ k)}
    [Algebra (MvPolynomial τ k) B] [IsLocalization S B]
    [IsScalarTower k (MvPolynomial τ k) B]
    (φ : MvPolynomial σ k →ₐ[k] B) (hφ : Function.Injective φ) :
    Fintype.card σ ≤ Fintype.card τ := by
  classical
  -- Reindex both sides by `Fin (card σ)` / `Fin (card τ)`.
  let eσ : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let eτ : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
  -- Transport the base ring `k[xτ] ≃+* k[Fin (card τ)]` along the rename equiv,
  -- carrying the localization structure with it.
  let h : MvPolynomial τ k ≃+* MvPolynomial (Fin (Fintype.card τ)) k :=
    (renameEquiv k eτ).toRingEquiv
  letI algB : Algebra (MvPolynomial (Fin (Fintype.card τ)) k) B :=
    ((algebraMap (MvPolynomial τ k) B).comp h.symm.toRingHom).toAlgebra
  haveI locB : IsLocalization (S.map h) B :=
    IsLocalization.isLocalization_of_base_ringEquiv S B h
  -- `k`-compatibility of the transported base algebra.
  haveI towerB : IsScalarTower k (MvPolynomial (Fin (Fintype.card τ)) k) B := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    have e1 : (algebraMap (MvPolynomial (Fin (Fintype.card τ)) k) B)
        = (algebraMap (MvPolynomial τ k) B).comp h.symm.toRingHom :=
      RingHom.algebraMap_toAlgebra _
    have e2 : h.symm.toRingHom (algebraMap k (MvPolynomial (Fin (Fintype.card τ)) k) x)
        = algebraMap k (MvPolynomial τ k) x :=
      (renameEquiv k eτ).symm.commutes x
    rw [e1, RingHom.comp_apply, e2, ← IsScalarTower.algebraMap_apply k (MvPolynomial τ k) B]
  -- Reindex the source by precomposition and apply the `Fin`-indexed bridge.
  let φ' : MvPolynomial (Fin (Fintype.card σ)) k →ₐ[k] B :=
    φ.comp (renameEquiv k eσ.symm).toAlgHom
  have hφ' : Function.Injective φ' := by
    have : (φ' : MvPolynomial (Fin (Fintype.card σ)) k → B)
        = φ ∘ (renameEquiv k eσ.symm) := by
      ext p; simp [φ']
    rw [show (⇑φ') = _ from this]
    exact hφ.comp (renameEquiv k eσ.symm).injective
  exact dim_le_of_injective_comorphism_isLocalization (S := S.map h) φ' hφ'

/-! ## The concrete dimension bound for `W(m)` / `G(m)` -/

variable {k : Type} [Field k] [Infinite k] {n : ℕ}
  [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]

/-- **Step 2(b)/(c) for `W(m)` / `G(m)`.** Over an infinite field with finitely many
`G(m)`-orbits on `W(m)`, the coordinate dimension of the representation space is at
most that of the group ambient space: `card (WIdx m) ≤ card (GIdx m)`.

This instantiates the index-agnostic bridge at the concrete principal-open
coordinate ring `B = k[gₚᵩ, detProd⁻¹] = Localization (powers (detProd m))`
(a domain, since `detProd m ≠ 0` over the domain `k[gₚᵩ]`), fed the injective
orbit-map comorphism of the dense-orbit base point
(`exists_injective_orbitComorphism`, #4807). -/
theorem card_wIdx_le_card_gIdx (m : Fin n → ℕ)
    [Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))] :
    Fintype.card (WIdx m) ≤ Fintype.card (GIdx m) := by
  -- the concrete principal-open coordinate ring
  haveI : IsDomain (Localization (Submonoid.powers (detProd (k := k) m))) :=
    IsLocalization.isDomain_localization
      (M := Submonoid.powers (detProd (k := k) m))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (detProd_ne_zero (k := k) m))
  obtain ⟨v₀, hv₀⟩ :=
    exists_injective_orbitComorphism
      (B := Localization (Submonoid.powers (detProd (k := k) m))) (k := k) m
  exact dim_le_of_injective_comorphism_isLocalization_index
    (S := Submonoid.powers (detProd (k := k) m))
    (orbitComorphism (B := Localization (Submonoid.powers (detProd (k := k) m))) m v₀) hv₀

set_option linter.unusedFintypeInType false in
/-- **The S2/S3 interface: `dim W(m) ≤ dim G(m)`.** Over an infinite field with
finitely many `G(m)`-orbits on `W(m)`,
`Module.finrank k (W(m)) ≤ Module.finrank k (∏ᵢ Matrix (Fin mᵢ) (Fin mᵢ) k)`, i.e.
`∑ᵢⱼ bᵢⱼ mᵢ mⱼ ≤ ∑ᵢ mᵢ²`. This is the dimension inequality the orbit-counting
argument delivers, ready for the `−1` strict refinement and `titsForm_posDef_of_cone`
(`Problem6_1_5_PosDef`). -/
theorem repSpace_finrank_le_repGroup_ambient_finrank (m : Fin n → ℕ)
    [Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))] :
    Module.finrank k (repSpace (k := k) m)
      ≤ Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k) := by
  have hle := card_wIdx_le_card_gIdx (k := k) m
  rwa [wIdx_card, gIdx_card, ← repSpace_finrank (k := k) m,
    ← repGroup_ambient_finrank (k := k) m] at hle

/-! ## The `−1` strict refinement -/

/-- **Step 2(c), strict refinement: `dim W(m) < dim G(m)` for nonzero `m`.** The
non-strict `card_wIdx_le_card_gIdx` only yields `q(m) ≥ 0` (positive
*semi*definite), satisfied by the affine/extended Dynkin diagrams — exactly the
borderline infinite-type quivers. The strict `<` is what distinguishes finite
type, and it comes from the single copy of global scalars `k*` that embeds
diagonally into `repGroup k m = ∏ᵢ GL(Fin (m i))` as `λ ↦ (fun i => λ • 1)` and
acts **trivially** on `repSpace m`: on the `i⟶j` block the action is
`(λ·1)·x·(λ·1)⁻¹ = x`. So the orbit map is constant on `k*`-cosets and the generic
orbit has dimension `≤ dim G(m) − 1`.

In comorphism terms (this proof's route): under the global-scalar scaling of the
`GIdx m` generators, the image of `orbitComorphism m v₀` is invariant — each
generator maps to an entry of `G_j · v₀ · G_i⁻¹`, where the `λ` and `λ⁻¹` cancel
— so it lands in the **degree-0 part** of `B`. The distinguished generator `g*`
is then transcendental over the image subfield (Vandermonde over the infinite
field `k`), so the `card (WIdx m)` algebraically independent images together with
`g*` give `card (WIdx m) + 1 ≤ trdeg = card (GIdx m)`.

The proof is split across two sub-issues of #4824: the reusable abstract core
`card_lt_of_injective_comorphism_degreeZero` (#4828) and the comorphism degree-0
invariance + this assembly (#4830). The `sorry` below is tracked by **#4830**. -/
theorem card_wIdx_lt_card_gIdx (m : Fin n → ℕ) (hm : m ≠ 0)
    [Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))] :
    Fintype.card (WIdx m) < Fintype.card (GIdx m) := by
  sorry

set_option linter.unusedFintypeInType false in
/-- **The S2/S3 strict interface: `dim W(m) < dim G(m)` for nonzero `m`.** The
`−1` strict refinement of `repSpace_finrank_le_repGroup_ambient_finrank`,
phrased with the `Module.finrank` quantities of `Problem6_1_5_OrbitSpace`. This is
exactly the `hstrict` hypothesis consumed by
`Etingof.isDynkinDiagram_of_strict_finrank` (`Problem6_1_5_TitsBridge`), so it is
the directly-consumable hook for the final S4 assembly (#4786). It is derived
here sorry-free from `card_wIdx_lt_card_gIdx` (whose proof is #4830). -/
theorem repSpace_finrank_lt_repGroup_ambient_finrank (m : Fin n → ℕ) (hm : m ≠ 0)
    [Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))] :
    Module.finrank k (repSpace (k := k) m)
      < Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k) := by
  have hlt := card_wIdx_lt_card_gIdx (k := k) m hm
  rwa [wIdx_card, gIdx_card, ← repSpace_finrank (k := k) m,
    ← repGroup_ambient_finrank (k := k) m] at hlt

end Etingof.Problem6_1_5
