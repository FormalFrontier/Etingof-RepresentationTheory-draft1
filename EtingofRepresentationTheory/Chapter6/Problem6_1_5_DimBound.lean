import EtingofRepresentationTheory.Chapter6.Problem6_1_5_OrbitInjective
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_FieldEmbedding
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_StrictDimBound
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

/-! ## Scaling-automorphism machinery for the `−1` strict refinement -/

/-- **Global-scalar scaling automorphism of `k[gₚᵩ]`.** For a unit `c : kˣ`, the
`k`-algebra automorphism of `MvPolynomial (GIdx m) k` sending each coordinate
generator `X t` to `c • X t`. Its inverse scales by `c⁻¹`. This is the comorphism
incarnation of the diagonal `k*`-action on the group ambient space; on the orbit
comorphism image it acts trivially (degree 0), which is the source of the `−1`. -/
noncomputable def gidxScaleAut (m : Fin n → ℕ) (c : kˣ) :
    MvPolynomial (GIdx m) k ≃ₐ[k] MvPolynomial (GIdx m) k :=
  AlgEquiv.ofAlgHom
    (aeval fun t : GIdx m => (c : k) • X t)
    (aeval fun t : GIdx m => ((c⁻¹ : kˣ) : k) • X t)
    (by
      apply MvPolynomial.algHom_ext
      intro t
      simp only [AlgHom.comp_apply, aeval_X, map_smul, AlgHom.coe_id, id_eq]
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul])
    (by
      apply MvPolynomial.algHom_ext
      intro t
      simp only [AlgHom.comp_apply, aeval_X, map_smul, AlgHom.coe_id, id_eq]
      rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])

omit [Quiver.{0} (Fin n)] [Infinite k] [∀ i j : Fin n, Fintype (i ⟶ j)] in
@[simp]
theorem gidxScaleAut_X (m : Fin n → ℕ) (c : kˣ) (t : GIdx m) :
    gidxScaleAut m c (X t) = (c : k) • X t := by
  rw [gidxScaleAut, AlgEquiv.ofAlgHom_apply, aeval_X]

/-- The scaling automorphism `gidxScaleAut` extended to the fraction field
`k(gₚᵩ) = FractionRing (MvPolynomial (GIdx m) k)`, by functoriality of the fraction
field (`IsFractionRing.algEquivOfAlgEquiv`). This is the scaling automorphism family
`scale` fed to the abstract `−1` core `card_lt_of_scaleInvariant_image_fractionRing`. -/
noncomputable def gidxScaleK (m : Fin n → ℕ) (c : kˣ) :
    FractionRing (MvPolynomial (GIdx m) k) ≃ₐ[k] FractionRing (MvPolynomial (GIdx m) k) :=
  IsFractionRing.algEquivOfAlgEquiv (gidxScaleAut m c)

omit [Quiver.{0} (Fin n)] [Infinite k] [∀ i j : Fin n, Fintype (i ⟶ j)] in
@[simp]
theorem gidxScaleK_algebraMap (m : Fin n → ℕ) (c : kˣ) (x : MvPolynomial (GIdx m) k) :
    gidxScaleK m c (algebraMap (MvPolynomial (GIdx m) k)
        (FractionRing (MvPolynomial (GIdx m) k)) x)
      = algebraMap (MvPolynomial (GIdx m) k) (FractionRing (MvPolynomial (GIdx m) k))
          (gidxScaleAut m c x) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (gidxScaleAut m c) x

/-- **Block cancellation `G_j · V · G_i⁻¹` is scale-invariant.** If a ring
homomorphism `Φ` scales two square matrices `A`, `C` by the same unit `μ`
(`A.map Φ = μ • A`, `C.map Φ = μ • C`) and fixes a third matrix `V`, then it fixes
the conjugated product `A · V · C⁻¹`: the `μ` from `A` and the `μ⁻¹` from `C⁻¹`
cancel. This is the matrix core of the degree-0 invariance of the orbit comorphism
image (with `A = G_j`, `C = G_i`, `V` the constant base-point block). -/
theorem map_smul_conj_eq {K : Type*} [Field K] {p q : ℕ}
    {F : Type*} [FunLike F K K] [RingHomClass F K K] (Φ : F) (μ : Kˣ)
    {A : Matrix (Fin p) (Fin p) K} {V : Matrix (Fin p) (Fin q) K}
    {C : Matrix (Fin q) (Fin q) K}
    (hA : A.map Φ = (μ : K) • A) (hV : V.map Φ = V)
    (hCm : C.map Φ = (μ : K) • C) (hCdet : IsUnit C.det) :
    (A * V * C⁻¹).map Φ = A * V * C⁻¹ := by
  have hCinv : (C⁻¹).map Φ = (μ : K)⁻¹ • C⁻¹ := by
    have h1 : (C * C⁻¹).map Φ = (1 : Matrix (Fin q) (Fin q) K).map Φ := by
      rw [Matrix.mul_nonsing_inv C hCdet]
    rw [Matrix.map_mul, hCm, Matrix.map_one (⇑Φ) (map_zero Φ) (map_one Φ)] at h1
    -- h1 : (↑μ • C) * (C⁻¹).map Φ = 1
    have hsc : ((μ : K) • C)⁻¹ = (μ : K)⁻¹ • C⁻¹ := by
      have h := Matrix.inv_smul' C μ hCdet
      rwa [Units.smul_def, Units.smul_def, Units.val_inv_eq_inv_val] at h
    rw [← hsc, ← Matrix.inv_eq_right_inv h1]
  rw [Matrix.map_mul, Matrix.map_mul, hA, hV, hCinv, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, inv_mul_cancel₀ (Units.ne_zero μ), one_smul]

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
`card_lt_of_scaleInvariant_image_fractionRing` (#4828) and the comorphism degree-0
invariance + this assembly (#4830). -/
theorem card_wIdx_lt_card_gIdx (m : Fin n → ℕ) (hm : m ≠ 0)
    [Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))] :
    Fintype.card (WIdx m) < Fintype.card (GIdx m) := by
  classical
  -- `B` := the principal-open localization (a domain); `K` := its fraction field.
  haveI : IsDomain (Localization (Submonoid.powers (detProd (k := k) m))) :=
    IsLocalization.isDomain_localization
      (M := Submonoid.powers (detProd (k := k) m))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (detProd_ne_zero (k := k) m))
  -- the injective orbit-map comorphism into `B`
  obtain ⟨v₀, hv₀⟩ :=
    exists_injective_orbitComorphism
      (B := Localization (Submonoid.powers (detProd (k := k) m))) (k := k) m
  -- `algebraMap k[G] → k(G)` is injective (fraction field)
  have halg_inj : Function.Injective
      (algebraMap (MvPolynomial (GIdx m) k) (FractionRing (MvPolynomial (GIdx m) k))) :=
    IsFractionRing.injective _ _
  -- powers of `detProd` map to units in the fraction field
  have hf_units : ∀ y : Submonoid.powers (detProd (k := k) m),
      IsUnit (IsScalarTower.toAlgHom k (MvPolynomial (GIdx m) k)
        (FractionRing (MvPolynomial (GIdx m) k)) (y : MvPolynomial (GIdx m) k)) := by
    intro y
    have hy : (y : MvPolynomial (GIdx m) k) ∈ nonZeroDivisors (MvPolynomial (GIdx m) k) :=
      powers_le_nonZeroDivisors_of_noZeroDivisors (detProd_ne_zero (k := k) m) y.2
    rw [IsScalarTower.toAlgHom_apply]
    exact (Ne.isUnit ((map_ne_zero_iff _ halg_inj).mpr (nonZeroDivisors.ne_zero hy)))
  -- the `k`-algebra embedding `ιB : B → K`
  let ιB : Localization (Submonoid.powers (detProd (k := k) m)) →ₐ[k]
      FractionRing (MvPolynomial (GIdx m) k) := IsLocalization.liftAlgHom hf_units
  have hιB_alg : ∀ x : MvPolynomial (GIdx m) k,
      ιB (algebraMap (MvPolynomial (GIdx m) k)
            (Localization (Submonoid.powers (detProd (k := k) m))) x)
        = algebraMap (MvPolynomial (GIdx m) k) (FractionRing (MvPolynomial (GIdx m) k)) x := by
    intro x
    change IsLocalization.liftAlgHom hf_units _ = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rfl
  -- `ιB` is injective
  have hιB_inj : Function.Injective ιB := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨x, s⟩, hs⟩ :=
      IsLocalization.surj (Submonoid.powers (detProd (k := k) m)) b
    have happ := congrArg ιB hs
    rw [map_mul, hb, zero_mul, hιB_alg] at happ
    have hx0 : x = 0 := (map_eq_zero_iff _ halg_inj).mp happ.symm
    rw [hx0, map_zero] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact h
    · exact absurd h (IsLocalization.map_units _ s).ne_zero
  -- the comorphism `φ = ιB ∘ orbitComorphism : k[W] → K`, injective
  set φ : MvPolynomial (WIdx m) k →ₐ[k] FractionRing (MvPolynomial (GIdx m) k) :=
    ιB.comp (orbitComorphism
      (B := Localization (Submonoid.powers (detProd (k := k) m))) m v₀) with hφ
  have hφ_inj : Function.Injective φ := by
    rw [hφ, AlgHom.coe_comp]; exact hιB_inj.comp hv₀
  -- the distinguished coordinate `g = X t₀` (`t₀` exists since `m ≠ 0`)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hm
  rw [Pi.zero_apply] at hi₀
  set t₀ : GIdx m :=
    ⟨i₀, (⟨0, Nat.pos_of_ne_zero hi₀⟩, ⟨0, Nat.pos_of_ne_zero hi₀⟩)⟩ with ht₀
  set g : FractionRing (MvPolynomial (GIdx m) k) :=
    algebraMap (MvPolynomial (GIdx m) k) (FractionRing (MvPolynomial (GIdx m) k)) (X t₀)
    with hg_def
  have hg : g ≠ 0 := (map_ne_zero_iff _ halg_inj).mpr (MvPolynomial.X_ne_zero t₀)
  -- `algebraMap k[G] → k(G)` commutes with `k`-scaling
  have hsmul : ∀ (c : k) (z : MvPolynomial (GIdx m) k),
      algebraMap (MvPolynomial (GIdx m) k) (FractionRing (MvPolynomial (GIdx m) k)) (c • z)
        = c • algebraMap (MvPolynomial (GIdx m) k)
            (FractionRing (MvPolynomial (GIdx m) k)) z := by
    intro c z
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  -- `scale μ g = μ • g`
  have hscale_g : ∀ μ : kˣ, gidxScaleK m μ g = (μ : k) • g := by
    intro μ
    rw [hg_def, gidxScaleK_algebraMap, gidxScaleAut_X, hsmul]
  -- **the degree-0 invariance**: `scale μ` fixes every image coordinate `φ (X w)`
  have hscale_f : ∀ (μ : kˣ) (w : WIdx m), gidxScaleK m μ (φ (X w)) = φ (X w) := by
    intro μ w
    -- `μ` as a unit of `K`, with `↑μ' = algebraMap k K μ`
    set μ' : (FractionRing (MvPolynomial (GIdx m) k))ˣ :=
      Units.map (algebraMap k (FractionRing (MvPolynomial (GIdx m) k))).toMonoidHom μ with hμ'
    have hμ'val : (μ' : FractionRing (MvPolynomial (GIdx m) k))
        = algebraMap k (FractionRing (MvPolynomial (GIdx m) k)) (μ : k) := by
      rw [hμ', Units.coe_map]; rfl
    -- entry value of the mapped generic matrix
    have hentry : ∀ (i' : Fin n) (a b : Fin (m i')),
        ((genMatB (k := k)
            (B := Localization (Submonoid.powers (detProd (k := k) m))) m i').map ιB) a b
          = algebraMap (MvPolynomial (GIdx m) k) (FractionRing (MvPolynomial (GIdx m) k))
              (X (⟨i', (a, b)⟩ : GIdx m)) := by
      intro i' a b
      simp only [Matrix.map_apply, genMatB, genMat]
      exact hιB_alg _
    -- `scale μ` scales each mapped generic matrix by `μ'`
    have hAscale : ∀ i' : Fin n,
        ((genMatB (k := k)
            (B := Localization (Submonoid.powers (detProd (k := k) m))) m i').map ιB).map
            (gidxScaleK m μ)
          = (μ' : FractionRing (MvPolynomial (GIdx m) k)) •
            ((genMatB (k := k)
              (B := Localization (Submonoid.powers (detProd (k := k) m))) m i').map ιB) := by
      intro i'; ext a b
      rw [Matrix.map_apply, hentry, gidxScaleK_algebraMap, gidxScaleAut_X, hsmul,
        Matrix.smul_apply, hentry, hμ'val, algebraMap_smul]
    -- `scale μ` fixes the constant base-point block
    have hVfix : (((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
          (Localization (Submonoid.powers (detProd (k := k) m))))).map ιB).map (gidxScaleK m μ)
        = ((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
          (Localization (Submonoid.powers (detProd (k := k) m))))).map ιB := by
      ext a b
      simp only [Matrix.map_apply]
      rw [AlgHom.commutes, AlgEquiv.commutes]
    -- `(genMatBInv i).map ιB` is the inverse of `(genMatB i).map ιB`
    have hCBinv : (genMatBInv (k := k)
          (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB
        = ((genMatB (k := k)
          (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB)⁻¹ := by
      have h1 : ((genMatB (k := k)
            (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB)
          * ((genMatBInv (k := k)
            (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB) = 1 := by
        rw [← Matrix.map_mul, genMatB_mul_inv,
          Matrix.map_one (⇑ιB) (map_zero ιB) (map_one ιB)]
      exact (Matrix.inv_eq_right_inv h1).symm
    -- expand `φ (X w)` as a conjugated product, then cancel
    have hCdet : IsUnit (((genMatB (k := k)
        (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB).det) := by
      rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
      exact (isUnit_det_genMatB (k := k)
        (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB
    -- the conjugated product as a matrix over `K`
    have hmatrix : (genMatB (k := k)
          (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.2.1
        * (v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
            (Localization (Submonoid.powers (detProd (k := k) m))))
        * genMatBInv (k := k)
            (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB
        = (genMatB (k := k)
              (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.2.1).map ιB
          * ((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
              (Localization (Submonoid.powers (detProd (k := k) m))))).map ιB
          * ((genMatB (k := k)
              (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB)⁻¹ := by
      rw [Matrix.map_mul, Matrix.map_mul, hCBinv]
    have hexp : φ (X w)
        = (((genMatB (k := k)
              (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.2.1).map ιB)
          * (((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k
              (Localization (Submonoid.powers (detProd (k := k) m))))).map ιB)
          * ((genMatB (k := k)
              (B := Localization (Submonoid.powers (detProd (k := k) m))) m w.1).map ιB)⁻¹)
            w.2.2.2.1 w.2.2.2.2 := by
      rw [hφ, AlgHom.comp_apply, orbitComorphism_X, ← hmatrix, Matrix.map_apply]
    rw [hexp]
    exact (Matrix.map_apply).symm.trans
      (congrFun (congrFun (map_smul_conj_eq (gidxScaleK m μ) μ'
        (hAscale w.2.1) hVfix (hAscale w.1) hCdet) _) _)
  -- feed the abstract `−1` core
  exact card_lt_of_scaleInvariant_image_fractionRing φ hφ_inj g hg
    (fun μ => gidxScaleK m μ) hscale_g hscale_f

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
