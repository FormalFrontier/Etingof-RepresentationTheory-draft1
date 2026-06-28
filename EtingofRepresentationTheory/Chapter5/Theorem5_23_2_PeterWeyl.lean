import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.LocalizationGLBiAction
import EtingofRepresentationTheory.Chapter5.PeterWeylMatrixCoeff
import EtingofRepresentationTheory.Chapter5.MatrixCoeffInjective
import EtingofRepresentationTheory.Chapter5.CrossSummandMatrixCoeff
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLNonIso
import EtingofRepresentationTheory.Chapter5.RightTranslationHull
import EtingofRepresentationTheory.Chapter5.RightTranslationHullDecomp

/-!
# Theorem 5.23.2(ii): the genuine `GL_n × GL_n`-equivariant Peter-Weyl decomposition

`Theorem5_23_2.lean` states part (ii) only as a *bare `k`-linear* rank-matching
isomorphism `R ≃ₗ[k] ⊕_λ L*_λ ⊗ L_λ` — true for any two countably-infinite-dim
free modules, carrying no representation-theoretic content. This file states the
genuine theorem: a **`GL_n × GL_n`-equivariant** isomorphism

  `R ≅ ⊕_λ L*_λ ⊗ L_λ`   as representations of `GL_n × GL_n`,

where `R = k[gᵢⱼ][1/det] = Localization.Away (detPoly k n)` is the coordinate ring
with its left/right translation bi-action (`localBiRep`, `LocalizationGLBiAction.lean`),
`L_λ = AlgIrrepGL` carries the det-twisted Schur-module action (`algIrrepGLRepρ`,
`AlgIrrepGLRep.lean`), `L*_λ = AlgIrrepGLDual` its contragredient
(`algIrrepGLRepDualρ`), and the action on the summand `L*_λ ⊗ L_λ` is the left
factor on `L*_λ` (via the first `GL_n`) and the right factor on `L_λ` (via the
second `GL_n`).

The right-hand-side representation `peterWeylRHS` is assembled with
`Representation.tprod` and `Representation.directSum`. The candidate isomorphism
`peterWeylMap : peterWeylRHS → R` is assembled here from the per-summand
matrix-coefficient maps `peterWeylSummandMap` (`PeterWeylMatrixCoeff.lean`) via
`DirectSum.toModule`, and its `GL_n × GL_n`-equivariance (`peterWeylMap_equivariant`)
is assembled from the per-summand equivariance. This reduces the capstone
`Theorem5_23_2_ii_equivariant` to a single bijectivity statement
`peterWeylMap_bijective` (the Cauchy decomposition,
`PolynomialGLDecomposition.lean` / `CauchyDetQuotient*`), which is the sole remaining
`sorry` and is being assembled separately.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof

open Etingof.LocalizationGLAction Etingof.DetLocalization

variable {k : Type*}

/-- **The right-hand side of Peter-Weyl as a `GL_n × GL_n`-representation.**
`⊕_λ L*_λ ⊗ L_λ`, where the first `GL_n` acts on the `L*_λ` factor (via
`MonoidHom.fst`) and the second `GL_n` acts on the `L_λ` factor (via
`MonoidHom.snd`). Built from `Representation.tprod` over each summand and
`Representation.directSum` over all dominant weights. -/
noncomputable def peterWeylRHS (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] :
    Representation k
      (Matrix.GeneralLinearGroup (Fin n) k × Matrix.GeneralLinearGroup (Fin n) k)
      (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) :=
  Representation.directSum fun lam =>
    Representation.tprod
      ((algIrrepGLRepDualρ n lam k).comp (MonoidHom.fst _ _))
      ((algIrrepGLRepρ n lam k).comp (MonoidHom.snd _ _))

@[simp] theorem peterWeylRHS_apply (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k]
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (x : DirectSum (DominantWeight n) fun lam =>
      (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) :
    peterWeylRHS n k (g, h) x =
      DirectSum.lmap (fun lam =>
        TensorProduct.map (algIrrepGLRepDualρ n lam k g) (algIrrepGLRepρ n lam k h)) x :=
  rfl

/-- A `GL_n × GL_n`-equivariant `k`-linear isomorphism between two representations:
a linear equivalence intertwining the two actions. (The full content of the
Peter-Weyl statement lives in the equivariance condition; without it the bare
linear equivalence is vacuous, as the rank iso in `Theorem5_23_2.lean` shows.) -/
def IsEquivariantEquiv {G W₁ W₂ : Type*} [Monoid G] [Field k]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    (ρ₁ : Representation k G W₁) (ρ₂ : Representation k G W₂)
    (e : W₁ ≃ₗ[k] W₂) : Prop :=
  ∀ (g : G) (x : W₁), e (ρ₁ g x) = ρ₂ g (e x)

/-- The inverse of an equivariant equivalence is equivariant for the reversed
pair. The matrix-coefficient map of Peter-Weyl is naturally built in the
`peterWeylRHS → R` direction (`u ⊗ v ↦` matrix coefficient); this lemma transports
its equivariance to the `R ≃ peterWeylRHS` direction demanded by
`Theorem5_23_2_ii_equivariant`. -/
theorem IsEquivariantEquiv.symm {G W₁ W₂ : Type*} [Monoid G] [Field k]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    {ρ₁ : Representation k G W₁} {ρ₂ : Representation k G W₂}
    {e : W₁ ≃ₗ[k] W₂} (he : IsEquivariantEquiv ρ₁ ρ₂ e) :
    IsEquivariantEquiv ρ₂ ρ₁ e.symm := by
  intro g y
  apply e.injective
  rw [e.apply_symm_apply, he g (e.symm y), e.apply_symm_apply]

/-- Decidable equality on dominant weights (the underlying type is a subtype of the
finite-support function type `Fin n → ℤ`). Needed for the `DirectSum.of`/`toModule`
API on `⊕_λ`, which `Representation.directSum` (using only `DirectSum.lmap`) sidesteps. -/
instance instDecidableEqDominantWeight (n : ℕ) : DecidableEq (DominantWeight n) :=
  inferInstanceAs (DecidableEq {lam : Fin n → ℤ // Antitone lam})

/-- **The assembled direct-sum matrix-coefficient map** `⊕_λ L*_λ ⊗ L_λ →ₗ[k] R`.
Built from the per-summand maps `peterWeylSummandMap` (`PeterWeylMatrixCoeff.lean`)
via `DirectSum.toModule`. This is the candidate Peter-Weyl isomorphism, in the
`peterWeylRHS → R` direction (matrix coefficients `u ⊗ v ↦ (g ↦ ⟨u, ρ(g) v⟩)`). -/
noncomputable def peterWeylMap (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) →ₗ[k]
      Localization.Away (detPoly k n) :=
  DirectSum.toModule k (DominantWeight n) _ (fun lam => peterWeylSummandMap n lam k)

@[simp] theorem peterWeylMap_of (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) (y : AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k) :
    peterWeylMap n k (DirectSum.of _ lam y) = peterWeylSummandMap n lam k y := by
  unfold peterWeylMap
  erw [DirectSum.toModule_lof]

/-- The per-summand equivariance, extended from pure tensors to all of `L*_λ ⊗ L_λ`
by linearity: the per-summand map intertwines the summand action
`ρ*(g) ⊗ ρ(h)` (as `TensorProduct.map`) with the bi-action `localBiRep`. -/
theorem peterWeylSummandMap_map_equivariant (n : ℕ) (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (y : AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k) :
    peterWeylSummandMap n lam k
        (TensorProduct.map (algIrrepGLRepDualρ n lam k g) (algIrrepGLRepρ n lam k h) y)
      = localBiRep k n (g, h) (peterWeylSummandMap n lam k y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [TensorProduct.map_tmul]
      exact peterWeylSummandMap_equivariant n lam k g h u v
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **`GL_n × GL_n`-equivariance of the assembled map.** `peterWeylMap` intertwines
the right-hand-side representation `peterWeylRHS` with the left/right-translation
bi-action `localBiRep`. Assembled summand-by-summand from
`peterWeylSummandMap_equivariant`, since `peterWeylRHS` acts as `DirectSum.lmap` of
the per-summand `TensorProduct.map` actions. -/
theorem peterWeylMap_equivariant (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (x : DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) :
    peterWeylMap n k (peterWeylRHS n k (g, h) x)
      = localBiRep k n (g, h) (peterWeylMap n k x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of lam y =>
      rw [peterWeylRHS_apply, DirectSum.lmap_of, peterWeylMap_of, peterWeylMap_of]
      exact peterWeylSummandMap_map_equivariant n k lam g h y
  | add x₁ x₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-- **Reduction of the Peter-Weyl capstone to a single bijectivity statement.**
Given that the assembled matrix-coefficient map `peterWeylMap` is bijective,
`LinearEquiv.ofBijective` upgrades it to a `k`-linear equivalence `peterWeylRHS ≃ R`;
its inverse `R ≃ peterWeylRHS` is the equivalence demanded by
`Theorem5_23_2_ii_equivariant`, and `peterWeylMap_equivariant` (transported across
`IsEquivariantEquiv.symm`) supplies the intertwining. Thus the only remaining
representation-theoretic input is the Cauchy bijectivity of `peterWeylMap`. -/
theorem nonempty_equivariantEquiv_of_bijective
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (hbij : Function.Bijective (peterWeylMap n k)) :
    Nonempty { e : Localization.Away (detPoly k n) ≃ₗ[k]
        (DirectSum (DominantWeight n) fun lam =>
          (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) //
      IsEquivariantEquiv (localBiRep k n) (peterWeylRHS n k) e } := by
  let e := LinearEquiv.ofBijective (peterWeylMap n k) hbij
  have he : IsEquivariantEquiv (peterWeylRHS n k) (localBiRep k n) e := by
    intro gh x
    obtain ⟨g, h⟩ := gh
    change peterWeylMap n k (peterWeylRHS n k (g, h) x)
      = localBiRep k n (g, h) (peterWeylMap n k x)
    exact peterWeylMap_equivariant n k g h x
  exact ⟨e.symm, he.symm⟩

/-- **Assembly lemma (pure linear algebra): a direct-sum coproduct is injective when each
summand map is injective and their ranges are independent.** If `f i : N i →ₗ M` is injective
for every `i` and the family of ranges `range (f i)` is `iSupIndep`, then the coproduct
`DirectSum.toModule R ι M f : (⨁ i, N i) →ₗ M` is injective.

Proof: corestrict each `f i` to its range, `f i = (range (f i)).subtype ∘ rangeRestrict (f i)`.
Then `toModule R ι M f = (lsum (subtype)) ∘ (mapRange rangeRestrict)`. The right factor is
injective because each `rangeRestrict (f i)` is (injectivity of `f i`); the left factor is
injective by `iSupIndep.dfinsupp_lsum_injective`. This is the structural skeleton of
Peter-Weyl injectivity: the two genuinely representation-theoretic facts it consumes are the
per-summand injectivity and the independence of the ranges. -/
theorem injective_toModule_of_iSupIndep_range
    {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι]
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    {M : Type*} [AddCommGroup M] [Module R M]
    (f : ∀ i, N i →ₗ[R] M) (hf : ∀ i, Function.Injective (f i))
    (hindep : iSupIndep (fun i => LinearMap.range (f i))) :
    Function.Injective (DirectSum.toModule R ι M f) := by
  -- `f i` factors as `subtype ∘ rangeRestrict`.
  have hfeq : (fun i => ((LinearMap.range (f i)).subtype).comp ((f i).rangeRestrict)) = f := by
    funext i; exact LinearMap.subtype_comp_codRestrict (f i) _ _
  -- `toModule f = (lsum subtype) ∘ (mapRange rangeRestrict)` pointwise.
  have hcomp : ∀ x, DirectSum.toModule R ι M f x
      = (DFinsupp.lsum ℕ (fun i => (LinearMap.range (f i)).subtype))
          (DFinsupp.mapRange.linearMap (fun i => (f i).rangeRestrict) x) := by
    intro x
    rw [DFinsupp.sum_mapRange_index.linearMap, hfeq]
    rfl
  -- Left factor injective: ranges are independent.
  have h1 : Function.Injective
      (DFinsupp.lsum ℕ (fun i => (LinearMap.range (f i)).subtype)) :=
    hindep.dfinsupp_lsum_injective
  -- Right factor injective: each corestriction is injective.
  have h2 : Function.Injective
      (DFinsupp.mapRange.linearMap (fun i => (f i).rangeRestrict)) := by
    have hcoe : ⇑(DFinsupp.mapRange.linearMap (fun i => (f i).rangeRestrict))
        = DFinsupp.mapRange (fun i => ⇑((f i).rangeRestrict)) (fun i => map_zero _) := rfl
    rw [hcoe, DFinsupp.mapRange_injective]
    refine fun i => LinearMap.ker_eq_bot.mp ?_
    rw [LinearMap.ker_rangeRestrict]
    exact LinearMap.ker_eq_bot.mpr (hf i)
  intro a b hab
  apply h2
  apply h1
  rw [← hcomp, ← hcomp, hab]

/-- **Pure linear algebra: the range of a `DirectSum.toModule` coproduct is the supremum of the
per-summand ranges.** `range (DirectSum.toModule R ι M f) = ⨆ i, range (f i)`. The forward
inclusion runs over the `DirectSum.induction_on` generators (each `of i y ↦ f i y` via
`DirectSum.toModule_lof`); the reverse factors `f i = (toModule f) ∘ lof i`, so each summand range
is `≤` the coproduct range (`LinearMap.range_comp_le_range`). This is the surjectivity counterpart
of `injective_toModule_of_iSupIndep_range`: it reduces `peterWeylMap` surjectivity to the spanning
statement `⨆_λ range (peterWeylSummandMap n λ k) = ⊤`. -/
theorem range_toModule_eq_iSup_range
    {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (f : ∀ i, N i →ₗ[R] M) :
    LinearMap.range (DirectSum.toModule R ι M f) = ⨆ i, LinearMap.range (f i) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨a, rfl⟩ := hx
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i y =>
        have hval : DirectSum.toModule R ι M f (DirectSum.of N i y) = f i y := by
          erw [DirectSum.toModule_lof]
        rw [hval]
        exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ _)
    | add a b ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  · rw [iSup_le_iff]
    intro i
    have hfi : f i = (DirectSum.toModule R ι M f).comp (DirectSum.lof R ι N i) :=
      LinearMap.ext fun y => (DirectSum.toModule_lof R i y).symm
    rw [hfi]
    exact LinearMap.range_comp_le_range _ _

/-- **General-`k`, all-weights simplicity of `L_λ` as a `k[GL_n]`-module (issue #5559).**
`algIrrepGLRepρ n lam k` is the `det^{-λ.shift}`-twist of the Schur module
`schurModuleRep k n lam.toNatWeight`; det-twisting preserves simplicity
(`isSimpleModule_charTwistRep`), so this reduces to general-`k`, all-weights Schur-module
simplicity `schurModule_isSimple_general` (no `∑ λ ≤ n` degree guard needed). This lifts
the `ℂ`-only, degree-constrained `algIrrepGLRep_isSimple` (`AlgIrrepGLRep.lean`) to a
general algebraically-closed characteristic-zero field, and is the shared simplicity input
for `peterWeylSummandMap_injective` (#5555), `peterWeylSummandMap_range_iSupIndep` (#5556),
and `peterWeylMap_injective` (#5549). -/
theorem algIrrepGLRepρ_isSimpleModule (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (algIrrepGLRepρ n lam k).asModule := by
  haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule (schurModuleRep k n lam.toNatWeight)) :=
    schurModule_isSimple_general k n lam.toNatWeight lam.toNatWeight_antitone
  unfold algIrrepGLRepρ
  exact isSimpleModule_charTwistRep _ (schurModuleRep k n lam.toNatWeight)

/-- **Per-summand injectivity (within-summand Schur orthogonality / Burnside density).**
The single-irreducible matrix-coefficient map `peterWeylSummandMap n lam k : L*_λ ⊗ L_λ →ₗ R`,
`u ⊗ v ↦ (g ↦ ⟨u, ρ_λ(g) v⟩)`, is injective: the matrix coefficients of one irreducible are
linearly independent.

Read through the faithful functions-on-`GL` model `evalGLAway_peterWeylSummandMap`, a nonzero
`z = ∑ uᵢ ⊗ vᵢ` in the kernel gives a linear functional `T ↦ ∑ ⟨uᵢ, T vᵢ⟩` on `End_k(L_λ)`
that vanishes on every `ρ_λ(g)`; by Burnside density (the image of the group algebra in
`End_k(L_λ)` is everything, since `L_λ` is simple and `k` is algebraically closed —
`Module.Finite.toModuleEnd_moduleEnd_surjective`) the functional vanishes on all of
`End_k(L_λ)`, and nondegeneracy of the contragredient pairing
(`algIrrepDualPairing_nondegenerate`) forces `z = 0`.

The representation-theoretic content (Burnside density + trace-form nondegeneracy) is
discharged sorry-free by the abstract engine
`matrixCoeff_injective_of_isSimpleModule` (`MatrixCoeffInjective.lean`): a kernel
element `z`, read through the unconditional contragredient iso `algIrrepGLDualIso`
into `Module.Dual k L_λ ⊗ L_λ`, satisfies `contractLeft (id ⊗ ρ g) z' = 0` for every
`g` (the matrix-coefficient identity `evalGLAway_peterWeylSummandMap`); Burnside
density (`Representation.span_range_eq_top_of_isSimpleModule`, from Schur over
`IsAlgClosed k` plus Jacobson density) and trace nondegeneracy then force `z' = 0`.

The general-`k`, all-weights simplicity of `L_λ` as a `k[GL_n]`-module — the lift of the
`ℂ`-only, degree-constrained `algIrrepGLRep_isSimple` — is supplied sorry-free by
`algIrrepGLRepρ_isSimpleModule` (above, issue #5559), so this proof is now sorry-free. -/
theorem peterWeylSummandMap_injective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) :
    Function.Injective (peterWeylSummandMap n lam k) := by
  -- General-`k`, all-weights simplicity of `L_λ` (issue #5559), factored above.
  haveI hsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (algIrrepGLRepρ n lam k).asModule := algIrrepGLRepρ_isSimpleModule n k lam
  rw [injective_iff_map_eq_zero]
  intro z hz
  -- Transport the kernel element into `Module.Dual k L_λ ⊗ L_λ`.
  set z' : Module.Dual k (AlgIrrepGL n lam k) ⊗[k] AlgIrrepGL n lam k :=
    TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap LinearMap.id z with hz'
  -- Matrix-coefficient identity in transported form, for an arbitrary tensor `w`.
  have key : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k)
      (w : AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k),
      contractLeft k (AlgIrrepGL n lam k)
          (TensorProduct.map LinearMap.id (algIrrepGLRepρ n lam k g)
            (TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap LinearMap.id w))
        = evalGLAway (peterWeylSummandMap n lam k w) g := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
          evalGLAway_peterWeylSummandMap, algIrrepDualPairing_tmul]
        rfl
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  -- The transported element satisfies the Burnside hypothesis.
  have hcond : ∀ g, contractLeft k (AlgIrrepGL n lam k)
      (TensorProduct.map LinearMap.id (algIrrepGLRepρ n lam k g) z') = 0 := by
    intro g
    rw [hz', key g z, hz, map_zero, Pi.zero_apply]
  -- Burnside density + trace nondegeneracy: `z' = 0`, hence `z = 0`.
  have hz'0 : z' = 0 :=
    matrixCoeff_injective_of_isSimpleModule (algIrrepGLRepρ n lam k) z' hcond
  have hinj : Function.Injective (TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap
      (LinearMap.id : AlgIrrepGL n lam k →ₗ[k] AlgIrrepGL n lam k)) := by
    have hmap : TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap
        (LinearMap.id : AlgIrrepGL n lam k →ₗ[k] AlgIrrepGL n lam k)
        = (TensorProduct.congr (algIrrepGLDualIso n lam k)
            (LinearEquiv.refl k (AlgIrrepGL n lam k))).toLinearMap := by
      rw [TensorProduct.toLinearMap_congr]; rfl
    rw [hmap]
    exact (TensorProduct.congr (algIrrepGLDualIso n lam k) _).injective
  apply hinj
  rw [map_zero]
  exact hz'.symm.trans hz'0

/-- **Transported matrix-coefficient identity.** The contraction of `id ⊗ ρ_λ(g)` against the
contragredient-transported tensor `(algIrrepGLDualIso ⊗ id) w` reads off the matrix coefficient
of `w` through the faithful functions-on-`GL` model `evalGLAway`. This is the per-`g` bridge that
feeds the abstract cross-summand engine `crossMatrixCoeff_indep_finset`; it is the
single-summand `key` of `peterWeylSummandMap_injective`, factored for reuse across summands. -/
theorem evalGLAway_peterWeylSummandMap_contractLeft
    (n : ℕ) (lam : DominantWeight n) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (w : AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k) :
    contractLeft k (AlgIrrepGL n lam k)
        (TensorProduct.map LinearMap.id (algIrrepGLRepρ n lam k g)
          (TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap LinearMap.id w))
      = evalGLAway (peterWeylSummandMap n lam k w) g := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
        evalGLAway_peterWeylSummandMap, algIrrepDualPairing_tmul]
      rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/-- **Finite-family matrix-coefficient independence across summands.** If a finite sum of
per-summand matrix coefficients vanishes in `R`, then each summand vanishes. This is the
representation-theoretic core: through `evalGLAway` (faithful) and the transported identity
above, the hypothesis becomes the abstract cross-summand hypothesis fed to
`crossMatrixCoeff_indep_finset` (simplicity `algIrrepGLRepρ_isSimpleModule` + non-isomorphism
`algIrrepGLRepρ_noniso`), which forces the transported tensors to vanish; `evalGLAway`
injectivity then forces each summand map value to vanish. -/
theorem peterWeylSummandMap_finsetSum_eq_zero
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (s : Finset (DominantWeight n))
    (z : ∀ lam, AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)
    (hsum : ∑ lam ∈ s, peterWeylSummandMap n lam k (z lam) = 0) :
    ∀ lam ∈ s, peterWeylSummandMap n lam k (z lam) = 0 := by
  -- The transported tensors `(algIrrepGLDualIso ⊗ id)(z lam)` vanish, by the abstract engine.
  have hzero : ∀ lam ∈ s,
      TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap LinearMap.id (z lam) = 0 := by
    intro lam0 hlam0
    refine crossMatrixCoeff_indep_finset (k := k)
      (G := Matrix.GeneralLinearGroup (Fin n) k)
      (fun lam => AlgIrrepGL n lam k) (fun lam => algIrrepGLRepρ n lam k) s
      (fun lam => algIrrepGLRepρ_isSimpleModule n k lam)
      (fun lam _ mu _ hne => algIrrepGLRepρ_noniso n k hne)
      (fun lam => TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap LinearMap.id (z lam))
      ?_ lam0 hlam0
    intro g
    have hterm : ∀ lam ∈ s, contractLeft k (AlgIrrepGL n lam k)
        (TensorProduct.map LinearMap.id (algIrrepGLRepρ n lam k g)
          (TensorProduct.map (algIrrepGLDualIso n lam k).toLinearMap LinearMap.id (z lam)))
        = evalGLAway (peterWeylSummandMap n lam k (z lam)) g :=
      fun lam _ => evalGLAway_peterWeylSummandMap_contractLeft n lam k g (z lam)
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_apply, ← map_sum, hsum, map_zero]
    rfl
  -- A vanishing transported tensor forces the summand value to vanish (`evalGLAway` injective).
  intro lam0 hlam0
  apply evalGLAway_injective
  funext g
  rw [← evalGLAway_peterWeylSummandMap_contractLeft n lam0 k g (z lam0), hzero lam0 hlam0]
  simp

/-- **Cross-summand independence (distinct-irreducible Schur orthogonality).** The ranges of
the per-summand maps `peterWeylSummandMap n lam k` (the matrix coefficients of `L_λ` inside `R`)
form an `iSupIndep` family: matrix coefficients of pairwise non-isomorphic irreducibles are
linearly independent across distinct weights.

The argument lives entirely on the right `GL_n`-action: through the faithful functions-on-`GL`
model `evalGLAway`, a finite vanishing combination of matrix coefficients of the simple,
pairwise non-isomorphic `L_λ` is killed by the abstract Jacobson-density engine
`crossMatrixCoeff_indep_finset` (no external-tensor `GL_n × GL_n` simplicity needed). The two
representation-theoretic inputs are the general-`k` simplicity `algIrrepGLRepρ_isSimpleModule`
(#5559) and the highest-weight non-isomorphism `algIrrepGLRepρ_noniso`. This is the
across-summand half of Peter-Weyl orthogonality. -/
theorem peterWeylSummandMap_range_iSupIndep
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    iSupIndep (fun lam => LinearMap.range (peterWeylSummandMap n lam k)) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum
  -- Choose a preimage `z lam` with `peterWeylSummandMap (z lam) = v lam` for each `lam ∈ s`.
  set z : ∀ lam, AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k :=
    fun lam => if h : lam ∈ s then (LinearMap.mem_range.mp (hv lam h)).choose else 0 with hzdef
  have hzv : ∀ lam ∈ s, peterWeylSummandMap n lam k (z lam) = v lam := by
    intro lam h
    simp only [z, dif_pos h]
    exact (LinearMap.mem_range.mp (hv lam h)).choose_spec
  have hsum' : ∑ lam ∈ s, peterWeylSummandMap n lam k (z lam) = 0 := by
    rw [Finset.sum_congr rfl hzv]; exact hsum
  intro lam0 hlam0
  rw [← hzv lam0 hlam0]
  exact peterWeylSummandMap_finsetSum_eq_zero n k s z hsum' lam0 hlam0

/-- **Injectivity of the assembled matrix-coefficient map** — distinct-irreducible
orthogonality (Schur orthogonality across summands). `peterWeylMap` is the direct-sum coproduct
`DirectSum.toModule` of the per-summand maps `peterWeylSummandMap`; by the pure-linear-algebra
assembly `injective_toModule_of_iSupIndep_range` it is injective once each per-summand map is
injective (`peterWeylSummandMap_injective`, within-summand Burnside density) and the ranges are
independent (`peterWeylSummandMap_range_iSupIndep`, across-summand orthogonality).

This is one of the two genuine Cauchy/Peter-Weyl halves of `peterWeylMap_bijective`. The two
representation-theoretic inputs both currently rest on the simplicity infrastructure
(`algIrrepGLRep_isSimple`, presently `ℂ`-only and degree-constrained, with the general route
tracked in `progress/schurModule-isSimple-general-route.md`, issue #4946). Tracked as #5549. -/
theorem peterWeylMap_injective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Function.Injective (peterWeylMap n k) :=
  injective_toModule_of_iSupIndep_range _
    (peterWeylSummandMap_injective n k) (peterWeylSummandMap_range_iSupIndep n k)

set_option maxHeartbeats 800000 in
/-- **Right-translation stability of a per-summand range.** Each
`LinearMap.range (peterWeylSummandMap n lam k)` (the `L_λ`-isotypic matrix coefficients) is stable
under right translation `localRightRep k n g`: right translation acts within the summand as the
`L_λ`-action `algIrrepGLRepρ n lam k g`, which is the `(1, g)`-specialization of the bi-equivariance
`peterWeylSummandMap_equivariant`. -/
theorem localRightRep_mapsTo_range_peterWeylSummandMap
    (n : ℕ) (lam : DominantWeight n) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    ∀ x ∈ LinearMap.range (peterWeylSummandMap n lam k),
      localRightRep k n g x ∈ LinearMap.range (peterWeylSummandMap n lam k) := by
  -- `localBiRep (1, g)` is just `localRightRep g`.
  have hbi1 : ∀ w, localBiRep k n (1, g) w = localRightRep k n g w := by
    intro w
    rw [localBiRep_apply, ← localLeftRep_apply, map_one, Module.End.one_apply,
      ← localRightRep_apply]
  -- The defining intertwining identity: `R_g ∘ pwsm = pwsm ∘ (id ⊗ ρ(g))`.
  have key : ∀ z, peterWeylSummandMap n lam k
        (TensorProduct.map LinearMap.id (algIrrepGLRepρ n lam k g) z)
      = localRightRep k n g (peterWeylSummandMap n lam k z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
      have he := peterWeylSummandMap_equivariant n lam k 1 g u v
      rw [show algIrrepGLRepDualρ n lam k 1 u = u from by rw [map_one]; rfl] at he
      rw [he, hbi1]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rintro _ ⟨z, rfl⟩
  exact ⟨TensorProduct.map LinearMap.id (algIrrepGLRepρ n lam k g) z, key z⟩

/-- **The full matrix-coefficient span is right-translation stable.** The supremum
`⨆_λ range (peterWeylSummandMap n λ k)` is a `localRightRep`-invariant subspace of `R`, being a
join of the right-stable per-summand ranges. -/
theorem localRightRep_mem_iSup_range_peterWeylSummandMap
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    ∀ x ∈ (⨆ lam, LinearMap.range (peterWeylSummandMap n lam k)),
      localRightRep k n g x ∈ ⨆ lam, LinearMap.range (peterWeylSummandMap n lam k) := by
  intro x hx
  refine Submodule.iSup_induction
    (fun lam => LinearMap.range (peterWeylSummandMap n lam k))
    (motive := fun y => localRightRep k n g y ∈
      ⨆ lam, LinearMap.range (peterWeylSummandMap n lam k)) hx ?_ ?_ ?_
  · intro lam y hy
    exact Submodule.mem_iSup_of_mem lam
      (localRightRep_mapsTo_range_peterWeylSummandMap n lam k g y hy)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

/-- **Realization core.** A simple, finite-dimensional `localRightRep`-subrepresentation `S` of
`R = Localization.Away (detPoly k n)` is realized by a concrete dominant weight: there is a
`λ : DominantWeight n` and a `GL_n`-equivariant `k`-linear map
`ι : AlgIrrepGL n λ k →ₗ[k] R` intertwining `algIrrepGLRepρ n λ k` with the right-translation
action `localRightRep`, whose range is exactly `S.toSubmodule`.

This is the genuinely missing highest-weight-classification step of the Cauchy/Peter-Weyl
spanning argument. Its construction (issue #5599): pick a common denominator exponent `r` so that
`det^r · S ⊆ A = k[Xᵢⱼ]` (`exists_invSelf_normalForm` on a basis of `S`); the `det^r`-multiplication
map intertwines `localRightRep` on `S` with right translation on a finite-dimensional space of
polynomials, exhibiting `M := charTwistRep (detChar^r) S.toRepresentation` as a simple, algebraic
(`boundedRightRep_isAlgebraic`), weight-spanning, single-degree-homogeneous polynomial
`GL_n`-representation. By `decompose_polynomial_gl_rep` together with simplicity its formal
character is a single Schur polynomial `schurPoly N ν`, so `iso_of_formalCharacter_eq_schurPoly`
gives a `GL_n`-equivariant iso `M ≅ SchurModule k n ν`. Setting `λ.val := ν − r` (with
`λ.shift = r`, so `λ.toNatWeight = ν`) and untwisting by `det^{-r}` produces the equivariant iso
`AlgIrrepGL n λ k ≃ S`; composing with the inclusion `S ↪ R` yields `ι`. -/
theorem exists_dominantWeight_equivariant_realization
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (localRightRep k n))
    [FiniteDimensional k S.toSubmodule]
    (hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S)) :
    ∃ (lam : DominantWeight n) (ι : AlgIrrepGL n lam k →ₗ[k] Localization.Away (detPoly k n)),
      (∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGL n lam k),
        ι (algIrrepGLRepρ n lam k g v) = localRightRep k n g (ι v)) ∧
      LinearMap.range ι = S.toSubmodule := by
  sorry

/-- **Realization of a simple right-translation subrepresentation as a matrix-coefficient block.**
Every simple, finite-dimensional `localRightRep`-subrepresentation `S` of
`R = Localization.Away (detPoly k n)` lies in the supremum
`⨆_λ range (peterWeylSummandMap n λ k)` of the per-summand matrix-coefficient ranges.

By the realization core `exists_dominantWeight_equivariant_realization`, `S.toSubmodule` is the range
of a `GL_n`-equivariant `ι : AlgIrrepGL n λ k →ₗ[k] R`; the step-4 correspondence
`equivariant_range_le_peterWeylSummandMap` (#5578) places that range inside
`range (peterWeylSummandMap n λ k) ≤ ⨆_λ …`. -/
theorem simpleSubrep_localRightRep_le_iSup_range
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (localRightRep k n))
    [FiniteDimensional k S.toSubmodule]
    (hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S)) :
    S.toSubmodule ≤ ⨆ lam, LinearMap.range (peterWeylSummandMap n lam k) := by
  obtain ⟨lam, ι, hι_equiv, hrange⟩ :=
    exists_dominantWeight_equivariant_realization n k S hSsimple
  rw [← hrange]
  exact (equivariant_range_le_peterWeylSummandMap n lam k ι hι_equiv).trans
    (le_iSup (fun lam => LinearMap.range (peterWeylSummandMap n lam k)) lam)

/-- **Hull-spanning bridge (the remaining Cauchy obligation, steps 2–4).** Every element of the
finite-dimensional right-translation hull `rightHull φ` of `φ ∈ R = Localization.Away (detPoly k n)`
lies in the supremum `⨆_λ range (peterWeylSummandMap n λ k)` of the per-summand matrix-coefficient
ranges.

**Intended proof route.** The hull `rightHull φ`, with the right-translation action `localRightRep`,
is a finite-dimensional semisimple `k[GL_n]`-module (`rightHull_isSemisimple`, #5577). Decompose it
into simple submodules (`IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp` /
`SimpleSubrepExtraction.exists_isSimpleModule_le`); it suffices to show each simple submodule
`S ≤ rightHull φ` lies in `⨆_λ range (peterWeylSummandMap n λ k)`, since `rightHull φ` is their
join and the supremum is a submodule.

For a single simple submodule `S`: `S` is a simple algebraic `GL_n`-representation (a constituent of
the algebraic hull), so by the highest-weight classification
(`iso_of_formalCharacter_eq_schurPoly`, identifying a simple with a Schur module / `AlgIrrepGL`
through its formal character) there is a dominant weight `λ` and a `GL_n`-equivariant linear
isomorphism `e : AlgIrrepGL n λ k ≃ₗ[k] S` intertwining `algIrrepGLRepρ n λ k` with the
`localRightRep`-action on `S`. Composing with the (equivariant) inclusion `S ↪ R` yields a
`GL_n`-equivariant map `ι : AlgIrrepGL n λ k →ₗ[k] R` intertwining `algIrrepGLRepρ` with
`localRightRep`, whence `S = range ι ≤ range (peterWeylSummandMap n λ k)` by the step-4
correspondence `equivariant_range_le_peterWeylSummandMap` (#5578). Summing over the simple
constituents gives `rightHull φ ≤ ⨆_λ range (peterWeylSummandMap n λ k)`.

**Status.** The genuinely missing infrastructure is the *realization* step: turning a simple
constituent `S ≤ R` of the hull into a concrete `λ` together with the equivariant isomorphism
`AlgIrrepGL n λ k ≃ S` (the highest-weight classification wired to submodules of `R`). The
semisimplicity (#5577) and the matrix-coefficient correspondence (#5578) are in place; this lemma
records the remaining obligation as a single isolated statement. -/
theorem rightHull_le_iSup_range_peterWeylSummandMap
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (φ : Localization.Away (detPoly k n)) :
    RightTranslationHull.rightHull φ ≤
      ⨆ lam, LinearMap.range (peterWeylSummandMap n lam k) := by
  classical
  set T : Submodule k (Localization.Away (detPoly k n)) :=
    ⨆ lam, LinearMap.range (peterWeylSummandMap n lam k) with hT
  -- `T` is `localRightRep`-stable, so it packages as a `k[GL_n]`-submodule of `R`.
  have hT_stable : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k),
      ∀ x ∈ T, localRightRep k n g ((localRightRep k n).asModuleEquiv x) ∈ T := by
    intro g x hx
    exact localRightRep_mem_iSup_range_peterWeylSummandMap n k g x hx
  set T_KG : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (localRightRep k n).asModule :=
    Representation.stableSubmodule (localRightRep k n) T hT_stable with hTKG
  have hTKG_restrict : T_KG.restrictScalars k = T := by
    apply SetLike.ext; intro x
    rw [Submodule.restrictScalars_mem, hTKG, Representation.mem_stableSubmodule]
  -- The hull as a subrepresentation, finite-dimensional and semisimple.
  set H : Subrepresentation (localRightRep k n) := RightTranslationHull.rightHullSubrep φ with hH
  haveI hfin : FiniteDimensional k (RightTranslationHull.rightHull φ) :=
    RightTranslationHull.rightHull_finiteDimensional φ
  haveI hss := RightTranslationHull.rightHull_isSemisimple k φ
  -- The `k[GL_n]`-linear inclusion `asModule H.toRepresentation ↪ asModule (localRightRep)`.
  have hsub : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (x : H.toSubmodule),
      H.toSubmodule.subtype (H.toRepresentation g x)
        = localRightRep k n g (H.toSubmodule.subtype x) :=
    fun g x => LinearMap.restrict_coe_apply (localRightRep k n g)
      (H.apply_mem_toSubmodule g) x
  set incl :
      Representation.asModule H.toRepresentation →ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)] Representation.asModule (localRightRep k n) :=
    Representation.asModuleHomOfIntertwiner H.toSubmodule.subtype hsub with hincl
  have hincl_apply : ∀ x, incl x = H.toSubmodule.subtype x := fun x => rfl
  -- `range incl` (as `k`-submodule) is exactly the hull.
  have hrange_restrict : (LinearMap.range incl).restrictScalars k
      = RightTranslationHull.rightHull φ := by
    have hset : (LinearMap.range incl).restrictScalars k
        = LinearMap.range H.toSubmodule.subtype := by
      apply SetLike.ext; intro x
      rw [Submodule.restrictScalars_mem, LinearMap.mem_range, LinearMap.mem_range]
      constructor
      · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩
      · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩
    rw [hset, Submodule.range_subtype]; rfl
  -- Each simple `k[GL_n]`-submodule `p` of `asModule H.toRep` maps into `T_KG`.
  have hbound : ∀ p ∈ {m : Submodule (MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin n) k)) (Representation.asModule H.toRepresentation) |
      IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) m},
      Submodule.map incl p ≤ T_KG := by
    intro p hp
    -- `incl` is injective (it is the subtype inclusion).
    have hincl_inj : Function.Injective incl := by
      intro a b hab
      apply Subtype.coe_injective
      have : H.toSubmodule.subtype a = H.toSubmodule.subtype b := by
        rw [← hincl_apply, ← hincl_apply, hab]
      simpa using this
    -- `map incl p ≅ p` is simple, and lies inside the (finite-dimensional) hull.
    have hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
        (Subrepresentation.asSubmodule
          (Subrepresentation.ofSubmodule' (Submodule.map incl p))) :=
      (LinearEquiv.isSimpleModule_iff (Submodule.equivMapOfInjective incl hincl_inj p)).mp hp
    have hSsub : (Subrepresentation.ofSubmodule' (Submodule.map incl p)).toSubmodule
        ≤ RightTranslationHull.rightHull φ := by
      rw [← hrange_restrict]
      intro y hy
      rw [Submodule.restrictScalars_mem]
      exact (LinearMap.map_le_range (f := incl) (p := p)) hy
    haveI : FiniteDimensional k
        (Subrepresentation.ofSubmodule' (Submodule.map incl p)).toSubmodule :=
      Submodule.finiteDimensional_of_le hSsub
    have hreal := simpleSubrep_localRightRep_le_iSup_range n k
      (Subrepresentation.ofSubmodule' (Submodule.map incl p)) hSsimple
    intro y hy
    exact hreal ((Subrepresentation.mem_ofSubmodule'_iff).mpr hy)
  -- Assemble: `range incl ≤ T_KG`, restrict scalars, and identify with the hull.
  have hrange_le : LinearMap.range incl ≤ T_KG := by
    rw [← Submodule.map_top,
      ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)) (Representation.asModule H.toRepresentation),
      sSup_eq_iSup, Submodule.map_iSup]
    refine iSup_le fun p => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hp => hbound p hp
  calc RightTranslationHull.rightHull φ
      = (LinearMap.range incl).restrictScalars k := hrange_restrict.symm
    _ ≤ T_KG.restrictScalars k := Submodule.restrictScalars_mono (S := k) hrange_le
    _ = T := hTKG_restrict

/-- **The Cauchy spanning statement — the crux of Peter-Weyl surjectivity.** The matrix
coefficients of all the irreducibles `L_λ` together span the whole coordinate ring
`R = k[gᵢⱼ][1/det]`: the ranges of the per-summand maps `peterWeylSummandMap n λ k` have
supremum `⊤`. Equivalent to `peterWeylMap_surjective` (via `range_toModule_eq_iSup_range`), and
the sole remaining representation-theoretic obligation of `peterWeylMap_bijective`.

**Intended proof route (Etingof §5.23(ii), the Cauchy decomposition of `R`).** This is the
abstract Peter-Weyl "every regular function is a matrix coefficient" argument:

1. *Finite-dimensional right-translation hull.* Every `φ ∈ R = Localization.Away (detPoly k n)`
   has normal form `Q · det^{-r}` (`exists_invSelf_normalForm`); right translation
   (`localRightRep`) multiplies `det^{-r}` by the scalar `det(g)^{-r}` and acts on `Q` preserving
   total degree, so the span `W_φ` of the right-translates of `φ` is a finite-dimensional
   `localRightRep`-invariant submodule of `R`.

2. *Algebraicity / complete reducibility of the hull.* After the `det^{r}`-twist, `W_φ` is a
   polynomial representation, hence (Theorem 5.23.2(i), `polynomialRep_isSemisimple` /
   `decompose_polynomial_gl_rep`) completely reducible into the irreducibles `L_λ`; untwisting by
   `det^{-r}` shifts the constituent weights down by `r·(1,…,1)`, ranging over all dominant `λ`
   (`quotDetRep_irreducible_constituent_lastWeight_zero` characterizes the constituents of the
   determinant quotient as exactly the polynomial irreducibles).

3. *`φ` is a matrix coefficient of its hull.* Through the faithful functions-on-`GL` model
   `evalGLAway`, `φ(g) = ε(localRightRep g φ)` where `ε` is "evaluation at the identity"; so `φ`
   is a matrix coefficient of `(W_φ, localRightRep, ε)`.

4. *Matrix-coefficient correspondence (the genuine bridge).* A `GL`-equivariant inclusion
   `L_λ ↪ R` (a summand of `W_φ`) has its matrix coefficients realized exactly by
   `peterWeylSummandMap n λ k`; hence the matrix coefficient of `W_φ`, decomposed across the
   `L_λ` summands, lies in `⨆_λ range (peterWeylSummandMap n λ k)`.

The matrix-coefficient correspondence of step 4 is now available
(`equivariant_range_le_peterWeylSummandMap`, #5578), and the hull machinery of steps 1–2 is in
place (`RightTranslationHull.self_mem_rightHull`, `RightTranslationHull.rightHull_isSemisimple`,
#5577). What remains is the *realization* half of steps 2–4: identifying each simple constituent
of the semisimple hull with a concrete `L_λ = AlgIrrepGL n λ k` via a `GL_n`-equivariant
inclusion into `R`. That is isolated as the bridge lemma
`rightHull_le_iSup_range_peterWeylSummandMap` below. -/
theorem peterWeylSummandMap_iSup_range_eq_top
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    ⨆ lam, LinearMap.range (peterWeylSummandMap n lam k) = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  exact rightHull_le_iSup_range_peterWeylSummandMap n k φ
    (RightTranslationHull.self_mem_rightHull φ)

/-- **Surjectivity of the assembled matrix-coefficient map** — the Cauchy decomposition of
`R = k[gᵢⱼ][1/det]`: every regular function on `GL_n` is a finite sum of matrix coefficients.
Each homogeneous degree-`d` piece of the polynomial ring `k[gᵢⱼ]` decomposes, as a right-`GL_n`
representation, into irreducible Schur constituents
(`CauchyCharacterRightAssembly.polyRightDegreeFDRep_formalCharacter`,
`PolynomialGLDecomposition.decompose_polynomial_gl_rep`); inverting the determinant and using
that the constituents of the determinant quotient are exactly the polynomial irreducibles
(`CauchyDetQuotient.quotDetRep_irreducible_constituent_lastWeight_zero`) exhibits `R` as the sum
over all dominant weights `λ` of the `L*_λ ⊗ L_λ` isotypic block, i.e. `peterWeylMap` hits every
element of `R`.

This is the second of the two genuine Cauchy/Peter-Weyl halves of `peterWeylMap_bijective`. The
Cauchy machinery it consumes (`Cauchy*`, `PolynomialGL*`) is sorry-free; the present obligation is
its assembly at the level of the localization `R`, i.e. transporting the per-degree polynomial
decomposition across the determinant localization to the spanning statement for matrix
coefficients. Tracked as issue #5550. -/
theorem peterWeylMap_surjective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Function.Surjective (peterWeylMap n k) := by
  rw [← LinearMap.range_eq_top]
  unfold peterWeylMap
  rw [range_toModule_eq_iSup_range]
  exact peterWeylSummandMap_iSup_range_eq_top n k

/-- **Bijectivity of the assembled matrix-coefficient map** (the Cauchy decomposition).
This is the remaining representation-theoretic input to the Peter-Weyl capstone: the matrix
coefficients of the pairwise-distinct irreducibles `L_λ` are linearly independent
(`peterWeylMap_injective`) and span `R = k[gᵢⱼ][1/det]` (`peterWeylMap_surjective`). Bijectivity
is the conjunction of the two; each half is its own genuine Cauchy/orthogonality theorem. -/
theorem peterWeylMap_bijective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Function.Bijective (peterWeylMap n k) :=
  ⟨peterWeylMap_injective n k, peterWeylMap_surjective n k⟩

/-- **Theorem 5.23.2(ii) — Peter-Weyl for `GL_n(k)`.** The coordinate ring
`R = k[gᵢⱼ][1/det]`, as a representation of `GL_n × GL_n` under the left/right
translation bi-action `(g, h) · φ = L_g R_h φ` (`localBiRep`), is
**`GL_n × GL_n`-equivariantly isomorphic** to `⊕_λ L*_λ ⊗ L_λ` (`peterWeylRHS`),
the sum over all dominant integer weights `λ = (λ₁ ≥ ⋯ ≥ λ_n)`.

Unlike the bare rank iso `Theorem5_23_2_ii` in `Theorem5_23_2.lean`, this carries
genuine representation-theoretic content: the isomorphism intertwines the two
`GL_n × GL_n`-actions (`IsEquivariantEquiv`).

**Proof (Etingof §5.23(ii)).** By part (i) every algebraic representation is
completely reducible into the `L_λ`, which are pairwise non-isomorphic. The matrix
coefficient map `L*_λ ⊗ L_λ → R`, `u ⊗ v ↦ (g ↦ ⟨u, g⁻¹ v⟩)`, is `GL × GL`-equivariant
(left `GL` on `L*_λ`, right `GL` on `L_λ`); summing over `λ` and using that the
matrix coefficients of the pairwise-distinct irreducibles `L_λ` are linearly
independent and span `R` (the Cauchy decomposition,
`PolynomialGLDecomposition.lean` / `CauchyDetQuotient*`) gives the isomorphism.
The detailed assembly is out of scope for this file. -/
theorem Theorem5_23_2_ii_equivariant
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Nonempty { e : Localization.Away (detPoly k n) ≃ₗ[k]
        (DirectSum (DominantWeight n) fun lam =>
          (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) //
      IsEquivariantEquiv (localBiRep k n) (peterWeylRHS n k) e } :=
  -- The equivariant *structure* is assembled here: `peterWeylMap` together with
  -- `peterWeylMap_equivariant` reduce the capstone to `peterWeylMap_bijective`
  -- (the Cauchy decomposition), the sole remaining sorry.
  nonempty_equivariantEquiv_of_bijective n k (peterWeylMap_bijective n k)

end Etingof
