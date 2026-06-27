import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.LocalizationGLBiAction
import EtingofRepresentationTheory.Chapter5.PeterWeylMatrixCoeff

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

BLOCKED: the Burnside/nondegeneracy route currently rests on `algIrrepGLRep_isSimple`, which is
`ℂ`-only and degree-constrained (`∑ lam.toNatWeight ≤ n`); the general-`k`, all-weights
generalization is tracked in `progress/schurModule-isSimple-general-route.md` (issue #4946). -/
theorem peterWeylSummandMap_injective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) :
    Function.Injective (peterWeylSummandMap n lam k) := by
  sorry

/-- **Cross-summand independence (distinct-irreducible Schur orthogonality).** The ranges of
the per-summand maps `peterWeylSummandMap n lam k` (the matrix coefficients of `L_λ` inside `R`)
form an `iSupIndep` family: matrix coefficients of pairwise non-isomorphic irreducibles are
linearly independent across distinct weights.

Equivariantly, each range is the `GL_n × GL_n`-isotypic component for the simple external-tensor
module `L*_λ ⊗ L_λ`; distinct `λ` give non-isomorphic simples (distinguished by formal
character / highest weight), so the isotypic components are independent. This is the
across-summand half of Peter-Weyl orthogonality.

BLOCKED: rests on simplicity and non-isomorphism of the `L_λ`, i.e. on `algIrrepGLRep_isSimple`
(presently `ℂ`-only, `∑ lam.toNatWeight ≤ n`) and the external-tensor simplicity of
`L*_λ ⊗ L_λ` as a `GL_n × GL_n`-module; general route in
`progress/schurModule-isSimple-general-route.md` (issue #4946). -/
theorem peterWeylSummandMap_range_iSupIndep
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    iSupIndep (fun lam => LinearMap.range (peterWeylSummandMap n lam k)) := by
  sorry

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
  sorry

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
