import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2_PeterWeyl
import EtingofRepresentationTheory.Chapter5.RepresentationAsModuleHom

-- These mirror the lakefile's project-wide `[leanOptions]` so the module also
-- type-checks under a bare `lake env lean` fresh check (which does not read
-- lakefile options). `maxSynthPendingDepth 3` clears the deep Schur-module
-- `asModule`/instance chains; `backward.isDefEq.respectTransparency false`
-- restores the pre-v4.29 full-transparency `isDefEq` the `charTwistRep`/Schur
-- carrier defeqs rely on.
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

/-!
# Exhaustiveness of the family `L_λ`: every simple algebraic `GL_n`-representation is some `L_λ`

`AlgIrrepGLNonIso.lean` shows the family `λ ↦ L_λ = algIrrepGLRepρ n λ k`, indexed by
`DominantWeight n`, is *injective* up to isomorphism, and
`algIrrepGLRepρ_isSimpleModule` (`Theorem5_23_2_PeterWeyl.lean`) shows each member is
simple. This file supplies the missing half of Theorem 5.23.2(i): the family is
*exhaustive*. Every simple finite-dimensional algebraic representation of `GL_n(k)` is
isomorphic to `L_λ` for exactly one dominant integer weight `λ`.

## The route

The book's proof embeds an algebraic representation `Y` into `Y ⊗ R` by
`⟨u, ξ(v)⟩(g) = u(g v)`, `R = k[gᵢⱼ][1/det]` the coordinate ring. Fixing a single
functional `u ∈ Y*` gives the matrix-coefficient map

  `mc : Y →ₗ[k] R`,  `mc v = (g ↦ u(ρ(g) v))`,

which intertwines `ρ` with the right-translation action `localRightRep` on `R`
(`exists_equivariant_matrixCoeff`). It really lands in `R` because `ρ` is algebraic:
its matrix coefficients are the polynomials supplied by `IsAlgebraicCoefficientFamily`.

If `ρ` is simple, `mc` is injective as soon as it is nonzero (its kernel is a
subrepresentation), and choosing `u` to be a basis coordinate functional that is nonzero
on some `v₀` makes `mc v₀ ≠ 0` (evaluate at `g = 1`). So a simple algebraic `Y` is
realized as a simple, finite-dimensional `localRightRep`-subrepresentation of `R`; the
Peter-Weyl realization core `exists_dominantWeight_equivariant_realization` then names
that subrepresentation as some `L_λ`.

## Main results

* `exists_equivariant_matrixCoeff`: the matrix-coefficient map of an algebraic
  representation against a functional `u`, with its defining identity and equivariance.
* `exists_dominantWeight_asModuleEquiv_of_isSimpleModule`: exhaustiveness — every simple
  algebraic representation is isomorphic to some `L_λ`.
* `existsUnique_dominantWeight_asModuleEquiv_of_isSimpleModule`: exhaustiveness plus the
  uniqueness supplied by `algIrrepGLRepρ_iso_iff_eq`, i.e. the existence-and-uniqueness
  classification of the simple algebraic `GL_n(k)`-representations by `DominantWeight n`.
-/

noncomputable section

namespace Etingof

open Etingof.DetLocalization Etingof.LocalizationGLAction Etingof.DetInvElim
  Etingof.KernelLemmaKPrime

/-! ## The matrix-coefficient map of an algebraic representation -/

/-- **Matrix coefficients of an algebraic representation live in the coordinate ring.**
For an algebraic representation `ρ` of `GL_n(k)` on `Y` and a linear functional
`u : Y →ₗ[k] k` there is a `k`-linear map `mc : Y →ₗ[k] R = k[gᵢⱼ][1/det]` whose value at
`v`, read through the faithful functions-on-`GL` model `evalGLAway`, is the matrix
coefficient `g ↦ u(ρ(g) v)`.

Explicitly, with the algebraic witness `(b, P)` of `ρ` (`b` a basis, `P a c` the
coefficient polynomials with `b.repr (ρ(g) (b c)) a = evalAtGL g (P a c)`),

  `mc v = ∑_{a,c} (b.repr v c) • (u (b a) • coordToAway (P a c))`. -/
theorem exists_equivariant_matrixCoeff
    {n : ℕ} {k : Type} [Field k] {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y)
    (halg : IsAlgebraicCoefficientFamily n ρ) (u : Y →ₗ[k] k) :
    ∃ mc : Y →ₗ[k] Localization.Away (detPoly k n),
      ∀ (v : Y) (g : Matrix.GeneralLinearGroup (Fin n) k),
        evalGLAway (mc v) g = u (ρ g v) := by
  classical
  obtain ⟨d, b, P, hP⟩ := halg
  refine ⟨∑ a, ∑ c, LinearMap.smulRight (b.coord c) (u (b a) • coordToAway (P a c)), ?_⟩
  intro v g
  -- Expand the localization element as an explicit double sum and evaluate at `g`.
  have hmc : (∑ a, ∑ c,
        LinearMap.smulRight (b.coord c) (u (b a) • coordToAway (P a c))) v
      = ∑ a, ∑ c, (b.repr v c * u (b a)) • coordToAway (P a c) := by
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      smul_smul]
  rw [hmc, map_sum, Finset.sum_apply]
  have hLHS : ∀ a : Fin d, evalGLAway (∑ c, (b.repr v c * u (b a)) • coordToAway (P a c)) g
      = ∑ c, (b.repr v c * u (b a)) * Etingof.evalAtGL g (P a c) := by
    intro a
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [evalGLAway_smul, Pi.smul_apply, smul_eq_mul, ← evalAtGL_eq_evalGLAway_coordToAway]
  rw [Finset.sum_congr rfl fun a _ => hLHS a]
  -- Expand `u (ρ g v)` in the basis `b` twice, using the coefficient identity `hP`.
  have hexp : u (ρ g v) = ∑ c, b.repr v c * ∑ a, Etingof.evalAtGL g (P a c) * u (b a) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
    congr 1
    conv_lhs => rw [← b.sum_repr (ρ g (b c))]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul, hP g a c]
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Equivariance of the matrix-coefficient map.** A `k`-linear map `mc : Y →ₗ[k] R` whose
`evalGLAway`-values are the matrix coefficients `g ↦ u(ρ(g) v)` of a *representation* `ρ`
intertwines `ρ` with the right-translation action `localRightRep` on `R`. Through
`evalGLAway` (injective for infinite `k`) this is the identity
`u(ρ(y g) v) = u(ρ(y) (ρ(g) v))`, i.e. `evalGLAway_localRightRep`. -/
theorem matrixCoeff_equivariant
    {n : ℕ} {k : Type} [Field k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (u : Y →ₗ[k] k) (mc : Y →ₗ[k] Localization.Away (detPoly k n))
    (hmc : ∀ (v : Y) (g : Matrix.GeneralLinearGroup (Fin n) k),
      evalGLAway (mc v) g = u (ρ g v))
    (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Y) :
    mc (ρ g v) = localRightRep k n g (mc v) := by
  apply evalGLAway_injective
  funext y
  rw [hmc, evalGLAway_localRightRep, hmc]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]

/-! ## Exhaustiveness -/

/-- **A nonzero equivariant map out of a simple representation is injective.** The kernel of
`f` is a `ρ`-stable `k`-subspace, hence a `k[GL_n]`-submodule of `ρ.asModule`; simplicity
makes it `⊥` or `⊤`, and `⊤` would force `f = 0`. -/
private theorem injective_of_isSimpleModule_of_ne_zero
    {n : ℕ} {k : Type} [Field k]
    {Y : Type} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule]
    {W : Type} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) W)
    (f : Y →ₗ[k] W)
    (hf : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Y), f (ρ g v) = σ g (f v))
    (hne : f ≠ 0) :
    Function.Injective f := by
  have hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k),
      ∀ x ∈ LinearMap.ker f, ρ g (ρ.asModuleEquiv x) ∈ LinearMap.ker f := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show ρ.asModuleEquiv x = x from rfl, hf, hx, map_zero]
  rcases hsimp.eq_bot_or_eq_top
      (Representation.stableSubmodule ρ (LinearMap.ker f) hstable) with h | h
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.eq_bot_iff] at h
    exact h x ((Representation.mem_stableSubmodule ρ _ hstable x).mpr hx)
  · exfalso
    apply hne
    ext x
    rw [Submodule.eq_top_iff'] at h
    exact (LinearMap.mem_ker).mp
      ((Representation.mem_stableSubmodule ρ _ hstable x).mp (h x))

/-- **Exhaustiveness of the family `L_λ` (Theorem 5.23.2(i), constituent classification).**
Every simple finite-dimensional algebraic representation `ρ` of `GL_n(k)` is isomorphic, as a
`k[GL_n]`-module, to `L_λ = algIrrepGLRepρ n λ k` for some dominant integer weight
`λ = (λ₁ ≥ ⋯ ≥ λ_n)`.

**Proof.** Pick a basis coordinate functional `u` on `Y` with `u v₀ ≠ 0` for some `v₀ ≠ 0`.
The matrix-coefficient map `mc : Y →ₗ[k] R` (`exists_equivariant_matrixCoeff`) intertwines
`ρ` with right translation (`matrixCoeff_equivariant`) and is nonzero (`evalGLAway (mc v₀) 1
= u v₀ ≠ 0`), hence injective. Its image is a simple, finite-dimensional
`localRightRep`-subrepresentation `S ⊆ R`, so the Peter-Weyl realization core
`exists_dominantWeight_equivariant_realization` supplies a dominant weight `λ` and an
equivariant `ι : L_λ →ₗ[k] R` with `range ι = S = range mc`. Both `mc` and `ι` are
injective equivariant maps with the same range, so `mc⁻¹ ∘ ι : L_λ ≃ₗ[k] Y` intertwines
`algIrrepGLRepρ n λ k` with `ρ`. -/
theorem exists_dominantWeight_asModuleEquiv_of_isSimpleModule
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : IsAlgebraicCoefficientFamily n ⇑ρ)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule] :
    ∃ lam : DominantWeight n,
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        (algIrrepGLRepρ n lam k).asModule) := by
  classical
  -- `Y` is nontrivial: a simple module is.
  haveI hnt : Nontrivial Y := by
    have h := (Submodule.nontrivial_iff
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))).mp hsimp.toNontrivial
    exact (show Nontrivial ρ.asModule from h)
  -- Choose a basis coordinate functional `u` and a vector `v₀` with `u v₀ ≠ 0`.
  obtain ⟨d, b, P, hP⟩ := halg
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Y)
  have hrepr : b.repr v₀ ≠ 0 := fun h => hv₀ (by simpa using congrArg b.repr.symm h)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, b.repr v₀ c₀ ≠ 0 := by
    by_contra hcon
    exact hrepr (by ext c; simpa using not_not.mp (not_exists.mp hcon c))
  set u : Y →ₗ[k] k := b.coord c₀ with hu
  have huv₀ : u v₀ ≠ 0 := hc₀
  -- The matrix-coefficient map and its two properties.
  obtain ⟨mc, hmc⟩ := exists_equivariant_matrixCoeff (n := n) (k := k) ⇑ρ ⟨d, b, P, hP⟩ u
  have hmc_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Y),
      mc (ρ g v) = localRightRep k n g (mc v) :=
    fun g v => matrixCoeff_equivariant ρ u mc hmc g v
  have hmc_ne : mc ≠ 0 := by
    intro h
    apply huv₀
    have := hmc v₀ 1
    rw [h] at this
    simpa using this.symm
  have hmc_inj : Function.Injective mc :=
    injective_of_isSimpleModule_of_ne_zero ρ (localRightRep k n) mc hmc_equiv hmc_ne
  -- The `k[GL_n]`-linear form of `mc`, its (simple) range, and the induced subrepresentation.
  set mcKG : ρ.asModule →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
      (localRightRep k n).asModule :=
    Representation.asModuleHomOfIntertwiner mc hmc_equiv with hmcKG
  have hmcKG_inj : Function.Injective mcKG := hmc_inj
  set S : Subrepresentation (localRightRep k n) :=
    Subrepresentation.ofSubmodule' (LinearMap.range mcKG) with hS
  have hS_toSubmodule : S.toSubmodule = LinearMap.range mc := by
    apply SetLike.ext; intro x
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  haveI hSfin : FiniteDimensional k S.toSubmodule := by
    rw [hS_toSubmodule]; infer_instance
  have hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S) :=
    (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective mcKG hmcKG_inj)).mp hsimp
  -- Name the subrepresentation by a dominant weight.
  obtain ⟨lam, ι, hι_equiv, hι_range⟩ :=
    exists_dominantWeight_equivariant_realization n k S hSsimple
  rw [hS_toSubmodule] at hι_range
  -- `ι` is injective: `L_λ` is simple and `ι ≠ 0` (its range is the nonzero `range mc`).
  haveI := algIrrepGLRepρ_isSimpleModule n k lam
  have hι_ne : ι ≠ 0 := by
    intro h
    apply hmc_ne
    have hrange0 : LinearMap.range mc = ⊥ := by rw [← hι_range, h, LinearMap.range_zero]
    ext v
    exact (Submodule.eq_bot_iff _).mp hrange0 (mc v) ⟨v, rfl⟩
  have hι_inj : Function.Injective ι :=
    injective_of_isSimpleModule_of_ne_zero (algIrrepGLRepρ n lam k) (localRightRep k n) ι
      hι_equiv hι_ne
  -- Transport: `e : L_λ ≃ₗ[k] Y` with `mc (e w) = ι w`.
  set e : AlgIrrepGL n lam k ≃ₗ[k] Y :=
    (LinearEquiv.ofInjective ι hι_inj).trans
      ((LinearEquiv.ofEq _ _ hι_range).trans (LinearEquiv.ofInjective mc hmc_inj).symm) with he
  have he_spec : ∀ w : AlgIrrepGL n lam k, mc (e w) = ι w := by
    intro w
    have h2 : (LinearEquiv.ofInjective mc hmc_inj) (e w)
        = (LinearEquiv.ofEq _ _ hι_range) ((LinearEquiv.ofInjective ι hι_inj) w) := by
      rw [he]
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    have h3 : ((LinearEquiv.ofEq _ _ hι_range)
        ((LinearEquiv.ofInjective ι hι_inj) w) : Localization.Away (detPoly k n)) = ι w := rfl
    rw [← h3, ← h2]
    rfl
  have he_int : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (w : AlgIrrepGL n lam k),
      e (algIrrepGLRepρ n lam k g w) = ρ g (e w) := by
    intro g w
    apply hmc_inj
    rw [he_spec, hι_equiv, ← he_spec, hmc_equiv]
  exact ⟨lam, ⟨(Representation.asModuleEquivOfIntertwiner e he_int).symm⟩⟩

/-- **Existence and uniqueness: the classification of the simple algebraic
`GL_n(k)`-representations (Theorem 5.23.2(i)).** Every simple finite-dimensional algebraic
representation of `GL_n(k)` is isomorphic to `L_λ = algIrrepGLRepρ n λ k` for *exactly one*
dominant integer weight `λ = (λ₁ ≥ ⋯ ≥ λ_n)`.

Existence is `exists_dominantWeight_asModuleEquiv_of_isSimpleModule`; uniqueness is
`algIrrepGLRepρ_iso_iff_eq` (`AlgIrrepGLNonIso.lean`), which says distinct dominant weights
give non-isomorphic irreducibles. Together with `algIrrepGLRepρ_isSimpleModule` (each `L_λ`
*is* simple and algebraic) this is the book's assertion that the simple algebraic
representations of `GL(V)` are exactly the `L_λ`, pairwise nonisomorphic. -/
theorem existsUnique_dominantWeight_asModuleEquiv_of_isSimpleModule
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : IsAlgebraicCoefficientFamily n ⇑ρ)
    [IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule] :
    ∃! lam : DominantWeight n,
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        (algIrrepGLRepρ n lam k).asModule) := by
  obtain ⟨lam, ⟨e⟩⟩ := exists_dominantWeight_asModuleEquiv_of_isSimpleModule n k ρ halg
  refine ⟨lam, ⟨e⟩, fun mu ⟨f⟩ => ?_⟩
  exact (algIrrepGLRepρ_iso_iff_eq n k).mp ⟨f.symm.trans e⟩

/-! ## Naming the constituents of an arbitrary algebraic representation -/

/-- **A simple `k[GL_n]`-submodule of an algebraic representation is some `L_λ`.** The
submodule `S` is `ρ`-stable, so it carries a subrepresentation, algebraic by
`IsAlgebraicCoefficientFamily.restrict`; exhaustiveness
(`exists_dominantWeight_asModuleEquiv_of_isSimpleModule`) then names it. -/
theorem exists_dominantWeight_asModuleEquiv_of_simple_submodule
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : IsAlgebraicCoefficientFamily n ⇑ρ)
    (S : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule)
    (hS : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) S) :
    ∃ lam : DominantWeight n,
      Nonempty (S ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        (algIrrepGLRepρ n lam k).asModule) := by
  classical
  -- `S` as a subrepresentation of `ρ`, and the associated representation `σ` on it.
  set T : Subrepresentation ρ := Subrepresentation.ofSubmodule' S with hT
  set σ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) T.toSubmodule :=
    T.toRepresentation with hσ
  haveI : Module.Finite k T.toSubmodule := Module.Finite.of_injective T.toSubmodule.subtype
    Subtype.coe_injective
  -- The `k[GL_n]`-linear inclusion `σ.asModule ↪ ρ.asModule`, with range exactly `S`.
  have hsub : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (x : T.toSubmodule),
      T.toSubmodule.subtype (σ g x) = ρ g (T.toSubmodule.subtype x) :=
    fun g x => LinearMap.coe_restrict_apply (T.apply_mem_toSubmodule g) x
  set incl : Representation.asModule σ →ₗ[MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin n) k)] ρ.asModule :=
    Representation.asModuleHomOfIntertwiner T.toSubmodule.subtype hsub with hincl
  have hincl_inj : Function.Injective incl := by
    intro a b hab
    apply σ.asModuleEquiv.injective
    apply Subtype.coe_injective
    exact hab
  have hrange : LinearMap.range incl = S := by
    apply SetLike.ext; intro x
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  set eS : Representation.asModule σ ≃ₗ[MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin n) k)] S :=
    (LinearEquiv.ofInjective incl hincl_inj).trans (LinearEquiv.ofEq _ _ hrange) with heS
  -- `σ` is simple and algebraic, so exhaustiveness applies.
  haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule σ) := (LinearEquiv.isSimpleModule_iff eS).mpr hS
  have halgσ : IsAlgebraicCoefficientFamily n ⇑σ :=
    halg.restrict T.toSubmodule (fun g _ hv => T.apply_mem_toSubmodule g hv)
  obtain ⟨lam, ⟨f⟩⟩ := exists_dominantWeight_asModuleEquiv_of_isSimpleModule n k σ halgσ
  exact ⟨lam, ⟨eS.symm.trans f⟩⟩

/-- **Theorem 5.23.2(i), full form: an algebraic representation is a direct sum of `L_λ`'s.**
Every finite-dimensional algebraic representation `ρ` of `GL_n(k)` decomposes,
`GL_n`-equivariantly, as a finite direct sum `⨁_{j < p} L_{λ_j}` of the named irreducibles
`L_λ = algIrrepGLRepρ n λ k`. This is the book's "decomposes into summands of the form
`L_λ`"; the accompanying "(which are pairwise nonisomorphic)" is
`algIrrepGLRepρ_noniso` (`AlgIrrepGLNonIso.lean`), and simplicity of each summand is
`algIrrepGLRepρ_isSimpleModule`.

**Proof.** Complete reducibility (`Theorem5_23_2_i`) makes `ρ.asModule` a semisimple
`k[GL_n]`-module, and it is `k[GL_n]`-finite because it is `k`-finite; so it is a finite
direct sum of simple submodules (`IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp`).
Each simple summand is named by `exists_dominantWeight_asModuleEquiv_of_simple_submodule`,
and the naming isomorphisms are assembled summand-wise. -/
theorem exists_directSum_algIrrepGL_of_isAlgebraic
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : IsAlgebraicCoefficientFamily n ⇑ρ) :
    ∃ (p : ℕ) (lam : Fin p → DominantWeight n),
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        DirectSum (Fin p) fun j => (algIrrepGLRepρ n (lam j) k).asModule) := by
  classical
  haveI hss : IsSemisimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      ρ.asModule := Theorem5_23_2_i n ρ halg
  haveI : Module.Finite (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule
  obtain ⟨p, S, e, hSsimple⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp
    (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule
  choose lam hlam using fun j : Fin p =>
    exists_dominantWeight_asModuleEquiv_of_simple_submodule n k ρ halg (S j) (hSsimple j)
  refine ⟨p, lam, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun j => (hlam j).some)⟩⟩

end Etingof
