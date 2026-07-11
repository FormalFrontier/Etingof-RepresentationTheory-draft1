import Mathlib.Algebra.Group.Idempotent
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import EtingofRepresentationTheory.Chapter9.Definition9_5_1

/-!
# Problem 9.5.3: Blocks and central idempotents

Etingof Problem 9.5.3 relates the block decomposition of a finite abelian category `𝒞`
(here the category of finite dimensional `A`-modules) to the structure of `A`.

* **(i)** There is a natural bijection between blocks of `𝒞` and *indecomposable* central
  idempotents `eₖ` of `A` (central idempotents that cannot be split nontrivially into a sum of
  two orthogonal central idempotents), under which `𝒞ₖ` is the category of `eₖ A`-modules.

* **(ii)** Every indecomposable object of `𝒞` lies in some block `𝒞ₖ`, and
  `Hom(M, N) = 0` whenever `M ∈ 𝒞ₖ`, `N ∈ 𝒞ₗ` with `k ≠ l`. Thus `𝒞 = ⊕ₖ 𝒞ₖ`.

* **(iii)** Determine the blocks of the category of left `A`-modules for `A = k[S₃]` with `k`
  of characteristic `2`. *(Deferred: this concrete modular-representation computation is left
  to a follow-up statement-pass item.)*

## Statement-pass note

Blocks are `Etingof.Block R` and block membership is `Etingof.InBlock R S M` (Definition
9.5.1). "Indecomposable central idempotent" is the predicate
`Etingof.Problem953.IsIndecomposableCentralIdempotent` defined below (a nonzero central
idempotent not expressible as a sum of two nonzero orthogonal central idempotents).
"`Hom(M, N) = 0`" is `Subsingleton (M ⟶ N)`, and "indecomposable object" is
`CategoryTheory.Indecomposable`. Two blocks are distinct exactly when their representative
simple modules are not `Etingof.AreLinked`. Proofs are deferred (`sorry`).
-/

universe v u

open CategoryTheory

namespace Etingof

section CompositionFactor

variable {R : Type u} [Ring R]

/-- A composition factor is exactly a **simple quotient of a submodule**: `S` is a composition
factor of `M` iff `S` is simple and there is a submodule `P ≤ M` together with a surjective
`R`-linear map `P → S`. This reformulation of `Etingof.IsCompositionFactor` avoids
quotient-of-quotient manipulations. -/
theorem isCompositionFactor_iff {M S : ModuleCat.{v} R} :
    IsCompositionFactor R M S ↔
      IsSimpleModule R S ∧ ∃ (P : Submodule R M) (g : P →ₗ[R] S), Function.Surjective g := by
  constructor
  · rintro ⟨hS, N₁, N₂, hle, ⟨e⟩⟩
    refine ⟨hS, N₂, e.toLinearMap ∘ₗ (N₁.comap N₂.subtype).mkQ, ?_⟩
    exact e.surjective.comp (Submodule.mkQ_surjective _)
  · rintro ⟨hS, P, g, hg⟩
    refine ⟨hS, (LinearMap.ker g).map P.subtype, P, Submodule.map_subtype_le _ _, ?_⟩
    have hcomap : ((LinearMap.ker g).map P.subtype).comap P.subtype = LinearMap.ker g :=
      Submodule.comap_map_eq_of_injective P.subtype_injective _
    rw [hcomap]
    exact ⟨g.quotKerEquivOfSurjective hg⟩

/-- A composition factor of a submodule `↥P` of `M` is a composition factor of `M`. -/
theorem IsCompositionFactor.of_submodule {M S : ModuleCat.{v} R} (P : Submodule R M)
    (h : IsCompositionFactor R (ModuleCat.of R P) S) : IsCompositionFactor R M S := by
  rw [isCompositionFactor_iff] at h ⊢
  obtain ⟨hS, Q, g, hg⟩ := h
  refine ⟨hS, Q.map P.subtype,
    g ∘ₗ (Submodule.equivMapOfInjective P.subtype P.subtype_injective Q).symm.toLinearMap, ?_⟩
  exact hg.comp (Submodule.equivMapOfInjective P.subtype P.subtype_injective Q).symm.surjective

/-- A composition factor of a quotient (surjective image) of `M` is a composition factor of `M`. -/
theorem IsCompositionFactor.of_surjective {M : ModuleCat.{v} R} {B : Type v} [AddCommGroup B]
    [Module R B] {S : ModuleCat.{v} R} (q : M →ₗ[R] B) (hq : Function.Surjective q)
    (h : IsCompositionFactor R (ModuleCat.of R B) S) : IsCompositionFactor R M S := by
  rw [isCompositionFactor_iff] at h ⊢
  obtain ⟨hS, P, g, hg⟩ := h
  have hres : ∀ x ∈ P.comap q, q x ∈ P := fun x hx => hx
  refine ⟨hS, P.comap q, g ∘ₗ q.restrict hres, ?_⟩
  apply hg.comp
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hq y
  exact ⟨⟨x, hy⟩, Subtype.ext (by simp)⟩

/-- Every nonzero module has a composition factor: a nonzero element generates a cyclic
submodule, which (via a maximal left ideal above its annihilator) has a simple quotient. The
simple quotient naturally lives in `R`'s universe and is shrunk into universe `v` using
`Small.{v} R`. -/
theorem exists_isCompositionFactor {M : ModuleCat.{v} R} [Small.{v} R] [Nontrivial M] :
    ∃ S : ModuleCat.{v} R, IsCompositionFactor R M S := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M m with hgdef
  have hkerne : LinearMap.ker g ≠ ⊤ := by
    intro htop
    apply hm
    have h1 : (1 : R) ∈ LinearMap.ker g := htop ▸ Submodule.mem_top
    have h2 := LinearMap.mem_ker.mp h1
    simpa [g, LinearMap.toSpanSingleton_apply] using h2
  obtain ⟨𝔪, h𝔪max, hle⟩ := Ideal.exists_le_maximal (LinearMap.ker g) hkerne
  have h𝔪coatom : IsCoatom 𝔪 := Ideal.isMaximal_def.mp h𝔪max
  -- Natural surjection `R ⧸ ker g.rangeRestrict → R ⧸ 𝔪`.
  have hle'' : LinearMap.ker g.rangeRestrict ≤ Submodule.comap LinearMap.id 𝔪 := by
    rw [Submodule.comap_id, LinearMap.ker_rangeRestrict]; exact hle
  set proj : (R ⧸ LinearMap.ker g.rangeRestrict) →ₗ[R] (R ⧸ 𝔪) :=
    Submodule.mapQ _ 𝔪 LinearMap.id hle'' with hprojdef
  have hprojsurj : Function.Surjective proj := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective 𝔪 y
    exact ⟨Submodule.Quotient.mk r, by simp [hprojdef, Submodule.mapQ_apply]⟩
  -- Surjection `↥(range g) → R ⧸ 𝔪`.
  set e := (g.rangeRestrict.quotKerEquivOfSurjective (LinearMap.surjective_rangeRestrict g)).symm
    with hedef
  set gmap : (LinearMap.range g) →ₗ[R] (R ⧸ 𝔪) := proj ∘ₗ e.toLinearMap with hgmapdef
  have hgmapsurj : Function.Surjective gmap := hprojsurj.comp e.surjective
  -- Shrink the simple quotient into universe `v`.
  have hsimple : IsSimpleModule R (R ⧸ 𝔪) := isSimpleModule_iff_isCoatom.mpr h𝔪coatom
  set sh := Shrink.linearEquiv R (R ⧸ 𝔪) with hshdef
  refine ⟨ModuleCat.of R (Shrink.{v} (R ⧸ 𝔪)), isCompositionFactor_iff.mpr
    ⟨sh.isSimpleModule_iff.mpr hsimple, LinearMap.range g, sh.symm.toLinearMap ∘ₗ gmap, ?_⟩⟩
  exact sh.symm.surjective.comp hgmapsurj

end CompositionFactor

namespace Problem953

variable (R : Type u) [Ring R]

/-- An **indecomposable central idempotent** of a ring `R`: a nonzero central idempotent that
cannot be written as a sum `e = e₁ + e₂` of two nonzero orthogonal central idempotents. These
are the primitive idempotents of the center; by Problem 9.5.3(i) they index the blocks. -/
def IsIndecomposableCentralIdempotent (e : R) : Prop :=
  e ≠ 0 ∧ IsIdempotentElem e ∧ (∀ y : R, e * y = y * e) ∧
    ¬ ∃ e₁ e₂ : R, e₁ ≠ 0 ∧ e₂ ≠ 0 ∧ IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧
      (∀ y, e₁ * y = y * e₁) ∧ (∀ y, e₂ * y = y * e₂) ∧ e₁ * e₂ = 0 ∧ e = e₁ + e₂

/-- **Problem 9.5.3 (i).** There is a bijection between the blocks of the category of
(finite dimensional) `R`-modules and the indecomposable central idempotents of `R`. -/
theorem blocks_equiv_indecomposableCentralIdempotents [Small.{v} R] :
    Nonempty (Etingof.Block.{v} R ≃ {e : R // IsIndecomposableCentralIdempotent R e}) := by
  sorry

/-- **Problem 9.5.3 (ii), orthogonality.** If `M` lies in the block of the simple module `S`
and `N` lies in the block of the simple module `T`, and `S`, `T` are not linked (i.e. `M`, `N`
are in different blocks), then `Hom(M, N) = 0`. -/
theorem hom_subsingleton_of_not_linked [Small.{v} R]
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    {M N : ModuleCat.{v} R} (hM : Etingof.InBlock R S M) (hN : Etingof.InBlock R T N)
    (hST : ¬ Etingof.AreLinked R S T) :
    Subsingleton (M ⟶ N) := by
  -- It suffices to show every morphism `M ⟶ N` is zero.
  suffices h0 : ∀ f : M ⟶ N, f = 0 by exact ⟨fun f g => by rw [h0 f, h0 g]⟩
  intro f
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  by_contra hfhom
  -- If `f.hom ≠ 0` its range is a nonzero submodule of `N`, hence has a composition factor `U`.
  have hrange : LinearMap.range f.hom ≠ ⊥ := by rwa [Ne, LinearMap.range_eq_bot]
  haveI hnt : Nontrivial (LinearMap.range f.hom) := Submodule.nontrivial_iff_ne_bot.mpr hrange
  obtain ⟨U, hU⟩ :=
    Etingof.exists_isCompositionFactor (M := ModuleCat.of R (LinearMap.range f.hom))
  -- `U` is a composition factor of `N` (range is a submodule of `N`) ...
  have hUN : Etingof.IsCompositionFactor R N U :=
    Etingof.IsCompositionFactor.of_submodule (LinearMap.range f.hom) hU
  -- ... and of `M` (range is a surjective image of `M`).
  have hUM : Etingof.IsCompositionFactor R M U :=
    Etingof.IsCompositionFactor.of_surjective f.hom.rangeRestrict
      (LinearMap.surjective_rangeRestrict _) hU
  -- Both blocks then link `S` and `T`, contradicting `hST`.
  have h1 : Etingof.AreLinked R U S := hM U hUM
  have h2 : Etingof.AreLinked R U T := hN U hUN
  exact hST ((Etingof.areLinked_equivalence R).trans
    ((Etingof.areLinked_equivalence R).symm h1) h2)

/-- **Problem 9.5.3 (ii), decomposition.** Every indecomposable (finite length) object lies in
some block: there is a simple module `S` such that all composition factors of `M` are linked
to `S`. The finite-length assumption is recorded as the existence of at least one composition
factor. -/
theorem exists_block_of_indecomposable [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M)
    (hfl : ∃ S : ModuleCat.{v} R, Etingof.IsCompositionFactor R M S) :
    ∃ S : ModuleCat.{v} R, IsSimpleModule R S ∧ Etingof.InBlock R S M := by
  sorry

end Problem953

end Etingof
