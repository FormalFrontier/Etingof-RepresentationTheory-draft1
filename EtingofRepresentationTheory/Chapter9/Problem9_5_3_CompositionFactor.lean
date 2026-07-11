import Mathlib.RingTheory.FiniteLength
import EtingofRepresentationTheory.Chapter9.Definition9_5_1

/-!
# Composition-factor manipulation lemmas (Problem 9.5.3)

Basic manipulation lemmas for `Etingof.IsCompositionFactor` (Definition 9.5.1), factored out of
`Problem9_5_3.lean` so that the dévissage (`Problem9_5_3_Devissage.lean`) and the main block
statements (`Problem9_5_3.lean`) can both depend on them without an import cycle.

* `isCompositionFactor_iff` — a composition factor is a simple quotient of a submodule.
* `IsCompositionFactor.of_submodule` / `.of_surjective` — composition factors pull back along
  submodule inclusions and push along surjections.
* `exists_isCompositionFactor` — every nonzero module has a composition factor.
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

end Etingof
