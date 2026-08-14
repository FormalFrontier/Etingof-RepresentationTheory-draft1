import RepresentationTheory.CategoryTheory.Abelian.FiniteLength
import RepresentationTheory.FGModuleCat.SimpleModules
import RepresentationTheory.FGModuleCat.Projectivity

open CategoryTheory Limits
open RepresentationTheory.CategoryTheory.Abelian.FiniteLength
open RepresentationTheory.FGModuleCat.SimpleModules

namespace RepresentationTheory.FGModuleCat.FiniteLengthAndSubmoduleComplexes

universe u

noncomputable section

variable {A : Type u} [Ring A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- A finite module with at most one element defines a zero object in the category of finitely generated modules. -/
lemma isZero_fgModule_of_subsingleton (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Subsingleton M] : IsZero (FGModuleCat.of A M) := by
  rw [IsZero.iff_id_eq_zero]
  apply FGModuleCat.hom_ext
  ext x
  exact Subsingleton.elim _ _

/-- A short complex determined by a finite submodule of a finite module. -/
def shortComplexOfSubmodule {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) [Module.Finite A ↥N] : ShortComplex (FGModuleCat.{u} A) where
  X₁ := FGModuleCat.of A ↥N
  X₂ := FGModuleCat.of A M
  X₃ := FGModuleCat.of A (M ⧸ N)
  f := FGModuleCat.ofHom N.subtype
  g := FGModuleCat.ofHom N.mkQ
  zero := by
    apply FGModuleCat.hom_ext
    ext x
    change N.mkQ (N.subtype x) = 0
    simp

/-- The short complex attached to a finite submodule is short exact over a Noetherian ring. -/
theorem shortExact_shortComplexOfSubmodule {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) [Module.Finite A ↥N] : (shortComplexOfSubmodule N).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · have hmap : ((shortComplexOfSubmodule N).map (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))).Exact := by
      apply ModuleCat.shortComplex_exact
      exact LinearMap.exact_subtype_mkQ N
    exact (ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))).mp hmap
  · apply (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).mono_of_mono_map
      (f := (shortComplexOfSubmodule N).f)
    rw [ModuleCat.mono_iff_injective]
    exact N.injective_subtype
  · apply RepresentationTheory.FGModuleCat.Projectivity.epi_of_toModuleCat_map_epi
      (shortComplexOfSubmodule N).g
    rw [ModuleCat.epi_iff_surjective]
    exact N.mkQ_surjective

/-- A finite module of finite length has the designated property when regarded as a finitely generated module. -/
theorem fgModuleProperty_of_isFiniteLength
    {M : Type u} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    ∀ [Module.Finite A M], HasFiniteLength (FGModuleCat.of A M) := by
  induction hM with
  | of_subsingleton =>
      intro _
      exact HasFiniteLength.of_isZero (isZero_fgModule_of_subsingleton _)
  | @of_simple_quotient M _ _ N _ _hN ih =>
      intro _
      haveI : Module.Finite A ↥N := inferInstance
      haveI : Module.Finite A (M ⧸ N) := inferInstance
      exact HasFiniteLength.of_shortExact (shortExact_shortComplexOfSubmodule N) ih
        (HasFiniteLength.of_simple (simple_of_isSimpleModule (M ⧸ N)))

/-- Finitely generated modules over a Noetherian Artinian ring have the designated module property. -/
theorem fgModuleProperty_of_isNoetherianRing_of_isArtinianRing [IsArtinianRing A]
    (X : FGModuleCat.{u} A) : HasFiniteLength X := by
  haveI : IsFiniteLength A X :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have h := fgModuleProperty_of_isFiniteLength (A := A) (M := X) this
  exact h

end

end RepresentationTheory.FGModuleCat.FiniteLengthAndSubmoduleComplexes
