import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import EtingofRepresentationTheory.Chapter9.Exercise9_6_3
import EtingofRepresentationTheory.Infrastructure.SimpleModuleFamily
import EtingofRepresentationTheory.Infrastructure.FGModuleCatFiniteLength
import EtingofRepresentationTheory.Infrastructure.FGModuleCatSubobjectFiniteDimensional
import EtingofRepresentationTheory.Infrastructure.FGModuleCatEnoughProjectives

/-!
# Definition 9.6.1, the motivating example: `FGModuleCat A` is a finite abelian category

Etingof Definition 9.6.1 names the category of finite-dimensional modules over a
finite-dimensional algebra as the primary example of a finite abelian category, and §9.6 as a
whole develops the theory (Theorem 9.6.4, Exercise 9.6.3, ...) over an abstract such category.
This file wires the motivating example `FGModuleCat A` into that abstract API, for `A` a
finite-dimensional algebra over an algebraically closed field `k`.

## Main results

* `Etingof.fgModuleCatIsFiniteAbelianCategory` — the
  `Etingof.IsFiniteAbelianCategory (FGModuleCat A)` data, assembled from the sub-issue results:
  `Abelian` and `EnoughProjectives` (Noetherian), the finite simple family
  (`Etingof.exists_fgModuleCat_simple_family`), and the order-theoretic finite length
  (`Etingof.finiteDimensionalOrder_subobject_fgModuleCat`).
* `Etingof.fgModuleCat_hom_finiteDimensional` — every `Hom` space of `FGModuleCat A` is
  finite dimensional over `k` (an `A`-linear map between finite-dimensional `k`-spaces is
  `k`-linear).
* `Etingof.fgModuleCat_end_algEquiv_of_simple` — Schur's lemma over an algebraically closed
  field: `End X ≃ₐ[k] k` for a simple `X`. This is the `endSimple` datum.
* `Etingof.fgModuleCatIsFiniteAbelianCategoryOverField` — the
  `Etingof.IsFiniteAbelianCategoryOverField k (FGModuleCat A)` data.
* `Etingof.exists_progenerator_fgModuleCat`,
  `Etingof.morita_fgModuleCat` — the §9.6 capstones (Exercise 9.6.3, Theorem 9.6.4)
  instantiated on `FGModuleCat A`.

## Why `def`s rather than global `instance`s

`Etingof.IsFiniteAbelianCategory (FGModuleCat A)` does not mention the ground field `k`, but
its construction needs `k` (the finite simple family and finite length rest on `A` being a
finite-dimensional `k`-algebra). A global instance keyed only on `A` could therefore never
recover `k`, so the assembled classes are exposed as `def`s parameterised by `k`; the capstone
example lemmas activate them with `letI`.
-/

open CategoryTheory Limits

open scoped ModuleCat.Algebra

namespace Etingof

universe u

noncomputable section

variable (k : Type u) [Field k] [IsAlgClosed k]
variable (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]

-- `k` is not mentioned in the *types* of several results below (e.g. the finite-abelian
-- structure on `FGModuleCat A`), so force it (and its algebra structure on `A`) into scope.
include k

omit [IsAlgClosed k] in
/-- `A`, being a finite-dimensional algebra over a field, is an Artinian ring. -/
theorem isArtinianRing_of_finiteDimensional : IsArtinianRing A :=
  IsArtinianRing.of_finite k A

/-- **Definition 9.6.1, motivating example.** The finite-abelian-category data on
`FGModuleCat A` for a finite-dimensional `k`-algebra `A`: enough projectives and abelianness
come from `A` being Noetherian, the finitely many simple objects from
`Etingof.exists_fgModuleCat_simple_family`, and the order-theoretic finite length from
`Etingof.finiteDimensionalOrder_subobject_fgModuleCat`. -/
@[reducible]
def fgModuleCatIsFiniteAbelianCategory : IsFiniteAbelianCategory (FGModuleCat.{u} A) :=
  haveI : IsArtinianRing A := isArtinianRing_of_finiteDimensional k A
  haveI : IsNoetherianRing A := inferInstance
  -- Extract the finite simple family with `Classical.choice` (an existential over data cannot
  -- be `obtain`ed when building a structure).
  let H := exists_fgModuleCat_simple_family k A
  { ι := H.choose
    finι := H.choose_spec.choose
    simpleObj := H.choose_spec.choose_spec.choose
    simple_simpleObj := H.choose_spec.choose_spec.choose_spec.1
    iso_of_simple := H.choose_spec.choose_spec.choose_spec.2
    finiteDimensionalOrder_subobject := fun X =>
      finiteDimensionalOrder_subobject_fgModuleCat X }

/-! ### Hom spaces are finite dimensional -/

/-- The `k`-linear equivalence between categorical morphisms of `FGModuleCat A` and `A`-linear
maps of the underlying modules. -/
def fgModuleCatHomLinearEquiv (X Y : FGModuleCat.{u} A) :
    (X ⟶ Y) ≃ₗ[k] (X →ₗ[A] Y) :=
  (InducedCategory.homLinearEquiv (R := k)).trans ModuleCat.homLinearEquiv

omit [IsAlgClosed k] in
/-- **The `Hom` spaces of `FGModuleCat A` are finite dimensional over `k`.** An `A`-linear map
between two modules that are finite dimensional over `k` is in particular a `k`-linear map, so
`Hom` embeds `k`-linearly into the finite-dimensional space of `k`-linear maps. -/
theorem fgModuleCat_hom_finiteDimensional (X Y : FGModuleCat.{u} A) :
    FiniteDimensional k (X ⟶ Y) := by
  haveI : Module.Finite k (X : Type u) := Module.Finite.trans A (X : Type u)
  haveI : Module.Finite k (Y : Type u) := Module.Finite.trans A (Y : Type u)
  -- `A`-linear maps embed `k`-linearly into the finite-dimensional space of `k`-linear maps.
  haveI : Module.Finite k (X →ₗ[A] Y) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ (S := A) (M := (X : Type u)) (N := (Y : Type u)) (R := k)
        (R₁ := k))
      (LinearMap.restrictScalars_injective k)
  exact Module.Finite.equiv (fgModuleCatHomLinearEquiv k A X Y).symm

/-! ### Schur's lemma: `End X ≃ₐ[k] k` for simple `X` -/

/-- **Schur's lemma over an algebraically closed field.** For a simple object `X` of
`FGModuleCat A`, every endomorphism is a scalar multiple of the identity
(`CategoryTheory.endomorphism_simple_eq_smul_id`), so `algebraMap k (End X)` is bijective and
`End X ≃ₐ[k] k`. -/
theorem fgModuleCat_end_algEquiv_of_simple (X : FGModuleCat.{u} A) (hX : Simple X) :
    Nonempty (End X ≃ₐ[k] k) := by
  haveI : IsArtinianRing A := isArtinianRing_of_finiteDimensional k A
  haveI : IsNoetherianRing A := inferInstance
  haveI := hX
  haveI : FiniteDimensional k (X ⟶ X) := fgModuleCat_hom_finiteDimensional k A X X
  haveI : Nontrivial (End X) := nontrivial_of_ne _ _ (id_nonzero X)
  have hsurj : Function.Surjective (algebraMap k (End X)) := by
    intro f
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k f
    refine ⟨c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, End.one_def]
    exact hc
  -- A ring homomorphism out of the field `k` into the nontrivial ring `End X` is injective.
  have hinj : Function.Injective (algebraMap k (End X)) := RingHom.injective _
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (End X)) ⟨hinj, hsurj⟩).symm⟩

/-! ### The over-a-field structure -/

/-- **Definition 9.6.1 over a field.** The `k`-linear finite-abelian-category structure on
`FGModuleCat A`: finite length (`Etingof.hasFiniteLength_fgModuleCat`) and Schur's lemma
(`fgModuleCat_end_algEquiv_of_simple`). It is stated relative to the concrete
`fgModuleCatIsFiniteAbelianCategory k A` (pinning that instance keeps the `Preadditive`
structure canonical, so `Linear k (FGModuleCat A)` resolves). -/
theorem fgModuleCatIsFiniteAbelianCategoryOverField :
    letI := fgModuleCatIsFiniteAbelianCategory k A
    IsFiniteAbelianCategoryOverField k (FGModuleCat.{u} A) := by
  letI := fgModuleCatIsFiniteAbelianCategory k A
  haveI : IsArtinianRing A := isArtinianRing_of_finiteDimensional k A
  haveI : IsNoetherianRing A := inferInstance
  exact
    { finiteLength := fun X => hasFiniteLength_fgModuleCat X
      endSimple := fun X hX => fgModuleCat_end_algEquiv_of_simple k A X hX }

/-! ### The §9.6 capstones, instantiated -/

omit [IsAlgClosed k] in
/-- **Exercise 9.6.3 on the motivating example.** `FGModuleCat A` has a projective generator. -/
theorem exists_progenerator_fgModuleCat :
    ∃ P : FGModuleCat.{u} A, Nonempty (Etingof.IsProgenerator P) := by
  letI := fgModuleCatIsFiniteAbelianCategory k A
  exact Etingof.Exercise963.exists_progenerator (FGModuleCat.{u} A)

/-- The opposite endomorphism ring of any object of `FGModuleCat A` is Noetherian
(`Etingof.isNoetherianRing_endOp_of_overField`, using that `Hom` spaces are finite
dimensional). -/
theorem isNoetherianRing_endOp_fgModuleCat (P : FGModuleCat.{u} A) :
    IsNoetherianRing (End P)ᵐᵒᵖ := by
  letI := fgModuleCatIsFiniteAbelianCategory k A
  letI := fgModuleCatIsFiniteAbelianCategoryOverField k A
  exact Etingof.isNoetherianRing_endOp_of_overField (k := k) P

/-- **Theorem 9.6.4 (Morita equivalence) on the motivating example.** For a finite-dimensional
algebra `A` over an algebraically closed field, `FGModuleCat A` is equivalent to finitely
generated modules over `(End P)ᵐᵒᵖ` for a progenerator `P`. -/
theorem morita_fgModuleCat :
    ∃ P : FGModuleCat.{u} A, Nonempty (FGModuleCat.{u} A ≌ FGModuleCat.{u} (End P)ᵐᵒᵖ) := by
  letI := fgModuleCatIsFiniteAbelianCategory k A
  letI := fgModuleCatIsFiniteAbelianCategoryOverField k A
  obtain ⟨P, ⟨hP⟩⟩ := Etingof.Exercise963.exists_progenerator (FGModuleCat.{u} A)
  haveI := hP
  exact ⟨P, Etingof.Theorem_9_6_4_corollary (k := k) (FGModuleCat.{u} A) P⟩

end

end Etingof
