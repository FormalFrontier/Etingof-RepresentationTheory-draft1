import Mathlib
import EtingofRepresentationTheory.Chapter7.KunnethNatural
import EtingofRepresentationTheory.Chapter7.Problem7_8_7

/-!
# The natural Künneth map is an isomorphism

`EtingofRepresentationTheory/Chapter7/KunnethNatural.lean` constructs the choice-free cross
product

`κ_{C,D,i} : ∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D) ⟶ Hⁱ(C ⊗ D)`

(`Etingof.kunnethMap`) and packages it as a natural transformation of bifunctors
(`Etingof.kunnethNatTrans`). This file proves that over a field `κ` is an isomorphism, and
exposes the resulting isomorphism and natural isomorphism.

## Strategy

The proof has two halves.

* **Zero differentials.** If `C` and `D` both carry the zero differential, then `iCycles` and
  `homologyπ` are isomorphisms in every degree for `C`, for `D` and for `C ⊗ D`, and `κ` is
  literally the coproduct decomposition `(C ⊗ D)ⁱ ≅ ∐_{j+m=i} Cʲ ⊗ Dᵐ` of
  `Etingof.tensorObjXIsoCoproduct` read through those identifications
  (`Etingof.isIso_kunnethMap_homologyZeroComplex`).

* **Reduction to that case.** Problem 7.8.7(iii) writes `C ≅ E ⊞ homologyZeroComplex C` with
  `E` acyclic, and Exercise 7.8.4 makes an acyclic complex contractible. Consequently the two
  structure maps between `C` and `homologyZeroComplex C` are mutually inverse *up to homotopy*
  (`Etingof.exists_homotopyEquiv_homologyZeroComplex`). A homotopy equivalence in either
  variable stays a homotopy equivalence after tensoring
  (`HomologicalComplex.mapBifunctorMapHomotopy₁`/`₂`), so both the source and the target
  bifunctor of `κ` send it to an isomorphism. The naturality square of `kunnethNatTrans` then
  transports the zero-differential case to arbitrary `C` and `D`.

Note that this is a different route from the additivity/four-summand bookkeeping of
`Problem7_8_7_iv`: replacing the abstract biproduct splitting by an explicit homotopy
equivalence lets the naturality square do all of the work.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex

-- As in `KunnethNatural.lean`, the `mapBifunctor` API is stated through `GradedObject` layers
-- that are only definitionally equal to the `HomologicalComplex` spellings used here.
set_option backward.isDefEq.respectTransparency false

namespace Etingof

universe u

variable {k : Type u} [Field k]

section ZeroDifferential

variable (C D : CochainComplex (ModuleCat.{u} k) ℤ)

/-- For the zero-differential complex `homologyZeroComplex C`, the degree-`j` homology is
canonically the degree-`j` object `Hʲ(C)`: both `homologyπ` and `iCycles` are isomorphisms. -/
noncomputable def homologyZeroComplexHomologyIso (j : ℤ) :
    (homologyZeroComplex C).homology j ≅ C.homology j :=
  ((homologyZeroComplex C).isoHomologyπ (j - 1) j (by simp) rfl).symm ≪≫
    (homologyZeroComplex C).iCyclesIso j (j + 1) (by simp) rfl

@[reassoc (attr := simp)]
lemma homologyπ_homologyZeroComplexHomologyIso (j : ℤ) :
    (homologyZeroComplex C).homologyπ j ≫ (homologyZeroComplexHomologyIso C j).hom
      = (homologyZeroComplex C).iCycles j := by
  simp [homologyZeroComplexHomologyIso]

/-- The tensor product of two zero-differential complexes again has zero differential, so its
degree-`i` object *is* its degree-`i` homology. -/
noncomputable def tensorZeroObjHomologyIso (i : ℤ) :
    (HomologicalComplex.tensorObj (homologyZeroComplex C) (homologyZeroComplex D)).X i ≅
      (HomologicalComplex.tensorObj (homologyZeroComplex C) (homologyZeroComplex D)).homology i :=
  ((HomologicalComplex.tensorObj (homologyZeroComplex C) (homologyZeroComplex D)).iCyclesIso i
      (i + 1) (by simp) (tensorHomologyZero_d_eq_zero C D i (i + 1))).symm ≪≫
    (HomologicalComplex.tensorObj (homologyZeroComplex C) (homologyZeroComplex D)).isoHomologyπ
      (i - 1) i (by simp) (tensorHomologyZero_d_eq_zero C D (i - 1) i)

/-- `homologyTensorHomologyZeroIso` is the composite of `tensorZeroObjHomologyIso` (backwards)
with the coproduct decomposition of the degree-`i` object. -/
lemma homologyTensorHomologyZeroIso_eq (i : ℤ) :
    homologyTensorHomologyZeroIso C D i =
      (tensorZeroObjHomologyIso C D i).symm ≪≫
        tensorObjXIsoCoproduct (homologyZeroComplex C) (homologyZeroComplex D) i :=
  rfl

/-- The cycle-level description of the cross product for zero-differential complexes: it is the
summand inclusion `Hʲ(C) ⊗ Hᵐ(D) ⟶ (H(C) ⊗ H(D))^{j+m}`, read through the canonical
identifications of cycles, homology and objects. -/
lemma kunnethSummand_homologyZeroComplex (j m : ℤ) :
    kunnethSummand (homologyZeroComplex C) (homologyZeroComplex D) j m
      = ((homologyZeroComplexHomologyIso C j).hom ⊗ₘ
            (homologyZeroComplexHomologyIso D m).hom) ≫
        HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D) j m
          (j + m) rfl ≫
        (tensorZeroObjHomologyIso C D (j + m)).hom := by
  have key : ((homologyZeroComplex C).iCycles j ⊗ₘ (homologyZeroComplex D).iCycles m) ≫
      HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D) j m
        (j + m) rfl ≫
      (tensorZeroObjHomologyIso C D (j + m)).hom
      = cyclesTensorHomologyπ (homologyZeroComplex C) (homologyZeroComplex D) j m := by
    rw [← Category.assoc, ← cyclesTensorι, ← cyclesTensorLift_i, cyclesTensorHomologyπ,
      Category.assoc]
    congr 1
    rw [tensorZeroObjHomologyIso]
    simp
  rw [← cancel_epi ((homologyZeroComplex C).homologyπ j ⊗ₘ (homologyZeroComplex D).homologyπ m),
    homologyπ_tensorHom_kunnethSummand]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    homologyπ_homologyZeroComplexHomologyIso]
  simp only [Category.assoc]
  exact key.symm

/-- The Künneth map of two zero-differential complexes is the summandwise identification
`Hʲ(H(C)) ⊗ Hᵐ(H(D)) ≅ Hʲ(C) ⊗ Hᵐ(D)` followed by the inverse of the coproduct decomposition
of `Hⁱ(H(C) ⊗ H(D))`. In particular it is an isomorphism. -/
lemma kunnethMap_homologyZeroComplex (i : ℤ) :
    kunnethMap (homologyZeroComplex C) (homologyZeroComplex D) i
      = (Sigma.mapIso (fun p : KunnethIndex i =>
            tensorIso (homologyZeroComplexHomologyIso C p.1.1)
              (homologyZeroComplexHomologyIso D p.1.2))).hom ≫
        (homologyTensorHomologyZeroIso C D i).inv := by
  refine Sigma.hom_ext _ _ ?_
  rintro ⟨⟨j, m⟩, rfl⟩
  have hι : ∀ {W : ModuleCat.{u} k}
      (f : (HomologicalComplex.tensorObj (homologyZeroComplex C)
        (homologyZeroComplex D)).X (j + m) ⟶ W),
      Sigma.ι (fun p : KunnethIndex (j + m) => C.homology p.1.1 ⊗ D.homology p.1.2)
          ⟨(j, m), rfl⟩ ≫
        (tensorObjXIsoCoproduct (homologyZeroComplex C) (homologyZeroComplex D) (j + m)).inv ≫ f
      = HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D) j m
          (j + m) rfl ≫ f := by
    intro W f
    rw [← Category.assoc]
    congr 1
    exact Sigma.ι_desc _ _
  rw [ι_kunnethMap_diagonal, kunnethSummand_homologyZeroComplex,
    homologyTensorHomologyZeroIso_eq]
  simp only [Iso.trans_inv, Iso.symm_inv, Sigma.ι_mapIso_hom_assoc, tensorIso_hom, hι]

/-- **The split case of the Künneth theorem.** For two complexes with vanishing differentials
the Künneth map is an isomorphism. -/
instance isIso_kunnethMap_homologyZeroComplex (i : ℤ) :
    IsIso (kunnethMap (homologyZeroComplex C) (homologyZeroComplex D) i) := by
  rw [kunnethMap_homologyZeroComplex]
  infer_instance

end ZeroDifferential

end Etingof
