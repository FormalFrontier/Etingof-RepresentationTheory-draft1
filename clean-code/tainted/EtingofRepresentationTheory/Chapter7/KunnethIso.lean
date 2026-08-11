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
  (`Etingof.nonempty_homotopyEquiv_homologyZeroComplex`). A homotopy equivalence in either
  variable stays a homotopy equivalence after tensoring
  (`HomologicalComplex.mapBifunctorMapHomotopy₁`/`₂`), so both the source and the target
  bifunctor of `κ` send it to an isomorphism. The naturality square of `kunnethNatTrans` then
  transports the zero-differential case to arbitrary `C` and `D`.

This is a shorter route than the additivity/four-summand bookkeeping used by
`Problem7_8_7_iv_nonempty`: replacing the abstract biproduct splitting by an explicit homotopy
equivalence lets the naturality square do all of the work, so no compatibility of `κ` with
`Functor.mapBiprod` has to be established. The degenerate case where one factor is acyclic is
still recorded (`Etingof.isZero_kunnethSource_of_acyclic_left` and friends), since it identifies
both sides as zero objects rather than merely asserting that `κ` is invertible there.

## Main results

* `Etingof.isIso_kunnethMap` : `κ_{C,D,i}` is an isomorphism.
* `Etingof.kunnethIso` : the isomorphism `∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D) ≅ Hⁱ(C ⊗ D)`.
* `Etingof.kunnethNatIso` : the same as a natural isomorphism of bifunctors.
* `Etingof.Problem7_8_7_iv` : the book's statement, `Hⁱ(C ⊗ D) ≅ ⨁_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`.
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

section HomotopyEquivalence

/-- The monoidal tensor product of cochain complexes is Mathlib's `mapBifunctorMap` for the
curried tensor bifunctor; this is how the homotopy-invariance API is phrased. -/
lemma tensorHom_eq_mapBifunctorMap {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    (f : C ⟶ C') (g : D ⟶ D') :
    f ⊗ₘ g = HomologicalComplex.mapBifunctorMap f g (curriedTensor (ModuleCat.{u} k))
      (ComplexShape.up ℤ) :=
  rfl

/-- Tensoring cochain complexes is homotopy invariant in both variables. -/
noncomputable def tensorHomotopy {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    {f f' : C ⟶ C'} {g g' : D ⟶ D'} (hf : Homotopy f f') (hg : Homotopy g g') :
    Homotopy (f ⊗ₘ g) (f' ⊗ₘ g') :=
  (Homotopy.ofEq (tensorHom_eq_mapBifunctorMap f g)).trans
    (((HomologicalComplex.mapBifunctorMapHomotopy₁ hf g
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ f' hg
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (tensorHom_eq_mapBifunctorMap f' g').symm))

/-- **Over a field every complex is homotopy equivalent to its homology** (with the zero
differential). Problem 7.8.7(iii) splits `C ≅ E ⊞ homologyZeroComplex C` with `E` acyclic, and
Exercise 7.8.4 contracts `E`; the two structure maps of the second summand are therefore
mutually inverse up to homotopy. -/
lemma nonempty_homotopyEquiv_homologyZeroComplex (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    Nonempty (HomotopyEquiv (homologyZeroComplex C) C) := by
  obtain ⟨E, hE, iso, -⟩ := Problem7_8_7_iii C
  obtain ⟨hEH⟩ := Etingof.Exercise7_8_4 E hE
  -- `biprod.fst ≫ biprod.inl` is null-homotopic because `𝟙 E` is.
  have H₁ : Homotopy ((biprod.fst : E ⊞ homologyZeroComplex C ⟶ E) ≫ biprod.inl)
      (0 : E ⊞ homologyZeroComplex C ⟶ E ⊞ homologyZeroComplex C) :=
    (Homotopy.ofEq (by simp)).trans
      (((hEH.compLeft (biprod.fst : E ⊞ homologyZeroComplex C ⟶ E)).compRight
        (biprod.inl : E ⟶ E ⊞ homologyZeroComplex C)).trans (Homotopy.ofEq (by simp)))
  -- hence `𝟙 = biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr` is homotopic to the second
  -- term alone.
  have H₂ : Homotopy (𝟙 (E ⊞ homologyZeroComplex C))
      ((biprod.snd : E ⊞ homologyZeroComplex C ⟶ homologyZeroComplex C) ≫ biprod.inr) :=
    (Homotopy.ofEq biprod.total.symm).trans
      ((H₁.add (Homotopy.refl _)).trans (Homotopy.ofEq (zero_add _)))
  refine ⟨{ hom := biprod.inr ≫ iso.inv
            inv := iso.hom ≫ biprod.snd
            homotopyHomInvId := Homotopy.ofEq ?_
            homotopyInvHomId := ?_ }⟩
  · rw [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd]
  · exact (Homotopy.ofEq (by simp)).trans
      (((H₂.compLeft iso.hom).compRight iso.inv).symm.trans (Homotopy.ofEq (by simp)))

end HomotopyEquivalence

section Reduction

/-- If both components of an endomorphism of a pair of complexes are null-homotopic to the
identity, then `kunnethSource i` sends it to the identity: `kunnethSource i` only sees the
induced maps on homology. -/
lemma kunnethSource_map_eq_id (i : ℤ) {C D : CochainComplex (ModuleCat.{u} k) ℤ}
    {f : C ⟶ C} {g : D ⟶ D} (hf : Homotopy f (𝟙 C)) (hg : Homotopy g (𝟙 D)) :
    (kunnethSource i).map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
      (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) = 𝟙 _ := by
  have key : (kunnethSource i).map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))
      = (kunnethSource i).map (𝟙 ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ))) := by
    refine Sigma.hom_ext _ _ fun p => ?_
    rw [ι_kunnethSource_map, ι_kunnethSource_map]
    congr 1
    change HomologicalComplex.homologyMap f p.1.1 ⊗ₘ HomologicalComplex.homologyMap g p.1.2
      = HomologicalComplex.homologyMap (𝟙 C) p.1.1 ⊗ₘ HomologicalComplex.homologyMap (𝟙 D) p.1.2
    rw [hf.homologyMap_eq, hg.homologyMap_eq]
  rw [key, CategoryTheory.Functor.map_id]

/-- The same statement for `kunnethTarget i`: tensoring is homotopy invariant, so `Hⁱ(f ⊗ g)`
is the identity as soon as `f` and `g` are homotopic to identities. -/
lemma kunnethTarget_map_eq_id (i : ℤ) {C D : CochainComplex (ModuleCat.{u} k) ℤ}
    {f : C ⟶ C} {g : D ⟶ D} (hf : Homotopy f (𝟙 C)) (hg : Homotopy g (𝟙 D)) :
    (kunnethTarget i).map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
      (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) = 𝟙 _ := by
  have key : (kunnethTarget i).map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))
      = (kunnethTarget i).map (𝟙 ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ))) := by
    change HomologicalComplex.homologyMap (f ⊗ₘ g) i
      = HomologicalComplex.homologyMap (𝟙 C ⊗ₘ 𝟙 D) i
    exact (tensorHomotopy hf hg).homologyMap_eq i
  rw [key, CategoryTheory.Functor.map_id]

/-- A functor on pairs of complexes that is insensitive to homotopies (in the sense of
`kunnethSource_map_eq_id` / `kunnethTarget_map_eq_id`) sends a pair of homotopy equivalences to
an isomorphism. -/
lemma isIso_map_of_homotopyEquiv
    (F : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ) ⥤
      ModuleCat.{u} k)
    (hF : ∀ {C D : CochainComplex (ModuleCat.{u} k) ℤ} {f : C ⟶ C} {g : D ⟶ D},
      Homotopy f (𝟙 C) → Homotopy g (𝟙 D) →
        F.map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) = 𝟙 _)
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    (eC : HomotopyEquiv C C') (eD : HomotopyEquiv D D') :
    IsIso (F.map ((eC.hom, eD.hom) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
      (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C', D'))) := by
  refine ⟨F.map ((eC.inv, eD.inv) : ((C', D') : (CochainComplex (ModuleCat.{u} k) ℤ) ×
    (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)), ?_, ?_⟩
  · rw [← F.map_comp]
    exact hF eC.homotopyHomInvId eD.homotopyHomInvId
  · rw [← F.map_comp]
    exact hF eC.homotopyInvHomId eD.homotopyInvHomId

/-- **The Künneth natural transformation is an isomorphism at every pair of complexes.** Each
factor is homotopy equivalent to its homology with zero differential; both the source and the
target bifunctor turn that homotopy equivalence into an isomorphism, and the split case handles
the zero-differential pair, so the naturality square forces `κ` itself to be invertible. -/
instance isIso_kunnethNatTrans_app (i : ℤ)
    (X : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) :
    IsIso ((kunnethNatTrans (k := k) i).app X) := by
  obtain ⟨C, D⟩ := X
  obtain ⟨eC⟩ := nonempty_homotopyEquiv_homologyZeroComplex C
  obtain ⟨eD⟩ := nonempty_homotopyEquiv_homologyZeroComplex D
  haveI : IsIso ((kunnethSource i).map ((eC.hom, eD.hom) :
      ((homologyZeroComplex C, homologyZeroComplex D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))) :=
    isIso_map_of_homotopyEquiv _ (fun hf hg => kunnethSource_map_eq_id i hf hg) eC eD
  haveI : IsIso ((kunnethTarget i).map ((eC.hom, eD.hom) :
      ((homologyZeroComplex C, homologyZeroComplex D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))) :=
    isIso_map_of_homotopyEquiv _ (fun hf hg => kunnethTarget_map_eq_id i hf hg) eC eD
  haveI : IsIso ((kunnethNatTrans (k := k) i).app
      (homologyZeroComplex C, homologyZeroComplex D)) :=
    isIso_kunnethMap_homologyZeroComplex C D i
  haveI : IsIso ((kunnethSource i).map ((eC.hom, eD.hom) :
      ((homologyZeroComplex C, homologyZeroComplex D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) ≫
      (kunnethNatTrans i).app (C, D)) := by
    rw [(kunnethNatTrans i).naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left ((kunnethSource i).map ((eC.hom, eD.hom) :
    ((homologyZeroComplex C, homologyZeroComplex D) :
      (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)))
    ((kunnethNatTrans (k := k) i).app (C, D))

/-- **The Künneth map is an isomorphism.** Over a field the natural cross product
`∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D) ⟶ Hⁱ(C ⊗ D)` is invertible. -/
instance isIso_kunnethMap (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    IsIso (kunnethMap C D i) :=
  isIso_kunnethNatTrans_app i (C, D)

end Reduction

section API

variable (C D : CochainComplex (ModuleCat.{u} k) ℤ)

/-- **The Künneth isomorphism**, `∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D) ≅ Hⁱ(C ⊗ D)`, given by the natural
cross product `kunnethMap`. -/
noncomputable def kunnethIso (i : ℤ) :
    (∐ fun p : KunnethIndex i => C.homology p.1.1 ⊗ D.homology p.1.2) ≅
      (tensorComplex C D).homology i :=
  asIso (kunnethMap C D i)

@[simp]
lemma kunnethIso_hom (i : ℤ) : (kunnethIso C D i).hom = kunnethMap C D i := rfl

instance isIso_kunnethNatTrans (i : ℤ) : IsIso (kunnethNatTrans (k := k) i) :=
  NatIso.isIso_of_isIso_app _

/-- **The Künneth natural isomorphism of bifunctors**
`(C, D) ↦ ∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)` ≅ `(C, D) ↦ Hⁱ(C ⊗ D)`. -/
noncomputable def kunnethNatIso (i : ℤ) :
    kunnethSource (k := k) i ≅ kunnethTarget (k := k) i :=
  asIso (kunnethNatTrans i)

@[simp]
lemma kunnethNatIso_hom (i : ℤ) : (kunnethNatIso (k := k) i).hom = kunnethNatTrans i := rfl

@[simp]
lemma kunnethNatIso_hom_app (i : ℤ)
    (X : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) :
    (kunnethNatIso (k := k) i).hom.app X = kunnethMap X.1 X.2 i := rfl

/-- **Problem 7.8.7(iv), the Künneth formula.** There is an isomorphism of vector spaces
`Hⁱ(C ⊗ D) ≅ ⨁_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`, natural in `C` and `D` (see `kunnethNatIso`). -/
noncomputable def Problem7_8_7_iv (i : ℤ) :
    (tensorComplex C D).homology i ≅
      ∐ fun p : KunnethIndex i => C.homology p.1.1 ⊗ D.homology p.1.2 :=
  (kunnethIso C D i).symm

/-! ### The acyclic case

If either factor is acyclic then both sides of the Künneth map are zero objects: the source
because each summand `Hʲ(C) ⊗ Hᵐ(D)` has a vanishing tensor factor, the target by
`Problem7_8_7_ii`. This is the degenerate case of the theorem, recorded separately because it is
what identifies the "extra" summands in a splitting argument.
-/

/-- If `C` is acyclic then every summand `Hʲ(C) ⊗ Hᵐ(D)` vanishes, so the source of the Künneth
map is a zero object. -/
lemma isZero_kunnethSource_of_acyclic_left (i : ℤ) (hC : C.Acyclic) :
    IsZero ((kunnethSource i).obj (C, D)) := by
  rw [IsZero.iff_id_eq_zero]
  refine Sigma.hom_ext _ _ fun p => ?_
  have hz : IsZero (C.homology p.1.1 ⊗ D.homology p.1.2) := by
    rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id,
      (IsZero.iff_id_eq_zero _).mp
        ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hC p.1.1)),
      MonoidalPreadditive.zero_tensor]
  rw [comp_zero]
  exact hz.eq_zero_of_src _

/-- The mirror statement for an acyclic second factor. -/
lemma isZero_kunnethSource_of_acyclic_right (i : ℤ) (hD : D.Acyclic) :
    IsZero ((kunnethSource i).obj (C, D)) := by
  rw [IsZero.iff_id_eq_zero]
  refine Sigma.hom_ext _ _ fun p => ?_
  have hz : IsZero (C.homology p.1.1 ⊗ D.homology p.1.2) := by
    rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id,
      (IsZero.iff_id_eq_zero _).mp
        ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hD p.1.2)),
      MonoidalPreadditive.tensor_zero]
  rw [comp_zero]
  exact hz.eq_zero_of_src _

/-- If either factor is acyclic then `Hⁱ(C ⊗ D)` is a zero object: this is `Problem7_8_7_ii`. -/
lemma isZero_kunnethTarget_of_acyclic (i : ℤ) (h : C.Acyclic ∨ D.Acyclic) :
    IsZero ((kunnethTarget i).obj (C, D)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (Problem7_8_7_ii C D h i)

end API

end Etingof
