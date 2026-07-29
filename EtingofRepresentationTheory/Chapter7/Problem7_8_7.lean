import Mathlib
import EtingofRepresentationTheory.Chapter7.Exercise7_8_4
import EtingofRepresentationTheory.Chapter7.TensorComplexBiprod

set_option backward.isDefEq.respectTransparency false

/-!
# Problem 7.8.7: The tensor product of complexes and the Künneth formula

**Problem 7.8.7.** Let `C•` and `D•` be complexes of modules over a commutative ring `A`.
Define the tensor product complex `(C ⊗ D)•` by the formula

`(C ⊗ D)_i = ⨁_{j+m=i} C_j ⊗_A D_m`,

with differentials

`d_i^{C⊗D}|_{C_j ⊗ D_m} = d_j^C ⊗ 1 + (-1)^j · 1 ⊗ d_m^D`.

* (i) Show that this is a complex.
* Now assume that `A = k` is a field.
* (ii) Show that if `C` or `D` is an exact sequence, then so is `C ⊗ D`.
  (Hint: Use the decomposition of Exercise 7.8.4.)
* (iii) Show that any complex `C` can be identified with a direct sum of an exact sequence
  and the complex consisting of `Hⁱ(C)` with the zero differentials, in such a way that the
  induced isomorphism `Hⁱ(C) → Hⁱ(C)` is the identity.
* (iv) Show that there is a natural isomorphism of vector spaces
  `Hⁱ(C ⊗ D) ≅ ⨁_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`. This is the **Künneth** formula.

## Formalization

We model complexes as `CochainComplex (ModuleCat k) ℤ` (i.e.
`HomologicalComplex (ModuleCat k) (ComplexShape.up ℤ)`). Mathlib's
`HomologicalComplex.tensorObj` is exactly the tensor product complex of the statement: the
degree-`i` object is the coproduct of `Cⱼ ⊗ Dₘ` over `j + m = i` (with `j + m = i` supplied
by `ComplexShape.up ℤ` via `TensorSigns`) and its differential carries the Koszul sign
`(-1)ʲ`, matching Etingof's formula. We write `Etingof.tensorComplex C D` for it.

* **(i)** `Etingof.Problem7_8_7_i` records that `tensorComplex C D` is a complex
  (`d ≫ d = 0` in every degree); it holds by construction (`HomologicalComplex.d_comp_d`).
* **(ii)** `Etingof.Problem7_8_7_ii`: over a field, if `C` or `D` is acyclic then so is
  `C ⊗ D`.
* **(iii)** `Etingof.Problem7_8_7_iii`: every complex `C` is isomorphic to
  `E ⊞ (homologyZeroComplex C)` with `E` acyclic, where `homologyZeroComplex C` is the
  complex whose degree-`i` object is `Hⁱ(C)` with zero differentials. The clause "the
  induced isomorphism `Hⁱ(C) → Hⁱ(C)` is the identity" is encoded as: the map
  `homologyZeroComplex C ⟶ C` given by `biprod.inr ≫ iso.inv` induces an isomorphism on
  `Hⁱ` (its `homologyMap` is `IsIso`); since `Hⁱ(homologyZeroComplex C)` is canonically
  `Hⁱ(C)`, this is exactly the "identity on homology" refinement.
* **(iv)** `Etingof.Problem7_8_7_iv_nonempty` (Künneth): `Hⁱ(C ⊗ D)` is isomorphic to the
  coproduct of `Hʲ(C) ⊗ Hᵐ(D)` over `j + m = i`. This file proves only the bare existence of
  such an isomorphism; the *natural* Künneth isomorphism, which is what
  `Etingof.Problem7_8_7_iv` now denotes, is built in
  `EtingofRepresentationTheory/Chapter7/KunnethNatural.lean` and
  `EtingofRepresentationTheory/Chapter7/KunnethIso.lean`.
-/

open CategoryTheory Limits MonoidalCategory

namespace Etingof

universe u

variable {k : Type u} [Field k]

/-- The complex whose degree-`i` object is the homology `Hⁱ(C)` and whose differentials are
all zero (used in part (iii)). -/
noncomputable def homologyZeroComplex (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ where
  X i := C.homology i
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

section SplitField

variable (C : CochainComplex (ModuleCat.{u} k) ℤ)

/-!
### Construction for part (iii)

Over a field, in each degree the projection `homologyπ : Zⁱ ↠ Hⁱ(C)` splits (choose a
section `rho`) and the inclusion of cycles `iCycles : Zⁱ ↪ Cⁱ` splits (choose a retraction
`tau`). These degreewise splittings assemble into a chain map `sMap : Hⁱ(C)[0] ⟶ C` (a
section landing in cycles) and a chain map `pMap : C ⟶ Hⁱ(C)[0]` (a retraction vanishing on
boundaries), with `sMap ≫ pMap = 𝟙` and `homologyMap (pMap ≫ sMap) = 𝟙`. The idempotent
`𝟙 - pMap ≫ sMap` then splits (abelian categories are idempotent complete) into the acyclic
complement `E`, giving `C ≅ E ⊞ homologyZeroComplex C`.
-/

/-- A degreewise section of `homologyπ` (exists since `Hⁱ(C)` is projective over a field). -/
private lemma exists_rho (i : ℤ) :
    ∃ g : (C.homology i) →ₗ[k] (C.cycles i), (C.homologyπ i).hom ∘ₗ g = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _
    ((ModuleCat.epi_iff_range_eq_top _).mp inferInstance)

/-- The chosen linear section of `homologyπ i`. -/
noncomputable def rhoLin (i : ℤ) : (C.homology i) →ₗ[k] (C.cycles i) := (exists_rho C i).choose

lemma rhoLin_spec (i : ℤ) : (C.homologyπ i).hom ∘ₗ rhoLin C i = LinearMap.id :=
  (exists_rho C i).choose_spec

/-- The section `Hⁱ(C) ⟶ Zⁱ` as a morphism. -/
noncomputable def rho (i : ℤ) : C.homology i ⟶ C.cycles i := ModuleCat.ofHom (rhoLin C i)

@[reassoc]
lemma rho_homologyπ (i : ℤ) : rho C i ≫ C.homologyπ i = 𝟙 (C.homology i) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, rho, ModuleCat.hom_ofHom, ModuleCat.hom_id]
  exact rhoLin_spec C i

/-- A degreewise retraction of `iCycles` (exists since `iCycles` is injective over a field). -/
private lemma exists_tau (i : ℤ) :
    ∃ g : (C.X i) →ₗ[k] (C.cycles i), g ∘ₗ (C.iCycles i).hom = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective _
    ((ModuleCat.mono_iff_ker_eq_bot _).mp inferInstance)

/-- The chosen linear retraction of `iCycles i`. -/
noncomputable def tauLin (i : ℤ) : (C.X i) →ₗ[k] (C.cycles i) := (exists_tau C i).choose

lemma tauLin_spec (i : ℤ) : tauLin C i ∘ₗ (C.iCycles i).hom = LinearMap.id :=
  (exists_tau C i).choose_spec

/-- The retraction `Cⁱ ⟶ Zⁱ` as a morphism. -/
noncomputable def tau (i : ℤ) : C.X i ⟶ C.cycles i := ModuleCat.ofHom (tauLin C i)

@[reassoc]
lemma iCycles_tau (i : ℤ) : C.iCycles i ≫ tau C i = 𝟙 (C.cycles i) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, tau, ModuleCat.hom_ofHom, ModuleCat.hom_id]
  exact tauLin_spec C i

/-- The section chain map `homologyZeroComplex C ⟶ C`, degreewise `rho ≫ iCycles`. -/
noncomputable def sMap : homologyZeroComplex C ⟶ C where
  f i := rho C i ≫ C.iCycles i
  comm' i j hij := by
    have hd : (homologyZeroComplex C).d i j = 0 := rfl
    rw [hd, zero_comp, Category.assoc, C.iCycles_d, comp_zero]

/-- The retraction chain map `C ⟶ homologyZeroComplex C`, degreewise `tau ≫ homologyπ`. -/
noncomputable def pMap : C ⟶ homologyZeroComplex C where
  f i := tau C i ≫ C.homologyπ i
  comm' i j hij := by
    have hd : (homologyZeroComplex C).d i j = 0 := rfl
    rw [hd, comp_zero, ← C.toCycles_i i j]
    simp only [Category.assoc, iCycles_tau_assoc,
      HomologicalComplex.toCycles_comp_homologyπ]

/-- `sMap ≫ pMap = 𝟙`: the section followed by the retraction is the identity on homology. -/
lemma sMap_pMap : sMap C ≫ pMap C = 𝟙 (homologyZeroComplex C) := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change (rho C i ≫ C.iCycles i) ≫ (tau C i ≫ C.homologyπ i) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (C.iCycles i), iCycles_tau, Category.id_comp,
    rho_homologyπ]

/-- `homologyMap (pMap ≫ sMap) = 𝟙`: the composite `pMap ≫ sMap` induces the identity on
homology (here `pMap ≫ sMap` is degreewise the projection onto a complement of the
boundaries, which is homologous to the identity). -/
lemma homologyMap_pMap_sMap (i : ℤ) :
    HomologicalComplex.homologyMap (pMap C ≫ sMap C) i = 𝟙 (C.homology i) := by
  have hcyc : HomologicalComplex.cyclesMap (pMap C ≫ sMap C) i = C.homologyπ i ≫ rho C i := by
    rw [← cancel_mono (C.iCycles i), HomologicalComplex.cyclesMap_i, HomologicalComplex.comp_f]
    change C.iCycles i ≫ ((tau C i ≫ C.homologyπ i) ≫ (rho C i ≫ C.iCycles i))
      = (C.homologyπ i ≫ rho C i) ≫ C.iCycles i
    simp only [Category.assoc, iCycles_tau_assoc]
  have hnat := HomologicalComplex.homologyπ_naturality (pMap C ≫ sMap C) i
  rw [hcyc, Category.assoc, rho_homologyπ, Category.comp_id] at hnat
  rw [← cancel_epi (C.homologyπ i), Category.comp_id]
  exact hnat

end SplitField

/-- Problem 7.8.7(i): the tensor product `C ⊗ D` is a complex, i.e. consecutive
differentials compose to zero. -/
theorem Problem7_8_7_i (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i j l : ℤ) :
    (tensorComplex C D).d i j ≫ (tensorComplex C D).d j l = 0 :=
  (tensorComplex C D).d_comp_d i j l

/-- A complex whose identity morphism is null-homotopic (contractible) is acyclic: homotopic
chain maps induce equal maps on homology, so `𝟙 (Hⁱ X) = homologyMap (𝟙 X) i =
homologyMap 0 i = 0`, whence `Hⁱ X` is zero in every degree. -/
private lemma acyclic_of_homotopy_id_zero {X : CochainComplex (ModuleCat.{u} k) ℤ}
    (H : Homotopy (𝟙 X) 0) : X.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h := H.homologyMap_eq i
  rwa [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at h

/-- Problem 7.8.7(ii): over a field, if either factor is an exact (acyclic) complex, then so
is the tensor product `C ⊗ D`. -/
theorem Problem7_8_7_ii (C D : CochainComplex (ModuleCat.{u} k) ℤ)
    (h : C.Acyclic ∨ D.Acyclic) :
    (tensorComplex C D).Acyclic := by
  -- Over a field an acyclic complex is contractible (`Exercise7_8_4`: `𝟙` is null-homotopic).
  -- Whiskering that contracting homotopy through the tensor bifunctor makes `𝟙 (C ⊗ D)`
  -- null-homotopic, hence `C ⊗ D` acyclic.
  -- `tensorHom (𝟙) (𝟙) = 𝟙`: the tensor bifunctor sends `𝟙` to `𝟙`, so the induced
  -- morphism on total complexes is `total.map (𝟙) = 𝟙`.
  have hid : HomologicalComplex.mapBifunctorMap (𝟙 C) (𝟙 D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) = 𝟙 (tensorComplex C D) := by
    rw [HomologicalComplex.mapBifunctorMap, CategoryTheory.Functor.map_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, HomologicalComplex₂.total.map_id]
    rfl
  -- `Acyclic` is a `Prop`, so split the disjunction first, then build the null-homotopy of
  -- `𝟙 (C ⊗ D)` in each branch by whiskering the contracting homotopy of the acyclic factor.
  rcases h with hC | hD
  · obtain ⟨hCH⟩ := Etingof.Exercise7_8_4 C hC
    -- `tensorHom 0 (𝟙 D) = 0`: the bifunctor sends `0` to `0`, so each injection composes to `0`.
    have hz : HomologicalComplex.mapBifunctorMap (0 : C ⟶ C) (𝟙 D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) = 0 := by
      apply HomologicalComplex.hom_ext
      intro j
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro i₁ i₂ hji
      simp
    have Hmap := HomologicalComplex.mapBifunctorMapHomotopy₁ hCH (𝟙 D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
    exact acyclic_of_homotopy_id_zero
      ((Homotopy.ofEq hid.symm).trans (Hmap.trans (Homotopy.ofEq hz)))
  · obtain ⟨hDH⟩ := Etingof.Exercise7_8_4 D hD
    have hz : HomologicalComplex.mapBifunctorMap (𝟙 C) (0 : D ⟶ D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) = 0 := by
      apply HomologicalComplex.hom_ext
      intro j
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro i₁ i₂ hji
      simp
    have Hmap := HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 C) hDH
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
    exact acyclic_of_homotopy_id_zero
      ((Homotopy.ofEq hid.symm).trans (Hmap.trans (Homotopy.ofEq hz)))

/-- Problem 7.8.7(iii): every complex `C` decomposes as a direct sum of an acyclic complex
`E` and the zero-differential complex on its homology `Hⁱ(C)`, in a way that induces the
identity on homology (encoded here as: the summand map `homologyZeroComplex C ⟶ C` is a
homology isomorphism in every degree). -/
theorem Problem7_8_7_iii (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    ∃ (E : CochainComplex (ModuleCat.{u} k) ℤ) (_ : E.Acyclic)
      (iso : C ≅ E ⊞ homologyZeroComplex C),
      ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap
        ((biprod.inr : homologyZeroComplex C ⟶ E ⊞ homologyZeroComplex C) ≫ iso.inv) i) := by
  -- `sMap ≫ pMap = 𝟙`, so `pMap ≫ sMap` is idempotent; `𝟙 - pMap ≫ sMap` is the
  -- complementary idempotent, which splits (abelian ⇒ idempotent complete) into `E`.
  have hXX : (pMap C ≫ sMap C) ≫ (pMap C ≫ sMap C) = pMap C ≫ sMap C := by
    rw [Category.assoc, ← Category.assoc (sMap C), sMap_pMap C, Category.id_comp]
  obtain ⟨E, ι, r, hιr, hrι⟩ :=
    IsIdempotentComplete.idempotents_split C (𝟙 C - pMap C ≫ sMap C) (by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, hXX]
      abel)
  -- `hιr : ι ≫ r = 𝟙 E`, `hrι : r ≫ ι = 𝟙 C - pMap C ≫ sMap C`.
  have hqp : (𝟙 C - pMap C ≫ sMap C) ≫ pMap C = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, sMap_pMap C, Category.comp_id,
      sub_self]
  have hsq : sMap C ≫ (𝟙 C - pMap C ≫ sMap C) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, sMap_pMap C, Category.id_comp,
      sub_self]
  haveI : IsSplitEpi r := ⟨⟨ι, hιr⟩⟩
  haveI : IsSplitMono ι := ⟨⟨r, hιr⟩⟩
  have hιp : ι ≫ pMap C = 0 := by
    rw [← cancel_epi r, comp_zero, ← Category.assoc, hrι, hqp]
  have hsr : sMap C ≫ r = 0 := by
    rw [← cancel_mono ι, zero_comp, Category.assoc, hrι, hsq]
  -- The isomorphism `C ≅ E ⊞ homologyZeroComplex C`.
  let iso : C ≅ E ⊞ homologyZeroComplex C :=
    { hom := biprod.lift r (pMap C)
      inv := biprod.desc ι (sMap C)
      hom_inv_id := by rw [biprod.lift_desc, hrι]; abel
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [hιr, sMap_pMap C, hιp, hsr] }
  -- `E` is acyclic: `homologyMap (𝟙 - pMap ≫ sMap) = 0`, and `𝟙_E` factors through it.
  have hqhom : ∀ i, HomologicalComplex.homologyMap (𝟙 C - pMap C ≫ sMap C) i = 0 := by
    intro i
    rw [HomologicalComplex.homologyMap_sub, HomologicalComplex.homologyMap_id,
      homologyMap_pMap_sMap C i, sub_self]
  have hAc : E.Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have hid : 𝟙 (E.homology i)
        = HomologicalComplex.homologyMap ι i ≫ HomologicalComplex.homologyMap r i := by
      rw [← HomologicalComplex.homologyMap_comp, hιr, HomologicalComplex.homologyMap_id]
    have he0 : HomologicalComplex.homologyMap r i ≫ HomologicalComplex.homologyMap ι i = 0 := by
      rw [← HomologicalComplex.homologyMap_comp, hrι, hqhom i]
    calc 𝟙 (E.homology i)
        = (HomologicalComplex.homologyMap ι i ≫ HomologicalComplex.homologyMap r i)
            ≫ (HomologicalComplex.homologyMap ι i ≫ HomologicalComplex.homologyMap r i) := by
          rw [← hid, Category.comp_id]
      _ = HomologicalComplex.homologyMap ι i
            ≫ (HomologicalComplex.homologyMap r i ≫ HomologicalComplex.homologyMap ι i)
            ≫ HomologicalComplex.homologyMap r i := by simp only [Category.assoc]
      _ = 0 := by rw [he0, zero_comp, comp_zero]
  refine ⟨E, hAc, iso, ?_⟩
  intro i
  have hbi : (biprod.inr : homologyZeroComplex C ⟶ E ⊞ homologyZeroComplex C) ≫ iso.inv
      = sMap C := by
    change biprod.inr ≫ biprod.desc ι (sMap C) = sMap C
    rw [biprod.inr_desc]
  rw [hbi]
  -- `homologyMap (sMap C) i` is iso, with inverse `homologyMap (pMap C) i`.
  refine ⟨HomologicalComplex.homologyMap (pMap C) i, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, sMap_pMap C, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp]; exact homologyMap_pMap_sMap C i

/-!
### Homology of a tensor of two zero-differential complexes

The final step of the Künneth argument (part iv) identifies `Hⁱ(C ⊗ D)`, after the four-way
split, with the homology of `tensorComplex (homologyZeroComplex C) (homologyZeroComplex D)`, a
tensor of two complexes whose differentials all vanish. Its differential vanishes in every
degree, so its homology at `i` is its degree-`i` object, which is the internal coproduct of the
`Cⱼ ⊗ Dₘ` over `j + m = i`. We package that identification as the reusable
`homologyTensorHomologyZeroIso`.
-/

/-- The degree-`i` object of a tensor of complexes, `(C ⊗ D)ᵢ`, is the categorical coproduct of
the summands `Cᵢ₁ ⊗ Dᵢ₂` over `i₁ + i₂ = i`. This "total degree object as explicit `∐`" iso is
general (it holds for any two complexes admitting a tensor product) and reusable. -/
noncomputable def tensorObjXIsoCoproduct
    (K₁ K₂ : CochainComplex (ModuleCat.{u} k) ℤ) [HomologicalComplex.HasTensor K₁ K₂] (i : ℤ) :
    (HomologicalComplex.tensorObj K₁ K₂).X i ≅
      ∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = i}) => K₁.X p.1.1 ⊗ K₂.X p.1.2 where
  hom := HomologicalComplex.mapBifunctorDesc
    (fun i₁ i₂ h => Sigma.ι (fun p : {p : ℤ × ℤ // p.1 + p.2 = i} => K₁.X p.1.1 ⊗ K₂.X p.1.2)
      ⟨(i₁, i₂), h⟩)
  inv := Sigma.desc (fun p => HomologicalComplex.ιTensorObj K₁ K₂ p.1.1 p.1.2 i p.2)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    simp [HomologicalComplex.ιTensorObj]
  inv_hom_id := by
    apply Sigma.hom_ext
    rintro ⟨⟨i₁, i₂⟩, h⟩
    simp [HomologicalComplex.ιTensorObj]

@[simp] lemma homologyZeroComplex_d (C : CochainComplex (ModuleCat.{u} k) ℤ) (i j : ℤ) :
    (homologyZeroComplex C).d i j = 0 := rfl

/-- A tensor of two zero-differential complexes has zero differential in every degree: both the
`d₁` and `d₂` summands of the total differential vanish because each factor differential does. -/
lemma tensorHomologyZero_d_eq_zero (C D : CochainComplex (ModuleCat.{u} k) ℤ) (j j' : ℤ) :
    (HomologicalComplex.tensorObj (homologyZeroComplex C) (homologyZeroComplex D)).d j j' = 0 := by
  have hd₁ : ∀ i₁ i₂ : ℤ,
      HomologicalComplex.mapBifunctor.d₁ (homologyZeroComplex C) (homologyZeroComplex D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i₁ i₂ j' = 0 := by
    intro i₁ i₂
    by_cases hrel : (ComplexShape.up ℤ).Rel i₁ ((ComplexShape.up ℤ).next i₁)
    · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hrel i₂ j']
      simp
    · apply HomologicalComplex.mapBifunctor.d₁_eq_zero
      exact hrel
  have hd₂ : ∀ i₁ i₂ : ℤ,
      HomologicalComplex.mapBifunctor.d₂ (homologyZeroComplex C) (homologyZeroComplex D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i₁ i₂ j' = 0 := by
    intro i₁ i₂
    by_cases hrel : (ComplexShape.up ℤ).Rel i₂ ((ComplexShape.up ℤ).next i₂)
    · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ i₁ hrel j']
      simp
    · apply HomologicalComplex.mapBifunctor.d₂_eq_zero
      exact hrel
  have hD₁ : HomologicalComplex.mapBifunctor.D₁ (homologyZeroComplex C) (homologyZeroComplex D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j j' = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rw [HomologicalComplex.mapBifunctor.ι_D₁, comp_zero, hd₁]
  have hD₂ : HomologicalComplex.mapBifunctor.D₂ (homologyZeroComplex C) (homologyZeroComplex D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j j' = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rw [HomologicalComplex.mapBifunctor.ι_D₂, comp_zero, hd₂]
  rw [HomologicalComplex.mapBifunctor.d_eq, hD₁, hD₂, add_zero]

/-- Homology of a tensor of two zero-differential complexes: since the total differential
vanishes, `Hⁱ` is the degree-`i` object, which is the coproduct of the `Cᵢ₁ ⊗ Dᵢ₂` over
`i₁ + i₂ = i`. This is the final identification used in the Künneth formula. -/
noncomputable def homologyTensorHomologyZeroIso
    (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    (tensorComplex (homologyZeroComplex C) (homologyZeroComplex D)).homology i ≅
      ∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2 :=
  let K := HomologicalComplex.tensorObj (homologyZeroComplex C) (homologyZeroComplex D)
  ((K.isoHomologyπ (i - 1) i (by simp) (tensorHomologyZero_d_eq_zero C D (i - 1) i)).symm ≪≫
    K.iCyclesIso i (i + 1) (by simp) (tensorHomologyZero_d_eq_zero C D i (i + 1))) ≪≫
    tensorObjXIsoCoproduct (homologyZeroComplex C) (homologyZeroComplex D) i

/-- Problem 7.8.7(iv), the **Künneth formula**, in its bare `Nonempty` form: `Hⁱ(C ⊗ D)` is
isomorphic to `⨁_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`. The isomorphism produced here is built from the
non-natural splitting of part (iii), so it carries no naturality data. The honest, natural
statement is `Etingof.Problem7_8_7_iv` in
`EtingofRepresentationTheory/Chapter7/KunnethIso.lean`, which exhibits the isomorphism as the
choice-free cross product `Etingof.kunnethMap`; this version is kept as a compatibility
corollary. -/
theorem Problem7_8_7_iv_nonempty (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    Nonempty ((tensorComplex C D).homology i ≅
      ∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2) := by
  -- Part (iii): decompose each factor into an acyclic complex plus its zero-differential
  -- homology complex.
  obtain ⟨E, hE, iC, -⟩ := Problem7_8_7_iii C
  obtain ⟨F, hF, iD, -⟩ := Problem7_8_7_iii D
  -- The homology functor `Hⁱ` at degree `i`; it is additive, so it preserves biproducts.
  let Hi := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) i
  haveI : Limits.PreservesBinaryBiproducts Hi :=
    Limits.preservesBinaryBiproducts_of_preservesBiproducts Hi
  -- Functoriality of `⊗` plus binary distributivity split `C ⊗ D` into the four Künneth
  -- summands `E⊗F ⊞ H_C⊗F ⊞ E⊗H_D ⊞ H_C⊗H_D`.
  let Θ : tensorComplex C D ≅
      (tensorComplex E F ⊞ tensorComplex (homologyZeroComplex C) F)
        ⊞ (tensorComplex E (homologyZeroComplex D)
            ⊞ tensorComplex (homologyZeroComplex C) (homologyZeroComplex D)) :=
    tensorIso iC iD ≪≫
      tensorComplex_biprodRightIso (E ⊞ homologyZeroComplex C) F (homologyZeroComplex D) ≪≫
      biprod.mapIso
        (tensorComplex_biprodLeftIso E (homologyZeroComplex C) F)
        (tensorComplex_biprodLeftIso E (homologyZeroComplex C) (homologyZeroComplex D))
  -- Three of the four summands are acyclic (part (ii)), so their `Hⁱ` is a zero object.
  have hzEF : IsZero (Hi.obj (tensorComplex E F)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (Problem7_8_7_ii E F (Or.inl hE) i)
  have hzHCF : IsZero (Hi.obj (tensorComplex (homologyZeroComplex C) F)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (Problem7_8_7_ii (homologyZeroComplex C) F (Or.inr hF) i)
  have hzEHD : IsZero (Hi.obj (tensorComplex E (homologyZeroComplex D))) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (Problem7_8_7_ii E (homologyZeroComplex D) (Or.inl hE) i)
  -- Collapse `Hⁱ(four-way biprod)` down to `Hⁱ(H_C ⊗ H_D)` by killing the three zero summands.
  let collapse : Hi.obj ((tensorComplex E F ⊞ tensorComplex (homologyZeroComplex C) F)
        ⊞ (tensorComplex E (homologyZeroComplex D)
            ⊞ tensorComplex (homologyZeroComplex C) (homologyZeroComplex D))) ≅
      Hi.obj (tensorComplex (homologyZeroComplex C) (homologyZeroComplex D)) :=
    Hi.mapBiprod _ _ ≪≫
      biprod.mapIso (Hi.mapBiprod _ _) (Hi.mapBiprod _ _) ≪≫
      (Limits.isoZeroBiprod ((Limits.biprod_isZero_iff _ _).mpr ⟨hzEF, hzHCF⟩)).symm ≪≫
      (Limits.isoZeroBiprod hzEHD).symm
  -- Assemble: `Hⁱ(C⊗D) ≅ Hⁱ(four-way) ≅ Hⁱ(H_C⊗H_D) ≅ ∐ Hʲ(C) ⊗ Hᵐ(D)`.
  exact ⟨Hi.mapIso Θ ≪≫ collapse ≪≫ homologyTensorHomologyZeroIso C D i⟩

end Etingof
