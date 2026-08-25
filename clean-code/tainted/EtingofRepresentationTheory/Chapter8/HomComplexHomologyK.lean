import EtingofRepresentationTheory.Chapter8.ExtCohomologyHomK
import EtingofRepresentationTheory.Chapter8.IsoPrecompHomEquiv
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.Grp.Zero

set_option backward.isDefEq.respectTransparency false

/-!
# Identifying the two `Hⁿ Hom(P•, N)` presentations

Both `Ext` notions used in Problem 8.2.8 (`Ext` half) compute `Extⁿ_A(M, N)` as the cohomology of
`Hom_A(P•, N)` for a projective resolution `P` of `M`, but through two different Mathlib
presentations of that cohomology that Mathlib does not identify:

* **Derived-category side** (used by `CategoryTheory.Abelian.Ext`): the `AddCommGrp`-valued cochain
  complex `HomComplex P.cochainComplex ((singleFunctor (ModuleCat A) 0).obj N)`, an `ℤ`-indexed
  `CochainComplex AddCommGrp ℤ` whose degree-`i` term is `Cochain P.cochainComplex (single 0 N) i`.
* **Left-derived-functor side** (used by `Etingof.Extₖ`): the `ModuleCat k`-valued cochain complex
  `P.complex.linearYonedaObj k N` (`ChainComplex.linearYonedaObj`), an `ℕ`-indexed
  `CochainComplex (ModuleCat k) ℕ` whose degree-`i` term is `Hom_A(P.complex.X i, N)`.

This file provides `Etingof.homComplexHomologyAddEquivₖ`, the additive isomorphism of the degree-`n`
homologies of these two complexes.

## Construction

The two complexes are degreewise "the same" `Hom(P•, N)`:

* `homDegEquiv i : Cochain P.cochainComplex (single 0 N) i ≃+ (P.complex.X i ⟶ N)` identifies the
  degree-`i` term of the `HomComplex` with the categorical hom `P.complex.X i ⟶ N` (which underlies
  the degree-`i` term `ModuleCat.of k (P.complex.X i ⟶ N)` of `linearYonedaObj`), via
  `Cochain.toSingleEquiv` and `ProjectiveResolution.cochainComplexXIso`.
* `homDegEquiv_δ` records the degreewise **sign twist**: the `HomComplex` differential `δ` becomes
  `(i+1).negOnePow •` precomposition with `P.complex.d (i+1) i`, whereas the `linearYonedaObj`
  differential is precomposition with no sign (`ChainComplex.linearYonedaObj_d`).

The category change `ModuleCat k → AddCommGrp` is handled by
`(forget₂ (ModuleCat k) Ab).PreservesHomology`.
-/

universe u

open CategoryTheory Limits CochainComplex.HomComplex

namespace Etingof

variable (k : Type u) [Field k]
variable {A : Type u} [Ring A] [Algebra k A]
variable {M : ModuleCat.{u} A} (N : ModuleCat.{u} A) (P : ProjectiveResolution M)

/-- The `AddCommGrp`-valued `HomComplex` of the projective resolution into `N[0]`, whose degree-`n`
homology underlies the derived-category `Ext`. -/
noncomputable abbrev homCochainComplex : CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.HomComplex P.cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)

/-- The degree-`i` term of the `HomComplex` is the categorical hom `P.complex.X i ⟶ N`, via the
`toSingle` identification and the reindexing `P.cochainComplex.X (-i) ≅ P.complex.X i`. -/
noncomputable def homDegEquiv (i : ℕ) :
    Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (i : ℤ)
      ≃+ (P.complex.X i ⟶ N) :=
  (Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
      (p := -(i : ℤ)) (q := 0) (n := (i : ℤ)) (by ring)).trans
    (isoPrecompHomEquiv (P.cochainComplexXIso (-(i : ℤ)) i (by ring)))

lemma homDegEquiv_apply (i : ℕ)
    (z : Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
      (i : ℤ)) :
    homDegEquiv N P i z =
      (P.cochainComplexXIso (-(i : ℤ)) i (by ring)).inv ≫
        Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
          (p := -(i : ℤ)) (q := 0) (n := (i : ℤ)) (by ring) z := rfl

/-- The main content: under `homDegEquiv`, the `HomComplex` differential `δ i (i+1)`
becomes `(i+1).negOnePow •` precomposition with the resolution differential `P.complex.d (i+1) i`.
The `linearYonedaObj` differential is the same precomposition with no sign, so the two complexes
differ by a degreewise sign twist. -/
lemma homDegEquiv_δ (i : ℕ)
    (z : Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
      (i : ℤ)) :
    homDegEquiv N P (i + 1) (δ (i : ℤ) (↑(i + 1)) z) =
      ((↑(i + 1) : ℤ)).negOnePow • (P.complex.d (i + 1) i ≫ homDegEquiv N P i z) := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (-(i : ℤ)) (by ring)
  rw [homDegEquiv_apply, homDegEquiv_apply,
    Cochain.δ_toSingleMk g (by ring) (↑(i + 1)) (-(↑(i + 1) : ℤ)) (by ring),
    Units.smul_def, map_zsmul, Cochain.toSingleEquiv_toSingleMk, Cochain.toSingleEquiv_toSingleMk,
    ProjectiveResolution.cochainComplex_d P (-(↑(i + 1) : ℤ)) (-(i : ℤ)) (i + 1) i
      (by ring) (by ring)]
  -- LHS: `xiso'.inv ≫ (negOnePow • (xiso'.hom ≫ d ≫ xiso.inv ≫ g))`;
  -- RHS: `negOnePow • (d ≫ xiso.inv ≫ g)`. Move the sign out and cancel `xiso'.inv ≫ xiso'.hom`.
  simp only [Units.smul_def, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]

/-!
## The homology comparison

We construct the additive isomorphism `homComplexHomologyAddEquivₖ`. Throughout, write
`L := homCochainComplex N P` (an `AddCommGrpCat`-valued cochain complex over `ℤ`),
`R := P.complex.linearYonedaObj k N` (a `ModuleCat k`-valued cochain complex over `ℕ`), and
`Ff := forget₂ (ModuleCat k) AddCommGrpCat` (which has `PreservesHomology`).

The degreewise `homDegEquiv` identifies `L.X ↑i` with `Ff.obj (R.X i)`, and `homDegEquiv_δ` records
the degreewise sign twist. Folding a unit sign into each degreewise identification (`sIso`) turns
the sign twist into a strictly commuting square (`sqGen`); combining three of these into a
`ShortComplex.isoMk` and transporting through `ShortComplex.homologyMapIso`,
`ShortComplex.mapHomologyIso`, and the reindexing `isoSc'` gives
`L.homology ↑(m+1) ≅ Ff.obj (R.homology (m+1))` (`homologyIsoSucc`).

For `n = 0` the incoming differentials both vanish (`L.X (-1)` is a zero object,
`isZeroLXneg1`, and `R.d 0 0 = 0`), so the epi/iso/mono criterion
`isIso_homologyMap_of_epi_of_isIso_of_mono` applied to the short-complex morphism `scHom0` yields
the homology isomorphism `homologyIsoZero`.
-/

/-- The forgetful functor `ModuleCat k ⥤ AddCommGrpCat`, which preserves homology; used to compare
the `AddCommGrpCat`-valued `HomComplex` with the `ModuleCat k`-valued `linearYonedaObj`. -/
noncomputable abbrev Ff : ModuleCat.{u} k ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} k) AddCommGrpCat

/-- The identification `homDegEquiv` twisted by a unit sign `u : ℤˣ`, as an `AddEquiv`. -/
noncomputable def sDegEquiv (i : ℕ) (u : ℤˣ) :
    Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (i : ℤ)
      ≃+ (P.complex.X i ⟶ N) := (homDegEquiv N P i).trans (DistribMulAction.toAddEquiv _ u)

/-- The sign-twisted degreewise isomorphism `L.X ↑i ≅ Ff.obj (R.X i)`. The unit sign `u` is chosen,
per short complex, to absorb the sign twist of `homDegEquiv_δ` into a strictly commuting square. -/
noncomputable def sIso (i : ℕ) (u : ℤˣ) :
    (homCochainComplex N P).X (i : ℤ) ≅ (Ff k).obj ((P.complex.linearYonedaObj k N).X i) :=
  (sDegEquiv N P i u).toAddCommGrpIso

@[simp] lemma sIso_hom_apply (i : ℕ) (u : ℤˣ) (z : (homCochainComplex N P).X (i : ℤ)) :
    (sIso k N P i u).hom z = (u : ℤ) • (homDegEquiv N P i z) := by
  simp only [sIso, AddEquiv.toAddCommGrpIso_hom]; rfl

/-- The degreewise commuting square: `sIso` at degree `i` with left sign `u`, and at degree `i+1`
with right sign `u * (i+1).negOnePow`, intertwines the `HomComplex` differential with the (unsigned)
`linearYonedaObj` differential. This is the sign-twist `homDegEquiv_δ` rewritten as a strict square,
the unit sign in `homDegEquiv_δ` being absorbed by the choice of right sign. -/
lemma sqGen (m : ℕ) (u : ℤˣ) :
    (sIso k N P m u).hom ≫ (Ff k).map ((P.complex.linearYonedaObj k N).d m (m+1))
      = (homCochainComplex N P).d ↑m ↑(m+1)
        ≫ (sIso k N P (m+1) (u * (↑(m+1):ℤ).negOnePow)).hom := by
  ext z
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, sIso_hom_apply, sIso_hom_apply]
  rw [show (ConcreteCategory.hom ((homCochainComplex N P).d (↑m) (↑(m+1)))) z
        = δ (↑m : ℤ) (↑(m+1)) z from rfl, homDegEquiv_δ N P m z]
  rw [← Units.smul_def, ← Units.smul_def, smul_smul, mul_assoc, Int.units_mul_self, mul_one]
  simp only [ChainComplex.linearYonedaObj_d, ModuleCat.forget₂_map, ConcreteCategory.hom_ofHom]
  rfl

/-- The degree-`(m+1)` homology short complexes of `L` and `Ff.obj R` are isomorphic, via the three
sign-twisted degreewise identifications and the two commuting squares `sqGen`. -/
noncomputable def scIso (m : ℕ) :
    (homCochainComplex N P).sc' (↑m) (↑(m+1)) (↑(m+2))
      ≅ ((P.complex.linearYonedaObj k N).sc' m (m+1) (m+2)).map (Ff k) :=
  ShortComplex.isoMk (sIso k N P m 1) (sIso k N P (m+1) (1 * (↑(m+1):ℤ).negOnePow))
    (sIso k N P (m+2) (1 * (↑(m+1):ℤ).negOnePow * (↑(m+2):ℤ).negOnePow))
    (sqGen k N P m 1) (sqGen k N P (m+1) (1 * (↑(m+1):ℤ).negOnePow))

/-- The degree-`(m+1)` homology isomorphism `L.homology ↑(m+1) ≅ Ff.obj (R.homology (m+1))`,
obtained from `scIso` by transporting through `homologyMapIso`, `mapHomologyIso`, and the reindexing
`isoSc'` on both sides. -/
noncomputable def homologyIsoSucc (m : ℕ) :
    (homCochainComplex N P).homology (↑(m+1))
      ≅ (Ff k).obj ((P.complex.linearYonedaObj k N).homology (m+1)) := by
  have hprevL : (ComplexShape.up ℤ).prev (↑(m+1)) = ↑m := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(m+1)) = ↑(m+2) := by
    have h : (ComplexShape.up ℤ).Rel (↑(m+1)) (↑(m+2)) := by
      simp only [ComplexShape.up_Rel]; omega
    rw [ComplexShape.next_eq' _ h]
  have hprevR : (ComplexShape.up ℕ).prev (m+1) = m := by simp
  have hnextR : (ComplexShape.up ℕ).next (m+1) = m+2 := by simp
  exact ShortComplex.homologyMapIso
      ((homCochainComplex N P).isoSc' (↑m) (↑(m+1)) (↑(m+2)) hprevL hnextL) ≪≫
    ShortComplex.homologyMapIso (scIso k N P m) ≪≫
    ((P.complex.linearYonedaObj k N).sc' m (m+1) (m+2)).mapHomologyIso (Ff k) ≪≫
    (Ff k).mapIso (ShortComplex.homologyMapIso
      ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).symm

/-- The degree-`(-1)` term of `L` is a zero object: a `(-1)`-cochain into `N[0]` is a map out of
`P.cochainComplex.X 1`, which vanishes since `P.cochainComplex` is supported in degrees `≤ 0`. -/
lemma isZeroLXneg1 : IsZero ((homCochainComplex N P).X (-1)) := by
  have hz1 : IsZero (P.cochainComplex.X 1) :=
    P.cochainComplex.isZero_of_isStrictlyLE 0 1 (by norm_num)
  have e := (Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
    (p := (1:ℤ)) (q := 0) (n := -1) (by ring))
  haveI : Subsingleton (P.cochainComplex.X 1 ⟶ N) := ⟨fun f g => (hz1.eq_of_src f g)⟩
  haveI : Subsingleton ↑((homCochainComplex N P).X (-1)) := e.toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The short-complex morphism at degree `0`, from `Ff.obj (R.sc' 0 0 1)` to `L.sc' (-1) 0 1`. The
degree-`(-1)` component is the (necessarily epimorphic) zero map into the zero object `L.X (-1)`;
the middle and top components are the sign-twisted degreewise isomorphisms. The lower square
commutes as both differentials into `X₂` vanish; the upper square is `sqGen` at `m = 0`. -/
noncomputable def scHom0 :
    ((P.complex.linearYonedaObj k N).sc' 0 0 (0+1)).map (Ff k)
      ⟶ (homCochainComplex N P).sc' (-1) (↑(0:ℕ)) (↑(0+1:ℕ)) where
  τ₁ := 0
  τ₂ := (sIso k N P 0 1).inv
  τ₃ := (sIso k N P (0+1) (1 * (↑(0+1):ℤ).negOnePow)).inv
  comm₁₂ := by
    have hf : (((P.complex.linearYonedaObj k N).sc' 0 0 (0+1)).map (Ff k)).f = 0 := by
      change (Ff k).map ((P.complex.linearYonedaObj k N).d 0 0) = 0
      rw [(P.complex.linearYonedaObj k N).shape 0 0 (by simp), Functor.map_zero]
    rw [hf, zero_comp, zero_comp]
  comm₂₃ := by
    simp only [ShortComplex.map_g, HomologicalComplex.shortComplexFunctor'_obj_g]
    refine (Iso.inv_comp_eq _).mpr ?_
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).mpr (sqGen k N P 0 1).symm

/-- The degree-`0` homology isomorphism `L.homology 0 ≅ Ff.obj (R.homology 0)`, obtained from
`scHom0` by the epi/iso/mono criterion for `homologyMap` and the reindexing `isoSc'`. -/
noncomputable def homologyIsoZero :
    (homCochainComplex N P).homology (↑(0:ℕ))
      ≅ (Ff k).obj ((P.complex.linearYonedaObj k N).homology 0) := by
  have hprevL : (ComplexShape.up ℤ).prev (↑(0:ℕ)) = -1 := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(0:ℕ)) = ↑(0+1:ℕ) := by
    have h : (ComplexShape.up ℤ).Rel (↑(0:ℕ)) (↑(0+1:ℕ)) := by
      simp only [ComplexShape.up_Rel]; omega
    rw [ComplexShape.next_eq' _ h]
  have hprevR : (ComplexShape.up ℕ).prev 0 = 0 := by simp
  have hnextR : (ComplexShape.up ℕ).next 0 = 0+1 := by simp
  haveI : Epi (scHom0 k N P).τ₁ := (isZeroLXneg1 N P).epi _
  haveI : IsIso (scHom0 k N P).τ₂ := inferInstanceAs (IsIso (sIso k N P 0 1).inv)
  haveI : Mono (scHom0 k N P).τ₃ :=
    inferInstanceAs (Mono (sIso k N P (0+1) (1 * (↑(0+1):ℤ).negOnePow)).inv)
  exact ShortComplex.homologyMapIso
      ((homCochainComplex N P).isoSc' (-1) (↑(0:ℕ)) (↑(0+1:ℕ)) hprevL hnextL) ≪≫
    (asIso (ShortComplex.homologyMap (scHom0 k N P))).symm ≪≫
    ((P.complex.linearYonedaObj k N).sc' 0 0 (0+1)).mapHomologyIso (Ff k) ≪≫
    (Ff k).mapIso (ShortComplex.homologyMapIso
      ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).symm

/-- The degree-`n` homology isomorphism `L.homology ↑n ≅ Ff.obj (R.homology n)`, cased on `n`. -/
noncomputable def homIso (n : ℕ) :
    (homCochainComplex N P).homology (↑n)
      ≅ (Ff k).obj ((P.complex.linearYonedaObj k N).homology n) := by
  cases n with
  | zero => exact homologyIsoZero k N P
  | succ m => exact homologyIsoSucc k N P m

/-- The additive isomorphism of the degree-`n` homologies of the two `Hom(P•, N)` presentations:
the `AddCommGrpCat`-valued `HomComplex` (underlying the derived-category `Ext`) and the `ModuleCat k`-
valued `linearYonedaObj` (underlying `Etingof.Extₖ`). This is the main step of the `Ext ≃ₗ[k] Extₖ`
comparison. -/
noncomputable def homComplexHomologyAddEquivₖ (n : ℕ) :
    (homCochainComplex N P).homology (↑n)
      ≃+ (P.complex.linearYonedaObj k N).homology n :=
  (homIso k N P n).addCommGroupIsoToAddEquiv

/-!
## Postcomposition functoriality of `homCochainComplex` in `N`

Mathlib does not package the whole-complex map `HomComplex K L ⟶ HomComplex K L'` induced by a
morphism `L ⟶ L'`. We build the special case we need: a morphism `g : N ⟶ N'` induces a chain map
`homCochainComplex N P ⟶ homCochainComplex N' P` by degreewise postcomposition of cochains with
`(singleFunctor _ 0).map g`. The chain-map condition is `δ_comp_ofHom` (postcomposition by an
honest morphism commutes with the `HomComplex` differential `δ`). This is used in the
scalar-endomorphism naturality that upgrades `homComplexHomologyAddEquivₖ` to `k`-linear.
-/

variable {N' : ModuleCat.{u} A}

/-- Degreewise postcomposition of `i`-cochains into `N[0]` with `(singleFunctor _ 0).map g`, as an
additive homomorphism `Cochain P.cochainComplex N[0] i →+ Cochain P.cochainComplex N'[0] i`. -/
noncomputable def cochainPostcompHom (g : N ⟶ N') (i : ℤ) :
    Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) i →+
      Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') i where
  toFun z := z.comp (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g))
    (add_zero i)
  map_zero' := Cochain.zero_comp _ _
  map_add' z z' := Cochain.add_comp z z' _ _

/-- The chain map `homCochainComplex N P ⟶ homCochainComplex N' P` induced by `g : N ⟶ N'`, given
degreewise by `cochainPostcompHom`. The chain-map square is `δ_comp_ofHom`. -/
noncomputable def homCochainComplexPostcomp (g : N ⟶ N') :
    homCochainComplex N P ⟶ homCochainComplex N' P where
  f i := AddCommGrpCat.ofHom (cochainPostcompHom N P g i)
  comm' i j _ := by
    ext z
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
    exact CochainComplex.HomComplex.δ_comp_ofHom z _ j

@[simp] lemma homCochainComplexPostcomp_f_apply (g : N ⟶ N') (i : ℤ)
    (z : (homCochainComplex N P).X i) :
    (homCochainComplexPostcomp N P g).f i z =
      z.comp (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g))
        (add_zero i) := rfl

/-!
## `homologyAddEquiv` naturality under postcomposition

The middle step of the additive tower `e123` is
`(homologyAddEquiv P.cochainComplex N[0] n).symm ∘ CohomologyClass.mk`. We record its naturality
under the postcomposition chain map `homCochainComplexPostcomp N P g`: on a cocycle representative
`c` it intertwines `Cocycle.postcomp` (on the class) with `HomologicalComplex.homologyMap` of the
chain map. The proof builds the `ShortComplex.LeftHomologyMapData` for `homCochainComplexPostcomp`
between the two `leftHomologyData` presentations of the cohomology (whose `π` is
`CohomologyClass.mkAddMonoidHom`), with `φK = Cocycle.postcomp` and `φH = ` the descended
postcomposition on cohomology classes, and applies `LeftHomologyMapData.homologyMap_eq`.
-/

variable (g : N ⟶ N')

/-- Postcomposition of `n`-cocycles into `N[0]` with `(singleFunctor _ 0).map g`, as an additive
hom; the cocycle-level restriction of `homCochainComplexPostcomp N P g` (its `φK`). -/
noncomputable def cocyclePostcompHom (n : ℤ) :
    Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n →+
      Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n where
  toFun z := z.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g)
  map_zero' := by
    apply Cocycle.ext
    simp only [Cocycle.postcomp, Cocycle.mk_coe, Cocycle.coe_zero, Cochain.zero_comp]
  map_add' z z' := by
    apply Cocycle.ext
    simp only [Cocycle.postcomp, Cocycle.mk_coe, Cocycle.coe_add, Cochain.add_comp]

@[simp] lemma cocyclePostcompHom_apply (n : ℤ)
    (z : Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n) :
    cocyclePostcompHom N P g n z =
      z.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g) := rfl

/-- Coboundaries land in coboundaries under postcomposition: this is the kernel condition that
descends `mk ∘ cocyclePostcompHom` to cohomology classes. Postcomposition commutes with `δ`
(`δ_comp_ofHom`), so the image of a coboundary `δ β` is the coboundary `δ (β.postcomp)`. -/
lemma coboundaries_le_ker_mk_cocyclePostcomp (n : ℤ) :
    coboundaries P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n ≤
      ((CohomologyClass.mkAddMonoidHom P.cochainComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n).comp
        (cocyclePostcompHom N P g n)).ker := by
  rintro α ⟨m, hm, β, hβ⟩
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
    cocyclePostcompHom_apply, CohomologyClass.mkAddMonoidHom_apply, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  refine ⟨β.comp (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g))
    (add_zero m), ?_⟩
  rw [δ_comp_ofHom, hβ]
  rfl

/-- Postcomposition on cohomology classes with `(singleFunctor _ 0).map g`, the descent of
`mk ∘ cocyclePostcompHom` (its `φH`). -/
noncomputable def cohomologyClassPostcompHom (n : ℤ) :
    CohomologyClass P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n →+
      CohomologyClass P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n).comp
      (cocyclePostcompHom N P g n))
    (coboundaries_le_ker_mk_cocyclePostcomp N P g n)

@[simp] lemma cohomologyClassPostcompHom_mk (n : ℤ)
    (c : Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n) :
    cohomologyClassPostcompHom N P g n (CohomologyClass.mk c) =
      CohomologyClass.mk
        (c.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g)) := rfl

/-- The `ShortComplex.LeftHomologyMapData` for the postcomposition chain map
`homCochainComplexPostcomp N P g`, between the two `leftHomologyData` presentations of the
degree-`n` cohomology. Its `φK` is `Cocycle.postcomp`; its `φH` is `cohomologyClassPostcompHom`. -/
noncomputable def leftHomologyMapDataPostcomp (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
        (homCochainComplexPostcomp N P g))
      (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n)
      (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n) := by
  set h₂ := CochainComplex.HomComplex.leftHomologyData P.cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n with hh₂
  have hcommi :
      AddCommGrpCat.ofHom (cocyclePostcompHom N P g n) ≫ h₂.i
        = (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n).i
          ≫ ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
              (homCochainComplexPostcomp N P g)).τ₂ := by
    ext c
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
    rfl
  haveI : Mono h₂.i := by
    rw [AddCommGrpCat.mono_iff_injective]
    exact fun a b hab => Subtype.ext hab
  exact
  { φK := AddCommGrpCat.ofHom (cocyclePostcompHom N P g n)
    φH := AddCommGrpCat.ofHom (cohomologyClassPostcompHom N P g n)
    commi := hcommi
    commπ := by
      ext c
      rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
      rfl
    commf' := by
      rw [← cancel_mono h₂.i]
      simp only [Category.assoc, hcommi]
      rw [h₂.f'_i, ← Category.assoc,
        (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n).f'_i]
      exact (((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
        (homCochainComplexPostcomp N P g)).comm₁₂).symm }

@[simp] lemma leftHomologyMapDataPostcomp_φH (n : ℤ) :
    (leftHomologyMapDataPostcomp N P g n).φH
      = AddCommGrpCat.ofHom (cohomologyClassPostcompHom N P g n) := rfl

/-- `homologyAddEquiv` is `homologyIso.hom`, with types stated so downstream rewrites keep the
`HomologicalComplex.homology` presentation (avoids unfolding the `def` into `(sc n).homology`). -/
lemma homologyAddEquiv_apply_hom (L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (y : (P.cochainComplex.HomComplex L).homology n) :
    CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex L n y
      = (CochainComplex.HomComplex.leftHomologyData P.cochainComplex L n).homologyIso.hom y := rfl

/-- **Forward naturality square of `homologyAddEquiv` under postcomposition.** `homologyAddEquiv`
intertwines `HomologicalComplex.homologyMap (homCochainComplexPostcomp N P g)` with
`cohomologyClassPostcompHom` (postcomposition on cohomology classes). Proved from
`LeftHomologyMapData.homologyMap_comm` transported through `homologyIso`. -/
lemma homologyAddEquiv_homologyMap (n : ℤ)
    (y : (homCochainComplex N P).homology n) :
    CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n
        ((HomologicalComplex.homologyMap (homCochainComplexPostcomp N P g) n) y)
      = cohomologyClassPostcompHom N P g n
          (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n y) := by
  have h := ConcreteCategory.congr_hom
    (leftHomologyMapDataPostcomp N P g n).homologyMap_comm y
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

/-- **Naturality of the middle step `homologyAddEquiv.symm ∘ mk` under postcomposition.** For a
cocycle `c` and `g : N ⟶ N'`, applying `homCochainComplexPostcomp N P g` on homology after
`homologyAddEquiv.symm (mk c)` equals `homologyAddEquiv.symm (mk (c.postcomp g))`. This is the
`N`-side naturality used in the `k`-homogeneity step. -/
lemma homologyAddEquiv_symm_mk_postcomp (n : ℤ)
    (c : Cocycle P.cochainComplex
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n) :
    (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n).symm
        (CohomologyClass.mk
          (c.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g)))
      = (HomologicalComplex.homologyMap (homCochainComplexPostcomp N P g) n)
          ((CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n).symm
            (CohomologyClass.mk c)) := by
  rw [AddEquiv.symm_apply_eq, homologyAddEquiv_homologyMap, AddEquiv.apply_symm_apply,
    cohomologyClassPostcompHom_mk]

/-!
## Tower naturality of `homComplexHomologyAddEquivₖ` under the scalar endomorphism

For the scalar endomorphism `g = r • 𝟙 N`, the postcomposition chain map
`homCochainComplexPostcomp N P g` corresponds, degreewise under `homDegEquiv` (hence `sIso`), to the
`linearYonedaObj`-side scalar `r • 𝟙` (`homDegEquiv_homCochainComplexPostcomp`,
`sIso_hom_homCochainComplexPostcomp_smul`). Combining the degreewise squares into `ShortComplex`
morphisms (`scIso`/`scHom0` naturality) and transporting through `homIso` upgrades
`homComplexHomologyAddEquivₖ` to intertwine the `HomComplex`-side postcomposition `homologyMap` with
the `linearYonedaObj`-side scalar `homologyMap (r • 𝟙)`. This tower naturality
(`homComplexHomologyAddEquivₖ_homologyMap_postcomp`) is the last ingredient of the `k`-homogeneity
step.
-/

/-- **Degreewise postcomposition compatibility of `homDegEquiv`.** Under the degreewise
identification `homDegEquiv`, the degree-`i` component of the postcomposition chain map
`homCochainComplexPostcomp N P g` is postcomposition `- ≫ g` on the categorical hom
`P.complex.X i ⟶ N`. -/
lemma homDegEquiv_homCochainComplexPostcomp (g : N ⟶ N') (i : ℕ)
    (z : (homCochainComplex N P).X (i : ℤ)) :
    homDegEquiv N' P i ((homCochainComplexPostcomp N P g).f (i : ℤ) z)
      = homDegEquiv N P i z ≫ g := by
  rw [homCochainComplexPostcomp_f_apply, homDegEquiv_apply, homDegEquiv_apply, Category.assoc]
  congr 1
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-(i : ℤ)) (by ring)
  rw [← Cochain.toSingleMk_postcomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]

/-- Underlying-map computation: `Ff.map (r • 𝟙 X)` acts as the scalar `r` on elements. -/
lemma Ff_map_smul_id (r : k) (X : ModuleCat.{u} k) (w : X) :
    (Ff k).map (r • 𝟙 X) w = r • w := by
  rw [ModuleCat.forget₂_map]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_id]
  rfl

/-- **Specialized degreewise square.** For the scalar endomorphism
`g = r • 𝟙 N`, the sign-twisted degreewise iso `sIso` intertwines the postcomposition chain map
`homCochainComplexPostcomp N P (r • 𝟙 N)` with the `linearYonedaObj`-side scalar `r • 𝟙`. -/
lemma sIso_hom_homCochainComplexPostcomp_smul (r : k) (i : ℕ) (u : ℤˣ)
    (z : (homCochainComplex N P).X (i : ℤ)) :
    (sIso k N P i u).hom ((homCochainComplexPostcomp N P (r • 𝟙 N)).f (i : ℤ) z)
      = (Ff k).map (r • 𝟙 ((P.complex.linearYonedaObj k N).X i)) ((sIso k N P i u).hom z) := by
  rw [sIso_hom_apply, sIso_hom_apply, Ff_map_smul_id,
    homDegEquiv_homCochainComplexPostcomp, Linear.comp_smul, Category.comp_id, smul_comm]

/-- **Reindexing naturality square.** For an endomorphism `α : K ⟶ K` of a homological complex,
`HomologicalComplex.homologyMap α j` conjugates, via `ShortComplex.homologyMapIso (K.isoSc' i j l)`,
to the `ShortComplex.homologyMap` of the reindexed short-complex morphism. This is the naturality of
`natIsoSc'`. Reused for both the `L`-side (before the crossing) and the `R`-side (after). -/
lemma homologyMap_homologyMapIso_isoSc'
    {C : Type*} [Category C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
    [CategoryWithHomology C] {K : HomologicalComplex C c} (α : K ⟶ K) (i j l : ι)
    (hi : c.prev j = i) (hl : c.next j = l) :
    HomologicalComplex.homologyMap α j
        ≫ (ShortComplex.homologyMapIso (K.isoSc' i j l hi hl)).hom
      = (ShortComplex.homologyMapIso (K.isoSc' i j l hi hl)).hom
          ≫ ShortComplex.homologyMap
              ((HomologicalComplex.shortComplexFunctor' C c i j l).map α) := by
  simp only [ShortComplex.homologyMapIso_hom]
  rw [show HomologicalComplex.homologyMap α j
        = ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor C c j).map α) from rfl,
    ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (HomologicalComplex.natIsoSc' C c i j l hi hl).hom.naturality α

/-- Morphism-level degreewise square: `sIso` intertwines the postcomposition endomorphism
`homCochainComplexPostcomp N P (r • 𝟙 N)` with the `linearYonedaObj` scalar `r • 𝟙`. -/
lemma sIso_hom_naturality_component (r : k) (i : ℕ) (u : ℤˣ) :
    (homCochainComplexPostcomp N P (r • 𝟙 N)).f (i : ℤ) ≫ (sIso k N P i u).hom
      = (sIso k N P i u).hom ≫ (Ff k).map (r • 𝟙 ((P.complex.linearYonedaObj k N).X i)) := by
  ext z
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
  exact sIso_hom_homCochainComplexPostcomp_smul k N P r i u z

/-- **`scIso` naturality square (succ case).** The reindexed short-complex morphism of the
postcomposition chain map corresponds, under `scIso`, to `Ff` of the reindexed scalar
`r • 𝟙`-morphism. Componentwise this is `sIso_hom_naturality_component`. -/
lemma scIso_hom_naturality_succ (r : k) (m : ℕ) :
    (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
        ↑m ↑(m+1) ↑(m+2)).map (homCochainComplexPostcomp N P (r • 𝟙 N))
        ≫ (scIso k N P m).hom
      = (scIso k N P m).hom
          ≫ (Ff k).mapShortComplex.map
              ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
                  m (m+1) (m+2)).map (r • 𝟙 (P.complex.linearYonedaObj k N))) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact sIso_hom_naturality_component k N P r m 1
  · exact sIso_hom_naturality_component k N P r (m+1) (1 * (↑(m+1):ℤ).negOnePow)
  · exact sIso_hom_naturality_component k N P r (m+2)
      (1 * (↑(m+1):ℤ).negOnePow * (↑(m+2):ℤ).negOnePow)

/-- **Tower naturality (succ case).** `homologyIsoSucc` intertwines the postcomposition
`homologyMap` with `Ff` of the `linearYonedaObj`-side scalar `homologyMap`. The four naturality
squares: `L`-reindex (`homologyMap_homologyMapIso_isoSc'`), the crossing (`scIso` square),
`mapHomologyIso` (`ShortComplex.mapHomologyIso_hom_naturality`), and `Ff` of the `R`-reindex. -/
lemma homologyIsoSucc_hom_naturality (r : k) (m : ℕ) :
    HomologicalComplex.homologyMap (homCochainComplexPostcomp N P (r • 𝟙 N)) (↑(m+1))
        ≫ (homologyIsoSucc k N P m).hom
      = (homologyIsoSucc k N P m).hom
          ≫ (Ff k).map (HomologicalComplex.homologyMap
              (r • 𝟙 (P.complex.linearYonedaObj k N)) (m+1)) := by
  set φ := homCochainComplexPostcomp N P (r • 𝟙 N) with hφ
  set ψ := r • 𝟙 (P.complex.linearYonedaObj k N) with hψ
  have hprevL : (ComplexShape.up ℤ).prev (↑(m+1)) = ↑m := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(m+1)) = ↑(m+2) := by
    rw [ComplexShape.next_eq' _ (by simp only [ComplexShape.up_Rel]; omega :
      (ComplexShape.up ℤ).Rel (↑(m+1)) (↑(m+2)))]
  have hprevR : (ComplexShape.up ℕ).prev (m+1) = m := by simp
  have hnextR : (ComplexShape.up ℕ).next (m+1) = m+2 := by simp
  have hA := homologyMap_homologyMapIso_isoSc' φ (↑m) (↑(m+1)) (↑(m+2)) hprevL hnextL
  have hB : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
          ↑m ↑(m+1) ↑(m+2)).map φ)
        ≫ (ShortComplex.homologyMapIso (scIso k N P m)).hom
      = (ShortComplex.homologyMapIso (scIso k N P m)).hom
          ≫ ShortComplex.homologyMap ((Ff k).mapShortComplex.map
              ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
                  m (m+1) (m+2)).map ψ)) := by
    rw [ShortComplex.homologyMapIso_hom,
      ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
      scIso_hom_naturality_succ]
  have hC := ShortComplex.mapHomologyIso_hom_naturality (F := Ff k)
    (φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
      m (m+1) (m+2)).map ψ)
  have hR := homologyMap_homologyMapIso_isoSc' ψ m (m+1) (m+2) hprevR hnextR
  have hDinner : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          m (m+1) (m+2)).map ψ)
        ≫ (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
      = (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
          ≫ HomologicalComplex.homologyMap ψ (m+1) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hR.symm
  have hD : (Ff k).map (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          m (m+1) (m+2)).map ψ))
        ≫ (Ff k).map (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
      = (Ff k).map (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
          ≫ (Ff k).map (HomologicalComplex.homologyMap ψ (m+1)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hDinner]
  simp only [homologyIsoSucc, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [reassoc_of% hA, reassoc_of% hB, reassoc_of% hC, hD]
  simp only [Category.assoc]

/-- Inverse form of the degreewise square, for the `n = 0` crossing built from `sIso.inv`. -/
lemma sIso_inv_naturality_component (r : k) (i : ℕ) (u : ℤˣ) :
    (Ff k).map (r • 𝟙 ((P.complex.linearYonedaObj k N).X i)) ≫ (sIso k N P i u).inv
      = (sIso k N P i u).inv ≫ (homCochainComplexPostcomp N P (r • 𝟙 N)).f (i : ℤ) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, sIso_hom_naturality_component]

/-- **`scHom0` naturality square (zero case).** The degree-`0` short-complex morphism `scHom0`
intertwines `Ff` of the `linearYonedaObj`-side scalar `r • 𝟙`-morphism with the postcomposition
chain map. The `τ₁` component is `0 = 0` (into the zero object `L.X (-1)`), the `τ₂`/`τ₃` components
are the inverse degreewise squares. -/
lemma scHom0_naturality (r : k) :
    (Ff k).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map (r • 𝟙 (P.complex.linearYonedaObj k N)))
        ≫ scHom0 k N P
      = scHom0 k N P
          ≫ (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
              (-1) (↑(0:ℕ)) (↑(0+1:ℕ))).map (homCochainComplexPostcomp N P (r • 𝟙 N)) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · simp only [scHom0, ShortComplex.comp_τ₁, comp_zero, zero_comp]
  · exact sIso_inv_naturality_component k N P r 0 1
  · exact sIso_inv_naturality_component k N P r (0+1) (1 * (↑(0+1):ℤ).negOnePow)

/-- **Tower naturality (zero case).** `homologyIsoZero` intertwines the postcomposition
`homologyMap` with `Ff` of the `linearYonedaObj`-side scalar `homologyMap`. Same four squares as the
succ case, with the crossing built from `inv (homologyMap scHom0)` (via `scHom0_naturality`). -/
lemma homologyIsoZero_hom_naturality (r : k) :
    HomologicalComplex.homologyMap (homCochainComplexPostcomp N P (r • 𝟙 N)) (↑(0:ℕ))
        ≫ (homologyIsoZero k N P).hom
      = (homologyIsoZero k N P).hom
          ≫ (Ff k).map (HomologicalComplex.homologyMap
              (r • 𝟙 (P.complex.linearYonedaObj k N)) 0) := by
  set φ := homCochainComplexPostcomp N P (r • 𝟙 N) with hφ
  set ψ := r • 𝟙 (P.complex.linearYonedaObj k N) with hψ
  have hprevL : (ComplexShape.up ℤ).prev (↑(0:ℕ)) = -1 := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(0:ℕ)) = ↑(0+1:ℕ) := by
    rw [ComplexShape.next_eq' _ (by simp only [ComplexShape.up_Rel]; omega :
      (ComplexShape.up ℤ).Rel (↑(0:ℕ)) (↑(0+1:ℕ)))]
  have hprevR : (ComplexShape.up ℕ).prev 0 = 0 := by simp
  have hnextR : (ComplexShape.up ℕ).next 0 = 0+1 := by simp
  haveI : Epi (scHom0 k N P).τ₁ := (isZeroLXneg1 N P).epi _
  haveI : IsIso (scHom0 k N P).τ₂ := inferInstanceAs (IsIso (sIso k N P 0 1).inv)
  haveI : Mono (scHom0 k N P).τ₃ :=
    inferInstanceAs (Mono (sIso k N P (0+1) (1 * (↑(0+1):ℤ).negOnePow)).inv)
  have hA := homologyMap_homologyMapIso_isoSc' φ (-1) (↑(0:ℕ)) (↑(0+1:ℕ)) hprevL hnextL
  have hSmap : ShortComplex.homologyMap ((Ff k).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map ψ)) ≫ ShortComplex.homologyMap (scHom0 k N P)
      = ShortComplex.homologyMap (scHom0 k N P) ≫ ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
            (-1) (↑(0:ℕ)) (↑(0+1:ℕ))).map φ) := by
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp, scHom0_naturality]
  have hB : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
          (-1) (↑(0:ℕ)) (↑(0+1:ℕ))).map φ) ≫ inv (ShortComplex.homologyMap (scHom0 k N P))
      = inv (ShortComplex.homologyMap (scHom0 k N P))
          ≫ ShortComplex.homologyMap ((Ff k).mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
            0 0 (0+1)).map ψ)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hSmap.symm
  have hC := ShortComplex.mapHomologyIso_hom_naturality (F := Ff k)
    (φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
      0 0 (0+1)).map ψ)
  have hR := homologyMap_homologyMapIso_isoSc' ψ 0 0 (0+1) hprevR hnextR
  have hDinner : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map ψ)
        ≫ (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
      = (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
          ≫ HomologicalComplex.homologyMap ψ 0 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hR.symm
  have hD : (Ff k).map (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map ψ))
        ≫ (Ff k).map (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
      = (Ff k).map (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
          ≫ (Ff k).map (HomologicalComplex.homologyMap ψ 0) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hDinner]
  simp only [homologyIsoZero, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv]
  rw [reassoc_of% hA, reassoc_of% hB, reassoc_of% hC, hD]
  simp only [Category.assoc]

/-- **Tower naturality of `homComplexHomologyAddEquivₖ`.** For the scalar
endomorphism `r • 𝟙 N`, the additive comparison `homComplexHomologyAddEquivₖ` intertwines the
`HomComplex`-side postcomposition `homologyMap (homCochainComplexPostcomp N P (r • 𝟙 N))` with the
`linearYonedaObj`-side scalar `homologyMap (r • 𝟙)`. Cased on `n` via `homologyIsoZero`/
`homologyIsoSucc` naturality. -/
lemma homComplexHomologyAddEquivₖ_homologyMap_postcomp (r : k) (n : ℕ)
    (z : (homCochainComplex N P).homology (↑n)) :
    homComplexHomologyAddEquivₖ k N P n
        (HomologicalComplex.homologyMap (homCochainComplexPostcomp N P (r • 𝟙 N)) (↑n) z)
      = (HomologicalComplex.homologyMap
            (r • 𝟙 (P.complex.linearYonedaObj k N)) n).hom
          (homComplexHomologyAddEquivₖ k N P n z) := by
  have hmor : HomologicalComplex.homologyMap (homCochainComplexPostcomp N P (r • 𝟙 N)) (↑n)
        ≫ (homIso k N P n).hom
      = (homIso k N P n).hom ≫ (Ff k).map (HomologicalComplex.homologyMap
          (r • 𝟙 (P.complex.linearYonedaObj k N)) n) := by
    cases n with
    | zero => exact homologyIsoZero_hom_naturality k N P r
    | succ m => exact homologyIsoSucc_hom_naturality k N P r m
  have key := ConcreteCategory.congr_hom hmor z
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at key
  exact key

end Etingof
