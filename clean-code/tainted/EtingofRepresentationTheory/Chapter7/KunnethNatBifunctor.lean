import EtingofRepresentationTheory.Chapter7.KunnethChainComplexNat
import EtingofRepresentationTheory.Chapter7.KunnethCochainComplexNat

/-!
# Natural Künneth isomorphisms for `ℕ`-indexed complexes

This file packages the reindexed chain and cochain Künneth isomorphisms as natural
isomorphisms of bifunctors. The four comparison steps are natural: homology across `extend`,
tensor compatibility of `extend`, the `ℤ`-indexed Künneth isomorphism, and removal of the
vanishing summands outside the image of `ℕ → ℤ`.

The components are definitionally the existing `kunnethChainComplexNatIso` and
`kunnethCochainComplexNatIso`, so existing objectwise clients continue to use the same maps.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex

-- The composite naturality proofs elaborate four large categorical isomorphisms at once.
set_option linter.style.setOption false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Etingof

universe u

variable {k : Type u} [Field k]

/-- Pairs of natural-number degrees whose sum is `i`. -/
abbrev KunnethNatIndex (i : ℕ) := {p : ℕ × ℕ // p.1 + p.2 = i}

private noncomputable abbrev chainKunnethSourceObj
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :=
  ∐ fun p : KunnethNatIndex i => C.homology p.1.1 ⊗ D.homology p.1.2

private noncomputable abbrev chainExtendedKunnethSourceObj
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :=
  ∐ fun p : KunnethIndex (-(i : ℤ)) =>
    (C.extend ComplexShape.embeddingDownNat).homology p.1.1 ⊗
      (D.extend ComplexShape.embeddingDownNat).homology p.1.2

private noncomputable def chainKunnethSourceMap
    {C C' D D' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    chainKunnethSourceObj C D i ⟶ chainKunnethSourceObj C' D' i :=
  Sigma.desc fun p => (homologyMap f p.1.1 ⊗ₘ homologyMap g p.1.2) ≫
    Sigma.ι (fun p : KunnethNatIndex i => C'.homology p.1.1 ⊗ D'.homology p.1.2) p

private noncomputable def chainExtendedKunnethSourceMap
    {C C' D D' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    chainExtendedKunnethSourceObj C D i ⟶ chainExtendedKunnethSourceObj C' D' i :=
  Sigma.desc fun p =>
    (homologyMap (extendMap f ComplexShape.embeddingDownNat) p.1.1 ⊗ₘ
      homologyMap (extendMap g ComplexShape.embeddingDownNat) p.1.2) ≫
    Sigma.ι (fun p : KunnethIndex (-(i : ℤ)) =>
      (C'.extend ComplexShape.embeddingDownNat).homology p.1.1 ⊗
        (D'.extend ComplexShape.embeddingDownNat).homology p.1.2) p

/-- The chain Künneth direct-sum bifunctor
`(C, D) ↦ ⨁_{p+q=i} H_p(C) ⊗ H_q(D)`. -/
noncomputable def kunnethChainComplexSource (i : ℕ) :
    (ChainComplex (ModuleCat.{u} k) ℕ) × (ChainComplex (ModuleCat.{u} k) ℕ) ⥤
      ModuleCat.{u} k where
  obj X := chainKunnethSourceObj X.1 X.2 i
  map {X Y} φ := chainKunnethSourceMap φ.1 φ.2 i
  map_id X := by
    refine Sigma.hom_ext _ _ fun p => ?_
    rw [chainKunnethSourceMap, Sigma.ι_desc]
    simp
  map_comp {X Y Z} φ ψ := by
    refine Sigma.hom_ext _ _ fun p => ?_
    simp only [chainKunnethSourceMap]
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc,
      ← Category.assoc]
    congr 1
    rw [show (φ ≫ ψ).1 = φ.1 ≫ ψ.1 from rfl, show (φ ≫ ψ).2 = φ.2 ≫ ψ.2 from rfl,
      homologyMap_comp, homologyMap_comp, MonoidalCategory.tensorHom_comp_tensorHom]

/-- The chain Künneth tensor-homology bifunctor `(C, D) ↦ H_i(C ⊗ D)`. -/
noncomputable def kunnethChainComplexTarget (i : ℕ) :
    (ChainComplex (ModuleCat.{u} k) ℕ) × (ChainComplex (ModuleCat.{u} k) ℕ) ⥤
      ModuleCat.{u} k :=
  MonoidalCategory.tensor (ChainComplex (ModuleCat.{u} k) ℕ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i

@[reassoc (attr := simp)]
private lemma ι_kunnethChainComplexSource_map (i : ℕ)
    {X Y : (ChainComplex (ModuleCat.{u} k) ℕ) × (ChainComplex (ModuleCat.{u} k) ℕ)}
    (φ : X ⟶ Y) (p : KunnethNatIndex i) :
    Sigma.ι (fun p : KunnethNatIndex i => X.1.homology p.1.1 ⊗ X.2.homology p.1.2) p ≫
        (kunnethChainComplexSource i).map φ =
      (homologyMap φ.1 p.1.1 ⊗ₘ homologyMap φ.2 p.1.2) ≫
        Sigma.ι (fun p : KunnethNatIndex i => Y.1.homology p.1.1 ⊗ Y.2.homology p.1.2) p :=
  Sigma.ι_desc _ _

private abbrev chainKunnethIndexEmbedding (i : ℕ) :
    KunnethNatIndex i → KunnethIndex (-(i : ℤ)) :=
  fun p => ⟨(-(p.1.1 : ℤ), -(p.1.2 : ℤ)), by
    have h2 : (p.1.1 : ℤ) + (p.1.2 : ℤ) = (i : ℤ) := by exact_mod_cast p.2
    omega⟩

private theorem chainKunnethIndexEmbedding_injective (i : ℕ) :
    Function.Injective (chainKunnethIndexEmbedding i) := by
    intro p p' hpp
    apply Subtype.ext
    have hv := congrArg Subtype.val hpp
    have h1 : (p.1.1 : ℤ) = (p'.1.1 : ℤ) := neg_injective (congrArg Prod.fst hv)
    have h2 : (p.1.2 : ℤ) = (p'.1.2 : ℤ) := neg_injective (congrArg Prod.snd hv)
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

private noncomputable def chainKunnethReindexIso
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    chainExtendedKunnethSourceObj C D i ≅ chainKunnethSourceObj C D i :=
  sigmaIsoOfInjOfIsZeroCompl (chainKunnethIndexEmbedding i)
    (chainKunnethIndexEmbedding_injective i)
    (fun a => tensorIso (homology_extend_iso C a.1.1) (homology_extend_iso D a.1.2))
    (by
      rintro ⟨⟨a, b⟩, hab⟩ hj
      by_cases ha : 0 < a
      · exact TensorExtend.isZero_tensorObj_left (homology_extend_isZero C a ha)
      by_cases hb : 0 < b
      · exact TensorExtend.isZero_tensorObj_right (homology_extend_isZero D b hb)
      rw [not_lt] at ha hb
      exfalso
      have hp : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
      have hq : ((-b).toNat : ℤ) = -b := Int.toNat_of_nonneg (by omega)
      have hpq : (-a).toNat + (-b).toNat = i := by
        have : ((-a).toNat : ℤ) + ((-b).toNat : ℤ) = (i : ℤ) := by rw [hp, hq]; omega
        exact_mod_cast this
      refine hj ⟨((-a).toNat, (-b).toNat), hpq⟩ (Subtype.ext ?_)
      change (-(((-a).toNat : ℕ) : ℤ), -(((-b).toNat : ℕ) : ℤ)) = (a, b)
      rw [Prod.mk.injEq]
      exact ⟨by rw [hp]; ring, by rw [hq]; ring⟩)

@[reassoc]
private lemma ι_chainKunnethReindexIso_hom
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) (p : KunnethNatIndex i) :
    Sigma.ι (fun q : KunnethIndex (-(i : ℤ)) =>
        (C.extend ComplexShape.embeddingDownNat).homology q.1.1 ⊗
          (D.extend ComplexShape.embeddingDownNat).homology q.1.2)
        (chainKunnethIndexEmbedding i p) ≫ (chainKunnethReindexIso C D i).hom =
      (tensorIso (homology_extend_iso C p.1.1) (homology_extend_iso D p.1.2)).hom ≫
        Sigma.ι (fun q : KunnethNatIndex i => C.homology q.1.1 ⊗ D.homology q.1.2) p := by
  simpa only [chainKunnethReindexIso, sigmaIsoOfInjOfIsZeroCompl] using
    (ι_sigmaSupportHom (F := fun q : KunnethIndex (-(i : ℤ)) =>
        (C.extend ComplexShape.embeddingDownNat).homology q.1.1 ⊗
          (D.extend ComplexShape.embeddingDownNat).homology q.1.2)
      (G := fun q : KunnethNatIndex i => C.homology q.1.1 ⊗ D.homology q.1.2)
      (chainKunnethIndexEmbedding i)
      (chainKunnethIndexEmbedding_injective i)
      (fun a => tensorIso (homology_extend_iso C a.1.1) (homology_extend_iso D a.1.2)) p)

@[reassoc]
private lemma chainKunnethReindexIso_hom_naturality
    {C C' D D' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    chainExtendedKunnethSourceMap f g i ≫
        (chainKunnethReindexIso (k := k) C' D' i).hom =
      (chainKunnethReindexIso (k := k) C D i).hom ≫
        chainKunnethSourceMap f g i := by
  refine Sigma.hom_ext _ _ fun j => ?_
  by_cases hj : ∃ p, chainKunnethIndexEmbedding i p = j
  · obtain ⟨p, rfl⟩ := hj
    rw [chainExtendedKunnethSourceMap, ← Category.assoc, Sigma.ι_desc]
    rw [Category.assoc, ι_chainKunnethReindexIso_hom]
    rw [ι_chainKunnethReindexIso_hom_assoc]
    rw [chainKunnethSourceMap, Sigma.ι_desc]
    simp only [tensorIso_hom, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    rw [homology_extend_iso_hom_naturality, homology_extend_iso_hom_naturality]
  · by_cases ha : 0 < j.1.1
    · exact (TensorExtend.isZero_tensorObj_left
        (homology_extend_isZero C j.1.1 ha)).eq_of_src _ _
    by_cases hb : 0 < j.1.2
    · exact (TensorExtend.isZero_tensorObj_right
        (homology_extend_isZero D j.1.2 hb)).eq_of_src _ _
    · rw [not_lt] at ha hb
      have hp : ((-j.1.1).toNat : ℤ) = -j.1.1 := Int.toNat_of_nonneg (by omega)
      have hq : ((-j.1.2).toNat : ℤ) = -j.1.2 := Int.toNat_of_nonneg (by omega)
      have hpq : (-j.1.1).toNat + (-j.1.2).toNat = i := by
        have hzsum : ((-j.1.1).toNat : ℤ) + ((-j.1.2).toNat : ℤ) = (i : ℤ) := by
          rw [hp, hq]
          have := j.2
          omega
        exact_mod_cast hzsum
      exfalso
      apply hj
      refine ⟨⟨((-j.1.1).toNat, (-j.1.2).toNat), hpq⟩, Subtype.ext ?_⟩
      change (-(((-j.1.1).toNat : ℕ) : ℤ), -(((-j.1.2).toNat : ℕ) : ℤ)) = j.1
      simp [hp, hq]

private noncomputable def chainKunnethAlphaOne
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅
      ((HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingDownNat).homology
        (-(i : ℤ)) :=
  (homology_extend_iso (HomologicalComplex.tensorObj C D) i).symm

private noncomputable def chainKunnethAlphaTwo
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    ((HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingDownNat).homology
        (-(i : ℤ)) ≅
      (HomologicalComplex.tensorObj
        (C.extend ComplexShape.embeddingDownNat)
        (D.extend ComplexShape.embeddingDownNat)).homology (-(i : ℤ)) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (-(i : ℤ))).mapIso (TensorExtend.tensorObjExtendIso C D).symm

private noncomputable def chainKunnethAlphaThree
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj
        (C.extend ComplexShape.embeddingDownNat)
        (D.extend ComplexShape.embeddingDownNat)).homology (-(i : ℤ)) ≅
      chainExtendedKunnethSourceObj C D i :=
  Problem7_8_7_iv (C.extend ComplexShape.embeddingDownNat)
    (D.extend ComplexShape.embeddingDownNat) (-(i : ℤ))

@[reassoc]
private lemma chainKunnethAlphaOne_naturality
    {C C' D D' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (HomologicalComplex.tensorHom f g) i ≫ (chainKunnethAlphaOne C' D' i).hom =
      (chainKunnethAlphaOne C D i).hom ≫
        homologyMap (extendMap (HomologicalComplex.tensorHom f g)
          ComplexShape.embeddingDownNat) (-(i : ℤ)) := by
  rw [← cancel_mono (homology_extend_iso (HomologicalComplex.tensorObj C' D') i).hom]
  simp only [chainKunnethAlphaOne, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [homology_extend_iso_hom_naturality (HomologicalComplex.tensorHom f g),
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc]
private lemma chainKunnethAlphaTwo_naturality
    {C C' D D' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (extendMap (HomologicalComplex.tensorHom f g)
          ComplexShape.embeddingDownNat) (-(i : ℤ)) ≫
        (chainKunnethAlphaTwo C' D' i).hom =
      (chainKunnethAlphaTwo C D i).hom ≫
        homologyMap (HomologicalComplex.tensorHom
          (extendMap f ComplexShape.embeddingDownNat)
          (extendMap g ComplexShape.embeddingDownNat)) (-(i : ℤ)) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (-(i : ℤ))
  have h := TensorExtend.tensorObjExtendIso_hom_naturality f g
  have hinv :
      extendMap (HomologicalComplex.tensorHom f g) ComplexShape.embeddingDownNat ≫
          (TensorExtend.tensorObjExtendIso C' D').inv =
        (TensorExtend.tensorObjExtendIso C D).inv ≫
          HomologicalComplex.tensorHom
            (extendMap f ComplexShape.embeddingDownNat)
            (extendMap g ComplexShape.embeddingDownNat) := by
    rw [← cancel_mono (TensorExtend.tensorObjExtendIso C' D').hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp]
  simpa only [Iso.symm_hom] using congrArg H.map hinv

@[reassoc]
private lemma chainKunnethAlphaThree_naturality
    {C C' D D' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (HomologicalComplex.tensorHom
          (extendMap f ComplexShape.embeddingDownNat)
          (extendMap g ComplexShape.embeddingDownNat)) (-(i : ℤ)) ≫
        (chainKunnethAlphaThree C' D' i).hom =
      (chainKunnethAlphaThree C D i).hom ≫ chainExtendedKunnethSourceMap f g i := by
  rw [← cancel_mono (kunnethIso
    (C'.extend ComplexShape.embeddingDownNat)
    (D'.extend ComplexShape.embeddingDownNat) (-(i : ℤ))).hom]
  simp only [chainKunnethAlphaThree, Problem7_8_7_iv, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hnat : chainExtendedKunnethSourceMap f g i ≫
        kunnethMap (C'.extend ComplexShape.embeddingDownNat)
          (D'.extend ComplexShape.embeddingDownNat) (-(i : ℤ)) =
      kunnethMap (C.extend ComplexShape.embeddingDownNat)
          (D.extend ComplexShape.embeddingDownNat) (-(i : ℤ)) ≫
        homologyMap (HomologicalComplex.tensorHom
          (extendMap f ComplexShape.embeddingDownNat)
          (extendMap g ComplexShape.embeddingDownNat)) (-(i : ℤ)) := by
    simpa only [chainExtendedKunnethSourceMap, kunnethSource] using
      kunnethMap_naturality (extendMap f ComplexShape.embeddingDownNat)
        (extendMap g ComplexShape.embeddingDownNat) (-(i : ℤ))
  rw [kunnethIso_hom (C'.extend ComplexShape.embeddingDownNat)
      (D'.extend ComplexShape.embeddingDownNat), hnat,
    ← kunnethIso_hom (C.extend ComplexShape.embeddingDownNat)
      (D.extend ComplexShape.embeddingDownNat),
    ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

private noncomputable def kunnethChainComplexNatIsoNatural
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅ chainKunnethSourceObj C D i :=
  chainKunnethAlphaOne C D i ≪≫ chainKunnethAlphaTwo C D i ≪≫
    chainKunnethAlphaThree C D i ≪≫ chainKunnethReindexIso C D i

@[reassoc]
private lemma kunnethChainComplexNatIsoNatural_hom_naturality
    {C C' D D' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (HomologicalComplex.tensorHom f g) i ≫
        (kunnethChainComplexNatIsoNatural C' D' i).hom =
      (kunnethChainComplexNatIsoNatural C D i).hom ≫ chainKunnethSourceMap f g i := by
  simp only [kunnethChainComplexNatIsoNatural, Iso.trans_hom]
  rw [chainKunnethAlphaOne_naturality_assoc, chainKunnethAlphaTwo_naturality_assoc,
    chainKunnethAlphaThree_naturality_assoc,
    chainKunnethReindexIso_hom_naturality]
  simp only [Category.assoc]

/-- The natural Künneth isomorphism
`H_i(C ⊗ D) ≅ ⨁_{p+q=i} H_p(C) ⊗ H_q(D)` for `ℕ`-indexed chain complexes. -/
noncomputable def kunnethChainComplexNatNatIso (i : ℕ) :
    kunnethChainComplexTarget (k := k) i ≅ kunnethChainComplexSource (k := k) i :=
  NatIso.ofComponents
    (fun X => kunnethChainComplexNatIso X.1 X.2 i)
    (fun {_ _} φ => kunnethChainComplexNatIsoNatural_hom_naturality φ.1 φ.2 i)

/-- The components of `kunnethChainComplexNatNatIso` are the existing objectwise isomorphisms. -/
@[simp]
lemma kunnethChainComplexNatNatIso_app
    (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (kunnethChainComplexNatNatIso (k := k) i).app (C, D) =
      kunnethChainComplexNatIso C D i := rfl

private noncomputable abbrev cochainKunnethSourceObj
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :=
  ∐ fun p : KunnethNatIndex i => C.homology p.1.1 ⊗ D.homology p.1.2

private noncomputable abbrev cochainExtendedKunnethSourceObj
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :=
  ∐ fun p : KunnethIndex (i : ℤ) =>
    (C.extend ComplexShape.embeddingUpNat).homology p.1.1 ⊗
      (D.extend ComplexShape.embeddingUpNat).homology p.1.2

private noncomputable def cochainKunnethSourceMap
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    cochainKunnethSourceObj C D i ⟶ cochainKunnethSourceObj C' D' i :=
  Sigma.desc fun p => (homologyMap f p.1.1 ⊗ₘ homologyMap g p.1.2) ≫
    Sigma.ι (fun p : KunnethNatIndex i => C'.homology p.1.1 ⊗ D'.homology p.1.2) p

private noncomputable def cochainExtendedKunnethSourceMap
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    cochainExtendedKunnethSourceObj C D i ⟶ cochainExtendedKunnethSourceObj C' D' i :=
  Sigma.desc fun p =>
    (homologyMap (extendMap f ComplexShape.embeddingUpNat) p.1.1 ⊗ₘ
      homologyMap (extendMap g ComplexShape.embeddingUpNat) p.1.2) ≫
    Sigma.ι (fun p : KunnethIndex (i : ℤ) =>
      (C'.extend ComplexShape.embeddingUpNat).homology p.1.1 ⊗
        (D'.extend ComplexShape.embeddingUpNat).homology p.1.2) p

/-- The cochain Künneth direct-sum bifunctor
`(C, D) ↦ ⨁_{p+q=i} H^p(C) ⊗ H^q(D)`. -/
noncomputable def kunnethCochainComplexSource (i : ℕ) :
    (CochainComplex (ModuleCat.{u} k) ℕ) × (CochainComplex (ModuleCat.{u} k) ℕ) ⥤
      ModuleCat.{u} k where
  obj X := cochainKunnethSourceObj X.1 X.2 i
  map {X Y} φ := cochainKunnethSourceMap φ.1 φ.2 i
  map_id X := by
    refine Sigma.hom_ext _ _ fun p => ?_
    rw [cochainKunnethSourceMap, Sigma.ι_desc]
    simp
  map_comp {X Y Z} φ ψ := by
    refine Sigma.hom_ext _ _ fun p => ?_
    simp only [cochainKunnethSourceMap]
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc,
      ← Category.assoc]
    congr 1
    rw [show (φ ≫ ψ).1 = φ.1 ≫ ψ.1 from rfl, show (φ ≫ ψ).2 = φ.2 ≫ ψ.2 from rfl,
      homologyMap_comp, homologyMap_comp, MonoidalCategory.tensorHom_comp_tensorHom]

/-- The cochain Künneth tensor-cohomology bifunctor `(C, D) ↦ H^i(C ⊗ D)`. -/
noncomputable def kunnethCochainComplexTarget (i : ℕ) :
    (CochainComplex (ModuleCat.{u} k) ℕ) × (CochainComplex (ModuleCat.{u} k) ℕ) ⥤
      ModuleCat.{u} k :=
  MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} k) ℕ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i

private abbrev cochainKunnethIndexEmbedding (i : ℕ) :
    KunnethNatIndex i → KunnethIndex (i : ℤ) :=
  fun p => ⟨((p.1.1 : ℤ), (p.1.2 : ℤ)), by
    have h2 : (p.1.1 : ℤ) + (p.1.2 : ℤ) = (i : ℤ) := by exact_mod_cast p.2
    exact h2⟩

private theorem cochainKunnethIndexEmbedding_injective (i : ℕ) :
    Function.Injective (cochainKunnethIndexEmbedding i) := by
  intro p p' hpp
  apply Subtype.ext
  have hv := congrArg Subtype.val hpp
  have h1 : (p.1.1 : ℤ) = (p'.1.1 : ℤ) := congrArg Prod.fst hv
  have h2 : (p.1.2 : ℤ) = (p'.1.2 : ℤ) := congrArg Prod.snd hv
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

private noncomputable def cochainKunnethReindexIso
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    cochainExtendedKunnethSourceObj C D i ≅ cochainKunnethSourceObj C D i :=
  sigmaIsoOfInjOfIsZeroCompl (cochainKunnethIndexEmbedding i)
    (cochainKunnethIndexEmbedding_injective i)
    (fun a => tensorIso (homology_extend_iso_up C a.1.1) (homology_extend_iso_up D a.1.2))
    (by
      rintro ⟨⟨a, b⟩, hab⟩ hj
      by_cases ha : a < 0
      · exact TensorExtendUp.isZero_tensorObj_left (homology_extend_isZero_up C a ha)
      by_cases hb : b < 0
      · exact TensorExtendUp.isZero_tensorObj_right (homology_extend_isZero_up D b hb)
      rw [not_lt] at ha hb
      exfalso
      have hp : ((a.toNat) : ℤ) = a := Int.toNat_of_nonneg ha
      have hq : ((b.toNat) : ℤ) = b := Int.toNat_of_nonneg hb
      have hpq : a.toNat + b.toNat = i := by
        have : ((a.toNat) : ℤ) + ((b.toNat) : ℤ) = (i : ℤ) := by rw [hp, hq]; exact hab
        exact_mod_cast this
      refine hj ⟨(a.toNat, b.toNat), hpq⟩ (Subtype.ext ?_)
      change (((a.toNat : ℕ) : ℤ), ((b.toNat : ℕ) : ℤ)) = (a, b)
      rw [Prod.mk.injEq]
      exact ⟨hp, hq⟩)

@[reassoc]
private lemma ι_cochainKunnethReindexIso_hom
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) (p : KunnethNatIndex i) :
    Sigma.ι (fun q : KunnethIndex (i : ℤ) =>
        (C.extend ComplexShape.embeddingUpNat).homology q.1.1 ⊗
          (D.extend ComplexShape.embeddingUpNat).homology q.1.2)
        (cochainKunnethIndexEmbedding i p) ≫ (cochainKunnethReindexIso C D i).hom =
      (tensorIso (homology_extend_iso_up C p.1.1) (homology_extend_iso_up D p.1.2)).hom ≫
        Sigma.ι (fun q : KunnethNatIndex i => C.homology q.1.1 ⊗ D.homology q.1.2) p := by
  simpa only [cochainKunnethReindexIso, sigmaIsoOfInjOfIsZeroCompl] using
    (ι_sigmaSupportHom (F := fun q : KunnethIndex (i : ℤ) =>
        (C.extend ComplexShape.embeddingUpNat).homology q.1.1 ⊗
          (D.extend ComplexShape.embeddingUpNat).homology q.1.2)
      (G := fun q : KunnethNatIndex i => C.homology q.1.1 ⊗ D.homology q.1.2)
      (cochainKunnethIndexEmbedding i)
      (cochainKunnethIndexEmbedding_injective i)
      (fun a => tensorIso (homology_extend_iso_up C a.1.1)
        (homology_extend_iso_up D a.1.2)) p)

@[reassoc]
private lemma cochainKunnethReindexIso_hom_naturality
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    cochainExtendedKunnethSourceMap f g i ≫
        (cochainKunnethReindexIso C' D' i).hom =
      (cochainKunnethReindexIso C D i).hom ≫ cochainKunnethSourceMap f g i := by
  refine Sigma.hom_ext _ _ fun j => ?_
  by_cases hj : ∃ p, cochainKunnethIndexEmbedding i p = j
  · obtain ⟨p, rfl⟩ := hj
    rw [cochainExtendedKunnethSourceMap, ← Category.assoc, Sigma.ι_desc]
    rw [Category.assoc, ι_cochainKunnethReindexIso_hom]
    rw [ι_cochainKunnethReindexIso_hom_assoc]
    rw [cochainKunnethSourceMap, Sigma.ι_desc]
    simp only [tensorIso_hom, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    rw [homology_extend_iso_up_hom_naturality, homology_extend_iso_up_hom_naturality]
  · by_cases ha : j.1.1 < 0
    · exact (TensorExtendUp.isZero_tensorObj_left
        (homology_extend_isZero_up C j.1.1 ha)).eq_of_src _ _
    by_cases hb : j.1.2 < 0
    · exact (TensorExtendUp.isZero_tensorObj_right
        (homology_extend_isZero_up D j.1.2 hb)).eq_of_src _ _
    · rw [not_lt] at ha hb
      have hp : (j.1.1.toNat : ℤ) = j.1.1 := Int.toNat_of_nonneg ha
      have hq : (j.1.2.toNat : ℤ) = j.1.2 := Int.toNat_of_nonneg hb
      have hpq : j.1.1.toNat + j.1.2.toNat = i := by
        have hzsum : (j.1.1.toNat : ℤ) + (j.1.2.toNat : ℤ) = (i : ℤ) := by
          rw [hp, hq]
          exact j.2
        exact_mod_cast hzsum
      exfalso
      apply hj
      refine ⟨⟨(j.1.1.toNat, j.1.2.toNat), hpq⟩, Subtype.ext ?_⟩
      change (((j.1.1.toNat : ℕ) : ℤ), ((j.1.2.toNat : ℕ) : ℤ)) = j.1
      simp [hp, hq]

private noncomputable def cochainKunnethAlphaOne
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅
      ((HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingUpNat).homology
        (i : ℤ) :=
  (homology_extend_iso_up (HomologicalComplex.tensorObj C D) i).symm

private noncomputable def cochainKunnethAlphaTwo
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    ((HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingUpNat).homology (i : ℤ) ≅
      (HomologicalComplex.tensorObj
        (C.extend ComplexShape.embeddingUpNat)
        (D.extend ComplexShape.embeddingUpNat)).homology (i : ℤ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (i : ℤ)).mapIso (TensorExtendUp.tensorObjExtendIso C D).symm

private noncomputable def cochainKunnethAlphaThree
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj
        (C.extend ComplexShape.embeddingUpNat)
        (D.extend ComplexShape.embeddingUpNat)).homology (i : ℤ) ≅
      cochainExtendedKunnethSourceObj C D i :=
  Problem7_8_7_iv (C.extend ComplexShape.embeddingUpNat)
    (D.extend ComplexShape.embeddingUpNat) (i : ℤ)

@[reassoc]
private lemma cochainKunnethAlphaOne_naturality
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (HomologicalComplex.tensorHom f g) i ≫ (cochainKunnethAlphaOne C' D' i).hom =
      (cochainKunnethAlphaOne C D i).hom ≫
        homologyMap (extendMap (HomologicalComplex.tensorHom f g)
          ComplexShape.embeddingUpNat) (i : ℤ) := by
  rw [← cancel_mono (homology_extend_iso_up (HomologicalComplex.tensorObj C' D') i).hom]
  simp only [cochainKunnethAlphaOne, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [homology_extend_iso_up_hom_naturality (HomologicalComplex.tensorHom f g),
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc]
private lemma cochainKunnethAlphaTwo_naturality
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (extendMap (HomologicalComplex.tensorHom f g)
          ComplexShape.embeddingUpNat) (i : ℤ) ≫
        (cochainKunnethAlphaTwo C' D' i).hom =
      (cochainKunnethAlphaTwo C D i).hom ≫
        homologyMap (HomologicalComplex.tensorHom
          (extendMap f ComplexShape.embeddingUpNat)
          (extendMap g ComplexShape.embeddingUpNat)) (i : ℤ) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) (i : ℤ)
  have h := TensorExtendUp.tensorObjExtendIso_hom_naturality f g
  have hinv :
      extendMap (HomologicalComplex.tensorHom f g) ComplexShape.embeddingUpNat ≫
          (TensorExtendUp.tensorObjExtendIso C' D').inv =
        (TensorExtendUp.tensorObjExtendIso C D).inv ≫
          HomologicalComplex.tensorHom
            (extendMap f ComplexShape.embeddingUpNat)
            (extendMap g ComplexShape.embeddingUpNat) := by
    rw [← cancel_mono (TensorExtendUp.tensorObjExtendIso C' D').hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp]
  simpa only [Iso.symm_hom] using congrArg H.map hinv

@[reassoc]
private lemma cochainKunnethAlphaThree_naturality
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (HomologicalComplex.tensorHom
          (extendMap f ComplexShape.embeddingUpNat)
          (extendMap g ComplexShape.embeddingUpNat)) (i : ℤ) ≫
        (cochainKunnethAlphaThree C' D' i).hom =
      (cochainKunnethAlphaThree C D i).hom ≫ cochainExtendedKunnethSourceMap f g i := by
  rw [← cancel_mono (kunnethIso
    (C'.extend ComplexShape.embeddingUpNat)
    (D'.extend ComplexShape.embeddingUpNat) (i : ℤ)).hom]
  simp only [cochainKunnethAlphaThree, Problem7_8_7_iv, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hnat : cochainExtendedKunnethSourceMap f g i ≫
        kunnethMap (C'.extend ComplexShape.embeddingUpNat)
          (D'.extend ComplexShape.embeddingUpNat) (i : ℤ) =
      kunnethMap (C.extend ComplexShape.embeddingUpNat)
          (D.extend ComplexShape.embeddingUpNat) (i : ℤ) ≫
        homologyMap (HomologicalComplex.tensorHom
          (extendMap f ComplexShape.embeddingUpNat)
          (extendMap g ComplexShape.embeddingUpNat)) (i : ℤ) := by
    simpa only [cochainExtendedKunnethSourceMap, kunnethSource] using
      kunnethMap_naturality (extendMap f ComplexShape.embeddingUpNat)
        (extendMap g ComplexShape.embeddingUpNat) (i : ℤ)
  rw [kunnethIso_hom (C'.extend ComplexShape.embeddingUpNat)
      (D'.extend ComplexShape.embeddingUpNat), hnat,
    ← kunnethIso_hom (C.extend ComplexShape.embeddingUpNat)
      (D.extend ComplexShape.embeddingUpNat),
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private noncomputable def kunnethCochainComplexNatIsoNatural
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅ cochainKunnethSourceObj C D i :=
  cochainKunnethAlphaOne C D i ≪≫ cochainKunnethAlphaTwo C D i ≪≫
    cochainKunnethAlphaThree C D i ≪≫ cochainKunnethReindexIso C D i

@[reassoc]
private lemma kunnethCochainComplexNatIsoNatural_hom_naturality
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℕ) :
    homologyMap (HomologicalComplex.tensorHom f g) i ≫
        (kunnethCochainComplexNatIsoNatural C' D' i).hom =
      (kunnethCochainComplexNatIsoNatural C D i).hom ≫ cochainKunnethSourceMap f g i := by
  simp only [kunnethCochainComplexNatIsoNatural, Iso.trans_hom]
  rw [cochainKunnethAlphaOne_naturality_assoc, cochainKunnethAlphaTwo_naturality_assoc,
    cochainKunnethAlphaThree_naturality_assoc,
    cochainKunnethReindexIso_hom_naturality]
  simp only [Category.assoc]

/-- The natural Künneth isomorphism
`H^i(C ⊗ D) ≅ ⨁_{p+q=i} H^p(C) ⊗ H^q(D)` for `ℕ`-indexed cochain complexes. -/
noncomputable def kunnethCochainComplexNatNatIso (i : ℕ) :
    kunnethCochainComplexTarget (k := k) i ≅ kunnethCochainComplexSource (k := k) i :=
  NatIso.ofComponents
    (fun X => kunnethCochainComplexNatIso X.1 X.2 i)
    (fun {_ _} φ => kunnethCochainComplexNatIsoNatural_hom_naturality φ.1 φ.2 i)

/-- The components of `kunnethCochainComplexNatNatIso` are the existing objectwise
isomorphisms. -/
@[simp]
lemma kunnethCochainComplexNatNatIso_app
    (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (kunnethCochainComplexNatNatIso (k := k) i).app (C, D) =
      kunnethCochainComplexNatIso C D i := rfl

end Etingof
