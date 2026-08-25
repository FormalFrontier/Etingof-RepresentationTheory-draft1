import EtingofRepresentationTheory.Chapter8.ExternalTensorComplex
import EtingofRepresentationTheory.Chapter8.ExternalTensorProjective
import EtingofRepresentationTheory.Chapter8.ExternalTensorRestriction
import EtingofRepresentationTheory.Chapter7.KunnethChainComplexNat
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

set_option backward.isDefEq.respectTransparency false

/-!
# The external tensor product of two projective resolutions is a projective resolution

Combining the pieces built in `ExternalTensorComplex.lean` (the total complex
`Etingof.extTensorComplex P₁ P₂` and its augmentation `Etingof.extTensorπ P₁ P₂`) and
`ExternalTensorProjective.lean` (degreewise projectivity `Etingof.extTensor_projective`), this
file constructs the `ProjectiveResolution` of `M₁ ⊗[k] M₂` over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`:

* `Etingof.extTensorComplex_projective`: each degree `(extTensorComplex P₁ P₂).X n` is projective
  over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. Degree `n` is the coproduct `⨁_{i₁+i₂=n} (P₁)_{i₁} ⊗[k] (P₂)_{i₂}` of the
  bidegree pieces (`GradedObject.mapObj` = `∐`), each projective by `extTensor_projective` since the
  factors `(P₁)_{i₁}`, `(P₂)_{i₂}` are projective; a coproduct of projectives is projective.
* `Etingof.extTensorProjectiveResolution`: the `ProjectiveResolution` itself, with
  `complex := extTensorComplex P₁ P₂`, `π := extTensorπ P₁ P₂`, degreewise projectivity from the
  lemma above, and the `quasiIso` obligation (exactness of the resolution).

## The base ring must be a field

This file works over a field `k`, not a general `CommRing`. The `quasiIso` field of
`extTensorProjectiveResolution` (exactness of `P•₁ ⊗_k P•₂` as a resolution of `M₁ ⊗_k M₂`) is
false over a general commutative ring: it is the vanishing of the higher `Tor`
`Tor_{>0}^k(M₁, M₂)`, which is nonzero already for `k = ℤ`, `M₁ = M₂ = ℤ/2` (there
`Tor_1^ℤ(ℤ/2, ℤ/2) = ℤ/2`, so `P•₁ ⊗_ℤ P•₂` has homology in degree 1 and is not a resolution).
Over a field every module is flat, so the obstruction vanishes. Accordingly the section variable is
`[Field k]`.

## The `quasiIso` obligation

Restriction of scalars to `k` reflects
`QuasiIso` (it preserves homology, `restrictScalars_preservesHomology`, and reflects isomorphisms),
so it suffices to check the restricted augmentation, which `extTensorComplex_restrictIso`
identifies with the augmentation `Φ` of the `k`-tensor total complex
`res₁Complex P₁ ⊗ res₂Complex P₂ → res₁ M₁ ⊗ res₂ M₂`. That map is a quasi-isomorphism degreewise:

* **positive degrees** by `homology_tensorObj_res_isZero_succ`: the `k`-tensor of the two restricted
  resolutions is exact in every degree `n + 1`, via the Chapter 7 Künneth formula
  `kunnethChainComplexNatIso` (`H_{n+1}(C₁ ⊗ C₂) ≅ ⨁_{p+q=n+1} H_p(C₁) ⊗ H_q(C₂)`, every summand
  zero since one index is positive and the restricted resolutions are acyclic in positive degrees);
* **degree `0`** by `quasiIsoAt_zero_of_isColimitCokernelCofork` together with
  `isColimitCokernelCofork_tensorObj_augmentation`: `Φ.f 0` is a cokernel of the total-complex
  differential `d 1 0`. Its degree-`0` component is `res₁ (P₁.π)₀ ⊗ res₂ (P₂.π)₀` (the map-level
  `i = 0` square `ι_extRestrictComplexXIso_aug₀`), and the tensor of two cokernels is a
  cokernel (right-exactness of `⊗`, `CokernelCofork.isColimitTensor`), so it induces an isomorphism
  on `H_0`.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace Etingof

universe u

variable {k : Type u} [Field k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}

-- The restriction-of-scalars `k`-module structures on `A₁ᵐᵒᵖ`- and `A₂ᵐᵒᵖ`-modules, needed to
-- form the `k`-tensor `M₁ ⊗[k] M₂` and its external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action.
attribute [local instance] restrictModule₁ restrictModule₂ tower₁ tower₂ extModule

/-- The degree `.X n` of the external tensor complex, unfolded to the coproduct `mapObj` of its
bidegree summands. Stated as a `rfl` at the `mapObj` level (a single `total` projection), which is
cheap; unfolding all the way to `∐` forces a costly normalization of the bifunctor terms. -/
private theorem extTensorComplex_X_eq (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) :
    (extTensorComplex (k := k) P₁ P₂).X n
      = (((((extTensorFunctor k A₁ A₂).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
          P₂.complex).toGradedObject.mapObj
          (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n :=
  rfl

/-- Each degree of the external tensor complex is projective over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. Degree `n` is
the coproduct of the bidegree pieces `(P₁)_{i₁} ⊗[k] (P₂)_{i₂}` over `i₁ + i₂ = n`; each is
projective by `extTensor_projective` (the factors are projective, being terms of projective
resolutions), and a coproduct of projectives is projective. The lifting property is built by
hand from `Sigma.desc`/`Sigma.ι` rather than via the coproduct-`Projective` instance, whose
full-transparency defeq check does not terminate on the heavy bifunctor summands. -/
theorem extTensorComplex_projective (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) : Projective ((extTensorComplex (k := k) P₁ P₂).X n) := by
  rw [extTensorComplex_X_eq]
  set g := ((((extTensorFunctor k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
    P₂.complex).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n with hg
  -- Each summand `(P₁)_{i₁} ⊗[k] (P₂)_{i₂}` is projective; the coproduct exists.
  haveI hsummand : ∀ i, Projective (g i) := by
    rw [hg]; rintro ⟨⟨i₁, i₂⟩, h⟩
    exact extTensor_projective k A₁ A₂ (P₁.complex.X i₁) (P₂.complex.X i₂)
  haveI hcop : HasCoproduct g := by rw [hg]; infer_instance
  change Projective (∐ g)
  refine ⟨fun {E X} f e he => ⟨Sigma.desc fun b => Projective.factorThru (Sigma.ι g b ≫ f) e, ?_⟩⟩
  apply Sigma.hom_ext
  intro b
  rw [Sigma.ι_desc_assoc]
  exact Projective.factorThru_comp _ e

/-- Restriction of scalars along any ring hom preserves homology. It is a left adjoint
(`restrictCoextendScalarsAdj`), hence preserves cokernels; it also preserves monomorphisms and zero
morphisms, so `preservesHomology_of_preservesMonos_and_cokernels` applies. (The
`ChangeOfRingsExact` instances give this only for *commutative* target rings, which fails here since
`A₁ᵐᵒᵖ`, `A₂ᵐᵒᵖ` are noncommutative.) -/
theorem restrictScalars_preservesHomology {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology := by
  haveI : Limits.PreservesColimits (ModuleCat.restrictScalars.{u} f) :=
    (ModuleCat.restrictCoextendScalarsAdj f).leftAdjoint_preservesColimits
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- A homology-preserving functor `F : ModuleCat R ⥤ ModuleCat k` carries a projective resolution to
a complex that is exact in every positive degree: `F` sends the quasi-isomorphism `Q.π` to a
quasi-isomorphism onto `F (single₀ N)`, whose homology vanishes above degree `0`. Applied below with
`F = res₁ k A₁` and `F = res₂ k A₂` to the two restricted resolutions. -/
theorem homology_mapHomologicalComplex_projective_isZero_succ
    {R : Type u} [Ring R] {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} k) [F.Additive] [F.PreservesHomology] (n : ℕ) :
    IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology (n + 1)) := by
  have hqi : QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) (n + 1) :=
    inferInstance
  rw [quasiIsoAt_iff_isIso_homologyMap] at hqi
  refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) (n + 1)))
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ)
    (n + 1)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app N))
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 (F.obj N) (n + 1)
    (by simp)

/-- **Positive-degree acyclicity** of the `k`-tensor of the two restricted resolutions. By the
Chapter 7 Künneth formula `kunnethChainComplexNatIso`,
`H_{n+1}(C₁ ⊗ C₂) ≅ ⨁_{p+q=n+1} H_p(C₁) ⊗ H_q(C₂)`; every summand vanishes because one of `p, q`
is positive and `homology_mapHomologicalComplex_projective_isZero_succ` makes the corresponding
restricted-resolution homology zero, so the tensor summand is zero. This is the positive-degree
input to the `quasiIso` obligation of `extTensorProjectiveResolution`. -/
theorem homology_tensorObj_res_isZero_succ
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    IsZero ((HomologicalComplex.tensorObj (res₁Complex (k := k) P₁)
      (res₂Complex (k := k) P₂)).homology (n + 1)) := by
  haveI : (res₁ k A₁).PreservesHomology := restrictScalars_preservesHomology _
  haveI : (res₂ k A₂).PreservesHomology := restrictScalars_preservesHomology _
  refine IsZero.of_iso ?_
    (kunnethChainComplexNatIso (res₁Complex (k := k) P₁) (res₂Complex (k := k) P₂) (n + 1))
  rw [IsZero.iff_id_eq_zero]
  apply Limits.Sigma.hom_ext
  intro a
  rw [Category.comp_id, comp_zero]
  obtain ⟨⟨p, q⟩, hpq⟩ := a
  have hpq' : p + q = n + 1 := hpq
  refine IsZero.eq_zero_of_src ?_ _
  rcases p with _ | p'
  · have hq : q = n + 1 := by omega
    subst hq
    exact TensorExtend.isZero_tensorObj_right
      (homology_mapHomologicalComplex_projective_isZero_succ P₂ (res₂ k A₂) n)
  · exact TensorExtend.isZero_tensorObj_left
      (homology_mapHomologicalComplex_projective_isZero_succ P₁ (res₁ k A₁) p')

/-- **Reverse of `ProjectiveResolution.isColimitCokernelCofork`.** If a chain map
`φ : K ⟶ single₀ N` (over an abelian category) has its degree-`0` component `φ.f 0` exhibiting `N`
as the cokernel of `K.d 1 0`, then `φ` is a quasi-isomorphism at degree `0`. The homology at `0`
of a chain complex is its degree-`0` opcycles (`isoHomologyι₀`), and both `K.pOpcycles 0` and
`φ.f 0` are cokernels of `K.d 1 0`, so the comparison of the two cokernels shows `opcyclesMap φ 0`
is an isomorphism. -/
theorem quasiIsoAt_zero_of_isColimitCokernelCofork {V : Type*} [Category V] [Abelian V]
    {K : ChainComplex V ℕ} {N : V} (φ : K ⟶ (ChainComplex.single₀ V).obj N)
    (hc : IsColimit (CokernelCofork.ofπ (φ.f 0)
      (show K.d 1 0 ≫ φ.f 0 = 0 by
        rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]))) :
    QuasiIsoAt φ 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- The comparison isomorphism between the two cokernels of `K.d 1 0`.
  have hcompare : K.pOpcycles 0 ≫
      (IsColimit.coconePointUniqueUpToIso (K.opcyclesIsCokernel 1 0 (by simp)) hc).hom = φ.f 0 := by
    have := IsColimit.comp_coconePointUniqueUpToIso_hom
      (K.opcyclesIsCokernel 1 0 (by simp)) hc WalkingParallelPair.one
    simpa only [Cofork.app_one_eq_π, CokernelCofork.π_ofπ] using this
  -- `L.pOpcycles 0` is an isomorphism since `L = single₀ N` has `L.d 1 0 = 0`.
  haveI : IsIso (((ChainComplex.single₀ V).obj N).pOpcycles 0) :=
    ((ChainComplex.single₀ V).obj N).isIso_pOpcycles 1 0 (by simp)
      (by rw [HomologicalComplex.single_obj_d])
  -- Hence `opcyclesMap φ 0 = e.hom ≫ L.pOpcycles 0` is an isomorphism.
  haveI : IsIso (HomologicalComplex.opcyclesMap φ 0) := by
    have hmap : HomologicalComplex.opcyclesMap φ 0 =
        (IsColimit.coconePointUniqueUpToIso (K.opcyclesIsCokernel 1 0 (by simp)) hc).hom ≫
          ((ChainComplex.single₀ V).obj N).pOpcycles 0 := by
      rw [← cancel_epi (K.pOpcycles 0), HomologicalComplex.p_opcyclesMap, ← Category.assoc,
        hcompare]
    rw [hmap]; infer_instance
  -- Transport back to `homologyMap` via `isoHomologyι₀`.
  have key : HomologicalComplex.homologyMap φ 0 =
      K.isoHomologyι₀.hom ≫ HomologicalComplex.opcyclesMap φ 0 ≫
        ((ChainComplex.single₀ V).obj N).isoHomologyι₀.inv := by
    rw [← ChainComplex.isoHomologyι₀_inv_naturality, Iso.hom_inv_id_assoc]
  rw [key]; infer_instance

/-- **Tensor of two degree-`0` cokernels is a cokernel of the total-complex differential.** If
`p₁` (resp. `p₂`) exhibits `N₁` (resp. `N₂`) as the cokernel of `C₁.d 1 0` (resp. `C₂.d 1 0`), then
any `q : (C₁ ⊗ C₂).X 0 ⟶ N₁ ⊗ N₂` whose restriction to the single degree-`0` summand is
`p₁ ⊗ p₂` exhibits `N₁ ⊗ N₂` as the cokernel of `(C₁ ⊗ C₂).d 1 0`. This is the categorical
right-exactness of `⊗` (`CokernelCofork.isColimitTensor`) transported through the identification of
the total-complex degree-`1 → 0` differential with `coprod.desc (d₁ ▷ ·) (· ◁ d₂)`. Extracted as a
standalone lemma so the heavy colimit bookkeeping is checked over abstract complexes. -/
noncomputable def isColimitCokernelCofork_tensorObj_augmentation
    {C₁ C₂ : ChainComplex (ModuleCat.{u} k) ℕ} [HomologicalComplex.HasTensor C₁ C₂]
    {N₁ N₂ : ModuleCat.{u} k} {p₁ : C₁.X 0 ⟶ N₁} {p₂ : C₂.X 0 ⟶ N₂}
    (hp₁comm : C₁.d 1 0 ≫ p₁ = 0) (hp₂comm : C₂.d 1 0 ≫ p₂ = 0)
    (hc₁ : IsColimit (CokernelCofork.ofπ p₁ hp₁comm))
    (hc₂ : IsColimit (CokernelCofork.ofπ p₂ hp₂comm))
    {q : (HomologicalComplex.tensorObj C₁ C₂).X 0 ⟶ N₁ ⊗ N₂}
    (hqcomm : (HomologicalComplex.tensorObj C₁ C₂).d 1 0 ≫ q = 0)
    (hq : HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl ≫ q = MonoidalCategory.tensorHom p₁ p₂) :
    IsColimit (CokernelCofork.ofπ q hqcomm) := by
  have htensor := CokernelCofork.isColimitTensor hc₁ hc₂
  have hππ : Cofork.π (CokernelCofork.tensor (CokernelCofork.ofπ p₁ hp₁comm)
      (CokernelCofork.ofπ p₂ hp₂comm)) = MonoidalCategory.tensorHom p₁ p₂ := by
    rw [CokernelCofork.π_ofπ, CokernelCofork.π_ofπ, CokernelCofork.π_ofπ]
  have hrel1 : HomologicalComplex.ιTensorObj C₁ C₂ 1 0 1 rfl ≫
      (HomologicalComplex.tensorObj C₁ C₂).d 1 0
      = (C₁.d 1 0 ▷ C₂.X 0) ≫ HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl := by
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₂_eq_zero (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 1) (i₂ := 0) (j := 0) (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₁_eq (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 1) (i₁' := 0) (i₂ := 0) (j := 0) (by simp [ComplexShape.down_Rel])
        (by simp ),
      show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (1, 0) = 1 from rfl, one_smul, add_zero]
    rfl
  have hrel2 : HomologicalComplex.ιTensorObj C₁ C₂ 0 1 1 rfl ≫
      (HomologicalComplex.tensorObj C₁ C₂).d 1 0
      = (C₁.X 0 ◁ C₂.d 1 0) ≫ HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl := by
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq_zero (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 0) (i₂ := 1) (j := 0) (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₂_eq (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 0) (i₂ := 1) (i₂' := 0) (j := 0) (by simp [ComplexShape.down_Rel])
        (by simp ),
      show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (0, 1) = 1 from by simp [ComplexShape.ε₂, ComplexShape.ε],
      one_smul, zero_add]
    rfl
  refine Cofork.IsColimit.mk _
    (fun s => htensor.desc (CokernelCofork.ofπ
      (HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl ≫ Cofork.π s) ?_)) ?_ ?_
  · apply Limits.coprod.hom_ext
    · rw [Limits.coprod.inl_desc_assoc, comp_zero, ← Category.assoc, ← hrel1, Category.assoc,
        CokernelCofork.condition s, comp_zero]
    · rw [Limits.coprod.inr_desc_assoc, comp_zero, ← Category.assoc, ← hrel2, Category.assoc,
        CokernelCofork.condition s, comp_zero]
  · intro s
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    obtain ⟨rfl, rfl⟩ : i₁ = 0 ∧ i₂ = 0 := by
      have : i₁ + i₂ = 0 := h
      omega
    rw [← Category.assoc, CokernelCofork.π_ofπ, hq, ← hππ, Cofork.IsColimit.π_desc,
      CokernelCofork.π_ofπ]
  · intro s m hm
    rw [CokernelCofork.π_ofπ] at hm
    apply Cofork.IsColimit.hom_ext htensor
    rw [Cofork.IsColimit.π_desc, hππ, CokernelCofork.π_ofπ, ← hq, Category.assoc, hm]

/-- The **external tensor product of two projective resolutions** `P•₁ ⊗_k P•₂` is a projective
resolution of `M₁ ⊗[k] M₂` over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. The complex and augmentation are the total
complex `extTensorComplex P₁ P₂` and its augmentation `extTensorπ P₁ P₂`; degreewise projectivity is
`extTensorComplex_projective`.

Exactness of the resolution (`quasiIso`): restriction of scalars to `k` reflects `QuasiIso` (it
preserves homology, `restrictScalars_preservesHomology`, and reflects isomorphisms), so it suffices
to check the restricted map, which `extTensorComplex_restrictIso` identifies with the
augmentation of the `k`-tensor total complex `res₁Complex P₁ ⊗ res₂Complex P₂ → res₁ M₁ ⊗ res₂ M₂`.
That is a quasi-isomorphism degreewise: positive degrees by the acyclicity
`homology_tensorObj_res_isZero_succ`, and degree `0` by the tensor-cokernel isomorphism. -/
noncomputable def extTensorProjectiveResolution
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ProjectiveResolution (ModuleCat.of (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂)) where
  complex := extTensorComplex P₁ P₂
  projective := extTensorComplex_projective P₁ P₂
  π := extTensorπ P₁ P₂
  quasiIso := by
    haveI : (resExt k A₁ A₂).PreservesHomology :=
      restrictScalars_preservesHomology (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)
    rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology (extTensorπ P₁ P₂)
      (resExt k A₁ A₂)]
    set sIso := extTensorComplex_restrictIso (k := k) P₁ P₂ with hsIso
    set tIso := (HomologicalComplex.singleMapHomologicalComplex (resExt k A₁ A₂)
        (ComplexShape.down ℕ) 0).app (extTensorFunctorObj k A₁ A₂ M₁ M₂) ≪≫
      (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
        (extRestrictObjIso (k := k) M₁ M₂) with htIso
    set Φ := sIso.inv ≫ ((resExt k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (extTensorπ P₁ P₂) ≫ tIso.hom with hΦ
    suffices hQ : QuasiIso Φ by
      have heq : ((resExt k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (extTensorπ P₁ P₂) = sIso.hom ≫ Φ ≫ tIso.inv := by
        rw [hΦ]; simp
      rw [heq]; infer_instance
    rw [quasiIso_iff]
    rintro (_ | n)
    · -- degree `0`: the tensor-cokernel augmentation isomorphism.
      refine quasiIsoAt_zero_of_isColimitCokernelCofork Φ ?_
      -- The two degree-`0` augmentations of the restricted resolutions.
      set p₁ : (res₁Complex P₁).X 0 ⟶ (res₁ k A₁).obj M₁ :=
        (res₁ k A₁).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1 with hp₁def
      set p₂ : (res₂Complex P₂).X 0 ⟶ (res₂ k A₂).obj M₂ :=
        (res₂ k A₂).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 with hp₂def
      -- Restriction of scalars preserves the degree-`0` cokernel, so `pᵢ` is a cokernel of `Cᵢ.d 1 0`.
      haveI : Limits.PreservesColimits (res₁ k A₁) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₁ᵐᵒᵖ)).leftAdjoint_preservesColimits
      haveI : Limits.PreservesColimits (res₂ k A₂) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₂ᵐᵒᵖ)).leftAdjoint_preservesColimits
      have hp₁comm : (res₁Complex P₁).d 1 0 ≫ p₁ = 0 := by
        have h : (res₁Complex P₁).d 1 0 ≫ p₁ = (res₁ k A₁).map (P₁.complex.d 1 0 ≫ P₁.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hp₂comm : (res₂Complex P₂).d 1 0 ≫ p₂ = 0 := by
        have h : (res₂Complex P₂).d 1 0 ≫ p₂ = (res₂ k A₂).map (P₂.complex.d 1 0 ≫ P₂.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hc₁ : IsColimit (CokernelCofork.ofπ p₁ hp₁comm) :=
        P₁.cokernelCofork.mapIsColimit P₁.isColimitCokernelCofork (res₁ k A₁)
      have hc₂ : IsColimit (CokernelCofork.ofπ p₂ hp₂comm) :=
        P₂.cokernelCofork.mapIsColimit P₂.isColimitCokernelCofork (res₂ k A₂)
      -- Identify `ι₀₀ ≫ Φ.f 0` with `p₁ ⊗ₘ p₂`.
      have h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (0, 0) = 0 := rfl
      have hgapA : HomologicalComplex.ιTensorObj (res₁Complex P₁) (res₂Complex P₂) 0 0 0 rfl ≫
          Φ.f 0 = MonoidalCategory.tensorHom p₁ p₂ := by
        have hs0 : sIso.inv.f 0 = (extRestrictComplexXIso P₁ P₂ 0).inv := by rw [hsIso]; rfl
        have hmid0 : (((resExt k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (extTensorπ P₁ P₂)).f 0 = (resExt k A₁ A₂).map (extTensorAug₀ P₁ P₂) := by
          change (resExt k A₁ A₂).map ((extTensorπ P₁ P₂).f 0) = _
          congr 1
        have ht0 : tIso.hom.f 0 = (extRestrictObjIso M₁ M₂).hom := by
          rw [htIso, Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom,
            HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
          simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, CategoryTheory.Functor.map_id,
            Iso.refl_inv, Category.id_comp,
            CategoryTheory.Functor.mapIso_hom, ChainComplex.single₀_map_f_zero]
          exact Category.id_comp _
        rw [hΦ]
        simp only [HomologicalComplex.comp_f]
        rw [hs0, hmid0, ht0, ← Category.assoc,
          ι_extRestrictComplexXIso_inv (k := k) P₁ P₂ 0 0 0 h₀, Category.assoc,
          ι_extRestrictComplexXIso_aug₀ (k := k) P₁ P₂ h₀, Iso.inv_hom_id_assoc]
      -- Build the cokernel of `K.d 1 0` from the tensor cokernel (right-exactness of `⊗`).
      exact isColimitCokernelCofork_tensorObj_augmentation hp₁comm hp₂comm hc₁ hc₂
        (show (HomologicalComplex.tensorObj (res₁Complex P₁) (res₂Complex P₂)).d 1 0 ≫ Φ.f 0 = 0 by
          rw [← Φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]) hgapA
    · -- positive degrees: source is acyclic, target is `single₀`.
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff_isZero_homology]
      exact homology_tensorObj_res_isZero_succ P₁ P₂ n

end Etingof
