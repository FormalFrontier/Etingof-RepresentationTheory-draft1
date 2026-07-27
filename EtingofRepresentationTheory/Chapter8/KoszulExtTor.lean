import EtingofRepresentationTheory.Chapter8.KoszulResolution
import EtingofRepresentationTheory.Chapter8.ExtCohomologyHomK
import EtingofRepresentationTheory.Chapter8.Problem8_2_6_ii_Crux
import EtingofRepresentationTheory.Chapter8.RearrangeHomComplexX
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import EtingofRepresentationTheory.Chapter8.Definition8_2_3_RightExact
import EtingofRepresentationTheory.Chapter8.PIDDecomposition
import Mathlib.Algebra.Homology.ShortComplex.RightHomology
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# `Ext` and `Tor` of the residue field over a symmetric algebra

This file computes both sides of Problem 8.2.10(v) directly from the Koszul resolution. After
applying either `Hom_{SV}(-, k)` or `- ⊗_{SV} k`, every differential is zero because each term of
the Koszul differential contains a positive-degree generator of `SV`, and those generators act
as zero on the augmentation module `k`.
-/

universe u

open CategoryTheory Limits

namespace Etingof

/-- If both differentials adjacent to degree `i` are zero, the homology in degree `i` is the
degree-`i` object itself. -/
noncomputable def homologyIsoXOfAllDZero {C : Type u} [Category C] [HasZeroMorphisms C]
    [CategoryWithHomology C] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (hzero : ∀ i j, K.d i j = 0) (i : ι) :
    K.homology i ≅ K.X i :=
  K.homologyIsoSc' (c.prev i) i (c.next i) rfl rfl ≪≫
    (ShortComplex.RightHomologyData.ofZeros (K.sc' (c.prev i) i (c.next i))
      (hzero _ _) (hzero _ _)).homologyIso

section Ext

variable (k : Type u) [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V]
variable {κ : Type u} [LinearOrder κ] [Fintype κ]

local notation "SV" => SymmetricAlgebra k V
local notation "K" => KoszulAugModule k V

/-- The tensor–Hom adjunction for a free `SV`-module, upgraded from the additive equivalence
`coeffHomEquiv` to a `k`-linear equivalence. -/
noncomputable def koszulHomLinearEquiv (i : ℕ) :
    (koszulX k V i →ₗ[SV] K) ≃ₗ[k] (⋀[k]^i V →ₗ[k] K) where
  toFun := coeffHomEquiv k SV K (⋀[k]^i V)
  invFun := (coeffHomEquiv k SV K (⋀[k]^i V)).symm
  left_inv := (coeffHomEquiv k SV K (⋀[k]^i V)).left_inv
  right_inv := (coeffHomEquiv k SV K (⋀[k]^i V)).right_inv
  map_add' := (coeffHomEquiv k SV K (⋀[k]^i V)).map_add
  map_smul' c f := by
    ext w
    rfl

@[simp]
theorem koszulHomLinearEquiv_apply (i : ℕ) (f : koszulX k V i →ₗ[SV] K)
    (w : ⋀[k]^i V) :
    koszulHomLinearEquiv k V i f w = f (1 ⊗ₜ[k] w) := rfl

/-- An `SV`-linear functional on a Koszul term is exactly a functional on its exterior-power
generator. -/
noncomputable def koszulHomDualEquiv (i : ℕ) :
    (koszulX k V i →ₗ[SV] K) ≃ₗ[k] Module.Dual k (⋀[k]^i V) :=
  koszulHomLinearEquiv k V i |>.trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl k (⋀[k]^i V)) (KoszulAugModule.equiv k V))

omit [LinearOrder κ] in
/-- Precomposition with a Koszul differential is zero on functionals valued in the
augmentation module. -/
theorem koszulHom_comp_koszulD_zero (b : Module.Basis κ k V) (i : ℕ)
    (f : koszulX k V i →ₗ[SV] K) :
    f.comp (koszulD b i) = 0 := by
  apply koszulX_hom_ext
  intro v
  apply (KoszulAugModule.equiv k V).injective
  rw [LinearMap.comp_apply, LinearMap.zero_apply, koszulD_one_tmul_ιMulti]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [LinearMap.map_smul_of_tower, map_smul]
  rw [show SymmetricAlgebra.ι k V (v j) ⊗ₜ[k]
      exteriorPower.ιMulti k i (v ∘ j.succAbove) =
      SymmetricAlgebra.ι k V (v j) •
        (1 ⊗ₜ[k] exteriorPower.ιMulti k i (v ∘ j.succAbove)) by
        rw [TensorProduct.smul_tmul']; simp]
  rw [f.map_smul, KoszulAugModule.equiv_smul]
  simp [SymmetricAlgebra.algebraMapInv_ι]

/-- The differential of the packaged Koszul resolution is the explicit Koszul differential. -/
theorem koszulResolution_d (b : Module.Basis κ k V) (i : ℕ) :
    (koszulResolution b).complex.d (i + 1) i = ModuleCat.ofHom (koszulD b i) := by
  change (koszulComplex b).d (i + 1) i = _
  exact koszulComplex_d b i

/-- Every differential in `Hom_{SV}(C_•, k)` is zero. -/
theorem koszulLinearYoneda_d_zero (b : Module.Basis κ k V) :
    ∀ i j, ((koszulResolution b).complex.linearYonedaObj k
      (ModuleCat.of SV K)).d i j = 0 := by
  intro i j
  rw [ChainComplex.linearYonedaObj_d]
  have hd : Linear.leftComp k (ModuleCat.of SV K)
      ((koszulResolution b).complex.d j i) = 0 := by
    by_cases h : j = i + 1
    · subst j
      apply DFunLike.ext _ _
      intro f
      apply ModuleCat.hom_ext
      apply DFunLike.ext _ _
      intro x
      rw [koszulResolution_d]
      change f.hom (koszulD b i x) = 0
      exact LinearMap.congr_fun (koszulHom_comp_koszulD_zero k V b i f.hom) x
    · have hshape : ¬ (ComplexShape.down ℕ).Rel j i := by simpa [eq_comm] using h
      rw [(koszulResolution b).complex.shape j i hshape]
      apply DFunLike.ext _ _
      intro f
      apply ModuleCat.hom_ext
      apply DFunLike.ext _ _
      intro x
      change ((0 : (koszulResolution b).complex.X j ⟶
        (koszulResolution b).complex.X i) ≫ f).hom x = (0 : K)
      rw [zero_comp]
      rfl
  rw [hd]
  rfl

/-- The categorical `SV`-Hom out of a Koszul term is linearly equivalent to the dual of its
exterior-power generators. -/
noncomputable def koszulCategoricalHomDualEquiv (i : ℕ) :
    (ModuleCat.of SV (koszulX k V i) ⟶ ModuleCat.of SV K) ≃ₗ[k]
      Module.Dual k (⋀[k]^i V) where
  toFun f := (KoszulAugModule.equiv k V).toLinearMap.comp
    (koszulHomLinearEquiv k V i f.hom)
  invFun g := ModuleCat.ofHom ((koszulHomLinearEquiv k V i).symm
    ((KoszulAugModule.equiv k V).symm.toLinearMap.comp g))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply (koszulHomLinearEquiv k V i).injective
    ext w
    simp
  right_inv g := by
    ext w
    simp
  map_add' f g := by
    ext w
    rfl
  map_smul' c f := by
    ext w
    rfl

/-- The degree-`i` object of the Koszul Hom complex is the dual of `⋀ⁱV`. -/
noncomputable def koszulLinearYonedaXIso (b : Module.Basis κ k V) (i : ℕ) :
    ((koszulResolution b).complex.linearYonedaObj k (ModuleCat.of SV K)).X i ≅
      ModuleCat.of k (Module.Dual k (⋀[k]^i V)) :=
  eqToIso (linYonedaXEq k SV K (koszulResolution b).complex i) ≪≫
    eqToIso (congrArg (fun X : ModuleCat SV => ModuleCat.of k
      (X ⟶ ModuleCat.of SV K)) (by rw [koszulResolution_complex, koszulComplex_X])) ≪≫
    (koszulCategoricalHomDualEquiv k V i).toModuleIso

/-- **Problem 8.2.10(v), `Ext`.** For every `i`,
`Extⁱ_{SV}(k,k) ≅ (⋀ⁱV)∗` as `k`-vector spaces. -/
noncomputable def koszulExtIso (b : Module.Basis κ k V) (i : ℕ) :
    Extₖ k SV (ModuleCat.of SV K) (ModuleCat.of SV K) i ≅
      ModuleCat.of k (Module.Dual k (⋀[k]^i V)) :=
  extIsoCohomologyHomₖ k SV (ModuleCat.of SV K) (ModuleCat.of SV K)
      (koszulResolution b) i ≪≫
    homologyIsoXOfAllDZero _ (koszulLinearYoneda_d_zero k V b) i ≪≫
    koszulLinearYonedaXIso k V b i

end Ext

section Tor

variable (k : Type u) [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V]
variable {κ : Type u} [LinearOrder κ] [Fintype κ]

local notation "SV" => SymmetricAlgebra k V
local notation "K" => KoszulAugModule k V

noncomputable local instance instModuleKSVObj (M : ModuleCat.{u} SV) : Module k M :=
  Module.compHom M (algebraMap k SV)

local instance instTowerSVObj (M : ModuleCat.{u} SV) : IsScalarTower k SV M :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

noncomputable local instance instModuleKMopObj (M : ModuleCat.{u} SVᵐᵒᵖ) : Module k M :=
  Module.compHom M (algebraMap k SVᵐᵒᵖ)

local instance instTowerMopObj (M : ModuleCat.{u} SVᵐᵒᵖ) : IsScalarTower k SVᵐᵒᵖ M :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance instCommMopObj (M : ModuleCat.{u} SVᵐᵒᵖ) : SMulCommClass k SVᵐᵒᵖ M where
  smul_comm c a m := by
    change (algebraMap k SVᵐᵒᵖ c) • (a • m) = a • ((algebraMap k SVᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

noncomputable local instance instModuleSVMopObj (M : ModuleCat.{u} SV) :
    Module SV ((mopFunctor SV).obj M) :=
  Module.compHom ((mopFunctor SV).obj M) (mopRingEquiv SV).symm.toRingHom

noncomputable local instance (priority := 2000) instModuleKMopLeftObj
    (M : ModuleCat.{u} SV) : Module k ((mopFunctor SV).obj M) :=
  Module.compHom ((mopFunctor SV).obj M) (algebraMap k SV)

local instance instTowerSVMopObj (M : ModuleCat.{u} SV) :
    IsScalarTower k SV ((mopFunctor SV).obj M) where
  smul_assoc c a x := by
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

local instance (priority := 2000) instCommKMopLeftObj (M : ModuleCat.{u} SV) :
    SMulCommClass k SVᵐᵒᵖ ((mopFunctor SV).obj M) where
  smul_comm c a x := by
    change (algebraMap k SV c) • (a.unop • x) = a.unop • ((algebraMap k SV c) • x)
    rw [← mul_smul, ← mul_smul, mul_comm]

/-- A commutative module transported to right modules and back to left modules has its original
action. -/
noncomputable def mopAsLeftLinearEquiv (M : ModuleCat.{u} SV) :
    ((mopFunctor SV).obj M) ≃ₗ[SV] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def mopTensorLinearEquiv (M : ModuleCat.{u} SV) :
    TensorProduct SV ((mopFunctor SV).obj M) K ≃ₗ[k] TensorProduct SV M K :=
  ((TensorProduct.congr (mopAsLeftLinearEquiv k V M) (LinearEquiv.refl SV K) :
    TensorProduct SV ((mopFunctor SV).obj M) K ≃ₗ[SV] TensorProduct SV M K)).restrictScalars k

noncomputable def koszulTensorComm (i : ℕ) :
    TensorProduct SV (koszulX k V i) K ≃ₗ[k] TensorProduct SV K (koszulX k V i) :=
  ((TensorProduct.comm SV (koszulX k V i) K :
    TensorProduct SV (koszulX k V i) K ≃ₗ[SV]
      TensorProduct SV K (koszulX k V i))).restrictScalars k

noncomputable def koszulCancelBaseChange (i : ℕ) :
    TensorProduct SV K (koszulX k V i) ≃ₗ[k] TensorProduct k K (⋀[k]^i V) :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange k SV SV K (⋀[k]^i V) :
    TensorProduct SV K (koszulX k V i) ≃ₗ[SV]
      TensorProduct k K (⋀[k]^i V))).restrictScalars k

/-- The left and right `SV`-actions agree after applying `mopFunctor`, because `SV` is
commutative. -/
theorem mopFunctor_compat (M : ModuleCat.{u} SV) (a : SV) (x : M) :
    (MulOpposite.op a • (show (mopFunctor SV).obj M from x)) = a • x := by
  change mopRingEquiv SV (MulOpposite.op a) • x = a • x
  rfl

/-- For a commutative `k`-algebra, the repository's noncommutative ring tensor product agrees
`k`-linearly with Mathlib's tensor product. -/
noncomputable def tensorOverMopLinearEquivTensor (M : ModuleCat.{u} SV) :
    tensorOver SV K ((mopFunctor SV).obj M) ≃ₗ[k]
      TensorProduct SV ((mopFunctor SV).obj M) K where
  toFun := tensorOverEquivTensor (M := (mopFunctor SV).obj M) (mopFunctor_compat k V M)
  invFun := (tensorOverEquivTensor (M := (mopFunctor SV).obj M)
    (mopFunctor_compat k V M)).symm
  left_inv := (tensorOverEquivTensor (M := (mopFunctor SV).obj M)
    (mopFunctor_compat k V M)).left_inv
  right_inv := (tensorOverEquivTensor (M := (mopFunctor SV).obj M)
    (mopFunctor_compat k V M)).right_inv
  map_add' := (tensorOverEquivTensor (M := (mopFunctor SV).obj M)
    (mopFunctor_compat k V M)).map_add
  map_smul' c z := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    induction y with
    | zero => rfl
    | tmul m x => rfl
    | add x y hx hy =>
        simpa only [QuotientAddGroup.mk_add, smul_add, map_add] using congrArg₂ (· + ·) hx hy

@[simp]
theorem tensorOverMopLinearEquivTensor_mk (M : ModuleCat.{u} SV)
    (m : (mopFunctor SV).obj M) (c : K) :
    tensorOverMopLinearEquivTensor k V M
      (QuotientAddGroup.mk (m ⊗ₜ[ℤ] c)) = m ⊗ₜ[SV] c := rfl

/-- The base-changed Koszul term tensored with the residue field is its exterior-power
generator space. -/
noncomputable def koszulTensorTermEquiv (i : ℕ) :
    tensorOver SV K ((mopFunctor SV).obj (ModuleCat.of SV (koszulX k V i))) ≃ₗ[k]
      ⋀[k]^i V :=
  tensorOverMopLinearEquivTensor k V (ModuleCat.of SV (koszulX k V i)) |>.trans
    (mopTensorLinearEquiv k V (ModuleCat.of SV (koszulX k V i))) |>.trans
    (koszulTensorComm k V i) |>.trans
    (koszulCancelBaseChange k V i) |>.trans
    (TensorProduct.congr (KoszulAugModule.equiv k V)
      (LinearEquiv.refl k (⋀[k]^i V))) |>.trans
    (TensorProduct.lid k (⋀[k]^i V))

/-- The Koszul resolution transported to right `SV`-modules. -/
noncomputable def koszulRightResolution (b : Module.Basis κ k V) :
    ProjectiveResolution ((mopFunctor SV).obj (ModuleCat.of SV K)) :=
  (mopFunctor SV).mapProjectiveResolution (koszulResolution b)

theorem symmetricGenerator_smul_koszulAug_zero (v : V) (c : K) :
    SymmetricAlgebra.ι k V v • c = 0 := by
  apply (KoszulAugModule.equiv k V).injective
  rw [KoszulAugModule.equiv_smul]
  simp [SymmetricAlgebra.algebraMapInv_ι]

omit [LinearOrder κ] in
theorem koszulD_tmul_tensor_koszulAug_zero (b : Module.Basis κ k V) (i : ℕ)
    (s : SV) (w : ⋀[k]^(i + 1) V) (c : K) :
    koszulD b i (s ⊗ₜ[k] w) ⊗ₜ[SV] c = 0 := by
  rw [koszulD_tmul, TensorProduct.sum_tmul]
  apply Finset.sum_eq_zero
  intro a _
  rw [show SymmetricAlgebra.ι k V (b a) * s =
      SymmetricAlgebra.ι k V (b a) • s by rfl]
  rw [show (SymmetricAlgebra.ι k V (b a) • s) ⊗ₜ[k]
      exteriorContraction k (b.coord a) i w =
      SymmetricAlgebra.ι k V (b a) •
        (s ⊗ₜ[k] exteriorContraction k (b.coord a) i w) by
        rw [TensorProduct.smul_tmul']]
  calc
    (SymmetricAlgebra.ι k V (b a) •
        (s ⊗ₜ[k] exteriorContraction k (b.coord a) i w)) ⊗ₜ[SV] c =
      (s ⊗ₜ[k] exteriorContraction k (b.coord a) i w) ⊗ₜ[SV]
        (SymmetricAlgebra.ι k V (b a) • c) := TensorProduct.smul_tmul _ _ _
    _ = 0 := by rw [symmetricGenerator_smul_koszulAug_zero, TensorProduct.tmul_zero]

omit [LinearOrder κ] in
theorem koszulD_tensor_koszulAug_zero (b : Module.Basis κ k V) (i : ℕ)
    (m : koszulX k V (i + 1)) (c : K) : koszulD b i m ⊗ₜ[SV] c = 0 := by
  induction m using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.zero_tmul]
  | tmul s w => exact koszulD_tmul_tensor_koszulAug_zero k V b i s w c
  | add x y hx hy => rw [map_add, TensorProduct.add_tmul, hx, hy, add_zero]

omit [LinearOrder κ] in
/-- Tensoring a Koszul differential with the augmentation module gives the zero map. -/
theorem koszulTensorMapD_zero (b : Module.Basis κ k V) (i : ℕ) :
    tensorRightMapₖ k SV K
      ((mopFunctor SV).map (ModuleCat.ofHom (koszulD b i))) = 0 := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.zero_apply]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => rfl
  | tmul m c =>
      apply (tensorOverMopLinearEquivTensor k V
        (ModuleCat.of SV (koszulX k V i))).injective
      rw [tensorRightMapₖ_mk, map_zero]
      rw [tensorOverMopLinearEquivTensor_mk]
      exact koszulD_tensor_koszulAug_zero k V b i m c
  | add x y hx hy =>
      rw [QuotientAddGroup.mk_add, map_add, hx, hy, add_zero]

/-- The Koszul resolution after tensoring with the augmentation module. -/
noncomputable def koszulTensorComplex (b : Module.Basis κ k V) :
    HomologicalComplex (ModuleCat.{u} k) (ComplexShape.down ℕ) :=
  ((tensorRightFunctorₖ k SV K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (koszulRightResolution k V b).complex

theorem koszulTensorComplex_d_zero (b : Module.Basis κ k V) :
    ∀ i j, (koszulTensorComplex k V b).d i j = 0 := by
  intro i j
  rw [koszulTensorComplex, Functor.mapHomologicalComplex_obj_d]
  by_cases h : i = j + 1
  · subst i
    change ModuleCat.ofHom (tensorRightMapₖ k SV K
      ((mopFunctor SV).map ((koszulResolution b).complex.d (j + 1) j))) = 0
    rw [koszulResolution_d]
    apply ModuleCat.hom_ext
    exact koszulTensorMapD_zero k V b j
  · have hshape : ¬(ComplexShape.down ℕ).Rel i j := by simpa [eq_comm] using h
    rw [(koszulRightResolution k V b).complex.shape i j hshape]
    exact (tensorRightFunctorₖ k SV K).map_zero _ _

/-- The degree-`i` object of the tensor-applied Koszul complex is `⋀ⁱV`. -/
noncomputable def koszulTensorComplexXIso (b : Module.Basis κ k V) (i : ℕ) :
    (koszulTensorComplex k V b).X i ≅ ModuleCat.of k (⋀[k]^i V) :=
  (koszulTensorTermEquiv k V i).toModuleIso

/-- **Problem 8.2.10(v), `Tor`.** For every `i`,
`Torᵢ^{SV}(k,k) ≅ ⋀ⁱV` as `k`-vector spaces. -/
noncomputable def koszulTorIso (b : Module.Basis κ k V) (i : ℕ) :
    Torₖ k SV K ((mopFunctor SV).obj (ModuleCat.of SV K)) i ≅
      ModuleCat.of k (⋀[k]^i V) :=
  torIsoHomologyTensorRightₖ k SV K _ (koszulRightResolution k V b) i ≪≫
    homologyIsoXOfAllDZero _ (koszulTensorComplex_d_zero k V b) i ≪≫
    koszulTensorComplexXIso k V b i

end Tor

end Etingof
