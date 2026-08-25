import EtingofRepresentationTheory.Chapter8.SymmetricAlgebraDirectSum
import EtingofRepresentationTheory.Chapter8.ExternalTensorResolutionLeft
import EtingofRepresentationTheory.Chapter8.KoszulResolution

/-!
# The Koszul resolution of a complementary symmetric algebra

For finite-dimensional vector spaces `U` and `W`, this file constructs the resolution in Problem
8.2.10(ii).  We tensor the Koszul resolution of the trivial `S(U)`-module with the degree-zero
resolution of the regular `S(W)`-module.  The external tensor product is a resolution over
`S(U) ⊗ S(W)`; restriction along `S(U ⊕ W) ≃ S(U) ⊗ S(W)` transports it to `S(U ⊕ W)`.

The resolved object `koszulComplementModule k U W` has underlying vector space
`k ⊗[k] S(W)`, canonically equivalent to `S(W)`.  Its action is the requested one: the `U`
generators act through the augmentation of `S(U)`, hence by zero, while the `W` generators act
regularly on the second factor.
-/

open scoped TensorProduct
open CategoryTheory Limits HomologicalComplex

namespace Etingof

universe u

variable (k U W : Type u) [Field k]
  [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  [AddCommGroup W] [Module k W]

/-- The degree-zero projective resolution of the regular `S(W)`-module. -/
noncomputable def symmetricAlgebraSelfResolution :
    ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) :=
  ProjectiveResolution.self
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))

/-- The only nonzero term of the degree-zero resolution of the regular `S(W)`-module. -/
noncomputable def symmetricAlgebraSelfResolutionZeroIso :
    (symmetricAlgebraSelfResolution k W).complex.X 0 ≅
      ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W) :=
  HomologicalComplex.singleObjXIsoOfEq (ComplexShape.down ℕ) 0
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) 0 rfl

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

/-- The component of the projection from the external total complex to its unique nonzero
summand. The second resolution is concentrated in degree zero, so all components with positive
second degree are zero. -/
noncomputable def externalRegularTermComponent
    {M : ModuleCat.{u} (SymmetricAlgebra k U)} (P : ProjectiveResolution M)
    (n i₁ i₂ : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    ((extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X i₁)).obj ((symmetricAlgebraSelfResolution k W).complex.X i₂) ⟶
      ((extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X n)).obj
          (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) := by
  rcases i₂ with _ | i₂
  · have hi : i₁ = n := by simpa using h
    subst i₁
    exact ((extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
      (P.complex.X n)).map (symmetricAlgebraSelfResolutionZeroIso k W).hom
  · exact 0

omit [FiniteDimensional k U] in
@[simp]
theorem externalRegularTermComponent_zero
    {M : ModuleCat.{u} (SymmetricAlgebra k U)} (P : ProjectiveResolution M) (n : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (n, 0) = n) :
    externalRegularTermComponent k U W P n n 0 h =
      ((extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X n)).map (symmetricAlgebraSelfResolutionZeroIso k W).hom := by
  simp [externalRegularTermComponent]

/-- Because the regular `S(W)`-resolution is concentrated in degree zero, degree `n` of the
external total complex is canonically its `(n, 0)` summand. -/
noncomputable def externalRegularTermIso
    {M : ModuleCat.{u} (SymmetricAlgebra k U)} (P : ProjectiveResolution M) (n : ℕ) :
    (extTensorComplexLeft (k := k) P (symmetricAlgebraSelfResolution k W)).X n ≅
      ((extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X n)).obj
          (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) where
  hom := HomologicalComplex.mapBifunctorDesc (j := n)
    (externalRegularTermComponent k U W P n)
  inv := ((extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
      (P.complex.X n)).map (symmetricAlgebraSelfResolutionZeroIso k W).inv ≫
    HomologicalComplex.ιMapBifunctor P.complex (symmetricAlgebraSelfResolution k W).complex
      (extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W))
      (ComplexShape.down ℕ) n 0 n (by simp)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rcases i₂ with _ | i₂
    · have hi : i₁ = n := by simpa using h
      subst i₁
      rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
        externalRegularTermComponent_zero, ← Category.assoc, ← Functor.map_comp]
      simp
    · have hz : IsZero ((symmetricAlgebraSelfResolution k W).complex.X (i₂ + 1)) := by
        change IsZero (((ChainComplex.single₀ (ModuleCat.{u} (SymmetricAlgebra k W))).obj
          (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))).X (i₂ + 1))
        apply HomologicalComplex.isZero_single_obj_X
        simp
      exact (((extTensorFunctorLeft k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X i₁)).map_isZero hz).eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
      externalRegularTermComponent_zero, ← Functor.map_comp]
    simp

/-- Tensor the Koszul resolution of `k` over `S(U)` with the regular `S(W)`-module.  This is the
untransported form of Problem 8.2.10(ii), over `S(U) ⊗ S(W)`. -/
noncomputable def tensorKoszulComplementResolution :
    ProjectiveResolution
      (extTensorFunctorLeftObj k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
        (ModuleCat.of (SymmetricAlgebra k U) (KoszulAugModule k U))
        (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))) :=
  extTensorProjectiveResolutionLeft
    (koszulResolutionOfFiniteDimensional k U)
    (symmetricAlgebraSelfResolution k W)

/-- Change scalars from `S(U) ⊗ S(W)` to `S(U ⊕ W)` along the canonical algebra equivalence. -/
noncomputable abbrev restrictTensorToProd :
    ModuleCat (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W) ⥤
      ModuleCat (SymmetricAlgebra k (U × W)) :=
  ModuleCat.restrictScalars
    (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.toRingHom

/-- `S(W)` as an `S(U ⊕ W)`-module, presented as `k ⊗[k] S(W)`.  The first summand acts through
the augmentation and the second summand acts regularly. -/
noncomputable def koszulComplementModule : ModuleCat (SymmetricAlgebra k (U × W)) :=
  (restrictTensorToProd k U W).obj
    (extTensorFunctorLeftObj k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
      (ModuleCat.of (SymmetricAlgebra k U) (KoszulAugModule k U))
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)))

/-- **Problem 8.2.10(ii), resolution endpoint.**  The external tensor Koszul complex, transported
along `S(U ⊕ W) ≃ S(U) ⊗ S(W)`, is a projective resolution of the complementary symmetric-algebra
module.  Exactness is inherited from `extTensorProjectiveResolutionLeft`; no new homological
choice is made here. -/
noncomputable def koszulComplementResolution :
    ProjectiveResolution (koszulComplementModule k U W) :=
  (restrictTensorToProd k U W).mapProjectiveResolution
    (tensorKoszulComplementResolution k U W)

@[simp]
theorem koszulComplementResolution_complex :
    (koszulComplementResolution k U W).complex =
      ((restrictTensorToProd k U W).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (tensorKoszulComplementResolution k U W).complex :=
  rfl

/-- Every term of the transported complex is projective. -/
theorem koszulComplementResolution_projective (i : ℕ) :
    Projective ((koszulComplementResolution k U W).complex.X i) :=
  (koszulComplementResolution k U W).projective i

/-- The augmentation of the transported complex is a quasi-isomorphism, i.e. the complex is
exact and resolves `koszulComplementModule`. -/
theorem koszulComplementResolution_quasiIso :
    QuasiIso (koszulComplementResolution k U W).π :=
  (koszulComplementResolution k U W).quasiIso

/-! ## The literal free terms -/

/-- The unique nonzero summand in degree `i` before changing scalars. -/
noncomputable abbrev koszulComplementTermExternal (i : ℕ) :=
  extTensorFunctorLeftObj k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
    (ModuleCat.of (SymmetricAlgebra k U) (koszulX k U i))
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))

/-- The literal degree-`i` free module from Problem 8.2.10(ii). -/
abbrev koszulComplementX (i : ℕ) :=
  SymmetricAlgebra k (U × W) ⊗[k] (⋀[k]^i U)

noncomputable def koszulXRestrictEquiv (i : ℕ) :
    (res₁L k (SymmetricAlgebra k U)).obj
        (ModuleCat.of (SymmetricAlgebra k U) (koszulX k U i)) ≃ₗ[k]
      koszulX k U i where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

noncomputable def symmetricAlgebraRestrictEquiv :
    (res₂L k (SymmetricAlgebra k W)).obj
        (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) ≃ₗ[k]
      SymmetricAlgebra k W where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity-on-pure-tensors comparison from the categorical external tensor instance to the
ordinary tensor product. -/
noncomputable def koszulComplementTermBridge (i : ℕ) :
    letI : Module k (koszulComplementTermExternal k U W i) :=
      Module.compHom _ (algebraMap k
        (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W))
    koszulComplementTermExternal k U W i ≃ₗ[k]
      (koszulX k U i ⊗[k] SymmetricAlgebra k W) :=
  extRestrictObjEquivL
      (ModuleCat.of (SymmetricAlgebra k U) (koszulX k U i))
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) ≪≫ₗ
    TensorProduct.congr (koszulXRestrictEquiv k U i)
      (symmetricAlgebraRestrictEquiv k W)

/-- Reassociate `(S(U) ⊗ ⋀ⁱU) ⊗ S(W)` as `(S(U) ⊗ S(W)) ⊗ ⋀ⁱU`. -/
noncomputable def koszulComplementReassoc (i : ℕ) :
    (koszulX k U i ⊗[k] SymmetricAlgebra k W) ≃ₗ[k]
      ((SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W) ⊗[k] (⋀[k]^i U)) :=
  TensorProduct.assoc k (SymmetricAlgebra k U) (⋀[k]^i U)
      (SymmetricAlgebra k W) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl k (SymmetricAlgebra k U))
      (TensorProduct.comm k (⋀[k]^i U) (SymmetricAlgebra k W)) ≪≫ₗ
    (TensorProduct.assoc k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
      (⋀[k]^i U)).symm

/-- The underlying `k`-linear equivalence from the external summand to the literal term. -/
noncomputable def koszulComplementTermLinearEquiv (i : ℕ) :
    letI : Module k (koszulComplementTermExternal k U W i) :=
      Module.compHom _ (algebraMap k
        (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W))
    koszulComplementTermExternal k U W i ≃ₗ[k] koszulComplementX k U W i :=
  koszulComplementTermBridge k U W i ≪≫ₗ
    koszulComplementReassoc k U W i ≪≫ₗ
    TensorProduct.congr
      (symmetricAlgebraProdEquivTensor k U W).symm.toLinearEquiv
      (LinearEquiv.refl k (⋀[k]^i U))

/-- A pure tensor in the categorical external term, with its scalar instances fixed explicitly. -/
noncomputable def externalTermTmul (i : ℕ) (x : koszulX k U i)
    (t : SymmetricAlgebra k W) : koszulComplementTermExternal k U W i :=
  @TensorProduct.tmul k _
    (ModuleCat.of (SymmetricAlgebra k U) (koszulX k U i))
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) _ _
    (restrictModule₁L k (SymmetricAlgebra k U)
      (ModuleCat.of (SymmetricAlgebra k U) (koszulX k U i)))
    (restrictModule₂L k (SymmetricAlgebra k W)
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))) x t

omit [FiniteDimensional k U] in
@[simp]
theorem externalTermTmul_zero (i : ℕ) (t : SymmetricAlgebra k W) :
    externalTermTmul k U W i 0 t = 0 :=
  TensorProduct.zero_tmul
    (ModuleCat.of (SymmetricAlgebra k U) (koszulX k U i)) t

omit [FiniteDimensional k U] in
theorem externalTermTmul_add (i : ℕ) (x y : koszulX k U i)
    (t : SymmetricAlgebra k W) :
    externalTermTmul k U W i (x + y) t =
      externalTermTmul k U W i x t + externalTermTmul k U W i y t :=
  TensorProduct.add_tmul _ _ _

omit [FiniteDimensional k U] in
@[simp]
theorem koszulComplementTermLinearEquiv_tmul (i : ℕ)
    (s : SymmetricAlgebra k U) (x : ⋀[k]^i U) (t : SymmetricAlgebra k W) :
    koszulComplementTermLinearEquiv k U W i
      (externalTermTmul k U W i (s ⊗ₜ[k] x) t) =
        (symmetricAlgebraProdEquivTensor k U W).symm (s ⊗ₜ[k] t) ⊗ₜ[k] x := by
  rfl

noncomputable local instance symmetricAlgebraProdTensor_invPair :
    RingHomInvPair
      (symmetricAlgebraProdEquivTensor k U W).symm.toRingEquiv.toRingHom
      (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.toRingHom where
  comp_eq := by
    apply DFunLike.ext _ _
    exact (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.apply_symm_apply
  comp_eq₂ := by
    apply DFunLike.ext _ _
    exact (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.symm_apply_apply

noncomputable local instance symmetricAlgebraTensorProd_invPair :
    RingHomInvPair
      (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.toRingHom
      (symmetricAlgebraProdEquivTensor k U W).symm.toRingEquiv.toRingHom where
  comp_eq := by
    apply DFunLike.ext _ _
    exact (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.symm_apply_apply
  comp_eq₂ := by
    apply DFunLike.ext _ _
    exact (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.apply_symm_apply

omit [FiniteDimensional k U] in
theorem koszulComplementTermExternal_smul_tmul (i : ℕ)
    (a : SymmetricAlgebra k U) (b : SymmetricAlgebra k W)
    (q : koszulX k U i) (t : SymmetricAlgebra k W) :
    (koszulComplementTermExternal k U W i).isModule.toSMul.smul (a ⊗ₜ[k] b)
        (externalTermTmul k U W i q t) =
      externalTermTmul k U W i (a • q) (b * t) :=
  extTensorFunctorLeft_smul_tmul k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
    (ModuleCat.of (SymmetricAlgebra k U) (koszulX k U i))
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) a b q t

omit [FiniteDimensional k U] in
theorem koszulComplementTermLinearEquiv_external_smul_tmul (i : ℕ)
    (a : SymmetricAlgebra k U) (b : SymmetricAlgebra k W)
    (q : koszulX k U i) (t : SymmetricAlgebra k W) :
    koszulComplementTermLinearEquiv k U W i
        (externalTermTmul k U W i (a • q) (b * t)) =
      (symmetricAlgebraProdEquivTensor k U W).symm (a ⊗ₜ[k] b) •
        koszulComplementTermLinearEquiv k U W i
          (externalTermTmul k U W i q t) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      rw [smul_zero, externalTermTmul_zero, externalTermTmul_zero]
      simp only [map_zero, smul_zero]
  | add x y hx hy =>
      simp only [smul_add]
      change koszulComplementTermLinearEquiv k U W i
          (externalTermTmul k U W i (a • x + a • y) (b * t)) = _
      rw [externalTermTmul_add, externalTermTmul_add, map_add, map_add, hx, hy, smul_add]
  | tmul s x =>
      rw [TensorProduct.smul_tmul']
      rw [koszulComplementTermLinearEquiv_tmul,
        koszulComplementTermLinearEquiv_tmul]
      rw [TensorProduct.smul_tmul']
      congr 1
      change (symmetricAlgebraProdEquivTensor k U W).symm
          ((a * s) ⊗ₜ[k] (b * t)) =
        (symmetricAlgebraProdEquivTensor k U W).symm (a ⊗ₜ[k] b) *
          (symmetricAlgebraProdEquivTensor k U W).symm (s ⊗ₜ[k] t)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

omit [FiniteDimensional k U] in
/-- The canonical reassociation is equivariant for the external action, semilinearly along the
inverse of `S(U ⊕ W) ≃ S(U) ⊗ S(W)`. -/
theorem koszulComplementTermLinearEquiv_smul (i : ℕ)
    (r : SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W)
    (z : koszulComplementTermExternal k U W i) :
    koszulComplementTermLinearEquiv k U W i
        ((koszulComplementTermExternal k U W i).isModule.toSMul.smul r z) =
      (symmetricAlgebraProdEquivTensor k U W).symm r •
        koszulComplementTermLinearEquiv k U W i z := by
  induction r using TensorProduct.induction_on with
  | zero =>
      calc
        koszulComplementTermLinearEquiv k U W i
            ((koszulComplementTermExternal k U W i).isModule.toSMul.smul 0 z) =
          koszulComplementTermLinearEquiv k U W i 0 :=
            congrArg (koszulComplementTermLinearEquiv k U W i)
              ((koszulComplementTermExternal k U W i).isModule.zero_smul z)
        _ = 0 := map_zero _
        _ = _ := (zero_smul _ _).symm
  | add r t hr ht =>
      calc
        koszulComplementTermLinearEquiv k U W i
            ((koszulComplementTermExternal k U W i).isModule.toSMul.smul (r + t) z) =
          koszulComplementTermLinearEquiv k U W i
            ((koszulComplementTermExternal k U W i).isModule.toSMul.smul r z +
              (koszulComplementTermExternal k U W i).isModule.toSMul.smul t z) :=
                congrArg (koszulComplementTermLinearEquiv k U W i)
                  ((koszulComplementTermExternal k U W i).isModule.add_smul r t z)
        _ = koszulComplementTermLinearEquiv k U W i
              ((koszulComplementTermExternal k U W i).isModule.toSMul.smul r z) +
            koszulComplementTermLinearEquiv k U W i
              ((koszulComplementTermExternal k U W i).isModule.toSMul.smul t z) := map_add _ _ _
        _ = _ := by rw [hr, ht, map_add, add_smul]
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero =>
          calc
            koszulComplementTermLinearEquiv k U W i
                ((koszulComplementTermExternal k U W i).isModule.toSMul.smul
                  (a ⊗ₜ[k] b) 0) =
              koszulComplementTermLinearEquiv k U W i 0 :=
                congrArg (koszulComplementTermLinearEquiv k U W i)
                  ((koszulComplementTermExternal k U W i).isModule.smul_zero (a ⊗ₜ[k] b))
            _ = 0 := map_zero _
            _ = _ := (smul_zero _).symm
      | add x y hx hy =>
          calc
            koszulComplementTermLinearEquiv k U W i
                ((koszulComplementTermExternal k U W i).isModule.toSMul.smul
                  (a ⊗ₜ[k] b) (x + y)) =
              koszulComplementTermLinearEquiv k U W i
                ((koszulComplementTermExternal k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) x +
                  (koszulComplementTermExternal k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) y) :=
                      congrArg (koszulComplementTermLinearEquiv k U W i)
                        ((koszulComplementTermExternal k U W i).isModule.smul_add
                          (a ⊗ₜ[k] b) x y)
            _ = koszulComplementTermLinearEquiv k U W i
                  ((koszulComplementTermExternal k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) x) +
                koszulComplementTermLinearEquiv k U W i
                  ((koszulComplementTermExternal k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) y) := map_add _ _ _
            _ = _ := by
              rw [hx, hy]
              calc
                (symmetricAlgebraProdEquivTensor k U W).symm (a ⊗ₜ[k] b) •
                      koszulComplementTermLinearEquiv k U W i
                        (show koszulComplementTermExternal k U W i from x) +
                    (symmetricAlgebraProdEquivTensor k U W).symm (a ⊗ₜ[k] b) •
                      koszulComplementTermLinearEquiv k U W i
                        (show koszulComplementTermExternal k U W i from y) =
                  (symmetricAlgebraProdEquivTensor k U W).symm (a ⊗ₜ[k] b) •
                    (koszulComplementTermLinearEquiv k U W i
                        (show koszulComplementTermExternal k U W i from x) +
                      koszulComplementTermLinearEquiv k U W i
                        (show koszulComplementTermExternal k U W i from y)) :=
                          (smul_add _ _ _).symm
                _ = _ := congrArg
                  ((symmetricAlgebraProdEquivTensor k U W).symm (a ⊗ₜ[k] b) • ·)
                  (map_add (koszulComplementTermLinearEquiv k U W i)
                    (show koszulComplementTermExternal k U W i from x)
                    (show koszulComplementTermExternal k U W i from y)).symm
      | tmul q t =>
          change koszulComplementTermLinearEquiv k U W i
              ((koszulComplementTermExternal k U W i).isModule.toSMul.smul
                (a ⊗ₜ[k] b) (externalTermTmul k U W i q t)) =
            (symmetricAlgebraProdEquivTensor k U W).symm (a ⊗ₜ[k] b) •
              koszulComplementTermLinearEquiv k U W i (externalTermTmul k U W i q t)
          rw [koszulComplementTermExternal_smul_tmul,
            koszulComplementTermLinearEquiv_external_smul_tmul]

noncomputable def koszulComplementTermSemilinearEquiv (i : ℕ) :
    @LinearEquiv
      (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W)
      (SymmetricAlgebra k (U × W)) _ _
      (symmetricAlgebraProdEquivTensor k U W).symm.toRingEquiv.toRingHom
      (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.toRingHom
      (by infer_instance) (by infer_instance)
      (koszulComplementTermExternal k U W i) (koszulComplementX k U W i)
      _ _ (koszulComplementTermExternal k U W i).isModule inferInstance where
  toFun := koszulComplementTermLinearEquiv k U W i
  invFun := (koszulComplementTermLinearEquiv k U W i).symm
  left_inv := (koszulComplementTermLinearEquiv k U W i).left_inv
  right_inv := (koszulComplementTermLinearEquiv k U W i).right_inv
  map_add' := (koszulComplementTermLinearEquiv k U W i).map_add
  map_smul' := koszulComplementTermLinearEquiv_smul k U W i

/-- After restriction along `S(U ⊕ W) ≃ S(U) ⊗ S(W)`, the semilinear reassociation is an
honest `S(U ⊕ W)`-module isomorphism to the literal free term. -/
noncomputable def koszulComplementRestrictedTermIso (i : ℕ) :
    (restrictTensorToProd k U W).obj (koszulComplementTermExternal k U W i) ≅
      ModuleCat.of (SymmetricAlgebra k (U × W)) (koszulComplementX k U W i) := by
  let X := (restrictTensorToProd k U W).obj (koszulComplementTermExternal k U W i)
  change X ≅ _
  letI : Module (SymmetricAlgebra k (U × W)) X := X.isModule
  let eₛ := koszulComplementTermSemilinearEquiv k U W i
  let e : X ≃ₗ[SymmetricAlgebra k (U × W)] koszulComplementX k U W i :=
    { toFun := eₛ
      invFun := eₛ.symm
      left_inv := eₛ.left_inv
      right_inv := eₛ.right_inv
      map_add' := eₛ.map_add
      map_smul' := by
        intro r z
        change koszulComplementTermLinearEquiv k U W i
            ((koszulComplementTermExternal k U W i).isModule.toSMul.smul
              (symmetricAlgebraProdEquivTensor k U W r)
              (show koszulComplementTermExternal k U W i from z)) =
          r • koszulComplementTermLinearEquiv k U W i
            (show koszulComplementTermExternal k U W i from z)
        rw [koszulComplementTermLinearEquiv_smul]
        simp }
  exact e.toModuleIso

/-- **Literal degree-`i` term of Problem 8.2.10(ii).** Degree `i` of the transported external
Koszul resolution is canonically `S(U ⊕ W) ⊗[k] ⋀ⁱU`. -/
noncomputable def koszulComplementResolutionTermIso (i : ℕ) :
    (koszulComplementResolution k U W).complex.X i ≅
      ModuleCat.of (SymmetricAlgebra k (U × W)) (koszulComplementX k U W i) :=
  (restrictTensorToProd k U W).mapIso
      (externalRegularTermIso k U W (koszulResolutionOfFiniteDimensional k U) i) ≪≫
    koszulComplementRestrictedTermIso k U W i

/-- **Freeness endpoint of Problem 8.2.10(ii).** Every term in the complementary Koszul
resolution is free over `S(U ⊕ W)`, not merely projective. -/
theorem koszulComplementResolution_free (i : ℕ) :
    Module.Free (SymmetricAlgebra k (U × W))
      ((koszulComplementResolution k U W).complex.X i) := by
  letI : Module.Free k (⋀[k]^i U) := inferInstance
  letI : Module.Free (SymmetricAlgebra k (U × W)) (koszulComplementX k U W i) :=
    inferInstance
  exact Module.Free.of_equiv (koszulComplementResolutionTermIso k U W i).symm.toLinearEquiv

end Etingof
