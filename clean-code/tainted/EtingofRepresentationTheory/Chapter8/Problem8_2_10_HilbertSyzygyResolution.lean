import EtingofRepresentationTheory.Chapter8.KoszulBimoduleShear
import EtingofRepresentationTheory.Chapter8.Problem8_2_10_HilbertSyzygy

open CategoryTheory Limits TensorProduct MonoidalCategory

universe u
namespace Etingof

private theorem quasiIso_comp_iso
    {C : Type u} [Category C] [Abelian C] {K L M : ChainComplex C ℕ}
    (φ : K ⟶ L) [QuasiIso φ] (e : L ≅ M) : QuasiIso (φ ≫ e.hom) := by
  infer_instance

private theorem quasiIso_comp_explicit
    {C : Type u} [Category C] [Abelian C] {K L M : ChainComplex C ℕ}
    (φ : K ⟶ L) (φ' : L ⟶ M) (hφ : QuasiIso φ) (hφ' : QuasiIso φ') :
    QuasiIso (φ ≫ φ') := by
  letI : QuasiIso φ := hφ
  letI : QuasiIso φ' := hφ'
  infer_instance

private theorem quasiIso_of_comp_right_explicit
    {C : Type u} [Category C] [Abelian C] {K L M : ChainComplex C ℕ}
    (φ : K ⟶ L) (φ' : L ⟶ M) (hφ' : QuasiIso φ')
    (hcomp : QuasiIso (φ ≫ φ')) : QuasiIso φ := by
  letI : QuasiIso φ' := hφ'
  letI : QuasiIso (φ ≫ φ') := hcomp
  exact quasiIso_of_comp_right φ φ'

variable (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V]

noncomputable abbrev rightRestrictionFunctor :
    ModuleCat.{u} (E k V) ⥤ ModuleCat.{u} (S k V) :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight.toRingHom)

noncomputable abbrev rightRestrictedLiteralTerm (i : ℕ) : ModuleCat.{u} (S k V) :=
  (rightRestrictionFunctor k V).obj
    (@ModuleCat.of (E k V) _ (koszulBimoduleX k V i) _
      (koszulBimoduleTermModule k V i))

theorem rightRestrictedLiteralTerm_smul_tmul (i : ℕ) (a : S k V)
    (q : koszulX k V i) (t : S k V) :
    a • (show rightRestrictedLiteralTerm k V i from
      explicitKoszulTermTmul k V i q t) =
      explicitKoszulTermTmul k V i q (a * t) := by
  change (koszulBimoduleTermExternalModule k V i).toSMul.smul
      (shearEquiv k V (Algebra.TensorProduct.includeRight a))
      (explicitKoszulTermTmul k V i q t) = _
  rw [show shearEquiv k V (Algebra.TensorProduct.includeRight a) =
      Algebra.TensorProduct.includeRight a by
        simp [shearEquiv, shearHom]]
  simpa [Algebra.TensorProduct.includeRight_apply] using
    explicitKoszulTerm_smul_tmul k V i 1 a q t

noncomputable def rightRestrictedLiteralTermAction (i : ℕ) (a : S k V)
    (z : koszulBimoduleX k V i) : koszulBimoduleX k V i :=
  show rightRestrictedLiteralTerm k V i from
    a • (show rightRestrictedLiteralTerm k V i from z)

@[simp] theorem rightRestrictedLiteralTermAction_zero (i : ℕ) (a : S k V) :
    rightRestrictedLiteralTermAction k V i a 0 = 0 := by
  change a • (0 : rightRestrictedLiteralTerm k V i) = 0
  exact smul_zero a

theorem rightRestrictedLiteralTermAction_add (i : ℕ) (a : S k V)
    (x y : koszulBimoduleX k V i) :
    rightRestrictedLiteralTermAction k V i a (x + y) =
      rightRestrictedLiteralTermAction k V i a x +
        rightRestrictedLiteralTermAction k V i a y := by
  change a • (show rightRestrictedLiteralTerm k V i from x + y) = _
  exact (rightRestrictedLiteralTerm k V i).isModule.smul_add a
    (show rightRestrictedLiteralTerm k V i from x)
    (show rightRestrictedLiteralTerm k V i from y)

@[simp] theorem rightRestrictedLiteralTermAction_tmul (i : ℕ) (a : S k V)
    (q : koszulX k V i) (t : S k V) :
    rightRestrictedLiteralTermAction k V i a
        (explicitKoszulTermTmul k V i q t) =
      explicitKoszulTermTmul k V i q (a * t) :=
  rightRestrictedLiteralTerm_smul_tmul k V i a q t

noncomputable def rightRestrictedLiteralTermFreeEquiv (i : ℕ) :
    rightRestrictedLiteralTerm k V i ≃ₗ[S k V]
      (S k V ⊗[k] koszulX k V i) where
  toFun := TensorProduct.comm k (koszulX k V i) (S k V)
  invFun := (TensorProduct.comm k (koszulX k V i) (S k V)).symm
  left_inv := (TensorProduct.comm k (koszulX k V i) (S k V)).left_inv
  right_inv := (TensorProduct.comm k (koszulX k V i) (S k V)).right_inv
  map_add' := (TensorProduct.comm k (koszulX k V i) (S k V)).map_add
  map_smul' := by
    intro a z
    change (TensorProduct.comm k (koszulX k V i) (S k V))
        (rightRestrictedLiteralTermAction k V i a z) =
      a • (TensorProduct.comm k (koszulX k V i) (S k V)) z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        rw [rightRestrictedLiteralTermAction_add, map_add, hx, hy, map_add, smul_add]
    | tmul q t =>
        change (TensorProduct.comm k (koszulX k V i) (S k V))
            (rightRestrictedLiteralTermAction k V i a
              (explicitKoszulTermTmul k V i q t)) = _
        rw [rightRestrictedLiteralTermAction_tmul]
        rfl

theorem rightRestrictedLiteralTerm_free (i : ℕ) :
    Module.Free (S k V) (rightRestrictedLiteralTerm k V i) := by
  letI : Module.Free k (koszulX k V i) := inferInstance
  letI : Module.Free (S k V) (S k V ⊗[k] koszulX k V i) := inferInstance
  exact Module.Free.of_equiv (rightRestrictedLiteralTermFreeEquiv k V i).symm

@[simp] theorem rightRestrictedLiteralTermFreeEquiv_tmul (i : ℕ)
    (s t : S k V) (x : ⋀[k]^i V) :
    rightRestrictedLiteralTermFreeEquiv k V i
      (show rightRestrictedLiteralTerm k V i from
        explicitKoszulTermTmul k V i (s ⊗ₜ[k] x) t) =
      t ⊗ₜ[k] (s ⊗ₜ[k] x) := rfl

noncomputable def rightRestrictedBimoduleResolutionTermIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    (((rightRestrictionFunctor k V).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (koszulBimoduleResolution k V b).complex).X i ≅
      rightRestrictedLiteralTerm k V i :=
  (rightRestrictionFunctor k V).mapIso (koszulBimoduleResolutionTermIso k V b i)

theorem rightRestrictedBimoduleResolutionTerm_free
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    Module.Free (S k V)
      ((((rightRestrictionFunctor k V).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (koszulBimoduleResolution k V b).complex).X i) := by
  letI : Module.Free (S k V) (rightRestrictedLiteralTerm k V i) :=
    rightRestrictedLiteralTerm_free k V i
  exact Module.Free.of_equiv
    (rightRestrictedBimoduleResolutionTermIso k V b i).symm.toLinearEquiv

noncomputable abbrev rightRestrictedBimoduleTarget : ModuleCat.{u} (S k V) :=
  (rightRestrictionFunctor k V).obj
    (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V))

noncomputable def rightRestrictedBimoduleTargetIso :
    rightRestrictedBimoduleTarget k V ≅ regularObj k V := by
  let e : rightRestrictedBimoduleTarget k V ≃ₗ[S k V] S k V :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change bimodAct k V (Algebra.TensorProduct.includeRight a) (show S k V from x) =
          a * (show S k V from x)
        simpa [Algebra.TensorProduct.includeRight_apply] using
          bimodAct_tmul k V 1 a x }
  exact e.toModuleIso

noncomputable def rightRestrictedBimoduleResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ProjectiveResolution (regularObj k V) where
  complex := ((rightRestrictionFunctor k V).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (koszulBimoduleResolution k V b).complex
  projective i := by
    letI : Module.Free (S k V)
        ((((rightRestrictionFunctor k V).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
          (koszulBimoduleResolution k V b).complex).X i) :=
      rightRestrictedBimoduleResolutionTerm_free k V b i
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis (S k V) _)
  π := ((rightRestrictionFunctor k V).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (koszulBimoduleResolution k V b).π ≫
    (HomologicalComplex.singleMapHomologicalComplex (rightRestrictionFunctor k V)
      (ComplexShape.down ℕ) 0).hom.app _ ≫
    (ChainComplex.single₀ (ModuleCat.{u} (S k V))).map
      (rightRestrictedBimoduleTargetIso k V).hom
  quasiIso := by
    letI : (rightRestrictionFunctor k V).PreservesHomology :=
      restrictScalars_preservesHomology _
    let φ := ((rightRestrictionFunctor k V).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (koszulBimoduleResolution k V b).π
    let e₁ := (HomologicalComplex.singleMapHomologicalComplex (rightRestrictionFunctor k V)
      (ComplexShape.down ℕ) 0).app
        (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V))
    let e₂ := (ChainComplex.single₀ (ModuleCat.{u} (S k V))).mapIso
      (rightRestrictedBimoduleTargetIso k V)
    haveI : QuasiIso φ := inferInstance
    haveI hφe₁ : QuasiIso (φ ≫ e₁.hom) := quasiIso_comp_iso φ e₁
    change QuasiIso (φ ≫ e₁.hom ≫ e₂.hom)
    exact quasiIso_comp_iso (φ ≫ e₁.hom) e₂

/-! Tensoring a bimodule over its right `SV` action while retaining the left action. -/

noncomputable abbrev rightInclude : S k V →+* E k V :=
  (Algebra.TensorProduct.includeRight (R := k) (A := S k V) (B := S k V)).toRingHom

noncomputable abbrev leftInclude : S k V →+* E k V :=
  (Algebra.TensorProduct.includeLeft (R := k) (S := k)
    (A := S k V) (B := S k V)).toRingHom

@[reducible] noncomputable def bimoduleTensorModule (M : ModuleCat.{u} (S k V))
    (X : ModuleCat.{u} (E k V)) :
    Module (S k V) ((rightRestrictionFunctor k V).obj X ⊗[S k V] M) := by
  letI : Module (E k V) ((rightRestrictionFunctor k V).obj X) := X.isModule
  letI : SMulCommClass (S k V) (E k V) ((rightRestrictionFunctor k V).obj X) := by
    constructor
    intro a r x
    simp only [ModuleCat.restrictScalars.smul_def]
    exact smul_comm (rightInclude k V a) r (show X from x)
  letI : Module (E k V) ((rightRestrictionFunctor k V).obj X ⊗[S k V] M) :=
    TensorProduct.leftModule
  exact Module.compHom _ (leftInclude k V)

noncomputable def bimoduleTensorObj (M : ModuleCat.{u} (S k V))
    (X : ModuleCat.{u} (E k V)) : ModuleCat.{u} (S k V) :=
  @ModuleCat.of (S k V) _
    ((rightRestrictionFunctor k V).obj X ⊗[S k V] M) _
      (bimoduleTensorModule k V M X)

noncomputable def bimoduleTensorAction (M : ModuleCat.{u} (S k V))
    (X : ModuleCat.{u} (E k V)) (a : S k V)
    (z : (rightRestrictionFunctor k V).obj X ⊗[S k V] M) :
    (rightRestrictionFunctor k V).obj X ⊗[S k V] M :=
  show bimoduleTensorObj k V M X from
    a • (show bimoduleTensorObj k V M X from z)

@[simp] theorem bimoduleTensorAction_zero (M : ModuleCat.{u} (S k V))
    (X : ModuleCat.{u} (E k V)) (a : S k V) :
    bimoduleTensorAction k V M X a 0 = 0 := by
  change a • (0 : bimoduleTensorObj k V M X) = 0
  exact (bimoduleTensorObj k V M X).isModule.smul_zero a

theorem bimoduleTensorAction_add (M : ModuleCat.{u} (S k V))
    (X : ModuleCat.{u} (E k V)) (a : S k V)
    (x y : (rightRestrictionFunctor k V).obj X ⊗[S k V] M) :
    bimoduleTensorAction k V M X a (x + y) =
      bimoduleTensorAction k V M X a x + bimoduleTensorAction k V M X a y := by
  change a • (show bimoduleTensorObj k V M X from x + y) = _
  exact (bimoduleTensorObj k V M X).isModule.smul_add a x y

@[simp] theorem bimoduleTensorAction_tmul (M : ModuleCat.{u} (S k V))
    (X : ModuleCat.{u} (E k V)) (a : S k V)
    (x : (rightRestrictionFunctor k V).obj X) (m : M) :
    bimoduleTensorAction k V M X a (x ⊗ₜ[S k V] m) =
      (show (rightRestrictionFunctor k V).obj X from
        (leftInclude k V a) • (show X from x)) ⊗ₜ[S k V] m := by
  rfl

noncomputable def bimoduleTensorLinearMap (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y) :
    bimoduleTensorObj k V M X →ₗ[S k V] bimoduleTensorObj k V M Y := by
  let g : ((rightRestrictionFunctor k V).obj X ⊗[S k V] M) →ₗ[S k V]
      ((rightRestrictionFunctor k V).obj Y ⊗[S k V] M) :=
    TensorProduct.map ((rightRestrictionFunctor k V).map f).hom LinearMap.id
  exact
  { toFun := g
    map_add' := g.map_add
    map_smul' := by
      intro a z
      change g (bimoduleTensorAction k V M X a z) =
        bimoduleTensorAction k V M Y a (g z)
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          rw [bimoduleTensorAction_add, map_add, hx, hy, map_add,
            bimoduleTensorAction_add]
      | tmul x m =>
          rw [bimoduleTensorAction_tmul, TensorProduct.map_tmul,
            TensorProduct.map_tmul, bimoduleTensorAction_tmul]
          congr 1
          exact f.hom.map_smul (leftInclude k V a) (show X from x) }

noncomputable def bimoduleTensorMap (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y) :
    bimoduleTensorObj k V M X ⟶ bimoduleTensorObj k V M Y :=
  (ModuleCat.hom_bijective.surjective (bimoduleTensorLinearMap k V M f)).choose

@[simp] theorem bimoduleTensorMap_hom (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y) :
    (bimoduleTensorMap k V M f).hom = bimoduleTensorLinearMap k V M f :=
  (ModuleCat.hom_bijective.surjective (bimoduleTensorLinearMap k V M f)).choose_spec

@[simp] theorem bimoduleTensorMap_tmul (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y)
    (x : (rightRestrictionFunctor k V).obj X) (m : M) :
    (bimoduleTensorMap k V M f).hom
        (show bimoduleTensorObj k V M X from x ⊗ₜ[S k V] m) =
      (show (rightRestrictionFunctor k V).obj Y from f.hom x) ⊗ₜ[S k V] m := by
  rw [bimoduleTensorMap_hom]
  rfl

noncomputable def bimoduleTensorMapApply (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y)
    (z : (rightRestrictionFunctor k V).obj X ⊗[S k V] M) :
    (rightRestrictionFunctor k V).obj Y ⊗[S k V] M :=
  show bimoduleTensorObj k V M Y from
    (bimoduleTensorMap k V M f).hom (show bimoduleTensorObj k V M X from z)

@[simp] theorem bimoduleTensorMapApply_zero (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y) :
    bimoduleTensorMapApply k V M f 0 = 0 := by
  exact map_zero (bimoduleTensorMap k V M f).hom

theorem bimoduleTensorMapApply_add (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y)
    (x y : (rightRestrictionFunctor k V).obj X ⊗[S k V] M) :
    bimoduleTensorMapApply k V M f (x + y) =
      bimoduleTensorMapApply k V M f x + bimoduleTensorMapApply k V M f y := by
  exact map_add (bimoduleTensorMap k V M f).hom x y

@[simp] theorem bimoduleTensorMapApply_tmul (M : ModuleCat.{u} (S k V))
    {X Y : ModuleCat.{u} (E k V)} (f : X ⟶ Y)
    (x : (rightRestrictionFunctor k V).obj X) (m : M) :
    bimoduleTensorMapApply k V M f (x ⊗ₜ[S k V] m) =
      (show (rightRestrictionFunctor k V).obj Y from f.hom x) ⊗ₜ[S k V] m := by
  exact bimoduleTensorMap_tmul k V M f x m

noncomputable def bimoduleTensorFunctor (M : ModuleCat.{u} (S k V)) :
    ModuleCat.{u} (E k V) ⥤ ModuleCat.{u} (S k V) where
  obj := bimoduleTensorObj k V M
  map := bimoduleTensorMap k V M
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change bimoduleTensorMapApply k V M (𝟙 X) z = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [bimoduleTensorMapApply_add, hx, hy]
    | tmul x m => rw [bimoduleTensorMapApply_tmul]; rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change bimoduleTensorMapApply k V M (f ≫ g) z =
      bimoduleTensorMapApply k V M g (bimoduleTensorMapApply k V M f z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [bimoduleTensorMapApply_add, bimoduleTensorMapApply_add,
        bimoduleTensorMapApply_add, hx, hy]
    | tmul x m => rw [bimoduleTensorMapApply_tmul, bimoduleTensorMapApply_tmul,
        bimoduleTensorMapApply_tmul]; rfl

instance (M : ModuleCat.{u} (S k V)) : (bimoduleTensorFunctor k V M).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change bimoduleTensorMapApply k V M (f + g) z =
      bimoduleTensorMapApply k V M f z + bimoduleTensorMapApply k V M g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [bimoduleTensorMapApply_add, bimoduleTensorMapApply_add,
        bimoduleTensorMapApply_add, hx, hy]; abel
    | tmul x m =>
        rw [bimoduleTensorMapApply_tmul, bimoduleTensorMapApply_tmul,
          bimoduleTensorMapApply_tmul]
        change (show (rightRestrictionFunctor k V).obj Y from
            f.hom x + g.hom x) ⊗ₜ[S k V] m = _
        exact TensorProduct.add_tmul _ _ _

noncomputable local instance moduleKOfSObj (M : ModuleCat.{u} (S k V)) : Module k M :=
  Module.compHom M (algebraMap k (S k V))

local instance towerKOfSObj (M : ModuleCat.{u} (S k V)) :
    IsScalarTower k (S k V) M where
  smul_assoc r s m := by
    change ((algebraMap k (S k V) r) * s) • m =
      (algebraMap k (S k V) r) • (s • m)
    rw [mul_smul]

noncomputable def canonicalLiteralTensorFreeEquiv
    (M : ModuleCat.{u} (S k V)) (i : ℕ) :
    (rightRestrictedLiteralTerm k V i ⊗[S k V] M) ≃+
      (S k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
  (TensorProduct.congr (rightRestrictedLiteralTermFreeEquiv k V i)
      (LinearEquiv.refl (S k V) M)).toAddEquiv.trans <|
    (TensorProduct.comm (S k V) (S k V ⊗[k] koszulX k V i) M).toAddEquiv.trans <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k (S k V) (S k V)
        M (koszulX k V i)).toAddEquiv.trans <|
        (TensorProduct.comm k M (koszulX k V i)).toAddEquiv.trans <|
          (TensorProduct.assoc k (S k V) (⋀[k]^i V) M).toAddEquiv

@[simp] theorem canonicalLiteralTensorFreeEquiv_tmul_tmul
    (M : ModuleCat.{u} (S k V)) (i : ℕ)
    (s t : S k V) (x : ⋀[k]^i V) (m : M) :
    canonicalLiteralTensorFreeEquiv k V M i
      ((show rightRestrictedLiteralTerm k V i from
          explicitKoszulTermTmul k V i (s ⊗ₜ[k] x) t) ⊗ₜ[S k V] m) =
      s ⊗ₜ[k] (x ⊗ₜ[k] (t • m)) := by
  simp [canonicalLiteralTensorFreeEquiv]

noncomputable abbrev bimoduleFreeTermObj (i : ℕ) : ModuleCat.{u} (E k V) :=
  ModuleCat.of (E k V) (koszulBimoduleFreeX k V i)

noncomputable def bimoduleFreeTermRightAction (i : ℕ) (a : S k V)
    (z : koszulBimoduleFreeX k V i) : koszulBimoduleFreeX k V i :=
  show (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i) from
    a • (show (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i) from z)

@[simp] theorem bimoduleFreeTermRightAction_zero (i : ℕ) (a : S k V) :
    bimoduleFreeTermRightAction k V i a 0 = 0 := by
  change a • (0 : (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i)) = 0
  exact smul_zero a

theorem bimoduleFreeTermRightAction_add (i : ℕ) (a : S k V)
    (x y : koszulBimoduleFreeX k V i) :
    bimoduleFreeTermRightAction k V i a (x + y) =
      bimoduleFreeTermRightAction k V i a x + bimoduleFreeTermRightAction k V i a y := by
  change a • (show (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i) from
    x + y) = _
  exact ((rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i)).isModule.smul_add a x y

@[simp] theorem bimoduleFreeTermRightAction_tmul_tmul (i : ℕ) (a s t : S k V)
    (x : ⋀[k]^i V) :
    bimoduleFreeTermRightAction k V i a
        (((s ⊗ₜ[k] t : E k V) ⊗ₜ[k] x : koszulBimoduleFreeX k V i)) =
      ((s ⊗ₜ[k] (a * t) : E k V) ⊗ₜ[k] x) := by
  change ((rightInclude k V a) * (s ⊗ₜ[k] t : E k V)) ⊗ₜ[k] x = _
  simp [rightInclude, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

/-- Put the right `SV` coefficient first, so tensoring it with `M` cancels visibly. -/
noncomputable def bimoduleFreeTermRightEquiv (i : ℕ) :
    (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i) ≃ₗ[S k V]
      (S k V ⊗[k] koszulX k V i) := by
  let eₖ : koszulBimoduleFreeX k V i ≃ₗ[k] S k V ⊗[k] koszulX k V i :=
    TensorProduct.congr (Algebra.TensorProduct.comm k (S k V) (S k V)).toLinearEquiv
        (LinearEquiv.refl k (⋀[k]^i V)) ≪≫ₗ
      TensorProduct.assoc k (S k V) (S k V) (⋀[k]^i V)
  exact
  { toFun := eₖ
    invFun := eₖ.symm
    left_inv := eₖ.left_inv
    right_inv := eₖ.right_inv
    map_add' := eₖ.map_add
    map_smul' := by
      intro a z
      change eₖ (bimoduleFreeTermRightAction k V i a z) = a • eₖ z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          rw [bimoduleFreeTermRightAction_add, map_add, hx, hy, map_add, smul_add]
      | tmul e x =>
          induction e using TensorProduct.induction_on with
          | zero => simp
          | add p q hp hq =>
              rw [add_tmul, bimoduleFreeTermRightAction_add, map_add, hp, hq, map_add, smul_add]
          | tmul s t =>
              rw [bimoduleFreeTermRightAction_tmul_tmul]
              simp only [Algebra.TensorProduct.comm_toLinearEquiv, LinearEquiv.trans_apply,
                congr_tmul, comm_tmul, LinearEquiv.refl_apply, assoc_tmul, eₖ]
              rw [TensorProduct.smul_tmul', smul_eq_mul]
  }

noncomputable def canonicalFreeTermTensorEquiv
    (M : ModuleCat.{u} (S k V)) (i : ℕ) :
    (((rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i)) ⊗[S k V] M) ≃+
      (S k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
  (TensorProduct.congr (bimoduleFreeTermRightEquiv k V i)
      (LinearEquiv.refl (S k V) M)).toAddEquiv.trans <|
    (TensorProduct.comm (S k V) (S k V ⊗[k] koszulX k V i) M).toAddEquiv.trans <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k (S k V) (S k V)
        M (koszulX k V i)).toAddEquiv.trans <|
        (TensorProduct.comm k M (koszulX k V i)).toAddEquiv.trans <|
          (TensorProduct.assoc k (S k V) (⋀[k]^i V) M).toAddEquiv

@[simp] theorem canonicalFreeTermTensorEquiv_tmul_tmul
    (M : ModuleCat.{u} (S k V)) (i : ℕ)
    (s t : S k V) (x : ⋀[k]^i V) (m : M) :
    canonicalFreeTermTensorEquiv k V M i
      ((((s ⊗ₜ[k] t : E k V) ⊗ₜ[k] x : koszulBimoduleFreeX k V i) ⊗ₜ[S k V] m)) =
      s ⊗ₜ[k] (x ⊗ₜ[k] (t • m)) := by
  simp [canonicalFreeTermTensorEquiv, bimoduleFreeTermRightEquiv]

noncomputable def bimoduleFreeTermTensorTmul
    (M : ModuleCat.{u} (S k V)) (i : ℕ)
    (q : koszulBimoduleFreeX k V i) (m : M) :
    (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i) ⊗[S k V] M :=
  (show (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i) from q) ⊗ₜ[S k V] m

@[simp] theorem bimoduleFreeTermTensorTmul_zero
    (M : ModuleCat.{u} (S k V)) (i : ℕ) (m : M) :
    bimoduleFreeTermTensorTmul k V M i 0 m = 0 := by
  change (0 : (rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i))
    ⊗ₜ[S k V] m = 0
  exact TensorProduct.zero_tmul
    ((rightRestrictionFunctor k V).obj (bimoduleFreeTermObj k V i)) m

theorem bimoduleFreeTermTensorTmul_add
    (M : ModuleCat.{u} (S k V)) (i : ℕ)
    (p q : koszulBimoduleFreeX k V i) (m : M) :
    bimoduleFreeTermTensorTmul k V M i (p + q) m =
      bimoduleFreeTermTensorTmul k V M i p m +
        bimoduleFreeTermTensorTmul k V M i q m := by
  exact TensorProduct.add_tmul _ _ _

theorem bimoduleTensorAction_free_tmul_tmul
    (M : ModuleCat.{u} (S k V)) (i : ℕ)
    (a s t : S k V) (x : ⋀[k]^i V) (m : M) :
    bimoduleTensorAction k V M (bimoduleFreeTermObj k V i) a
        (bimoduleFreeTermTensorTmul k V M i
          ((s ⊗ₜ[k] t : E k V) ⊗ₜ[k] x) m) =
      bimoduleFreeTermTensorTmul k V M i
        (((a * s) ⊗ₜ[k] t : E k V) ⊗ₜ[k] x) m := by
  unfold bimoduleFreeTermTensorTmul
  rw [bimoduleTensorAction_tmul]
  congr 1
  change ((leftInclude k V a) * (s ⊗ₜ[k] t : E k V)) ⊗ₜ[k] x = _
  simp [leftInclude, Algebra.TensorProduct.tmul_mul_tmul]

/-- The term obtained by tensoring the unsheared free bimodule on the right with
`M` is a free left `SV`-module, with coefficients `⋀ⁱV ⊗ M`. -/
noncomputable def bimoduleFreeTermTensorFreeEquiv
    (M : ModuleCat.{u} (S k V)) (i : ℕ) :
    bimoduleTensorObj k V M (bimoduleFreeTermObj k V i) ≃ₗ[S k V]
      (S k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) := by
  let e := canonicalFreeTermTensorEquiv k V M i
  exact
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := by
      intro a z
      change e (bimoduleTensorAction k V M (bimoduleFreeTermObj k V i) a z) =
        a • e z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add p q hp hq =>
          rw [bimoduleTensorAction_add, map_add, hp, hq, map_add, smul_add]
      | tmul q m =>
          change e (bimoduleTensorAction k V M (bimoduleFreeTermObj k V i) a
            (bimoduleFreeTermTensorTmul k V M i q m)) =
              a • e (bimoduleFreeTermTensorTmul k V M i q m)
          induction q using TensorProduct.induction_on with
          | zero =>
              rw [bimoduleFreeTermTensorTmul_zero, bimoduleTensorAction_zero,
                map_zero]
              exact smul_zero a
          | add p q hp hq =>
              rw [bimoduleFreeTermTensorTmul_add, bimoduleTensorAction_add,
                map_add, hp, hq, map_add, smul_add]
          | tmul r x =>
              induction r using TensorProduct.induction_on with
              | zero =>
                  rw [TensorProduct.zero_tmul, bimoduleFreeTermTensorTmul_zero,
                    bimoduleTensorAction_zero, map_zero]
                  exact smul_zero a
              | add s t hs ht =>
                  rw [TensorProduct.add_tmul, bimoduleFreeTermTensorTmul_add,
                    bimoduleTensorAction_add, map_add, hs, ht, map_add, smul_add]
              | tmul s t =>
                  rw [bimoduleTensorAction_free_tmul_tmul]
                  change canonicalFreeTermTensorEquiv k V M i
                      (bimoduleFreeTermTensorTmul k V M i
                        (((a * s) ⊗ₜ[k] t : E k V) ⊗ₜ[k] x) m) =
                    a • canonicalFreeTermTensorEquiv k V M i
                      (bimoduleFreeTermTensorTmul k V M i
                        ((s ⊗ₜ[k] t : E k V) ⊗ₜ[k] x) m)
                  unfold bimoduleFreeTermTensorTmul
                  rw [
                    canonicalFreeTermTensorEquiv_tmul_tmul,
                    canonicalFreeTermTensorEquiv_tmul_tmul,
                    TensorProduct.smul_tmul', smul_eq_mul] }

/-- The degree-`i` term after tensoring the literal bimodule resolution on the
right with `M`, explicitly identified with `SV ⊗[k] (⋀ⁱV ⊗[k] M)`. -/
noncomputable def tensorBimoduleResolutionTermIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) (i : ℕ) :
    (((bimoduleTensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (koszulBimoduleResolution k V b).complex).X i ≅
      ModuleCat.of (S k V) (S k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
  (bimoduleTensorFunctor k V M).mapIso
      (koszulBimoduleResolutionTermIso k V b i) ≪≫
    (bimoduleTensorFunctor k V M).mapIso
      (koszulBimoduleTermFreeIso k V i) ≪≫
    (bimoduleFreeTermTensorFreeEquiv k V M i).toModuleIso

/-- Tensoring the literal Koszul bimodule resolution with any `SV`-module has
free terms. -/
theorem tensorBimoduleResolutionTerm_free
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) (i : ℕ) :
    Module.Free (S k V)
      ((((bimoduleTensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (koszulBimoduleResolution k V b).complex).X i) := by
  letI : Module.Free k ((⋀[k]^i V) ⊗[k] M) := inferInstance
  letI : Module.Free (S k V) (S k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) := inferInstance
  exact Module.Free.of_equiv
    (tensorBimoduleResolutionTermIso k V b M i).symm.toLinearEquiv

theorem tensorBimoduleResolutionTerm_projective
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) (i : ℕ) :
    Projective
      ((((bimoduleTensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (koszulBimoduleResolution k V b).complex).X i) := by
  letI := tensorBimoduleResolutionTerm_free k V b M i
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis (S k V) _)

/-- The tensor resolution stops in degree `dim V`: its degree-`i` term is a
zero object whenever `dim V < i`. -/
theorem tensorBimoduleResolutionTerm_isZero_of_finrank_lt
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) (i : ℕ)
    (hi : Module.finrank k V < i) :
    IsZero
      ((((bimoduleTensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (koszulBimoduleResolution k V b).complex).X i) := by
  letI : Module.Finite k V := Module.Finite.of_basis b
  have hfin : Module.finrank k (⋀[k]^i V) = 0 := by
    rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hi]
  have hext : ∀ x : ⋀[k]^i V, x = 0 :=
    finrank_zero_iff_forall_zero.mp hfin
  have hinner : ∀ z : (⋀[k]^i V) ⊗[k] M, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul x m => rw [hext x, TensorProduct.zero_tmul]
  have houter : ∀ z : S k V ⊗[k] ((⋀[k]^i V) ⊗[k] M), z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul s x => rw [hinner x, TensorProduct.tmul_zero]
  letI : Subsingleton (S k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
    ⟨fun x y => (houter x).trans (houter y).symm⟩
  exact (tensorBimoduleResolutionTermIso k V b M i).isZero_iff.mpr
    (ModuleCat.isZero_of_subsingleton _)

noncomputable abbrev bimoduleTargetObj : ModuleCat.{u} (E k V) :=
  @ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V)

/-- Forget the retained left action for a moment: tensoring the regular right
`SV`-module with `M` is canonically `M`. -/
noncomputable def canonicalBimoduleTensorTargetEquiv
    (M : ModuleCat.{u} (S k V)) :
    ((rightRestrictionFunctor k V).obj (bimoduleTargetObj k V) ⊗[S k V] M) ≃+ M :=
  (TensorProduct.congr (rightRestrictedBimoduleTargetIso k V).toLinearEquiv
      (LinearEquiv.refl (S k V) M)).toAddEquiv.trans
    (TensorProduct.lid (S k V) M).toAddEquiv

@[simp] theorem rightRestrictedBimoduleTargetIso_hom_apply
    (s : rightRestrictedBimoduleTarget k V) :
    (rightRestrictedBimoduleTargetIso k V).hom.hom s = (show S k V from s) := by
  rfl

@[simp] theorem canonicalBimoduleTensorTargetEquiv_tmul
    (M : ModuleCat.{u} (S k V))
    (s : (rightRestrictionFunctor k V).obj (bimoduleTargetObj k V)) (m : M) :
    canonicalBimoduleTensorTargetEquiv k V M
      (s ⊗ₜ[S k V] m) = (show S k V from s) • m := by
  change (rightRestrictedBimoduleTargetIso k V).hom.hom
      (show rightRestrictedBimoduleTarget k V from s) • m =
    (show S k V from s) • m
  rw [rightRestrictedBimoduleTargetIso_hom_apply]

noncomputable def bimoduleTargetTensorTmul
    (M : ModuleCat.{u} (S k V))
    (s : (rightRestrictionFunctor k V).obj (bimoduleTargetObj k V)) (m : M) :
    (rightRestrictionFunctor k V).obj (bimoduleTargetObj k V) ⊗[S k V] M :=
  s ⊗ₜ[S k V] m

theorem bimoduleTensorAction_target_tmul
    (M : ModuleCat.{u} (S k V)) (a : S k V)
    (s : (rightRestrictionFunctor k V).obj (bimoduleTargetObj k V)) (m : M) :
    bimoduleTensorAction k V M (bimoduleTargetObj k V) a
        (bimoduleTargetTensorTmul k V M s m) =
      bimoduleTargetTensorTmul k V M
        (show (rightRestrictionFunctor k V).obj (bimoduleTargetObj k V) from
          a * (show S k V from s)) m := by
  unfold bimoduleTargetTensorTmul
  rw [bimoduleTensorAction_tmul]
  congr 1
  change bimodAct k V (leftInclude k V a) (show S k V from s) =
    a * (show S k V from s)
  simpa [leftInclude, Algebra.TensorProduct.includeLeft_apply] using
    bimodAct_tmul k V a 1 (show S k V from s)

/-- The canonical cancellation is left `SV`-linear, so it identifies the
tensor of the bimodule target with the original module `M`. -/
noncomputable def bimoduleTensorTargetIso
    (M : ModuleCat.{u} (S k V)) :
    (bimoduleTensorFunctor k V M).obj (bimoduleTargetObj k V) ≅ M := by
  let e := canonicalBimoduleTensorTargetEquiv k V M
  let eₗ : bimoduleTensorObj k V M (bimoduleTargetObj k V) ≃ₗ[S k V] M :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a z
        change e (bimoduleTensorAction k V M (bimoduleTargetObj k V) a z) =
          a • e z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
            rw [bimoduleTensorAction_add, map_add, hx, hy, map_add, smul_add]
        | tmul s m =>
            change e (bimoduleTensorAction k V M (bimoduleTargetObj k V) a
                (bimoduleTargetTensorTmul k V M s m)) =
              a • e (bimoduleTargetTensorTmul k V M s m)
            rw [bimoduleTensorAction_target_tmul]
            change canonicalBimoduleTensorTargetEquiv k V M
                (bimoduleTargetTensorTmul k V M
                  (show (rightRestrictionFunctor k V).obj (bimoduleTargetObj k V) from
                    a * (show S k V from s)) m) =
              a • canonicalBimoduleTensorTargetEquiv k V M
                (bimoduleTargetTensorTmul k V M s m)
            unfold bimoduleTargetTensorTmul
            rw [canonicalBimoduleTensorTargetEquiv_tmul,
              canonicalBimoduleTensorTargetEquiv_tmul, mul_smul] }
  exact eₗ.toModuleIso

noncomputable abbrev ordinaryRightTensorFunctor
    (M : ModuleCat.{u} (S k V)) :
    ModuleCat.{u} (E k V) ⥤ ModuleCat.{u} (S k V) :=
  rightRestrictionFunctor k V ⋙ MonoidalCategory.tensorRight M

/-- After forgetting scalar actions, retained-left tensoring is the ordinary
tensor functor on the right-restricted bimodule. -/
noncomputable def bimoduleTensorForgetIso
    (M : ModuleCat.{u} (S k V)) :
    bimoduleTensorFunctor k V M ⋙
        forget₂ (ModuleCat.{u} (S k V)) AddCommGrpCat.{u} ≅
      ordinaryRightTensorFunctor k V M ⋙
        forget₂ (ModuleCat.{u} (S k V)) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp only [Functor.comp_map, Iso.refl_hom]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change bimoduleTensorMapApply k V M f z =
      (((rightRestrictionFunctor k V).map f) ▷ M).hom z
    induction z using TensorProduct.induction_on with
    | zero => rw [bimoduleTensorMapApply_zero, map_zero]
    | add x y hx hy =>
        rw [bimoduleTensorMapApply_add, map_add, hx, hy]
    | tmul x m =>
        rw [bimoduleTensorMapApply_tmul,
          ModuleCat.MonoidalCategory.whiskerRight_apply]
        rfl)

theorem ordinaryRightTensor_augmentation_quasiIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) :
    QuasiIso
      (((ordinaryRightTensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (koszulBimoduleResolution k V b).π) := by
  let P := koszulBimoduleResolution k V b
  let Q := rightRestrictedBimoduleResolution k V b
  let R := rightRestrictionFunctor k V
  let T := MonoidalCategory.tensorRight M
  let e := (HomologicalComplex.singleMapHomologicalComplex R
    (ComplexShape.down ℕ) 0).app
      (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V))
      ≪≫ (ChainComplex.single₀ (ModuleCat.{u} (S k V))).mapIso
        (rightRestrictedBimoduleTargetIso k V)
  let e' : (ProjectiveResolution.self (regularObj k V)).complex ≅
      (R.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((ChainComplex.single₀ (ModuleCat.{u} (E k V))).obj
          (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V))) := e.symm
  have hQ : Q.π = (Q.homotopyEquiv (ProjectiveResolution.self (regularObj k V))).hom := by
    have h := ProjectiveResolution.homotopyEquiv_hom_π Q
      (ProjectiveResolution.self (regularObj k V))
    change (Q.homotopyEquiv (ProjectiveResolution.self (regularObj k V))).hom ≫
      𝟙 _ = Q.π at h
    rw [Category.comp_id] at h
    exact h.symm
  have hQ_def : Q.π =
      (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫ e'.inv := by
    rfl
  let hraw := (Q.homotopyEquiv (ProjectiveResolution.self (regularObj k V))).trans
    (HomotopyEquiv.ofIso e')
  have hraw_hom : hraw.hom =
      (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π := by
    change (Q.homotopyEquiv (ProjectiveResolution.self (regularObj k V))).hom ≫
      e'.hom = (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
    rw [← hQ, hQ_def]
    change (((R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫ e'.inv) ≫
      e'.hom) = (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change QuasiIso
    ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π))
  rw [← hraw_hom]
  exact (T.mapHomotopyEquiv hraw).quasiIso_hom

theorem bimoduleTensor_augmentation_quasiIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) :
    QuasiIso
      (((bimoduleTensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (koszulBimoduleResolution k V b).π) := by
  let P := koszulBimoduleResolution k V b
  let B := bimoduleTensorFunctor k V M
  let G := ordinaryRightTensorFunctor k V M
  let U := forget₂ (ModuleCat.{u} (S k V)) AddCommGrpCat.{u}
  let η := NatIso.mapHomologicalComplex (bimoduleTensorForgetIso k V M)
    (ComplexShape.down ℕ)
  let φB := (B.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
  let φG := (G.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
  let φU := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map φB
  let φGU := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map φG
  haveI hG : QuasiIso φG := ordinaryRightTensor_augmentation_quasiIso k V b M
  haveI hGU : QuasiIso φGU := inferInstance
  haveI hηP : QuasiIso (η.hom.app P.complex) := inferInstance
  haveI hηS : QuasiIso
      (η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (E k V))).obj
        (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V)))) := inferInstance
  haveI hright : QuasiIso (η.hom.app P.complex ≫ φGU) :=
    quasiIso_comp_explicit _ _ hηP hGU
  have hnat : φU ≫
      η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (E k V))).obj
        (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V))) =
      η.hom.app P.complex ≫ φGU := by
    exact NatTrans.mapHomologicalComplex_naturality
      (bimoduleTensorForgetIso k V M).hom P.π
  haveI hcomp : QuasiIso
      (φU ≫ η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (E k V))).obj
        (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V)))) :=
    hnat ▸ hright
  haveI hU : QuasiIso φU := quasiIso_of_comp_right_explicit φU
    (η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (E k V))).obj
      (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V)))) hηS hcomp
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology φB U).mp hU

/-- **The book's Hilbert-syzygy resolution.** Tensor the literal free Koszul
bimodule resolution over its right `SV` action with the arbitrary module `M`,
retaining the left action. -/
noncomputable def tensorBimoduleResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) : ProjectiveResolution M where
  complex := ((bimoduleTensorFunctor k V M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (koszulBimoduleResolution k V b).complex
  projective i := tensorBimoduleResolutionTerm_projective k V b M i
  π := ((bimoduleTensorFunctor k V M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (koszulBimoduleResolution k V b).π ≫
    (HomologicalComplex.singleMapHomologicalComplex (bimoduleTensorFunctor k V M)
      (ComplexShape.down ℕ) 0).hom.app (bimoduleTargetObj k V) ≫
    (ChainComplex.single₀ (ModuleCat.{u} (S k V))).map
      (bimoduleTensorTargetIso k V M).hom
  quasiIso := by
    let φ := ((bimoduleTensorFunctor k V M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (koszulBimoduleResolution k V b).π
    let e₁ := (HomologicalComplex.singleMapHomologicalComplex
      (bimoduleTensorFunctor k V M) (ComplexShape.down ℕ) 0).app
        (bimoduleTargetObj k V)
    let e₂ := (ChainComplex.single₀ (ModuleCat.{u} (S k V))).mapIso
      (bimoduleTensorTargetIso k V M)
    haveI : QuasiIso φ := bimoduleTensor_augmentation_quasiIso k V b M
    haveI : QuasiIso (φ ≫ e₁.hom) := quasiIso_comp_iso φ e₁
    change QuasiIso (φ ≫ e₁.hom ≫ e₂.hom)
    exact quasiIso_comp_iso (φ ≫ e₁.hom) e₂

theorem tensorBimoduleResolution_isZero_of_finrank_lt
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (S k V)) (i : ℕ)
    (hi : Module.finrank k V < i) :
    IsZero ((tensorBimoduleResolution k V b M).complex.X i) :=
  tensorBimoduleResolutionTerm_isZero_of_finrank_lt k V b M i hi

/-- **Problem 8.2.10(iv), literal resolution.** For finite-dimensional `V`,
the Koszul bimodule construction gives every `SV`-module a projective
resolution whose degree-`i` term is explicitly
`SV ⊗[k] (⋀ⁱV ⊗[k] M)`. -/
noncomputable def Problem_8_2_10_iv_resolution [FiniteDimensional k V]
    (M : ModuleCat.{u} (S k V)) : ProjectiveResolution M :=
  tensorBimoduleResolution k V (Module.finBasis k V) M

/-- The book-specific projective resolution is zero in every degree strictly
above `dim V`. Together with the public `Ext` and `Tor` endpoints in
`Problem8_2_10_HilbertSyzygy`, this is the literal Hilbert-syzygy witness. -/
theorem Problem_8_2_10_iv_resolution_isZero [FiniteDimensional k V]
    (M : ModuleCat.{u} (S k V)) (i : ℕ) (hi : Module.finrank k V < i) :
    IsZero ((Problem_8_2_10_iv_resolution k V M).complex.X i) :=
  tensorBimoduleResolution_isZero_of_finrank_lt k V
    (Module.finBasis k V) M i hi

end Etingof
