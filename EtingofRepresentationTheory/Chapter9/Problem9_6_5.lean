import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Problem 9.6.5: the explicit balanced tensor quasi-inverse

For a progenerator `P` and `B = (End P)ᵐᵒᵖ`, this file defines

* the basis-independent finite copower `P ⊗ₖ V`, characterized by
  `Hom(P ⊗ₖ V, Y) ≃ (V →ₗ[k] Hom(P,Y))`;
* the two action maps and their difference
  `balancedRelation P X : P ⊗ₖ (B ⊗ₖ X) ⟶ P ⊗ₖ X`;
* `balancedTensor P X = cokernel (balancedRelation P X)` and the functor
  `balancedTensorFunctor P : FGModuleCat B ⥤ C`;
* the unit `X ⟶ Hom(P, P ⊗_B X)` and evaluation
  `P ⊗_B Hom(P,Y) ⟶ Y`.

The last section proves the three parts of Problem 9.6.5 separately.  In particular, the
proof of the counit being an isomorphism records the kernel argument from the book.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Etingof.Problem965

-- The finite copowers below unfold through chosen biproducts, while the module structures
-- on restricted `B`-modules follow a separate reducibility path from the native hom modules.
set_option backward.isDefEq.respectTransparency false

/-! ## Finite copowers in a finite linear abelian category -/

section Copower

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Etingof.IsFiniteAbelianCategory C] [Linear k C]

/-- A concrete choice of the finite copower `P ⊗ₖ V`.  Although the object uses
`Module.finBasis`, `finiteCopowerHomEquiv` below gives its basis-independent universal
property. -/
noncomputable def finiteCopower (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] : C :=
  ⨁ fun _ : Fin (Module.finrank k V) => P

/-- The universal linear insertion `V → Hom(P, P ⊗ₖ V)`. -/
noncomputable def finiteCopowerι (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] :
    V →ₗ[k] (P ⟶ finiteCopower (k := k) P V) where
  toFun x := biproduct.lift fun i =>
    ((Module.finBasis k V).repr x i) • 𝟙 P
  map_add' x y := by
    apply biproduct.hom_ext
    intro i
    rw [Preadditive.add_comp, biproduct.lift_π, biproduct.lift_π]
    simp [add_smul]
  map_smul' r x := by
    apply biproduct.hom_ext
    intro i
    rw [Linear.smul_comp, biproduct.lift_π]
    simp [mul_smul]

@[simp]
theorem finiteCopowerι_comp_π (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (x : V) (i : Fin (Module.finrank k V)) :
    finiteCopowerι (k := k) P V x ≫ biproduct.π (fun _ : Fin (Module.finrank k V) => P) i =
      ((Module.finBasis k V).repr x i) • 𝟙 P := by
  change (biproduct.lift fun j =>
    ((Module.finBasis k V).repr x j) • 𝟙 P) ≫
      biproduct.π (fun _ : Fin (Module.finrank k V) => P) i = _
  simp

@[simp]
theorem finiteCopowerι_basis (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (i : Fin (Module.finrank k V)) :
    finiteCopowerι (k := k) P V (Module.finBasis k V i) =
      biproduct.ι (fun _ : Fin (Module.finrank k V) => P) i := by
  classical
  change (biproduct.lift fun j =>
    ((Module.finBasis k V).repr (Module.finBasis k V i) j) • 𝟙 P) = _
  apply biproduct.hom_ext
  intro j
  by_cases h : i = j <;> simp [h]

/-- The morphism out of a finite copower induced by a linear family of morphisms. -/
noncomputable def finiteCopowerDesc (P : C) {V : Type v} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {Y : C} (f : V →ₗ[k] (P ⟶ Y)) :
    finiteCopower (k := k) P V ⟶ Y :=
  biproduct.desc fun i => f (Module.finBasis k V i)

@[simp, reassoc]
theorem finiteCopowerι_desc (P : C) {V : Type v} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {Y : C} (f : V →ₗ[k] (P ⟶ Y)) (x : V) :
    finiteCopowerι (k := k) P V x ≫ finiteCopowerDesc (k := k) P f = f x := by
  let g : V →ₗ[k] (P ⟶ Y) := {
    toFun := fun y => finiteCopowerι (k := k) P V y ≫ finiteCopowerDesc (k := k) P f
    map_add' := fun y z => by simp
    map_smul' := fun r y => by simp }
  have hg : g = f := by
    apply (Module.finBasis k V).ext
    intro i
    change finiteCopowerι (k := k) P V (Module.finBasis k V i) ≫
      finiteCopowerDesc (k := k) P f = f (Module.finBasis k V i)
    rw [finiteCopowerι_basis]
    simp [finiteCopowerDesc]
  exact LinearMap.congr_fun hg x

/-- Morphisms out of `P ⊗ₖ V` are naturally linear families of morphisms out of `P`.
This universal property makes the construction independent of the chosen finite basis. -/
noncomputable def finiteCopowerHomEquiv (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (Y : C) :
    (finiteCopower (k := k) P V ⟶ Y) ≃ₗ[k] (V →ₗ[k] (P ⟶ Y)) where
  toFun f := {
    toFun := fun x => finiteCopowerι (k := k) P V x ≫ f
    map_add' := fun x y => by simp
    map_smul' := fun r x => by simp }
  invFun := finiteCopowerDesc (k := k) P
  left_inv f := by
    apply biproduct.hom_ext'
    intro i
    change biproduct.ι (fun _ : Fin (Module.finrank k V) => P) i ≫
      biproduct.desc (fun j =>
        finiteCopowerι (k := k) P V (Module.finBasis k V j) ≫ f) = _
    rw [biproduct.ι_desc, finiteCopowerι_basis]
  right_inv f := by
    ext x
    exact finiteCopowerι_desc (k := k) P f x
  map_add' f g := by
    ext x
    simp
  map_smul' r f := by
    ext x
    simp

/-- Extensionality for maps out of a finite copower. -/
theorem finiteCopower_hom_ext (P : C) {V : Type v} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {Y : C} {f g : finiteCopower (k := k) P V ⟶ Y}
    (h : ∀ x, finiteCopowerι (k := k) P V x ≫ f =
      finiteCopowerι (k := k) P V x ≫ g) : f = g := by
  exact (finiteCopowerHomEquiv (k := k) P V Y).injective (LinearMap.ext h)

/-- Functoriality of the finite copower in the vector-space variable. -/
noncomputable def finiteCopowerMap (P : C) {V W : Type v}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (f : V →ₗ[k] W) : finiteCopower (k := k) P V ⟶ finiteCopower (k := k) P W :=
  finiteCopowerDesc (k := k) P ((finiteCopowerι (k := k) P W).comp f)

@[simp, reassoc]
theorem finiteCopowerι_map (P : C) {V W : Type v}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (f : V →ₗ[k] W) (x : V) :
    finiteCopowerι (k := k) P V x ≫ finiteCopowerMap (k := k) P f =
      finiteCopowerι (k := k) P W (f x) := by
  exact finiteCopowerι_desc (k := k) P _ x

@[simp]
theorem finiteCopowerMap_id (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] :
    finiteCopowerMap (k := k) P (LinearMap.id : V →ₗ[k] V) = 𝟙 _ := by
  apply finiteCopower_hom_ext (k := k) P
  intro x
  rw [finiteCopowerι_map]
  simp

@[reassoc]
theorem finiteCopowerMap_comp (P : C) {U V W : Type v}
    [AddCommGroup U] [Module k U] [Module.Finite k U]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) :
    finiteCopowerMap (k := k) P (g.comp f) =
      finiteCopowerMap (k := k) P f ≫ finiteCopowerMap (k := k) P g := by
  apply finiteCopower_hom_ext (k := k) P
  intro x
  calc
    finiteCopowerι (k := k) P U x ≫ finiteCopowerMap (k := k) P (g.comp f) =
        finiteCopowerι (k := k) P W ((g.comp f) x) := finiteCopowerι_map P _ _
    _ = finiteCopowerι (k := k) P W (g (f x)) := rfl
    _ = finiteCopowerι (k := k) P V (f x) ≫ finiteCopowerMap (k := k) P g :=
      (finiteCopowerι_map P g (f x)).symm
    _ = (finiteCopowerι (k := k) P U x ≫ finiteCopowerMap (k := k) P f) ≫
        finiteCopowerMap (k := k) P g :=
      congrArg (fun h : P ⟶ finiteCopower (k := k) P V =>
        h ≫ finiteCopowerMap (k := k) P g) (finiteCopowerι_map P f x).symm
    _ = _ := Category.assoc _ _ _

end Copower

/-! ## The balanced relation and its cokernel -/

section BalancedTensor

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Etingof.IsFiniteAbelianCategory C] [Linear k C]
  [Etingof.IsFiniteAbelianCategoryOverField k C]

/-- The algebra used in Morita reconstruction. -/
abbrev endOp (P : C) := (End P)ᵐᵒᵖ

noncomputable local instance endFiniteDimensional (P : C) : FiniteDimensional k (End P) :=
  Etingof.IsFiniteAbelianCategoryOverField.finiteDimensional_hom P P

noncomputable local instance fgModuleModule (P : C) (X : FGModuleCat.{v} (endOp P)) :
    Module k X :=
  Module.compHom X (algebraMap k (endOp P))

local instance fgModuleTower (P : C) (X : FGModuleCat.{v} (endOp P)) :
    IsScalarTower k (endOp P) X where
  smul_assoc a b x := by
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

local instance fgModuleComm (P : C) (X : FGModuleCat.{v} (endOp P)) :
    SMulCommClass (endOp P) k X where
  smul_comm b a x := by
    change b • ((algebraMap k (endOp P) a) • x) =
      (algebraMap k (endOp P) a) • (b • x)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

noncomputable local instance fgModuleFiniteDimensional
    (P : C) (X : FGModuleCat.{v} (endOp P)) :
    FiniteDimensional k X :=
  Module.Finite.trans (endOp P) X

/-- The right `B = (End P)ᵐᵒᵖ` action on `P`, written as a morphism
`P ⊗ₖ B ⟶ P`. -/
noncomputable def rightAction (P : C) :
    finiteCopower (k := k) P (endOp P) ⟶ P :=
  finiteCopowerDesc (k := k) P
    (MulOpposite.opLinearEquiv k : End P ≃ₗ[k] endOp P).symm.toLinearMap

@[simp, reassoc]
theorem finiteCopowerι_rightAction (P : C) (b : endOp P) :
    finiteCopowerι (k := k) P (endOp P) b ≫ rightAction (k := k) P = b.unop := by
  exact finiteCopowerι_desc (k := k) P _ b

/-- The underlying `k`-linear left action `B ⊗ₖ X → X` of a finite `B`-module. -/
noncomputable def leftAction (P : C) (X : FGModuleCat.{v} (endOp P)) :
    TensorProduct k (endOp P) X →ₗ[k] X :=
  TensorProduct.lift (Algebra.lsmul k k X).toLinearMap

omit [Etingof.IsFiniteAbelianCategoryOverField k C] in
@[simp]
theorem leftAction_tmul (P : C) (X : FGModuleCat.{v} (endOp P))
    (b : endOp P) (x : X) :
    leftAction (k := k) P X (b ⊗ₜ[k] x) = b • x := by
  simp [leftAction, Algebra.lsmul_apply]

/-- `a_P ⊗ Id`: on a pure tensor `b ⊗ x`, act by `b` on the `P` factor and
insert `x` in the finite copower. -/
noncomputable def rightActionTensor (P : C) (X : FGModuleCat.{v} (endOp P)) :
    finiteCopower (k := k) P (TensorProduct k (endOp P) X) ⟶
      finiteCopower (k := k) P X :=
  finiteCopowerDesc (k := k) P (TensorProduct.lift {
    toFun := fun b => {
      toFun := fun x => b.unop ≫ finiteCopowerι (k := k) P X x
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
    map_add' := fun b c => by
      ext x
      change (b.unop + c.unop) ≫ finiteCopowerι (k := k) P X x = _
      exact Preadditive.add_comp P P (finiteCopower (k := k) P X) b.unop c.unop
        (finiteCopowerι (k := k) P X x)
    map_smul' := fun r b => by
      ext x
      change (r • b.unop) ≫ finiteCopowerι (k := k) P X x = _
      exact Linear.smul_comp P P (finiteCopower (k := k) P X) r b.unop
        (finiteCopowerι (k := k) P X x) })

@[simp, reassoc]
theorem finiteCopowerι_rightActionTensor_tmul (P : C)
    (X : FGModuleCat.{v} (endOp P)) (b : endOp P) (x : X) :
    finiteCopowerι (k := k) P (TensorProduct k (endOp P) X) (b ⊗ₜ[k] x) ≫
      rightActionTensor (k := k) P X =
        b.unop ≫ finiteCopowerι (k := k) P X x := by
  simp [rightActionTensor]

/-- `Id ⊗ a_X`, expressed using functoriality of the finite copower. -/
noncomputable def idTensorLeftAction (P : C) (X : FGModuleCat.{v} (endOp P)) :
    finiteCopower (k := k) P (TensorProduct k (endOp P) X) ⟶
      finiteCopower (k := k) P X :=
  finiteCopowerMap (k := k) P (leftAction (k := k) P X)

@[simp, reassoc]
theorem finiteCopowerι_idTensorLeftAction_tmul (P : C)
    (X : FGModuleCat.{v} (endOp P)) (b : endOp P) (x : X) :
    finiteCopowerι (k := k) P (TensorProduct k (endOp P) X) (b ⊗ₜ[k] x) ≫
      idTensorLeftAction (k := k) P X =
        finiteCopowerι (k := k) P X (b • x) := by
  simp [idTensorLeftAction]

/-- The book's morphism
`ψ_X = a_P ⊗ Id - Id ⊗ a_X : P ⊗ₖ B ⊗ₖ X ⟶ P ⊗ₖ X`. -/
noncomputable def balancedRelation (P : C) (X : FGModuleCat.{v} (endOp P)) :
    finiteCopower (k := k) P (TensorProduct k (endOp P) X) ⟶
      finiteCopower (k := k) P X :=
  rightActionTensor (k := k) P X - idTensorLeftAction (k := k) P X

@[simp, reassoc]
theorem finiteCopowerι_balancedRelation_tmul (P : C)
    (X : FGModuleCat.{v} (endOp P)) (b : endOp P) (x : X) :
    finiteCopowerι (k := k) P (TensorProduct k (endOp P) X) (b ⊗ₜ[k] x) ≫
      balancedRelation (k := k) P X =
        b.unop ≫ finiteCopowerι (k := k) P X x -
          finiteCopowerι (k := k) P X (b • x) := by
  simp [balancedRelation, Preadditive.comp_sub]

/-- The underlying `k`-linear map of a morphism of finite `B`-modules. -/
noncomputable def moduleHomRestrict (P : C) {X Y : FGModuleCat.{v} (endOp P)} (f : X ⟶ Y) :
    X →ₗ[k] Y where
  toFun := f
  map_add' := f.hom.hom.map_add
  map_smul' r x := by
    change f ((algebraMap k (endOp P) r) • x) =
      (algebraMap k (endOp P) r) • f x
    exact f.hom.hom.map_smul _ _

omit [Etingof.IsFiniteAbelianCategoryOverField k C] in
@[simp]
theorem moduleHomRestrict_apply (P : C) {X Y : FGModuleCat.{v} (endOp P)} (f : X ⟶ Y)
    (x : X) : moduleHomRestrict (k := k) P f x = f x := rfl

omit [Etingof.IsFiniteAbelianCategoryOverField k C] in
@[simp]
theorem moduleHomRestrict_id (P : C) (X : FGModuleCat.{v} (endOp P)) :
    moduleHomRestrict (k := k) P (𝟙 X) = LinearMap.id := by
  ext x
  rfl

omit [Etingof.IsFiniteAbelianCategoryOverField k C] in
@[simp]
theorem moduleHomRestrict_comp (P : C) {X Y Z : FGModuleCat.{v} (endOp P)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleHomRestrict (k := k) P (f ≫ g) =
      (moduleHomRestrict (k := k) P g).comp (moduleHomRestrict (k := k) P f) := by
  ext x
  rfl

/-- The map `B ⊗ₖ X → B ⊗ₖ Y` induced by a `B`-linear map `X → Y`. -/
noncomputable def tensorModuleHom (P : C) {X Y : FGModuleCat.{v} (endOp P)} (f : X ⟶ Y) :
    TensorProduct k (endOp P) X →ₗ[k] TensorProduct k (endOp P) Y :=
  TensorProduct.map LinearMap.id (moduleHomRestrict (k := k) P f)

omit [Etingof.IsFiniteAbelianCategoryOverField k C] in
@[simp]
theorem tensorModuleHom_tmul (P : C) {X Y : FGModuleCat.{v} (endOp P)} (f : X ⟶ Y)
    (b : endOp P) (x : X) :
    tensorModuleHom (k := k) P f (b ⊗ₜ[k] x) = b ⊗ₜ[k] f x := by
  simp [tensorModuleHom, moduleHomRestrict]

/-- Naturality of the balanced relation. -/
theorem balancedRelation_naturality (P : C) {X Y : FGModuleCat.{v} (endOp P)} (f : X ⟶ Y) :
    balancedRelation (k := k) P X ≫
        finiteCopowerMap (k := k) P (moduleHomRestrict (k := k) P f) =
      finiteCopowerMap (k := k) P (tensorModuleHom (k := k) P f) ≫
        balancedRelation (k := k) P Y := by
  apply finiteCopower_hom_ext (k := k) P
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
      rw [← Category.assoc, ← Category.assoc]
      calc
        (finiteCopowerι (k := k) P (TensorProduct k (endOp P) X) (b ⊗ₜ[k] x) ≫
            balancedRelation (k := k) P X) ≫
              finiteCopowerMap (k := k) P (moduleHomRestrict (k := k) P f) =
            (b.unop ≫ finiteCopowerι (k := k) P X x -
              finiteCopowerι (k := k) P X (b • x)) ≫
                finiteCopowerMap (k := k) P (moduleHomRestrict (k := k) P f) := by
                  rw [finiteCopowerι_balancedRelation_tmul]
        _ = b.unop ≫ finiteCopowerι (k := k) P Y (f x) -
              finiteCopowerι (k := k) P Y (f (b • x)) := by
                rw [Preadditive.sub_comp, Category.assoc, finiteCopowerι_map,
                  finiteCopowerι_map]
                rfl
        _ = b.unop ≫ finiteCopowerι (k := k) P Y (f x) -
              finiteCopowerι (k := k) P Y (b • f x) := by
                congr 2
                exact f.hom.hom.map_smul b x
        _ = finiteCopowerι (k := k) P (TensorProduct k (endOp P) Y)
              (b ⊗ₜ[k] f x) ≫ balancedRelation (k := k) P Y :=
                (finiteCopowerι_balancedRelation_tmul (k := k) P Y b (f x)).symm
        _ = (finiteCopowerι (k := k) P (TensorProduct k (endOp P) X) (b ⊗ₜ[k] x) ≫
              finiteCopowerMap (k := k) P (tensorModuleHom (k := k) P f)) ≫
                balancedRelation (k := k) P Y := by
                  rw [finiteCopowerι_map, tensorModuleHom_tmul]
  | add z z' hz hz' =>
      simp only [map_add, Preadditive.add_comp]
      rw [hz, hz']

/-- The explicit object `P ⊗_B X`, defined as the cokernel of `ψ_X`. -/
noncomputable def balancedTensor (P : C) (X : FGModuleCat.{v} (endOp P)) : C :=
  cokernel (balancedRelation (k := k) P X)

/-- The quotient map `P ⊗ₖ X ⟶ P ⊗_B X`. -/
noncomputable def balancedTensorπ (P : C) (X : FGModuleCat.{v} (endOp P)) :
    finiteCopower (k := k) P X ⟶ balancedTensor (k := k) P X :=
  cokernel.π (balancedRelation (k := k) P X)

noncomputable instance balancedTensorπ_epi (P : C) (X : FGModuleCat.{v} (endOp P)) :
    Epi (balancedTensorπ (k := k) P X) := by
  dsimp [balancedTensorπ]
  infer_instance

@[reassoc (attr := simp)]
theorem balancedRelation_π (P : C) (X : FGModuleCat.{v} (endOp P)) :
    balancedRelation (k := k) P X ≫ balancedTensorπ (k := k) P X = 0 :=
  cokernel.condition _

/-- The morphism `P ⊗_B X ⟶ P ⊗_B Y` induced by a `B`-linear map `X ⟶ Y`. -/
noncomputable def balancedTensorMap (P : C) {X Y : FGModuleCat.{v} (endOp P)} (f : X ⟶ Y) :
    balancedTensor (k := k) P X ⟶ balancedTensor (k := k) P Y :=
  cokernel.desc (balancedRelation (k := k) P X)
    (finiteCopowerMap (k := k) P (moduleHomRestrict (k := k) P f) ≫
      balancedTensorπ (k := k) P Y) (by
        rw [← Category.assoc, balancedRelation_naturality, Category.assoc,
          balancedRelation_π, comp_zero])

@[reassoc (attr := simp)]
theorem balancedTensorπ_map (P : C) {X Y : FGModuleCat.{v} (endOp P)} (f : X ⟶ Y) :
    balancedTensorπ (k := k) P X ≫ balancedTensorMap (k := k) P f =
      finiteCopowerMap (k := k) P (moduleHomRestrict (k := k) P f) ≫
        balancedTensorπ (k := k) P Y :=
  cokernel.π_desc _ _ _

/-- The balanced tensor functor `P ⊗_B -`. -/
noncomputable def balancedTensorFunctor (P : C) : FGModuleCat.{v} (endOp P) ⥤ C where
  obj X := balancedTensor (k := k) P X
  map f := balancedTensorMap (k := k) P f
  map_id X := by
    apply (cancel_epi (balancedTensorπ (k := k) P X)).1
    rw [balancedTensorπ_map, moduleHomRestrict_id, finiteCopowerMap_id,
      Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (balancedTensorπ (k := k) P _)).1
    rw [balancedTensorπ_map, ← Category.assoc, balancedTensorπ_map, Category.assoc,
      balancedTensorπ_map, moduleHomRestrict_comp, finiteCopowerMap_comp]
    exact Category.assoc _ _ _

end BalancedTensor

-- Keep the restriction-of-scalars instances available for the remaining construction while
-- preventing them from participating in instance search for downstream importers.
attribute [local instance] endFiniteDimensional fgModuleModule fgModuleTower fgModuleComm
  fgModuleFiniteDimensional

/-! ## Part (i): `Hom(P, P ⊗_B X) ≅ X` -/

section Unit

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Etingof.IsFiniteAbelianCategory C] [Linear k C]
  [Etingof.IsFiniteAbelianCategoryOverField k C]
variable {P : C} [hp : Etingof.IsProgenerator P]

omit [Etingof.IsFiniteAbelianCategoryOverField k C] hp in
theorem endOp_algebraMap_unop (r : k) :
    (algebraMap k (endOp P) r).unop = r • 𝟙 P := by
  rfl

/-- Contract a map `P ⟶ P ⊗ₖ X` by applying each endomorphism coefficient to the
corresponding basis vector of `X`. -/
noncomputable def collapse (X : FGModuleCat.{v} (endOp P)) :
    (P ⟶ finiteCopower (k := k) P X) →ₗ[endOp P] X where
  toFun g := ∑ i : Fin (Module.finrank k X),
    (MulOpposite.op (g ≫ biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) :
      endOp P) • Module.finBasis k X i
  map_add' g h := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Preadditive.add_comp]
    change (MulOpposite.op ((g ≫ biproduct.π
        (fun _ : Fin (Module.finrank k X) => P) i) +
          (h ≫ biproduct.π (fun _ : Fin (Module.finrank k X) => P) i)) : endOp P) •
            Module.finBasis k X i = _
    rw [MulOpposite.op_add, add_smul]
  map_smul' b g := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (MulOpposite.op ((b.unop ≫ g) ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : endOp P) •
          Module.finBasis k X i =
      b • ((MulOpposite.op (g ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : endOp P) •
          Module.finBasis k X i)
    rw [smul_smul]
    congr 1
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_mul]
    exact Category.assoc _ _ _

omit hp in
@[simp]
theorem collapse_finiteCopowerι (X : FGModuleCat.{v} (endOp P)) (x : X) :
    collapse (k := k) (P := P) X (finiteCopowerι (k := k) P X x) = x := by
  classical
  unfold collapse
  change (∑ i : Fin (Module.finrank k X),
    (MulOpposite.op ((biproduct.lift fun j =>
      ((Module.finBasis k X).repr x j) • 𝟙 P) ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : endOp P) •
          Module.finBasis k X i) = x
  simp_rw [biproduct.lift_π]
  have hop (r : k) : MulOpposite.op (r • 𝟙 P) = algebraMap k (endOp P) r := by
    apply MulOpposite.unop_injective
    rw [endOp_algebraMap_unop]
    rfl
  simp_rw [hop]
  exact (Module.finBasis k X).sum_repr x

omit hp in
/-- `collapse` kills the balanced relation on every universal insertion. -/
theorem collapse_balancedRelation_ι (X : FGModuleCat.{v} (endOp P))
    (z : TensorProduct k (endOp P) X) :
    collapse (k := k) (P := P) X
      (finiteCopowerι (k := k) P (TensorProduct k (endOp P) X) z ≫
        balancedRelation (k := k) P X) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
      rw [finiteCopowerι_balancedRelation_tmul]
      change collapse (k := k) (P := P) X
        (b • finiteCopowerι (k := k) P X x -
          finiteCopowerι (k := k) P X (b • x)) = 0
      rw [map_sub, map_smul, collapse_finiteCopowerι, collapse_finiteCopowerι, sub_self]
  | add z z' hz hz' =>
      rw [map_add, Preadditive.add_comp, map_add, hz, hz', add_zero]

omit hp in
/-- `collapse` kills every map which factors through `ψ_X`. -/
theorem collapse_comp_balancedRelation (X : FGModuleCat.{v} (endOp P))
    (h : P ⟶ finiteCopower (k := k) P (TensorProduct k (endOp P) X)) :
    collapse (k := k) (P := P) X (h ≫ balancedRelation (k := k) P X) = 0 := by
  let I := Fin (Module.finrank k (TensorProduct k (endOp P) X))
  let Q := fun _ : I => P
  have hh : h = ∑ i : I,
      (h ≫ biproduct.π Q i) ≫ biproduct.ι Q i := by
    have htotal : (∑ i : I, biproduct.π Q i ≫ biproduct.ι Q i) =
        𝟙 (finiteCopower (k := k) P (TensorProduct k (endOp P) X)) := biproduct.total
    calc
      h = h ≫ 𝟙 _ := (Category.comp_id h).symm
      _ = h ≫ ∑ i : I, biproduct.π Q i ≫ biproduct.ι Q i := by rw [htotal]
      _ = _ := by rw [Preadditive.comp_sum]; simp only [Category.assoc]
  rw [hh, Preadditive.sum_comp, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Category.assoc]
  change collapse (k := k) (P := P) X
      ((MulOpposite.op (h ≫ biproduct.π Q i) : endOp P) •
        (biproduct.ι Q i ≫ balancedRelation (k := k) P X)) = 0
  rw [map_smul]
  rw [← finiteCopowerι_basis (k := k) P (TensorProduct k (endOp P) X) i]
  rw [collapse_balancedRelation_ι, smul_zero]

/-- An explicit preimage under `ψ_X` of
`g - (1_P ⊗ collapse(g))`. -/
noncomputable def relationLift (X : FGModuleCat.{v} (endOp P))
    (g : P ⟶ finiteCopower (k := k) P X) :
    P ⟶ finiteCopower (k := k) P (TensorProduct k (endOp P) X) :=
  ∑ i : Fin (Module.finrank k X),
    finiteCopowerι (k := k) P (TensorProduct k (endOp P) X)
      ((MulOpposite.op (g ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : endOp P) ⊗ₜ[k]
          Module.finBasis k X i)

omit hp in
theorem relationLift_comp_balancedRelation (X : FGModuleCat.{v} (endOp P))
    (g : P ⟶ finiteCopower (k := k) P X) :
    relationLift (k := k) (P := P) X g ≫ balancedRelation (k := k) P X =
      g - finiteCopowerι (k := k) P X (collapse (k := k) (P := P) X g) := by
  classical
  unfold relationLift
  rw [Preadditive.sum_comp]
  simp_rw [finiteCopowerι_balancedRelation_tmul]
  rw [Finset.sum_sub_distrib]
  simp_rw [MulOpposite.unop_op, finiteCopowerι_basis]
  have hfirst : (∑ i : Fin (Module.finrank k X),
      (g ≫ biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) ≫
        biproduct.ι (fun _ : Fin (Module.finrank k X) => P) i) = g := by
    have htotal : (∑ i : Fin (Module.finrank k X),
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i ≫
          biproduct.ι (fun _ : Fin (Module.finrank k X) => P) i) =
        𝟙 (finiteCopower (k := k) P X) := biproduct.total
    calc
      _ = g ≫ ∑ i : Fin (Module.finrank k X),
          biproduct.π (fun _ : Fin (Module.finrank k X) => P) i ≫
            biproduct.ι (fun _ : Fin (Module.finrank k X) => P) i := by
              rw [Preadditive.comp_sum]
              simp only [Category.assoc]
      _ = g ≫ 𝟙 _ := by rw [htotal]
      _ = g := Category.comp_id g
  rw [hfirst]
  congr 1
  change (∑ i : Fin (Module.finrank k X),
      finiteCopowerι (k := k) P X
        ((MulOpposite.op (g ≫
          biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : endOp P) •
            Module.finBasis k X i)) =
    finiteCopowerι (k := k) P X
      (∑ i : Fin (Module.finrank k X),
        (MulOpposite.op (g ≫
          biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : endOp P) •
            Module.finBasis k X i)
  exact (map_sum (finiteCopowerι (k := k) P X) _ _).symm

/-- A map into `P ⊗ₖ X` killed by the quotient map factors through `ψ_X`.
This is the abelian image/kernel step used in the book. -/
theorem exists_factor_balancedRelation (X : FGModuleCat.{v} (endOp P))
    (g : P ⟶ finiteCopower (k := k) P X)
    (hg : g ≫ balancedTensorπ (k := k) P X = 0) :
    ∃ h : P ⟶ finiteCopower (k := k) P (TensorProduct k (endOp P) X),
      h ≫ balancedRelation (k := k) P X = g := by
  haveI : Projective P := hp.toProjective
  let gLift := kernel.lift (balancedTensorπ (k := k) P X) g hg
  let h := Projective.factorThru gLift
    (Abelian.factorThruImage (balancedRelation (k := k) P X))
  refine ⟨h, ?_⟩
  have h₁ := Projective.factorThru_comp gLift
    (Abelian.factorThruImage (balancedRelation (k := k) P X))
  have h₂ := Abelian.image.fac (balancedRelation (k := k) P X)
  calc
    h ≫ balancedRelation (k := k) P X =
        h ≫ (Abelian.factorThruImage (balancedRelation (k := k) P X) ≫
          Abelian.image.ι (balancedRelation (k := k) P X)) := by rw [h₂]
    _ = (h ≫ Abelian.factorThruImage (balancedRelation (k := k) P X)) ≫
          Abelian.image.ι (balancedRelation (k := k) P X) := by rw [Category.assoc]
    _ = gLift ≫ Abelian.image.ι (balancedRelation (k := k) P X) := by rw [h₁]
    _ = gLift ≫ kernel.ι (balancedTensorπ (k := k) P X) := rfl
    _ = g := kernel.lift_ι _ _ _

/-- The class of `1_P ⊗ x` in `P ⊗_B X`, as a `B`-linear map
`X → Hom(P, P ⊗_B X)`. -/
noncomputable def unitLinear (X : FGModuleCat.{v} (endOp P)) :
    X →ₗ[endOp P] (P ⟶ balancedTensor (k := k) P X) where
  toFun x := finiteCopowerι (k := k) P X x ≫ balancedTensorπ (k := k) P X
  map_add' x y := by simp
  map_smul' b x := by
    change finiteCopowerι (k := k) P X (b • x) ≫ balancedTensorπ (k := k) P X =
      b.unop ≫ (finiteCopowerι (k := k) P X x ≫ balancedTensorπ (k := k) P X)
    symm
    apply sub_eq_zero.mp
    calc
      b.unop ≫ (finiteCopowerι (k := k) P X x ≫ balancedTensorπ (k := k) P X) -
          finiteCopowerι (k := k) P X (b • x) ≫ balancedTensorπ (k := k) P X =
        (b.unop ≫ finiteCopowerι (k := k) P X x -
          finiteCopowerι (k := k) P X (b • x)) ≫
            balancedTensorπ (k := k) P X := by
              rw [Preadditive.sub_comp, Category.assoc]
      _ = (finiteCopowerι (k := k) P (TensorProduct k (endOp P) X) (b ⊗ₜ[k] x) ≫
          balancedRelation (k := k) P X) ≫ balancedTensorπ (k := k) P X := by
            rw [finiteCopowerι_balancedRelation_tmul]
      _ = 0 := by rw [Category.assoc, balancedRelation_π, comp_zero]

/-- Part (i)'s component `X ⟶ Hom(P, P ⊗_B X)` in `FGModuleCat B`. -/
noncomputable def unitApp (X : FGModuleCat.{v} (endOp P)) :
    X ⟶ hp.preadditiveCoyonedaObjFG.obj (balancedTensor (k := k) P X) :=
  InducedCategory.homMk (ModuleCat.ofHom (unitLinear (k := k) (P := P) X))

@[simp]
theorem unitApp_apply (X : FGModuleCat.{v} (endOp P)) (x : X) :
    unitApp (k := k) (P := P) X x =
      finiteCopowerι (k := k) P X x ≫ balancedTensorπ (k := k) P X := rfl

/-- The natural transformation `Id ⟶ G ⋙ Hom(P,-)` whose component sends
`x` to the class of `1_P ⊗ x`. -/
noncomputable def unit :
    𝟭 (FGModuleCat.{v} (endOp P)) ⟶
      balancedTensorFunctor (k := k) P ⋙ hp.preadditiveCoyonedaObjFG where
  app X := unitApp (k := k) (P := P) X
  naturality X Y f := by
    apply FGModuleCat.hom_ext
    ext x
    change finiteCopowerι (k := k) P Y (f x) ≫ balancedTensorπ (k := k) P Y =
      (finiteCopowerι (k := k) P X x ≫ balancedTensorπ (k := k) P X) ≫
        balancedTensorMap (k := k) P f
    symm
    calc
      (finiteCopowerι (k := k) P X x ≫ balancedTensorπ (k := k) P X) ≫
          balancedTensorMap (k := k) P f =
        finiteCopowerι (k := k) P X x ≫
          (balancedTensorπ (k := k) P X ≫ balancedTensorMap (k := k) P f) :=
            Category.assoc _ _ _
      _ = finiteCopowerι (k := k) P X x ≫
          (finiteCopowerMap (k := k) P (moduleHomRestrict (k := k) P f) ≫
            balancedTensorπ (k := k) P Y) := by rw [balancedTensorπ_map]
      _ = (finiteCopowerι (k := k) P X x ≫
          finiteCopowerMap (k := k) P (moduleHomRestrict (k := k) P f)) ≫
            balancedTensorπ (k := k) P Y := (Category.assoc _ _ _).symm
      _ = finiteCopowerι (k := k) P Y (f x) ≫ balancedTensorπ (k := k) P Y := by
        rw [finiteCopowerι_map]
        rfl

/-- Injectivity in part (i).  If `1_P ⊗ x` vanishes in the balanced quotient,
projectivity factors it through `ψ_X`, and `collapse` recovers `x`. -/
theorem unitLinear_injective (X : FGModuleCat.{v} (endOp P)) :
    Function.Injective (unitLinear (k := k) (P := P) X) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let g := finiteCopowerι (k := k) P X (x - y)
  have hg : g ≫ balancedTensorπ (k := k) P X = 0 := by
    change unitLinear (k := k) (P := P) X (x - y) = 0
    rw [map_sub, hxy, sub_self]
  obtain ⟨t, ht⟩ := exists_factor_balancedRelation (k := k) (P := P) X g hg
  calc
    x - y = collapse (k := k) (P := P) X g := by
      symm
      exact collapse_finiteCopowerι (k := k) (P := P) X (x - y)
    _ = collapse (k := k) (P := P) X
        (t ≫ balancedRelation (k := k) P X) := by rw [ht]
    _ = 0 := collapse_comp_balancedRelation (k := k) (P := P) X t

/-- Surjectivity in part (i).  Lift a map through the cokernel and use
`relationLift` to compare it with `1_P ⊗ collapse(g)`. -/
theorem unitLinear_surjective (X : FGModuleCat.{v} (endOp P)) :
    Function.Surjective (unitLinear (k := k) (P := P) X) := by
  intro y
  haveI : Projective P := hp.toProjective
  let g : P ⟶ finiteCopower (k := k) P X :=
    Projective.factorThru y (balancedTensorπ (k := k) P X)
  refine ⟨collapse (k := k) (P := P) X g, ?_⟩
  have hrel := balancedRelation_π (k := k) P X
  have hlift := relationLift_comp_balancedRelation (k := k) (P := P) X g
  have hz : (g - finiteCopowerι (k := k) P X
      (collapse (k := k) (P := P) X g)) ≫
        balancedTensorπ (k := k) P X = 0 := by
    rw [← hlift, Category.assoc, hrel, comp_zero]
  have heq : g ≫ balancedTensorπ (k := k) P X =
      finiteCopowerι (k := k) P X (collapse (k := k) (P := P) X g) ≫
        balancedTensorπ (k := k) P X := by
    exact sub_eq_zero.mp (by simpa [Preadditive.sub_comp] using hz)
  change finiteCopowerι (k := k) P X (collapse (k := k) (P := P) X g) ≫
      balancedTensorπ (k := k) P X = y
  rw [← heq]
  exact Projective.factorThru_comp y (balancedTensorπ (k := k) P X)

noncomputable def unitIsoApp (X : FGModuleCat.{v} (endOp P)) :
    X ≅ hp.preadditiveCoyonedaObjFG.obj (balancedTensor (k := k) P X) := by
  let e : X ≃ₗ[endOp P] (P ⟶ balancedTensor (k := k) P X) :=
    LinearEquiv.ofBijective (unitLinear (k := k) (P := P) X)
      ⟨unitLinear_injective (k := k) (P := P) X,
        unitLinear_surjective (k := k) (P := P) X⟩
  exact {
    hom := unitApp (k := k) (P := P) X
    inv := InducedCategory.homMk (ModuleCat.ofHom e.symm.toLinearMap)
    hom_inv_id := by
      apply FGModuleCat.hom_ext
      ext x
      exact e.left_inv x
    inv_hom_id := by
      apply FGModuleCat.hom_ext
      ext x
      exact e.right_inv x }

noncomputable instance unitApp_isIso (X : FGModuleCat.{v} (endOp P)) :
    IsIso (unitApp (k := k) (P := P) X) :=
  (unitIsoApp (k := k) (P := P) X).isIso_hom

@[simp]
theorem unitIsoApp_hom (X : FGModuleCat.{v} (endOp P)) :
    (unitIsoApp (k := k) (P := P) X).hom = unitApp (k := k) (P := P) X := rfl

/-- **Problem 9.6.5(i).**  The explicit map `x ↦ 1_P ⊗ x` is a natural
isomorphism `X ≅ Hom(P, P ⊗_B X)`.  Only projectivity is used to prove its
components bijective; the progenerator hypothesis ensures the codomain is finitely generated. -/
noncomputable def partI :
    balancedTensorFunctor (k := k) P ⋙ hp.preadditiveCoyonedaObjFG ≅
      𝟭 (FGModuleCat.{v} (endOp P)) :=
  (NatIso.ofComponents
    (fun X => unitIsoApp (k := k) (P := P) X)
    (fun f => (unit (k := k) (P := P)).naturality f)).symm

end Unit

/-! ## Parts (ii) and (iii): evaluation and the kernel argument -/

section Evaluation

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Etingof.IsFiniteAbelianCategory C] [Linear k C]
  [Etingof.IsFiniteAbelianCategoryOverField k C]
variable {P : C} [hp : Etingof.IsProgenerator P]

/-- Restriction of the `B`-module `Hom(P,Y)` to `k`, identified with its native
`k`-linear hom-space structure. -/
noncomputable def homEvaluationLinear (Y : C) :
    hp.preadditiveCoyonedaObjFG.obj Y →ₗ[k] (P ⟶ Y) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' r f := by
    change (algebraMap k (endOp P) r).unop ≫ f = _
    rw [endOp_algebraMap_unop, Linear.smul_comp, Category.id_comp]
    rfl

/-- Evaluation before imposing the balancing relation. -/
noncomputable def evaluationRaw (Y : C) :
    finiteCopower (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ⟶ Y :=
  finiteCopowerDesc (k := k) P (homEvaluationLinear (k := k) (P := P) Y)

@[simp, reassoc]
theorem finiteCopowerι_evaluationRaw (Y : C)
    (f : hp.preadditiveCoyonedaObjFG.obj Y) :
    finiteCopowerι (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) f ≫
      evaluationRaw (k := k) (P := P) Y = f :=
  finiteCopowerι_desc (k := k) P (homEvaluationLinear (k := k) (P := P) Y) f

/-- Ordinary evaluation is balanced, so it descends to `P ⊗_B Hom(P,Y)`. -/
theorem balancedRelation_evaluationRaw (Y : C) :
    balancedRelation (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ≫
      evaluationRaw (k := k) (P := P) Y = 0 := by
  apply finiteCopower_hom_ext (k := k) P
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b f =>
      rw [← Category.assoc, finiteCopowerι_balancedRelation_tmul,
        Preadditive.sub_comp, Category.assoc, finiteCopowerι_evaluationRaw,
        finiteCopowerι_evaluationRaw]
      simp only [comp_zero]
      change b.unop ≫ f - b.unop ≫ f = 0
      rw [sub_self]
  | add z z' hz hz' =>
      simp only [map_add, Preadditive.add_comp, hz, hz', comp_zero, add_zero]

/-- The component `P ⊗_B Hom(P,Y) ⟶ Y` of the book's evaluation map `ξ`. -/
noncomputable def evaluationApp (Y : C) :
    balancedTensor (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ⟶ Y :=
  cokernel.desc _ (evaluationRaw (k := k) (P := P) Y)
    (balancedRelation_evaluationRaw (k := k) (P := P) Y)

@[reassoc (attr := simp)]
theorem balancedTensorπ_evaluationApp (Y : C) :
    balancedTensorπ (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ≫
      evaluationApp (k := k) (P := P) Y = evaluationRaw (k := k) (P := P) Y :=
  cokernel.π_desc _ _ _

@[simp, reassoc]
theorem evaluationApp_on_tmul (Y : C) (f : hp.preadditiveCoyonedaObjFG.obj Y) :
    finiteCopowerι (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) f ≫
      (balancedTensorπ (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ≫
        evaluationApp (k := k) (P := P) Y) = f := by
  rw [balancedTensorπ_evaluationApp, finiteCopowerι_evaluationRaw]

theorem evaluationRaw_naturality {Y Z : C} (f : Y ⟶ Z) :
    finiteCopowerMap (k := k) P
        (moduleHomRestrict (k := k) P (hp.preadditiveCoyonedaObjFG.map f)) ≫
      evaluationRaw (k := k) (P := P) Z =
        evaluationRaw (k := k) (P := P) Y ≫ f := by
  apply finiteCopower_hom_ext (k := k) P
  intro g
  rw [← Category.assoc, finiteCopowerι_map, finiteCopowerι_evaluationRaw,
    ← Category.assoc, finiteCopowerι_evaluationRaw]
  rfl

/-- The natural evaluation transformation
`ξ : Hom(P,-) ⋙ (P ⊗_B -) ⟶ Id`. -/
noncomputable def ξ :
    hp.preadditiveCoyonedaObjFG ⋙ balancedTensorFunctor (k := k) P ⟶ 𝟭 C where
  app Y := evaluationApp (k := k) (P := P) Y
  naturality Y Z f := by
    apply (cancel_epi
      (balancedTensorπ (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y))).1
    change balancedTensorπ (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ≫
        (balancedTensorMap (k := k) P (hp.preadditiveCoyonedaObjFG.map f) ≫
          evaluationApp (k := k) (P := P) Z) =
      balancedTensorπ (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ≫
        (evaluationApp (k := k) (P := P) Y ≫ f)
    rw [← Category.assoc, balancedTensorπ_map, Category.assoc,
      balancedTensorπ_evaluationApp, ← Category.assoc, balancedTensorπ_evaluationApp]
    exact evaluationRaw_naturality (k := k) (P := P) f

/-- Every evaluation component is an epimorphism: maps out of its target are
detected by the generator `P`, and every `P ⟶ Y` is hit by `1_P ⊗ f`. -/
noncomputable instance evaluationApp_epi (Y : C) :
    Epi (evaluationApp (k := k) (P := P) Y) := by
  constructor
  intro Z f g hfg
  apply sub_eq_zero.mp
  apply (Preadditive.isSeparator_iff P).1 hp.isSeparator (f - g)
  intro a
  rw [Preadditive.comp_sub]
  apply sub_eq_zero.mpr
  rw [← evaluationApp_on_tmul (k := k) (P := P) Y a]
  simp only [Category.assoc]
  rw [hfg]

/-- **Problem 9.6.5(ii).**  The evaluation map `ξ_Y` is epi (the categorical
form of surjectivity in the book). -/
theorem partII (Y : C) : Epi ((ξ (k := k) (P := P)).app Y) := by
  change Epi (evaluationApp (k := k) (P := P) Y)
  infer_instance

/-- The unit/evaluation triangle on `Hom(P,Y)`. -/
theorem unit_evaluation_triangle (Y : C) :
    unitApp (k := k) (P := P) (hp.preadditiveCoyonedaObjFG.obj Y) ≫
        hp.preadditiveCoyonedaObjFG.map (evaluationApp (k := k) (P := P) Y) =
      𝟙 (hp.preadditiveCoyonedaObjFG.obj Y) := by
  apply FGModuleCat.hom_ext
  ext f
  change (finiteCopowerι (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) f ≫
      balancedTensorπ (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y)) ≫
        evaluationApp (k := k) (P := P) Y = f
  simpa only [Category.assoc] using evaluationApp_on_tmul (k := k) (P := P) Y f

noncomputable instance coyonedaMap_evaluationApp_isIso (Y : C) :
    IsIso (hp.preadditiveCoyonedaObjFG.map
      (evaluationApp (k := k) (P := P) Y)) := by
  haveI : IsIso (unitApp (k := k) (P := P)
      (hp.preadditiveCoyonedaObjFG.obj Y)) :=
    unitApp_isIso (k := k) (P := P) (hp.preadditiveCoyonedaObjFG.obj Y)
  haveI : IsIso
      (unitApp (k := k) (P := P) (hp.preadditiveCoyonedaObjFG.obj Y) ≫
        hp.preadditiveCoyonedaObjFG.map (evaluationApp (k := k) (P := P) Y)) := by
    rw [unit_evaluation_triangle]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (unitApp (k := k) (P := P) (hp.preadditiveCoyonedaObjFG.obj Y))
    (hp.preadditiveCoyonedaObjFG.map (evaluationApp (k := k) (P := P) Y))

/-- The kernel step in part (iii): since `Hom(P, ξ_Y)` is invertible, every
map from the generator to `ker ξ_Y` vanishes, hence the kernel is zero. -/
theorem evaluationApp_kernel_isZero (Y : C) :
    IsZero (kernel (evaluationApp (k := k) (P := P) Y)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (Preadditive.isSeparator_iff P).1 hp.isSeparator
    (𝟙 (kernel (evaluationApp (k := k) (P := P) Y)))
  intro f
  rw [Category.comp_id]
  have hfι : f ≫ kernel.ι (evaluationApp (k := k) (P := P) Y) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (hp.preadditiveCoyonedaObjFG.map
        (evaluationApp (k := k) (P := P) Y))).1
    change (f ≫ kernel.ι (evaluationApp (k := k) (P := P) Y)) ≫
        evaluationApp (k := k) (P := P) Y = 0 ≫
          evaluationApp (k := k) (P := P) Y
    rw [Category.assoc, kernel.condition, comp_zero, zero_comp]
  apply (cancel_mono (kernel.ι (evaluationApp (k := k) (P := P) Y))).1
  rw [hfι, zero_comp]

noncomputable instance evaluationApp_isIso (Y : C) :
    IsIso (evaluationApp (k := k) (P := P) Y) := by
  haveI : Mono (evaluationApp (k := k) (P := P) Y) :=
    Preadditive.mono_of_isZero_kernel _
      (evaluationApp_kernel_isZero (k := k) (P := P) Y)
  exact isIso_of_mono_of_epi _

noncomputable def evaluationIsoApp (Y : C) :
    balancedTensor (k := k) P (hp.preadditiveCoyonedaObjFG.obj Y) ≅ Y := by
  letI : IsIso (evaluationApp (k := k) (P := P) Y) :=
    evaluationApp_isIso (k := k) (P := P) Y
  exact asIso (evaluationApp (k := k) (P := P) Y)

@[simp]
theorem evaluationIsoApp_hom (Y : C) :
    (evaluationIsoApp (k := k) (P := P) Y).hom =
      evaluationApp (k := k) (P := P) Y := rfl

/-- **Problem 9.6.5(iii).**  The natural evaluation transformation `ξ` is an
isomorphism.  The component proof is the book's kernel/epi argument. -/
theorem partIII : IsIso (ξ (k := k) (P := P)) := by
  let e : hp.preadditiveCoyonedaObjFG ⋙ balancedTensorFunctor (k := k) P ≅ 𝟭 C :=
    NatIso.ofComponents
      (fun Y => evaluationIsoApp (k := k) (P := P) Y)
      (fun f => (ξ (k := k) (P := P)).naturality f)
  have he : e.hom = ξ (k := k) (P := P) := by
    ext Y
    exact evaluationIsoApp_hom (k := k) (P := P) Y
  rw [← he]
  exact e.isIso_hom

/-- The evaluation natural isomorphism obtained in part (iii). -/
noncomputable def partIIIso :
    hp.preadditiveCoyonedaObjFG ⋙ balancedTensorFunctor (k := k) P ≅ 𝟭 C := by
  letI := partIII (k := k) (P := P)
  exact asIso (ξ (k := k) (P := P))

/-- The Morita equivalence whose inverse functor is the explicitly constructed
`balancedTensorFunctor P`. -/
noncomputable def explicit_balancedTensor_quasiInverse :
    C ≌ FGModuleCat.{v} (endOp P) :=
  CategoryTheory.Equivalence.mk hp.preadditiveCoyonedaObjFG
    (balancedTensorFunctor (k := k) P)
    (partIIIso (k := k) (P := P)).symm (partI (k := k) (P := P))

end Evaluation

end Etingof.Problem965
