import RepresentationTheory.Algebra.TensorProduct.ModuleCat
import RepresentationTheory.TensorProduct.LinearMap
open CategoryTheory TensorProduct
open RepresentationTheory.TensorProduct.LinearMap
namespace RepresentationTheory.TensorProduct.LinearMapModuleEquiv
universe u
variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
  [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))
attribute [local instance] RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule
/-- Provides the scalar-tower structure from the base field through a tensor-product algebra to a tensor product of modules. -/
local instance tensorProductModuleIsScalarTower (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    IsScalarTower k (A₁ ⊗[k] A₂) (X ⊗[k] Y) := by
  refine ⟨fun c s z => ?_⟩
  change RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k A₁ A₂ X Y (c • s) z = c • RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k A₁ A₂ X Y s z
  rw [map_smul]
  rfl
variable {A₁ A₂}
include hN in
/-- The linear equivalence between maps out of a tensor product and the tensor product of linear-map modules for finite projective factors. -/
noncomputable def tensorProductLinearMapEquiv (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂] :
    ((X₁ ⊗[k] X₂ →ₗ[A₁ ⊗[k] A₂] N₁ ⊗[k] N₂)) ≃ₗ[k]
      ((X₁ →ₗ[A₁] N₁) ⊗[k] (X₂ →ₗ[A₂] N₂)) :=
  (RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensorEquiv k A₁ A₂ X₁ X₂ N₁ N₂
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k A₁ A₂ X₁ X₂) hN).symm
include hN in
/-- An isomorphism of k-modules between a linear-map module over the tensor-product algebra and the tensor product of the corresponding factorwise linear-map modules. -/
noncomputable def tensorProductLinearMapIso (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂] :
    ModuleCat.of k (↥(RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ X₁ X₂) →ₗ[A₁ ⊗[k] A₂] N₁ ⊗[k] N₂)
      ≅ ModuleCat.of k ((X₁ →ₗ[A₁] N₁) ⊗[k] (X₂ →ₗ[A₂] N₂)) :=
  (tensorProductLinearMapEquiv k N₁ N₂ hN X₁ X₂).toModuleIso
/-- States that the tensor-product linear-map construction is compatible with a morphism in the first module factor. -/
theorem tensorProductLinearMap_comp_map_left {X₁ X₁' : ModuleCat.{u} A₁} (f : X₁' ⟶ X₁)
    (X₂ : ModuleCat.{u} A₂) :
    (RepresentationTheory.TensorProduct.LinearMap.LinearMap.precompLinear k (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap k f (𝟙 X₂))).comp
        (RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensor k A₁ A₂ X₁ X₂ N₁ N₂
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k A₁ A₂ X₁ X₂) hN)
      = (RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensor k A₁ A₂ X₁' X₂ N₁ N₂
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k A₁ A₂ X₁' X₂) hN).comp
          (TensorProduct.map (RepresentationTheory.TensorProduct.LinearMap.LinearMap.precompLinear k f.hom) LinearMap.id) := by
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  refine RepresentationTheory.TensorProduct.LinearMap.LinearMap.ext_tmul k A₁ A₂ X₁' X₂ N₁ N₂ fun x₁ x₂ => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, RepresentationTheory.TensorProduct.LinearMap.LinearMap.precompLinear_apply,
    RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensor_tmul_apply_tmul, RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap_tmul, ModuleCat.hom_id, LinearMap.id_coe]
/-- States that the tensor-product linear-map construction is compatible with a morphism in the second module factor. -/
theorem tensorProductLinearMap_comp_map_right (X₁ : ModuleCat.{u} A₁) {X₂ X₂' : ModuleCat.{u} A₂}
    (g : X₂' ⟶ X₂) :
    (RepresentationTheory.TensorProduct.LinearMap.LinearMap.precompLinear k (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap k (𝟙 X₁) g)).comp
        (RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensor k A₁ A₂ X₁ X₂ N₁ N₂
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k A₁ A₂ X₁ X₂) hN)
      = (RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensor k A₁ A₂ X₁ X₂' N₁ N₂
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k A₁ A₂ X₁ X₂') hN).comp
          (TensorProduct.map LinearMap.id (RepresentationTheory.TensorProduct.LinearMap.LinearMap.precompLinear k g.hom)) := by
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  refine RepresentationTheory.TensorProduct.LinearMap.LinearMap.ext_tmul k A₁ A₂ X₁ X₂' N₁ N₂ fun x₁ x₂ => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, RepresentationTheory.TensorProduct.LinearMap.LinearMap.precompLinear_apply,
    RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensor_tmul_apply_tmul, RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap_tmul, ModuleCat.hom_id, LinearMap.id_coe]
end RepresentationTheory.TensorProduct.LinearMapModuleEquiv
