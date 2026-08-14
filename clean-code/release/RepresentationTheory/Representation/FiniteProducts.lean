/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib
import RepresentationTheory.Algebra.ModuleActions

/-!
# Finite products of finite-dimensional representations

This module constructs coordinatewise finite products of finite-dimensional representations and
exhibits them as categorical biproducts.
-/

open CategoryTheory Module
open RepresentationTheory.Algebra.ModuleActions

namespace RepresentationTheory.Representation.FiniteProducts

section PiEnd

variable {k : Type} [Field k]
variable {ι : Type}
variable {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

/-- A family of endomorphisms induces an endomorphism of the dependent function space. -/
def piLinearMap (f : ∀ i, M i →ₗ[k] M i) : (∀ i, M i) →ₗ[k] (∀ i, M i) :=
  LinearMap.pi fun i => (f i) ∘ₗ LinearMap.proj i

/-- The endomorphism induced on a dependent function space applies the given maps coordinatewise. -/
@[simp]
theorem piLinearMap_apply (f : ∀ i, M i →ₗ[k] M i) (x : ∀ i, M i) (i : ι) :
    piLinearMap f x i = f i (x i) := rfl

/-- The coordinatewise endomorphism induced by identity maps is the identity. -/
theorem piLinearMap_id :
    piLinearMap (fun i => (LinearMap.id : M i →ₗ[k] M i)) = LinearMap.id := rfl

/-- The coordinatewise endomorphism associated to a family of composites is the composite of the
associated endomorphisms. -/
theorem piLinearMap_comp (f g : ∀ i, M i →ₗ[k] M i) :
    piLinearMap (fun i => (f i) ∘ₗ (g i)) = (piLinearMap f) ∘ₗ (piLinearMap g) := rfl

/-- A coordinatewise endomorphism of a finite product is the sum of its projected
single-coordinate components. -/
theorem piLinearMap_eq_sum_single_comp_proj [Fintype ι] [DecidableEq ι]
    (f : ∀ i, M i →ₗ[k] M i) :
    piLinearMap f = ∑ i, (LinearMap.single k M i) ∘ₗ ((f i) ∘ₗ LinearMap.proj i) := by
  ext x j
  simp [Finset.sum_apply]

/-- Projection after the single-coordinate linear map at the same index is the identity. -/
theorem proj_comp_single [DecidableEq ι] (i : ι) :
    (LinearMap.proj i : (∀ j, M j) →ₗ[k] M i) ∘ₗ LinearMap.single k M i = LinearMap.id := by
  ext x
  simp

variable [Fintype ι] [∀ i, FiniteDimensional k (M i)]

/-- The trace of a coordinatewise endomorphism of a finite product is the sum of the traces of its
components. -/
theorem trace_piLinearMap (f : ∀ i, M i →ₗ[k] M i) :
    LinearMap.trace k (∀ i, M i) (piLinearMap f) = ∑ i, LinearMap.trace k (M i) (f i) := by
  classical
  rw [piLinearMap_eq_sum_single_comp_proj, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm' ((f i) ∘ₗ LinearMap.proj i) (LinearMap.single k M i),
    LinearMap.comp_assoc, proj_comp_single, LinearMap.comp_id]

end PiEnd

end RepresentationTheory.Representation.FiniteProducts

namespace RepresentationTheory.Algebra.ModuleActions.RingActionStructure

variable {k : Type} [Field k] {G : Type} [Monoid G]
variable {ι : Type}
variable {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

/-- The representation on a dependent function space obtained by acting in every coordinate. -/
def piRepresentation (ρ : ∀ i, _root_.Representation k G (M i)) :
    _root_.Representation k G (∀ i, M i) where
  toFun g := RepresentationTheory.Representation.FiniteProducts.piLinearMap fun i => ρ i g
  map_one' := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp [Module.End.mul_eq_comp]

/-- The dependent function space representation acts pointwise in each coordinate. -/
@[simp]
theorem piRepresentation_apply (ρ : ∀ i, _root_.Representation k G (M i)) (g : G)
    (x : ∀ i, M i) (i : ι) : piRepresentation ρ g x i = ρ i g (x i) := rfl

end RepresentationTheory.Algebra.ModuleActions.RingActionStructure

namespace RepresentationTheory.Representation.FiniteProducts

variable {k : Type} [Field k] {G : Type} [Monoid G]
variable {ι : Type}

/-- An equivariant linear map determines a morphism of finite-dimensional representations. -/
def homOfEquivariantLinearMap (V W : FDRep k G) (f : (V : Type) →ₗ[k] (W : Type))
    (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v)) : V ⟶ W where
  hom := FGModuleCat.ofHom f
  comm := by intro g; ext v; exact hf g v

/-- The representation morphism induced by an equivariant linear map agrees pointwise with that
map. -/
theorem homOfEquivariantLinearMap_apply (V W : FDRep k G)
    (f : (V : Type) →ₗ[k] (W : Type)) (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v))
    (v : (V : Type)) : (homOfEquivariantLinearMap V W f hf).hom.hom.hom v = f v := rfl

/-- The finite-dimensional representation formed by the coordinatewise product of a finite
family. -/
noncomputable def finiteProduct [Fintype ι] (V : ι → FDRep k G) : FDRep k G :=
  FDRep.of (RingActionStructure.piRepresentation fun i => (V i).ρ)

/-- The action on a finite product representation is evaluated coordinatewise. -/
@[simp]
theorem finiteProduct_rho_apply [Fintype ι] (V : ι → FDRep k G) (g : G)
    (x : (finiteProduct V : Type)) (i : ι) : (finiteProduct V).ρ g x i = (V i).ρ g (x i) := rfl

/-- The canonical morphism from a finite product representation to one of its factors. -/
noncomputable def finiteProductProjection [Fintype ι] (V : ι → FDRep k G) (i : ι) :
    finiteProduct V ⟶ V i :=
  homOfEquivariantLinearMap _ _ (LinearMap.proj i) fun _ _ => rfl

/-- The canonical morphism from one factor into a finite product representation. -/
noncomputable def finiteProductInclusion [Fintype ι] [DecidableEq ι] (V : ι → FDRep k G)
    (i : ι) : V i ⟶ finiteProduct V :=
  homOfEquivariantLinearMap _ _ (LinearMap.single k (fun j => ((V j : Type))) i) fun g v => by
    refine funext fun j => ?_
    change (Pi.single (M := fun j => ((V j : Type))) i ((V i).ρ g v)) j
        = (V j).ρ g ((Pi.single (M := fun j => ((V j : Type))) i v) j)
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h), map_zero]

/-- The canonical projection from a finite product evaluates at the selected coordinate. -/
@[simp]
theorem finiteProductProjection_apply [Fintype ι] (V : ι → FDRep k G) (i : ι)
    (x : (finiteProduct V : Type)) : (finiteProductProjection V i).hom.hom.hom x = x i := rfl

/-- The canonical inclusion into a finite product acts as the single-coordinate function. -/
@[simp]
theorem finiteProductInclusion_apply [Fintype ι] [DecidableEq ι] (V : ι → FDRep k G)
    (i : ι) (v : (V i : Type)) :
    (finiteProductInclusion V i).hom.hom.hom v = Pi.single i v := rfl

/-- An inclusion followed by the projection to the same coordinate is the identity. -/
theorem finiteProductInclusion_comp_projection [Fintype ι] [DecidableEq ι]
    (V : ι → FDRep k G) (i : ι) :
    finiteProductInclusion V i ≫ finiteProductProjection V i = 𝟙 (V i) := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  ext v
  simp

/-- An inclusion followed by a projection to a distinct coordinate is zero. -/
theorem finiteProductInclusion_comp_projection_of_ne [Fintype ι] [DecidableEq ι]
    (V : ι → FDRep k G) {i j : ι} (h : i ≠ j) :
    finiteProductInclusion V i ≫ finiteProductProjection V j = 0 := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  ext v
  exact Pi.single_eq_of_ne (M := fun j => ((V j : Type))) (Ne.symm h) v

/-- The character of a finite product of representations is the sum of the characters of its
factors. -/
theorem character_finiteProduct [Fintype ι] (V : ι → FDRep k G) (g : G) :
    (finiteProduct V).character g = ∑ i, (V i).character g :=
  trace_piLinearMap _

/-- The additive homomorphism that sends a morphism of representations to its underlying linear
map. -/
def homToLinearMap (X Y : FDRep k G) : (X ⟶ Y) →+ ((X : Type) →ₗ[k] (Y : Type)) where
  toFun f := f.hom.hom.hom
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The sum of each coordinate projection followed by its inclusion is the identity of the finite
product. -/
theorem sum_projection_comp_inclusion [Fintype ι] [DecidableEq ι] (V : ι → FDRep k G) :
    ∑ i, finiteProductProjection V i ≫ finiteProductInclusion V i = 𝟙 (finiteProduct V) := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  ext x
  have h := map_sum (homToLinearMap (finiteProduct V) (finiteProduct V))
    (fun i => finiteProductProjection V i ≫ finiteProductInclusion V i) Finset.univ
  have h2 := congrFun
    (congrArg (fun m : (finiteProduct V : Type) →ₗ[k] (finiteProduct V : Type) => (m : _ → _)) h) x
  simp only [homToLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h2
  rw [h2]
  have hstep : ∀ i : ι,
      ((finiteProductProjection V i ≫ finiteProductInclusion V i).hom.hom.hom) x
        = Pi.single (M := fun j => ((V j : Type))) i (x i) := fun _ => rfl
  simp only [LinearMap.coe_sum, Finset.sum_apply, hstep]
  exact Finset.univ_sum_single x

/-- The bicone whose cone point is the coordinatewise finite product representation. -/
noncomputable def finiteProductBicone [Fintype ι] [DecidableEq ι] (V : ι → FDRep k G) :
    Limits.Bicone V where
  pt := finiteProduct V
  π := finiteProductProjection V
  ι := finiteProductInclusion V
  ι_π i j := by
    rcases eq_or_ne i j with rfl | h
    · simp [finiteProductInclusion_comp_projection]
    · simp [finiteProductInclusion_comp_projection_of_ne V h, dif_neg h]

/-- The coordinatewise finite product bicone is a bilimit bicone. -/
noncomputable def finiteProductBiconeIsBilimit [Fintype ι] [DecidableEq ι]
    (V : ι → FDRep k G) : (finiteProductBicone V).IsBilimit :=
  Limits.isBilimitOfTotal _ (sum_projection_comp_inclusion V)

/-- A finite family of finite-dimensional representations admits a biproduct. -/
instance hasBiproduct_of_finite [Finite ι] (V : ι → FDRep k G) : Limits.HasBiproduct V := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  exact Limits.HasBiproduct.mk ⟨_, finiteProductBiconeIsBilimit V⟩

/-- Finite-dimensional representations of a monoid have all finite biproducts. -/
instance hasFiniteBiproducts : Limits.HasFiniteBiproducts (FDRep k G) :=
  ⟨fun _ => ⟨fun _ => inferInstance⟩⟩

/-- The coordinatewise finite product representation is isomorphic to the categorical biproduct. -/
noncomputable def finiteProductIsoBiproduct [Fintype ι] [DecidableEq ι]
    (V : ι → FDRep k G) : finiteProduct V ≅ ⨁ V :=
  Limits.biproduct.uniqueUpToIso V (finiteProductBiconeIsBilimit V)

/-- Monoid homomorphisms from a group to the units of the complex numbers are equivalent to monoid
homomorphisms into the complex numbers. -/
def monoidHomUnitsComplexEquiv {A : Type} [Group A] : (A →* ℂˣ) ≃ (A →* ℂ) where
  toFun f := (Units.coeHom ℂ).comp f
  invFun f := f.toHomUnits
  left_inv f := by ext a; simp
  right_inv f := by ext a; simp

/-- The sum of all complex-valued additive characters at an element is the group cardinality at
zero and vanishes otherwise. -/
theorem sum_additiveCharacters {α : Type} [AddCommGroup α] [Fintype α] [DecidableEq α]
    [Fintype (Multiplicative α →* ℂˣ)] (x : α) :
    ∑ f : Multiplicative α →* ℂˣ, ((f (Multiplicative.ofAdd x) : ℂ)) =
      if x = 0 then (Fintype.card α : ℂ) else 0 := by
  have h : ∑ f : Multiplicative α →* ℂˣ, ((f (Multiplicative.ofAdd x) : ℂ))
      = ∑ ψ : AddChar α ℂ, ψ x :=
    Fintype.sum_equiv (monoidHomUnitsComplexEquiv.trans AddChar.toMonoidHomEquiv.symm)
      _ _ fun _ => rfl
  rw [h, AddChar.sum_apply_eq_ite]

end RepresentationTheory.Representation.FiniteProducts
