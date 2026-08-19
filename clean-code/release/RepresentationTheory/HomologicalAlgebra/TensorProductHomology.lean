/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Mathlib.Algebra.Homology.CochainComplex.Monoidal

open CategoryTheory Limits MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace RepresentationTheory.HomologicalAlgebra.TensorProductHomology

universe u

variable {k : Type u} [Field k]

private lemma comp_units_zsmul_eq_zero {X Y Z : ModuleCat.{u} k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : ℤˣ) (h : f ≫ g = 0) : f ≫ (e • g) = 0 := by
  rw [Units.smul_def, Preadditive.comp_zsmul, h, smul_zero]

private lemma int_units_val_mul_self (e : ℤˣ) : (e : ℤ) * (e : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

section CrossProduct

variable (C D : CochainComplex (ModuleCat.{u} k) ℤ)

/-- Maps a tensor of cycles into the summed-degree component of the tensor product complex. -/
noncomputable def cyclesTensorCyclesToTensorComponent (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).X (j + m) :=
  (C.iCycles j ⊗ₘ D.iCycles m) ≫ HomologicalComplex.ιTensorObj C D j m (j + m) rfl

private lemma iCycles_tensor_comp_d₁ (j m j' : ℤ) :
    (C.iCycles j ⊗ₘ D.iCycles m) ≫
      mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' = 0 := by
  have h0 : ∀ {W : ModuleCat.{u} k} (z : C.X (j + 1) ⊗ D.X m ⟶ W),
      (C.iCycles j ⊗ₘ D.iCycles m) ≫ (C.d j (j + 1) ▷ D.X m) ≫ z = 0 := by
    intro W z
    rw [← Category.assoc, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, HomologicalComplex.iCycles_d, Category.comp_id]
    simp
  rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) m j']
  exact comp_units_zsmul_eq_zero _ _ _ (h0 _)

private lemma iCycles_tensor_comp_d₂ (j m j' : ℤ) :
    (C.iCycles j ⊗ₘ D.iCycles m) ≫
      mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' = 0 := by
  have h0 : ∀ {W : ModuleCat.{u} k} (z : C.X j ⊗ D.X (m + 1) ⟶ W),
      (C.iCycles j ⊗ₘ D.iCycles m) ≫ (C.X j ◁ D.d m (m + 1)) ≫ z = 0 := by
    intro W z
    rw [← Category.assoc, ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, HomologicalComplex.iCycles_d, Category.comp_id]
    simp
  rw [mapBifunctor.d₂_eq' _ _ _ _ j (show (ComplexShape.up ℤ).Rel m (m + 1) by simp) j']
  exact comp_units_zsmul_eq_zero _ _ _ (h0 _)

/-- The degree-component map obtained from two cycles is annihilated by every outgoing differential. -/
lemma cyclesTensorCyclesToTensorComponent_comp_d (j m j' : ℤ) :
    cyclesTensorCyclesToTensorComponent C D j m ≫ (HomologicalComplex.tensorObj C D).d (j + m) j' = 0 := by
  have h1 : HomologicalComplex.ιTensorObj C D j m (j + m) rfl ≫
      mapBifunctor.D₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j + m) j'
      = mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' :=
    mapBifunctor.ι_D₁ _ _ _ _ _ _ _ _ _
  have h2 : HomologicalComplex.ιTensorObj C D j m (j + m) rfl ≫
      mapBifunctor.D₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j + m) j'
      = mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' :=
    mapBifunctor.ι_D₂ _ _ _ _ _ _ _ _ _
  rw [cyclesTensorCyclesToTensorComponent, Category.assoc]
  change _ ≫ _ ≫ (HomologicalComplex.tensorObj C D).d _ _ = 0
  rw [mapBifunctor.d_eq, Preadditive.comp_add, h1, h2, Preadditive.comp_add,
    iCycles_tensor_comp_d₁, iCycles_tensor_comp_d₂, add_zero]

/-- Maps a tensor of cycle objects into the cycles of the tensor product complex in total degree. -/
noncomputable def cyclesTensorCyclesToTensorCycles (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).cycles (j + m) :=
  (HomologicalComplex.tensorObj C D).liftCycles (cyclesTensorCyclesToTensorComponent C D j m) (j + m + 1) (by simp)
    (cyclesTensorCyclesToTensorComponent_comp_d C D j m _)

/-- Including the induced tensor-product cycle map recovers the corresponding map into the degree component. -/
@[reassoc (attr := simp)]
lemma cyclesTensorCyclesToTensorCycles_comp_iCycles (j m : ℤ) :
    cyclesTensorCyclesToTensorCycles C D j m ≫ (HomologicalComplex.tensorObj C D).iCycles (j + m)
      = cyclesTensorCyclesToTensorComponent C D j m :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- Sends a tensor of cycles to the homology of the tensor product complex in the summed degree. -/
noncomputable def cyclesTensorCyclesToTensorHomology (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).homology (j + m) :=
  cyclesTensorCyclesToTensorCycles C D j m ≫ (HomologicalComplex.tensorObj C D).homologyπ (j + m)

private lemma eps₁_eq_one (p : ℤ × ℤ) :
    ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p = 1 := by
  simp [ComplexShape.ε₁]

private lemma d₁_eq_first (j m : ℤ) :
    mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j - 1) m (j + m)
      = (C.d (j - 1) j ▷ D.X m) ≫ HomologicalComplex.ιTensorObj C D j m (j + m) rfl := by
  rw [mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel (j - 1) j by simp) m (j + m) rfl,
    eps₁_eq_one, one_smul]
  rfl

private lemma d₂_eq_second (j m : ℤ) :
    mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j (m - 1) (j + m)
      = ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (j, m - 1) •
        ((C.X j ◁ D.d (m - 1) m) ≫ HomologicalComplex.ιTensorObj C D j m (j + m) rfl) := by
  rw [mapBifunctor.d₂_eq _ _ _ _ j (show (ComplexShape.up ℤ).Rel (m - 1) m by simp) (j + m) rfl]
  rfl

private lemma toCycles_whiskerRight_cyclesTensorι (j m : ℤ) :
    (C.toCycles (j - 1) j ▷ D.cycles m) ≫ cyclesTensorCyclesToTensorComponent C D j m
      = ((C.X (j - 1) ◁ D.iCycles m) ≫
          HomologicalComplex.ιTensorObj C D (j - 1) m (j - 1 + m) rfl) ≫
        (HomologicalComplex.tensorObj C D).d (j - 1 + m) (j + m) := by
  have h1 : HomologicalComplex.ιTensorObj C D (j - 1) m (j - 1 + m) rfl ≫
      mapBifunctor.D₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j - 1 + m) (j + m)
      = mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
          (j - 1) m (j + m) :=
    mapBifunctor.ι_D₁ _ _ _ _ _ _ _ _ _
  have h2 : HomologicalComplex.ιTensorObj C D (j - 1) m (j - 1 + m) rfl ≫
      mapBifunctor.D₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j - 1 + m) (j + m)
      = mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
          (j - 1) m (j + m) :=
    mapBifunctor.ι_D₂ _ _ _ _ _ _ _ _ _

  have hzero : (C.X (j - 1) ◁ D.iCycles m) ≫
      mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        (j - 1) m (j + m) = 0 := by
    have h0 : ∀ {W : ModuleCat.{u} k} (z : C.X (j - 1) ⊗ D.X (m + 1) ⟶ W),
        (C.X (j - 1) ◁ D.iCycles m) ≫ (C.X (j - 1) ◁ D.d m (m + 1)) ≫ z = 0 := by
      intro W z
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
        HomologicalComplex.iCycles_d, MonoidalPreadditive.whiskerLeft_zero, zero_comp]
    rw [mapBifunctor.d₂_eq' _ _ _ _ (j - 1)
      (show (ComplexShape.up ℤ).Rel m (m + 1) by simp) (j + m)]
    exact comp_units_zsmul_eq_zero _ _ _ (h0 _)
  rw [Category.assoc]
  change _ = _ ≫ _ ≫ (HomologicalComplex.tensorObj C D).d _ _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, h1, h2, Preadditive.comp_add, hzero, add_zero,
    d₁_eq_first, cyclesTensorCyclesToTensorComponent, ← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

private lemma whiskerLeft_toCycles_cyclesTensorι (j m : ℤ) :
    (C.cycles j ◁ D.toCycles (m - 1) m) ≫ cyclesTensorCyclesToTensorComponent C D j m
      = (ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (j, m - 1) •
          ((C.iCycles j ▷ D.X (m - 1)) ≫
            HomologicalComplex.ιTensorObj C D j (m - 1) (j + (m - 1)) rfl)) ≫
        (HomologicalComplex.tensorObj C D).d (j + (m - 1)) (j + m) := by
  have h1 : HomologicalComplex.ιTensorObj C D j (m - 1) (j + (m - 1)) rfl ≫
      mapBifunctor.D₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        (j + (m - 1)) (j + m)
      = mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
          j (m - 1) (j + m) :=
    mapBifunctor.ι_D₁ _ _ _ _ _ _ _ _ _
  have h2 : HomologicalComplex.ιTensorObj C D j (m - 1) (j + (m - 1)) rfl ≫
      mapBifunctor.D₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        (j + (m - 1)) (j + m)
      = mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
          j (m - 1) (j + m) :=
    mapBifunctor.ι_D₂ _ _ _ _ _ _ _ _ _

  have hzero : (C.iCycles j ▷ D.X (m - 1)) ≫
      mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        j (m - 1) (j + m) = 0 := by
    have h0 : ∀ {W : ModuleCat.{u} k} (z : C.X (j + 1) ⊗ D.X (m - 1) ⟶ W),
        (C.iCycles j ▷ D.X (m - 1)) ≫ (C.d j (j + 1) ▷ D.X (m - 1)) ≫ z = 0 := by
      intro W z
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        HomologicalComplex.iCycles_d, MonoidalPreadditive.zero_whiskerRight, zero_comp]
    rw [mapBifunctor.d₁_eq' _ _ _ _
      (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (m - 1) (j + m)]
    exact comp_units_zsmul_eq_zero _ _ _ (h0 _)
  rw [Units.smul_def, Preadditive.zsmul_comp, Category.assoc]
  change _ = _ • (_ ≫ _ ≫ (HomologicalComplex.tensorObj C D).d _ _)
  rw [mapBifunctor.d_eq, Preadditive.comp_add, h1, h2, Preadditive.comp_add, hzero, zero_add,
    d₂_eq_second, Units.smul_def, Preadditive.comp_zsmul, smul_smul, int_units_val_mul_self,
    one_smul, cyclesTensorCyclesToTensorComponent, ← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- Tensoring on the right preserves the colimit witness for the cokernel defining a homology object. -/
noncomputable def tensorRight_homologyCokernel_isColimit (j : ℤ) (Z : ModuleCat.{u} k) :
    IsColimit (CokernelCofork.ofπ ((tensorRight Z).map (C.homologyπ j))
      (show (tensorRight Z).map (C.toCycles (j - 1) j) ≫ (tensorRight Z).map (C.homologyπ j) = 0 by
        rw [← Functor.map_comp, HomologicalComplex.toCycles_comp_homologyπ, Functor.map_zero])) :=
  isColimitCoforkMapOfIsColimit' (tensorRight Z) _
    (C.homologyIsCokernel (j - 1) j (by simp))

/-- Tensoring on the left carries the cokernel presentation of a homology object to a colimit cokernel cofork. -/
noncomputable def tensorLeft_homologyCokernel_isColimit (m : ℤ) (W : ModuleCat.{u} k) :
    IsColimit (CokernelCofork.ofπ ((tensorLeft W).map (D.homologyπ m))
      (show (tensorLeft W).map (D.toCycles (m - 1) m) ≫ (tensorLeft W).map (D.homologyπ m) = 0 by
        rw [← Functor.map_comp, HomologicalComplex.toCycles_comp_homologyπ, Functor.map_zero])) :=
  isColimitCoforkMapOfIsColimit' (tensorLeft W) _
    (D.homologyIsCokernel (m - 1) m (by simp))

/-- Maps homology in one factor tensored with cycles in the other to homology of the tensor product complex. -/
noncomputable def homologyTensorCyclesToTensorHomology (j m : ℤ) :
    C.homology j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).homology (j + m) :=
  (tensorRight_homologyCokernel_isColimit C j (D.cycles m)).desc
    (CokernelCofork.ofπ (cyclesTensorCyclesToTensorHomology C D j m) (by
      change (C.toCycles (j - 1) j ▷ D.cycles m) ≫ cyclesTensorCyclesToTensorHomology C D j m = 0
      rw [cyclesTensorCyclesToTensorHomology, cyclesTensorCyclesToTensorCycles, ← Category.assoc,
        HomologicalComplex.comp_liftCycles]
      exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _
        (toCycles_whiskerRight_cyclesTensorι C D j m)))

/-- Projecting the first cycle factor to homology and then using the mixed map recovers the map defined on two cycle objects. -/
@[reassoc (attr := simp)]
lemma tensorRight_homologyProjection_comp_homologyTensorCyclesToTensorHomology (j m : ℤ) :
    (C.homologyπ j ▷ D.cycles m) ≫ homologyTensorCyclesToTensorHomology C D j m = cyclesTensorCyclesToTensorHomology C D j m :=
  Cofork.IsColimit.π_desc (tensorRight_homologyCokernel_isColimit C j (D.cycles m))

/-- Maps a tensor product of two homology objects to homology of the tensor product complex in the summed degree. -/
noncomputable def homologyTensorHomologyToTensorHomology (j m : ℤ) :
    C.homology j ⊗ D.homology m ⟶ (HomologicalComplex.tensorObj C D).homology (j + m) :=
  (tensorLeft_homologyCokernel_isColimit D m (C.homology j)).desc
    (CokernelCofork.ofπ (homologyTensorCyclesToTensorHomology C D j m) (by
      change (C.homology j ◁ D.toCycles (m - 1) m) ≫ homologyTensorCyclesToTensorHomology C D j m = 0
      refine Cofork.IsColimit.hom_ext (tensorRight_homologyCokernel_isColimit C j (D.X (m - 1))) ?_
      change (C.homologyπ j ▷ D.X (m - 1)) ≫ _ = (C.homologyπ j ▷ D.X (m - 1)) ≫ _
      rw [comp_zero, ← Category.assoc, ← MonoidalCategory.whisker_exchange, Category.assoc,
        tensorRight_homologyProjection_comp_homologyTensorCyclesToTensorHomology, cyclesTensorCyclesToTensorHomology, cyclesTensorCyclesToTensorCycles,
        ← Category.assoc, HomologicalComplex.comp_liftCycles]
      exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _
        (whiskerLeft_toCycles_cyclesTensorι C D j m)))

/-- Projecting the second cycle factor to homology before the pairwise homology map gives the homology-tensored-with-cycles map. -/
@[reassoc (attr := simp)]
lemma tensorLeft_homologyProjection_comp_homologyTensorHomologyToTensorHomology (j m : ℤ) :
    (C.homology j ◁ D.homologyπ m) ≫ homologyTensorHomologyToTensorHomology C D j m = homologyTensorCyclesToTensorHomology C D j m :=
  Cofork.IsColimit.π_desc (tensorLeft_homologyCokernel_isColimit D m (C.homology j))

/-- Tensoring a canonical homology projection on the right by a module yields an epimorphism. -/
instance tensorRight_homologyProjection_epi (j : ℤ) (Z : ModuleCat.{u} k) :
    Epi (C.homologyπ j ▷ Z) :=
  Limits.epi_of_isColimit_cofork (tensorRight_homologyCokernel_isColimit C j Z)

/-- Tensoring a canonical homology projection on the left by a module preserves its epimorphism property. -/
instance tensorLeft_homologyProjection_epi (m : ℤ) (W : ModuleCat.{u} k) :
    Epi (W ◁ D.homologyπ m) :=
  Limits.epi_of_isColimit_cofork (tensorLeft_homologyCokernel_isColimit D m W)

/-- The tensor product of the two canonical projections onto homology is an epimorphism. -/
instance tensorHomologyProjections_epi (j m : ℤ) :
    Epi (C.homologyπ j ⊗ₘ D.homologyπ m) := by
  rw [MonoidalCategory.tensorHom_def]
  infer_instance

/-- Passing both cycle factors to homology before applying the pairwise tensor-homology map gives the direct cycle-level map. -/
@[reassoc (attr := simp)]
lemma tensorHomologyProjections_comp_homologyTensorHomologyToTensorHomology (j m : ℤ) :
    (C.homologyπ j ⊗ₘ D.homologyπ m) ≫ homologyTensorHomologyToTensorHomology C D j m
      = cyclesTensorCyclesToTensorHomology C D j m := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, tensorLeft_homologyProjection_comp_homologyTensorHomologyToTensorHomology,
    tensorRight_homologyProjection_comp_homologyTensorCyclesToTensorHomology]

end CrossProduct

section Naturality

variable {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}

/-- The component-level tensor map on cycles commutes with maps of the two complexes. -/
lemma cyclesTensorCyclesToTensorComponent_natural (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.cyclesMap f j ⊗ₘ HomologicalComplex.cyclesMap g m)
        ≫ cyclesTensorCyclesToTensorComponent C' D' j m
      = cyclesTensorCyclesToTensorComponent C D j m ≫ (HomologicalComplex.tensorHom f g).f (j + m) := by
  rw [cyclesTensorCyclesToTensorComponent, cyclesTensorCyclesToTensorComponent, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  congr 1
  rw [MonoidalCategory.tensorHom_def]
  rfl

/-- The map from tensors of cycles to tensor-product cycles is natural in both complexes. -/
lemma cyclesTensorCyclesToTensorCycles_natural (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.cyclesMap f j ⊗ₘ HomologicalComplex.cyclesMap g m)
        ≫ cyclesTensorCyclesToTensorCycles C' D' j m
      = cyclesTensorCyclesToTensorCycles C D j m
        ≫ HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom f g) (j + m) := by
  rw [← cancel_mono ((HomologicalComplex.tensorObj C' D').iCycles (j + m)),
    Category.assoc, Category.assoc, cyclesTensorCyclesToTensorCycles_comp_iCycles, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, cyclesTensorCyclesToTensorCycles_comp_iCycles, cyclesTensorCyclesToTensorComponent_natural]

/-- The cycle-tensor map to tensor-product homology commutes with morphisms of both complexes. -/
lemma cyclesTensorCyclesToTensorHomology_natural (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.cyclesMap f j ⊗ₘ HomologicalComplex.cyclesMap g m)
        ≫ cyclesTensorCyclesToTensorHomology C' D' j m
      = cyclesTensorCyclesToTensorHomology C D j m
        ≫ HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) (j + m) := by
  rw [cyclesTensorCyclesToTensorHomology, cyclesTensorCyclesToTensorHomology, ← Category.assoc, cyclesTensorCyclesToTensorCycles_natural,
    Category.assoc, Category.assoc, HomologicalComplex.homologyπ_naturality]

/-- The pairwise map from a tensor of homology objects to tensor-product homology is natural in both inputs. -/
lemma homologyTensorHomologyToTensorHomology_natural (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.homologyMap f j ⊗ₘ HomologicalComplex.homologyMap g m)
        ≫ homologyTensorHomologyToTensorHomology C' D' j m
      = homologyTensorHomologyToTensorHomology C D j m
        ≫ HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) (j + m) := by
  rw [← cancel_epi (C.homologyπ j ⊗ₘ D.homologyπ m), ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.homologyπ_naturality, ← MonoidalCategory.tensorHom_comp_tensorHom,
    Category.assoc, tensorHomologyProjections_comp_homologyTensorHomologyToTensorHomology, ← Category.assoc,
    tensorHomologyProjections_comp_homologyTensorHomologyToTensorHomology, cyclesTensorCyclesToTensorHomology_natural]

end Naturality

section Assembly

/-- The type of bidegree indices associated with an integer total degree. -/
abbrev TotalDegreeIndex (i : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = i}

/-- Combines the direct sum of pairwise tensor products of homology into tensor-product homology at a fixed total degree. -/
noncomputable def totalHomologyTensorToTensorHomology (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    (∐ fun p : TotalDegreeIndex i => C.homology p.1.1 ⊗ D.homology p.1.2)
      ⟶ (HomologicalComplex.tensorObj C D).homology i :=
  Sigma.desc fun p => homologyTensorHomologyToTensorHomology C D p.1.1 p.1.2 ≫ eqToHom (by rw [p.2])

/-- On each summand, the total-degree homology map agrees with the pairwise map followed by degree transport. -/
@[reassoc (attr := simp)]
lemma sigmaInclusion_comp_totalHomologyTensorToTensorHomology (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) (p : TotalDegreeIndex i) :
    Sigma.ι (fun p : TotalDegreeIndex i => C.homology p.1.1 ⊗ D.homology p.1.2) p
        ≫ totalHomologyTensorToTensorHomology C D i
      = homologyTensorHomologyToTensorHomology C D p.1.1 p.1.2 ≫ eqToHom (by rw [p.2]) :=
  Sigma.ι_desc _ _

/-- The summand indexed by a chosen degree pair is sent by the total map through the corresponding pairwise homology morphism. -/
lemma sigmaInclusion_pair_comp_totalHomologyTensorToTensorHomology (C D : CochainComplex (ModuleCat.{u} k) ℤ) (j m : ℤ) :
    Sigma.ι (fun p : TotalDegreeIndex (j + m) => C.homology p.1.1 ⊗ D.homology p.1.2)
        ⟨(j, m), rfl⟩ ≫ totalHomologyTensorToTensorHomology C D (j + m)
      = homologyTensorHomologyToTensorHomology C D j m := by
  rw [sigmaInclusion_comp_totalHomologyTensorToTensorHomology]
  simp

/-- The functor assigning two cochain complexes their total-degree object assembled from tensor products of homology. -/
noncomputable def totalHomologyTensorFunctor (i : ℤ) :
    (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ) ⥤
      ModuleCat.{u} k where
  obj X := ∐ fun p : TotalDegreeIndex i => X.1.homology p.1.1 ⊗ X.2.homology p.1.2
  map {X Y} φ := Sigma.desc fun p =>
    (HomologicalComplex.homologyMap φ.1 p.1.1 ⊗ₘ HomologicalComplex.homologyMap φ.2 p.1.2) ≫
      Sigma.ι (fun p : TotalDegreeIndex i => Y.1.homology p.1.1 ⊗ Y.2.homology p.1.2) p
  map_id X := by
    refine Sigma.hom_ext _ _ fun p => ?_
    simp
  map_comp {X Y Z} φ ψ := by
    refine Sigma.hom_ext _ _ fun p => ?_
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc,
      ← Category.assoc]
    congr 1
    rw [show (φ ≫ ψ).1 = φ.1 ≫ ψ.1 from rfl, show (φ ≫ ψ).2 = φ.2 ≫ ψ.2 from rfl,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
      MonoidalCategory.tensorHom_comp_tensorHom]

/-- Mapping the total-degree functor after a summand inclusion equals the tensor of the induced homology maps followed by the target inclusion. -/
@[reassoc (attr := simp)]
lemma sigmaInclusion_naturality (i : ℤ)
    {X Y : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)}
    (φ : X ⟶ Y) (p : TotalDegreeIndex i) :
    Sigma.ι (fun p : TotalDegreeIndex i => X.1.homology p.1.1 ⊗ X.2.homology p.1.2) p
        ≫ (totalHomologyTensorFunctor i).map φ
      = (HomologicalComplex.homologyMap φ.1 p.1.1 ⊗ₘ HomologicalComplex.homologyMap φ.2 p.1.2)
        ≫ Sigma.ι (fun p : TotalDegreeIndex i => Y.1.homology p.1.1 ⊗ Y.2.homology p.1.2) p :=
  Sigma.ι_desc _ _

/-- The functor taking a pair of cochain complexes to the specified degree of the homology of their tensor product. -/
noncomputable def tensorHomologyFunctor (i : ℤ) :
    (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ) ⥤
      ModuleCat.{u} k :=
  MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} k) ℤ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) i

/-- The natural transformation from the total pairwise-homology functor to tensor-product homology in a fixed degree. -/
noncomputable def totalHomologyTensorNatTrans (i : ℤ) :
    totalHomologyTensorFunctor (k := k) i ⟶ tensorHomologyFunctor (k := k) i where
  app X := totalHomologyTensorToTensorHomology X.1 X.2 i
  naturality {X Y} φ := by
    refine Sigma.hom_ext _ _ fun p => ?_
    obtain ⟨⟨j, m⟩, rfl⟩ := p
    simp only [sigmaInclusion_naturality_assoc, sigmaInclusion_comp_totalHomologyTensorToTensorHomology, sigmaInclusion_comp_totalHomologyTensorToTensorHomology_assoc, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    exact homologyTensorHomologyToTensorHomology_natural φ.1 φ.2 j m

/-- The total-degree map from pairwise homology tensors is natural in both cochain complexes. -/
lemma totalHomologyTensorToTensorHomology_natural {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℤ) :
    (totalHomologyTensorFunctor i).map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C', D')) ≫ totalHomologyTensorToTensorHomology C' D' i
      = totalHomologyTensorToTensorHomology C D i
        ≫ HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) i :=
  (totalHomologyTensorNatTrans i).naturality ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
    (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C', D'))

end Assembly

/-- The specified complex constructed from two cochain complexes agrees with their monoidal tensor object. -/
lemma tensorComplex_eq_tensorObj (C D : CochainComplex (ModuleCat.{u} k) ℤ) :
    RepresentationTheory.Mathlib.Algebra.Homology.CochainComplex.Monoidal.CochainComplex.binaryOperation C D = HomologicalComplex.tensorObj C D :=
  rfl

/-- The comparison between the cycle map and its inclusion remains valid after postcomposition. -/
add_decl_doc cyclesTensorCyclesToTensorCycles_comp_iCycles_assoc

/-- The factorization through the tensor of homology objects is stable under further postcomposition. -/
add_decl_doc tensorHomologyProjections_comp_homologyTensorHomologyToTensorHomology_assoc

/-- The factorization through homology in the second tensor factor persists after postcomposition. -/
add_decl_doc tensorLeft_homologyProjection_comp_homologyTensorHomologyToTensorHomology_assoc

/-- The first-factor homology projection identity is unchanged by an additional morphism on the right. -/
add_decl_doc tensorRight_homologyProjection_comp_homologyTensorCyclesToTensorHomology_assoc

/-- The description of the total-degree map on a summand remains valid after postcomposition. -/
add_decl_doc sigmaInclusion_comp_totalHomologyTensorToTensorHomology_assoc

namespace Auxiliary

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias statement024740 := sigmaInclusion_comp_totalHomologyTensorToTensorHomology

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias statement024741 := sigmaInclusion_comp_totalHomologyTensorToTensorHomology_assoc

end Auxiliary

/-- Naturality of a total-degree summand inclusion is preserved under subsequent composition. -/
add_decl_doc sigmaInclusion_naturality_assoc

end RepresentationTheory.HomologicalAlgebra.TensorProductHomology

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.HomologicalAlgebra.TensorProductHomology.Auxiliary.statement020807 := _root_.RepresentationTheory.HomologicalAlgebra.TensorProductHomology.tensorLeft_homologyCokernel_isColimit

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.HomologicalAlgebra.TensorProductHomology.Auxiliary.statement020810 := _root_.RepresentationTheory.HomologicalAlgebra.TensorProductHomology.tensorRight_homologyCokernel_isColimit

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.HomologicalAlgebra.TensorProductHomology.Auxiliary.statement024742 := _root_.RepresentationTheory.HomologicalAlgebra.TensorProductHomology.sigmaInclusion_pair_comp_totalHomologyTensorToTensorHomology
