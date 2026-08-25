import Mathlib
import EtingofRepresentationTheory.Chapter7.TensorComplexBiprod

/-!
# The natural Künneth (cross product) map

Problem 7.8.7(iv) asserts a **natural** isomorphism
`Hⁱ(C ⊗ D) ≅ ⨁_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`. The witness produced in
`EtingofRepresentationTheory/Chapter7/Problem7_8_7.lean` is built from the splitting
`C ≅ E ⊞ homologyZeroComplex C` of part (iii), which is manufactured by choosing sections of
`homologyπ` and retractions of `iCycles` degreewise and then splitting an idempotent. Those
choices are not natural in `C`, so the resulting isomorphism carries no naturality data at all,
and is exposed only as a `Nonempty`.

This file builds the map that *is* natural: the **cross product** (external product)

`κ_{C,D,j,m} : Hʲ(C) ⊗ Hᵐ(D) ⟶ H^{j+m}(C ⊗ D)`,

assembled over `j + m = i` into

`kunnethMap C D i : (∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)) ⟶ Hⁱ(C ⊗ D)`.

The construction is choice-free:

* a cycle `z ∈ Zʲ(C)` and a cycle `w ∈ Zᵐ(D)` give a cycle `z ⊗ w` of `C ⊗ D` in degree
  `j + m`, because the two halves `dᶜ ⊗ 1` and `± 1 ⊗ dᴰ` of the total differential kill `z`
  and `w` respectively (`cyclesTensorLift`);
* the resulting map `Zʲ(C) ⊗ Zᵐ(D) ⟶ H^{j+m}(C ⊗ D)` kills boundaries in either variable, so
  it descends along the epimorphism `homologyπ ⊗ homologyπ`. We descend in two steps, using
  that `ModuleCat k` is monoidal closed, hence `tensorLeft`/`tensorRight` preserve cokernels,
  and that `homologyπ` is the cokernel of `toCycles` (`kunnethAux`, `kunnethSummand`).

Naturality in both variables is then a `cancel_epi` argument against `homologyπ ⊗ homologyπ`.
Finally the two sides are packaged as bifunctors
`kunnethSource i, kunnethTarget i : (CochainComplex (ModuleCat k) ℤ)² ⥤ ModuleCat k` and `κ`
as `kunnethNatTrans i`.

That `kunnethNatTrans i` is an isomorphism is *not* proved here; see the successor issue.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex

-- The `mapBifunctor` API is stated through `GradedObject` layers that are only definitionally
-- equal to the `HomologicalComplex` spellings used here, so unification has to look past
-- `instances` transparency (Mathlib does the same in `ShortComplex/HomologicalComplex.lean`).
set_option backward.isDefEq.respectTransparency false

namespace Etingof

universe u

variable {k : Type u} [Field k]

/-- A composite with a `ℤˣ`-scaled second factor vanishes as soon as the unscaled composite
does. Used to discharge the Koszul signs appearing in the total differential. -/
private lemma comp_units_zsmul_eq_zero {X Y Z : ModuleCat.{u} k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : ℤˣ) (h : f ≫ g = 0) : f ≫ (e • g) = 0 := by
  rw [Units.smul_def, Preadditive.comp_zsmul, h, smul_zero]

/-- `(-1)^n * (-1)^n = 1`, in the coerced form produced by the Koszul-sign rewrites. -/
private lemma int_units_val_mul_self (e : ℤˣ) : (e : ℤ) * (e : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

section CrossProduct

variable (C D : CochainComplex (ModuleCat.{u} k) ℤ)

/-! ### The cross product on cycles -/

/-- The summand inclusion `Zʲ(C) ⊗ Zᵐ(D) ⟶ (C ⊗ D)^{j+m}` obtained from the inclusions of
cycles into the two factors. -/
noncomputable def cyclesTensorι (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).X (j + m) :=
  (C.iCycles j ⊗ₘ D.iCycles m) ≫ HomologicalComplex.ιTensorObj C D j m (j + m) rfl

/-- The `dᶜ ⊗ 1` half of the total differential kills a cycle of `C`. -/
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

/-- The `± 1 ⊗ dᴰ` half of the total differential kills a cycle of `D`. -/
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

/-- A tensor of cycles is a cycle: the tensor of `Zʲ(C)` and `Zᵐ(D)` is annihilated by the
total differential of `C ⊗ D`. -/
lemma cyclesTensorι_d (j m j' : ℤ) :
    cyclesTensorι C D j m ≫ (HomologicalComplex.tensorObj C D).d (j + m) j' = 0 := by
  have h1 : HomologicalComplex.ιTensorObj C D j m (j + m) rfl ≫
      mapBifunctor.D₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j + m) j'
      = mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' :=
    mapBifunctor.ι_D₁ _ _ _ _ _ _ _ _ _
  have h2 : HomologicalComplex.ιTensorObj C D j m (j + m) rfl ≫
      mapBifunctor.D₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j + m) j'
      = mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' :=
    mapBifunctor.ι_D₂ _ _ _ _ _ _ _ _ _
  rw [cyclesTensorι, Category.assoc]
  change _ ≫ _ ≫ (HomologicalComplex.tensorObj C D).d _ _ = 0
  rw [mapBifunctor.d_eq, Preadditive.comp_add, h1, h2, Preadditive.comp_add,
    iCycles_tensor_comp_d₁, iCycles_tensor_comp_d₂, add_zero]

/-- The cross product on cycles, `Zʲ(C) ⊗ Zᵐ(D) ⟶ Z^{j+m}(C ⊗ D)`. -/
noncomputable def cyclesTensorLift (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).cycles (j + m) :=
  (HomologicalComplex.tensorObj C D).liftCycles (cyclesTensorι C D j m) (j + m + 1) (by simp)
    (cyclesTensorι_d C D j m _)

@[reassoc (attr := simp)]
lemma cyclesTensorLift_i (j m : ℤ) :
    cyclesTensorLift C D j m ≫ (HomologicalComplex.tensorObj C D).iCycles (j + m)
      = cyclesTensorι C D j m :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The cross product on cycles followed by the projection to homology. -/
noncomputable def cyclesTensorHomologyπ (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).homology (j + m) :=
  cyclesTensorLift C D j m ≫ (HomologicalComplex.tensorObj C D).homologyπ (j + m)

/-! ### The cross product kills boundaries in either variable -/

/-- For the complex shapes at hand the first Koszul sign is trivial. -/
private lemma eps₁_eq_one (p : ℤ × ℤ) :
    ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p = 1 := by
  simp [ComplexShape.ε₁]

/-- `d ⊗ 1` on the summand `Cʲ⁻¹ ⊗ Zᵐ`. -/
private lemma d₁_eq_first (j m : ℤ) :
    mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j - 1) m (j + m)
      = (C.d (j - 1) j ▷ D.X m) ≫ HomologicalComplex.ιTensorObj C D j m (j + m) rfl := by
  rw [mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel (j - 1) j by simp) m (j + m) rfl,
    eps₁_eq_one, one_smul]
  rfl

/-- `1 ⊗ d` on the summand `Zʲ ⊗ Dᵐ⁻¹`. -/
private lemma d₂_eq_second (j m : ℤ) :
    mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j (m - 1) (j + m)
      = ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (j, m - 1) •
        ((C.X j ◁ D.d (m - 1) m) ≫ HomologicalComplex.ιTensorObj C D j m (j + m) rfl) := by
  rw [mapBifunctor.d₂_eq _ _ _ _ j (show (ComplexShape.up ℤ).Rel (m - 1) m by simp) (j + m) rfl]
  rfl

/-- A cross product with a boundary in the first variable is a boundary: the summand
`Cʲ⁻¹ ⊗ Zᵐ` of `(C ⊗ D)^{j-1+m}` maps onto it under the total differential. -/
private lemma toCycles_whiskerRight_cyclesTensorι (j m : ℤ) :
    (C.toCycles (j - 1) j ▷ D.cycles m) ≫ cyclesTensorι C D j m
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
  -- the `1 ⊗ d` half dies because `iCycles ≫ d = 0` in `D`
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
    d₁_eq_first, cyclesTensorι, ← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- A cross product with a boundary in the second variable is a boundary. -/
private lemma whiskerLeft_toCycles_cyclesTensorι (j m : ℤ) :
    (C.cycles j ◁ D.toCycles (m - 1) m) ≫ cyclesTensorι C D j m
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
  -- the `d ⊗ 1` half dies because `iCycles ≫ d = 0` in `C`
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
    one_smul, cyclesTensorι, ← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-! ### Descending the cross product to homology

`Hʲ(C)` is the cokernel of `toCycles : Cʲ⁻¹ ⟶ Zʲ(C)`, and `ModuleCat k` is monoidal closed,
so `tensorRight Z` and `tensorLeft W` are left adjoints and preserve that cokernel. Descending
first in the `C` variable and then in the `D` variable produces the cross product on homology
without any choice of splitting.
-/

/-- `homologyπ ▷ Z` is a cokernel of `toCycles ▷ Z`. -/
noncomputable def isColimitTensorRightHomologyπ (j : ℤ) (Z : ModuleCat.{u} k) :
    IsColimit (CokernelCofork.ofπ ((tensorRight Z).map (C.homologyπ j))
      (show (tensorRight Z).map (C.toCycles (j - 1) j) ≫ (tensorRight Z).map (C.homologyπ j) = 0 by
        rw [← Functor.map_comp, HomologicalComplex.toCycles_comp_homologyπ, Functor.map_zero])) :=
  isColimitCoforkMapOfIsColimit' (tensorRight Z) _
    (C.homologyIsCokernel (j - 1) j (by simp))

/-- `W ◁ homologyπ` is a cokernel of `W ◁ toCycles`. -/
noncomputable def isColimitTensorLeftHomologyπ (m : ℤ) (W : ModuleCat.{u} k) :
    IsColimit (CokernelCofork.ofπ ((tensorLeft W).map (D.homologyπ m))
      (show (tensorLeft W).map (D.toCycles (m - 1) m) ≫ (tensorLeft W).map (D.homologyπ m) = 0 by
        rw [← Functor.map_comp, HomologicalComplex.toCycles_comp_homologyπ, Functor.map_zero])) :=
  isColimitCoforkMapOfIsColimit' (tensorLeft W) _
    (D.homologyIsCokernel (m - 1) m (by simp))

/-- The cross product after descending in the first variable only:
`Hʲ(C) ⊗ Zᵐ(D) ⟶ H^{j+m}(C ⊗ D)`. -/
noncomputable def kunnethAux (j m : ℤ) :
    C.homology j ⊗ D.cycles m ⟶ (HomologicalComplex.tensorObj C D).homology (j + m) :=
  (isColimitTensorRightHomologyπ C j (D.cycles m)).desc
    (CokernelCofork.ofπ (cyclesTensorHomologyπ C D j m) (by
      change (C.toCycles (j - 1) j ▷ D.cycles m) ≫ cyclesTensorHomologyπ C D j m = 0
      rw [cyclesTensorHomologyπ, cyclesTensorLift, ← Category.assoc,
        HomologicalComplex.comp_liftCycles]
      exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _
        (toCycles_whiskerRight_cyclesTensorι C D j m)))

@[reassoc (attr := simp)]
lemma whiskerRight_homologyπ_kunnethAux (j m : ℤ) :
    (C.homologyπ j ▷ D.cycles m) ≫ kunnethAux C D j m = cyclesTensorHomologyπ C D j m :=
  Cofork.IsColimit.π_desc (isColimitTensorRightHomologyπ C j (D.cycles m))

/-- The **cross product** on homology,
`κ_{j,m} : Hʲ(C) ⊗ Hᵐ(D) ⟶ H^{j+m}(C ⊗ D)`. -/
noncomputable def kunnethSummand (j m : ℤ) :
    C.homology j ⊗ D.homology m ⟶ (HomologicalComplex.tensorObj C D).homology (j + m) :=
  (isColimitTensorLeftHomologyπ D m (C.homology j)).desc
    (CokernelCofork.ofπ (kunnethAux C D j m) (by
      change (C.homology j ◁ D.toCycles (m - 1) m) ≫ kunnethAux C D j m = 0
      refine Cofork.IsColimit.hom_ext (isColimitTensorRightHomologyπ C j (D.X (m - 1))) ?_
      change (C.homologyπ j ▷ D.X (m - 1)) ≫ _ = (C.homologyπ j ▷ D.X (m - 1)) ≫ _
      rw [comp_zero, ← Category.assoc, ← MonoidalCategory.whisker_exchange, Category.assoc,
        whiskerRight_homologyπ_kunnethAux, cyclesTensorHomologyπ, cyclesTensorLift,
        ← Category.assoc, HomologicalComplex.comp_liftCycles]
      exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _
        (whiskerLeft_toCycles_cyclesTensorι C D j m)))

/-- The defining equation of the cross product: it is the unique map making the square with
`homologyπ ⊗ homologyπ` and the cycle-level cross product commute. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_homologyπ_kunnethSummand (j m : ℤ) :
    (C.homology j ◁ D.homologyπ m) ≫ kunnethSummand C D j m = kunnethAux C D j m :=
  Cofork.IsColimit.π_desc (isColimitTensorLeftHomologyπ D m (C.homology j))

/-- `homologyπ ▷ Z` is an epimorphism (it is a cokernel projection). -/
instance epi_whiskerRight_homologyπ (j : ℤ) (Z : ModuleCat.{u} k) :
    Epi (C.homologyπ j ▷ Z) :=
  Limits.epi_of_isColimit_cofork (isColimitTensorRightHomologyπ C j Z)

/-- `W ◁ homologyπ` is an epimorphism (it is a cokernel projection). -/
instance epi_whiskerLeft_homologyπ (m : ℤ) (W : ModuleCat.{u} k) :
    Epi (W ◁ D.homologyπ m) :=
  Limits.epi_of_isColimit_cofork (isColimitTensorLeftHomologyπ D m W)

/-- `homologyπ ⊗ homologyπ` is an epimorphism, so it can be cancelled on the left. -/
instance epi_tensorHom_homologyπ (j m : ℤ) :
    Epi (C.homologyπ j ⊗ₘ D.homologyπ m) := by
  rw [MonoidalCategory.tensorHom_def]
  infer_instance

/-- The workhorse identity: precomposing the cross product with `homologyπ ⊗ homologyπ`
recovers the cycle-level cross product. -/
@[reassoc (attr := simp)]
lemma homologyπ_tensorHom_kunnethSummand (j m : ℤ) :
    (C.homologyπ j ⊗ₘ D.homologyπ m) ≫ kunnethSummand C D j m
      = cyclesTensorHomologyπ C D j m := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, whiskerLeft_homologyπ_kunnethSummand,
    whiskerRight_homologyπ_kunnethAux]

end CrossProduct

section Naturality

variable {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}

/-- The summand inclusion of a tensor of cycles is natural. -/
lemma cyclesTensorι_naturality (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.cyclesMap f j ⊗ₘ HomologicalComplex.cyclesMap g m)
        ≫ cyclesTensorι C' D' j m
      = cyclesTensorι C D j m ≫ (HomologicalComplex.tensorHom f g).f (j + m) := by
  rw [cyclesTensorι, cyclesTensorι, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  congr 1
  rw [MonoidalCategory.tensorHom_def]
  rfl

/-- The cycle-level cross product is natural in both complexes. -/
lemma cyclesTensorLift_naturality (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.cyclesMap f j ⊗ₘ HomologicalComplex.cyclesMap g m)
        ≫ cyclesTensorLift C' D' j m
      = cyclesTensorLift C D j m
        ≫ HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom f g) (j + m) := by
  rw [← cancel_mono ((HomologicalComplex.tensorObj C' D').iCycles (j + m)),
    Category.assoc, Category.assoc, cyclesTensorLift_i, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, cyclesTensorLift_i, cyclesTensorι_naturality]

/-- The cycle-level cross product into homology is natural in both complexes. -/
lemma cyclesTensorHomologyπ_naturality (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.cyclesMap f j ⊗ₘ HomologicalComplex.cyclesMap g m)
        ≫ cyclesTensorHomologyπ C' D' j m
      = cyclesTensorHomologyπ C D j m
        ≫ HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) (j + m) := by
  rw [cyclesTensorHomologyπ, cyclesTensorHomologyπ, ← Category.assoc, cyclesTensorLift_naturality,
    Category.assoc, Category.assoc, HomologicalComplex.homologyπ_naturality]

/-- **Naturality of the cross product.** For chain maps `f : C ⟶ C'` and `g : D ⟶ D'`, the
square relating `κ_{j,m}` to `Hʲ(f) ⊗ Hᵐ(g)` and `H^{j+m}(f ⊗ g)` commutes. -/
lemma kunnethSummand_naturality (f : C ⟶ C') (g : D ⟶ D') (j m : ℤ) :
    (HomologicalComplex.homologyMap f j ⊗ₘ HomologicalComplex.homologyMap g m)
        ≫ kunnethSummand C' D' j m
      = kunnethSummand C D j m
        ≫ HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) (j + m) := by
  rw [← cancel_epi (C.homologyπ j ⊗ₘ D.homologyπ m), ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.homologyπ_naturality, ← MonoidalCategory.tensorHom_comp_tensorHom,
    Category.assoc, homologyπ_tensorHom_kunnethSummand, ← Category.assoc,
    homologyπ_tensorHom_kunnethSummand, cyclesTensorHomologyπ_naturality]

end Naturality

section Assembly

/-- The index type of the Künneth decomposition in total degree `i`: pairs `(j, m)` with
`j + m = i`. -/
abbrev KunnethIndex (i : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = i}

/-- The **Künneth map** in total degree `i`:
`∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D) ⟶ Hⁱ(C ⊗ D)`, assembled from the cross products `kunnethSummand`. -/
noncomputable def kunnethMap (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    (∐ fun p : KunnethIndex i => C.homology p.1.1 ⊗ D.homology p.1.2)
      ⟶ (HomologicalComplex.tensorObj C D).homology i :=
  Sigma.desc fun p => kunnethSummand C D p.1.1 p.1.2 ≫ eqToHom (by rw [p.2])

@[reassoc (attr := simp)]
lemma ι_kunnethMap (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) (p : KunnethIndex i) :
    Sigma.ι (fun p : KunnethIndex i => C.homology p.1.1 ⊗ D.homology p.1.2) p
        ≫ kunnethMap C D i
      = kunnethSummand C D p.1.1 p.1.2 ≫ eqToHom (by rw [p.2]) :=
  Sigma.ι_desc _ _

/-- On the diagonal `j + m = i` the Künneth map is literally the cross product. -/
lemma ι_kunnethMap_diagonal (C D : CochainComplex (ModuleCat.{u} k) ℤ) (j m : ℤ) :
    Sigma.ι (fun p : KunnethIndex (j + m) => C.homology p.1.1 ⊗ D.homology p.1.2)
        ⟨(j, m), rfl⟩ ≫ kunnethMap C D (j + m)
      = kunnethSummand C D j m := by
  rw [ι_kunnethMap]
  simp

/-! ### The two sides as bifunctors, and the Künneth natural transformation -/

/-- The source of the Künneth map as a bifunctor of the pair of complexes:
`(C, D) ↦ ∐_{j+m=i} Hʲ(C) ⊗ Hᵐ(D)`. -/
noncomputable def kunnethSource (i : ℤ) :
    (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ) ⥤
      ModuleCat.{u} k where
  obj X := ∐ fun p : KunnethIndex i => X.1.homology p.1.1 ⊗ X.2.homology p.1.2
  map {X Y} φ := Sigma.desc fun p =>
    (HomologicalComplex.homologyMap φ.1 p.1.1 ⊗ₘ HomologicalComplex.homologyMap φ.2 p.1.2) ≫
      Sigma.ι (fun p : KunnethIndex i => Y.1.homology p.1.1 ⊗ Y.2.homology p.1.2) p
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

@[reassoc (attr := simp)]
lemma ι_kunnethSource_map (i : ℤ)
    {X Y : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)}
    (φ : X ⟶ Y) (p : KunnethIndex i) :
    Sigma.ι (fun p : KunnethIndex i => X.1.homology p.1.1 ⊗ X.2.homology p.1.2) p
        ≫ (kunnethSource i).map φ
      = (HomologicalComplex.homologyMap φ.1 p.1.1 ⊗ₘ HomologicalComplex.homologyMap φ.2 p.1.2)
        ≫ Sigma.ι (fun p : KunnethIndex i => Y.1.homology p.1.1 ⊗ Y.2.homology p.1.2) p :=
  Sigma.ι_desc _ _

/-- The target of the Künneth map as a bifunctor of the pair of complexes:
`(C, D) ↦ Hⁱ(C ⊗ D)`. This is the monoidal tensor bifunctor on complexes followed by the
degree-`i` homology functor. -/
noncomputable def kunnethTarget (i : ℤ) :
    (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ) ⥤
      ModuleCat.{u} k :=
  MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} k) ℤ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) i

/-- **The Künneth map is a natural transformation of bifunctors.** Its component at `(C, D)`
is `kunnethMap C D i`, and naturality in each variable is `kunnethSummand_naturality`. -/
noncomputable def kunnethNatTrans (i : ℤ) :
    kunnethSource (k := k) i ⟶ kunnethTarget (k := k) i where
  app X := kunnethMap X.1 X.2 i
  naturality {X Y} φ := by
    refine Sigma.hom_ext _ _ fun p => ?_
    obtain ⟨⟨j, m⟩, rfl⟩ := p
    simp only [ι_kunnethSource_map_assoc, ι_kunnethMap, ι_kunnethMap_assoc, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    exact kunnethSummand_naturality φ.1 φ.2 j m

/-- Naturality of the Künneth map itself, unpacked from `kunnethNatTrans`. -/
lemma kunnethMap_naturality {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    (f : C ⟶ C') (g : D ⟶ D') (i : ℤ) :
    (kunnethSource i).map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C', D')) ≫ kunnethMap C' D' i
      = kunnethMap C D i
        ≫ HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) i :=
  (kunnethNatTrans i).naturality ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
    (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C', D'))

end Assembly

/-- `Etingof.tensorComplex` is by definition Mathlib's `HomologicalComplex.tensorObj`, so
`kunnethMap C D i` is also a morphism into `Hⁱ(tensorComplex C D)` and can be used directly by
clients phrased in terms of `tensorComplex` (such as `Problem7_8_7_iv`). -/
lemma tensorComplex_eq (C D : CochainComplex (ModuleCat.{u} k) ℤ) :
    tensorComplex C D = HomologicalComplex.tensorObj C D :=
  rfl

end Etingof
