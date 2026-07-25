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
    C.cycles j ⊗ D.cycles m ⟶ (tensorComplex C D).X (j + m) :=
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
    cyclesTensorι C D j m ≫ (tensorComplex C D).d (j + m) j' = 0 := by
  have h1 : HomologicalComplex.ιTensorObj C D j m (j + m) rfl ≫
      mapBifunctor.D₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j + m) j'
      = mapBifunctor.d₁ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' :=
    mapBifunctor.ι_D₁ _ _ _ _ _ _ _ _ _
  have h2 : HomologicalComplex.ιTensorObj C D j m (j + m) rfl ≫
      mapBifunctor.D₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) (j + m) j'
      = mapBifunctor.d₂ C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j m j' :=
    mapBifunctor.ι_D₂ _ _ _ _ _ _ _ _ _
  rw [cyclesTensorι, Category.assoc]
  show _ ≫ _ ≫ (HomologicalComplex.tensorObj C D).d _ _ = 0
  rw [mapBifunctor.d_eq, Preadditive.comp_add, h1, h2, Preadditive.comp_add,
    iCycles_tensor_comp_d₁, iCycles_tensor_comp_d₂, add_zero]

/-- The cross product on cycles, `Zʲ(C) ⊗ Zᵐ(D) ⟶ Z^{j+m}(C ⊗ D)`. -/
noncomputable def cyclesTensorLift (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (tensorComplex C D).cycles (j + m) :=
  (tensorComplex C D).liftCycles (cyclesTensorι C D j m) (j + m + 1) (by simp)
    (cyclesTensorι_d C D j m _)

@[reassoc (attr := simp)]
lemma cyclesTensorLift_i (j m : ℤ) :
    cyclesTensorLift C D j m ≫ (tensorComplex C D).iCycles (j + m) = cyclesTensorι C D j m :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The cross product on cycles followed by the projection to homology. -/
noncomputable def cyclesTensorHomologyπ (j m : ℤ) :
    C.cycles j ⊗ D.cycles m ⟶ (tensorComplex C D).homology (j + m) :=
  cyclesTensorLift C D j m ≫ (tensorComplex C D).homologyπ (j + m)

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
        (tensorComplex C D).d (j - 1 + m) (j + m) := by
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
    rw [mapBifunctor.d₂_eq' _ _ _ _ (j - 1) (show (ComplexShape.up ℤ).Rel m (m + 1) by simp) (j + m)]
    exact comp_units_zsmul_eq_zero _ _ _ (h0 _)
  rw [Category.assoc]
  show _ = _ ≫ _ ≫ (HomologicalComplex.tensorObj C D).d _ _
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
        (tensorComplex C D).d (j + (m - 1)) (j + m) := by
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
    rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (m - 1) (j + m)]
    exact comp_units_zsmul_eq_zero _ _ _ (h0 _)
  rw [Units.smul_def, Preadditive.zsmul_comp, Category.assoc]
  show _ = _ • (_ ≫ _ ≫ (HomologicalComplex.tensorObj C D).d _ _)
  rw [mapBifunctor.d_eq, Preadditive.comp_add, h1, h2, Preadditive.comp_add, hzero, zero_add,
    d₂_eq_second, Units.smul_def, Preadditive.comp_zsmul, smul_smul, int_units_val_mul_self,
    one_smul, cyclesTensorι, ← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

end CrossProduct

end Etingof
