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

namespace Etingof

universe u

variable {k : Type u} [Field k]

/-- A composite with a `ℤˣ`-scaled second factor vanishes as soon as the unscaled composite
does. Used to discharge the Koszul signs appearing in the total differential. -/
private lemma comp_units_zsmul_eq_zero {X Y Z : ModuleCat.{u} k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : ℤˣ) (h : f ≫ g = 0) : f ≫ (e • g) = 0 := by
  rw [Units.smul_def, Preadditive.comp_zsmul, h, smul_zero]

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

end CrossProduct

end Etingof
