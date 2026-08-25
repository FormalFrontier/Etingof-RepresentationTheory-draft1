import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_4
import EtingofRepresentationTheory.Chapter8.Problem8_2_6_Core

set_option backward.isDefEq.respectTransparency false

/-!
# Additivity of `Tor` and `Ext`

Problem 8.2.7 computes `Torᵢ(M, N)` and `Extⁱ(M, N)` for finitely generated modules `M`, `N`
over a PID. The book's hint is "reduce to the case of cyclic groups using the classification
theorem": a finitely generated module over a PID is a finite direct sum of a free module and
cyclic torsion modules, and `Tor`/`Ext` are additive in each argument, so the computation
reduces to the cyclic and free building blocks proved in `Chapter8/Problem8_2_7.lean`.

This file supplies the additivity half of that reduction for `Tor`. For `Ext` nothing is needed:
`Etingof.Ext` is a reducible abbreviation for `CategoryTheory.Abelian.Ext`, and Mathlib already
proves additivity in both variables, as `Abelian.Ext.biprodAddEquiv` / `Ext.biproductAddEquiv`
(first variable) and `Abelian.Ext.addEquivBiprod` / `Ext.addEquivBiproduct` (second variable).
Those may be applied to `Etingof.Ext` directly.

## Main results

* `CategoryTheory.projectiveResolutions_additive`: taking projective resolutions is an additive
  functor `C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`. Two lifts of the same map are
  homotopic, and `lift f + lift g` is a lift of `f + g`, so the two agree in the homotopy
  category. Mathlib knows the functor laws for `projectiveResolutions` but not this one.
* `CategoryTheory.Functor.leftDerived_additive`: consequently every left derived functor
  `F.leftDerived n` of an additive functor is additive, being the composite of the (now additive)
  resolution functor with `F.mapHomotopyCategory` and a homology functor. Additive functors
  preserve finite biproducts, so this is exactly what makes derived functors additive in the
  sense used by the book.
* `Etingof.torFunctor_additive`, `Etingof.torBiprodIso`, `Etingof.torBiproductIso`:
  `Torₙᴬ(-, N)` is additive, hence `Torₙᴬ(M₁ ⊕ M₂, N) ≅ Torₙᴬ(M₁, N) ⊕ Torₙᴬ(M₂, N)` and, for a
  finite index type, `Torₙᴬ(⨁ i, M i, N) ≅ ⨁ i, Torₙᴬ(M i, N)`.

Additivity of `Tor` in its *second* argument is not covered here: `Torₙᴬ(M, -)` is not the
value of a single left derived functor in the present set-up (the second argument is baked into
`Etingof.tensorRightFunctor` before deriving), so it needs a separate argument.
-/

universe u v u' v'

namespace CategoryTheory

open Limits

/-! ### The resolution functor is additive -/

section ProjectiveResolutions

variable (C : Type u) [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

/-- **Taking projective resolutions is additive.** `ProjectiveResolution.lift f P Q` is only well
defined up to homotopy, and `lift f P Q + lift g P Q` is *a* lift of `f + g`, so it agrees with
`lift (f + g) P Q` in the homotopy category. -/
instance projectiveResolutions_additive : (projectiveResolutions C).Additive where
  map_add {X Y f g} := by
    dsimp only [projectiveResolutions]
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    refine ProjectiveResolution.liftHomotopy (f + g) _ _ (by simp) ?_
    rw [Preadditive.add_comp, ProjectiveResolution.lift_commutes,
      ProjectiveResolution.lift_commutes, ← Preadditive.comp_add, ← Functor.map_add]

end ProjectiveResolutions

/-! ### Left derived functors are additive -/

section LeftDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **A left derived functor is additive.** `F.leftDerived n` is by definition the composite
`projectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ homologyFunctor _ _ n`, and all three
factors are additive. -/
instance Functor.leftDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).Additive := by
  dsimp only [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

omit [HasProjectiveResolutions C] in
/-- `NatTrans.mapHomologicalComplex` is additive in the natural transformation: it acts degreewise
by the components of `α`. -/
lemma NatTrans.mapHomologicalComplex_add {ι : Type*} (c : ComplexShape ι) {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α β : F ⟶ G) :
    NatTrans.mapHomologicalComplex (α + β) c =
      NatTrans.mapHomologicalComplex α c + NatTrans.mapHomologicalComplex β c := by
  ext K i
  rfl

/-- **`NatTrans.leftDerived` is additive in the natural transformation.** Mathlib records that it
is compatible with identities and composition; this is the remaining bilinearity fact, and it is
what makes `Torₙᴬ(M, -)` additive in its second argument. -/
lemma NatTrans.leftDerived_add {F G : C ⥤ D} [F.Additive] [G.Additive] (α β : F ⟶ G) (n : ℕ) :
    NatTrans.leftDerived (α + β) n = NatTrans.leftDerived α n + NatTrans.leftDerived β n := by
  ext X
  rw [ProjectiveResolution.leftDerived_app_eq (α + β) (projectiveResolution X) n,
    NatTrans.mapHomologicalComplex_add]
  change _ ≫ (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
      ((NatTrans.mapHomologicalComplex α _).app _ +
        (NatTrans.mapHomologicalComplex β _).app _) ≫ _ = _
  rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
    ← ProjectiveResolution.leftDerived_app_eq α (projectiveResolution X) n,
    ← ProjectiveResolution.leftDerived_app_eq β (projectiveResolution X) n]
  rfl

end LeftDerived

end CategoryTheory

/-! ### `Tor` is additive in its first argument -/

namespace Etingof

open CategoryTheory Limits

variable (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ)

/-- `Torₙᴬ(-, N)` is an additive functor: it is a left derived functor of the additive functor
`- ⊗_A N`. -/
instance torFunctor_additive : (TorFunctor.{u} A N n).Additive := by
  dsimp only [TorFunctor]
  infer_instance

/-- **`Tor` is additive in its first argument.**
`Torₙᴬ(M₁ ⊕ M₂, N) ≅ Torₙᴬ(M₁, N) ⊕ Torₙᴬ(M₂, N)`. -/
noncomputable def torBiprodIso (M₁ M₂ : ModuleCat.{u} Aᵐᵒᵖ) :
    Tor.{u} A N (M₁ ⊞ M₂) n ≅ Tor.{u} A N M₁ n ⊞ Tor.{u} A N M₂ n :=
  letI := preservesBinaryBiproduct_of_preservesBiproduct (TorFunctor.{u} A N n) M₁ M₂
  (TorFunctor.{u} A N n).mapBiprod M₁ M₂

/-- **`Tor` commutes with finite direct sums in its first argument.**
`Torₙᴬ(⨁ i, M i, N) ≅ ⨁ i, Torₙᴬ(M i, N)` for a finite index type. This is the form in which the
reduction of Problem 8.2.7 to the cyclic and free building blocks uses additivity. -/
noncomputable def torBiproductIso {ι : Type} [Finite ι] (M : ι → ModuleCat.{u} Aᵐᵒᵖ) :
    Tor.{u} A N (⨁ M) n ≅ ⨁ ((TorFunctor.{u} A N n).obj ∘ M) :=
  (TorFunctor.{u} A N n).mapBiproduct M

/-! ### `Tor` is additive in its second argument

`Torₙᴬ(M, -)` is not a left derived functor in the present set-up — the second argument is baked
into `tensorRightFunctor` before deriving — so additivity in it has to be assembled by hand from
the second-argument functoriality `Etingof.torSndMap` of Problem 8.2.6. The three functoriality
laws below (identity, composition, additivity) say exactly that `N ↦ Torₙᴬ(M, N)` is an additive
assignment on morphisms, and they let the biproduct identities of `N₁ × N₂` be transported. -/

section SecondArgument

variable {A}
variable {N₁ N₂ : Type u} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]

/-- Two natural transformations `- ⊗_A N ⟶ - ⊗_A N'` agree as soon as their components agree on
pure tensors. -/
private lemma tensorRightNatTrans_ext {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N']
    {α β : tensorRightFunctor A N ⟶ tensorRightFunctor A N'}
    (h : ∀ (M : ModuleCat.{u} Aᵐᵒᵖ) (m : M) (x : N),
      α.app M (TensorProduct.tmul ℤ m x : tensorOver A N M)
        = β.app M (TensorProduct.tmul ℤ m x : tensorOver A N M)) : α = β := by
  ext M z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => simp
  | tmul m x => exact h M m x
  | add a b ha hb =>
    rw [show ((a + b : TensorProduct ℤ M N) : tensorOver A N M)
          = (a : tensorOver A N M) + b from map_add (QuotientAddGroup.mk' _) a b,
      map_add, map_add, ha, hb]

@[simp]
lemma tensorRightNatTrans_id (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] :
    tensorRightNatTrans A (LinearMap.id : N →ₗ[A] N) = 𝟙 (tensorRightFunctor A N) :=
  tensorRightNatTrans_ext fun _ _ _ => rfl

@[simp]
lemma tensorRightNatTrans_comp {N₃ : Type u} [AddCommGroup N₃] [Module A N₃]
    (g : N₁ →ₗ[A] N₂) (g' : N₂ →ₗ[A] N₃) :
    tensorRightNatTrans A (g'.comp g) =
      tensorRightNatTrans A g ≫ tensorRightNatTrans A g' :=
  tensorRightNatTrans_ext fun _ _ _ => rfl

@[simp]
lemma tensorRightNatTrans_add (g g' : N₁ →ₗ[A] N₂) :
    tensorRightNatTrans A (g + g') =
      tensorRightNatTrans A g + tensorRightNatTrans A g' :=
  tensorRightNatTrans_ext fun M m x => by
    change (TensorProduct.tmul ℤ m (g x + g' x) : tensorOver A N₂ M) = _
    rw [TensorProduct.tmul_add]
    exact map_add (QuotientAddGroup.mk' (balancedSubgroup A N₂ M)) _ _

variable (M : ModuleCat.{u} Aᵐᵒᵖ)

@[simp]
lemma torSndMap_id (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (n : ℕ) (M : ModuleCat.{u} Aᵐᵒᵖ) :
    torSndMap A (LinearMap.id : N →ₗ[A] N) n M = 𝟙 _ := by
  rw [torSndMap, tensorRightNatTrans_id, NatTrans.leftDerived_id]
  rfl

@[simp]
lemma torSndMap_comp {N₃ : Type u} [AddCommGroup N₃] [Module A N₃]
    (g : N₁ →ₗ[A] N₂) (g' : N₂ →ₗ[A] N₃) (n : ℕ) :
    torSndMap A (g'.comp g) n M = torSndMap A g n M ≫ torSndMap A g' n M := by
  rw [torSndMap, tensorRightNatTrans_comp, NatTrans.leftDerived_comp]
  rfl

@[simp]
lemma torSndMap_add (g g' : N₁ →ₗ[A] N₂) (n : ℕ) :
    torSndMap A (g + g') n M = torSndMap A g n M + torSndMap A g' n M := by
  rw [torSndMap, tensorRightNatTrans_add, NatTrans.leftDerived_add]
  rfl

/-- `g ↦ Torₙᴬ(M, g)` as an additive map on `Hom_A(N₁, N₂)`. -/
noncomputable def torSndAddHom (n : ℕ) :
    (N₁ →ₗ[A] N₂) →+ (Tor.{u} A N₁ M n ⟶ Tor.{u} A N₂ M n) :=
  AddMonoidHom.mk' (fun g => torSndMap A g n M) fun g g' => torSndMap_add M g g' n

@[simp]
lemma torSndMap_zero (n : ℕ) :
    torSndMap A (0 : N₁ →ₗ[A] N₂) n M = 0 :=
  (torSndAddHom M n).map_zero

/-- **`Tor` is additive in its second argument.**
`Torₙᴬ(M, N₁ ⊕ N₂) ≅ Torₙᴬ(M, N₁) ⊕ Torₙᴬ(M, N₂)`, with the isomorphism given by the maps
induced by the two projections and the two inclusions of `N₁ × N₂`. -/
noncomputable def torProdIso (n : ℕ) :
    Tor.{u} A (N₁ × N₂) M n ≅ Tor.{u} A N₁ M n ⊞ Tor.{u} A N₂ M n where
  hom := biprod.lift (torSndMap A (LinearMap.fst A N₁ N₂) n M)
    (torSndMap A (LinearMap.snd A N₁ N₂) n M)
  inv := biprod.desc (torSndMap A (LinearMap.inl A N₁ N₂) n M)
    (torSndMap A (LinearMap.inr A N₁ N₂) n M)
  hom_inv_id := by
    rw [biprod.lift_desc, ← torSndMap_comp, ← torSndMap_comp, ← torSndMap_add]
    rw [show (LinearMap.inl A N₁ N₂).comp (LinearMap.fst A N₁ N₂) +
        (LinearMap.inr A N₁ N₂).comp (LinearMap.snd A N₁ N₂) = LinearMap.id from by
      ext x <;> simp]
    exact torSndMap_id A (N₁ × N₂) n M
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [← torSndMap_comp, LinearMap.fst_comp_inl, LinearMap.snd_comp_inl,
        LinearMap.fst_comp_inr, LinearMap.snd_comp_inr]

end SecondArgument

/-! ### `Tor` commutes with finite direct sums in its second argument

The finite-index form of `Etingof.torProdIso`. The direct sum of a finite family of `A`-modules is
realised as the product type `∀ i, N i`, whose projections and inclusions satisfy
`∑ i, (single i) ∘ (proj i) = id` and `(proj j) ∘ (single i) = if i = j then id else 0`; these are
exactly the two identities the biproduct `⨁ i, Torₙᴬ(M, N i)` needs. -/

section FiniteSecondArgument

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (N : ι → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]

/-- **`Tor` commutes with finite direct sums in its second argument.**
`Torₙᴬ(M, ⨁ i, N i) ≅ ⨁ i, Torₙᴬ(M, N i)` for a finite index type, with the isomorphism given by
the maps induced by the projections `LinearMap.proj i` and the inclusions `LinearMap.single A N i`
of `∀ i, N i`. -/
noncomputable def torPiIso (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) :
    Tor.{u} A (∀ i, N i) M n ≅ ⨁ fun i => Tor.{u} A (N i) M n where
  hom := biproduct.lift fun i => torSndMap A (LinearMap.proj i) n M
  inv := biproduct.desc fun i => torSndMap A (LinearMap.single A N i) n M
  hom_inv_id := by
    rw [biproduct.lift_desc]
    have h : ∀ i : ι,
        torSndMap A (LinearMap.proj (R := A) (φ := N) i) n M ≫
            torSndMap A (LinearMap.single A N i) n M
          = torSndAddHom M n ((LinearMap.single A N i).comp (LinearMap.proj i)) :=
      fun i => (torSndMap_comp M _ _ n).symm
    simp_rw [h]
    rw [← map_sum (torSndAddHom M n),
      show ∑ i : ι, (LinearMap.single A N i).comp (LinearMap.proj i) = LinearMap.id from
        LinearMap.ext fun x => by
          simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
            LinearMap.coe_single, LinearMap.id_apply]
          exact Finset.univ_sum_single x]
    exact torSndMap_id A (∀ i, N i) n M
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, ← torSndMap_comp,
      Category.comp_id]
    rcases eq_or_ne i j with rfl | hij
    · rw [LinearMap.proj_comp_single_same, biproduct.ι_π_self, torSndMap_id]
    · rw [LinearMap.proj_comp_single_ne A N j i hij.symm, torSndMap_zero,
        biproduct.ι_π_ne _ hij]

end FiniteSecondArgument

end Etingof
