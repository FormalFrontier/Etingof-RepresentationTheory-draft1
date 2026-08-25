/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import RepresentationTheory.Alignment.Attribute

/-!
# Functor endomorphisms of module categories

Develops dualization and natural endomorphism constructions for module categories.
-/

namespace RepresentationTheory.Module.FunctorEndomorphisms

set_option backward.isDefEq.respectTransparency false



universe u v


/-- A linear equivalence between a finite free module and its double dual. -/
noncomputable def moduleDoubleDualLinearEquiv
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Module.Free k V] :
    V ≃ₗ[k] Module.Dual k (Module.Dual k V) :=
  Module.evalEquiv k V


/-- Applying the dual-map construction twice and then evaluating agrees with evaluating after the original linear map. -/
theorem dualMap_dualMap_comp_eval
    (k : Type*) [CommSemiring k] (V W : Type*) [AddCommMonoid V] [AddCommMonoid W]
    [Module k V] [Module k W] (f : V →ₗ[k] W) :
    f.dualMap.dualMap ∘ₗ Module.Dual.eval k V = Module.Dual.eval k W ∘ₗ f :=
  Module.Dual.eval_naturality f


/-- A vector space is finite-dimensional exactly when it is linearly equivalent to its double dual. -/
@[source_ref "Chapter7/Example7.3.2" (role := supporting)]
theorem nonempty_doubleDualLinearEquiv_iff_finiteDimensional (k V : Type u)
    [Field k] [AddCommGroup V] [Module k V] :
    Nonempty (V ≃ₗ[k] Module.Dual k (Module.Dual k V)) ↔ FiniteDimensional k V := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
    by_contra! contra
    have h₁ : Module.rank k V < Module.rank k (Module.Dual k V) := by
      simpa using lift_rank_lt_rank_dual (K := k) (V := V) contra
    have hℵ : Cardinal.aleph0 ≤ Module.rank k (Module.Dual k V) := le_trans contra h₁.le
    have h₂ : Module.rank k (Module.Dual k V)
        < Module.rank k (Module.Dual k (Module.Dual k V)) := by
      simpa using lift_rank_lt_rank_dual (K := k) (V := Module.Dual k V) hℵ
    have heq : Module.rank k V = Module.rank k (Module.Dual k (Module.Dual k V)) := by
      simpa using e.lift_rank_eq
    exact absurd heq (lt_trans h₁ h₂).ne
  · haveI := h
    exact ⟨Module.evalEquiv k V⟩



open CategoryTheory in

/-- The double-dualization endofunctor on finitely generated modules. -/
noncomputable def finitelyGeneratedModuleDoubleDualFunctor (k : Type u) [Field k] :
    FGModuleCat.{u} k ⥤ FGModuleCat.{u} k where
  obj V := FGModuleCat.of k (Module.Dual k (Module.Dual k V))
  map {V W} f := FGModuleCat.ofHom f.hom.hom.dualMap.dualMap
  map_id V := by ext x; rfl
  map_comp f g := by ext x; rfl

open CategoryTheory in

/-- An isomorphism from the identity functor to double dualization on finitely generated modules. -/
@[source_ref "Chapter7/Example7.3.2" (role := supporting)]
noncomputable def finitelyGeneratedModuleDoubleDualIso (k : Type u) [Field k] :
    𝟭 (FGModuleCat.{u} k) ≅ finitelyGeneratedModuleDoubleDualFunctor k :=
  NatIso.ofComponents
    (fun V => (Module.evalEquiv k (V : Type u)).toFGModuleCatIso)
    (fun {V W} f => by
      ext x
      exact (LinearMap.congr_fun (Module.Dual.eval_naturality f.hom.hom) x).symm)




/-- A vector space is finite-dimensional exactly when it is linearly equivalent to its dual. -/
theorem nonempty_dualLinearEquiv_iff_finiteDimensional (k V : Type u)
    [Field k] [AddCommGroup V] [Module k V] :
    Nonempty (V ≃ₗ[k] Module.Dual k V) ↔ FiniteDimensional k V :=
  Basis.linearEquiv_dual_iff_finiteDimensional


/-- An automorphism-invariant linear map into the dual vanishes when the field contains a nonzero element whose square is not one. -/
theorem invariantLinearMapToDual_eq_zero_of_exists_square_ne_one
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (η : V →ₗ[k] Module.Dual k V)
    (hnat : ∀ a : V ≃ₗ[k] V, (a : V →ₗ[k] V).dualMap ∘ₗ η ∘ₗ (a : V →ₗ[k] V) = η)
    (hk : ∃ l : k, l ≠ 0 ∧ l ^ 2 ≠ 1) :
    η = 0 := by
  obtain ⟨l, hl0, hl1⟩ := hk
  
  set a : V ≃ₗ[k] V := LinearEquiv.smulOfNeZero k V l hl0 with ha
  ext u w
  
  have h := LinearMap.congr_fun (LinearMap.congr_fun (hnat a) u) w
  simp only [ha, LinearMap.comp_apply, LinearMap.dualMap_apply,
    LinearEquiv.coe_coe, LinearEquiv.smulOfNeZero_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at h
  
  have hzero : (l * l - 1) * η u w = 0 := by
    rw [sub_mul, one_mul, mul_assoc, h, sub_self]
  rcases mul_eq_zero.mp hzero with hcoeff | hval
  · exact absurd (by rw [sq]; exact sub_eq_zero.mp hcoeff) hl1
  · simpa using hval


/-- An automorphism-invariant linear map into the dual is not bijective when the field contains a nonzero element whose square is not one. -/
theorem invariantLinearMapToDual_not_bijective_of_exists_square_ne_one
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]
    (η : V →ₗ[k] Module.Dual k V)
    (hnat : ∀ a : V ≃ₗ[k] V, (a : V →ₗ[k] V).dualMap ∘ₗ η ∘ₗ (a : V →ₗ[k] V) = η)
    (hk : ∃ l : k, l ≠ 0 ∧ l ^ 2 ≠ 1) :
    ¬ Function.Bijective η := by
  intro hbij
  have hη0 : η = 0 := invariantLinearMapToDual_eq_zero_of_exists_square_ne_one η hnat hk
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (hbij.injective (by rw [hη0]; simp))

open CategoryTheory in

/-- The dualization endofunctor on the core of finitely generated modules. -/
noncomputable def finitelyGeneratedModuleDualFunctor (k : Type u) [Field k] :
    Core (FGModuleCat.{u} k) ⥤ Core (FGModuleCat.{u} k) where
  obj X := Core.mk (FGModuleCat.of k (Module.Dual k (X.of : Type u)))
  map {X Y} f := ⟨(FGModuleCat.isoToLinearEquiv f.iso).symm.dualMap.toFGModuleCatIso⟩




/-- The linear automorphism obtained by adding a multiple of a chosen vector using a functional that vanishes on it. -/
def transvection {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (f : Module.Dual k V) (x : V) (hx : f x = 0) : V ≃ₗ[k] V where
  toFun v := v + f v • x
  map_add' u v := by simp only [map_add, add_smul]; abel
  map_smul' c v := by simp only [map_smul, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]
  invFun v := v - f v • x
  left_inv v := by simp [hx]
  right_inv v := by simp [hx]

/-- A transvection sends a vector to itself plus its functional value times the chosen vector. -/
@[simp]
theorem transvection_apply {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (f : Module.Dual k V) (x : V) (hx : f x = 0) (v : V) :
    transvection f x hx v = v + f v • x := rfl


/-- In finite dimension at least three, any two vectors have a common nonzero annihilating functional. -/
theorem exists_nonzero_dual_vanishing_at_pair {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hdim : 3 ≤ Module.finrank k V) (u w : V) :
    ∃ f : Module.Dual k V, f ≠ 0 ∧ f u = 0 ∧ f w = 0 := by
  set φ : Module.Dual k V →ₗ[k] (Fin 2 → k) :=
    LinearMap.pi ![Module.Dual.eval k V u, Module.Dual.eval k V w] with hφ
  have hker : LinearMap.ker φ ≠ ⊥ := by
    intro h
    have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp h
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun] at hle
    omega
  obtain ⟨f, hfmem, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have h0 : φ f = 0 := hfmem
  exact ⟨f, hfne, by simpa [hφ] using congrFun h0 0, by simpa [hφ] using congrFun h0 1⟩


/-- An automorphism-invariant linear map into the dual vanishes in finite dimension at least three. -/
theorem invariantLinearMapToDual_eq_zero_of_finrank_ge_three
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hdim : 3 ≤ Module.finrank k V) (η : V →ₗ[k] Module.Dual k V)
    (hnat : ∀ a : V ≃ₗ[k] V, (a : V →ₗ[k] V).dualMap ∘ₗ η ∘ₗ (a : V →ₗ[k] V) = η) :
    η = 0 := by
  ext u w
  
  obtain ⟨f, hf0, hfu, hfw⟩ := exists_nonzero_dual_vanishing_at_pair hdim u w
  obtain ⟨q, hq⟩ : ∃ q : V, f q ≠ 0 := by
    by_contra hcon
    exact hf0 (LinearMap.ext fun v => by simpa using not_not.mp (not_exists.mp hcon v))
  have hp : f ((f q)⁻¹ • q) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hq]
  set p : V := (f q)⁻¹ • q with hpdef
  
  have h := LinearMap.congr_fun (LinearMap.congr_fun (hnat (transvection f u hfu)) p) w
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
    transvection_apply, hp, hfw, one_smul, zero_smul, add_zero, map_add,
    LinearMap.add_apply] at h
  
  simpa using h


/-- An automorphism-invariant linear map into the dual is not bijective in finite dimension at least three. -/
theorem invariantLinearMapToDual_not_bijective_of_finrank_ge_three
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hdim : 3 ≤ Module.finrank k V) (η : V →ₗ[k] Module.Dual k V)
    (hnat : ∀ a : V ≃ₗ[k] V, (a : V →ₗ[k] V).dualMap ∘ₗ η ∘ₗ (a : V →ₗ[k] V) = η) :
    ¬ Function.Bijective η := by
  intro hbij
  have hη0 : η = 0 := invariantLinearMapToDual_eq_zero_of_finrank_ge_three hdim η hnat
  have hV : Nontrivial V := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    omega
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (hbij.injective (by rw [hη0]; simp))

open CategoryTheory in

/-- No natural isomorphism exists from the identity functor to dualization on the core of finitely generated modules. -/
@[source_ref "Chapter7/Example7.3.2" (role := supporting)]
theorem isEmpty_iso_id_finitelyGeneratedModuleDualFunctor (k : Type u) [Field k] :
    IsEmpty (𝟭 (Core (FGModuleCat.{u} k)) ≅ finitelyGeneratedModuleDualFunctor k) := by
  refine ⟨fun ε => ?_⟩
  set X₀ : Core (FGModuleCat.{u} k) := Core.mk (FGModuleCat.of k (Fin 3 → k)) with hX
  
  set η : (Fin 3 → k) →ₗ[k] Module.Dual k (Fin 3 → k) := (ε.hom.app X₀).iso.hom.hom.hom with hη
  
  have hbij : Function.Bijective η :=
    (FGModuleCat.isoToLinearEquiv (ε.hom.app X₀).iso).bijective
  have hdim : 3 ≤ Module.finrank k (Fin 3 → k) := by simp
  
  refine invariantLinearMapToDual_not_bijective_of_finrank_ge_three hdim η (fun a => ?_) hbij
  
  have hn := ε.hom.naturality (X := X₀) (Y := X₀) (⟨a.toFGModuleCatIso⟩)
  have hn' := congrArg
    (fun p => (p.iso.hom.hom.hom : (Fin 3 → k) →ₗ[k] Module.Dual k (Fin 3 → k))) hn
  have rt : FGModuleCat.isoToLinearEquiv a.toFGModuleCatIso = a := by
    ext x; rfl
  have Fmap : ((finitelyGeneratedModuleDualFunctor k).map (⟨a.toFGModuleCatIso⟩ : X₀ ⟶ X₀)).iso
      = (FGModuleCat.isoToLinearEquiv a.toFGModuleCatIso).symm.dualMap.toFGModuleCatIso := rfl
  simp only [Functor.id_map, coreCategory_comp_iso, Iso.trans_hom, FGModuleCat.hom_hom_comp,
    LinearEquiv.toFGModuleCatIso_hom, Fmap, rt, ← hη] at hn'
  
  refine LinearMap.ext fun x => LinearMap.ext fun w => ?_
  have hx := LinearMap.congr_fun (LinearMap.congr_fun hn' x) (a w)
  have hx2 : (η ((a : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) x)) (a w) = (η x) (a.symm (a w)) := hx
  rw [LinearEquiv.symm_apply_apply] at hx2
  exact hx2




/-- A natural family of scalar-restricted endomorphisms acts by its value on one in the regular module. -/
theorem naturalRestrictionEnd_eq_smul
    {k : Type v} {A : Type u} [CommRing k] [Ring A] [Algebra k A]
    (η : ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M],
          M →ₗ[k] M)
    (hnat : ∀ {M N : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
              [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
              (f : M →ₗ[A] N),
              (f.restrictScalars k).comp (η M) = (η N).comp (f.restrictScalars k))
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] (m : M) :
    η M m = η A 1 • m := by
  
  have h := hnat (M := A) (N := M) (LinearMap.toSpanSingleton A M m)
  
  have h1 := LinearMap.congr_fun h 1
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, one_smul] using h1.symm


/-- Successive actions by two algebra elements equal the action by their product. -/
theorem smul_smul
    {k : Type v} {A : Type u} [CommRing k] [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (a b : A) (m : M) :
    a • b • m = (a * b) • m :=
  (mul_smul a b m).symm




/-- A natural family of module endomorphisms acts by its value at one in the regular module. -/
theorem naturalModuleIdentityEnd_eq_smul
    {A : Type u} [Ring A]
    (η : ∀ (M : Type u) [AddCommGroup M] [Module A M], M →ₗ[A] M)
    (hnat : ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
              (f : M →ₗ[A] N), f.comp (η M) = (η N).comp f)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    η M m = η A 1 • m := by
  
  have h := hnat (M := A) (N := M) (LinearMap.toSpanSingleton A M m)
  
  have h1 := LinearMap.congr_fun h 1
  simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul] using h1.symm


/-- The value at one of a natural family of module endomorphisms commutes with every ring element. -/
theorem naturalModuleIdentityEnd_one_mem_center
    {A : Type u} [Ring A]
    (η : ∀ (M : Type u) [AddCommGroup M] [Module A M], M →ₗ[A] M)
    (hnat : ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
              (f : M →ₗ[A] N), f.comp (η M) = (η N).comp f)
    (b : A) : η A 1 * b = b * η A 1 := by
  
  have hdet := naturalModuleIdentityEnd_eq_smul η hnat (M := A) b
  
  have hlin : η A (b • (1 : A)) = b • η A 1 := (η A).map_smul b 1
  rw [smul_eq_mul, mul_one] at hlin
  rw [hlin] at hdet
  simpa only [smul_eq_mul] using hdet.symm



open CategoryTheory in

/-- The functor that restricts modules along the given algebra structure. -/
noncomputable abbrev restrictionFunctor (k : Type v) (A : Type u)
    [CommRing k] [Ring A] [Algebra k A] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A)

open CategoryTheory in

/-- Turns an algebra element into the natural endomorphism of scalar restriction given by its action. -/
noncomputable def algebraToRestrictionEnd {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (a : A) :
    End (restrictionFunctor k A) where
  app M :=
    ModuleCat.ofHom (X := (restrictionFunctor k A).obj M)
      (Y := (restrictionFunctor k A).obj M)
      { toFun := fun m => a • (m : M)
        map_add' := fun x y => smul_add a x y
        map_smul' := fun c m => by
          simp only [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
          rw [← mul_smul, ← mul_smul, Algebra.commutes] }
  naturality M N f := by
    ext m
    exact (f.hom.map_smul a m).symm

open CategoryTheory in

/-- Extracts the algebra element determined by a natural endomorphism of the scalar-restriction functor. -/
noncomputable def restrictionEndToAlgebra {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (η : End (restrictionFunctor k A)) : A :=
  (η.app (ModuleCat.of A A)).hom (1 : A)

open CategoryTheory in

/-- Each component of a scalar-restriction endomorphism acts by the extracted algebra element. -/
theorem restrictionEnd_app_eq_smul {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (η : End (restrictionFunctor k A))
    (M : ModuleCat.{u} A) (m : M) :
    (η.app M).hom m = restrictionEndToAlgebra η • m := by
  have h := η.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))
  have h1 := congrArg (fun g => (ModuleCat.Hom.hom g) (1 : A)) h
  
  have h2 : (η.app M).hom ((1 : A) • m) = restrictionEndToAlgebra η • m := h1
  rwa [one_smul] at h2

open CategoryTheory in

/-- Extracting the algebra element from the scalar-restriction endomorphism induced by an element returns that element. -/
theorem restrictionEndToAlgebra_algebraToRestrictionEnd {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (a : A) :
    restrictionEndToAlgebra (algebraToRestrictionEnd (k := k) a) = a :=
  
  mul_one a

open CategoryTheory in

/-- The ring equivalence between natural endomorphisms of scalar restriction and the acting algebra. -/
@[source_ref "Chapter7/Example7.3.2" (role := primary)]
noncomputable def restrictionEndRingEquivAlgebra (k : Type v) (A : Type u)
    [CommRing k] [Ring A] [Algebra k A] :
    End (restrictionFunctor k A) ≃+* A where
  toFun := restrictionEndToAlgebra
  invFun := algebraToRestrictionEnd
  left_inv η :=
    NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun m =>
      (restrictionEnd_app_eq_smul η M m).symm))
  right_inv a := restrictionEndToAlgebra_algebraToRestrictionEnd a
  map_add' _ _ := rfl
  map_mul' η θ :=
    
    
    restrictionEnd_app_eq_smul η (ModuleCat.of A A)
      ((θ.app (ModuleCat.of A A)).hom (1 : A))



open CategoryTheory in

/-- Turns a central ring element into a natural endomorphism of the identity functor on modules. -/
def centerToModuleIdentityEnd {A : Type u} [Ring A] (c : Subring.center A) :
    End (𝟭 (ModuleCat.{u} A)) where
  app M :=
    ModuleCat.ofHom
      { toFun := fun m => (c : A) • (m : M)
        map_add' := fun x y => smul_add (c : A) x y
        map_smul' := fun b m => by
          simp only [RingHom.id_apply, ← mul_smul]
          rw [Subring.mem_center_iff.mp c.2 b] }
  naturality M N f := by
    ext m
    exact (f.hom.map_smul (c : A) m).symm

open CategoryTheory in

/-- Extracts the ring element determined by a natural endomorphism of the identity functor on modules. -/
def moduleIdentityEndToRing {A : Type u} [Ring A] (η : End (𝟭 (ModuleCat.{u} A))) : A :=
  (η.app (ModuleCat.of A A)).hom (1 : A)

open CategoryTheory in

/-- Each component of a module identity-functor endomorphism acts by the extracted ring element. -/
theorem moduleIdentityEnd_app_eq_smul {A : Type u} [Ring A]
    (η : End (𝟭 (ModuleCat.{u} A))) (M : ModuleCat.{u} A) (m : M) :
    (η.app M).hom m = moduleIdentityEndToRing η • m := by
  have h := η.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))
  have h1 := congrArg (fun g => (ModuleCat.Hom.hom g) (1 : A)) h
  have h2 : (η.app M).hom ((1 : A) • m) = moduleIdentityEndToRing η • m := h1
  rwa [one_smul] at h2

open CategoryTheory in

/-- The ring element extracted from a natural endomorphism of the module identity functor is central. -/
theorem moduleIdentityEndToRing_mem_center {A : Type u} [Ring A] (η : End (𝟭 (ModuleCat.{u} A))) :
    moduleIdentityEndToRing η ∈ Subring.center A := by
  refine Subring.mem_center_iff.mpr fun b => ?_
  
  have hdet : ((η.app (ModuleCat.of A A)).hom (b : A) : A) = moduleIdentityEndToRing η * b :=
    moduleIdentityEnd_app_eq_smul η (ModuleCat.of A A) b
  
  have hlin : ((η.app (ModuleCat.of A A)).hom (b * (1 : A)) : A) = b * moduleIdentityEndToRing η :=
    (η.app (ModuleCat.of A A)).hom.map_smul b (1 : A)
  rw [mul_one] at hlin
  exact hlin.symm.trans hdet

open CategoryTheory in

/-- Extracting the ring element from the identity-functor endomorphism induced by a central element returns that element. -/
theorem moduleIdentityEndToRing_centerToModuleIdentityEnd {A : Type u} [Ring A] (c : Subring.center A) :
    moduleIdentityEndToRing (centerToModuleIdentityEnd c) = (c : A) :=
  
  mul_one (c : A)

open CategoryTheory in

/-- The ring equivalence between natural endomorphisms of the module identity functor and the ring center. -/
@[source_ref "Chapter7/Example7.3.2" (role := primary)]
def moduleIdentityEndRingEquivCenter (A : Type u) [Ring A] :
    End (𝟭 (ModuleCat.{u} A)) ≃+* Subring.center A where
  toFun η := ⟨moduleIdentityEndToRing η, moduleIdentityEndToRing_mem_center η⟩
  invFun c := centerToModuleIdentityEnd c
  left_inv η :=
    NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun m =>
      (moduleIdentityEnd_app_eq_smul η M m).symm))
  right_inv c := Subtype.ext (moduleIdentityEndToRing_centerToModuleIdentityEnd c)
  map_add' _ _ := rfl
  map_mul' η θ :=
    Subtype.ext (moduleIdentityEnd_app_eq_smul η (ModuleCat.of A A)
      ((θ.app (ModuleCat.of A A)).hom (1 : A)))

end RepresentationTheory.Module.FunctorEndomorphisms
