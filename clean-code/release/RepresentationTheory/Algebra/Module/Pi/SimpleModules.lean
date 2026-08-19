/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RepresentationTheory.Alignment.Attribute

/-!
# Simple modules over finite products of rings

Develops indexed simple modules over finite products and full matrix algebras.
-/

namespace RepresentationTheory.Algebra.Module.Pi.SimpleModules

section PartA

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]
  (V : Type*) [AddCommGroup V] [Module (∀ i, 𝒜 i) V]


/-- Each component idempotent commutes with every element of the product ring. -/
theorem single_one_commute (i : Fin r) (a : ∀ i, 𝒜 i) :
    (Pi.single i 1 : ∀ i, 𝒜 i) * a = a * Pi.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]


/-- An auxiliary family of linear endomorphisms of a product-ring module, indexed by the factors. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
def indexedAuxiliaryEndomorphism (i : Fin r) : V →ₗ[∀ i, 𝒜 i] V where
  toFun v := (Pi.single i 1 : ∀ i, 𝒜 i) • v
  map_add' v w := smul_add _ _ _
  map_smul' a v := by
    simp only [RingHom.id_apply, smul_smul]
    rw [single_one_commute 𝒜 i a]


/-- Component idempotents multiply to the selected idempotent at equal indices and to zero at distinct indices. -/
@[source_ref "Chapter3/Problem3.3.3" (role := primary)]
theorem single_one_mul_single_one (i j : Fin r) :
    (Pi.single i 1 : ∀ i, 𝒜 i) * Pi.single j 1 = if i = j then Pi.single i 1 else 0 := by
  by_cases h : i = j
  · rw [if_pos h]; subst h; ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  · rw [if_neg h]; ext k
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hk : k = i
    · subst hk; simp [Ne.symm h]
    · simp [hk]


/-- The sum of the component idempotents in a finite product of rings is one. -/
@[source_ref "Chapter3/Problem3.3.3" (role := primary)]
theorem sum_single_one : (∑ i, (Pi.single i 1 : ∀ i, 𝒜 i)) = 1 := by
  simpa using Finset.univ_sum_single (1 : ∀ i, 𝒜 i)


/-- Successive actions by two component idempotents equal the first action when their indices agree and vanish otherwise. -/
theorem single_one_smul_single_one_smul (i j : Fin r) (v : V) :
    (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single j 1 : ∀ i, 𝒜 i) • v)
      = if i = j then (Pi.single i 1 : ∀ i, 𝒜 i) • v else 0 := by
  rw [← mul_smul, single_one_mul_single_one]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_smul]


/-- Every vector in a product-ring module is the sum of its component-idempotent actions. -/
theorem sum_single_one_smul (v : V) : (∑ i, (Pi.single i 1 : ∀ i, 𝒜 i) • v) = v := by
  rw [← Finset.sum_smul, sum_single_one, one_smul]


/-- A vector belongs to an indexed auxiliary endomorphism range exactly when the corresponding component idempotent fixes it. -/
theorem mem_indexedAuxiliaryEndomorphism_range_iff (i : Fin r) (v : V) :
    v ∈ LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) ↔ (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single i 1 : ∀ i, 𝒜 i) • w)
        = (Pi.single i 1 : ∀ i, 𝒜 i) • w
    rw [single_one_smul_single_one_smul, if_pos rfl]
  · intro h
    exact ⟨v, h⟩


/-- An indexed auxiliary endomorphism range is the whole module exactly when the corresponding component idempotent fixes every vector. -/
theorem indexedAuxiliaryEndomorphism_range_eq_top_iff (i : Fin r) :
    LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) = ⊤ ↔ ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
  rw [Submodule.eq_top_iff']
  exact ⟨fun h v => (mem_indexedAuxiliaryEndomorphism_range_iff 𝒜 V i v).1 (h v),
         fun h v => (mem_indexedAuxiliaryEndomorphism_range_iff 𝒜 V i v).2 (h v)⟩


/-- An indexed auxiliary endomorphism range is zero exactly when the corresponding component idempotent annihilates every vector. -/
theorem indexedAuxiliaryEndomorphism_range_eq_bot_iff (i : Fin r) :
    LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) = ⊥ ↔ ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = 0 := by
  rw [LinearMap.range_eq_bot, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply]
  rfl


/-- A module over a finite product of rings is simple exactly when one indexed auxiliary endomorphism range is simple over the product and every other such range is zero. -/
theorem isSimpleModule_pi_iff_exists_auxiliaryRange :
    IsSimpleModule (∀ i, 𝒜 i) V ↔
      ∃ i, IsSimpleModule (∀ i, 𝒜 i) (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) ∧
        ∀ j, j ≠ i → LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V j) = ⊥ := by
  constructor
  · 
    
    intro hV
    haveI := hV
    haveI : Nontrivial V := IsSimpleModule.nontrivial (∀ i, 𝒜 i) V
    have hclass : ∀ k, LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V k) = ⊥ ∨
        LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V k) = ⊤ := fun k => eq_bot_or_eq_top _
    have hexists : ∃ i, LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) = ⊤ := by
      by_contra h
      simp only [not_exists] at h
      have hbot : ∀ k, LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V k) = ⊥ :=
        fun k => (hclass k).resolve_right (h k)
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine hv ?_
      rw [← sum_single_one_smul 𝒜 V v]
      exact Finset.sum_eq_zero fun k _ => (indexedAuxiliaryEndomorphism_range_eq_bot_iff 𝒜 V k).1 (hbot k) v
    obtain ⟨i, hi_top⟩ := hexists
    have hi_id : ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := (indexedAuxiliaryEndomorphism_range_eq_top_iff 𝒜 V i).1 hi_top
    refine ⟨i, ?_, fun j hj => ?_⟩
    · rw [hi_top]
      exact (LinearEquiv.isSimpleModule_iff Submodule.topEquiv).2 hV
    · rcases hclass j with hb | ht
      · exact hb
      · exfalso
        have hj_id : ∀ v : V, (Pi.single j 1 : ∀ i, 𝒜 i) • v = v := (indexedAuxiliaryEndomorphism_range_eq_top_iff 𝒜 V j).1 ht
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine hv ?_
        have h1 : (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single j 1 : ∀ i, 𝒜 i) • v) = 0 := by
          rw [single_one_smul_single_one_smul, if_neg (fun h : i = j => hj h.symm)]
        rw [hj_id v, hi_id v] at h1
        exact h1
  · 
    
    rintro ⟨i, hi_simple, hj_bot⟩
    have hzero : ∀ j, j ≠ i → ∀ v : V, (Pi.single j 1 : ∀ i, 𝒜 i) • v = 0 :=
      fun j hj => (indexedAuxiliaryEndomorphism_range_eq_bot_iff 𝒜 V j).1 (hj_bot j hj)
    have hi_id : ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
      intro v
      have key : (∑ k, (Pi.single k 1 : ∀ i, 𝒜 i) • v) = (Pi.single i 1 : ∀ i, 𝒜 i) • v :=
        Finset.sum_eq_single i (fun k _ hk => hzero k hk v) (fun h => absurd (Finset.mem_univ i) h)
      rw [sum_single_one_smul] at key
      exact key.symm
    have hi_top : LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) = ⊤ := (indexedAuxiliaryEndomorphism_range_eq_top_iff 𝒜 V i).2 hi_id
    rw [hi_top] at hi_simple
    exact (LinearEquiv.isSimpleModule_iff Submodule.topEquiv).1 hi_simple

end PartA



section Inflation

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]

set_option linter.unusedVariables false in

/-- An auxiliary type obtained from a family of types, a finite index, and an additional type. -/
@[nolint unusedArguments]
def IndexedAuxiliaryType {r : ℕ} (𝒜 : Fin r → Type*) (i : Fin r) (W : Type*) : Type _ := W

namespace IndexedAuxiliaryType

variable {𝒜} {i : Fin r} {W W₁ W₂ : Type*}

/-- The additive commutative group structure on an indexed auxiliary type. -/
instance instAddCommGroup [AddCommGroup W] : AddCommGroup (IndexedAuxiliaryType 𝒜 i W) := inferInstanceAs (AddCommGroup W)


/-- An indexed auxiliary type is nontrivial whenever its base type is nontrivial. -/
instance nontrivial [AddCommGroup W] [Nontrivial W] : Nontrivial (IndexedAuxiliaryType 𝒜 i W) :=
  inferInstanceAs (Nontrivial W)

/-- The module structure over the selected factor on an indexed auxiliary type. -/
instance instModuleComponent [AddCommGroup W] [Module (𝒜 i) W] : Module (𝒜 i) (IndexedAuxiliaryType 𝒜 i W) :=
  inferInstanceAs (Module (𝒜 i) W)


/-- The module structure over the product ring on an indexed auxiliary type. -/
instance instModulePi [AddCommGroup W] [Module (𝒜 i) W] :
    Module (∀ j, 𝒜 j) (IndexedAuxiliaryType 𝒜 i W) :=
  Module.compHom (IndexedAuxiliaryType 𝒜 i W) (Pi.evalRingHom 𝒜 i)


/-- The action of a product-ring element on an indexed auxiliary type is the action of its selected component. -/
theorem pi_smul_eq_component_smul [AddCommGroup W] [Module (𝒜 i) W]
    (c : ∀ j, 𝒜 j) (w : IndexedAuxiliaryType 𝒜 i W) : c • w = c i • w := by
  change (Pi.evalRingHom 𝒜 i c) • w = c i • w
  rw [Pi.evalRingHom_apply]


/-- A product-ring element supported at the selected index acts on an indexed auxiliary type through its value at that index. -/
theorem single_smul [AddCommGroup W] [Module (𝒜 i) W] (a : 𝒜 i) (w : IndexedAuxiliaryType 𝒜 i W) :
    (Pi.single i a : ∀ j, 𝒜 j) • w = a • w := by
  rw [pi_smul_eq_component_smul, Pi.single_eq_same]


/-- A linear map from an indexed auxiliary type to its base type, with scalars mapped by evaluation at the selected index. -/
def toBaseLinearMap [AddCommGroup W] [Module (𝒜 i) W] :
    IndexedAuxiliaryType 𝒜 i W →ₛₗ[Pi.evalRingHom 𝒜 i] W where
  toFun w := w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


/-- The linear map from an indexed auxiliary type to its base type is bijective. -/
theorem toBaseLinearMap_bijective [AddCommGroup W] [Module (𝒜 i) W] :
    Function.Bijective (toBaseLinearMap (𝒜 := 𝒜) (i := i) (W := W)) :=
  ⟨fun _ _ h => h, fun w => ⟨w, rfl⟩⟩


/-- An indexed auxiliary type is simple over the product ring exactly when its base type is simple over the selected factor. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
theorem isSimpleModule_iff [AddCommGroup W] [Module (𝒜 i) W] :
    IsSimpleModule (∀ j, 𝒜 j) (IndexedAuxiliaryType 𝒜 i W) ↔ IsSimpleModule (𝒜 i) W :=
  LinearMap.isSimpleModule_iff_of_bijective _ toBaseLinearMap_bijective


/-- A linear equivalence over one factor induces a product-ring linear equivalence between the corresponding indexed auxiliary types. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
def linearEquivOfLinearEquiv [AddCommGroup W₁] [Module (𝒜 i) W₁] [AddCommGroup W₂] [Module (𝒜 i) W₂]
    (e : W₁ ≃ₗ[𝒜 i] W₂) : IndexedAuxiliaryType 𝒜 i W₁ ≃ₗ[∀ j, 𝒜 j] IndexedAuxiliaryType 𝒜 i W₂ where
  toFun w := e w
  invFun w := e.symm w
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' _ _ := e.map_add _ _
  map_smul' c w := by
    simp only [pi_smul_eq_component_smul, RingHom.id_apply]
    exact map_smul e (c i) (w : W₁)


/-- A product-ring linear equivalence between indexed auxiliary types at the same index induces a linear equivalence over the selected factor. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
def componentLinearEquivOfLinearEquiv [AddCommGroup W₁] [Module (𝒜 i) W₁] [AddCommGroup W₂] [Module (𝒜 i) W₂]
    (e : IndexedAuxiliaryType 𝒜 i W₁ ≃ₗ[∀ j, 𝒜 j] IndexedAuxiliaryType 𝒜 i W₂) : W₁ ≃ₗ[𝒜 i] W₂ where
  toFun w := e w
  invFun w := e.symm w
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' _ _ := e.map_add _ _
  map_smul' a w := by
    have h := map_smul e (Pi.single i a : ∀ j, 𝒜 j)
      (show IndexedAuxiliaryType 𝒜 i W₁ from w)
    rw [single_smul, single_smul] at h
    exact h


/-- A product-ring linear equivalence between nontrivial indexed auxiliary types forces their indices to agree. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
theorem eq_index_of_linearEquiv {i₁ i₂ : Fin r} {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module (𝒜 i₁) W₁] [Nontrivial W₁]
    [AddCommGroup W₂] [Module (𝒜 i₂) W₂]
    (e : IndexedAuxiliaryType 𝒜 i₁ W₁ ≃ₗ[∀ j, 𝒜 j] IndexedAuxiliaryType 𝒜 i₂ W₂) : i₁ = i₂ := by
  by_contra h
  obtain ⟨w, hw⟩ := exists_ne (0 : IndexedAuxiliaryType 𝒜 i₁ W₁)
  apply hw
  have key : e (Pi.single i₁ 1 • w) = Pi.single i₁ 1 • e w := map_smul e _ _
  rw [pi_smul_eq_component_smul, pi_smul_eq_component_smul, Pi.single_eq_same, one_smul,
      Pi.single_eq_of_ne (Ne.symm h), zero_smul] at key
  exact e.map_eq_zero_iff.mp key

end IndexedAuxiliaryType

end Inflation

section FactorClassification

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]
  (V : Type*) [AddCommGroup V] [Module (∀ i, 𝒜 i) V]


/-- The product of two product-ring elements supported at the same index is supported there with value equal to the product of their values. -/
theorem single_mul_single (i : Fin r) (a b : 𝒜 i) :
    (Pi.single i a : ∀ i, 𝒜 i) * Pi.single i b = Pi.single i (a * b) := by
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]


/-- The module structure over one factor on the range of the corresponding indexed auxiliary endomorphism. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
instance auxiliaryRangeModule (i : Fin r) :
    Module (𝒜 i) (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) where
  smul a x := ⟨(Pi.single i a : ∀ j, 𝒜 j) • (x : V), by
    rw [mem_indexedAuxiliaryEndomorphism_range_iff, ← mul_smul, single_mul_single, one_mul]⟩
  one_smul x := Subtype.ext (by
    change (Pi.single i (1 : 𝒜 i) : ∀ j, 𝒜 j) • (x : V) = (x : V)
    exact (mem_indexedAuxiliaryEndomorphism_range_iff 𝒜 V i _).1 x.2)
  mul_smul a b x := Subtype.ext (by
    change (Pi.single i (a * b) : ∀ j, 𝒜 j) • (x : V)
      = (Pi.single i a : ∀ j, 𝒜 j) • ((Pi.single i b : ∀ j, 𝒜 j) • (x : V))
    rw [← mul_smul, single_mul_single])
  smul_zero a := Subtype.ext (by
    change (Pi.single i a : ∀ j, 𝒜 j) • (0 : V) = 0
    rw [smul_zero])
  smul_add a x y := Subtype.ext (by
    change (Pi.single i a : ∀ j, 𝒜 j) • ((x : V) + (y : V))
      = (Pi.single i a : ∀ j, 𝒜 j) • (x : V) + (Pi.single i a : ∀ j, 𝒜 j) • (y : V)
    rw [smul_add])
  add_smul a b x := Subtype.ext (by
    change (Pi.single i (a + b) : ∀ j, 𝒜 j) • (x : V)
      = (Pi.single i a : ∀ j, 𝒜 j) • (x : V) + (Pi.single i b : ∀ j, 𝒜 j) • (x : V)
    rw [Pi.single_add, add_smul])
  zero_smul x := Subtype.ext (by
    change (Pi.single i (0 : 𝒜 i) : ∀ j, 𝒜 j) • (x : V) = 0
    rw [Pi.single_zero, zero_smul])


/-- The underlying vector of scalar multiplication in an indexed auxiliary range is obtained by acting with the product-ring element supported at that index. -/
@[simp] theorem coe_auxiliaryRange_smul (i : Fin r) (a : 𝒜 i)
    (x : LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) :
    ((a • x : LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) : V) = (Pi.single i a : ∀ j, 𝒜 j) • (x : V) :=
  rfl


/-- On an indexed auxiliary endomorphism range, the action of a product-ring element agrees with the action of its corresponding component. -/
theorem pi_smul_auxiliaryRange_eq_component_smul (i : Fin r) (c : ∀ j, 𝒜 j)
    (x : LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) :
    (c • x : LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i))
      = (c i • x : LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) := by
  apply Subtype.ext
  rw [coe_auxiliaryRange_smul]
  have hx : (Pi.single i 1 : ∀ j, 𝒜 j) • (x : V) = (x : V) := (mem_indexedAuxiliaryEndomorphism_range_iff 𝒜 V i _).1 x.2
  change (c : ∀ j, 𝒜 j) • (x : V) = (Pi.single i (c i) : ∀ j, 𝒜 j) • (x : V)
  conv_lhs => rw [← hx, ← mul_smul]
  congr 1
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]


/-- An auxiliary self-map of an indexed endomorphism range that is linear along evaluation from the product ring to the selected factor. -/
def auxiliaryRangeLinearMap (i : Fin r) :
    LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) →ₛₗ[Pi.evalRingHom 𝒜 i]
      LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by rw [Pi.evalRingHom_apply]; exact pi_smul_auxiliaryRange_eq_component_smul 𝒜 V i c x


/-- An indexed auxiliary endomorphism range is simple over the product ring exactly when it is simple over the corresponding factor. -/
theorem isSimpleModule_auxiliaryRange_iff (i : Fin r) :
    IsSimpleModule (∀ j, 𝒜 j) (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) ↔
      IsSimpleModule (𝒜 i) (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) :=
  LinearMap.isSimpleModule_iff_of_bijective (auxiliaryRangeLinearMap 𝒜 V i)
    ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩


/-- A module over a finite product of rings is simple exactly when one indexed auxiliary endomorphism range is simple over its factor and every other such range is zero. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
theorem isSimpleModule_pi_iff_exists_simple_auxiliaryRange :
    IsSimpleModule (∀ i, 𝒜 i) V ↔
      ∃ i, IsSimpleModule (𝒜 i) (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) ∧
        ∀ j, j ≠ i → LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V j) = ⊥ := by
  rw [isSimpleModule_pi_iff_exists_auxiliaryRange]
  refine exists_congr fun i => ?_
  rw [isSimpleModule_auxiliaryRange_iff]


/-- An indexed auxiliary endomorphism range is linearly equivalent over the product ring to the indexed auxiliary type formed from that range. -/
def auxiliaryRangeLinearEquivIndexedAuxiliaryType (i : Fin r) :
    LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i) ≃ₗ[∀ j, 𝒜 j]
      IndexedAuxiliaryType 𝒜 i (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    rw [IndexedAuxiliaryType.pi_smul_eq_component_smul]
    exact pi_smul_auxiliaryRange_eq_component_smul 𝒜 V i c x


/-- A simple module over a finite product of rings is linearly equivalent over that product to a range of an indexed auxiliary endomorphism that is simple over the corresponding factor. -/
theorem exists_equiv_auxiliaryRange [IsSimpleModule (∀ i, 𝒜 i) V] :
    ∃ i, IsSimpleModule (𝒜 i) (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) ∧
      Nonempty (V ≃ₗ[∀ i, 𝒜 i] LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) := by
  obtain ⟨i, hi, hbot⟩ := (isSimpleModule_pi_iff_exists_simple_auxiliaryRange 𝒜 V).1 ‹_›
  refine ⟨i, hi, ⟨(LinearEquiv.ofTop _ ?_).symm⟩⟩
  rw [eq_top_iff]
  intro v _
  have hfix : (Pi.single i 1 : ∀ j, 𝒜 j) • v = v := by
    have hsum : (∑ j, (Pi.single j 1 : ∀ j, 𝒜 j) • v) = v := sum_single_one_smul 𝒜 V v
    rw [Finset.sum_eq_single i (fun j _ hj => (indexedAuxiliaryEndomorphism_range_eq_bot_iff 𝒜 V j).1 (hbot j hj) v)
        (fun h => absurd (Finset.mem_univ i) h)] at hsum
    exact hsum
  rw [mem_indexedAuxiliaryEndomorphism_range_iff]; exact hfix


/-- A simple module over a finite product of rings is linearly equivalent to an indexed auxiliary type formed from a simple range of an indexed auxiliary endomorphism. -/
@[source_ref "Chapter3/Problem3.3.3" (role := supporting)]
theorem exists_equiv_indexedAuxiliaryType_auxiliaryRange [IsSimpleModule (∀ i, 𝒜 i) V] :
    ∃ i, IsSimpleModule (𝒜 i) (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i)) ∧
      Nonempty (V ≃ₗ[∀ j, 𝒜 j] IndexedAuxiliaryType 𝒜 i (LinearMap.range (indexedAuxiliaryEndomorphism 𝒜 V i))) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := exists_equiv_auxiliaryRange 𝒜 V
  exact ⟨i, hi, ⟨e.trans (auxiliaryRangeLinearEquivIndexedAuxiliaryType 𝒜 V i)⟩⟩

end FactorClassification



open scoped Matrix.Module

section MatrixAux

variable {k : Type*} [Field k] {d : ℕ} [NeZero d]
  {V : Type*} [AddCommGroup V] [Module k V]
  [Module (Matrix (Fin d) (Fin d) k) V]
  [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]

omit [NeZero d] in

private theorem smul_comm_k (A : Matrix (Fin d) (Fin d) k) (c : k) (x : V) :
    A • (c • x) = c • (A • x) := by
  conv_lhs => rw [show c • x = (c • (1 : Matrix (Fin d) (Fin d) k)) • x by
    rw [smul_assoc, one_smul]]
  rw [← mul_smul, mul_smul_comm, mul_one, smul_assoc]

omit [NeZero d] [Module k V] [IsScalarTower k (Matrix (Fin d) (Fin d) k) V] in

private theorem E_smul_E (i j l m : Fin d) (v : V) :
    (Matrix.single i j 1 : Matrix (Fin d) (Fin d) k) •
        ((Matrix.single l m 1 : Matrix (Fin d) (Fin d) k) • v)
      = if j = l then (Matrix.single i m 1 : Matrix (Fin d) (Fin d) k) • v else 0 := by
  rw [← mul_smul]
  by_cases h : j = l
  · subst h; simp
  · simp [h]

omit [NeZero d] in

private theorem sum_single_diag_eq_one :
    (∑ i, (Matrix.single i i 1 : Matrix (Fin d) (Fin d) k)) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp [and_self, Finset.sum_ite_eq']
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hab (h.1.symm.trans h.2)

omit [NeZero d] [Module k V] [IsScalarTower k (Matrix (Fin d) (Fin d) k) V] in

private theorem sum_E_diag_smul (v : V) :
    (∑ i, (Matrix.single i i 1 : Matrix (Fin d) (Fin d) k) • v) = v := by
  rw [← Finset.sum_smul, sum_single_diag_eq_one, one_smul]


private theorem A_smul_col (A : Matrix (Fin d) (Fin d) k) (a : Fin d) (v : V) :
    A • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v)
      = ∑ i, A i a • ((Matrix.single i 0 1 : Matrix (Fin d) (Fin d) k) • v) := by
  rw [← mul_smul]
  rw [show A * (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k)
        = ∑ i, A i a • Matrix.single i 0 1 from ?_]
  · rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_assoc]
  · ext p q
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply]
    rw [Finset.sum_eq_single a (fun l _ hl => by simp [Ne.symm hl]) (by simp),
        Finset.sum_eq_single p (fun i _ hi => by simp [hi]) (by simp)]
    simp


private def psi (v : V) : (Fin d → k) →ₗ[Matrix (Fin d) (Fin d) k] V where
  toFun w := ∑ a, w a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v)
  map_add' w w' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' A w := by
    change (∑ a, (A • w) a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v))
        = A • ∑ a, w a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v)
    rw [Finset.smul_sum]
    simp_rw [smul_comm_k, A_smul_col, Finset.smul_sum, smul_smul,
      Matrix.Module.smul_apply, Finset.sum_smul, smul_eq_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm]

@[simp]
private theorem psi_apply (v : V) (w : Fin d → k) :
    psi v w = ∑ a, w a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v) := rfl

end MatrixAux

section PartB

variable (k : Type*) [Field k] (d : ℕ) [NeZero d]


/-- The standard column module over a nonempty full matrix algebra is simple. -/
@[source_ref "Chapter3/Problem3.3.3" (role := primary),
  source_ref "Chapter3/Problem3.3.3/Derived12" (role := supporting)]
theorem isSimpleModule_standardMatrixModule :
    IsSimpleModule (Matrix (Fin d) (Fin d) k) (Fin d → k) where
  eq_bot_or_eq_top s := by
    rcases eq_or_ne s ⊥ with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hc; push Not at hc; exact hne (funext fun j => by simp [hc j])
      have basis_mem : ∀ j, (Pi.single j (1 : k) : Fin d → k) ∈ s := fun j => by
        have hmem := s.smul_mem (Matrix.single j i (v i)⁻¹) hv
        rwa [Matrix.Module.single_smul, smul_eq_mul, inv_mul_cancel₀ hi] at hmem
      rw [eq_top_iff]
      intro w _
      have hw : w = ∑ j, Pi.single j (w j) := by
        funext l
        rw [Finset.sum_apply]
        simp only [Pi.single_apply]
        rw [Finset.sum_ite_eq]
        simp
      rw [hw]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hsingle : (Pi.single j (w j) : Fin d → k)
          = (Matrix.single j j (w j) : Matrix (Fin d) (Fin d) k) •
            (Pi.single j (1 : k) : Fin d → k) := by
        rw [Matrix.Module.single_smul]; simp
      rw [hsingle]
      exact Submodule.smul_mem _ _ (basis_mem j)


/-- Every finite-dimensional simple module over a nonempty full matrix algebra is linearly equivalent to the standard column module. -/
@[source_ref "Chapter3/Problem3.3.3" (role := primary),
  source_ref "Chapter3/Problem3.3.3/Derived15" (role := supporting)]
theorem nonempty_equiv_standardModule_of_isSimpleModule (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (Matrix (Fin d) (Fin d) k) V
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  
  obtain ⟨a, ha⟩ : ∃ a, (Matrix.single a a 1 : Matrix (Fin d) (Fin d) k) • w₀ ≠ 0 := by
    by_contra hc; push Not at hc
    refine hw₀ ?_
    rw [← sum_E_diag_smul (k := k) (d := d) w₀]
    exact Finset.sum_eq_zero fun a _ => hc a
  
  set v : V := (Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • w₀ with hv_def
  have hEv : (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • v = v := by
    rw [hv_def, E_smul_E]; simp
  have hv_ne : v ≠ 0 := fun h => ha (by
    have h2 : (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v
        = (Matrix.single a a 1 : Matrix (Fin d) (Fin d) k) • w₀ := by
      rw [hv_def, E_smul_E]; simp
    rw [h, smul_zero] at h2; exact h2.symm)
  
  have hpsi_inj : Function.Injective (psi (k := k) (d := d) (V := V) v) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, psi_apply] at hw
    ext b
    have key : w b • v = 0 := by
      have h0 : (Matrix.single 0 b 1 : Matrix (Fin d) (Fin d) k) •
          (∑ c, w c • ((Matrix.single c 0 1 : Matrix (Fin d) (Fin d) k) • v)) = 0 := by
        rw [hw, smul_zero]
      rw [Finset.smul_sum] at h0
      simp_rw [smul_comm_k, E_smul_E] at h0
      simp_rw [smul_ite, smul_zero] at h0
      rw [Finset.sum_ite_eq] at h0
      simpa [hEv] using h0
    rcases smul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hv_ne
  
  have hrange : LinearMap.range (psi (k := k) (d := d) (V := V) v) = ⊤ := by
    rcases eq_bot_or_eq_top (LinearMap.range (psi (k := k) (d := d) (V := V) v)) with hb | ht
    · exfalso; apply hv_ne
      have hvmem : v ∈ LinearMap.range (psi (k := k) (d := d) (V := V) v) :=
        ⟨Pi.single 0 1, by rw [psi_apply]; simp [Pi.single_apply, hEv]⟩
      rw [hb, Submodule.mem_bot] at hvmem; exact hvmem
    · exact ht
  exact ⟨(LinearEquiv.ofBijective (psi (k := k) (d := d) (V := V) v)
    ⟨hpsi_inj, LinearMap.range_eq_top.mp hrange⟩).symm⟩


/-- Every finite-dimensional module over a nonempty full matrix algebra is linearly equivalent to a finite product of copies of its standard module. -/
@[source_ref "Chapter3/Problem3.3.3" (role := primary),
  source_ref "Chapter3/Problem3.3.3/Derived13" (role := supporting),
  source_ref "Chapter3/Problem3.3.3/Derived14" (role := supporting),
  source_ref "Chapter3/Problem3.3.3/Derived15" (role := supporting)]
theorem exists_equiv_pi_standardModule (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] :
    ∃ n : ℕ, Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin n → (Fin d → k))) := by
  classical
  
  let P0 : V →ₗ[k] V :=
    { toFun := fun x => (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • x
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun c x => by simp only [RingHom.id_apply]; rw [smul_comm_k] }
  set W := LinearMap.range P0 with hW_def
  set n := Module.finrank k W with hn_def
  let b := Module.finBasis k W
  
  have hfix : ∀ i, (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • (b i : V) = (b i : V) := by
    intro i
    obtain ⟨x, hx⟩ := (b i).2
    have hx' : (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • x = (b i : V) := hx
    rw [← hx', E_smul_E]; simp
  
  let Ψ : (Fin n → (Fin d → k)) →ₗ[Matrix (Fin d) (Fin d) k] V :=
    ∑ i, (psi (k := k) (d := d) (V := V) (b i : V)) ∘ₗ (LinearMap.proj i)
  have hΨ : ∀ f, Ψ f = ∑ i, psi (k := k) (d := d) (V := V) (b i : V) (f i) := fun f => by
    change (∑ i, (psi (k := k) (d := d) (V := V) (b i : V)) ∘ₗ (LinearMap.proj i)) f = _
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  
  have hli : LinearIndependent k (fun i => (b i : V)) :=
    (b.linearIndependent).map' W.subtype (Submodule.ker_subtype W)
  
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker, hΨ] at hf
    ext i j
    have key : (∑ i, (f i j) • (b i : V)) = 0 := by
      have h0 : (Matrix.single 0 j 1 : Matrix (Fin d) (Fin d) k) •
          (∑ i, psi (k := k) (d := d) (V := V) (b i : V) (f i)) = 0 := by rw [hf, smul_zero]
      simp_rw [psi_apply, Finset.smul_sum, smul_comm_k, E_smul_E,
        smul_ite, smul_zero] at h0
      simp_rw [Finset.sum_ite_eq] at h0
      simpa [hfix] using h0
    exact (Fintype.linearIndependent_iff.mp hli (fun i => f i j) key) i
  
  have hsurj : Function.Surjective Ψ := by
    intro x
    have hg_mem : ∀ a, (Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x ∈ W := by
      intro a
      refine ⟨(Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x, ?_⟩
      change (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) •
          ((Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x) = _
      rw [E_smul_E]; simp
    refine ⟨fun i a => b.repr ⟨_, hg_mem a⟩ i, ?_⟩
    rw [hΨ]
    have hrepr : ∀ a, (∑ i, (b.repr ⟨_, hg_mem a⟩ i) • (b i : V))
        = (Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x := by
      intro a
      have hsum := congrArg (Submodule.subtype W) (b.sum_repr ⟨_, hg_mem a⟩)
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using hsum
    calc ∑ i, psi (k := k) (d := d) (V := V) (b i : V) (fun a => b.repr ⟨_, hg_mem a⟩ i)
        = ∑ i, ∑ a, (b.repr ⟨_, hg_mem a⟩ i) •
            ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • (b i : V)) := by
          simp_rw [psi_apply]
      _ = ∑ a, ∑ i, (b.repr ⟨_, hg_mem a⟩ i) •
            ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • (b i : V)) := Finset.sum_comm
      _ = ∑ a, (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) •
            (∑ i, (b.repr ⟨_, hg_mem a⟩ i) • (b i : V)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => (smul_comm_k _ _ _).symm
      _ = ∑ a, (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) •
            ((Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x) := by
          simp_rw [hrepr]
      _ = ∑ a, (Matrix.single a a 1 : Matrix (Fin d) (Fin d) k) • x := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [E_smul_E]; simp
      _ = x := sum_E_diag_smul (k := k) (d := d) x
  exact ⟨n, ⟨(LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm⟩⟩

end PartB



attribute [nolint defsWithUnderscore]
  indexedAuxiliaryEndomorphism
  IndexedAuxiliaryType
  IndexedAuxiliaryType.instAddCommGroup
  IndexedAuxiliaryType.instModuleComponent
  IndexedAuxiliaryType.instModulePi
  IndexedAuxiliaryType.toBaseLinearMap
  IndexedAuxiliaryType.linearEquivOfLinearEquiv
  IndexedAuxiliaryType.componentLinearEquivOfLinearEquiv
  auxiliaryRangeModule
  auxiliaryRangeLinearMap
  auxiliaryRangeLinearEquivIndexedAuxiliaryType



attribute [nolint defsWithUnderscore unusedArguments] IndexedAuxiliaryType

end RepresentationTheory.Algebra.Module.Pi.SimpleModules
