/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib

set_option backward.isDefEq.respectTransparency false

universe u

namespace RepresentationTheory.Algebra.Homology.TensorBarResolution

open scoped TensorProduct
open CategoryTheory
open PiTensorProduct

variable (k A W : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

/-- The degree-indexed type used for tensor tails over `k` with coefficients in `W`. -/
abbrev tensorTail (n : ℕ) : Type u := (⨂[k]^n A) ⊗[k] W

/-- The degree-indexed type of terms in the tensor bar construction. -/
abbrev tensorBarTerm (n : ℕ) : Type u := A ⊗[k] tensorTail k A W n

/-- Every tensor bar term is a free `A`-module. -/
instance tensorBarTerm_free (n : ℕ) : Module.Free A (tensorBarTerm k A W n) :=
  inferInstanceAs (Module.Free A (A ⊗[k] tensorTail k A W n))

/-- Every tensor bar term is a projective `A`-module. -/
instance tensorBarTerm_projective (n : ℕ) : Module.Projective A (tensorBarTerm k A W n) :=
  inferInstance

/-- Each tensor-tail degree is finite as a `k`-module when `A` and `W` are finite-dimensional over `k`. -/
instance tensorTail_module_finite (n : ℕ) [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite k (tensorTail k A W n) :=
  inferInstanceAs (Module.Finite k ((⨂[k]^n A) ⊗[k] W))

/-- Each tensor bar term is finite as an `A`-module under the stated finite-dimensional hypotheses. -/
instance tensorBarTerm_module_finite (n : ℕ) [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite A (tensorBarTerm k A W n) :=
  inferInstanceAs (Module.Finite A (A ⊗[k] tensorTail k A W n))

/-- A tensor bar term regarded as an object of the category of `A`-modules. -/
noncomputable def tensorBarTermModule (n : ℕ) : ModuleCat.{u} A := ModuleCat.of A (tensorBarTerm k A W n)

/-- Every categorical tensor bar term is a projective object in `ModuleCat A`. -/
instance tensorBarTermModule_projective (n : ℕ) : Projective (tensorBarTermModule k A W n) :=
  inferInstanceAs (Projective (ModuleCat.of A (tensorBarTerm k A W n)))

/-- The carrier of each categorical tensor bar term is a finite `A`-module under the stated hypotheses. -/
instance tensorBarTermModule_finite (n : ℕ) [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite A (tensorBarTermModule k A W n) :=
  inferInstanceAs (Module.Finite A (tensorBarTerm k A W n))

/-- The linear equivalence between the degree-zero tensor tail and its coefficient module. -/
noncomputable def tensorTailZeroEquiv : tensorTail k A W 0 ≃ₗ[k] W :=
  TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0)) (LinearEquiv.refl k W) ≪≫ₗ
    TensorProduct.lid k W

/-- The `A`-linear augmentation from the degree-zero tensor bar term to `W`. -/
noncomputable def degreeZeroAugmentation : tensorBarTerm k A W 0 →ₗ[A] W :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (tensorTail k A W 0 →ₗ[k] W) (tensorTailZeroEquiv k A W).toLinearMap)

/-- On a pure degree-zero tensor, the augmentation is the leading algebra element acting on the represented coefficient. -/
@[simp]
lemma degreeZeroAugmentation_tmul (a : A) (c : tensorTail k A W 0) :
    degreeZeroAugmentation k A W (a ⊗ₜ c) = a • tensorTailZeroEquiv k A W c := by
  simp [degreeZeroAugmentation, LinearMap.toSpanSingleton_apply]

/-- The degree-zero augmentation is surjective. -/
lemma degreeZeroAugmentation_surjective : Function.Surjective (degreeZeroAugmentation k A W) := by
  intro w
  refine ⟨(1 : A) ⊗ₜ (tensorTailZeroEquiv k A W).symm w, ?_⟩
  simp

/-- The augmentation morphism from the degree-zero bar module to the coefficient module. -/
noncomputable def tensorBarAugmentation : tensorBarTermModule k A W 0 ⟶ ModuleCat.of A W :=
  ModuleCat.ofHom (degreeZeroAugmentation k A W)

/-- The underlying function of the degree-zero bar augmentation is surjective. -/
lemma tensorBarAugmentation_surjective : Function.Surjective (tensorBarAugmentation k A W) :=
  degreeZeroAugmentation_surjective k A W

section FaceMaps

local macro "fin_index" : tactic =>
  `(tactic| (simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega))

/-- Updating the left member of the contracted pair updates the contracted value by multiplying the replacement on the left. -/
theorem contractNth_update_left {n : ℕ} (i : Fin n) (v : Fin (n + 1) → A) (x : A)
    [DecidableEq (Fin (n + 1))] :
    Fin.contractNth (Fin.castSucc i) (· * ·) (Function.update v (Fin.castSucc i) x)
      = Function.update (Fin.contractNth (Fin.castSucc i) (· * ·) v) i (x * v (Fin.succ i)) := by
  funext k
  rcases lt_trichotomy (k : ℕ) (i : ℕ) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h),
        Function.update_of_ne (by fin_index),
        Function.update_of_ne (by fin_index),
        Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]
  · obtain rfl : k = i := Fin.ext h
    rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp), Function.update_self,
        Function.update_of_ne (by fin_index),
        Function.update_self]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h),
        Function.update_of_ne (by fin_index),
        Function.update_of_ne (by fin_index),
        Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h)]

/-- Updating the right member of the contracted pair updates the contracted value by multiplying the replacement on the right. -/
theorem contractNth_update_right {n : ℕ} (i : Fin n) (v : Fin (n + 1) → A) (x : A)
    [DecidableEq (Fin (n + 1))] :
    Fin.contractNth (Fin.castSucc i) (· * ·) (Function.update v (Fin.succ i) x) =
      Function.update (Fin.contractNth (Fin.castSucc i) (· * ·) v) i (v (Fin.castSucc i) * x) := by
  funext k
  rcases lt_trichotomy (k : ℕ) (i : ℕ) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h),
        Function.update_of_ne (by fin_index),
        Function.update_of_ne (by fin_index),
        Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]
  · obtain rfl : k = i := Fin.ext h
    rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp),
        Function.update_of_ne (by fin_index),
        Function.update_self, Function.update_self]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h),
        Function.update_of_ne (by fin_index),
        Function.update_of_ne (by fin_index),
        Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h)]

/-- Updating outside the contracted pair commutes with contraction after transporting the index by `predAbove`. -/
theorem contractNth_update_of_ne {n : ℕ} (i : Fin n) (v : Fin (n + 1) → A) (j : Fin (n + 1)) (x : A)
    [DecidableEq (Fin (n + 1))] (h1 : j ≠ Fin.castSucc i) (h2 : j ≠ Fin.succ i) :
    Fin.contractNth (Fin.castSucc i) (· * ·) (Function.update v j x)
      = Function.update (Fin.contractNth (Fin.castSucc i) (· * ·) v) (Fin.predAbove i j) x := by
  have hcol : Fin.predAbove i j ≠ i := by
    intro he
    apply h2
    rw [← Fin.succAbove_predAbove h1, he, Fin.succAbove_castSucc_self]
  funext k
  by_cases hk : k = Fin.predAbove i j
  · subst hk
    rw [Fin.contractNth_apply_of_ne _ _ _ _
          (by simpa [Fin.ext_iff] using fun e => hcol (Fin.ext e.symm)),
        Fin.succAbove_predAbove h1, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk]
    by_cases hki : k = i
    · subst hki
      rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp),
          Fin.contractNth_apply_of_eq _ _ _ _ (by simp),
          Function.update_of_ne (Ne.symm h1), Function.update_of_ne (Ne.symm h2)]
    · have hik : (Fin.castSucc i : Fin (n + 1)).val ≠ (k : ℕ) := by
        simp only [Fin.val_castSucc]; exact fun e => hki (Fin.ext e.symm)
      rw [Fin.contractNth_apply_of_ne _ _ _ _ hik, Fin.contractNth_apply_of_ne _ _ _ _ hik,
          Function.update_of_ne (by
            intro e
            exact hk (by rw [← Fin.predAbove_succAbove i k, e]))]

/-- For an associative operation, two ordered adjacent contractions satisfy the corresponding index-shift identity. -/
theorem contractNth_contractNth_assoc {α : Type*} (op : α → α → α)
    (hop : ∀ a b c, op (op a b) c = op a (op b c)) {n : ℕ}
    (p : Fin (n + 1)) (q : Fin (n + 2)) (hpq : (p : ℕ) < (q : ℕ)) (v : Fin (n + 2) → α) :
    Fin.contractNth p op (Fin.contractNth q op v)
      = Fin.contractNth (q.pred (by rintro rfl; simp at hpq)) op
          (Fin.contractNth p.castSucc op v) := by
  ext r
  simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, Fin.val_pred,
    Fin.succ_castSucc]
  split_ifs <;> first | rfl | (exfalso; omega) | rw [hop]

/-- The linear map that splits a nonempty tensor power into its head and tail. -/
noncomputable def tensorPowerUncons (n : ℕ) : (⨂[k]^(n + 1) A) →ₗ[k] A ⊗[k] (⨂[k]^n A) :=
  PiTensorProduct.lift <| LinearMap.uncurryLeft
    (M := fun _ : Fin (n + 1) => A)
    { toFun := fun a => (TensorProduct.mk k A (⨂[k]^n A) a).compMultilinearMap (tprod k)
      map_add' := by intro a b; ext v; simp
      map_smul' := by intro c a; ext v; simp [TensorProduct.smul_tmul'] }

/-- Splitting a pure tensor yields its first entry tensored with the tensor of its tail. -/
@[simp] theorem tensorPowerUncons_tprod (n : ℕ) (v : Fin (n + 1) → A) :
    tensorPowerUncons k A n (tprod k v) = v 0 ⊗ₜ tprod k (Fin.tail v) := by
  simp [tensorPowerUncons, LinearMap.uncurryLeft_apply]

/-- The linear map that separates the last factor of a nonempty tensor power. -/
noncomputable def tensorPowerUnsnoc (n : ℕ) : (⨂[k]^(n + 1) A) →ₗ[k] (⨂[k]^n A) ⊗[k] A :=
  PiTensorProduct.lift <| MultilinearMap.uncurryRight
    (M := fun _ : Fin (n + 1) => A)
    ((TensorProduct.mk k (⨂[k]^n A) A).compMultilinearMap (tprod k))

/-- Separating the last factor of a pure tensor yields the tensor of its initial entries paired with its last entry. -/
@[simp] theorem tensorPowerUnsnoc_tprod (n : ℕ) (v : Fin (n + 1) → A) :
    tensorPowerUnsnoc k A n (tprod k v) = tprod k (Fin.init v) ⊗ₜ v (Fin.last n) := by
  simp [tensorPowerUnsnoc, MultilinearMap.uncurryRight_apply]

/-- The linear map that multiplies a selected adjacent pair in a nonempty tensor power. -/
noncomputable def tensorPowerMul (n : ℕ) (i : Fin n) : (⨂[k]^(n + 1) A) →ₗ[k] (⨂[k]^n A) :=
  PiTensorProduct.lift
    (E := ⨂[k]^n A)
    { toFun := fun v => tprod k (Fin.contractNth (Fin.castSucc i) (· * ·) v)
      map_update_add' := by
        intro _ v j x y
        rcases eq_or_ne j (Fin.castSucc i) with rfl | hj1
        · simp only [contractNth_update_left, add_mul, MultilinearMap.map_update_add]
        · rcases eq_or_ne j (Fin.succ i) with rfl | hj2
          · simp only [contractNth_update_right, mul_add, MultilinearMap.map_update_add]
          · simp only [contractNth_update_of_ne _ _ _ _ _ hj1 hj2, MultilinearMap.map_update_add]
      map_update_smul' := by
        intro _ v j c x
        rcases eq_or_ne j (Fin.castSucc i) with rfl | hj1
        · simp only [contractNth_update_left, smul_mul_assoc, MultilinearMap.map_update_smul]
        · rcases eq_or_ne j (Fin.succ i) with rfl | hj2
          · simp only [contractNth_update_right, mul_smul_comm, MultilinearMap.map_update_smul]
          · simp only [contractNth_update_of_ne _ _ _ _ _ hj1 hj2, MultilinearMap.map_update_smul] }

/-- Adjacent-factor multiplication on a pure tensor is given by `Fin.contractNth`. -/
@[simp] theorem tensorPowerMul_tprod (n : ℕ) (i : Fin n) (v : Fin (n + 1) → A) :
    tensorPowerMul k A n i (tprod k v) = tprod k (Fin.contractNth (Fin.castSucc i) (· * ·) v) := by
  simp [tensorPowerMul]

end FaceMaps

section BarDifferential

/-- The linear map from `A tensor[k] W` to `W` induced by the action of `A` on `W`. -/
noncomputable def tensorAction : A ⊗[k] W →ₗ[k] W :=
  TensorProduct.lift <| LinearMap.mk₂ k (fun (a : A) (w : W) => a • w)
    (fun a₁ a₂ w => add_smul a₁ a₂ w)
    (fun c a w => smul_assoc c a w)
    (fun a w₁ w₂ => smul_add a w₁ w₂)
    (fun a c w => (smul_comm a c w).symm)

/-- The tensor action map sends a pure tensor to scalar multiplication. -/
@[simp] theorem tensorAction_tmul (a : A) (w : W) : tensorAction k A W (a ⊗ₜ[k] w) = a • w := by
  simp [tensorAction]

/-- The linear map from a tensor tail to the corresponding bar term obtained by adjoining the unit of `A`. -/
noncomputable def unitToBarTerm (n : ℕ) : tensorTail k A W n →ₗ[k] tensorBarTerm k A W n :=
  TensorProduct.mk k A (tensorTail k A W n) 1

omit [Module A W] [IsScalarTower k A W] in
/-- The unit-adjoining map sends a tensor tail to the pure tensor with leading factor one. -/
@[simp] theorem unitToBarTerm_apply (n : ℕ) (c : tensorTail k A W n) :
    unitToBarTerm k A W n c = (1 : A) ⊗ₜ[k] c := rfl

/-- The linear map that removes the final tensor factor by letting it act on the coefficient. -/
noncomputable def tensorTailLastAction (n : ℕ) : tensorTail k A W (n + 1) →ₗ[k] tensorTail k A W n :=
  TensorProduct.map LinearMap.id (tensorAction k A W)
    ∘ₗ (TensorProduct.assoc k (⨂[k]^n A) A W).toLinearMap
    ∘ₗ TensorProduct.map (tensorPowerUnsnoc k A n) LinearMap.id

/-- On a pure tensor, the final-factor action keeps the initial entries and applies the last entry to the coefficient. -/
@[simp] theorem tensorTailLastAction_tmul (n : ℕ) (v : Fin (n + 1) → A) (w : W) :
    tensorTailLastAction k A W n (tprod k v ⊗ₜ[k] w)
      = tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w) := by
  simp [tensorTailLastAction, TensorProduct.assoc_tmul]

/-- The linear map that separates the head factor of a tensor tail of successor degree. -/
noncomputable def splitHead (n : ℕ) : tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n :=
  (TensorProduct.assoc k A (⨂[k]^n A) W).toLinearMap
      ∘ₗ TensorProduct.map (tensorPowerUncons k A n) LinearMap.id
  + (∑ j : Fin n, (-1 : k) ^ ((j : ℕ) + 1) •
      (unitToBarTerm k A W n ∘ₗ TensorProduct.map (tensorPowerMul k A n j) LinearMap.id))
  + (-1 : k) ^ (n + 1) • (unitToBarTerm k A W n ∘ₗ tensorTailLastAction k A W n)

/-- A supporting result for the tensor-tail construction. -/
@[simp] theorem splitHead_aux_1 (n : ℕ) (v : Fin (n + 1) → A) (w : W) :
    splitHead k A W n (tprod k v ⊗ₜ[k] w)
      = v 0 ⊗ₜ[k] (tprod k (Fin.tail v) ⊗ₜ[k] w)
        + (∑ j : Fin n, (-1 : k) ^ ((j : ℕ) + 1) •
            ((1 : A) ⊗ₜ[k] (tprod k (Fin.contractNth j.castSucc (· * ·) v) ⊗ₜ[k] w)))
        + (-1 : k) ^ (n + 1) •
            ((1 : A) ⊗ₜ[k] (tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w))) := by
  simp only [splitHead, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    tensorPowerUncons_tprod, tensorPowerMul_tprod, LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul,
    unitToBarTerm_apply, tensorTailLastAction_tmul]

/-- The `A`-linear boundary map between consecutive tensor bar terms. -/
noncomputable def barBoundary (n : ℕ) : tensorBarTerm k A W (n + 1) →ₗ[A] tensorBarTerm k A W n :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n)
      (splitHead k A W n))

/-- Applying the bar boundary to a head tensor equals scalar multiplication by the head after splitting. -/
theorem barBoundary_tmul_splitHead (n : ℕ) (a₀ : A) (c : tensorTail k A W (n + 1)) :
    barBoundary k A W n (a₀ ⊗ₜ[k] c) = a₀ • splitHead k A W n c := by
  simp [barBoundary, LinearMap.toSpanSingleton_apply]

/-- A supporting result for the tensor bar boundary. -/
@[simp] theorem barBoundary_aux_1 (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barBoundary k A W n (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = (a₀ * v 0) ⊗ₜ[k] (tprod k (Fin.tail v) ⊗ₜ[k] w)
        + (∑ j : Fin n, (-1 : k) ^ ((j : ℕ) + 1) •
            (a₀ ⊗ₜ[k] (tprod k (Fin.contractNth j.castSucc (· * ·) v) ⊗ₜ[k] w)))
        + (-1 : k) ^ (n + 1) •
            (a₀ ⊗ₜ[k] (tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w))) := by
  rw [barBoundary_tmul_splitHead, splitHead_aux_1]
  simp only [smul_add, Finset.smul_sum, smul_comm (a₀ : A), TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

end BarDifferential

section BarFaces

/-- Extends a `k`-linear map on successor tensor tails to an `A`-linear map between bar terms. -/
noncomputable def linearizeBarMap {n : ℕ} (f : tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n) :
    tensorBarTerm k A W (n + 1) →ₗ[A] tensorBarTerm k A W n :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n) f)

omit [Module A W] [IsScalarTower k A W] in
/-- The linearized map sends a head tensor to the head acting on the value of the original map. -/
@[simp] theorem linearizeBarMap_tmul {n : ℕ} (f : tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n)
    (a₀ : A) (c : tensorTail k A W (n + 1)) :
    linearizeBarMap k A W f (a₀ ⊗ₜ[k] c) = a₀ • f c := by
  simp [linearizeBarMap, LinearMap.toSpanSingleton_apply]

/-- The bar boundary is the `A`-linear extension of the head-splitting map. -/
theorem barBoundary_eq_linearize_splitHead (n : ℕ) : barBoundary k A W n = linearizeBarMap k A W (splitHead k A W n) := rfl

/-- The initial tensor-tail face from successor degree to the corresponding bar term. -/
noncomputable def tensorTailFirstFace (n : ℕ) : tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n :=
  (TensorProduct.assoc k A (⨂[k]^n A) W).toLinearMap
    ∘ₗ TensorProduct.map (tensorPowerUncons k A n) LinearMap.id

/-- The interior tensor-tail face indexed by an adjacent pair among the tail factors. -/
noncomputable def tensorTailInnerFace (n : ℕ) (j : Fin n) :
    tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n :=
  unitToBarTerm k A W n ∘ₗ TensorProduct.map (tensorPowerMul k A n j) LinearMap.id

/-- The terminal tensor-tail face from successor degree to the corresponding bar term. -/
noncomputable def tensorTailLastFace (n : ℕ) : tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n :=
  unitToBarTerm k A W n ∘ₗ tensorTailLastAction k A W n

/-- The indexed `k`-linear face map from a successor tensor tail to a bar term. -/
noncomputable def tensorTailFace (n : ℕ) (i : Fin (n + 2)) :
    tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n :=
  if h0 : (i : ℕ) = 0 then tensorTailFirstFace k A W n
  else if hl : (i : ℕ) = n + 1 then tensorTailLastFace k A W n
  else tensorTailInnerFace k A W n ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

/-- The zeroth indexed tensor-tail face is the initial face map. -/
@[simp] theorem tensorTailFace_zero (n : ℕ) : tensorTailFace k A W n 0 = tensorTailFirstFace k A W n := by
  simp [tensorTailFace]

/-- The last indexed tensor-tail face is the terminal face map. -/
@[simp] theorem tensorTailFace_last (n : ℕ) :
    tensorTailFace k A W n (Fin.last (n + 1)) = tensorTailLastFace k A W n := by
  rw [tensorTailFace, dif_neg (by simp), dif_pos (by simp)]

/-- A successor-indexed tensor-tail face agrees with the corresponding interior face. -/
theorem tensorTailFace_succ_castSucc (n : ℕ) (j : Fin n) :
    tensorTailFace k A W n j.succ.castSucc = tensorTailInnerFace k A W n j := by
  rw [tensorTailFace]
  have h1 : ¬ ((j.succ.castSucc : Fin (n + 2)) : ℕ) = 0 := by simp [Fin.val_succ]
  have h2 : ¬ ((j.succ.castSucc : Fin (n + 2)) : ℕ) = n + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]; have := j.isLt; omega
  rw [dif_neg h1, dif_neg h2]
  congr 1

/-- The indexed `A`-linear face map between consecutive tensor bar terms. -/
noncomputable def barFace (n : ℕ) (i : Fin (n + 2)) :
    tensorBarTerm k A W (n + 1) →ₗ[A] tensorBarTerm k A W n :=
  linearizeBarMap k A W (tensorTailFace k A W n i)

omit [Module A W] [IsScalarTower k A W] in
/-- Linear extension to bar terms preserves addition of maps. -/
theorem linearizeBarMap_add {n : ℕ} (f g : tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n) :
    linearizeBarMap k A W (f + g) = linearizeBarMap k A W f + linearizeBarMap k A W g := by
  refine TensorProduct.AlgebraTensorModule.ext (fun a₀ c => ?_)
  simp [smul_add]

omit [Module A W] [IsScalarTower k A W] in
/-- Linear extension to bar terms preserves scalar multiplication by elements of `k`. -/
theorem linearizeBarMap_smul {n : ℕ} (c : k) (f : tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n) :
    linearizeBarMap k A W (c • f) = c • linearizeBarMap k A W f := by
  refine TensorProduct.AlgebraTensorModule.ext (fun a₀ x => ?_)
  simp only [linearizeBarMap_tmul, LinearMap.smul_apply]
  rw [smul_comm]

omit [Module A W] [IsScalarTower k A W] in
/-- Linear extension to bar terms commutes with finite sums of maps. -/
theorem linearizeBarMap_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (tensorTail k A W (n + 1) →ₗ[k] tensorBarTerm k A W n)) :
    linearizeBarMap k A W (∑ i ∈ s, f i) = ∑ i ∈ s, linearizeBarMap k A W (f i) := by
  classical
  induction s using Finset.induction with
  | empty => refine TensorProduct.AlgebraTensorModule.ext (fun a₀ c => ?_); simp [linearizeBarMap]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, linearizeBarMap_add, ih]

/-- A supporting result for the tensor-tail construction. -/
theorem splitHead_aux (n : ℕ) :
    splitHead k A W n = ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) • tensorTailFace k A W n i := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hlast : ((Fin.last n).succ : Fin (n + 2)) = Fin.last (n + 1) := Fin.succ_last n
  simp only [Fin.val_zero, pow_zero, one_smul, tensorTailFace_zero, Fin.val_succ, Fin.val_castSucc,
    Fin.succ_castSucc, tensorTailFace_succ_castSucc, hlast, tensorTailFace_last, Fin.val_last]
  rw [splitHead]
  abel

/-- A supporting result for the tensor bar boundary. -/
theorem barBoundary_aux (n : ℕ) :
    barBoundary k A W n = ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) • barFace k A W n i := by
  rw [barBoundary_eq_linearize_splitHead, splitHead_aux, linearizeBarMap_sum]
  simp only [linearizeBarMap_smul, barFace]

/-- The zeroth face of a pure tensor multiplies its leading two algebra entries. -/
@[simp] theorem barFace_zero_tmul (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n 0 (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = (a₀ * v 0) ⊗ₜ[k] (tprod k (Fin.tail v) ⊗ₜ[k] w) := by
  rw [barFace, tensorTailFace_zero, linearizeBarMap_tmul, tensorTailFirstFace]
  simp [TensorProduct.smul_tmul']

/-- An interior successor face preserves the leading factor and contracts the corresponding adjacent tail entries. -/
@[simp] theorem barFace_succ_tmul (n : ℕ) (j : Fin n) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n j.succ.castSucc (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = a₀ ⊗ₜ[k] (tprod k (Fin.contractNth (Fin.castSucc j) (· * ·) v) ⊗ₜ[k] w) := by
  rw [barFace, tensorTailFace_succ_castSucc, linearizeBarMap_tmul, tensorTailInnerFace]
  simp [TensorProduct.smul_tmul']

/-- The last face of a pure tensor lets the final algebra entry act on the coefficient. -/
@[simp] theorem barFace_last_tmul (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n (Fin.last (n + 1)) (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = a₀ ⊗ₜ[k] (tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w)) := by
  rw [barFace, tensorTailFace_last, linearizeBarMap_tmul, tensorTailLastFace]
  simp [TensorProduct.smul_tmul']

omit [Module A W] [IsScalarTower k A W] in

/-- Two `A`-linear maps from a successor bar term are equal if they agree on all displayed pure tensors. -/
theorem tensorBarTerm_ext {n m : ℕ}
    {F G : tensorBarTerm k A W (n + 1) →ₗ[A] tensorBarTerm k A W m}
    (h : ∀ (a₀ : A) (v : Fin (n + 1) → A) (w : W),
      F (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)) = G (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))) :
    F = G := by
  refine TensorProduct.AlgebraTensorModule.ext fun a₀ x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
      induction p using PiTensorProduct.induction_on with
      | smul_tprod r v =>
          simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
            LinearMap.map_smul_of_tower]
          rw [h a₀ v w]
      | add x y hx hy =>
          rw [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

end BarFaces

section BarSquareZero

/-- Contracting at a successor index after `Fin.cons` preserves the head and contracts the tail. -/
theorem contractNth_succ_cons {m : ℕ} (a : A) (g : Fin (m + 1) → A) (i : Fin (m + 1)) :
    Fin.contractNth i.succ (· * ·) (Fin.cons a g)
      = Fin.cons a (Fin.contractNth i (· * ·) g) := by
  funext k
  refine Fin.cases ?_ (fun p => ?_) k
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp only [Fin.val_zero, Fin.val_succ]; omega),
        Fin.castSucc_zero, Fin.cons_zero, Fin.cons_zero]
  · rw [Fin.cons_succ]
    rcases lt_trichotomy (p : ℕ) (i : ℕ) with h | h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp only [Fin.val_succ]; omega),
          Fin.contractNth_apply_of_lt _ _ _ _ h, ← Fin.succ_castSucc, Fin.cons_succ]
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp only [Fin.val_succ]; omega),
          Fin.contractNth_apply_of_eq _ _ _ _ h, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp only [Fin.val_succ]; omega),
          Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.cons_succ]

/-- Contracting at zero after `Fin.cons` multiplies the new head with the old head and retains the remaining tail. -/
theorem contractNth_zero_cons {m : ℕ} (a : A) (g : Fin (m + 1) → A) :
    Fin.contractNth 0 (· * ·) (Fin.cons a g) = Fin.cons (a * g 0) (Fin.tail g) := by
  funext k
  refine Fin.cases ?_ (fun p => ?_) k
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]
    simp
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp), Fin.cons_succ, Fin.cons_succ, Fin.tail]

/-- A nonterminal bar face multiplies the selected adjacent entries of a pure tensor. -/
theorem barFace_castSucc_tmul (n : ℕ) (i : Fin (n + 1)) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n i.castSucc (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = Fin.contractNth i.castSucc (· * ·) (Fin.cons a₀ v) 0 ⊗ₜ[k]
          (tprod k (Fin.tail (Fin.contractNth i.castSucc (· * ·) (Fin.cons a₀ v))) ⊗ₜ[k] w) := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [Fin.castSucc_zero, barFace_zero_tmul, contractNth_zero_cons, Fin.cons_zero, Fin.tail_cons]
  · rw [barFace_succ_tmul, ← Fin.succ_castSucc, contractNth_succ_cons, Fin.cons_zero,
      Fin.tail_cons]

/-- Contracting before the final entry commutes with taking the initial entries, with the last entry appended afterward. -/
theorem contractNth_castSucc_castSucc {m : ℕ} (p : Fin m) (u : Fin (m + 2) → A) :
    Fin.contractNth p.castSucc.castSucc (· * ·) u
      = Fin.snoc (Fin.contractNth p.castSucc (· * ·) (Fin.init u)) (u (Fin.last (m + 1))) := by
  funext k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · rw [Fin.snoc_last, Fin.contractNth_apply_of_gt _ _ _ _
        (by simp only [Fin.val_castSucc, Fin.val_last]; omega)]
    congr 1
  · rw [Fin.snoc_castSucc]
    rcases lt_trichotomy (k' : ℕ) (p : ℕ) with h | h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h),
          Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h), Fin.init]
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h),
          Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h), Fin.init, Fin.init,
          ← Fin.succ_castSucc]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h),
          Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h), Fin.init, ← Fin.succ_castSucc]

/-- Contracting the final adjacent pair produces the initial entries followed by the product of the last two entries. -/
theorem contractNth_last_castSucc {m : ℕ} (u : Fin (m + 2) → A) :
    Fin.contractNth (Fin.last m).castSucc (· * ·) u
      = Fin.snoc (fun i : Fin m => u i.castSucc.castSucc)
          (u (Fin.castSucc (Fin.last m)) * u (Fin.last (m + 1))) := by
  funext k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · rw [Fin.snoc_last, Fin.contractNth_apply_of_eq _ _ _ _
        (by simp only [Fin.val_castSucc, Fin.val_last]), Fin.succ_last]
  · rw [Fin.snoc_castSucc, Fin.contractNth_apply_of_lt _ _ _ _
        (by simp only [Fin.val_castSucc, Fin.val_last]; omega)]

/-- Ordered bar face maps satisfy the standard interchange identity for two contractions. -/
theorem barFace_comp_barFace (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3))
    (hij : (i : ℕ) < (j : ℕ)) :
    (barFace k A W n i).comp (barFace k A W (n + 1) j)
      = (barFace k A W n (j.pred (by rintro rfl; simp only [Fin.val_zero] at hij; omega))).comp
          (barFace k A W (n + 1) i.castSucc) := by
  apply tensorBarTerm_ext
  intro a₀ v w
  simp only [LinearMap.comp_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i₀, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
  · 
    have hj0 : j₀ ≠ 0 := by
      rintro rfl; simp only [Fin.val_castSucc, Fin.val_zero] at hij; omega
    have hpq : ((Fin.castSucc i₀ : Fin (n + 2)) : ℕ) < ((Fin.castSucc j₀ : Fin (n + 3)) : ℕ) := by
      simpa using hij
    rw [barFace_castSucc_tmul, barFace_castSucc_tmul, Fin.cons_self_tail,
        ← Fin.castSucc_pred_eq_pred_castSucc, barFace_castSucc_tmul, barFace_castSucc_tmul,
        Fin.cons_self_tail,
        contractNth_contractNth_assoc (· * ·) mul_assoc (Fin.castSucc i₀) (Fin.castSucc j₀) hpq
          (Fin.cons a₀ v), ← Fin.castSucc_pred_eq_pred_castSucc]
    all_goals exact hj0
  · 
    rw [barFace_last_tmul, barFace_castSucc_tmul, Fin.pred_last, barFace_castSucc_tmul,
        barFace_last_tmul]
    have hG : Fin.contractNth (Fin.castSucc i₀).castSucc (· * ·) (Fin.cons a₀ v)
        = Fin.snoc (Fin.contractNth (Fin.castSucc i₀) (· * ·) (Fin.cons a₀ (Fin.init v)))
            (v (Fin.last (n + 1))) := by
      rw [contractNth_castSucc_castSucc]
      congr 1
      congr 1
      funext j
      refine Fin.cases ?_ (fun p => ?_) j
      · simp [Fin.init]
      · simp only [Fin.init, ← Fin.succ_castSucc, Fin.cons_succ]
    rw [hG, Fin.snoc_apply_zero, ← Fin.tail_init_eq_init_tail, Fin.init_snoc]
    simp only [Fin.tail]
    rw [Fin.succ_last, Fin.snoc_last]
  · 
    exfalso; simp only [Fin.val_last, Fin.val_castSucc] at hij; omega
  · 
    rw [barFace_last_tmul, barFace_last_tmul, Fin.pred_last, barFace_castSucc_tmul,
        barFace_last_tmul, contractNth_last_castSucc, Fin.snoc_apply_zero,
        ← Fin.tail_init_eq_init_tail, Fin.init_snoc]
    have hlead : (Fin.cons a₀ v : Fin (n + 3) → A) (Fin.castSucc 0).castSucc = a₀ := by simp
    have hmid : (Fin.tail (fun i : Fin (n + 1) => (Fin.cons a₀ v : Fin (n + 3) → A)
          i.castSucc.castSucc) : Fin n → A)
        = Fin.init (Fin.init v) := by
      funext i
      simp only [Fin.tail, Fin.init]
      rw [← Fin.succ_castSucc, ← Fin.succ_castSucc, Fin.cons_succ]
    have hy1 : (Fin.cons a₀ v : Fin (n + 3) → A) (Fin.last (n + 1)).castSucc
        = Fin.init v (Fin.last n) := by
      simp only [Fin.init]
      rw [show (Fin.last (n + 1)).castSucc = (Fin.castSucc (Fin.last n)).succ from by
            rw [← Fin.succ_last, ← Fin.succ_castSucc], Fin.cons_succ]
    have hy2 : (Fin.cons a₀ v : Fin (n + 3) → A) (Fin.last (n + 1 + 1)) = v (Fin.last (n + 1)) := by
      rw [show (Fin.last (n + 1 + 1)) = (Fin.last (n + 1)).succ from (Fin.succ_last _).symm,
          Fin.cons_succ]
    rw [hlead, hmid]
    simp only [Fin.tail]
    rw [Fin.succ_last, Fin.snoc_last, hy1, hy2, mul_smul]

/-- Two consecutive bar boundary maps compose to zero. -/
theorem barBoundary_comp_barBoundary (n : ℕ) :
    (barBoundary k A W n).comp (barBoundary k A W (n + 1)) = 0 := by
  classical
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, barBoundary_aux, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, map_sum, LinearMap.map_smul_of_tower,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_product']
  set S : Finset (Fin (n + 2) × Fin (n + 3)) :=
    Finset.univ.filter (fun p => (p.2 : ℕ) ≤ (p.1 : ℕ)) with hS
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun p hp => (Fin.castLT p.2 (lt_of_le_of_lt
        (by simpa [hS] using (Finset.mem_filter.mp hp).2) p.1.isLt), p.1.succ)) ?_ ?_ ?_ ?_
  · 
    intro p hp
    have hji : (p.2 : ℕ) ≤ (p.1 : ℕ) := by simpa [hS] using (Finset.mem_filter.mp hp).2
    simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le,
      Fin.val_succ, Fin.val_castLT]
    omega
  · 
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    have h1 : (j : ℕ) = (j' : ℕ) := by simpa [Fin.val_castLT] using congrArg (fun q => (q.1 : ℕ)) h
    have h2 : (i : ℕ) = (i' : ℕ) := by
      have := congrArg (fun q => (q.2 : ℕ)) h
      simpa [Fin.val_succ] using this
    ext <;> assumption
  · 
    rintro ⟨i', j'⟩ hij'
    have hlt : (i' : ℕ) < (j' : ℕ) := by
      simpa [hS, Finset.mem_compl, Finset.mem_filter, not_le] using hij'
    have hj0 : j' ≠ 0 := by rintro rfl; simp only [Fin.val_zero] at hlt; omega
    refine ⟨(j'.pred hj0, Fin.castSucc i'), ?_, ?_⟩
    · simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]
      omega
    · simp only [Fin.castLT_castSucc, Fin.succ_pred]
  · 
    rintro ⟨i, j⟩ hij
    have hji : (j : ℕ) ≤ (i : ℕ) := by simpa [hS] using (Finset.mem_filter.mp hij).2
    have hlt : ((Fin.castLT j (lt_of_le_of_lt hji i.isLt) : Fin (n + 2)) : ℕ) < (i.succ : ℕ) := by
      simp only [Fin.val_castLT, Fin.val_succ]; omega
    have key := LinearMap.congr_fun
      (barFace_comp_barFace k A W n (Fin.castLT j (lt_of_le_of_lt hji i.isLt)) i.succ hlt) x
    simp only [LinearMap.comp_apply] at key
    rw [Fin.pred_succ, Fin.castSucc_castLT] at key
    simp only [key, Fin.val_castLT, Fin.val_succ, ← neg_smul]
    congr 1
    rw [pow_succ]
    ring

/-- The chain complex of `A`-modules associated with the tensor bar construction for `W`. -/
noncomputable def tensorBarComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun n => tensorBarTermModule k A W n) (fun n => ModuleCat.ofHom (barBoundary k A W n))
    (fun n => by
      ext y
      exact LinearMap.congr_fun (barBoundary_comp_barBoundary k A W n) y)

end BarSquareZero

section Augmentation

omit [Module A W] [IsScalarTower k A W] in
/-- The degree-zero equivalence evaluates an empty pure tensor paired with a coefficient to that coefficient. -/
@[simp] lemma tensorTailZeroEquiv_apply_tmul (v : Fin 0 → A) (w : W) :
    tensorTailZeroEquiv k A W (tprod k v ⊗ₜ[k] w) = w := by
  simp [tensorTailZeroEquiv, PiTensorProduct.isEmptyEquiv_apply_tprod]

/-- The degree-zero augmentation annihilates the first bar boundary. -/
theorem degreeZeroAugmentation_comp_barBoundary :
    (degreeZeroAugmentation k A W).comp (barBoundary k A W 0) = 0 := by
  refine TensorProduct.AlgebraTensorModule.ext fun a₀ x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
      induction p using PiTensorProduct.induction_on with
      | smul_tprod r v =>
          have hgen : degreeZeroAugmentation k A W (barBoundary k A W 0 (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))) = 0 := by
            rw [barBoundary_aux_1]
            simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, map_add,
              LinearMap.map_smul_of_tower, degreeZeroAugmentation_tmul, tensorTailZeroEquiv_apply_tmul]
            have hlast : v (Fin.last 0) = v 0 := rfl
            rw [hlast, ← mul_smul, show ((-1 : k) ^ (0 + 1)) = -1 by norm_num,
              neg_one_smul, add_neg_cancel]
          simp only [LinearMap.comp_apply, LinearMap.zero_apply]
          rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
            LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hgen, smul_zero]
      | add x y hx hy =>
          simp only [LinearMap.comp_apply, LinearMap.zero_apply] at *
          rw [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, map_add, hx, hy, add_zero]
  | add x y hx hy =>
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at *
      rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, add_zero]

/-- The chain map from the tensor bar complex to the complex concentrated in degree zero at `W`. -/
noncomputable def tensorBarAugmentationHom :
    tensorBarComplex k A W ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A W) :=
  (ChainComplex.toSingle₀Equiv (tensorBarComplex k A W) (ModuleCat.of A W)).symm
    ⟨tensorBarAugmentation k A W, by
      have hd : (tensorBarComplex k A W).d 1 0 = ModuleCat.ofHom (barBoundary k A W 0) :=
        ChainComplex.of_d (fun n => tensorBarTermModule k A W n)
          (fun n => ModuleCat.ofHom (barBoundary k A W n)) 0
      rw [hd, tensorBarAugmentation]
      ext x
      exact LinearMap.congr_fun (degreeZeroAugmentation_comp_barBoundary k A W) x⟩

/-- The degree-zero component of the augmentation chain map is the bar augmentation. -/
@[simp] lemma tensorBarAugmentationHom_f_zero :
    (tensorBarAugmentationHom k A W).f 0 = tensorBarAugmentation k A W := by
  simp [tensorBarAugmentationHom]

end Augmentation

section BarContraction

/-- The linear map that prepends one factor to a tensor power. -/
noncomputable def tensorPowerCons (n : ℕ) : A ⊗[k] (⨂[k]^n A) →ₗ[k] ⨂[k]^(n + 1) A :=
  TensorProduct.lift ((PiTensorProduct.lift (s := fun _ : Fin n => A)).toLinearMap.comp
    (PiTensorProduct.tprod k
      (s := fun _ : Fin (n + 1) => A)).curryLeft)

omit [Module A W] [IsScalarTower k A W] in
/-- Prepending a factor to a pure tensor gives the pure tensor indexed by `Fin.cons`. -/
@[simp] theorem tensorPowerCons_tmul (n : ℕ) (a : A) (v : Fin n → A) :
    tensorPowerCons k A n (a ⊗ₜ[k] tprod k v) = PiTensorProduct.tprod k (Fin.cons a v) := by
  simp only [tensorPowerCons, TensorProduct.lift.tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, MultilinearMap.curryLeft_apply]

/-- The linear map from one bar degree to the next obtained by inserting a leading unit. -/
noncomputable def extraDegeneracy (n : ℕ) : tensorBarTerm k A W n →ₗ[k] tensorBarTerm k A W (n + 1) :=
  unitToBarTerm k A W (n + 1)
    ∘ₗ (TensorProduct.map (tensorPowerCons k A n) LinearMap.id
        ∘ₗ (TensorProduct.assoc k A (⨂[k]^n A) W).symm.toLinearMap)

omit [Module A W] [IsScalarTower k A W] in
/-- On a pure tensor, the extra degeneracy inserts a leading unit and moves the previous head into the tensor tail. -/
@[simp] theorem extraDegeneracy_tmul (n : ℕ) (a₀ : A) (v : Fin n → A) (w : W) :
    extraDegeneracy k A W n (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = (1 : A) ⊗ₜ[k] (PiTensorProduct.tprod k (Fin.cons a₀ v) ⊗ₜ[k] w) := by
  simp only [extraDegeneracy, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul, tensorPowerCons_tmul, LinearMap.id_coe,
    id_eq, unitToBarTerm_apply]

/-- The linear map from `W` into the degree-zero bar term obtained by inserting the unit of `A`. -/
noncomputable def degreeZeroUnitMap : W →ₗ[k] tensorBarTerm k A W 0 :=
  unitToBarTerm k A W 0 ∘ₗ (tensorTailZeroEquiv k A W).symm.toLinearMap

omit [Module A W] [IsScalarTower k A W] in
/-- The degree-zero unit map sends a coefficient to the unit tensored with its degree-zero tensor representative. -/
@[simp] theorem degreeZeroUnitMap_apply (w : W) :
    degreeZeroUnitMap k A W w = (1 : A) ⊗ₜ[k] (tensorTailZeroEquiv k A W).symm w := by
  simp [degreeZeroUnitMap]

omit [Module A W] [IsScalarTower k A W] in

/-- The inverse degree-zero equivalence represents a coefficient as the unique empty tensor paired with it. -/
theorem tensorTailZeroEquiv_symm_apply (u : Fin 0 → A) (y : W) :
    (tensorTailZeroEquiv k A W).symm y = tprod k u ⊗ₜ[k] y := by
  apply (tensorTailZeroEquiv k A W).injective
  rw [LinearEquiv.apply_symm_apply]
  simp [tensorTailZeroEquiv, PiTensorProduct.isEmptyEquiv_apply_tprod]

omit [Module A W] [IsScalarTower k A W] in

/-- Two `k`-linear maps from a bar term are equal if they agree on all displayed pure tensors. -/
theorem tensorBarTerm_linearMap_ext {n : ℕ} {X : Type u} [AddCommGroup X] [Module k X]
    {F G : tensorBarTerm k A W n →ₗ[k] X}
    (h : ∀ (a₀ : A) (v : Fin n → A) (w : W),
      F (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)) = G (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))) :
    F = G := by
  refine TensorProduct.ext' fun a₀ c => ?_
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
      induction p using PiTensorProduct.induction_on with
      | smul_tprod r v =>
          simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
            LinearMap.map_smul_of_tower]
          rw [h a₀ v w]
      | add x y hx hy =>
          rw [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

/-- After restricting scalars, the degree-zero augmentation composed with the unit map is the identity. -/
theorem degreeZeroAugmentation_comp_degreeZeroUnitMap :
    ((degreeZeroAugmentation k A W).restrictScalars k).comp (degreeZeroUnitMap k A W) = LinearMap.id := by
  ext w
  simp [degreeZeroUnitMap_apply, degreeZeroAugmentation_tmul, one_smul]

/-- At degree zero, the boundary-unit-map composite and the unit-map-augmentation composite sum to the identity. -/
theorem degreeZero_contraction :
    ((barBoundary k A W 0).restrictScalars k).comp (extraDegeneracy k A W 0)
      + (degreeZeroUnitMap k A W).comp ((degreeZeroAugmentation k A W).restrictScalars k) = LinearMap.id := by
  apply tensorBarTerm_linearMap_ext
  intro a₀ v w
  have hε : tensorTailZeroEquiv k A W (tprod k v ⊗ₜ[k] w) = w :=
    ((LinearEquiv.symm_apply_eq (tensorTailZeroEquiv k A W)).1
      (tensorTailZeroEquiv_symm_apply k A W v w)).symm
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearMap.id_coe, id_eq, extraDegeneracy_tmul, degreeZeroAugmentation_tmul, hε]
  rw [barBoundary_aux_1]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.cons_zero, one_mul,
    Fin.tail_cons, zero_add, pow_one]
  have einit : Fin.init (Fin.cons (α := fun _ : Fin 1 => A) a₀ v) = v :=
    funext fun i => i.elim0
  rw [show (Fin.last 0 : Fin (0 + 1)) = 0 from Fin.ext rfl, Fin.cons_zero, einit]
  have hbase : degreeZeroUnitMap k A W (a₀ • w)
      = (1 : A) ⊗ₜ[k] (tprod k v ⊗ₜ[k] (a₀ • w)) := by
    rw [degreeZeroUnitMap_apply]
    congr 1
    exact tensorTailZeroEquiv_symm_apply k A W v (a₀ • w)
  rw [hbase]
  module

omit [Module A W] [IsScalarTower k A W] in

private theorem neg_one_pow_succ_smul {M : Type u} [AddCommGroup M] [Module k M]
    (m : ℕ) (y : M) : (-1 : k) ^ (m + 1) • y = -((-1 : k) ^ m • y) := by
  rw [pow_succ, mul_smul, neg_one_smul, smul_neg]

omit [Module A W] [IsScalarTower k A W] in

private theorem sum_neg_one_pow_succ_smul {M : Type u} [AddCommGroup M] [Module k M]
    {m : ℕ} (g : Fin m → M) :
    (∑ j : Fin m, (-1 : k) ^ ((j : ℕ) + 1 + 1) • g j)
      = -∑ j : Fin m, (-1 : k) ^ ((j : ℕ) + 1) • g j := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => neg_one_pow_succ_smul k ((j : ℕ) + 1) (g j)

/-- On pure tensors, the boundary and extra degeneracy satisfy the contracting-homotopy sum identity. -/
theorem barBoundary_extraDegeneracy_tmul_add (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barBoundary k A W (n + 1) (extraDegeneracy k A W (n + 1) (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)))
      + extraDegeneracy k A W n (barBoundary k A W n (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)))
      = a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w) := by
  have hinit : Fin.init (Fin.cons (α := fun _ : Fin (n + 2) => A) a₀ v)
      = Fin.cons (α := fun _ : Fin (n + 1) => A) a₀ (Fin.init v) := by
    funext i
    refine Fin.cases ?_ (fun p => ?_) i
    · simp [Fin.init, Fin.castSucc_zero]
    · simp only [Fin.init, ← Fin.succ_castSucc, Fin.cons_succ]
  rw [extraDegeneracy_tmul, barBoundary_aux_1, barBoundary_aux_1, map_add, map_add, map_sum]
  simp only [map_smul, extraDegeneracy_tmul, Fin.cons_zero, one_mul, Fin.tail_cons,
    ← Fin.succ_last, Fin.cons_succ]
  rw [hinit, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, contractNth_zero_cons, Fin.val_zero, Fin.val_succ,
    ← Fin.succ_castSucc, contractNth_succ_cons]
  have hsign (m : ℕ) (z : tensorBarTerm k A W (n + 1)) :
      (-1 : k) ^ (m + 1) • z = -((-1 : k) ^ m • z) :=
    neg_one_pow_succ_smul k m z
  let zfirst : tensorBarTerm k A W (n + 1) :=
    (1 : A) ⊗ₜ[k] (tprod k (Fin.cons (a₀ * v 0) (Fin.tail v)) ⊗ₜ[k] w)
  let zmid (x : Fin n) : tensorBarTerm k A W (n + 1) :=
    (1 : A) ⊗ₜ[k] (PiTensorProduct.tprod k
      (Fin.cons (α := fun _ : Fin (n + 1) => A) a₀
        (x.castSucc.contractNth (fun x₁ x₂ => x₁ * x₂) v)) ⊗ₜ[k] w)
  let zlast : tensorBarTerm k A W (n + 1) :=
    (1 : A) ⊗ₜ[k] (PiTensorProduct.tprod k (Fin.cons a₀ (Fin.init v)) ⊗ₜ[k]
      (v (Fin.last n) • w))
  have hfirst : (-1 : k) ^ (0 + 1) • zfirst = -zfirst := by
    simpa only [pow_zero, one_smul] using hsign 0 zfirst
  have hmiddle :
      (∑ x : Fin n, (-1 : k) ^ ((x : ℕ) + 1 + 1) • zmid x) =
        -(∑ x : Fin n, (-1 : k) ^ ((x : ℕ) + 1) • zmid x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => hsign ((x : ℕ) + 1) (zmid x)
  have hlast : (-1 : k) ^ (n + 1 + 1) • zlast =
      -((-1 : k) ^ (n + 1) • zlast) := hsign (n + 1) zlast
  dsimp [zfirst, zmid, zlast] at hfirst hmiddle hlast
  rw [hfirst, hmiddle, hlast]
  abel

/-- The two composites of the boundary and extra degeneracy add to the identity. -/
theorem barBoundary_extraDegeneracy_add (n : ℕ) (x : tensorBarTerm k A W (n + 1)) :
    barBoundary k A W (n + 1) (extraDegeneracy k A W (n + 1) x)
      + extraDegeneracy k A W n (barBoundary k A W n x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add]; rw [add_add_add_comm, hx, hy]
  | tmul a₀ c =>
      induction c using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd =>
          rw [TensorProduct.tmul_add]; simp only [map_add]; rw [add_add_add_comm, hc, hd]
      | tmul p w =>
          induction p using PiTensorProduct.induction_on with
          | smul_tprod r v =>
              rw [TensorProduct.smul_tmul]
              exact barBoundary_extraDegeneracy_tmul_add k A W n a₀ v (r • w)
          | add p q hp hq =>
              rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
              simp only [map_add]; rw [add_add_add_comm, hp, hq]

end BarContraction

section Resolution

open CategoryTheory Limits

/-- The tensor bar complex is exact at every positive degree. -/
theorem tensorBarComplex_exact_succ (n : ℕ) : (tensorBarComplex k A W).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hf : ((tensorBarComplex k A W).sc' (n + 2) (n + 1) n).f
      = ModuleCat.ofHom (barBoundary k A W (n + 1)) :=
    ChainComplex.of_d (fun n => tensorBarTermModule k A W n)
      (fun n => ModuleCat.ofHom (barBoundary k A W n)) (n + 1)
  have hg : ((tensorBarComplex k A W).sc' (n + 2) (n + 1) n).g
      = ModuleCat.ofHom (barBoundary k A W n) :=
    ChainComplex.of_d (fun n => tensorBarTermModule k A W n)
      (fun n => ModuleCat.ofHom (barBoundary k A W n)) n
  intro x hx
  refine ⟨extraDegeneracy k A W (n + 1) x, ?_⟩
  rw [hg] at hx
  rw [hf]
  change barBoundary k A W n x = 0 at hx
  change barBoundary k A W (n + 1) (extraDegeneracy k A W (n + 1) x) = x
  have h := barBoundary_extraDegeneracy_add k A W n x
  rw [hx, map_zero, add_zero] at h
  exact h

/-- The augmentation chain map from the tensor bar complex is a quasi-isomorphism. -/
theorem tensorBarAugmentationHom_quasiIso : QuasiIso (tensorBarAugmentationHom k A W) := by
  rw [quasiIso_iff]
  rintro (_ | n)
  · 
    
    have hf0 : (tensorBarComplex k A W).d 1 0 = ModuleCat.ofHom (barBoundary k A W 0) :=
      ChainComplex.of_d (fun n => tensorBarTermModule k A W n)
        (fun n => ModuleCat.ofHom (barBoundary k A W n)) 0
    have hTexact :
        (ShortComplex.moduleCatMk (barBoundary k A W 0) (degreeZeroAugmentation k A W)
          (degreeZeroAugmentation_comp_barBoundary k A W)).Exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      refine ⟨extraDegeneracy k A W 0 x, ?_⟩
      change degreeZeroAugmentation k A W x = 0 at hx
      change barBoundary k A W 0 (extraDegeneracy k A W 0 x) = x
      have h := LinearMap.congr_fun (degreeZero_contraction k A W) x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
        LinearMap.id_coe, id_eq] at h
      rw [hx, map_zero, add_zero] at h
      exact h
    have hTepi :
        Epi (ShortComplex.moduleCatMk (barBoundary k A W 0) (degreeZeroAugmentation k A W)
          (degreeZeroAugmentation_comp_barBoundary k A W)).g := by
      have hg : (ShortComplex.moduleCatMk (barBoundary k A W 0) (degreeZeroAugmentation k A W)
          (degreeZeroAugmentation_comp_barBoundary k A W)).g = ModuleCat.ofHom (degreeZeroAugmentation k A W) := rfl
      rw [hg, ModuleCat.epi_iff_surjective]
      exact degreeZeroAugmentation_surjective k A W
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)).2 ⟨hTexact, hTepi⟩
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact tensorBarComplex_exact_succ k A W n

/-- The projective resolution of `W` in `ModuleCat A` supplied by the tensor bar construction. -/
noncomputable def _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution :
    CategoryTheory.ProjectiveResolution (ModuleCat.of A W) where
  complex := tensorBarComplex k A W
  π := tensorBarAugmentationHom k A W
  projective n := tensorBarTermModule_projective k A W n
  quasiIso := tensorBarAugmentationHom_quasiIso k A W

/-- Every term in the complex of the tensor bar resolution has finite carrier as an `A`-module. -/
instance tensorBarResolution_complex_finite (n : ℕ)
    [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite A ((RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.X n) :=
  inferInstanceAs (Module.Finite A (tensorBarTerm k A W n))

end Resolution

end RepresentationTheory.Algebra.Homology.TensorBarResolution

/-- The formal statement of this declaration is unavailable in the packet. -/
alias _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.Auxiliary.statement000662 := _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.splitHead_aux

/-- The formal statement of this declaration is unavailable in the packet. -/
alias _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.Auxiliary.statement000664 := _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.splitHead_aux_1

/-- The formal statement of this declaration is unavailable in the packet. -/
alias _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.Auxiliary.statement000713 := _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary_aux

/-- The formal statement of this declaration is unavailable in the packet. -/
alias _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.Auxiliary.statement000715 := _root_.RepresentationTheory.Algebra.Homology.TensorBarResolution.barBoundary_aux_1
