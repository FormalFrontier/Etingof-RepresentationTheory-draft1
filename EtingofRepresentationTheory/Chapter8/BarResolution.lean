import Mathlib

set_option backward.isDefEq.respectTransparency false

/-!
# The relative bar resolution of a representation of a `k`-algebra

For a field `k`, a `k`-algebra `A`, and a left `A`-module `W` (a representation of `A`), the
*relative* (`k`-split) **bar resolution** of `W` is the chain complex

`… → P₂ → P₁ → P₀ → W → 0`

with terms `Pₙ = A ⊗_k A^{⊗_k n} ⊗_k W`, the leading `A` factor carrying the left `A`-action,
augmentation `π : P₀ = A ⊗_k W → W`, `a ⊗ w ↦ a • w`, and the usual alternating-sum bar
differential.  Because `k` is a field every `A^{⊗n} ⊗_k W` is a free `k`-module, so each `Pₙ` is a
*free* `A`-module (`A ⊗_k (free k-module)`), hence projective.  This is what makes the relative
bar resolution an honest projective resolution over a field, and it is the missing piece needed to
compute `Ext_A` via `CategoryTheory.ProjectiveResolution.extAddEquivCohomologyClass`, as used in
`Problem_8_2_6_ii`.

## What is formalized here

This file provides the terms of the resolution as free/projective `A`-modules, together with
the augmentation:

* `Etingof.BarResolution.barCoeff k A W n`: the `k`-module `A^{⊗_k n} ⊗_k W` of bar coefficients.
* `Etingof.BarResolution.barModule k A W n = A ⊗_k (A^{⊗n} ⊗_k W)`: the `n`-th term, an
  `A`-module via left multiplication on the leading factor; a free `A`-module
  (`instance : Module.Free A (barModule …)`).
* `Etingof.BarResolution.barObj k A W n : ModuleCat A`: the term packaged as an object of
  `ModuleCat A`, with a `Projective` instance.
* `Etingof.BarResolution.ε k A W : barModule k A W 0 →ₗ[A] W`: the augmentation `a ⊗ w ↦ a • w`,
  proved surjective (`ε_surjective`); `barπ` is its packaging as a `ModuleCat` morphism.

It also provides the three reusable `k`-linear face-map primitives on the tensor powers
`⨂[k]^(n+1) A` from which the bar differential's faces are built: `barConsSplit` (pull off the
first factor), `barSnocSplit` (pull off the last factor), and `barMerge i` (merge the adjacent
factors `i`, `i+1` via the multiplication of `A`); see the section below.

The bar differential, the identity `d ∘ d = 0`, exactness via the `k`-linear contracting
homotopy `s(x) = 1 ⊗ x`, and the packaging into
`CategoryTheory.ProjectiveResolution (ModuleCat.of A W)` are developed in the sections below,
building on the terms and augmentation defined here.
-/

universe u

namespace Etingof.BarResolution

open scoped TensorProduct
open CategoryTheory
open PiTensorProduct

variable (k A W : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

/-- The `k`-module of bar coefficients in degree `n`: `A^{⊗_k n} ⊗_k W`. -/
abbrev barCoeff (n : ℕ) : Type u := (⨂[k]^n A) ⊗[k] W

/-- The `n`-th term of the relative bar resolution, `Pₙ = A ⊗_k (A^{⊗n} ⊗_k W)`.

It is an `A`-module via left multiplication on the leading `A` factor (the
`TensorProduct.leftModule` instance), and, because `k` is a field, so `barCoeff k A W n` is a free
`k`-module, a free `A`-module. -/
abbrev barModule (n : ℕ) : Type u := A ⊗[k] barCoeff k A W n

/-- Each bar term is a free `A`-module: it is `A ⊗_k X` with `X` a free `k`-module. -/
instance instFreeBarModule (n : ℕ) : Module.Free A (barModule k A W n) :=
  inferInstanceAs (Module.Free A (A ⊗[k] barCoeff k A W n))

/-- Each bar term is a projective `A`-module (being free). -/
instance instProjectiveBarModule (n : ℕ) : Module.Projective A (barModule k A W n) :=
  inferInstance

/-- When `A` and `W` are finite dimensional over `k`, each bar coefficient module
`A^{⊗n} ⊗_k W` is finite dimensional over `k` (a tensor product of finite dimensional factors,
the tensor power `⨂[k]^n A` being finite over `k` by `PiTensorProduct.finite`). -/
instance instFiniteBarCoeff (n : ℕ) [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite k (barCoeff k A W n) :=
  inferInstanceAs (Module.Finite k ((⨂[k]^n A) ⊗[k] W))

/-- When `A` and `W` are finite dimensional over `k`, each bar term `Pₙ = A ⊗_k (A^{⊗n} ⊗_k W)` is
a finitely generated `A`-module: it is `A ⊗_k X` with `X` finite over `k`, so it is finite over `A`
by base change (`Module.Finite.base_change`). This finite generation is exactly the hypothesis
`Problem_8_2_8_extₖ` requires of its resolving complexes. -/
instance instFiniteBarModule (n : ℕ) [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite A (barModule k A W n) :=
  inferInstanceAs (Module.Finite A (A ⊗[k] barCoeff k A W n))

/-- The `n`-th bar term packaged as an object of `ModuleCat A`. -/
noncomputable def barObj (n : ℕ) : ModuleCat.{u} A := ModuleCat.of A (barModule k A W n)

/-- Each bar term is projective as an object of `ModuleCat A`. -/
instance instProjectiveBarObj (n : ℕ) : Projective (barObj k A W n) :=
  inferInstanceAs (Projective (ModuleCat.of A (barModule k A W n)))

/-- When `A` and `W` are finite dimensional over `k`, each bar term is finitely generated as an
`A`-module (as an object of `ModuleCat A`). -/
instance instFiniteBarObj (n : ℕ) [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite A (barObj k A W n) :=
  inferInstanceAs (Module.Finite A (barModule k A W n))

/-- The canonical `k`-linear identification `barCoeff k A W 0 = A^{⊗0} ⊗_k W ≃ₗ[k] W`
(the empty tensor power is `k`, and `k ⊗_k W ≃ W`). -/
noncomputable def barCoeffZeroEquiv : barCoeff k A W 0 ≃ₗ[k] W :=
  TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0)) (LinearEquiv.refl k W) ≪≫ₗ
    TensorProduct.lid k W

/-- The augmentation `ε : P₀ = A ⊗_k (A^{⊗0} ⊗_k W) →ₗ[A] W`, `a ⊗ (unit ⊗ w) ↦ a • w`.

It is `A`-linear via `TensorProduct.AlgebraTensorModule.lift` (valid for noncommutative `A`),
applied to the `k`-linear identification `barCoeff k A W 0 ≃ₗ[k] W`. -/
noncomputable def ε : barModule k A W 0 →ₗ[A] W :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (barCoeff k A W 0 →ₗ[k] W) (barCoeffZeroEquiv k A W).toLinearMap)

@[simp]
lemma ε_tmul (a : A) (c : barCoeff k A W 0) :
    ε k A W (a ⊗ₜ c) = a • barCoeffZeroEquiv k A W c := by
  simp [ε, LinearMap.toSpanSingleton_apply]

/-- The augmentation is surjective: `w = ε (1 ⊗ e⁻¹ w)`. -/
lemma ε_surjective : Function.Surjective (ε k A W) := by
  intro w
  refine ⟨(1 : A) ⊗ₜ (barCoeffZeroEquiv k A W).symm w, ?_⟩
  simp

/-- The augmentation packaged as a morphism `barObj k A W 0 ⟶ ModuleCat.of A W`. -/
noncomputable def barπ : barObj k A W 0 ⟶ ModuleCat.of A W :=
  ModuleCat.ofHom (ε k A W)

lemma barπ_surjective : Function.Surjective (barπ k A W) :=
  ε_surjective k A W

/-! ### Face-map primitives on the tensor powers `⨂[k]^(n+1) A`

The bar differential `dₙ : Pₙ₊₁ → Pₙ` is an alternating sum of `n+2` face maps, each of which
acts on the middle `A^{⊗(n+1)}` factor by either pulling off the leading/trailing tensor factor or
merging two adjacent factors via the multiplication of `A`.  We record here the three reusable
`k`-linear primitives on `⨂[k]^(n+1) A` that these faces are built from:

* `barConsSplit`: pull off the first factor, `tprod v ↦ v 0 ⊗ tprod (Fin.tail v)`;
* `barSnocSplit`: pull off the last factor, `tprod v ↦ tprod (Fin.init v) ⊗ v (Fin.last n)`;
* `barMerge i`: merge the adjacent factors `i` and `i+1` via the multiplication of `A`
  (`tprod v ↦ tprod (Fin.contractNth i.castSucc (·*·) v)`).

`barMerge` is indexed by `i : Fin n` (the `n` mergeable adjacent pairs among the `n+1` factors);
the degenerate `Fin (n+1)`-index `Fin.last n` would drop the last factor rather than merge, which is
not multilinear and is instead handled by `barSnocSplit`. -/

section FaceMaps

/-- Local helper: discharge `Fin`-index (dis)equalities among `castSucc`/`succ` by `omega`. -/
local macro "fin_index" : tactic =>
  `(tactic| (simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega))

/-- Updating input coordinate `castSucc i` of `Fin.contractNth (castSucc i) (·*·)` changes only the
merged output column `i`, left-multiplying by the new value. -/
theorem contractNth_update_castSucc {n : ℕ} (i : Fin n) (v : Fin (n + 1) → A) (x : A)
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

/-- Updating input coordinate `succ i` of `Fin.contractNth (castSucc i) (·*·)` changes only the
merged output column `i`, right-multiplying by the new value. -/
theorem contractNth_update_succ {n : ℕ} (i : Fin n) (v : Fin (n + 1) → A) (x : A)
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

/-- Updating a non-merged input coordinate `j` of `Fin.contractNth (castSucc i) (·*·)` changes only
its passthrough output column `Fin.predAbove i j`. -/
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

/-- **Simplicial identity for `Fin.contractNth`** with an associative operation `op`:
merging at position `q` then at the lower position `p` equals merging at `p` first, then at
`q - 1` (the original `q`-block's position after the lower merge shifts everything above `p` down
by one). This is the merge-face version of the simplicial identity `dᵢ ∘ dⱼ = d_{j-1} ∘ dᵢ`
(`i < j`); Mathlib has no `contractNth`-composition lemma, so we prove it here. -/
theorem contractNth_contractNth {α : Type*} (op : α → α → α)
    (hop : ∀ a b c, op (op a b) c = op a (op b c)) {n : ℕ}
    (p : Fin (n + 1)) (q : Fin (n + 2)) (hpq : (p : ℕ) < (q : ℕ)) (v : Fin (n + 2) → α) :
    Fin.contractNth p op (Fin.contractNth q op v)
      = Fin.contractNth (q.pred (by rintro rfl; simp at hpq)) op
          (Fin.contractNth p.castSucc op v) := by
  ext r
  simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, Fin.val_pred,
    Fin.succ_castSucc]
  split_ifs <;> first | rfl | (exfalso; omega) | rw [hop]

/-- Pull off the first tensor factor: `tprod v ↦ v 0 ⊗ tprod (Fin.tail v)`. -/
noncomputable def barConsSplit (n : ℕ) : (⨂[k]^(n + 1) A) →ₗ[k] A ⊗[k] (⨂[k]^n A) :=
  PiTensorProduct.lift <| LinearMap.uncurryLeft
    (M := fun _ : Fin (n + 1) => A)
    { toFun := fun a => (TensorProduct.mk k A (⨂[k]^n A) a).compMultilinearMap (tprod k)
      map_add' := by intro a b; ext v; simp
      map_smul' := by intro c a; ext v; simp [TensorProduct.smul_tmul'] }

@[simp] theorem barConsSplit_tprod (n : ℕ) (v : Fin (n + 1) → A) :
    barConsSplit k A n (tprod k v) = v 0 ⊗ₜ tprod k (Fin.tail v) := by
  simp [barConsSplit, LinearMap.uncurryLeft_apply]

/-- Pull off the last tensor factor: `tprod v ↦ tprod (Fin.init v) ⊗ v (Fin.last n)`. -/
noncomputable def barSnocSplit (n : ℕ) : (⨂[k]^(n + 1) A) →ₗ[k] (⨂[k]^n A) ⊗[k] A :=
  PiTensorProduct.lift <| MultilinearMap.uncurryRight
    (M := fun _ : Fin (n + 1) => A)
    ((TensorProduct.mk k (⨂[k]^n A) A).compMultilinearMap (tprod k))

@[simp] theorem barSnocSplit_tprod (n : ℕ) (v : Fin (n + 1) → A) :
    barSnocSplit k A n (tprod k v) = tprod k (Fin.init v) ⊗ₜ v (Fin.last n) := by
  simp [barSnocSplit, MultilinearMap.uncurryRight_apply]

/-- Merge the adjacent factors `i` and `i+1` via the multiplication of `A`:
`tprod v ↦ tprod (Fin.contractNth i.castSucc (·*·) v)`. -/
noncomputable def barMerge (n : ℕ) (i : Fin n) : (⨂[k]^(n + 1) A) →ₗ[k] (⨂[k]^n A) :=
  PiTensorProduct.lift
    (E := ⨂[k]^n A)
    { toFun := fun v => tprod k (Fin.contractNth (Fin.castSucc i) (· * ·) v)
      map_update_add' := by
        intro _ v j x y
        rcases eq_or_ne j (Fin.castSucc i) with rfl | hj1
        · simp only [contractNth_update_castSucc, add_mul, MultilinearMap.map_update_add]
        · rcases eq_or_ne j (Fin.succ i) with rfl | hj2
          · simp only [contractNth_update_succ, mul_add, MultilinearMap.map_update_add]
          · simp only [contractNth_update_of_ne _ _ _ _ _ hj1 hj2, MultilinearMap.map_update_add]
      map_update_smul' := by
        intro _ v j c x
        rcases eq_or_ne j (Fin.castSucc i) with rfl | hj1
        · simp only [contractNth_update_castSucc, smul_mul_assoc, MultilinearMap.map_update_smul]
        · rcases eq_or_ne j (Fin.succ i) with rfl | hj2
          · simp only [contractNth_update_succ, mul_smul_comm, MultilinearMap.map_update_smul]
          · simp only [contractNth_update_of_ne _ _ _ _ _ hj1 hj2, MultilinearMap.map_update_smul] }

@[simp] theorem barMerge_tprod (n : ℕ) (i : Fin n) (v : Fin (n + 1) → A) :
    barMerge k A n i (tprod k v) = tprod k (Fin.contractNth (Fin.castSucc i) (· * ·) v) := by
  simp [barMerge]

end FaceMaps

/-! ### The bar differential `dₙ : Pₙ₊₁ → Pₙ`

The differential is the alternating sum of the `n + 2` faces
```
a₀ ⊗ (a₁,…,aₙ₊₁) ⊗ w ↦ a₀a₁ ⊗ (a₂,…,aₙ₊₁) ⊗ w
   + Σ_{i=1}^{n} (-1)ⁱ a₀ ⊗ (a₁,…,aᵢaᵢ₊₁,…,aₙ₊₁) ⊗ w
   + (-1)ⁿ⁺¹ a₀ ⊗ (a₁,…,aₙ) ⊗ (aₙ₊₁ • w).
```
Because the leading `A`-factor `a₀` is only ever left-multiplied (face `0` merges it into `a₁`; the
others keep it untouched), the differential is `A`-linear and factors as
`barDiff n (a₀ ⊗ c) = a₀ • barCoeffD n c` for a coefficient-level `k`-linear map
`barCoeffD n : barCoeff (n+1) → barModule n`, exactly as the augmentation `ε` did.  We build
`barCoeffD n` as the alternating sum of the faces expressed via the primitives `barConsSplit`,
`barMerge`, `barSnocSplit` above. -/

section BarDifferential

/-- The `k`-linear action map `A ⊗_k W →ₗ[k] W`, `a ⊗ w ↦ a • w` (used by the last face). -/
noncomputable def barAct : A ⊗[k] W →ₗ[k] W :=
  TensorProduct.lift <| LinearMap.mk₂ k (fun (a : A) (w : W) => a • w)
    (fun a₁ a₂ w => add_smul a₁ a₂ w)
    (fun c a w => smul_assoc c a w)
    (fun a w₁ w₂ => smul_add a w₁ w₂)
    (fun a c w => (smul_comm a c w).symm)

@[simp] theorem barAct_tmul (a : A) (w : W) : barAct k A W (a ⊗ₜ[k] w) = a • w := by
  simp [barAct]

/-- Prepend the unit of `A` to a bar coefficient: `x ↦ 1 ⊗ x : barCoeff n → barModule n`.
The middle-and-last faces of the differential all produce a leading factor `1`. -/
noncomputable def oneTmul (n : ℕ) : barCoeff k A W n →ₗ[k] barModule k A W n :=
  TensorProduct.mk k A (barCoeff k A W n) 1

omit [Module A W] [IsScalarTower k A W] in
@[simp] theorem oneTmul_apply (n : ℕ) (c : barCoeff k A W n) :
    oneTmul k A W n c = (1 : A) ⊗ₜ[k] c := rfl

/-- The last face at coefficient level, `tprod v ⊗ w ↦ tprod (Fin.init v) ⊗ (v (last) • w)`:
split off the trailing factor with `barSnocSplit` and act it on `w`. -/
noncomputable def barSnocAct (n : ℕ) : barCoeff k A W (n + 1) →ₗ[k] barCoeff k A W n :=
  TensorProduct.map LinearMap.id (barAct k A W)
    ∘ₗ (TensorProduct.assoc k (⨂[k]^n A) A W).toLinearMap
    ∘ₗ TensorProduct.map (barSnocSplit k A n) LinearMap.id

@[simp] theorem barSnocAct_tprod (n : ℕ) (v : Fin (n + 1) → A) (w : W) :
    barSnocAct k A W n (tprod k v ⊗ₜ[k] w)
      = tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w) := by
  simp [barSnocAct, TensorProduct.assoc_tmul]

/-- The coefficient-level bar differential
`barCoeffD n : barCoeff (n+1) →ₗ[k] barModule n`, the alternating sum of the `n + 2` faces.
The `A`-linear differential is `barDiff n (a₀ ⊗ c) = a₀ • barCoeffD n c`. -/
noncomputable def barCoeffD (n : ℕ) : barCoeff k A W (n + 1) →ₗ[k] barModule k A W n :=
  (TensorProduct.assoc k A (⨂[k]^n A) W).toLinearMap
      ∘ₗ TensorProduct.map (barConsSplit k A n) LinearMap.id
  + (∑ j : Fin n, (-1 : k) ^ ((j : ℕ) + 1) •
      (oneTmul k A W n ∘ₗ TensorProduct.map (barMerge k A n j) LinearMap.id))
  + (-1 : k) ^ (n + 1) • (oneTmul k A W n ∘ₗ barSnocAct k A W n)

@[simp] theorem barCoeffD_tprod (n : ℕ) (v : Fin (n + 1) → A) (w : W) :
    barCoeffD k A W n (tprod k v ⊗ₜ[k] w)
      = v 0 ⊗ₜ[k] (tprod k (Fin.tail v) ⊗ₜ[k] w)
        + (∑ j : Fin n, (-1 : k) ^ ((j : ℕ) + 1) •
            ((1 : A) ⊗ₜ[k] (tprod k (Fin.contractNth j.castSucc (· * ·) v) ⊗ₜ[k] w)))
        + (-1 : k) ^ (n + 1) •
            ((1 : A) ⊗ₜ[k] (tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w))) := by
  simp only [barCoeffD, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    barConsSplit_tprod, barMerge_tprod, LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul,
    oneTmul_apply, barSnocAct_tprod]

/-- **The bar differential** `dₙ : Pₙ₊₁ → Pₙ`, an `A`-linear map, defined via
`TensorProduct.AlgebraTensorModule.lift` from the coefficient-level differential `barCoeffD`
(so `barDiff n (a₀ ⊗ c) = a₀ • barCoeffD n c`), exactly as the augmentation `ε` is built. -/
noncomputable def barDiff (n : ℕ) : barModule k A W (n + 1) →ₗ[A] barModule k A W n :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (barCoeff k A W (n + 1) →ₗ[k] barModule k A W n)
      (barCoeffD k A W n))

theorem barDiff_tmul (n : ℕ) (a₀ : A) (c : barCoeff k A W (n + 1)) :
    barDiff k A W n (a₀ ⊗ₜ[k] c) = a₀ • barCoeffD k A W n c := by
  simp [barDiff, LinearMap.toSpanSingleton_apply]

/-- The bar differential on a pure tensor, as the explicit alternating sum of faces. -/
@[simp] theorem barDiff_tmul_tprod (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barDiff k A W n (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = (a₀ * v 0) ⊗ₜ[k] (tprod k (Fin.tail v) ⊗ₜ[k] w)
        + (∑ j : Fin n, (-1 : k) ^ ((j : ℕ) + 1) •
            (a₀ ⊗ₜ[k] (tprod k (Fin.contractNth j.castSucc (· * ·) v) ⊗ₜ[k] w)))
        + (-1 : k) ^ (n + 1) •
            (a₀ ⊗ₜ[k] (tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w))) := by
  rw [barDiff_tmul, barCoeffD_tprod]
  simp only [smul_add, Finset.smul_sum, smul_comm (a₀ : A), TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

end BarDifferential

/-! ### The bar faces `δᵢ` and the differential as their alternating sum

To prove `d ∘ d = 0` we present `barDiff` as the alternating sum `∑ i, (-1)ⁱ • barFace i` of the
`n + 2` individual faces `barFace i : Pₙ₊₁ → Pₙ`, each an `A`-linear map, and reduce the square-zero
relation to the simplicial identities `barFace i ∘ barFace j = barFace (j-1) ∘ barFace i` (`i < j`),
following Mathlib's `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`. -/

section BarFaces

/-- Package a `k`-linear coefficient map `barCoeff (n+1) → barModule n` as an `A`-linear map
`barModule (n+1) → barModule n`, `a₀ ⊗ c ↦ a₀ • f c` (the same lift used for `barDiff`). -/
noncomputable def ofCoeff {n : ℕ} (f : barCoeff k A W (n + 1) →ₗ[k] barModule k A W n) :
    barModule k A W (n + 1) →ₗ[A] barModule k A W n :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (barCoeff k A W (n + 1) →ₗ[k] barModule k A W n) f)

omit [Module A W] [IsScalarTower k A W] in
@[simp] theorem ofCoeff_tmul {n : ℕ} (f : barCoeff k A W (n + 1) →ₗ[k] barModule k A W n)
    (a₀ : A) (c : barCoeff k A W (n + 1)) :
    ofCoeff k A W f (a₀ ⊗ₜ[k] c) = a₀ • f c := by
  simp [ofCoeff, LinearMap.toSpanSingleton_apply]

theorem barDiff_eq_ofCoeff (n : ℕ) : barDiff k A W n = ofCoeff k A W (barCoeffD k A W n) := rfl

/-- The `i = 0` bar face at coefficient level (multiply the leading factor into the first tensor
slot): `tprod v ⊗ w ↦ v 0 ⊗ (tprod (tail v) ⊗ w)`. -/
noncomputable def coeffFaceZero (n : ℕ) : barCoeff k A W (n + 1) →ₗ[k] barModule k A W n :=
  (TensorProduct.assoc k A (⨂[k]^n A) W).toLinearMap
    ∘ₗ TensorProduct.map (barConsSplit k A n) LinearMap.id

/-- The interior bar face `1 ≤ i ≤ n` at coefficient level: merge tensor slots `j, j+1`. -/
noncomputable def coeffFaceInterior (n : ℕ) (j : Fin n) :
    barCoeff k A W (n + 1) →ₗ[k] barModule k A W n :=
  oneTmul k A W n ∘ₗ TensorProduct.map (barMerge k A n j) LinearMap.id

/-- The last bar face `i = n+1` at coefficient level: act the trailing tensor slot on `W`. -/
noncomputable def coeffFaceLast (n : ℕ) : barCoeff k A W (n + 1) →ₗ[k] barModule k A W n :=
  oneTmul k A W n ∘ₗ barSnocAct k A W n

/-- The `i`-th bar face at coefficient level (`i : Fin (n+2)`): face `0` multiplies the leading
factor into the first slot, faces `1 ≤ i ≤ n` merge adjacent slots, face `n+1` acts the last slot on
`W`. -/
noncomputable def coeffFace (n : ℕ) (i : Fin (n + 2)) :
    barCoeff k A W (n + 1) →ₗ[k] barModule k A W n :=
  if h0 : (i : ℕ) = 0 then coeffFaceZero k A W n
  else if hl : (i : ℕ) = n + 1 then coeffFaceLast k A W n
  else coeffFaceInterior k A W n ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

@[simp] theorem coeffFace_zero (n : ℕ) : coeffFace k A W n 0 = coeffFaceZero k A W n := by
  simp [coeffFace]

@[simp] theorem coeffFace_last (n : ℕ) :
    coeffFace k A W n (Fin.last (n + 1)) = coeffFaceLast k A W n := by
  rw [coeffFace, dif_neg (by simp), dif_pos (by simp)]

theorem coeffFace_interior (n : ℕ) (j : Fin n) :
    coeffFace k A W n j.succ.castSucc = coeffFaceInterior k A W n j := by
  rw [coeffFace]
  have h1 : ¬ ((j.succ.castSucc : Fin (n + 2)) : ℕ) = 0 := by simp [Fin.val_succ]
  have h2 : ¬ ((j.succ.castSucc : Fin (n + 2)) : ℕ) = n + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]; have := j.isLt; omega
  rw [dif_neg h1, dif_neg h2]
  congr 1

/-- The `i`-th bar face as an `A`-linear map `Pₙ₊₁ → Pₙ`. The bar differential is the alternating
sum `∑ i, (-1)^i • barFace i` (`barDiff_eq_sum_barFace`). -/
noncomputable def barFace (n : ℕ) (i : Fin (n + 2)) :
    barModule k A W (n + 1) →ₗ[A] barModule k A W n :=
  ofCoeff k A W (coeffFace k A W n i)

omit [Module A W] [IsScalarTower k A W] in
theorem ofCoeff_add {n : ℕ} (f g : barCoeff k A W (n + 1) →ₗ[k] barModule k A W n) :
    ofCoeff k A W (f + g) = ofCoeff k A W f + ofCoeff k A W g := by
  refine TensorProduct.AlgebraTensorModule.ext (fun a₀ c => ?_)
  simp [smul_add]

omit [Module A W] [IsScalarTower k A W] in
theorem ofCoeff_smul {n : ℕ} (c : k) (f : barCoeff k A W (n + 1) →ₗ[k] barModule k A W n) :
    ofCoeff k A W (c • f) = c • ofCoeff k A W f := by
  refine TensorProduct.AlgebraTensorModule.ext (fun a₀ x => ?_)
  simp only [ofCoeff_tmul, LinearMap.smul_apply]
  rw [smul_comm]

omit [Module A W] [IsScalarTower k A W] in
theorem ofCoeff_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (barCoeff k A W (n + 1) →ₗ[k] barModule k A W n)) :
    ofCoeff k A W (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeff k A W (f i) := by
  classical
  induction s using Finset.induction with
  | empty => refine TensorProduct.AlgebraTensorModule.ext (fun a₀ c => ?_); simp [ofCoeff]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ofCoeff_add, ih]

/-- The coefficient-level bar differential is the alternating sum of the bar faces. -/
theorem barCoeffD_eq_sum_coeffFace (n : ℕ) :
    barCoeffD k A W n = ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) • coeffFace k A W n i := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hlast : ((Fin.last n).succ : Fin (n + 2)) = Fin.last (n + 1) := Fin.succ_last n
  simp only [Fin.val_zero, pow_zero, one_smul, coeffFace_zero, Fin.val_succ, Fin.val_castSucc,
    Fin.succ_castSucc, coeffFace_interior, hlast, coeffFace_last, Fin.val_last]
  rw [barCoeffD]
  abel

/-- **The bar differential as an alternating sum of faces.** -/
theorem barDiff_eq_sum_barFace (n : ℕ) :
    barDiff k A W n = ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) • barFace k A W n i := by
  rw [barDiff_eq_ofCoeff, barCoeffD_eq_sum_coeffFace, ofCoeff_sum]
  simp only [ofCoeff_smul, barFace]

/-! ### Evaluation of the individual faces on a pure generator -/

@[simp] theorem barFace_zero_apply (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n 0 (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = (a₀ * v 0) ⊗ₜ[k] (tprod k (Fin.tail v) ⊗ₜ[k] w) := by
  rw [barFace, coeffFace_zero, ofCoeff_tmul, coeffFaceZero]
  simp [TensorProduct.smul_tmul']

@[simp] theorem barFace_interior_apply (n : ℕ) (j : Fin n) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n j.succ.castSucc (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = a₀ ⊗ₜ[k] (tprod k (Fin.contractNth (Fin.castSucc j) (· * ·) v) ⊗ₜ[k] w) := by
  rw [barFace, coeffFace_interior, ofCoeff_tmul, coeffFaceInterior]
  simp [TensorProduct.smul_tmul']

@[simp] theorem barFace_last_apply (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n (Fin.last (n + 1)) (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = a₀ ⊗ₜ[k] (tprod k (Fin.init v) ⊗ₜ[k] (v (Fin.last n) • w)) := by
  rw [barFace, coeffFace_last, ofCoeff_tmul, coeffFaceLast]
  simp [TensorProduct.smul_tmul']

omit [Module A W] [IsScalarTower k A W] in
/-- Two `A`-linear maps out of a bar term agree once they agree on the pure generators
`a₀ ⊗ (tprod v ⊗ w)`. -/
theorem barModule_hom_ext {n m : ℕ}
    {F G : barModule k A W (n + 1) →ₗ[A] barModule k A W m}
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

/-! ### The simplicial identity `barFace i ∘ barFace j = barFace (j-1) ∘ barFace i` and `d ∘ d = 0`

We present each *merge* face (faces `0 … n`) uniformly as a single `Fin.contractNth` on the tuple
`Fin.cons a₀ v` obtained by prepending the leading `A`-factor `a₀` to the middle tensor `v`
(`barFace_castSucc_apply`).  With this description the simplicial identity among merge faces is
exactly `contractNth_contractNth`; only the interactions with the *last* face (which acts the
trailing factor on `W`) need separate treatment. -/

section BarSquareZero

/-- Contracting the tuple `Fin.cons a g` at a positive slot `i.succ` leaves the leading entry `a`
untouched and contracts `g` at slot `i`. -/
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

/-- Contracting `Fin.cons a g` at slot `0` merges `a` into `g 0` and shifts the rest down. -/
theorem contractNth_zero_cons {m : ℕ} (a : A) (g : Fin (m + 1) → A) :
    Fin.contractNth 0 (· * ·) (Fin.cons a g) = Fin.cons (a * g 0) (Fin.tail g) := by
  funext k
  refine Fin.cases ?_ (fun p => ?_) k
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]
    simp
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp), Fin.cons_succ, Fin.cons_succ, Fin.tail]

/-- **Uniform description of a merge face.** For `i : Fin (n+1)`, the merge face
`barFace n i.castSucc`
sends the generator `a₀ ⊗ (tprod v ⊗ w)` to the generator whose middle-and-leading tuple is
`Fin.contractNth i.castSucc (·*·) (Fin.cons a₀ v)` (prepend `a₀` to `v`, then merge at slot `i`). -/
theorem barFace_castSucc_apply (n : ℕ) (i : Fin (n + 1)) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barFace k A W n i.castSucc (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = Fin.contractNth i.castSucc (· * ·) (Fin.cons a₀ v) 0 ⊗ₜ[k]
          (tprod k (Fin.tail (Fin.contractNth i.castSucc (· * ·) (Fin.cons a₀ v))) ⊗ₜ[k] w) := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [Fin.castSucc_zero, barFace_zero_apply, contractNth_zero_cons, Fin.cons_zero, Fin.tail_cons]
  · rw [barFace_interior_apply, ← Fin.succ_castSucc, contractNth_succ_cons, Fin.cons_zero,
      Fin.tail_cons]

/-- A *non-last* merge commutes with dropping the last entry: contracting at a slot `p.castSucc`
(which never touches the final pair) equals contracting the truncation and re-appending the
untouched final entry. -/
theorem contractNth_castSucc_eq_snoc {m : ℕ} (p : Fin m) (u : Fin (m + 2) → A) :
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

/-- The *last-pair* merge, contracting the final two entries, keeps the leading block and appends
their product. -/
theorem contractNth_lastMerge_eq_snoc {m : ℕ} (u : Fin (m + 2) → A) :
    Fin.contractNth (Fin.last m).castSucc (· * ·) u
      = Fin.snoc (fun i : Fin m => u i.castSucc.castSucc)
          (u (Fin.castSucc (Fin.last m)) * u (Fin.last (m + 1))) := by
  funext k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · rw [Fin.snoc_last, Fin.contractNth_apply_of_eq _ _ _ _
        (by simp only [Fin.val_castSucc, Fin.val_last]), Fin.succ_last]
  · rw [Fin.snoc_castSucc, Fin.contractNth_apply_of_lt _ _ _ _
        (by simp only [Fin.val_castSucc, Fin.val_last]; omega)]

/-- **Simplicial identity for the bar faces.** For `i < j`,
`barFace i ∘ barFace j = barFace (j-1) ∘ barFace i`, the merge-face version of `δᵢ δⱼ = δ_{j-1} δᵢ`.
This is the combinatorial core of `d ∘ d = 0`. -/
theorem barFace_comp_barFace (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3))
    (hij : (i : ℕ) < (j : ℕ)) :
    (barFace k A W n i).comp (barFace k A W (n + 1) j)
      = (barFace k A W n (j.pred (by rintro rfl; simp only [Fin.val_zero] at hij; omega))).comp
          (barFace k A W (n + 1) i.castSucc) := by
  apply barModule_hom_ext
  intro a₀ v w
  simp only [LinearMap.comp_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i₀, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
  · -- (merge, merge)
    have hj0 : j₀ ≠ 0 := by
      rintro rfl; simp only [Fin.val_castSucc, Fin.val_zero] at hij; omega
    have hpq : ((Fin.castSucc i₀ : Fin (n + 2)) : ℕ) < ((Fin.castSucc j₀ : Fin (n + 3)) : ℕ) := by
      simpa using hij
    rw [barFace_castSucc_apply, barFace_castSucc_apply, Fin.cons_self_tail,
        ← Fin.castSucc_pred_eq_pred_castSucc, barFace_castSucc_apply, barFace_castSucc_apply,
        Fin.cons_self_tail,
        contractNth_contractNth (· * ·) mul_assoc (Fin.castSucc i₀) (Fin.castSucc j₀) hpq
          (Fin.cons a₀ v), ← Fin.castSucc_pred_eq_pred_castSucc]
    all_goals exact hj0
  · -- (merge, last): case B
    rw [barFace_last_apply, barFace_castSucc_apply, Fin.pred_last, barFace_castSucc_apply,
        barFace_last_apply]
    have hG : Fin.contractNth (Fin.castSucc i₀).castSucc (· * ·) (Fin.cons a₀ v)
        = Fin.snoc (Fin.contractNth (Fin.castSucc i₀) (· * ·) (Fin.cons a₀ (Fin.init v)))
            (v (Fin.last (n + 1))) := by
      rw [contractNth_castSucc_eq_snoc]
      congr 1
      congr 1
      funext j
      refine Fin.cases ?_ (fun p => ?_) j
      · simp [Fin.init]
      · simp only [Fin.init, ← Fin.succ_castSucc, Fin.cons_succ]
    rw [hG, Fin.snoc_apply_zero, ← Fin.tail_init_eq_init_tail, Fin.init_snoc]
    simp only [Fin.tail]
    rw [Fin.succ_last, Fin.snoc_last]
  · -- (last, merge): impossible from i < j
    exfalso; simp only [Fin.val_last, Fin.val_castSucc] at hij; omega
  · -- (last, last): case E
    rw [barFace_last_apply, barFace_last_apply, Fin.pred_last, barFace_castSucc_apply,
        barFace_last_apply, contractNth_lastMerge_eq_snoc, Fin.snoc_apply_zero,
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

/-- **`d ∘ d = 0`.** The composite of two consecutive bar differentials vanishes, so the bar terms
and differentials assemble into a chain complex. -/
theorem barDiff_comp_barDiff (n : ℕ) :
    (barDiff k A W n).comp (barDiff k A W (n + 1)) = 0 := by
  classical
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, barDiff_eq_sum_barFace, LinearMap.coe_sum, Finset.sum_apply,
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
  · -- lands in Sᶜ
    intro p hp
    have hji : (p.2 : ℕ) ≤ (p.1 : ℕ) := by simpa [hS] using (Finset.mem_filter.mp hp).2
    simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le,
      Fin.val_succ, Fin.val_castLT]
    omega
  · -- injective
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    have h1 : (j : ℕ) = (j' : ℕ) := by simpa [Fin.val_castLT] using congrArg (fun q => (q.1 : ℕ)) h
    have h2 : (i : ℕ) = (i' : ℕ) := by
      have := congrArg (fun q => (q.2 : ℕ)) h
      simpa [Fin.val_succ] using this
    ext <;> assumption
  · -- surjective
    rintro ⟨i', j'⟩ hij'
    have hlt : (i' : ℕ) < (j' : ℕ) := by
      simpa [hS, Finset.mem_compl, Finset.mem_filter, not_le] using hij'
    have hj0 : j' ≠ 0 := by rintro rfl; simp only [Fin.val_zero] at hlt; omega
    refine ⟨(j'.pred hj0, Fin.castSucc i'), ?_, ?_⟩
    · simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]
      omega
    · simp only [Fin.castLT_castSucc, Fin.succ_pred]
  · -- term identification
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

/-- **The relative bar chain complex** `… → P₂ → P₁ → P₀` of a representation `W`, assembled from
the projective bar terms `barObj` and the bar differential `barDiff` via `barDiff_comp_barDiff`. -/
noncomputable def barComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun n => barObj k A W n) (fun n => ModuleCat.ofHom (barDiff k A W n))
    (fun n => by
      ext y
      exact LinearMap.congr_fun (barDiff_comp_barDiff k A W n) y)

end BarSquareZero

/-! ### The augmentation as a chain map `barComplex ⟶ W[0]`

The augmentation `ε : P₀ → W` extends to a chain map from `barComplex` to the complex `W`
concentrated in degree `0`, because `ε ∘ d₀ = 0`: the first differential
`d₀ : P₁ → P₀` sends `a₀ ⊗ (a₁ ⊗ w)` to `(a₀ a₁) ⊗ w - a₀ ⊗ (a₁ • w)`, and both summands have
the same image `(a₀ a₁) • w` under `ε`, so they cancel. This chain map is the `π` datum of the
projective resolution. -/

section Augmentation

omit [Module A W] [IsScalarTower k A W] in
@[simp] lemma barCoeffZeroEquiv_tprod (v : Fin 0 → A) (w : W) :
    barCoeffZeroEquiv k A W (tprod k v ⊗ₜ[k] w) = w := by
  simp [barCoeffZeroEquiv, PiTensorProduct.isEmptyEquiv_apply_tprod]

/-- The augmentation kills the image of the first bar differential: `ε ∘ d₀ = 0`. -/
theorem ε_comp_barDiff_zero :
    (ε k A W).comp (barDiff k A W 0) = 0 := by
  refine TensorProduct.AlgebraTensorModule.ext fun a₀ x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
      induction p using PiTensorProduct.induction_on with
      | smul_tprod r v =>
          have hgen : ε k A W (barDiff k A W 0 (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))) = 0 := by
            rw [barDiff_tmul_tprod]
            simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, map_add,
              LinearMap.map_smul_of_tower, ε_tmul, barCoeffZeroEquiv_tprod]
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

/-- The augmentation `ε : P₀ → W`, packaged as a chain map from the bar complex to the complex
`W` concentrated in degree `0`. This is the `π` datum of the bar projective resolution. -/
noncomputable def barπChainMap :
    barComplex k A W ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A W) :=
  (ChainComplex.toSingle₀Equiv (barComplex k A W) (ModuleCat.of A W)).symm
    ⟨barπ k A W, by
      have hd : (barComplex k A W).d 1 0 = ModuleCat.ofHom (barDiff k A W 0) :=
        ChainComplex.of_d (fun n => barObj k A W n)
          (fun n => ModuleCat.ofHom (barDiff k A W n)) 0
      rw [hd, barπ]
      ext x
      exact LinearMap.congr_fun (ε_comp_barDiff_zero k A W) x⟩

@[simp] lemma barπChainMap_f_zero :
    (barπChainMap k A W).f 0 = barπ k A W := by
  simp [barπChainMap]

end Augmentation

/-! ### The `k`-linear contracting homotopy `s(x) = 1 ⊗ x` and exactness

The relative bar resolution is `k`-split exact: the `k`-linear (NOT `A`-linear) contracting homotopy
`s(a₀ ⊗ (tprod v ⊗ w)) = 1 ⊗ (tprod (Fin.cons a₀ v) ⊗ w)` inserts the leading `A`-factor into the
tensor string, and satisfies the standard identities `ε ∘ s₋₁ = id`, `d₀ ∘ s₀ + s₋₁ ∘ ε = id`, and
`d_{n+1} ∘ s_{n+1} + s_n ∘ d_n = id`.  On a pure generator the alternating faces telescope: the
`s`-inserted leading `1` makes face `0` of the next differential undo the contraction, and the
remaining `n+1` faces of `d ∘ s` match the `n+1` faces of `s ∘ d` with a sign shift.  Every map here
is `k`-linear, so the successor issue can push exactness through the (exact, faithful)
restriction-of-scalars functor to conclude `QuasiIso`. -/

section BarContraction

/-- The `k`-linear "cons" on tensor powers, `a ⊗ tprod v ↦ tprod (Fin.cons a v)`; the inverse
direction of `barConsSplit`. -/
noncomputable def barConsMerge (n : ℕ) : A ⊗[k] (⨂[k]^n A) →ₗ[k] ⨂[k]^(n + 1) A :=
  TensorProduct.lift ((PiTensorProduct.lift (s := fun _ : Fin n => A)).toLinearMap.comp
    (PiTensorProduct.tprod k
      (s := fun _ : Fin (n + 1) => A)).curryLeft)

omit [Module A W] [IsScalarTower k A W] in
@[simp] theorem barConsMerge_tmul (n : ℕ) (a : A) (v : Fin n → A) :
    barConsMerge k A n (a ⊗ₜ[k] tprod k v) = PiTensorProduct.tprod k (Fin.cons a v) := by
  simp only [barConsMerge, TensorProduct.lift.tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, MultilinearMap.curryLeft_apply]

/-- The `k`-linear contracting homotopy in degree `n`, inserting the leading `A`-factor into the
tensor string: `s(a₀ ⊗ (tprod v ⊗ w)) = 1 ⊗ (tprod (Fin.cons a₀ v) ⊗ w)`. -/
noncomputable def barContraction (n : ℕ) : barModule k A W n →ₗ[k] barModule k A W (n + 1) :=
  oneTmul k A W (n + 1)
    ∘ₗ (TensorProduct.map (barConsMerge k A n) LinearMap.id
        ∘ₗ (TensorProduct.assoc k A (⨂[k]^n A) W).symm.toLinearMap)

omit [Module A W] [IsScalarTower k A W] in
@[simp] theorem barContraction_apply (n : ℕ) (a₀ : A) (v : Fin n → A) (w : W) :
    barContraction k A W n (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w))
      = (1 : A) ⊗ₜ[k] (PiTensorProduct.tprod k (Fin.cons a₀ v) ⊗ₜ[k] w) := by
  simp only [barContraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul, barConsMerge_tmul, LinearMap.id_coe,
    id_eq, oneTmul_apply]

/-- The base contracting homotopy `s₋₁ : W → P₀`, `w ↦ 1 ⊗ (unit ⊗ w)`. -/
noncomputable def barContractionBase : W →ₗ[k] barModule k A W 0 :=
  oneTmul k A W 0 ∘ₗ (barCoeffZeroEquiv k A W).symm.toLinearMap

omit [Module A W] [IsScalarTower k A W] in
@[simp] theorem barContractionBase_apply (w : W) :
    barContractionBase k A W w = (1 : A) ⊗ₜ[k] (barCoeffZeroEquiv k A W).symm w := by
  simp [barContractionBase]

omit [Module A W] [IsScalarTower k A W] in
/-- The inverse identification: any `tprod (u : Fin 0 → A) ⊗ w` (empty tensor power) is
`(barCoeffZeroEquiv).symm w`, since the empty `tprod` maps to `1`. -/
theorem barCoeffZeroEquiv_symm_tmul (u : Fin 0 → A) (y : W) :
    (barCoeffZeroEquiv k A W).symm y = tprod k u ⊗ₜ[k] y := by
  apply (barCoeffZeroEquiv k A W).injective
  rw [LinearEquiv.apply_symm_apply]
  simp [barCoeffZeroEquiv, PiTensorProduct.isEmptyEquiv_apply_tprod]

omit [Module A W] [IsScalarTower k A W] in
/-- Two `k`-linear maps out of a bar term agree once they agree on the pure generators
`a₀ ⊗ (tprod v ⊗ w)`. -/
theorem barModule_hom_ext_k {n : ℕ} {X : Type u} [AddCommGroup X] [Module k X]
    {F G : barModule k A W n →ₗ[k] X}
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

/-- **Homotopy identity (base).** `ε ∘ s₋₁ = id` on `W`. -/
theorem ε_comp_barContractionBase :
    ((ε k A W).restrictScalars k).comp (barContractionBase k A W) = LinearMap.id := by
  ext w
  simp [barContractionBase_apply, ε_tmul, one_smul]

/-- **Homotopy identity (degree 0).** `d₀ ∘ s₀ + s₋₁ ∘ ε = id` on `P₀`. -/
theorem barDiff_zero_comp_barContraction_add :
    ((barDiff k A W 0).restrictScalars k).comp (barContraction k A W 0)
      + (barContractionBase k A W).comp ((ε k A W).restrictScalars k) = LinearMap.id := by
  apply barModule_hom_ext_k
  intro a₀ v w
  have hε : barCoeffZeroEquiv k A W (tprod k v ⊗ₜ[k] w) = w :=
    ((LinearEquiv.symm_apply_eq (barCoeffZeroEquiv k A W)).1
      (barCoeffZeroEquiv_symm_tmul k A W v w)).symm
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearMap.id_coe, id_eq, barContraction_apply, ε_tmul, hε]
  rw [barDiff_tmul_tprod]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.cons_zero, one_mul,
    Fin.tail_cons, zero_add, pow_one]
  have einit : Fin.init (Fin.cons (α := fun _ : Fin 1 => A) a₀ v) = v :=
    funext fun i => i.elim0
  rw [show (Fin.last 0 : Fin (0 + 1)) = 0 from Fin.ext rfl, Fin.cons_zero, einit]
  have hbase : barContractionBase k A W (a₀ • w)
      = (1 : A) ⊗ₜ[k] (tprod k v ⊗ₜ[k] (a₀ • w)) := by
    rw [barContractionBase_apply]
    congr 1
    exact barCoeffZeroEquiv_symm_tmul k A W v (a₀ • w)
  rw [hbase]
  module

omit [Module A W] [IsScalarTower k A W] in
/-- `(-1)^(m+1) • y = -((-1)^m • y)`: shifting the exponent by one flips the sign. -/
private theorem neg_one_pow_succ_smul {M : Type u} [AddCommGroup M] [Module k M]
    (m : ℕ) (y : M) : (-1 : k) ^ (m + 1) • y = -((-1 : k) ^ m • y) := by
  rw [pow_succ, mul_smul, neg_one_smul, smul_neg]

omit [Module A W] [IsScalarTower k A W] in
/-- The two alternating sums that appear in `d ∘ s` and `s ∘ d` are negatives of each other:
their signs differ by one exponent step. -/
private theorem sum_neg_one_pow_succ_smul {M : Type u} [AddCommGroup M] [Module k M]
    {m : ℕ} (g : Fin m → M) :
    (∑ j : Fin m, (-1 : k) ^ ((j : ℕ) + 1 + 1) • g j)
      = -∑ j : Fin m, (-1 : k) ^ ((j : ℕ) + 1) • g j := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => neg_one_pow_succ_smul k ((j : ℕ) + 1) (g j)

/-- **Homotopy identity (degree n+1), on a pure generator.** `d_{n+1} (s_{n+1} x) + s_n (d_n x) = x`
for `x = a₀ ⊗ (tprod v ⊗ w)`.  The alternating faces telescope: face `0` of `d_{n+1} ∘ s_{n+1}`
undoes the `s`-inserted leading `1`, and the remaining `n+1` faces cancel the `n+1` faces of
`s_n ∘ d_n` with a sign shift.  (Stated pointwise; the induction wrapper
`barDiff_contraction_homotopy` extends it to all of `Pₙ₊₁`.) -/
theorem barDiff_barContraction_gen (n : ℕ) (a₀ : A) (v : Fin (n + 1) → A) (w : W) :
    barDiff k A W (n + 1) (barContraction k A W (n + 1) (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)))
      + barContraction k A W n (barDiff k A W n (a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w)))
      = a₀ ⊗ₜ[k] (tprod k v ⊗ₜ[k] w) := by
  have hinit : Fin.init (Fin.cons (α := fun _ : Fin (n + 2) => A) a₀ v)
      = Fin.cons (α := fun _ : Fin (n + 1) => A) a₀ (Fin.init v) := by
    funext i
    refine Fin.cases ?_ (fun p => ?_) i
    · simp [Fin.init, Fin.castSucc_zero]
    · simp only [Fin.init, ← Fin.succ_castSucc, Fin.cons_succ]
  rw [barContraction_apply, barDiff_tmul_tprod, barDiff_tmul_tprod, map_add, map_add, map_sum]
  simp only [map_smul, barContraction_apply, Fin.cons_zero, one_mul, Fin.tail_cons,
    ← Fin.succ_last, Fin.cons_succ]
  rw [hinit, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, contractNth_zero_cons, Fin.val_zero, Fin.val_succ,
    ← Fin.succ_castSucc, contractNth_succ_cons]
  have hsign (m : ℕ) (z : barModule k A W (n + 1)) :
      (-1 : k) ^ (m + 1) • z = -((-1 : k) ^ m • z) :=
    neg_one_pow_succ_smul k m z
  let zfirst : barModule k A W (n + 1) :=
    (1 : A) ⊗ₜ[k] (tprod k (Fin.cons (a₀ * v 0) (Fin.tail v)) ⊗ₜ[k] w)
  let zmid (x : Fin n) : barModule k A W (n + 1) :=
    (1 : A) ⊗ₜ[k] (PiTensorProduct.tprod k
      (Fin.cons (α := fun _ : Fin (n + 1) => A) a₀
        (x.castSucc.contractNth (fun x₁ x₂ => x₁ * x₂) v)) ⊗ₜ[k] w)
  let zlast : barModule k A W (n + 1) :=
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

/-- **Homotopy identity (degree n+1).** `d_{n+1} (s_{n+1} x) + s_n (d_n x) = x` for every
`x : Pₙ₊₁`, extending `barDiff_barContraction_gen` off the pure generators by `k`-bilinearity. -/
theorem barDiff_contraction_homotopy (n : ℕ) (x : barModule k A W (n + 1)) :
    barDiff k A W (n + 1) (barContraction k A W (n + 1) x)
      + barContraction k A W n (barDiff k A W n x) = x := by
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
              exact barDiff_barContraction_gen k A W n a₀ v (r • w)
          | add p q hp hq =>
              rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
              simp only [map_add]; rw [add_add_add_comm, hp, hq]

end BarContraction

/-! ### The bar resolution as a `ProjectiveResolution`

The relative bar complex `barComplex`, its projective terms, and the augmentation `barπChainMap`
assemble into an honest `CategoryTheory.ProjectiveResolution (ModuleCat.of A W)`.  The
`k`-linear contracting homotopy `barContraction` / `barContractionBase` splits every bar
differential, so at the level of underlying `k`-modules (which are the same sets as the underlying
`A`-modules) every cycle is a boundary: this gives exactness in positive degrees and, together with
the surjectivity of `ε`, the degree-`0` homology isomorphism `H₀(barComplex) ≅ W`. -/

section Resolution

open CategoryTheory Limits

/-- The relative bar complex is exact in every positive degree.  The `k`-linear contracting
homotopy `barContraction` splits `barDiff`, so any cycle `x` with `barDiff n x = 0` is the boundary
`barDiff (n+1) (barContraction (n+1) x)`. -/
theorem barComplex_exactAt_succ (n : ℕ) : (barComplex k A W).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hf : ((barComplex k A W).sc' (n + 2) (n + 1) n).f
      = ModuleCat.ofHom (barDiff k A W (n + 1)) :=
    ChainComplex.of_d (fun n => barObj k A W n)
      (fun n => ModuleCat.ofHom (barDiff k A W n)) (n + 1)
  have hg : ((barComplex k A W).sc' (n + 2) (n + 1) n).g
      = ModuleCat.ofHom (barDiff k A W n) :=
    ChainComplex.of_d (fun n => barObj k A W n)
      (fun n => ModuleCat.ofHom (barDiff k A W n)) n
  intro x hx
  refine ⟨barContraction k A W (n + 1) x, ?_⟩
  rw [hg] at hx
  rw [hf]
  change barDiff k A W n x = 0 at hx
  change barDiff k A W (n + 1) (barContraction k A W (n + 1) x) = x
  have h := barDiff_contraction_homotopy k A W n x
  rw [hx, map_zero, add_zero] at h
  exact h

/-- The augmentation `barπChainMap` is a **quasi-isomorphism**.  In positive degrees both complexes
are exact (`barComplex_exactAt_succ` for the source; `single₀ W` is trivially exact away from `0`);
in degree `0` the augmentation `ε` presents `W` as the cokernel of `barDiff 0` (surjective, with
kernel exactly the boundaries by the degree-`0` homotopy identity), so the induced map on `H₀` is an
isomorphism. -/
theorem barπChainMap_quasiIso : QuasiIso (barπChainMap k A W) := by
  rw [quasiIso_iff]
  rintro (_ | n)
  · -- Degree `0`: transport to the clean augmentation short complex
    -- `barModule 1 → barModule 0 → W`.
    have hf0 : (barComplex k A W).d 1 0 = ModuleCat.ofHom (barDiff k A W 0) :=
      ChainComplex.of_d (fun n => barObj k A W n)
        (fun n => ModuleCat.ofHom (barDiff k A W n)) 0
    have hTexact :
        (ShortComplex.moduleCatMk (barDiff k A W 0) (ε k A W)
          (ε_comp_barDiff_zero k A W)).Exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      refine ⟨barContraction k A W 0 x, ?_⟩
      change ε k A W x = 0 at hx
      change barDiff k A W 0 (barContraction k A W 0 x) = x
      have h := LinearMap.congr_fun (barDiff_zero_comp_barContraction_add k A W) x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
        LinearMap.id_coe, id_eq] at h
      rw [hx, map_zero, add_zero] at h
      exact h
    have hTepi :
        Epi (ShortComplex.moduleCatMk (barDiff k A W 0) (ε k A W)
          (ε_comp_barDiff_zero k A W)).g := by
      have hg : (ShortComplex.moduleCatMk (barDiff k A W 0) (ε k A W)
          (ε_comp_barDiff_zero k A W)).g = ModuleCat.ofHom (ε k A W) := rfl
      rw [hg, ModuleCat.epi_iff_surjective]
      exact ε_surjective k A W
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)).2 ⟨hTexact, hTepi⟩
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact barComplex_exactAt_succ k A W n

/-- **The relative bar resolution of a representation `W` of a `k`-algebra `A`** as an honest
`CategoryTheory.ProjectiveResolution (ModuleCat.of A W)`: the free `A`-modules
`Pₙ = A ⊗_k A^{⊗n} ⊗_k W` (`barComplex`), the alternating-sum bar differential, and the augmentation
`ε : P₀ → W` (`barπChainMap`), which is a quasi-isomorphism because the `k`-split relative bar
complex is `k`-linearly contractible.  This is the input to
`ProjectiveResolution.extAddEquivCohomologyClass` computing `Ext_A` (see `Problem_8_2_6_ii`). -/
noncomputable def _root_.Etingof.barResolution :
    CategoryTheory.ProjectiveResolution (ModuleCat.of A W) where
  complex := barComplex k A W
  π := barπChainMap k A W
  projective n := instProjectiveBarObj k A W n
  quasiIso := barπChainMap_quasiIso k A W

/-- When `A` and `W` are finite dimensional over `k`, every term of the bar resolution complex is a
finitely generated `A`-module. Together with the `Projective` instances
(`barResolution.projective`), this exhibits `Etingof.barResolution` as a finitely generated
projective resolution of `ModuleCat.of A W`, exactly the input required by
`Etingof.Problem_8_2_8_extₖ`, the finite generation being what makes the degreewise `Hom`-tensor
comparison an isomorphism. -/
instance instFiniteBarResolutionComplexX (n : ℕ)
    [FiniteDimensional k A] [FiniteDimensional k W] :
    Module.Finite A ((Etingof.barResolution k A W).complex.X n) :=
  inferInstanceAs (Module.Finite A (barModule k A W n))

end Resolution

end Etingof.BarResolution
