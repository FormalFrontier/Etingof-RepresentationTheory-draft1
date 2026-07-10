import Mathlib

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
compute `Ext_A` via `CategoryTheory.ProjectiveResolution.extAddEquivCohomologyClass` (see #6297,
consumed by `Problem_8_2_6_ii`).

## What is formalized here

This file provides the **terms** of the resolution as free/projective `A`-modules, together with
the **augmentation**:

* `Etingof.BarResolution.barCoeff k A W n` — the `k`-module `A^{⊗_k n} ⊗_k W` of bar coefficients.
* `Etingof.BarResolution.barModule k A W n = A ⊗_k (A^{⊗n} ⊗_k W)` — the `n`-th term, an
  `A`-module via left multiplication on the leading factor; a *free* `A`-module
  (`instance : Module.Free A (barModule …)`).
* `Etingof.BarResolution.barObj k A W n : ModuleCat A` — the term packaged as an object of
  `ModuleCat A`, with a `Projective` instance.
* `Etingof.BarResolution.ε k A W : barModule k A W 0 →ₗ[A] W` — the augmentation `a ⊗ w ↦ a • w`,
  proved surjective (`ε_surjective`); `barπ` is its packaging as a `ModuleCat` morphism.

It also provides the three reusable `k`-linear **face-map primitives** on the tensor powers
`⨂[k]^(n+1) A` from which the bar differential's faces are assembled — `barConsSplit` (pull off the
first factor), `barSnocSplit` (pull off the last factor), and `barMerge i` (merge the adjacent
factors `i`, `i+1` via the multiplication of `A`) — see the section below.

The bar **differential**, the identity `d ∘ d = 0`, exactness via the `k`-linear contracting
homotopy `s(x) = 1 ⊗ x`, and the packaging into
`CategoryTheory.ProjectiveResolution (ModuleCat.of A W)` are follow-up work that builds on the
terms and augmentation defined here.
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
`TensorProduct.leftModule` instance), and — because `k` is a field, so `barCoeff k A W n` is a free
`k`-module — a *free* `A`-module. -/
abbrev barModule (n : ℕ) : Type u := A ⊗[k] barCoeff k A W n

/-- Each bar term is a free `A`-module: it is `A ⊗_k X` with `X` a free `k`-module. -/
instance instFreeBarModule (n : ℕ) : Module.Free A (barModule k A W n) :=
  inferInstanceAs (Module.Free A (A ⊗[k] barCoeff k A W n))

/-- Each bar term is a projective `A`-module (being free). -/
instance instProjectiveBarModule (n : ℕ) : Module.Projective A (barModule k A W n) :=
  inferInstance

/-- The `n`-th bar term packaged as an object of `ModuleCat A`. -/
noncomputable def barObj (n : ℕ) : ModuleCat.{u} A := ModuleCat.of A (barModule k A W n)

/-- Each bar term is projective as an object of `ModuleCat A`. -/
instance instProjectiveBarObj (n : ℕ) : Projective (barObj k A W n) :=
  inferInstanceAs (Projective (ModuleCat.of A (barModule k A W n)))

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

* `barConsSplit` — pull off the first factor, `tprod v ↦ v 0 ⊗ tprod (Fin.tail v)`;
* `barSnocSplit` — pull off the last factor, `tprod v ↦ tprod (Fin.init v) ⊗ v (Fin.last n)`;
* `barMerge i` — merge the adjacent factors `i` and `i+1` via the multiplication of `A`
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

end Etingof.BarResolution
