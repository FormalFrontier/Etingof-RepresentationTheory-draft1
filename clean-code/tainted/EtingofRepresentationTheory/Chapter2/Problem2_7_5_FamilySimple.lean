import EtingofRepresentationTheory.Chapter2.Problem2_7_5_Family

/-!
# Problem 2.7.5(c): irreducibility of the classifying family `V(α,β)`

`Problem2_7_5_Family.lean` constructs, for a primitive root of unity `q` of order `n` and
parameters `(α, β) ∈ ℂˣ × ℂˣ`, the `n`-dimensional `qWeylAlgebra ℂ q`-module `V(α,β)` on
`Fin n → ℂ`, with `x` acting as the twisted cyclic shift `Xlin` and `y` acting diagonally
by `Ylin` (`y·eⱼ = β·qʲ·eⱼ`).

This file proves that every member of the family is **simple**, following the book's hint that
the argument is "similar to Problem 2.7.4(c)":

* the `n` eigenvalues `β·qʲ` of the diagonal operator `y` are pairwise distinct
  (`wY_injective`), because `q` is primitive of order `n`;
* hence, given a nonzero `w` in a nonzero submodule `W` with `w k ≠ 0`, applying the operator
  `∏_{j ≠ k} (y - β·qʲ)` (a Lagrange-style separator, built here as an explicit iterated
  difference rather than through polynomial API) kills every coordinate but the `k`-th and
  produces a nonzero multiple of the basis vector `e_k`, so `e_k ∈ W`;
* the twisted shift `x` permutes the basis vectors `e_j` cyclically and transitively, so every
  `e_j` lies in `W`, and `W = ⊤`.

## Main results

* `Etingof.Problem2_7_5.wY_injective` — the `y`-eigenvalues `β·qᵏ` are pairwise distinct.
* `Etingof.Problem2_7_5.famModule_isSimpleModule` — `V(α,β)` is a simple `qWeylAlgebra ℂ q`-module
  for every choice of parameters `(α, β)`.
-/

namespace Etingof.Problem2_7_5

open Etingof

section Simple

variable (q α β : ℂˣ) (N : ℕ) [NeZero N]

/-! ### The `y`-eigenvalues are pairwise distinct -/

omit [NeZero N] in
/-- The diagonal weights `wY k = β·qᵏ` of `y` are pairwise distinct: `q` has order exactly `N`,
so the powers `q⁰, …, q^{N-1}` are distinct, and `β ≠ 0`. -/
theorem wY_injective (hqorder : orderOf q = N) : Function.Injective (wY q β N) := by
  intro i j hij
  simp only [wY] at hij
  have h : (q : ℂ) ^ (i : ℕ) = (q : ℂ) ^ (j : ℕ) := mul_left_cancel₀ β.ne_zero hij
  have hu : q ^ (i : ℕ) = q ^ (j : ℕ) := Units.ext (by push_cast; exact h)
  have hmod : (i : ℕ) ≡ (j : ℕ) [MOD N] := by
    have hmod' := pow_eq_pow_iff_modEq.mp hu
    rwa [hqorder] at hmod'
  have hi : (i : ℕ) % N = (i : ℕ) := Nat.mod_eq_of_lt i.isLt
  have hj : (j : ℕ) % N = (j : ℕ) := Nat.mod_eq_of_lt j.isLt
  exact Fin.ext (by rw [← hi, ← hj]; exact hmod)

/-! ### Irreducibility -/

/-- **Irreducibility of the classifying family.** For every pair of parameters `(α, β) ∈ ℂˣ × ℂˣ`
the module `V(α,β)` is a simple `qWeylAlgebra ℂ q`-module.

The proof separates the `y`-eigenlines using the operator `∏_{j ≠ k} (y - β·qʲ)` and then sweeps
the resulting basis vector around the cycle with the twisted shift `x`. -/
theorem famModule_isSimpleModule (hqorder : orderOf q = N) :
    letI := famModule q α β N hqorder
    IsSimpleModule (qWeylAlgebra ℂ q) (Fin N → ℂ) := by
  classical
  letI := famModule q α β N hqorder
  haveI : IsScalarTower ℂ (qWeylAlgebra ℂ q) (Fin N → ℂ) :=
    famModule_isScalarTower q α β N hqorder
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  -- The generator actions, with the module instance already fixed.
  have hx : ∀ f : Fin N → ℂ, (QWeyl.qWeylMono q (1, 0)) • f = Xlin α N f := fun f =>
    famModule_x_smul q α β N hqorder f
  have hy : ∀ f : Fin N → ℂ, (QWeyl.qWeylMono q (0, 1)) • f = Ylin q β N f := fun f =>
    famModule_y_smul q α β N hqorder f
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun W => ?_ }
  rcases eq_or_ne W ⊥ with hWbot | hWbot
  · exact Or.inl hWbot
  refine Or.inr ?_
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hWbot
  -- `W` is closed under the ambient `ℂ`-action, because `ℂ` acts through `qWeylAlgebra ℂ q`.
  have hsmulC : ∀ (c : ℂ) (v : Fin N → ℂ), v ∈ W → c • v ∈ W := by
    intro c v hv
    have hcv : c • v = (c • (1 : qWeylAlgebra ℂ q)) • v := by rw [smul_assoc, one_smul]
    rw [hcv]
    exact W.smul_mem _ hv
  -- `W` is stable under `y`.
  have hYmem : ∀ v : Fin N → ℂ, v ∈ W → Ylin q β N v ∈ W := by
    intro v hv
    rw [← hy v]
    exact W.smul_mem _ hv
  -- Applying `∏_{j ∈ s} (y - β·qʲ)` to `w` scales the `i`-th coordinate by the product
  -- `∏_{j ∈ s} (β·qⁱ - β·qʲ)`, and stays inside `W`.
  have hsep : ∀ s : Finset (Fin N),
      (fun i => (∏ j ∈ s, (wY q β N i - wY q β N j)) * w i) ∈ W := by
    intro s
    refine Finset.induction_on s (by simpa using hwW) ?_
    intro a s ha ih
    have hfun : (fun i => (∏ j ∈ insert a s, (wY q β N i - wY q β N j)) * w i)
        = Ylin q β N (fun i => (∏ j ∈ s, (wY q β N i - wY q β N j)) * w i)
          - wY q β N a • (fun i => (∏ j ∈ s, (wY q β N i - wY q β N j)) * w i) := by
      funext i
      simp only [Finset.prod_insert ha, Ylin, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    have hscaled : wY q β N a •
        (fun i => (∏ j ∈ s, (wY q β N i - wY q β N j)) * w i) ∈ W :=
      hsmulC _ _ ih
    exact Submodule.sub_mem (R := qWeylAlgebra ℂ q) W (hYmem _ ih) hscaled
  -- Pick a coordinate where `w` does not vanish.
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  -- The separator is nonzero at that coordinate.
  have hcne : (∏ j ∈ Finset.univ.erase k, (wY q β N k - wY q β N j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr fun h =>
      (Finset.mem_erase.mp hj).1 (wY_injective q β N hqorder h).symm
  -- Hence the basis vector `e_k` lies in `W`.
  have hsingle : Pi.single k (1 : ℂ) ∈ W := by
    have hval := hsep (Finset.univ.erase k)
    have heq : (fun i => (∏ j ∈ Finset.univ.erase k, (wY q β N i - wY q β N j)) * w i)
        = ((∏ j ∈ Finset.univ.erase k, (wY q β N k - wY q β N j)) * w k) • Pi.single k (1 : ℂ) := by
      funext i
      by_cases hik : i = k
      · subst hik; simp
      · have hzero : (∏ j ∈ Finset.univ.erase k, (wY q β N i - wY q β N j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩) (sub_self _)
        simp [hzero, hik]
    rw [heq] at hval
    have hscaled := hsmulC
      ((∏ j ∈ Finset.univ.erase k, (wY q β N k - wY q β N j)) * w k)⁻¹ _ hval
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hcne hk), one_smul] at hscaled
  -- The twisted shift moves `e_m` to a nonzero multiple of `e_{m+1}`.
  have hXsingle : ∀ m : Fin N, Pi.single m (1 : ℂ) ∈ W → Pi.single (m + 1) (1 : ℂ) ∈ W := by
    intro m hm
    have hX : Xlin α N (Pi.single m (1 : ℂ)) = wX α N (m + 1) • Pi.single (m + 1) (1 : ℂ) := by
      funext i
      simp only [Xlin, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = m + 1
      · subst hi; simp
      · have hne : i - 1 ≠ m := fun h => hi (sub_eq_iff_eq_add.mp h)
        simp [hne, hi]
    have hmem : Xlin α N (Pi.single m (1 : ℂ)) ∈ W := by
      rw [← hx (Pi.single m (1 : ℂ))]
      exact W.smul_mem _ hm
    rw [hX] at hmem
    have hscaled := hsmulC (wX α N (m + 1))⁻¹ _ hmem
    rwa [smul_smul, inv_mul_cancel₀ (wX_ne α N _), one_smul] at hscaled
  -- Sweeping the cycle: every basis vector lies in `W`.
  have hofNat_zero : Fin.ofNat N 0 = 0 := by
    refine Fin.ext ?_
    change 0 % N = (0 : Fin N).val
    simp
  have hofNat_succ : ∀ m : ℕ, Fin.ofNat N (m + 1) = Fin.ofNat N m + 1 := by
    intro m
    refine Fin.ext ?_
    change (m + 1) % N = (Fin.ofNat N m + (1 : Fin N)).val
    rw [Fin.val_add]
    change (m + 1) % N = (m % N + (1 : Fin N).val) % N
    rw [Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod]
  have hall : ∀ m : ℕ, Pi.single (k + Fin.ofNat N m) (1 : ℂ) ∈ W := by
    intro m
    induction m with
    | zero => rw [hofNat_zero, add_zero]; exact hsingle
    | succ m ih =>
        have hstep := hXsingle _ ih
        rwa [hofNat_succ m, ← add_assoc]
  have hallsingle : ∀ i : Fin N, Pi.single i (1 : ℂ) ∈ W := by
    intro i
    have hmem := hall ((i - k).val)
    have hofNat : Fin.ofNat N ((i - k).val) = i - k := by
      refine Fin.ext ?_
      change (i - k).val % N = (i - k).val
      exact Nat.mod_eq_of_lt (i - k).isLt
    have hik : k + (i - k) = i := by rw [add_comm]; exact sub_add_cancel i k
    rwa [hofNat, hik] at hmem
  -- The basis vectors span, so `W = ⊤`.
  refine Submodule.eq_top_iff'.mpr fun f => ?_
  have hf : f = ∑ i : Fin N, f i • Pi.single i (1 : ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hf]
  exact Submodule.sum_mem _ fun i _ => hsmulC _ _ (hallsingle i)

end Simple

end Etingof.Problem2_7_5
