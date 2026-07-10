import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.BigOperators.Pi

/-!
# Problem 2.16.2: Irreducible representations of the 2-dimensional Lie algebra `[X, Y] = Y`

Let `𝔤` be the two-dimensional Lie algebra with basis `X, Y` and commutation relation
`[X, Y] = Y`. We realize it as the Lie subalgebra of `𝔤𝔩(2, k)` spanned by the matrix units
`X = e₁₁` and `Y = e₁₂` (which satisfy `[e₁₁, e₁₂] = e₁₂`).

The problem asks to classify the irreducible finite-dimensional representations in characteristic
`0` and characteristic `p`, and whether Lie's theorem holds in characteristic `p`. We render the
book's *answers* as the statements:

* **Characteristic `0`** (algebraically closed, so Lie's theorem applies): every irreducible
  finite-dimensional representation is `1`-dimensional, and on such a representation `Y` acts as
  `0`. So the irreducibles are classified by the scalar `X ↦ λ ∈ k` (with `Y ↦ 0`).
* **Characteristic `p`**: Lie's theorem is **false** — there exist irreducible finite-dimensional
  representations of dimension `> 1` (in fact of dimension `p`).

Statement-only (proofs deferred).
-/

namespace Etingof.Problem2_16_2

open scoped Matrix

-- `LieRing.ofAssociativeRing` is a local instance from Mathlib v4.31 onward (to avoid a bracket
-- diamond when a ring acts on itself); re-enable it locally so the matrix Lie algebra elaborates.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [Field k]

/-- The two-dimensional Lie algebra `𝔤 = ⟨X, Y | [X, Y] = Y⟩`, realized as the Lie subalgebra of
`𝔤𝔩(2, k)` spanned by the matrix units `X = e₁₁` and `Y = e₁₂`. (Etingof Problem 2.16.2) -/
noncomputable def g : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  LieSubalgebra.lieSpan k _ {Matrix.single 0 0 1, Matrix.single 0 1 1}

/-- The generator `X = e₁₁` of `𝔤`. -/
noncomputable def X : g k :=
  ⟨Matrix.single 0 0 1, LieSubalgebra.subset_lieSpan (by left; rfl)⟩

/-- The generator `Y = e₁₂` of `𝔤`. -/
noncomputable def Y : g k :=
  ⟨Matrix.single 0 1 1, LieSubalgebra.subset_lieSpan (by right; rfl)⟩

/-- The defining commutation relation `[X, Y] = Y` of `𝔤`. -/
theorem bracket_X_Y : ⁅X k, Y k⁆ = Y k :=
  sorry

/-- **Characteristic `0`.** Every irreducible finite-dimensional representation of `𝔤` is
`1`-dimensional (Lie's theorem, `k` algebraically closed of characteristic `0`). -/
theorem charZero_irreducible_finrank_one [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] :
    Module.finrank k M = 1 :=
  sorry

/-- **Characteristic `0`.** On an irreducible (hence `1`-dimensional) representation, the generator
`Y` acts as `0`; thus the irreducibles are classified by the scalar `λ` with which `X` acts. -/
theorem charZero_Y_acts_zero [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] (m : M) :
    ⁅Y k, m⁆ = 0 :=
  sorry

/-! ## Characteristic `p`: an irreducible representation of dimension `p`

We realize the book's counterexample to Lie's theorem in characteristic `p`. Let `M = k^{ℤ/p}`
(functions on `ℤ/p`). We let `X` act by the diagonal operator `diagOp` with the `p` distinct
eigenvalues `0, 1, …, p-1` (the image of `ℤ/p` in `k` under the prime-field embedding) and `Y`
act by the cyclic shift `shiftOp`. These satisfy `[diagOp, shiftOp] = shiftOp`, matching
`[X, Y] = Y`, so they assemble into a representation `ρ : 𝔤 → End k M`. The resulting module is
irreducible of dimension `p > 1`, so Lie's theorem fails.

Because the counterexample module `k^{ℤ/p}` lives in the same universe as `k`, and the theorem
`lie_theorem_fails_charP` quantifies over `M : Type` (universe `0`), we specialize `k` to
`Type` here (the char-`0` results above keep `k : Type*`). -/

section CharP

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The prime-field embedding `ℤ/p ↪ k`, whose values `0, 1, …, p-1` are the `p` distinct
eigenvalues of the diagonal operator. -/
noncomputable def lam : ZMod p →+* k := ZMod.castHom (dvd_refl p) k

theorem lam_injective : Function.Injective (lam k p) := by
  show Function.Injective ⇑(ZMod.castHom (dvd_refl p) k)
  exact ZMod.castHom_injective k

/-- The diagonal operator on `k^{ℤ/p}`: `(diagOp v) i = (i : k) * v i`, with distinct
eigenvalues indexed by `ℤ/p`. This is the action of `X`. -/
noncomputable def diagOp : Module.End k (ZMod p → k) where
  toFun v i := lam k p i * v i
  map_add' u v := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The cyclic shift on `k^{ℤ/p}`: `(shiftOp v) i = v (i - 1)`. This is the action of `Y`. -/
noncomputable def shiftOp : Module.End k (ZMod p → k) :=
  LinearMap.funLeft k k (fun i => i - 1)

variable {k p}

@[simp] theorem diagOp_apply (v : ZMod p → k) (i : ZMod p) : diagOp k p v i = lam k p i * v i :=
  rfl

@[simp] theorem shiftOp_apply (v : ZMod p → k) (i : ZMod p) : shiftOp k p v i = v (i - 1) :=
  rfl

/-- The key relation `[diagOp, shiftOp] = shiftOp`, mirroring `[X, Y] = Y`. It holds because the
prime-field embedding is a ring homomorphism, so consecutive eigenvalues differ by `lam 1 = 1`. -/
theorem bracket_diag_shift : ⁅diagOp k p, shiftOp k p⁆ = shiftOp k p := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    diagOp_apply, shiftOp_apply]
  rw [← sub_mul, ← map_sub, sub_sub_cancel, map_one, one_mul]

variable (k p)

/-- Auxiliary Lie subalgebra of `2×2` matrices whose second row vanishes. It contains the
generators `e₁₁, e₁₂`, hence contains all of `g k`; this pins down the entries of elements of
`g k` used in the bracket computation for `ρ`. -/
def rowZero : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) where
  carrier := {A | A 1 0 = 0 ∧ A 1 1 = 0}
  add_mem' {a b} ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c a ha := ⟨by simp [ha.1], by simp [ha.2]⟩
  lie_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, ha.1, ha.2, hb.1, hb.2, zero_mul, mul_zero, add_zero, sub_zero, and_self]

/-- Every element of `g k` has vanishing second row. -/
theorem mem_g_row (A : g k) :
    (↑A : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧ (↑A : Matrix (Fin 2) (Fin 2) k) 1 1 = 0 := by
  have hg : g k = LieSubalgebra.lieSpan k (Matrix (Fin 2) (Fin 2) k)
      {Matrix.single 0 0 1, Matrix.single 0 1 1} := rfl
  have hle : g k ≤ rowZero k := by
    rw [hg, LieSubalgebra.lieSpan_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨by simp [Matrix.single_apply], by simp [Matrix.single_apply]⟩
    · exact ⟨by simp [Matrix.single_apply], by simp [Matrix.single_apply]⟩
  exact hle A.2

/-- The representation `ρ : 𝔤 → End k M` sending `X ↦ diagOp`, `Y ↦ shiftOp`, defined on a
matrix `A ∈ 𝔤` by `A ↦ A₀₀ • diagOp + A₀₁ • shiftOp`. -/
noncomputable def ρ : g k →ₗ⁅k⁆ Module.End k (ZMod p → k) where
  toFun A := (A : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
    + (A : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p
  map_add' A B := by
    simp only [AddMemClass.coe_add, Matrix.add_apply, add_smul]; abel
  map_smul' c A := by
    simp only [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]
  map_lie' := by
    intro A B
    -- The second row of any element of `g k` vanishes; use it to compute the two relevant
    -- entries of the matrix commutator `⁅A, B⁆`.
    obtain ⟨hA0, hA1⟩ := mem_g_row k A
    obtain ⟨hB0, hB1⟩ := mem_g_row k B
    have hds : ⁅shiftOp k p, diagOp k p⁆ = -shiftOp k p := by
      rw [← lie_skew, bracket_diag_shift]
    have hbr : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k)
        = (↑A : Matrix (Fin 2) (Fin 2) k) * (↑B : Matrix (Fin 2) (Fin 2) k)
          - (↑B : Matrix (Fin 2) (Fin 2) k) * (↑A : Matrix (Fin 2) (Fin 2) k) := by
      rw [LieSubalgebra.coe_bracket, Ring.lie_def]
    have e00 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA0, hB0, mul_zero,
        add_zero]
      ring
    have e01 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 =
        (↑A : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑B : Matrix (Fin 2) (Fin 2) k) 0 1
          - (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA1, hB1, mul_zero,
        add_zero]
    show (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
        + (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p
      = ⁅(↑A : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
          + (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p,
        (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
          + (↑B : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p⁆
    rw [e00, e01]
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, add_zero, zero_add,
      bracket_diag_shift, hds, smul_neg, zero_smul]
    module

/-- Coercion of the generator `X = e₁₁` to the underlying matrix. -/
theorem coe_X : (↑(X k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 0 1 := rfl

/-- Coercion of the generator `Y = e₁₂` to the underlying matrix. -/
theorem coe_Y : (↑(Y k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 1 1 := rfl

/-- Under `ρ`, the generator `X` acts as the diagonal operator. -/
@[simp] theorem ρ_X : ρ k p (X k) = diagOp k p := by
  have h0 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    simp [Matrix.single_apply]
  show (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
      + (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p = diagOp k p
  rw [coe_X, h0, h1, one_smul, zero_smul, add_zero]

/-- Under `ρ`, the generator `Y` acts as the cyclic shift. -/
@[simp] theorem ρ_Y : ρ k p (Y k) = shiftOp k p := by
  have h0 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 1 := by
    simp [Matrix.single_apply]
  show (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
      + (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p = shiftOp k p
  rw [coe_Y, h0, h1, zero_smul, one_smul, zero_add]

/-- The `𝔤`-module structure on `k^{ℤ/p}` induced by `ρ`. -/
noncomputable instance repModule : LieRingModule (g k) (ZMod p → k) :=
  LieRingModule.compLieHom _ (ρ k p)

/-- The induced module is a genuine Lie module. -/
noncomputable instance repLieModule : LieModule k (g k) (ZMod p → k) :=
  LieModule.compLieHom _ (ρ k p)

/-- In the induced module, `X` acts as the diagonal operator. -/
theorem lie_X_eq_diag (v : ZMod p → k) : (⁅X k, v⁆ : ZMod p → k) = diagOp k p v := by
  have h : (⁅X k, v⁆ : ZMod p → k) = ρ k p (X k) v := rfl
  rw [h, ρ_X]

/-- In the induced module, `Y` acts as the cyclic shift. -/
theorem lie_Y_eq_shift (v : ZMod p → k) : (⁅Y k, v⁆ : ZMod p → k) = shiftOp k p v := by
  have h : (⁅Y k, v⁆ : ZMod p → k) = ρ k p (Y k) v := rfl
  rw [h, ρ_Y]

/-- The cyclic shift permutes the standard basis: `shiftOp (eⱼ) = eⱼ₊₁`. -/
theorem shift_single (j : ZMod p) (c : k) :
    shiftOp k p (Pi.single j c) = Pi.single (j + 1) c := by
  funext m
  rw [shiftOp_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  simp [sub_eq_iff_eq_add]

variable {k p}

open scoped Classical in
/-- The support (as a `Finset`) of a vector in `k^{ℤ/p}`. -/
noncomputable def vsupp (v : ZMod p → k) : Finset (ZMod p) :=
  Finset.univ.filter fun i => v i ≠ 0

theorem mem_vsupp {v : ZMod p → k} {i : ZMod p} : i ∈ vsupp v ↔ v i ≠ 0 := by
  simp [vsupp]

variable (k p)

/-- **The counterexample module is irreducible.** A nonzero `𝔤`-submodule `N` of `k^{ℤ/p}` is all
of `k^{ℤ/p}`: pick a nonzero `v ∈ N` of minimal support; the diagonal action forces the support
to be a single point (else `diagOp v - λⱼ v ∈ N` has strictly smaller support), so a standard
basis vector lies in `N`, and the shift action (a `p`-cycle) sweeps out all of them. -/
theorem repModule_irreducible : LieModule.IsIrreducible k (g k) (ZMod p → k) := by
  classical
  haveI : Nontrivial (ZMod p → k) := inferInstance
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  -- `N` is closed under the diagonal and shift operators.
  have hdiag : ∀ v, v ∈ N → diagOp k p v ∈ N := fun v hv => by
    rw [← lie_X_eq_diag]; exact N.lie_mem hv
  have hshift : ∀ v, v ∈ N → shiftOp k p v ∈ N := fun v hv => by
    rw [← lie_Y_eq_shift]; exact N.lie_mem hv
  -- From one standard basis vector, the shift `p`-cycle produces all of them.
  have horbit : ∀ i₀ : ZMod p, Pi.single i₀ (1 : k) ∈ N → ∀ m, Pi.single m (1 : k) ∈ N := by
    intro i₀ hbase m
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = i₀ + t :=
      ⟨(m - i₀).val, by rw [ZMod.natCast_zmod_val]; abel⟩
    induction t with
    | zero => simpa using hbase
    | succ n ih =>
      have h2 := hshift _ ih
      rw [shift_single] at h2
      rw [Nat.cast_succ, ← add_assoc]
      exact h2
  -- All standard basis vectors in `N` forces `N = ⊤`.
  have htop : (∀ m : ZMod p, Pi.single m (1 : k) ∈ N) → N = ⊤ := by
    intro hall
    rw [← LieSubmodule.toSubmodule_eq_top, Submodule.eq_top_iff']
    intro x
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun m _ => ?_
    have hsingle : Pi.single m (x m) = x m • Pi.single m (1 : k) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [hsingle]
    exact Submodule.smul_mem _ _ (hall m)
  -- Extract a nonzero element of `N`.
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push_neg at hN
  obtain ⟨w, hwN, hw0⟩ := hN
  -- Strong induction on the size of the support.
  suffices H : ∀ (n : ℕ) (v : ZMod p → k), v ∈ N → v ≠ 0 → (vsupp v).card = n → N = ⊤ from
    H _ w hwN hw0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro v hvN hv0 hcard
    have hne : (vsupp v).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
      exact ⟨i, mem_vsupp.mpr hi⟩
    by_cases hone : (vsupp v).card = 1
    · -- Support is a single point: a basis vector lies in `N`, so `N = ⊤`.
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hone
      have hvi₀ : v i₀ ≠ 0 := mem_vsupp.mp (hi₀ ▸ Finset.mem_singleton_self i₀)
      have hzero : ∀ m, m ≠ i₀ → v m = 0 := by
        intro m hm
        by_contra hvm
        have : m ∈ vsupp v := mem_vsupp.mpr hvm
        rw [hi₀, Finset.mem_singleton] at this
        exact hm this
      have hbase : Pi.single i₀ (1 : k) ∈ N := by
        have hsm : (v i₀)⁻¹ • v ∈ N := N.smul_mem _ hvN
        have hval : (v i₀)⁻¹ • v = Pi.single i₀ (1 : k) := by
          funext m
          rw [Pi.smul_apply, smul_eq_mul]
          by_cases hm : m = i₀
          · subst hm; rw [Pi.single_eq_same, inv_mul_cancel₀ hvi₀]
          · rw [Pi.single_eq_of_ne hm, hzero m hm, mul_zero]
        rwa [hval] at hsm
      exact htop (horbit i₀ hbase)
    · -- Support has at least two points: subtract an eigenvalue to shrink it, then recurse.
      have h2 : 1 < (vsupp v).card := by
        have h1 := Finset.card_pos.mpr hne; omega
      obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp h2
      set w' := diagOp k p v - lam k p j • v with hw'def
      have hw'N : w' ∈ N := sub_mem (hdiag v hvN) (N.smul_mem _ hvN)
      have hw'coord : ∀ m, w' m = (lam k p m - lam k p j) * v m := fun m => by
        simp only [hw'def, Pi.sub_apply, diagOp_apply, Pi.smul_apply, smul_eq_mul]; ring
      have hlamij : lam k p i ≠ lam k p j := fun heq => hij (lam_injective k p heq)
      have hw'i : w' i ≠ 0 := by
        rw [hw'coord]
        exact mul_ne_zero (sub_ne_zero.mpr hlamij) (mem_vsupp.mp hi)
      have hw'0 : w' ≠ 0 := fun heq => hw'i (congrFun heq i)
      have hsub : vsupp w' ⊆ vsupp v := by
        intro m hm
        rw [mem_vsupp] at hm ⊢
        intro hvm
        exact hm (by rw [hw'coord, hvm, mul_zero])
      have hjnotin : j ∉ vsupp w' := by
        rw [mem_vsupp, not_not, hw'coord, sub_self, zero_mul]
      have hss : vsupp w' ⊂ vsupp v :=
        (Finset.ssubset_iff_of_subset hsub).mpr ⟨j, hj, hjnotin⟩
      have hlt : (vsupp w').card < n := hcard ▸ Finset.card_lt_card hss
      exact IH _ hlt w' hw'N hw'0 rfl

/-- **Characteristic `p`.** Lie's theorem fails: it is **not** the case that every irreducible
finite-dimensional representation of `𝔤` is `1`-dimensional. The `p`-dimensional module `k^{ℤ/p}`
built above is an explicit irreducible counterexample.

The statement quantifies over `M : Type` (universe `0`), and the witness `k^{ℤ/p}` lives in `k`'s
universe, so `k` is specialized to `Type` for this result. -/
theorem lie_theorem_fails_charP (k : Type) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
        [LieModule k (g k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M],
        Module.finrank k M = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI := repModule_irreducible k p
  intro h
  have hfr : Module.finrank k (ZMod p → k) = 1 := h (ZMod p → k)
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card p] at hfr
  exact ((Fact.out : p.Prime).one_lt).ne' hfr

end CharP

end Etingof.Problem2_16_2
