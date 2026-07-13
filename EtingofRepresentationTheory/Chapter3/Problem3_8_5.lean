import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Problem 3.8.5: periodic and antiperiodic functions

Let `A` be the algebra of real-valued continuous functions on `ℝ` that are periodic with
period `1`, and let `M` be the `A`-module of continuous functions `f` that are
**antiperiodic**: `f(x + 1) = −f(x)`.

* **(i)** `A` and `M` are indecomposable `A`-modules.
* **(ii)** `A` is not isomorphic to `M`, but `A ⊕ A ≅ M ⊕ M`.

We model `A` as the subalgebra `periodicSubalg` of `C(ℝ, ℝ)` cut out by `f(x+1) = f(x)`,
and `M` as the `A`-submodule `antiperiodicSubmod` of `C(ℝ, ℝ)` cut out by `f(x+1) = −f(x)`.
(`M` is closed under multiplication by a periodic function: if `g(x+1) = g(x)` and
`f(x+1) = −f(x)` then `(gf)(x+1) = −(gf)(x)`.) The regular module `A` and the module `M` are
then genuine `↥periodicSubalg`-modules.

`A ⊕ A ≅ M ⊕ M` reflects that `M ⊗_A M ≅ A` (antiperiodic × antiperiodic = periodic), so `M`
is an invertible module of order `2` in the Picard group of `A`; it is a nontrivial line
bundle on the circle (the Möbius bundle), whence `M ≇ A` yet `M ⊕ M ≅ A ⊕ A`.

The subalgebra and submodule carriers are genuine and their closure proof obligations are
discharged; the four theorems are left as `sorry`.
-/

namespace Etingof.Problem3_8_5

open scoped ContinuousMap

/-- The algebra `A` of continuous period-1 functions `ℝ → ℝ`, as a subalgebra of `C(ℝ, ℝ)`.
The carrier is the genuine set of periodic functions; closure under multiplication, addition,
and the algebra map follows from the defining identity `f (x + 1) = f x`. -/
noncomputable def periodicSubalg : Subalgebra ℝ C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = f x}
  mul_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.mul_apply, hf x, hg x]
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
  algebraMap_mem' := by
    intro r x
    simp

/-- The `A`-module `M` of continuous antiperiodic functions `f(x+1) = −f(x)`, as a submodule
of `C(ℝ, ℝ)` over the algebra `A = periodicSubalg`. The carrier is genuine; closure under
addition and multiplication by a periodic scalar follows from `f (x + 1) = - f x`. -/
noncomputable def antiperiodicSubmod : Submodule (periodicSubalg) C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = - f x}
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
    ring
  zero_mem' := by
    intro x
    simp
  smul_mem' := by
    intro c f hf x
    have key : ∀ y : ℝ, (c • f) y = (c : C(ℝ, ℝ)) y * f y := by
      intro y
      rw [Algebra.smul_def]
      rfl
    rw [key (x + 1), key x, hf x, c.2 x]
    ring

/-- The value of a periodic function at a point, as a plain real number. -/
private lemma periodicSubalg_coe_mul (e : periodicSubalg) (x : ℝ) :
    ((e * e : periodicSubalg) : C(ℝ, ℝ)) x = ((e : C(ℝ, ℝ)) x) * ((e : C(ℝ, ℝ)) x) := by
  simp

/-- **Idempotents in `A` are trivial.** An idempotent element `e` of the algebra of
continuous period-1 functions is either `0` or `1`: pointwise `e(x)² = e(x)` forces
`e(x) ∈ {0, 1}`, and since `e` is continuous and `ℝ` is connected, `e` is constant. -/
lemma periodicSubalg_idempotent_eq_zero_or_one (e : periodicSubalg) (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  -- The underlying continuous function.
  set f : C(ℝ, ℝ) := (e : C(ℝ, ℝ)) with hf
  -- Pointwise idempotence: `f x * f x = f x`.
  have hpt : ∀ x, f x * f x = f x := by
    intro x
    have := congrArg (fun z : periodicSubalg => (z : C(ℝ, ℝ)) x) he
    simpa using this
  -- Every value is `0` or `1`.
  have hdich : ∀ x, f x = 0 ∨ f x = 1 := by
    intro x
    have h := hpt x
    have : f x * (f x - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith [sub_eq_zero.mp h1])
  -- The set where `f = 1` is clopen.
  set s : Set ℝ := {x | f x = 1} with hs
  have hclosed : IsClosed s := by
    have : s = f ⁻¹' {1} := rfl
    rw [this]
    exact IsClosed.preimage (map_continuous f) isClosed_singleton
  have hcompl_closed : IsClosed sᶜ := by
    have : sᶜ = f ⁻¹' {0} := by
      ext x
      simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro hx; rcases hdich x with h0 | h1
        · exact h0
        · exact absurd h1 hx
      · intro hx; rw [hx]; norm_num
    rw [this]
    exact IsClosed.preimage (map_continuous f) isClosed_singleton
  have hclopen : IsClopen s := ⟨hclosed, isClosed_compl_iff.mp hcompl_closed⟩
  -- In the connected space `ℝ`, `s` is `∅` or `univ`.
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · -- `s = ∅`: `f` is identically `0`, so `e = 0`.
    left
    have hzero : ∀ x, f x = 0 := by
      intro x
      rcases hdich x with h0 | h1
      · exact h0
      · have hmem : x ∈ s := h1
        rw [hempty] at hmem
        simp at hmem
    have : f = 0 := by ext x; simp [hzero x]
    have : (e : C(ℝ, ℝ)) = ((0 : periodicSubalg) : C(ℝ, ℝ)) := by simpa [hf] using this
    exact Subtype.ext this
  · -- `s = univ`: `f` is identically `1`, so `e = 1`.
    right
    have hone : ∀ x, f x = 1 := by
      intro x
      have : x ∈ s := by rw [huniv]; exact Set.mem_univ x
      exact this
    have : f = 1 := by ext x; simp [hone x]
    have : (e : C(ℝ, ℝ)) = ((1 : periodicSubalg) : C(ℝ, ℝ)) := by simpa [hf] using this
    exact Subtype.ext this

/-- **Problem 3.8.5(i).** `A` is indecomposable as an `A`-module: the function algebra of the
circle has no nontrivial idempotents. -/
theorem periodic_isIndecomposable :
    Etingof.IsIndecomposable (periodicSubalg) (periodicSubalg) := by
  refine ⟨inferInstance, ?_⟩
  intro W₁ W₂ hC
  -- `1 = e₁ + e₂` with `e₁ ∈ W₁`, `e₂ ∈ W₂`, from codisjointness.
  have h1 : (1 : periodicSubalg) ∈ W₁ ⊔ W₂ := by rw [hC.sup_eq_top]; trivial
  rw [Submodule.mem_sup] at h1
  obtain ⟨e₁, he₁, e₂, he₂, hsum⟩ := h1
  -- `e₁ * e₂ ∈ W₁ ⊓ W₂ = ⊥`, so `e₁ * e₂ = 0`.
  have hmem12 : e₁ * e₂ ∈ W₁ ⊓ W₂ := by
    refine ⟨?_, ?_⟩
    · rw [mul_comm]
      have := W₁.smul_mem e₂ he₁
      rwa [smul_eq_mul] at this
    · have := W₂.smul_mem e₁ he₂
      rwa [smul_eq_mul] at this
  rw [hC.inf_eq_bot, Submodule.mem_bot] at hmem12
  -- Hence `e₁` is idempotent.
  have hidem : e₁ * e₁ = e₁ := by
    have h : e₁ * (e₁ + e₂) = e₁ * 1 := by rw [hsum]
    rw [mul_add, hmem12, add_zero, mul_one] at h
    exact h
  rcases periodicSubalg_idempotent_eq_zero_or_one e₁ hidem with rfl | rfl
  · -- `e₁ = 0` ⇒ `e₂ = 1` ⇒ `W₂ = ⊤` ⇒ `W₁ = ⊥`.
    left
    have he2 : e₂ = 1 := by rw [zero_add] at hsum; exact hsum
    rw [he2] at he₂
    have hW2 : W₂ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have := W₂.smul_mem a he₂
      rwa [smul_eq_mul, mul_one] at this
    have := hC.inf_eq_bot
    rwa [hW2, inf_top_eq] at this
  · -- `e₁ = 1` ⇒ `W₁ = ⊤` ⇒ `W₂ = ⊥`.
    right
    have hW1 : W₁ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have := W₁.smul_mem a he₁
      rwa [smul_eq_mul, mul_one] at this
    have := hC.inf_eq_bot
    rwa [hW1, top_inf_eq] at this

/-- **Problem 3.8.5(i).** `M` is indecomposable as an `A`-module. -/
theorem antiperiodic_isIndecomposable :
    Etingof.IsIndecomposable (periodicSubalg) (antiperiodicSubmod) := by
  sorry

/-- **Problem 3.8.5(ii), first part.** `A` is not isomorphic to `M` as `A`-modules: `M` is a
nontrivial line bundle on the circle (the Möbius bundle), so it is not free of rank 1. -/
theorem periodic_not_linearEquiv_antiperiodic :
    IsEmpty (periodicSubalg ≃ₗ[periodicSubalg] antiperiodicSubmod) := by
  sorry

/-- **Problem 3.8.5(ii), second part.** `A ⊕ A ≅ M ⊕ M` as `A`-modules. -/
theorem periodic_sq_linearEquiv_antiperiodic_sq :
    Nonempty ((periodicSubalg × periodicSubalg) ≃ₗ[periodicSubalg]
      (antiperiodicSubmod × antiperiodicSubmod)) := by
  sorry

end Etingof.Problem3_8_5
