import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import EtingofRepresentationTheory.Chapter3.Theorem3_3_1

/-!
# Problem 3.3.3: An alternative proof of Theorem 3.3.1

The problem gives an alternative route to Theorem 3.3.1 through the structure of a direct
sum of algebras.

Let `A = A₁ ⊕ ⋯ ⊕ Aₙ` (modeled as the finite product algebra `∀ i, 𝒜 i`), with unit
idempotents `1ᵢ = Pi.single i 1`.

* **(a)** A representation `V` of `A` is irreducible iff `1ᵢ V` is an irreducible
  representation of `Aᵢ` for exactly one `i`, while `1ⱼ V = 0` for all other `j`. Here
  `1ᵢ V` is the `A`-submodule `LinearMap.range (idemProj i)`, the image of the (central,
  hence `A`-linear) projection `v ↦ 1ᵢ • v`. Since the factors `Aⱼ` with `j ≠ i` act as
  `0` on `1ᵢ V`, the `A`-submodules of `1ᵢ V` are exactly its `Aᵢ`-submodules, so
  "irreducible representation of `Aᵢ`" is faithfully rendered as
  `IsSimpleModule A (1ᵢ V)`.

* **(b)** The only irreducible representation of `Matₙ(k) = Mat_d(k)` is `k^d`, and every
  finite dimensional representation of `Mat_d(k)` is a direct sum of copies of `k^d`
  (i.e. isomorphic to `(k^d)^n = Fin n → (Fin d → k)` for some `n`).

* **(c)** Theorem 3.3.1 follows; the full statement is already recorded as
  `Etingof.irreducible_reps_of_matrix_algebra` in `Theorem3_3_1`.

Statement pass: all proofs are left as `sorry`.
-/

namespace Etingof.Problem3_3_3

/-! ## Part (a): irreducibles of a direct sum of algebras

Part (a) is pure ring/module theory: it needs no base field, only the product ring
`A = ∀ i, 𝒜 i` and an `A`-module `V`. -/

section PartA

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]
  (V : Type*) [AddCommGroup V] [Module (∀ i, 𝒜 i) V]

/-- The unit idempotent `1ᵢ = Pi.single i 1` of the product algebra is central. -/
theorem single_one_central (i : Fin r) (a : ∀ i, 𝒜 i) :
    (Pi.single i 1 : ∀ i, 𝒜 i) * a = a * Pi.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

/-- The `A`-linear projection `v ↦ 1ᵢ • v`. It is `A`-linear because `1ᵢ` is central. Its
range is the subrepresentation `1ᵢ V`. -/
def idemProj (i : Fin r) : V →ₗ[∀ i, 𝒜 i] V where
  toFun v := (Pi.single i 1 : ∀ i, 𝒜 i) • v
  map_add' v w := smul_add _ _ _
  map_smul' a v := by
    simp only [RingHom.id_apply, smul_smul]
    rw [single_one_central 𝒜 i a]

/-- The unit idempotents are orthogonal: `1ᵢ · 1ⱼ = δᵢⱼ 1ᵢ`. -/
theorem single_mul_single_eq (i j : Fin r) :
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

/-- The unit idempotents sum to `1`. -/
theorem sum_single_one : (∑ i, (Pi.single i 1 : ∀ i, 𝒜 i)) = 1 := by
  simpa using Finset.univ_sum_single (1 : ∀ i, 𝒜 i)

/-- Applying two idempotent projections in succession: `1ᵢ · (1ⱼ · v) = δᵢⱼ (1ᵢ · v)`. -/
theorem single_smul_single_smul (i j : Fin r) (v : V) :
    (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single j 1 : ∀ i, 𝒜 i) • v)
      = if i = j then (Pi.single i 1 : ∀ i, 𝒜 i) • v else 0 := by
  rw [← mul_smul, single_mul_single_eq]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_smul]

/-- The projections `1ᵢ · (-)` sum to the identity: `∑ᵢ 1ᵢ · v = v`. -/
theorem sum_single_smul (v : V) : (∑ i, (Pi.single i 1 : ∀ i, 𝒜 i) • v) = v := by
  rw [← Finset.sum_smul, sum_single_one, one_smul]

/-- Membership in the range of `1ᵢ · (-)` is exactly idempotence: `v ∈ 1ᵢ V ↔ 1ᵢ · v = v`. -/
theorem mem_range_idemProj (i : Fin r) (v : V) :
    v ∈ LinearMap.range (idemProj 𝒜 V i) ↔ (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single i 1 : ∀ i, 𝒜 i) • w)
        = (Pi.single i 1 : ∀ i, 𝒜 i) • w
    rw [single_smul_single_smul, if_pos rfl]
  · intro h
    exact ⟨v, h⟩

/-- The summand `1ᵢ V` is everything iff `1ᵢ` acts as the identity. -/
theorem range_eq_top_iff (i : Fin r) :
    LinearMap.range (idemProj 𝒜 V i) = ⊤ ↔ ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
  rw [Submodule.eq_top_iff']
  exact ⟨fun h v => (mem_range_idemProj 𝒜 V i v).1 (h v),
         fun h v => (mem_range_idemProj 𝒜 V i v).2 (h v)⟩

/-- The summand `1ᵢ V` vanishes iff `1ᵢ` acts as zero. -/
theorem range_eq_bot_iff (i : Fin r) :
    LinearMap.range (idemProj 𝒜 V i) = ⊥ ↔ ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = 0 := by
  rw [LinearMap.range_eq_bot, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply]
  rfl

/-- **Problem 3.3.3(a).** A representation `V` of `A = ⊕ᵢ Aᵢ` is irreducible if and only if
`1ᵢ V` is an irreducible representation of `Aᵢ` for exactly one `i`, while `1ⱼ V = 0` for
all other `j`. -/
theorem simpleModule_prod_iff :
    IsSimpleModule (∀ i, 𝒜 i) V ↔
      ∃ i, IsSimpleModule (∀ i, 𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) ∧
        ∀ j, j ≠ i → LinearMap.range (idemProj 𝒜 V j) = ⊥ := by
  constructor
  · -- (⇒) `V` simple. Each summand `1ₖ V` is `⊥` or `⊤`; not all are `⊥` (they sum to `V`),
    -- and at most one is `⊤` (orthogonality). The unique `⊤` summand is the required `i`.
    intro hV
    haveI := hV
    haveI : Nontrivial V := IsSimpleModule.nontrivial (∀ i, 𝒜 i) V
    have hclass : ∀ k, LinearMap.range (idemProj 𝒜 V k) = ⊥ ∨
        LinearMap.range (idemProj 𝒜 V k) = ⊤ := fun k => eq_bot_or_eq_top _
    have hexists : ∃ i, LinearMap.range (idemProj 𝒜 V i) = ⊤ := by
      by_contra h
      simp only [not_exists] at h
      have hbot : ∀ k, LinearMap.range (idemProj 𝒜 V k) = ⊥ :=
        fun k => (hclass k).resolve_right (h k)
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine hv ?_
      rw [← sum_single_smul 𝒜 V v]
      exact Finset.sum_eq_zero fun k _ => (range_eq_bot_iff 𝒜 V k).1 (hbot k) v
    obtain ⟨i, hi_top⟩ := hexists
    have hi_id : ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := (range_eq_top_iff 𝒜 V i).1 hi_top
    refine ⟨i, ?_, fun j hj => ?_⟩
    · rw [hi_top]
      exact (LinearEquiv.isSimpleModule_iff Submodule.topEquiv).2 hV
    · rcases hclass j with hb | ht
      · exact hb
      · exfalso
        have hj_id : ∀ v : V, (Pi.single j 1 : ∀ i, 𝒜 i) • v = v := (range_eq_top_iff 𝒜 V j).1 ht
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine hv ?_
        have h1 : (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single j 1 : ∀ i, 𝒜 i) • v) = 0 := by
          rw [single_smul_single_smul, if_neg (fun h : i = j => hj h.symm)]
        rw [hj_id v, hi_id v] at h1
        exact h1
  · -- (⇐) exactly one `i` with `1ᵢ V` simple and all other `1ⱼ V = ⊥`. Then `1ᵢ` acts as the
    -- identity, so `V ≅ 1ᵢ V` is simple.
    rintro ⟨i, hi_simple, hj_bot⟩
    have hzero : ∀ j, j ≠ i → ∀ v : V, (Pi.single j 1 : ∀ i, 𝒜 i) • v = 0 :=
      fun j hj => (range_eq_bot_iff 𝒜 V j).1 (hj_bot j hj)
    have hi_id : ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
      intro v
      have key : (∑ k, (Pi.single k 1 : ∀ i, 𝒜 i) • v) = (Pi.single i 1 : ∀ i, 𝒜 i) • v :=
        Finset.sum_eq_single i (fun k _ hk => hzero k hk v) (fun h => absurd (Finset.mem_univ i) h)
      rw [sum_single_smul] at key
      exact key.symm
    have hi_top : LinearMap.range (idemProj 𝒜 V i) = ⊤ := (range_eq_top_iff 𝒜 V i).2 hi_id
    rw [hi_top] at hi_simple
    exact (LinearEquiv.isSimpleModule_iff Submodule.topEquiv).1 hi_simple

end PartA

/-! ## Part (b): representations of a single matrix algebra `Mat_d(k)` -/

open scoped Matrix.Module

section PartB

variable (k : Type*) [Field k] (d : ℕ) [NeZero d]

/-- **Problem 3.3.3(b), existence.** The standard representation `k^d` is an irreducible
representation of `Mat_d(k)`. -/
theorem std_isSimpleModule :
    IsSimpleModule (Matrix (Fin d) (Fin d) k) (Fin d → k) := by
  sorry

/-- **Problem 3.3.3(b), uniqueness.** Every finite dimensional irreducible representation of
`Mat_d(k)` is isomorphic to the standard representation `k^d`. -/
theorem simpleModule_iso_std (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  sorry

/-- **Problem 3.3.3(b), decomposition.** Every finite dimensional representation of
`Mat_d(k)` is a direct sum of copies of the standard representation `k^d`: it is isomorphic
to `(k^d)^n = Fin n → (Fin d → k)` for some `n`. -/
theorem finite_iso_std_pow (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] :
    ∃ n : ℕ, Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin n → (Fin d → k))) := by
  sorry

end PartB

/-! ## Part (c): deducing Theorem 3.3.1

Part (c) asks to deduce Theorem 3.3.1 from (a) and (b). The full statement — for
`A = ⊕ᵢ Mat_{dᵢ}(k)`, the irreducibles are the `k^{dᵢ}` and every finite dimensional
representation is a direct sum of copies of them — is recorded (and proved) as
`Etingof.irreducible_reps_of_matrix_algebra` in `Theorem3_3_1`. -/

end Etingof.Problem3_3_3
