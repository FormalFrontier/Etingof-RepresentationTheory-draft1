import Mathlib

/-!
# Problem 4.12.6: representations of the affine group `x ↦ ax + b` over `𝔽_q`

**Problem 4.12.6.** Let `𝔽_q` be a finite field with `q` elements, and let `G` be the group of
nonconstant inhomogeneous linear transformations, `x ↦ ax + b`, over `𝔽_q` (i.e.,
`a ∈ 𝔽_q^×`, `b ∈ 𝔽_q`). Find all irreducible complex representations of `G`, and compute
their characters. Compute the tensor products of irreducible representations.

Hint: Let `V` be the representation of `G` on the space of functions on `𝔽_q` with sum of all
values equal to zero. Show that `V` is an irreducible representation of `G`.

## Formalization

We model `𝔽_q` by an arbitrary finite field `K` (`q = Fintype.card K`) and `G` by the pairs
`⟨a, b⟩` with `a : Kˣ`, `b : K`, encoding the transformation `x ↦ a·x + b`. Composition gives
the multiplication `⟨a,b⟩ * ⟨a',b'⟩ = ⟨a·a', a·b' + b⟩`, so `G = K ⋊ Kˣ` has order `q(q-1)`.

The classification (recorded here; `sorry` proofs — a statement pass):

* `one_dim_reps_card`: the one-dimensional representations are the group homomorphisms
  `G → ℂˣ`, pulled back from the abelianization `G^{ab} ≅ Kˣ`; there are exactly `q-1` of them.
* `zeroSum` is the subspace of functions `K → ℂ` whose values sum to `0`; `zeroSum_invariant`
  and `zeroSum_finrank` show it is a `G`-invariant subspace of dimension `q-1`, and
  `zeroSum_irreducible` shows the corresponding representation `V` is irreducible.
* `irreducible_dim`: every irreducible complex representation of `G` has dimension `1` or
  `q-1`. Together with the sum-of-squares formula `(q-1)·1² + 1·(q-1)² = q(q-1) = |G|`, the
  irreducibles are exactly the `q-1` characters and the single `(q-1)`-dimensional
  representation `V`.

`G` acts on `𝔽_q` by the affine transformation, and hence on functions `K → ℂ` by
`(ρ g f)(x) = f(g⁻¹ · x)`; the irreducibility statements are phrased for any such `ρ`.
-/

noncomputable section

namespace Etingof.Problem4_12_6

variable {K : Type*} [Field K]

/-- The affine group of transformations `x ↦ a·x + b` over `K`, encoded by the pair `⟨a, b⟩`
with `a : Kˣ` and `b : K`. -/
@[ext]
structure Affine (K : Type*) [Field K] where
  a : Kˣ
  b : K

namespace Affine

instance : Mul (Affine K) :=
  ⟨fun g h => ⟨g.a * h.a, (g.a : K) * h.b + g.b⟩⟩

instance : One (Affine K) := ⟨⟨1, 0⟩⟩

instance : Inv (Affine K) :=
  ⟨fun g => ⟨g.a⁻¹, -((g.a⁻¹ : K) * g.b)⟩⟩

@[simp] theorem mul_a (g h : Affine K) : (g * h).a = g.a * h.a := rfl
@[simp] theorem mul_b (g h : Affine K) : (g * h).b = (g.a : K) * h.b + g.b := rfl
@[simp] theorem one_a : (1 : Affine K).a = 1 := rfl
@[simp] theorem one_b : (1 : Affine K).b = 0 := rfl
@[simp] theorem inv_a (g : Affine K) : g⁻¹.a = g.a⁻¹ := rfl
@[simp] theorem inv_b (g : Affine K) : g⁻¹.b = -((g.a⁻¹ : K) * g.b) := rfl

instance : Group (Affine K) where
  mul_assoc g h k := by
    ext
    · simp [mul_assoc]
    · simp; ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext
    · simp
    · simp

/-- The affine action of `G` on `K`: `⟨a,b⟩ · x = a·x + b`. -/
def act (g : Affine K) (x : K) : K := (g.a : K) * x + g.b

/-- The bijection `Affine K ≃ Kˣ × K` used to transport finiteness. -/
def equivProd (K : Type*) [Field K] : Affine K ≃ Kˣ × K where
  toFun g := (g.a, g.b)
  invFun t := ⟨t.1, t.2⟩
  left_inv g := by cases g; rfl
  right_inv t := by rfl

instance [DecidableEq K] : DecidableEq (Affine K) := (equivProd K).decidableEq

instance [Fintype K] [DecidableEq K] : Fintype (Affine K) := Fintype.ofEquiv _ (equivProd K).symm

/-- The affine group has order `q(q-1)`. -/
theorem card_eq [Fintype K] [DecidableEq K] :
    Fintype.card (Affine K) = Fintype.card K * (Fintype.card K - 1) := by
  sorry

end Affine

open Affine

/-- **One-dimensional representations.** They are the group homomorphisms `G → ℂˣ`
(pulled back from `G^{ab} ≅ Kˣ`), and there are exactly `q - 1` of them. -/
theorem one_dim_reps_card [Fintype K] :
    Nat.card (Affine K →* ℂˣ) = Fintype.card K - 1 := by
  sorry

/-- The subspace `V` of functions `K → ℂ` whose values sum to zero. -/
def zeroSum (K : Type*) [Fintype K] : Submodule ℂ (K → ℂ) where
  carrier := {f | ∑ x, f x = 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [← Finset.mul_sum, hf, mul_zero]

/-- `V = zeroSum K` is a `G`-invariant subspace of the permutation representation on `K → ℂ`
(where `(ρ g f)(x) = f(g⁻¹ · x)`). -/
theorem zeroSum_invariant [Fintype K]
    (ρ : Representation ℂ (Affine K) (K → ℂ))
    (hρ : ∀ (g : Affine K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x)) :
    ∀ (g : Affine K), ∀ f ∈ zeroSum K, ρ g f ∈ zeroSum K := by
  sorry

/-- The zero-sum representation `V` has dimension `q - 1`. -/
theorem zeroSum_finrank [Fintype K] :
    Module.finrank ℂ (zeroSum K) = Fintype.card K - 1 := by
  sorry

/-- **The hint.** The representation `V` of `G` on the zero-sum functions is irreducible:
every `G`-invariant subspace contained in `zeroSum K` is `⊥` or all of `zeroSum K`. -/
theorem zeroSum_irreducible [Fintype K]
    (ρ : Representation ℂ (Affine K) (K → ℂ))
    (hρ : ∀ (g : Affine K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (U : Submodule ℂ (K → ℂ)) (hUle : U ≤ zeroSum K)
    (hUinv : ∀ (g : Affine K), ∀ f ∈ U, ρ g f ∈ U) :
    U = ⊥ ∨ U = zeroSum K := by
  sorry

/-- **Classification.** Every irreducible complex representation of the affine group `G` has
dimension `1` or `q - 1`. (With the sum-of-squares formula `(q-1)·1² + (q-1)² = q(q-1) = |G|`,
the irreducibles are exactly the `q-1` characters and the single `(q-1)`-dimensional `V`.) -/
theorem irreducible_dim [Fintype K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Affine K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (Affine K)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = Fintype.card K - 1 := by
  sorry

end Etingof.Problem4_12_6
