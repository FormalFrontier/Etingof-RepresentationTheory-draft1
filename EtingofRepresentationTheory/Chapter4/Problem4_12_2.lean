import Mathlib

/-!
# Problem 4.12.2: representations of the Heisenberg group over `𝔽_p`

**Problem 4.12.2.** Let `p` be a prime. Let `G` be the group of `3 × 3` matrices over `𝔽_p`
which are upper triangular and have `1`'s on the diagonal, under multiplication (its order is
`p³`). It is called the **Heisenberg group**. For any complex number `z` such that `z^p = 1`,
we define a representation of `G` on the space `V` of complex functions on `𝔽_p` by
`(ρ x f)(t) = f(t - 1)` for the generator `x = ⟨1,0,0⟩` and `(ρ y f)(t) = z^t · f(t)` for the
generator `y = ⟨0,1,0⟩`.

(a) Show that such a representation exists and is unique, and compute `ρ(g)` for all `g ∈ G`.

(b) Denote this representation by `R_z`. Show that `R_z` is irreducible if and only if `z ≠ 1`.

(c) Classify all `1`-dimensional representations of `G`. Show that `R_1` decomposes into a
direct sum of `1`-dimensional representations, where each of them occurs exactly once.

(d) Use (a)–(c) and the "sum of squares" formula to classify all irreducible representations
of `G`.

## Formalization

We model the Heisenberg group by the triples `⟨a, b, c⟩ : ZMod p` encoding the unitriangular
matrix `[[1,a,c],[0,1,b],[0,0,1]]`; matrix multiplication is
`⟨a,b,c⟩ * ⟨a',b',c'⟩ = ⟨a+a', b+b', c+c'+a·b'⟩`, giving a group of order `p³`. The two
generators are `xGen = ⟨1,0,0⟩` and `yGen = ⟨0,1,0⟩`, and `V = ZMod p → ℂ`.

Statements (faithful signatures, `sorry` proofs — a statement pass):

* **(a)** `exists_unique_rep`: for `z^p = 1` there is a *unique* representation `ρ` of `G` on
  `V` acting on the two generators by the shift and the multiplication operators. (Uniqueness
  holds because `xGen, yGen` generate `G`; this also determines `ρ(g)` for every `g`.)
* **(b)** `irreducible_iff`: any such `R_z` is irreducible iff `z ≠ 1`.
* **(c)** `one_dim_reps_card`: there are exactly `p²` one-dimensional representations (group
  homomorphisms `G → ℂˣ`, since `G^{ab} ≅ (ZMod p)²`); `R1_decomposes`: `R_1` is an internal
  direct sum of `p` one-dimensional `G`-invariant subspaces (each of the `p` distinct
  characters of the cyclic quotient occurs exactly once).
* **(d)** `irreducible_dim`: every irreducible complex representation of `G` has dimension `1`
  or `p`. Together with (c) and the sum-of-squares formula
  `p²·1² + (p-1)·p² = p³ = |G|`, the irreducibles are the `p²` characters and the `p-1`
  representations `R_z` (`z ≠ 1`) of dimension `p`.
-/

noncomputable section

namespace Etingof.Problem4_12_2

/-- The Heisenberg group over `𝔽_p`: the unitriangular matrix `[[1,a,c],[0,1,b],[0,0,1]]` is
encoded by its three free entries `(a, b, c)`. -/
@[ext]
structure Heisenberg (p : ℕ) where
  a : ZMod p
  b : ZMod p
  c : ZMod p

namespace Heisenberg

variable {p : ℕ}

instance : Mul (Heisenberg p) :=
  ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩

instance : One (Heisenberg p) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (Heisenberg p) :=
  ⟨fun x => ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

@[simp] theorem mul_a (x y : Heisenberg p) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : Heisenberg p) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : Heisenberg p) : (x * y).c = x.c + y.c + x.a * y.b := rfl
@[simp] theorem one_a : (1 : Heisenberg p).a = 0 := rfl
@[simp] theorem one_b : (1 : Heisenberg p).b = 0 := rfl
@[simp] theorem one_c : (1 : Heisenberg p).c = 0 := rfl
@[simp] theorem inv_a (x : Heisenberg p) : x⁻¹.a = -x.a := rfl
@[simp] theorem inv_b (x : Heisenberg p) : x⁻¹.b = -x.b := rfl
@[simp] theorem inv_c (x : Heisenberg p) : x⁻¹.c = -x.c + x.a * x.b := rfl

instance : Group (Heisenberg p) where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by ext <;> simp

/-- The `x`-generator `⟨1,0,0⟩` of the Heisenberg group. -/
def xGen (p : ℕ) : Heisenberg p := ⟨1, 0, 0⟩

/-- The `y`-generator `⟨0,1,0⟩` of the Heisenberg group. -/
def yGen (p : ℕ) : Heisenberg p := ⟨0, 1, 0⟩

/-- The bijection `Heisenberg p ≃ (ZMod p)³` used to transport finiteness. -/
def equivProd (p : ℕ) : Heisenberg p ≃ ZMod p × ZMod p × ZMod p where
  toFun x := (x.a, x.b, x.c)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv x := by cases x; rfl
  right_inv t := by rfl

instance : DecidableEq (Heisenberg p) := (equivProd p).decidableEq

instance [NeZero p] : Fintype (Heisenberg p) := Fintype.ofEquiv _ (equivProd p).symm

/-- The Heisenberg group has order `p³`. -/
theorem card_eq [NeZero p] : Fintype.card (Heisenberg p) = p ^ 3 := by
  sorry

end Heisenberg

open Heisenberg

/-- **Part (a).** For any `z` with `z^p = 1`, there is a *unique* representation `ρ` of the
Heisenberg group on `V = ZMod p → ℂ` acting on the generators by
`(ρ xGen f)(t) = f(t-1)` and `(ρ yGen f)(t) = z^t · f(t)`. Uniqueness holds because `xGen`
and `yGen` generate `G`, so this data determines `ρ(g)` for every `g`. -/
theorem exists_unique_rep [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) :
    ∃! ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ),
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1)) ∧
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = z ^ t.val * f t) := by
  sorry

/-- **Part (b).** The representation `R_z` (any `ρ` satisfying the generator conditions with a
`p`-th root of unity `z`) is irreducible if and only if `z ≠ 1`. -/
theorem irreducible_iff [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hx : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1))
    (hy : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = z ^ t.val * f t) :
    IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) ρ.asModule ↔ z ≠ 1 := by
  sorry

/-- **Part (c), classification of `1`-dimensional representations.** The one-dimensional
complex representations of the Heisenberg group are its group homomorphisms to `ℂˣ`, and there
are exactly `p²` of them (the abelianization is `(ZMod p)²`). -/
theorem one_dim_reps_card [Fact p.Prime] :
    Nat.card (Heisenberg p →* ℂˣ) = p ^ 2 := by
  sorry

/-- **Part (c), decomposition of `R_1`.** When `z = 1` the representation `R_1` decomposes as
an internal direct sum of `p` one-dimensional `G`-invariant subspaces (the `p` distinct
characters of the cyclic quotient, each occurring exactly once). -/
theorem R1_decomposes [Fact p.Prime]
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hx : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1))
    (hy : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = f t) :
    ∃ S : Fin p → Submodule ℂ (ZMod p → ℂ),
      (∀ i, ∀ (g : Heisenberg p), ∀ v ∈ S i, ρ g v ∈ S i) ∧
      (∀ i, Module.finrank ℂ (S i) = 1) ∧
      DirectSum.IsInternal S := by
  sorry

/-- **Part (d).** Every irreducible complex representation of the Heisenberg group has
dimension `1` or `p`. (Combined with (c) and the sum-of-squares formula
`p²·1² + (p-1)·p² = p³`, the irreducibles are exactly the `p²` characters together with the
`p-1` representations `R_z` for `z ≠ 1`, each of dimension `p`.) -/
theorem irreducible_dim [Fact p.Prime]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Heisenberg p) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = p := by
  sorry

end Etingof.Problem4_12_2
