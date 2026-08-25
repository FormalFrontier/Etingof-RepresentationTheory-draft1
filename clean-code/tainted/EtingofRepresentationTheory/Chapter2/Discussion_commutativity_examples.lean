import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.FreeAlgebra

/-!
# Discussion (commutativity examples after the five examples of Section 2.2)

The book observes that, among the running examples of algebras, `A` is commutative in cases 1
and 2, not commutative in cases 3 (`End V` with `dim V > 1`) and 4 (`FreeAlgebra` on `> 1`
generators), and in case 5 (`A = k[G]`) commutative if and only if `G` is commutative.

This file formalizes the two non-trivial claims:

* **Case 5.** `MonoidAlgebra k G` is commutative if and only if `G` is commutative. The forward
  direction (`G` commutative `⇒` `k[G]` commutative) is Mathlib's `MonoidAlgebra.commSemiring`;
  the converse uses that `g ↦ single g 1` is an injective multiplicative map.
* **Cases 3 and 4.** `End V` is noncommutative for `dim V > 1` (witnessed at `dim V = 2` by two
  `2 × 2` matrix units), and `FreeAlgebra k (Fin n)` is noncommutative for `n > 1` (witnessed at
  `n = 2` by the two generators, mapped to the non-commuting matrix units).
-/

namespace Etingof

open Matrix

/-- **Case 5.** The group algebra `k[G]` is commutative if and only if the monoid `G` is
commutative. -/
theorem monoidAlgebra_mul_comm_iff (k : Type*) [CommSemiring k] [Nontrivial k]
    (G : Type*) [Monoid G] :
    (∀ x y : MonoidAlgebra k G, x * y = y * x) ↔ (∀ g h : G, g * h = h * g) := by
  constructor
  · -- `k[G]` commutative ⇒ `G` commutative: compare `single g 1 * single h 1` with the
    -- reversed product and use that `g ↦ single g 1` is injective (as `1 ≠ 0`).
    intro hcomm g h
    have key := hcomm (MonoidAlgebra.single g 1) (MonoidAlgebra.single h 1)
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single] at key
    simp only [mul_one] at key
    exact MonoidAlgebra.single_left_injective one_ne_zero key
  · -- `G` commutative ⇒ `k[G]` commutative: this is Mathlib's `CommSemiring` instance.
    intro hcomm
    letI : CommMonoid G := { (inferInstance : Monoid G) with mul_comm := hcomm }
    intro x y
    exact mul_comm x y

section Noncommutative

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- The two `2 × 2` matrix units `E₀₁` and `E₁₀` do not commute: `E₀₁E₁₀ = E₀₀` while
`E₁₀E₀₁ = E₁₁`, and these differ in their `(0,0)` entry. This is the concrete witness for the
noncommutativity of `End V` (here `dim V = 2`). -/
private lemma single_not_commute :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) k) * Matrix.single 1 0 1
      ≠ Matrix.single 1 0 1 * Matrix.single 0 1 1 := by
  intro h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrFun (congrFun h 0) 0
  rw [Matrix.single_apply, Matrix.single_apply, if_pos (by decide), if_neg (by decide),
    mul_one] at h00
  exact one_ne_zero h00

/-- **Case 3.** `End V` is not commutative when `dim V > 1`: already for `V = k²` there are two
endomorphisms (the matrix units `E₀₁`, `E₁₀`) that do not commute. -/
example : ∃ f g : Module.End k (Fin 2 → k), f * g ≠ g * f := by
  refine ⟨Matrix.toLinAlgEquiv' (Matrix.single 0 1 1),
    Matrix.toLinAlgEquiv' (Matrix.single 1 0 1), ?_⟩
  intro h
  rw [← map_mul, ← map_mul] at h
  exact single_not_commute k ((Matrix.toLinAlgEquiv' (R := k)).injective h)

/-- **Case 4.** `FreeAlgebra k (Fin n)` is not commutative when `n > 1`: the first two
generators do not commute, since the algebra map sending them to the non-commuting matrix units
`E₀₁`, `E₁₀` would otherwise force those matrix units to commute. -/
theorem freeAlgebra_noncommutative_of_one_lt (n : ℕ) (hn : 1 < n) :
    ∃ a b : FreeAlgebra k (Fin n), a * b ≠ b * a := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let images : Fin n → Matrix (Fin 2) (Fin 2) k := fun i =>
    if i = i0 then Matrix.single 0 1 1
    else if i = i1 then Matrix.single 1 0 1
    else 0
  refine ⟨FreeAlgebra.ι k i0, FreeAlgebra.ι k i1, fun hcomm => ?_⟩
  apply single_not_commute k
  have := congrArg
    (FreeAlgebra.lift k images) hcomm
  simpa only [map_mul, FreeAlgebra.lift_ι_apply, images, if_pos, if_neg hne.symm, hne] using this

end Noncommutative

section GeneralEndomorphism

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- **Case 3, general form.** The endomorphism algebra `End_k V` of any vector space with
`2 ≤ dim V` is noncommutative, including when `V` is infinite-dimensional: choosing a basis,
the two "matrix unit" endomorphisms `E₀₁` (sending the second basis vector to the first, all
others to `0`) and `E₁₀` (sending the first to the second, all others to `0`) fail to commute.
This is the source claim of the discussion after Example 2.2.4; the concrete `V = k²` case above
is the special case `dim V = 2`. -/
theorem End_noncommutative_of_two_le_rank
    (h : (2 : Cardinal) ≤ Module.rank k V) :
    ∃ f g : Module.End k V, f * g ≠ g * f := by
  let b := Module.Free.chooseBasis k V
  have hcard : (2 : Cardinal) ≤ Cardinal.mk (Module.Free.ChooseBasisIndex k V) := by
    rwa [← Module.Free.rank_eq_card_chooseBasisIndex]
  obtain ⟨i0, i1, hne⟩ := Cardinal.two_le_iff.mp hcard
  -- `f = E₀₁` (sends `b i1 ↦ b i0`, others to `0`), `g = E₁₀` (sends `b i0 ↦ b i1`).
  let f : Module.End k V := b.constr k (fun i => if i = i1 then b i0 else 0)
  let g : Module.End k V := b.constr k (fun i => if i = i0 then b i1 else 0)
  have hf0 : f (b i0) = 0 := by simp [f, hne]
  have hf1 : f (b i1) = b i0 := by simp [f]
  have hg0 : g (b i0) = b i1 := by simp [g]
  refine ⟨f, g, fun hcomm => ?_⟩
  -- Evaluate the claimed commutation at the first basis vector `b i0`:
  -- `f (g (b i0)) = f (b i1) = b i0`, but `g (f (b i0)) = g 0 = 0`.
  have key := congrArg (fun φ : Module.End k V => φ (b i0)) hcomm
  simp only [Module.End.mul_apply, hg0, hf1, hf0, map_zero] at key
  exact b.ne_zero i0 key

end GeneralEndomorphism

end Etingof
