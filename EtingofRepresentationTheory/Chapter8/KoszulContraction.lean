import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The contraction `ιᵤ : ⋀ⁱ V → ⋀ⁱ⁻¹ V` of Problem 8.2.10

Problem 8.2.10 builds the Koszul resolution out of the *contraction* operator: for a linear
functional `u : V →ₗ[k] k` the book defines `ιᵤ : ⋀ⁱ V → ⋀ⁱ⁻¹ V` by

> `ιᵤ (v₁ ∧ ⋯ ∧ vᵢ) = ∑_{j=1}^{i} (-1)ʲ u(vⱼ) v₁ ∧ … v̂ⱼ ⋯ ∧ vᵢ`.

This file constructs that operator and establishes the two properties the Koszul differential
needs: it squares to zero, and contractions by different functionals anticommute.

## Main definitions

* `Etingof.exteriorContraction u n : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M` — the book's `ιᵤ`.

## Main results

* `Etingof.exteriorContraction_ιMulti` — the book's defining formula, verbatim (with `Fin (n + 1)`
  0-indexed, so the book's `(-1)ʲ` for `j = 1, …, i` becomes `(-1)^(j + 1)`).
* `Etingof.exteriorContraction_exteriorContraction` — `ιᵤ ∘ ιᵤ = 0`.
* `Etingof.exteriorContraction_comm` — `ιᵤ ∘ ιᵤ' = - ιᵤ' ∘ ιᵤ`.

## Implementation notes

Mathlib's `⋀[R]^n M` is a submodule of `ExteriorAlgebra R M`, which in turn is an abbreviation for
`CliffordAlgebra (0 : QuadraticForm R M)`. So the ungraded contraction is already available as
`CliffordAlgebra.contractLeft`, together with `CliffordAlgebra.contractLeft_contractLeft` and
`CliffordAlgebra.contractLeft_comm`. The work here is to check that it carries `⋀ⁿ⁺¹` into `⋀ⁿ`
and that the resulting graded map is the book's alternating sum.

`CliffordAlgebra.contractLeft` corresponds to the *unsigned* alternating sum, i.e. to the book's
`ιᵤ` up to an overall sign; `exteriorContraction` carries that sign so that the statement of
`exteriorContraction_ιMulti` matches the book character for character.
-/

universe u v

open scoped BigOperators

namespace Etingof

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Formula

variable (R)

/-- The ungraded contraction applied to a wedge of `n + 1` vectors: the alternating sum
`∑ⱼ (-1)ʲ u(vⱼ) v₀ ∧ … v̂ⱼ ⋯ ∧ vₙ`, with `j` running over `Fin (n + 1)` (so 0-indexed).

This is `CliffordAlgebra.contractLeft`'s value; the book's `ιᵤ` is its negative, see
`Etingof.exteriorContraction_ιMulti`. -/
theorem contractLeft_ιMulti (u : Module.Dual R M) :
    ∀ (n : ℕ) (v : Fin (n + 1) → M),
      CliffordAlgebra.contractLeft u (ExteriorAlgebra.ιMulti R (n + 1) v) =
        ∑ j : Fin (n + 1),
          ((-1 : R) ^ (j : ℕ) * u (v j)) • ExteriorAlgebra.ιMulti R n (v ∘ j.succAbove) := by
  intro n
  induction n with
  | zero =>
    intro v
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ n ih =>
    intro v
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
    have htail : Matrix.vecTail v = v ∘ Fin.succ := rfl
    rw [htail, ih (v ∘ Fin.succ)]
    -- Push `ι (v 0) * -` through the sum coming from the inductive hypothesis.
    rw [Finset.mul_sum]
    rw [Fin.sum_univ_succ (f := fun j : Fin (n + 2) =>
      ((-1 : R) ^ (j : ℕ) * u (v j)) • ExteriorAlgebra.ιMulti R (n + 1) (v ∘ j.succAbove))]
    have h0 : (v ∘ (0 : Fin (n + 2)).succAbove) = v ∘ Fin.succ := by
      funext i; simp [Fin.succAbove_zero]
    rw [h0]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsucc : (v ∘ (Fin.succ j).succAbove) =
        Fin.cons (v 0) ((v ∘ Fin.succ) ∘ j.succAbove) := by
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ i => simp [Fin.succ_succAbove_succ]
    have htl : Matrix.vecTail (Fin.cons (v 0) ((v ∘ Fin.succ) ∘ j.succAbove)) =
        (v ∘ Fin.succ) ∘ j.succAbove := by
      funext i; simp [Matrix.vecTail]
    rw [hsucc, ExteriorAlgebra.ιMulti_succ_apply, htl]
    simp only [Fin.cons_zero, Function.comp_apply]
    rw [mul_smul_comm]
    module

end Formula

section Graded

variable (R)

/-- `CliffordAlgebra.contractLeft u` carries `⋀ⁿ⁺¹ M` into `⋀ⁿ M`. -/
theorem contractLeft_mem_exteriorPower (u : Module.Dual R M) (n : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    CliffordAlgebra.contractLeft u x ∈ ⋀[R]^n M := by
  rw [← exteriorPower.ιMulti_span_fixedDegree R (n + 1) M] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [contractLeft_ιMulti R u n v]
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      exact ExteriorAlgebra.ιMulti_range R n (Set.mem_range_self _)
  | zero => simp
  | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
  | smul r y _ hy => simpa using Submodule.smul_mem _ r hy

/-- **The contraction of Problem 8.2.10.** For `u : V →ₗ[k] k` this is the book's
`ιᵤ : ⋀ⁱ V → ⋀ⁱ⁻¹ V`, characterised by
`ιᵤ (v₁ ∧ ⋯ ∧ vᵢ) = ∑ⱼ (-1)ʲ u(vⱼ) v₁ ∧ … v̂ⱼ ⋯ ∧ vᵢ`
(see `Etingof.exteriorContraction_ιMulti`). -/
noncomputable def exteriorContraction (u : Module.Dual R M) (n : ℕ) :
    ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  -(LinearMap.restrict (CliffordAlgebra.contractLeft u)
    (fun _ hx => contractLeft_mem_exteriorPower R u n hx))

variable {R}

@[simp]
theorem exteriorContraction_coe (u : Module.Dual R M) (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    (exteriorContraction R u n x : ExteriorAlgebra R M) =
      -CliffordAlgebra.contractLeft u (x : ExteriorAlgebra R M) :=
  rfl

/-- **The book's defining formula for `ιᵤ`.** With `Fin (n + 1)` indexed from `0`, the book's
`∑_{j=1}^{i} (-1)ʲ u(vⱼ) v₁ ∧ … v̂ⱼ ⋯ ∧ vᵢ` reads as follows. -/
theorem exteriorContraction_ιMulti (u : Module.Dual R M) (n : ℕ) (v : Fin (n + 1) → M) :
    exteriorContraction R u n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ j : Fin (n + 1),
        ((-1 : R) ^ ((j : ℕ) + 1) * u (v j)) • exteriorPower.ιMulti R n (v ∘ j.succAbove) := by
  apply Subtype.ext
  push_cast
  rw [exteriorContraction_coe]
  simp only [exteriorPower.ιMulti_apply_coe]
  rw [contractLeft_ιMulti R u n v, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pow_succ]
  module

/-- The Koszul differential's defining property: `ιᵤ ∘ ιᵤ = 0`. -/
@[simp]
theorem exteriorContraction_exteriorContraction (u : Module.Dual R M) (n : ℕ)
    (x : ⋀[R]^(n + 2) M) :
    exteriorContraction R u n (exteriorContraction R u (n + 1) x) = 0 := by
  apply Subtype.ext
  simp [CliffordAlgebra.contractLeft_contractLeft]

theorem exteriorContraction_comp_exteriorContraction (u : Module.Dual R M) (n : ℕ) :
    (exteriorContraction R u n).comp (exteriorContraction R u (n + 1)) = 0 :=
  LinearMap.ext fun x => exteriorContraction_exteriorContraction u n x

/-- Contractions by two functionals anticommute. This is what makes the Koszul differential
`∑ₐ xₐ ⊗ ι_{xₐ*}` square to zero: the symmetric-algebra factors commute while the contractions
anticommute. -/
theorem exteriorContraction_comm (u u' : Module.Dual R M) (n : ℕ) (x : ⋀[R]^(n + 2) M) :
    exteriorContraction R u n (exteriorContraction R u' (n + 1) x) =
      -exteriorContraction R u' n (exteriorContraction R u (n + 1) x) := by
  apply Subtype.ext
  simp [CliffordAlgebra.contractLeft_comm (d := u) (d' := u')]

end Graded

end Etingof
