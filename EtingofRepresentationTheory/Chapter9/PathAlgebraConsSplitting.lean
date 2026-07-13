import EtingofRepresentationTheory.Chapter9.PathAlgebraLengthGrading

/-!
# Cons-splitting of the path algebra `A = PathAlgebra k Q`

Sixth layer of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i), parent #6420). Write `A := PathAlgebra k Q`. Its length-graded pieces `A_n`
(spanned by the length-`n` basis paths) satisfy the **cons-splitting**

```
A_n ⊗_S V ≅ A_{n+1},   x ⊗ e ↦ x · e   (concatenation),
```

the `S`-bimodule isomorphism underlying `Mono (stdd M)` for the standard short complex
(`Chapter9/PathAlgebraStandardComplex.lean`). The forward map `x ⊗ e ↦ x · e` appends one arrow
(`ofPath_mul_arrowElt`, from `Chapter9/PathAlgebraLengthGrading.lean`); the inverse decomposes a
length-`(n+1)` path into its initial length-`n` path and its final arrow.

This file records the **combinatorial core** of that iso: every path index of positive length is
*uniquely* a length-`n` path index followed by one arrow. Mathlib's
`Quiver.Path.length_ne_zero_iff_eq_cons` supplies existence; `Quiver.Path.comp_inj` /
`Quiver.Path.cons.injEq` supply uniqueness. These feed the genuine (non-`sorry`) inverse of the
bundled `A_n ⊗_S V ≅ A_{n+1}` isomorphism.

Template: the polynomial coordinate iso `coordMapCH` in `Chapter9/KoszulHelpers.lean` and its use
in `Chapter9/Example9_4_4.lean` (`koszulSES_shortExact`). The path-length grading itself lives in
`Chapter9/PathAlgebraLengthGrading.lean`.
-/

universe u

open Etingof

namespace Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-! ## Unique cons-decomposition of a positive-length path

A path `q : Path a c` of length `n + 1` is uniquely `q = p.comp e.toPath` with `p : Path a b` of
length `n` and `e : b ⟶ c` an arrow. This is the index-level inverse of the concatenation map
`(p, e) ↦ p.comp e.toPath` underlying the cons-splitting `A_n ⊗_S V ≅ A_{n+1}`. -/

omit [DecidableEq Q] in
/-- **Existence of the cons-decomposition.** A path of length `n + 1` factors as a length-`n`
initial path followed by one final arrow. Repackages Mathlib's
`Quiver.Path.length_ne_zero_iff_eq_cons` with the explicit degree bookkeeping. -/
theorem exists_cons_decomp {a c : Q} (q : Quiver.Path a c) {n : ℕ} (hq : q.length = n + 1) :
    ∃ (b : Q) (p : Quiver.Path a b) (e : b ⟶ c), q = p.comp e.toPath ∧ p.length = n := by
  have hne : q.length ≠ 0 := by rw [hq]; exact Nat.succ_ne_zero n
  obtain ⟨b, p, e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons q).1 hne
  refine ⟨b, p, e, (Quiver.Path.comp_toPath_eq_cons p e).symm, ?_⟩
  rw [Quiver.Path.length_cons] at hq
  exact Nat.succ_injective hq

omit [DecidableEq Q] in
/-- **Uniqueness of the cons-decomposition.** Two cons-decompositions of the same path agree in
their middle vertex, initial path, and final arrow. The middle-vertex and arrow equalities are
stated as heterogeneous equalities (`HEq`) because the arrow's type depends on the vertex. -/
theorem cons_decomp_unique {a c b₁ b₂ : Q}
    (p₁ : Quiver.Path a b₁) (e₁ : b₁ ⟶ c) (p₂ : Quiver.Path a b₂) (e₂ : b₂ ⟶ c)
    (h : p₁.comp e₁.toPath = p₂.comp e₂.toPath) :
    b₁ = b₂ ∧ HEq p₁ p₂ ∧ HEq e₁ e₂ := by
  rw [Quiver.Path.comp_toPath_eq_cons, Quiver.Path.comp_toPath_eq_cons] at h
  simp only [Quiver.Path.cons.injEq] at h
  exact h

end Etingof.PathAlgebra
