import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter9.PathAlgebraVertexSubalgebra
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# Projective covers of the path algebra and the Hom-space identification

For the path algebra `A = PathAlgebra k Q` of a finite quiver, the indecomposable projective
covers of the simple modules are the principal left ideals `Pᵢ = A · eᵢ`, where
`eᵢ = ofPath ⟨i, i, nil⟩` is the trivial-path idempotent at vertex `i`. This file constructs
that family and proves the Hom-space identification that carries the mathematical content of
Problem 9.4.6 (ii):

`Hom_A(A·eᵢ, A·eⱼ) ≅ eᵢ · A · eⱼ ≅ (paths i → j) →₀ k.`

The first isomorphism is the standard idempotent fact `Hom_A(A·e, M) ≅ e·M` (a hom `f` is
determined by `f(e) ∈ e·M`, and every `x ∈ e·M` gives back the hom `y ↦ y·x`). The second is
the observation that `eᵢ · A · eⱼ` is spanned by the basis paths from `i` to `j`.

## Main definitions and results

* `Etingof.PathAlgebra.pathAlgebraProj k Q i` — the projective cover `A · eᵢ`, as the principal
  left submodule `Submodule.span A {eᵢ}` with its inherited `A`- and `k`-module structures.
* `Etingof.PathAlgebra.pathAlgebraHomEquiv` —
  `(A·eᵢ →ₗ[A] A·eⱼ) ≃ₗ[k] (Quiver.Path i j →₀ k)`, the Hom-space identification.
-/

universe u

open Etingof
open scoped Classical

namespace Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-- The underlying finsupp coefficient of a path-algebra element at a basis index. Because
`PathAlgebra k Q` is a `def` (not a reducible `abbrev`), there is no `FunLike` instance to apply
elements as functions directly; `coeff f x` is the coefficient `f x` of the underlying finsupp. -/
noncomputable def coeff (f : PathAlgebra k Q) (x : QuiverPathIndex Q) : k :=
  @DFunLike.coe (QuiverPathIndex Q →₀ k) (QuiverPathIndex Q) (fun _ => k) _ f x

@[simp] theorem coeff_zero (x : QuiverPathIndex Q) : coeff (0 : PathAlgebra k Q) x = 0 := rfl

theorem coeff_add (f g : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (f + g) x = coeff f x + coeff g x :=
  Finsupp.add_apply _ _ _

theorem coeff_smul (c : k) (f : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (c • f) x = c * coeff f x :=
  Finsupp.smul_apply _ _ _

@[simp] theorem coeff_single (x y : QuiverPathIndex Q) (c : k) :
    coeff (Finsupp.single x c : PathAlgebra k Q) y = if x = y then c else 0 :=
  Finsupp.single_apply

/-- Two path-algebra elements are equal iff all their coefficients agree. -/
theorem coeff_ext {f g : PathAlgebra k Q} (h : ∀ x, coeff f x = coeff g x) : f = g :=
  Finsupp.ext h

/-- The trivial-path idempotent `eᵢ = ofPath ⟨i, i, nil⟩` at vertex `i`. -/
noncomputable def eIdem (i : Q) : PathAlgebra k Q := ofPath ⟨i, i, Quiver.Path.nil⟩

/-- `eᵢ` is idempotent: `eᵢ * eᵢ = eᵢ`. -/
theorem eIdem_mul_self (i : Q) : (eIdem i : PathAlgebra k Q) * eIdem i = eIdem i := by
  rw [eIdem, ofPath_nil_mul_ofPath_nil, if_pos rfl]

/-- Coefficient of `eᵢ * a` at an index `x`: it keeps the paths whose *source* is `i` and kills
the others. -/
theorem coeff_eIdem_mul (i : Q) (a : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (eIdem i * a) x = if x.1 = i then coeff a x else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp [mul_zero]
  | add u v hu hv =>
    rw [mul_add, coeff_add, hu, hv, coeff_add]
    split_ifs <;> ring
  | single y c =>
    obtain ⟨s, t, p⟩ := y
    simp only [eIdem, ofPath]
    rw [single_mul_single, one_mul, compSingle_nil_left]
    by_cases his : i = s
    · rw [if_pos his]; subst his
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hx : x = (⟨i, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [coeff_single]
      · simp [coeff_single, hx, Ne.symm hx]
    · rw [if_neg his, smul_zero, coeff_zero]
      by_cases hx : x = (⟨s, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [coeff_single, Ne.symm his]
      · simp [coeff_single, hx, Ne.symm hx]

/-- Coefficient of `a * eⱼ` at an index `x`: it keeps the paths whose *target* is `j` and kills
the others. -/
theorem coeff_mul_eIdem (j : Q) (a : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (a * eIdem j) x = if x.2.1 = j then coeff a x else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp [zero_mul]
  | add u v hu hv =>
    rw [add_mul, coeff_add, hu, hv, coeff_add]
    split_ifs <;> ring
  | single y c =>
    obtain ⟨s, t, p⟩ := y
    simp only [eIdem, ofPath]
    rw [single_mul_single, mul_one, compSingle_nil_right]
    by_cases htj : t = j
    · rw [if_pos htj]; subst htj
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hx : x = (⟨s, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [coeff_single]
      · simp [coeff_single, hx, Ne.symm hx]
    · rw [if_neg htj, smul_zero, coeff_zero]
      by_cases hx : x = (⟨s, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [coeff_single, htj]
      · simp [coeff_single, hx, Ne.symm hx]

/-- Coefficient of `eᵢ * a * eⱼ` at an index `x = ⟨s, t, p⟩`: it keeps the paths from `i` to `j`
and kills the others. This is the combinatorial heart of the identification `eᵢ A eⱼ ≅ paths i→j`. -/
theorem coeff_eIdem_mul_eIdem (i j : Q) (a : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (eIdem i * a * eIdem j) x = if x.1 = i ∧ x.2.1 = j then coeff a x else 0 := by
  rw [coeff_mul_eIdem, coeff_eIdem_mul]
  by_cases htj : x.2.1 = j
  · by_cases his : x.1 = i
    · rw [if_pos htj, if_pos his, if_pos ⟨his, htj⟩]
    · rw [if_pos htj, if_neg his, if_neg (fun h => his h.1)]
  · rw [if_neg htj, if_neg (fun h => htj h.2)]

end Etingof.PathAlgebra
