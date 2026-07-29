import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import Mathlib.RingTheory.SimpleModule.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# The vertex subalgebra of a path algebra

Foundations for the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i)). Write `A := PathAlgebra k Q` and `S := Q → k`, the commutative
subalgebra spanned by the trivial-path idempotents `eᵢ = ofPath ⟨i, i, nil⟩`.

This file supplies the reusable vertex-subalgebra layer that the noncommutative induction
functor `A ⊗_S -` is built on:

* `Etingof.PathAlgebra.isSemisimpleRing_vertexAlgebra`: `S = Q → k` is a semisimple ring
  (a finite product of fields), so every `S`-module is projective.
* `Etingof.PathAlgebra.ofPath_nil_mul_ofPath_nil`: orthogonality of the vertex idempotents,
  `eᵢ eⱼ = δᵢⱼ eᵢ`.
* `Etingof.PathAlgebra.vertexEmbedding`: the ring homomorphism `S →+* A`,
  `a ↦ ∑ i, a i • eᵢ`, along which restriction/induction of scalars is taken.

## Obstruction note

The image of `vertexEmbedding` is not central in `A` (the idempotents `eᵢ` do not commute
with the arrows), so `A` is not a commutative-base `S`-algebra and Mathlib's `extendScalars`
(which needs `[CommRing R] [CommRing S]`) does not apply. This is why the induction
functor `A ⊗_S -` requires new infrastructure.
-/

universe u

open Etingof

namespace Etingof.PathAlgebra

/-- **Semisimplicity of the vertex algebra.** The subalgebra `S = Q → k` spanned by the trivial
paths is a finite product of copies of the field `k`, hence a semisimple ring. Consequently
every `S`-module is projective, the fact that makes both nonzero terms of the standard
resolution projective `A`-modules. -/
theorem isSemisimpleRing_vertexAlgebra (k Q : Type*) [Field k] [Finite Q] :
    IsSemisimpleRing (Q → k) :=
  inferInstance

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- **Orthogonality of the vertex idempotents.** For vertices `i j`, the product of the trivial
paths `eᵢ = ofPath ⟨i, i, nil⟩` and `eⱼ` is `eᵢ` when `i = j` and `0` otherwise. -/
theorem ofPath_nil_mul_ofPath_nil (i j : Q) :
    (ofPath ⟨i, i, Quiver.Path.nil⟩ : PathAlgebra k Q) * ofPath ⟨j, j, Quiver.Path.nil⟩
      = if i = j then ofPath ⟨i, i, Quiver.Path.nil⟩ else 0 := by
  rw [ofPath, ofPath, single_mul_single, one_mul, one_smul, compSingle_nil_left]
  split_ifs with h
  · subst h; rfl
  · rfl

variable (k Q) in
/-- **The vertex embedding.** The ring homomorphism `S = (Q → k) →+* A = PathAlgebra k Q`
sending a family `a` of scalars to `∑ i, a i • eᵢ`, i.e. `∑ i, Finsupp.single ⟨i, i, nil⟩ (a i)`.

Multiplicativity `f(a) · f(b) = ∑ᵢⱼ (aᵢ bⱼ)(eᵢ eⱼ) = ∑ᵢ (aᵢ bᵢ) eᵢ = f(a·b)` uses the
idempotent orthogonality `ofPath_nil_mul_ofPath_nil` to collapse the double sum. The unit maps
to `∑ i, eᵢ = 1` (`sum_trivialPaths_eq_one`). The image is not central. -/
noncomputable def vertexEmbedding [Fintype Q] : (Q → k) →+* PathAlgebra k Q where
  toFun a := ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (a i)
  map_one' := by
    simp only [Pi.one_apply]
    exact one_def.symm
  map_mul' a b := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [single_mul_single, compSingle_nil_left, if_pos rfl, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      rfl
    · intro j _ hji
      rw [single_mul_single, compSingle_nil_left, if_neg (Ne.symm hji), smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  map_zero' := by simp
  map_add' a b := by
    simp only [Pi.add_apply, Finsupp.single_add]
    rw [Finset.sum_add_distrib]

@[simp]
theorem vertexEmbedding_apply [Fintype Q] (a : Q → k) :
    vertexEmbedding k Q a
      = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (a i) :=
  rfl

end Etingof.PathAlgebra
