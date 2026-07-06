import Mathlib

/-!
# Problem 2.13.1: The Dehn invariant and Hilbert's third problem

To any polyhedron `A` one attaches its **Dehn invariant** `D(A) ∈ ℝ ⊗ (ℝ/ℚ)` (a tensor product of
`ℚ`-vector spaces), `D(A) = Σₐ l(a) ⊗ β(a)/π`, summing over edges `a` with length `l(a)` and
dihedral angle `β(a)`. The problem has three parts:

* **(a)** cutting `A` into `B` and `C` gives `D(A) = D(B) + D(C)`;
* **(b)** `α = arccos(1/3)/π` is irrational;
* **(c)** the regular tetrahedron and cube of equal volume have different Dehn invariants, so they
  are not scissors-congruent (a negative answer to Hilbert's third problem).

## Formalization

The cleanly-statable core is part **(b)**: the irrationality of `arccos(1/3)/π`. Parts (a) and (c)
require the Dehn-invariant construction on polyhedra (the tensor product `ℝ ⊗_ℚ (ℝ/ℚ)` and a model
of polyhedra with edges/dihedral angles) and are deferred to a dedicated follow-up item.

This is the **statement pass**: part (b) is recorded with a `sorry` proof.
-/

namespace Etingof.Problem2_13_1

open Real

/-- **Problem 2.13.1(b).** The number `α = arccos(1/3)/π` is irrational. -/
theorem irrational_arccos_third_div_pi : Irrational (arccos (1 / 3) / π) := by
  sorry

end Etingof.Problem2_13_1
