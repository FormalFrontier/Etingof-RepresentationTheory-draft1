import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Definition 7.8.1: Complex, Differentials, Cohomology, Exact Sequence

A sequence of objects C_i (i ∈ ℤ) of an abelian category C and morphisms
d_i : C_i → C_{i+1} is a **complex** if the composition of any two consecutive
arrows is zero. The d_i are called **differentials**.

The **cohomology** is H^i = Ker(d_i)/Im(d_{i-1}). The complex is **exact** in the
i-th term if H^i = 0, and is an **exact sequence** if exact in all terms.

## Mathlib correspondence

Exact match:
- `CochainComplex` for complexes
- `HomologicalComplex.d` for differentials
- `HomologicalComplex.homology` for cohomology
- `HomologicalComplex.ExactAt` for exactness in one term
- `HomologicalComplex.Acyclic` for exactness in all terms (an exact sequence)
-/

open CategoryTheory

/-- A cochain complex in an abelian category, in the sense of Etingof Definition 7.8.1.
This is `CochainComplex` (= `HomologicalComplex` with `ComplexShape.up ℤ`) in Mathlib. -/
abbrev Etingof.CochainComplex' (C : Type*) [Category C]
    [Limits.HasZeroMorphisms C] := _root_.CochainComplex C ℤ

/-- The differential `d_i : C_i → C_{i+1}` of a cochain complex, in the sense of
Etingof Definition 7.8.1. This is `HomologicalComplex.d` in Mathlib. -/
abbrev Etingof.differential {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (K : Etingof.CochainComplex' C) (i : ℤ) : K.X i ⟶ K.X (i + 1) := K.d i (i + 1)

/-- The cohomology `H^i = Ker(d_i)/Im(d_{i-1})` of a cochain complex, in the sense of
Etingof Definition 7.8.1. This is `HomologicalComplex.homology` in Mathlib. -/
noncomputable abbrev Etingof.cohomology {C : Type*} [Category C] [Abelian C]
    (K : Etingof.CochainComplex' C) (i : ℤ) := K.homology i

/-- A cochain complex is **exact in the i-th term** if its cohomology `H^i` vanishes,
in the sense of Etingof Definition 7.8.1. This is `HomologicalComplex.ExactAt` in
Mathlib; `HomologicalComplex.exactAt_iff_isZero_homology` shows it is equivalent to
`H^i = 0`. -/
abbrev Etingof.ExactAt {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (K : Etingof.CochainComplex' C) (i : ℤ) : Prop := K.ExactAt i

/-- A cochain complex is **an exact sequence** if it is exact in every term, in the
sense of Etingof Definition 7.8.1. This is `HomologicalComplex.Acyclic` in Mathlib. -/
abbrev Etingof.IsExactSequence {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (K : Etingof.CochainComplex' C) : Prop := K.Acyclic
