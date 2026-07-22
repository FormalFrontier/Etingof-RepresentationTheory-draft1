import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Ring.Opposite

/-!
# Definition 9.4.3: Homological dimension of a ring

A ring `A` is said to have **left** (respectively, **right**) **homological dimension** `≤ d`
if every left (respectively, right) `A`-module has projective dimension `≤ d`. The left
(respectively right) homological dimension of `A` is exactly `d` if it is `≤ d` but not
`≤ d - 1`. If no such `d` exists, the homological dimension is infinite.

## Formalization

Right `A`-modules are the same thing as left `Aᵐᵒᵖ`-modules, so we define the right notions by
transporting the left ones across `MulOpposite`:

* `Etingof.HasHomologicalDimensionLE R d` / `Etingof.homologicalDimension R` are the **left**
  versions, phrased via `CategoryTheory.HasProjectiveDimensionLE` on `ModuleCat R`. These keep
  their historical (unqualified) names because the bulk of Chapter 9 only ever needs the left
  dimension.
* `Etingof.HasLeftHomologicalDimensionLE` / `Etingof.leftHomologicalDimension` are explicit
  aliases documenting that scope.
* `Etingof.HasRightHomologicalDimensionLE R d := HasHomologicalDimensionLE Rᵐᵒᵖ d` and
  `Etingof.rightHomologicalDimension R := homologicalDimension Rᵐᵒᵖ` are the right versions.

The transport lemmas below record that the right notions agree with the left notions over
`Rᵐᵒᵖ` (definitionally), and, for commutative rings, that the left and right dimensions coincide
(`Etingof.rightHomologicalDimension_eq_left` in
`Chapter9/HomologicalDimensionRingEquiv.lean`).

## Mathlib correspondence

Not directly in Mathlib. We define `HasHomologicalDimensionLE` as a predicate and
`homologicalDimension` as the infimum, both in terms of
`CategoryTheory.HasProjectiveDimensionLE` on `ModuleCat R`.
-/

universe u

/-- A ring `R` has **left** homological dimension `≤ d` if every left `R`-module has projective
dimension `≤ d`, in the sense of Etingof Definition 9.4.3. This is the historical unqualified
name; see `Etingof.HasLeftHomologicalDimensionLE` for the explicitly-left alias and
`Etingof.HasRightHomologicalDimensionLE` for the right version. -/
def Etingof.HasHomologicalDimensionLE (R : Type u) [Ring R] (d : ℕ) : Prop :=
  ∀ (M : ModuleCat.{u} R), CategoryTheory.HasProjectiveDimensionLE M d

/-- The **left** homological dimension of a ring, in the sense of Etingof Definition 9.4.3.
The smallest `d` such that every left module has projective dimension `≤ d`, or `⊤` if no such
`d` exists. Returns a value in `ℕ∞`. This is the historical unqualified name; see
`Etingof.leftHomologicalDimension` for the explicitly-left alias and
`Etingof.rightHomologicalDimension` for the right version. -/
noncomputable def Etingof.homologicalDimension (R : Type u) [Ring R] : ℕ∞ :=
  ⨅ (d : ℕ) (_ : Etingof.HasHomologicalDimensionLE R d), (d : ℕ∞)

/-- A ring `R` has **left** homological dimension `≤ d` if every left `R`-module has projective
dimension `≤ d`. An explicitly-named alias for the historical `Etingof.HasHomologicalDimensionLE`,
provided so downstream code can name the left/right sides symmetrically. -/
abbrev Etingof.HasLeftHomologicalDimensionLE (R : Type u) [Ring R] (d : ℕ) : Prop :=
  Etingof.HasHomologicalDimensionLE R d

/-- The **left** homological dimension of a ring. An explicitly-named alias for the historical
`Etingof.homologicalDimension`. -/
noncomputable abbrev Etingof.leftHomologicalDimension (R : Type u) [Ring R] : ℕ∞ :=
  Etingof.homologicalDimension R

/-- A ring `R` has **right** homological dimension `≤ d` if every right `R`-module has projective
dimension `≤ d`, in the sense of Etingof Definition 9.4.3. Right `R`-modules are left
`Rᵐᵒᵖ`-modules, so we define this by transporting the left notion across `MulOpposite`. -/
def Etingof.HasRightHomologicalDimensionLE (R : Type u) [Ring R] (d : ℕ) : Prop :=
  Etingof.HasHomologicalDimensionLE Rᵐᵒᵖ d

/-- The **right** homological dimension of a ring, defined as the left homological dimension of
`Rᵐᵒᵖ`. Returns a value in `ℕ∞`. -/
noncomputable def Etingof.rightHomologicalDimension (R : Type u) [Ring R] : ℕ∞ :=
  Etingof.homologicalDimension Rᵐᵒᵖ

/-- The right homological-dimension bound is, by definition, the left bound over `Rᵐᵒᵖ`. -/
@[simp]
theorem Etingof.hasRightHomologicalDimensionLE_iff_op (R : Type u) [Ring R] (d : ℕ) :
    Etingof.HasRightHomologicalDimensionLE R d ↔ Etingof.HasLeftHomologicalDimensionLE Rᵐᵒᵖ d :=
  Iff.rfl

/-- The right homological dimension is, by definition, the left homological dimension over
`Rᵐᵒᵖ`. -/
@[simp]
theorem Etingof.rightHomologicalDimension_eq_left_op (R : Type u) [Ring R] :
    Etingof.rightHomologicalDimension R = Etingof.leftHomologicalDimension Rᵐᵒᵖ :=
  rfl
