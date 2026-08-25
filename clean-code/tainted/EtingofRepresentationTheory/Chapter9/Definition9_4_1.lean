import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Definition 9.4.1: Projective dimension

A module M has a **projective resolution** if there exists an exact sequence
… → P₁ → P₀ → M → 0 where each Pᵢ is projective.

The **projective dimension** pd(M) of M is the length of the shortest finite projective
resolution of M. If no finite projective resolution exists, pd(M) = ∞. Etingof records the
basic edge case that a projective module has projective dimension `0`; this includes the zero
module, whose one-term resolution `0 → 0 → 0` is already projective.

## Mathlib correspondence and the bottom edge case

Mathlib defines `CategoryTheory.projectiveDimension` for objects in an abelian category, via
vanishing of Ext groups, valued in `WithBot ℕ∞`. Its convention differs from the book at a
single point: the zero object is assigned the value `⊥`, so that `= 0` characterizes the
*nonzero* projective objects (`CategoryTheory.projectiveDimension_eq_zero_iff`). The book instead
assigns the zero module the value `0`, so that `= 0` characterizes *all* projective modules,
zero included.

We therefore expose two names:

* `Etingof.projectiveDimensionRaw` — the verbatim Mathlib value, retaining `⊥` on the zero
  module. Downstream homological infrastructure that needs the raw `WithBot ℕ∞` value uses this.
* `Etingof.projectiveDimension` — the book-faithful value `max 0 (raw)`, which agrees with the
  raw value everywhere except on the zero module, where it takes the source value `0`.

The two conventions answer every "`≤ n`" query (for `n : ℕ`) identically
(`projectiveDimension_le_iff`), and differ only at the bottom: `raw = ⊥` versus `book = 0` on the
zero module. In particular all finite-dimension results transfer unchanged.
-/

universe u

open CategoryTheory

/-- The raw Mathlib projective dimension of a module, `CategoryTheory.projectiveDimension`
applied to the corresponding object of `ModuleCat R`. Returns a value in `WithBot ℕ∞`: `⊥` if
`M` is zero, a natural number for the finite case, or `⊤` if no finite projective resolution
exists. This is the internal value; the book-faithful `Etingof.projectiveDimension` normalizes
the zero-module edge case to `0`. -/
noncomputable def Etingof.projectiveDimensionRaw
    (R : Type u) [Ring R] (M : ModuleCat.{u} R) : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension M

/-- The projective dimension of a module, in the sense of Etingof Definition 9.4.1: the length of
the shortest finite projective resolution, with the book convention that every projective module
-- including the zero module -- has projective dimension `0`.

Concretely this is `max 0 (Etingof.projectiveDimensionRaw R M)`, which coincides with the raw
Mathlib value on every nonzero module and normalizes the zero module's value from `⊥` to `0`
(see `Etingof.projectiveDimension_eq_zero_iff`). -/
noncomputable def Etingof.projectiveDimension
    (R : Type u) [Ring R] (M : ModuleCat.{u} R) : WithBot ℕ∞ :=
  max 0 (Etingof.projectiveDimensionRaw R M)

namespace Etingof

variable {R : Type u} [Ring R]

/-- The book projective dimension is nonnegative: it never takes the value `⊥`. -/
lemma zero_le_projectiveDimension (M : ModuleCat.{u} R) :
    (0 : WithBot ℕ∞) ≤ Etingof.projectiveDimension R M :=
  le_max_left _ _

/-- The raw Mathlib projective dimension of a nonzero module is nonnegative. -/
lemma zero_le_projectiveDimensionRaw_of_not_isZero (M : ModuleCat.{u} R)
    (hM : ¬ Limits.IsZero M) : (0 : WithBot ℕ∞) ≤ Etingof.projectiveDimensionRaw R M := by
  have h : Etingof.projectiveDimensionRaw R M ≠ ⊥ := by
    rw [Etingof.projectiveDimensionRaw, Ne, CategoryTheory.projectiveDimension_eq_bot_iff]
    exact hM
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.1 h
  calc (0 : WithBot ℕ∞) = ((0 : ℕ∞) : WithBot ℕ∞) := by rw [WithBot.coe_zero]
    _ ≤ (b : WithBot ℕ∞) := WithBot.coe_le_coe.2 zero_le
    _ = Etingof.projectiveDimensionRaw R M := hb

/-- The book and raw projective dimensions answer every finite `≤ n` query identically:
`pd M ≤ n ↔ HasProjectiveDimensionLE M n` for `n : ℕ`. -/
lemma projectiveDimension_le_iff (M : ModuleCat.{u} R) (n : ℕ) :
    Etingof.projectiveDimension R M ≤ (n : WithBot ℕ∞) ↔ HasProjectiveDimensionLE M n := by
  simp only [Etingof.projectiveDimension, Etingof.projectiveDimensionRaw, max_le_iff]
  rw [CategoryTheory.projectiveDimension_le_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  calc (0 : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) := by rw [Nat.cast_zero]
    _ ≤ (n : WithBot ℕ∞) := by exact_mod_cast Nat.zero_le n

/-- **Book characterization of projective dimension zero.** A module has projective dimension `0`
in the book's sense exactly when it is projective. Unlike the raw Mathlib
`projectiveDimension_eq_zero_iff` (which excludes the zero module), this includes `M = 0`. -/
lemma projectiveDimension_eq_zero_iff (M : ModuleCat.{u} R) :
    Etingof.projectiveDimension R M = 0 ↔ Projective M := by
  rw [le_antisymm_iff, and_iff_left (zero_le_projectiveDimension M)]
  rw [show (0 : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) from by rw [Nat.cast_zero],
    projectiveDimension_le_iff, ← projective_iff_hasProjectiveDimensionLE_zero]

/-- The zero module has book projective dimension `0`, matching the source (a projective module
has projective dimension `0`). Under the raw Mathlib convention it is `⊥`. -/
lemma projectiveDimension_eq_zero_of_isZero (M : ModuleCat.{u} R) (hM : Limits.IsZero M) :
    Etingof.projectiveDimension R M = 0 :=
  (projectiveDimension_eq_zero_iff M).2 hM.projective

/-- On a nonzero module the book projective dimension coincides with the raw Mathlib value; the
two conventions differ only on the zero module. -/
lemma projectiveDimension_eq_raw_of_not_isZero (M : ModuleCat.{u} R) (hM : ¬ Limits.IsZero M) :
    Etingof.projectiveDimension R M = Etingof.projectiveDimensionRaw R M := by
  rw [Etingof.projectiveDimension, max_eq_right (zero_le_projectiveDimensionRaw_of_not_isZero M hM)]

end Etingof
