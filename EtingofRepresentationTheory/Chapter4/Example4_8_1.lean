import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Golden

/-!
# Example 4.8.1: Character Tables of `Q₈`, `S₄`, and `A₅`

The example states three full character tables.  The genuine content is the table of
character values together with the assertion that these rows really are *the* irreducible
characters of each group.

| `Q₈` | `1` | `-1` | `i` | `j` | `k` |
|---|---|---|---|---|---|
| `#` | 1 | 1 | 2 | 2 | 2 |
| `ℂ₊₊` | 1 | 1 | 1 | 1 | 1 |
| `ℂ₊₋` | 1 | 1 | 1 | -1 | -1 |
| `ℂ₋₊` | 1 | 1 | -1 | 1 | -1 |
| `ℂ₋₋` | 1 | 1 | -1 | -1 | 1 |
| `ℂ²` | 2 | -2 | 0 | 0 | 0 |

| `S₄` | `Id` | `(12)` | `(12)(34)` | `(123)` | `(1234)` |
|---|---|---|---|---|---|
| `#` | 1 | 6 | 3 | 8 | 6 |
| `ℂ₊` | 1 | 1 | 1 | 1 | 1 |
| `ℂ₋` | 1 | -1 | 1 | 1 | -1 |
| `ℂ²` | 2 | 0 | 2 | -1 | 0 |
| `ℂ³₊` | 3 | -1 | -1 | 0 | 1 |
| `ℂ³₋` | 3 | 1 | -1 | 0 | -1 |

| `A₅` | `Id` | `(123)` | `(12)(34)` | `(12345)` | `(13245)` |
|---|---|---|---|---|---|
| `#` | 1 | 20 | 15 | 12 | 12 |
| `ℂ` | 1 | 1 | 1 | 1 | 1 |
| `ℂ³₊` | 3 | 0 | -1 | `(1+√5)/2` | `(1-√5)/2` |
| `ℂ³₋` | 3 | 0 | -1 | `(1-√5)/2` | `(1+√5)/2` |
| `ℂ⁴` | 4 | 1 | 0 | -1 | -1 |
| `ℂ⁵` | 5 | -1 | 1 | 0 | 0 |

## Formalization strategy

We encode each table verbatim as an explicit class function and prove the rows are
**orthonormal** with respect to the class-size-weighted inner product
`⟪f, g⟫ = (1/|G|) Σ_c |class c| · f(c) · g(c)`.  Orthonormality of `r` class functions,
combined with the fact that the group has exactly `r` conjugacy classes (proved below for
`Q₈`, `S₄`, `A₅`), certifies that the tabulated functions are precisely the complete set of
distinct irreducible characters — i.e. that the table is correct and complete.  This is the
same certificate used for the character tables in Example 4.9.1.

The `A₅` values involve the golden ratio `(1 ± √5)/2`, so all character values are carried
in the ring `Q5 = ℚ[√5]` (`re + im·√5`); the `Q₈` and `S₄` values are rational (`im = 0`).

## Mathlib correspondence

Character tables for these groups are not in Mathlib; they are built here from scratch.
The dimension data is pinned down via the conjugacy-class counts and the sum-of-squares
formula `∑ dᵢ² = |G|`.
-/

/-! ## Underlying combinatorial data

The conjugacy-class counts pin down the *number* of irreducibles (= number of rows above),
and the orders pin down their dimensions via `∑ dᵢ² = |G|`. -/

/-- `Q₈` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiQ8`). (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_conj_classes :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  decide

/-- `Q₈` has order 8.  Combined with 5 conjugacy classes and the sum-of-squares formula
`∑ dᵢ² = |G|`, the only solution is dimensions 1,1,1,1,2. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_card :
    Fintype.card (QuaternionGroup 2) = 8 := by
  rw [QuaternionGroup.card]

/-- The five genuine irreducible representations of `Q₈`, indexed `0..4` as
`ℂ₊₊, ℂ₊₋, ℂ₋₊, ℂ₋₋, ℂ²`. -/
noncomputable def Etingof.Example4_8_1_Q8_irrep :
    Fin 5 → FDRep ℂ (QuaternionGroup 2) := Etingof.Example4_8_1.Q8.irrep

/-- Each of the five `Q₈` representations is simple (irreducible), proved via the
norm-one character criterion `FDRep.simple_iff_char_is_norm_one` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_simple (i : Fin 5) :
    CategoryTheory.Simple (Etingof.Example4_8_1_Q8_irrep i) :=
  Etingof.Example4_8_1.Q8.irrep_simple i

/-- The character (trace) of the `i`-th `Q₈` representation at the `j`-th class
representative `(1, -1, i, j, k)` equals the tabulated value `chiQ8 i j` — including
`χ_{ℂ²}(-1) = -2`.  This connects every row of the table to an actual representation.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_character (i j : Fin 5) :
    (Etingof.Example4_8_1_Q8_irrep i).character (Etingof.Example4_8_1.Q8.classRep j)
      = Etingof.Example4_8_1.Q5toC (Etingof.Example4_8_1.chiQ8 i j) :=
  Etingof.Example4_8_1.Q8.irrep_character i j

/-- The five `Q₈` representations are pairwise non-isomorphic (their characters differ).
Five distinct simples together with five conjugacy classes exhibit the complete character
table. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_pairwise (i j : Fin 5) (hij : i ≠ j) :
    ¬ Nonempty (Etingof.Example4_8_1_Q8_irrep i ≅ Etingof.Example4_8_1_Q8_irrep j) :=
  Etingof.Example4_8_1.Q8.irrep_pairwise i j hij

set_option maxRecDepth 4000 in
/-- `S₄` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiS4`).  Proved by honest `decide` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 := by
  decide

/-- `S₄` has order 24.  Combined with 5 conjugacy classes and `∑ dᵢ² = |G|`, the dimensions
are 1,1,2,3,3.  Proved from `Fintype.card_perm` (`= 4!`), no `native_decide`.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_card :
    Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Fintype.card_perm, Fintype.card_fin]; decide

/-- The five genuine irreducible representations of `S₄`, indexed `0..4` as
`ℂ₊, ℂ₋, ℂ², ℂ³₊, ℂ³₋`. -/
noncomputable def Etingof.Example4_8_1_S4_irrep :
    Fin 5 → FDRep ℂ (Equiv.Perm (Fin 4)) := Etingof.Example4_8_1.S4.irrepS4

/-- Each of the five `S₄` representations is simple (irreducible), proved via the
norm-one character criterion `FDRep.simple_iff_char_is_norm_one` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_simple (i : Fin 5) :
    CategoryTheory.Simple (Etingof.Example4_8_1_S4_irrep i) :=
  Etingof.Example4_8_1.S4.irrepS4_simple i

/-- The character (trace) of the `i`-th `S₄` representation at the `j`-th class
representative `(Id, (12), (12)(34), (123), (1234))` equals the tabulated value
`chiS4 i j`.  This connects every row of the table to an actual representation.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_character (i j : Fin 5) :
    (Etingof.Example4_8_1_S4_irrep i).character (Etingof.Example4_8_1.S4.classRepS4 j)
      = Etingof.Example4_8_1.Q5toC (Etingof.Example4_8_1.chiS4 i j) :=
  Etingof.Example4_8_1.S4.irrepS4_character_book i j

/-- The five `S₄` representations are pairwise non-isomorphic (their characters differ).
Five distinct simples together with five conjugacy classes exhibit the complete character
table. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_pairwise (i j : Fin 5) (hij : i ≠ j) :
    ¬ Nonempty (Etingof.Example4_8_1_S4_irrep i ≅ Etingof.Example4_8_1_S4_irrep j) :=
  Etingof.Example4_8_1.S4.irrepS4_pairwise i j hij

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the `ConjClasses` quotient of the 60-element group A₅; no `native_decide`
/-- `A₅` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiA5`).  Proved by honest `decide` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_conj_classes :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 := by
  decide

/-- `A₅` has order 60.  Combined with 5 conjugacy classes and `∑ dᵢ² = |G|`, the dimensions
are 1,3,3,4,5.  Proved from `card_alternatingGroup` (`= 5!/2`), no `native_decide`.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_card :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide

/-- The five genuine irreducible `A₅` representations, indexed `0..4` as `ℂ, ℂ³₊, ℂ³₋, ℂ⁴, ℂ⁵`
(the five rows of `chiA5`, in order). -/
noncomputable def Etingof.Example4_8_1_A5_irrep :
    Fin 5 → FDRep ℂ (alternatingGroup (Fin 5)) := Etingof.Example4_8_1.A5.irrepA5

