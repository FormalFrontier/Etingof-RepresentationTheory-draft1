import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Golden

/-!
# Problem 5.11.1: induced representations of `A₅`

**Problem 5.11.1.** Compute the decomposition into irreducibles of all the representations of
`A₅` induced from the irreducible representations of

(a) `ℤ₂`; (b) `ℤ₃`; (c) `ℤ₅`; (d) `A₄`; (e) `ℤ₂ × ℤ₂`.

## Formalization

`A₅ = ↥(alternatingGroup (Fin 5))` has five irreducible complex representations, of dimensions
`1, 3, 3', 4, 5`; they are the catalogue
`{repTriv, repC3plus, repC3minus, repC4, repC5}` built in `Etingof.Example4_8_1.A5` (the two
`3`-dimensional ones `repC3plus`, `repC3minus` are the golden-ratio icosahedral
representations, non-isomorphic). Its character table on the five classes
`(1a, 2a, 3a, 5a, 5b)` (sizes `1, 15, 20, 12, 12`) is

| | `1a` | `2a` | `3a` | `5a` | `5b` |
|---|---|---|---|---|---|
| `1`  | `1` | `1`  | `1`  | `1`     | `1`     |
| `3`  | `3` | `-1` | `0`  | `φ`     | `φ'`    |
| `3'` | `3` | `-1` | `0`  | `φ'`    | `φ`     |
| `4`  | `4` | `0`  | `1`  | `-1`    | `-1`    |
| `5`  | `5` | `1`  | `-1` | `0`     | `0`     |

with `φ = (1+√5)/2`, `φ' = (1-√5)/2`.

Each induced representation is decomposed via **Frobenius reciprocity** (Theorem 5.9.1): the
multiplicity of an irreducible `W` of `A₅` in `Ind_H^G ρ` equals the inner product
`⟨Res_H χ_W, χ_ρ⟩_H`. Because every subgroup of a given order in the list is unique up to
conjugacy in `A₅` — all involutions are conjugate (one class `2a`), all Sylow-`3` and Sylow-`5`
subgroups are conjugate, the order-`4` subgroups are the (conjugate) Klein four Sylow-`2`
subgroups `ℤ₂ × ℤ₂` (`A₅` has no element of order `4`), and the order-`12` subgroups are the
(conjugate) point stabilisers `A₄` — the decomposition depends only on the order of `H` and the
isomorphism class of the inducing character `ρ`, not on the particular subgroup chosen. We
therefore phrase each statement for an arbitrary subgroup `H` of the relevant order, and an
arbitrary irreducible `ρ` of `H` distinguished by dimension and (for one-dimensional `ρ`)
triviality of its character.

The resulting decompositions (dimensions in parentheses; `[G:H]·dim ρ` on the right):

* **(a) `H = ℤ₂`** (`|H| = 2`, index `30`), two irreducibles `1₊, 1₋`:
  * `Ind 1₊ ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³` (`30`) — the coset/edge permutation representation;
  * `Ind 1₋ ≅ 3² ⊕ 3'² ⊕ 4² ⊕ 5²` (`30`).
* **(b) `H = ℤ₃`** (`|H| = 3`, index `20`), irreducibles `1, ω, ω²`:
  * `Ind 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5` (`20`) — the coset/face permutation representation;
  * `Ind ω ≅ Ind ω² ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5²` (`20`).
* **(c) `H = ℤ₅`** (`|H| = 5`, index `12`), irreducibles `1, ζ, ζ², ζ³, ζ⁴`:
  * `Ind 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 5` (`12`) — the coset/vertex permutation representation;
  * each nontrivial `Ind ζ^k ≅ 3 ⊕ 4 ⊕ 5` or `≅ 3' ⊕ 4 ⊕ 5` (`12`) — the pair `{ζ, ζ⁴}`
    yields one of the two `3`-dimensionals and `{ζ², ζ³}` the other (the split matches the two
    classes `5a, 5b` of `5`-cycles inside `ℤ₅`), so we state the nontrivial case as a
    disjunction over the two `3`-dimensionals.
* **(d) `H = A₄`** (`|H| = 12`, index `5`), irreducibles `1, ω, ω², 3_{A₄}`:
  * `Ind 1 ≅ 1 ⊕ 4` (`5`) — the coset/`5`-point permutation representation;
  * `Ind ω ≅ Ind ω² ≅ 5` (`5`);
  * `Ind 3_{A₄} ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5` (`15`).
* **(e) `H = ℤ₂ × ℤ₂`** (`|H| = 4`, index `15`), four irreducibles `1, χ₁, χ₂, χ₃`:
  * `Ind 1 ≅ 1 ⊕ 4 ⊕ 5²` (`15`) — the coset permutation representation;
  * each nontrivial `Ind χᵢ ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5` (`15`).

Statement pass: every decomposition is stated as `Nonempty (Ind_H^G ρ ≅ ⊞ …)` in `FDRep ℂ A₅`,
with `sorry` proofs. `Ind_H^G` is `Etingof.Definition5_8_1`; the target biproducts use the
catalogue objects `repTriv, repC3plus, repC3minus, repC4, repC5`.
-/

open CategoryTheory Etingof.Example4_8_1.A5

noncomputable section

namespace Etingof.Problem5_11_1

/-- `A₅`, the alternating group on five letters, as the underlying group of the catalogue. -/
abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

/-- The representation of `A₅` induced from an irreducible `σ : FDRep ℂ ↥H` of a subgroup
`H ≤ A₅`, packaged as an object of `FDRep ℂ A₅` via `Etingof.Definition5_8_1`. -/
abbrev ind {H : Subgroup A5} (σ : FDRep ℂ ↥H) : FDRep ℂ A5 :=
  FDRep.of (Etingof.Definition5_8_1 H σ.ρ)

/-! ## (a) Induction from `ℤ₂` -/

/-- **(a) trivial character.** `Ind_{ℤ₂}^{A₅} 1₊ ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³` (dimension `30`), the
permutation representation on the `30` cosets. Multiplicities `(χ_W(1a) + χ_W(2a))/2`. -/
theorem indZ2_triv (H : Subgroup A5) (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅
      repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5 ⊞ repC5) := by
  sorry

/-- **(a) sign character.** `Ind_{ℤ₂}^{A₅} 1₋ ≅ 3² ⊕ 3'² ⊕ 4² ⊕ 5²` (dimension `30`).
Multiplicities `(χ_W(1a) − χ_W(2a))/2`. -/
theorem indZ2_sign (H : Subgroup A5) (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅
      repC3plus ⊞ repC3plus ⊞ repC3minus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  sorry

/-! ## (b) Induction from `ℤ₃` -/

/-- **(b) trivial character.** `Ind_{ℤ₃}^{A₅} 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5` (dimension `20`), the
permutation representation on the `20` cosets. Multiplicities `(χ_W(1a) + 2·χ_W(3a))/3`. -/
theorem indZ3_triv (H : Subgroup A5) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5) := by
  sorry

/-- **(b) nontrivial character.** For either nontrivial character `ω, ω²`,
`Ind_{ℤ₃}^{A₅} ω ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5²` (dimension `20`). -/
theorem indZ3_nontriv (H : Subgroup A5) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  sorry

/-! ## (c) Induction from `ℤ₅` -/

/-- **(c) trivial character.** `Ind_{ℤ₅}^{A₅} 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 5` (dimension `12`), the
permutation representation on the `12` cosets. Multiplicities `(χ_W(1a) + 2·χ_W(5a) +
2·χ_W(5b))/5`. -/
theorem indZ5_triv (H : Subgroup A5) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC5) := by
  sorry

/-- **(c) nontrivial character.** For any of the four nontrivial characters `ζ^k` (`k ≠ 0`),
`Ind_{ℤ₅}^{A₅} ζ^k` is `3 ⊕ 4 ⊕ 5` or `3' ⊕ 4 ⊕ 5` (dimension `12`); the pair `{ζ, ζ⁴}` picks
one `3`-dimensional and `{ζ², ζ³}` the other. -/
theorem indZ5_nontriv (H : Subgroup A5) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC4 ⊞ repC5) ∨
      Nonempty (ind σ ≅ repC3minus ⊞ repC4 ⊞ repC5) := by
  sorry

/-! ## (d) Induction from `A₄` -/

/-- **(d) trivial character.** `Ind_{A₄}^{A₅} 1 ≅ 1 ⊕ 4` (dimension `5`), the permutation
representation on the `5` cosets. -/
theorem indA4_triv (H : Subgroup A5) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 1)
    (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC4) := by
  sorry

/-- **(d) nontrivial linear character.** For either nontrivial one-dimensional character
`ω, ω²` of `A₄`, `Ind_{A₄}^{A₅} ω ≅ 5` (dimension `5`). -/
theorem indA4_nontriv_linear (H : Subgroup A5) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 1)
    (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC5) := by
  sorry

/-- **(d) three-dimensional character.** `Ind_{A₄}^{A₅} 3_{A₄} ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5`
(dimension `15`). -/
theorem indA4_threeDim (H : Subgroup A5) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 3) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5) := by
  sorry

/-! ## (e) Induction from `ℤ₂ × ℤ₂` -/

/-- **(e) trivial character.** `Ind_{ℤ₂×ℤ₂}^{A₅} 1 ≅ 1 ⊕ 4 ⊕ 5²` (dimension `15`), the
permutation representation on the `15` cosets. -/
theorem indV4_triv (H : Subgroup A5) (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  sorry

/-- **(e) nontrivial character.** For any of the three nontrivial characters `χ₁, χ₂, χ₃` of
`ℤ₂ × ℤ₂`, `Ind_{ℤ₂×ℤ₂}^{A₅} χᵢ ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5` (dimension `15`). -/
theorem indV4_nontriv (H : Subgroup A5) (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5) := by
  sorry

end Etingof.Problem5_11_1
