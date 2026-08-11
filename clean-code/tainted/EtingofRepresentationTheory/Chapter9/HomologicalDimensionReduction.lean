import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Data.ENat.Lattice

/-!
# Reduction lemma for infinite homological dimension

A small reusable reduction: the homological dimension of a ring `R` (Definition 9.4.3)
equals `⊤` as soon as `R` fails to have homological dimension `≤ d` for *every* `d`.

This is the packaging step used by the "infinite homological dimension" computations of
Problem 9.4.5 (ii): one exhibits, for each `d`, a module of projective dimension `> d`
(so `HasHomologicalDimensionLE R d` fails), and this lemma converts that into the
statement `homologicalDimension R = ⊤`.
-/

universe u

namespace Etingof

/-- If a ring has homological dimension `≤ d` for no `d`, its homological dimension is `⊤`.

`homologicalDimension R = ⨅ (d) (_ : HasHomologicalDimensionLE R d), (d : ℕ∞)`; under the
hypothesis every inner infimum is over a false proposition, hence `⊤` (`iInf_neg`), and
`⨅ d, ⊤ = ⊤` (`iInf_top`). -/
theorem homologicalDimension_eq_top {R : Type u} [Ring R]
    (h : ∀ d : ℕ, ¬ Etingof.HasHomologicalDimensionLE R d) :
    Etingof.homologicalDimension R = ⊤ := by
  unfold Etingof.homologicalDimension
  have hd : ∀ d : ℕ,
      (⨅ (_ : Etingof.HasHomologicalDimensionLE R d), (d : ℕ∞)) = ⊤ := fun d => iInf_neg (h d)
  simp_rw [hd]
  exact iInf_top

/-- If a ring has homological dimension `≤ d`, then its homological dimension (as an element
of `ℕ∞`) is `≤ d`.

`homologicalDimension R = ⨅ (d) (_ : HasHomologicalDimensionLE R d), (d : ℕ∞)`; the term at
this particular `d`, whose hypothesis `h` holds, bounds the infimum from below. -/
theorem homologicalDimension_le {R : Type u} [Ring R] {d : ℕ}
    (h : Etingof.HasHomologicalDimensionLE R d) :
    Etingof.homologicalDimension R ≤ (d : ℕ∞) := by
  unfold Etingof.homologicalDimension
  exact iInf₂_le d h

/-- A ring with homological dimension `≤ 1` but not `≤ 0` has homological dimension exactly `1`.

The upper bound `≤ 1` is `homologicalDimension_le h1`. For the lower bound `1 ≤ …`, bound the
infimum termwise (`le_iInf₂`): for each `d` with `HasHomologicalDimensionLE R d`, the `d = 0`
case contradicts `h0`, and every `d ≥ 1` gives `(d : ℕ∞) ≥ 1`. -/
theorem homologicalDimension_eq_one_of_not_le_zero {R : Type u} [Ring R]
    (h1 : Etingof.HasHomologicalDimensionLE R 1)
    (h0 : ¬ Etingof.HasHomologicalDimensionLE R 0) :
    Etingof.homologicalDimension R = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using homologicalDimension_le h1
  · unfold Etingof.homologicalDimension
    refine le_iInf₂ (fun d hd => ?_)
    match d with
    | 0 => exact absurd hd h0
    | (n + 1) => exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

end Etingof
