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

end Etingof
