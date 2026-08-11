import EtingofRepresentationTheory.Chapter6.Example6_4_9_Shared
import EtingofRepresentationTheory.Chapter6.Example6_4_9_EType
import EtingofRepresentationTheory.Chapter6.Example6_4_9_An
import EtingofRepresentationTheory.Chapter6.Example6_4_9_An_Lattice
import EtingofRepresentationTheory.Chapter6.Example6_4_9_Dn

/-!
# Example 6.4.9: Root Counts for Dynkin Diagrams

This file re-exports the root count results for all Dynkin types:
- `Etingof.Example_6_4_9_E6`: E₆ has 36 positive roots
- `Etingof.Example_6_4_9_E7`: E₇ has 63 positive roots
- `Etingof.Example_6_4_9_E8`: E₈ has 120 positive roots
- `Etingof.Example_6_4_9_An`: Aₙ has n(n+1)/2 positive roots
- `Etingof.Example_6_4_9_Dn`: Dₙ has n(n-1) positive roots

The proofs are split across files by Dynkin type:
- `Example6_4_9_Shared`: shared infrastructure (positiveRoots, rootCountFinset)
- `Example6_4_9_EType`: E₆, E₇, E₈ via SOS bounds + branch-decomposition `decide`
- `Example6_4_9_An`: Aₙ via interval indicator bijection
- `Example6_4_9_An_Lattice`: the explicit `A_{N-1}` sum-zero lattice model in `ℤ^N`
  (`Etingof.An.sumZeroLattice`), its consecutive-difference basis (`Etingof.An.basis`),
  the isometry with the Cartan form (`Etingof.An.dotProduct_toLat`), the classification of
  all roots as `±(e_i - e_j)` (`Etingof.An.mem_latticeRoots_iff`), and the reconnected
  positive-root count (`Etingof.An.ncard_positiveLatticeRoots`)
- `Example6_4_9_Dn`: Dₙ via quadratic form peeling induction
-/
