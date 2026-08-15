/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.YoungDiagram.PartitionFormulas

namespace RepresentationTheory.PartitionFinrank

noncomputable section

/-- The finrank of the partition-indexed subtype equals the cardinality of an auxiliary type. -/
theorem finrank_eq_card_auxiliaryType (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) =
      Nat.card
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource
          n la) :=
  RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card n la

/-- The finrank of the partition-indexed subtype equals the factorial divided by its Young diagram hook-length product. -/
theorem finrank_eq_factorial_div_hookLengthProduct (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) =
      n.factorial /
        RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic
          (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition
            la) := by
  rw [finrank_eq_card_auxiliaryType,
    RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct]

end

end RepresentationTheory.PartitionFinrank
