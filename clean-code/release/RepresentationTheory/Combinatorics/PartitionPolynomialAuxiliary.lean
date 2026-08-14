import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.SymmetricPolynomials.Alternant
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

set_option linter.style.longLine false

open MvPolynomial Finset

noncomputable section

namespace RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary

/-- Associates to each natural number a partition of that number. -/
def partitionChoice (n : ℕ) : Nat.Partition n where
  parts := Multiset.replicate n 1
  parts_pos hi := by
    rw [Multiset.mem_replicate] at hi; omega
  parts_sum := by
    rw [Multiset.sum_replicate]; simp

/-- Applying `MvPolynomial.psumPart` to the selected partition gives the corresponding power of the sum of all variables. -/
@[source_ref"Chapter5/Discussion_hook_length_derivation"(role:=supporting)]
theorem psumPart_partitionChoice_eq_sum_variables_pow (N n : ℕ) :
    MvPolynomial.psumPart (Fin N) ℚ (partitionChoice n) =
      (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n := by
  unfold MvPolynomial.psumPart
  change (Multiset.map (MvPolynomial.psum (Fin N) ℚ) (Multiset.replicate n 1)).prod = _
  rw [Multiset.map_replicate, Multiset.prod_replicate, MvPolynomial.psum_one]

/-- The power of the sum of all variables is a finite sum of auxiliary terms scaled by the indicated values. -/
theorem sum_variables_pow_eq_sum_auxiliary_smul (N n : ℕ) :
    (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n =
      ∑ lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n,
        RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (partitionChoice n) •
          RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam.parts := by
  rw [← psumPart_partitionChoice_eq_sum_variables_pow N n]
  exact RepresentationTheory.SymmetricPolynomials.Alternant.psumPart_expansion N (partitionChoice n)

/-- The auxiliary value at one agrees with the selected partition for every natural number. -/
theorem auxiliaryAtOne_eq_partitionChoice (n : ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType (1 : Equiv.Perm (Fin n)) = partitionChoice n := by
  apply Nat.Partition.ext
  change RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset n 1 = Multiset.replicate n 1
  unfold RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset
  rw [Equiv.Perm.cycleType_one, Equiv.Perm.support_one,
    Finset.card_empty, Nat.sub_zero, zero_add]

/-- The auxiliary construction evaluated at one equals the natural-number cast of the finrank of the displayed Complex subtype. -/
theorem auxiliaryAtOne_eq_finrank (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la 1 =
      (Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) : ℂ) := by
  unfold RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue
  rw [show (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la 1) =
        (1 : Module.End ℂ ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)) from
        map_one (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la),
      LinearMap.trace_one]

/-- The rational cast of the auxiliary value equals the natural-number cast of the finrank of the displayed Complex subtype. -/
theorem ratCastAuxiliaryValue_eq_finrank
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (partitionChoice n) : ℂ) =
      (Module.finrank ℂ
        (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n
          (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℂ) := by
  rw [← auxiliaryAtOne_eq_partitionChoice n,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.Auxiliary.cast_characterValue_eq N n lam 1,
      auxiliaryAtOne_eq_finrank]

/-- The auxiliary value equals the natural-number cast of the finrank of the displayed Complex subtype. -/
theorem auxiliaryValue_eq_finrank
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (partitionChoice n) =
      (Module.finrank ℂ
        (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n
          (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) := by
  apply (Rat.cast_injective (α := ℂ))
  rw [Rat.cast_natCast]
  exact ratCastAuxiliaryValue_eq_finrank N lam

/-- The power of the sum of all variables is a finite sum whose coefficients are natural-number casts of finranks of the displayed Complex subtypes. -/
theorem sum_variables_pow_eq_sum_finrank_smul (N n : ℕ) :
    (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n =
      ∑ lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n,
        (Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n
          (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) •
        RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam.parts := by
  rw [sum_variables_pow_eq_sum_auxiliary_smul]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [auxiliaryValue_eq_finrank]

end RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary
