/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.SolvableGroups.Series

/-- An auxiliary property of groups. -/
@[source_ref "Chapter5/Definition5.4.1" (role := supporting)]
def Auxiliary (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, ∃ H : ℕ → Subgroup G,
    H 0 = ⊤ ∧ H n = ⊥ ∧
      ∀ i : ℕ, i < n → H (i + 1) ≤ H i ∧ ⁅H i, H i⁆ ≤ H (i + 1)

/-- The pullback of the next subgroup to the current subgroup is normal when the current subgroup brackets into the next one. -/
@[source_ref "Chapter5/Definition5.4.1" (role := supporting)]
theorem normal_comap_of_bracket_le {G : Type*} [Group G] (H : ℕ → Subgroup G) (i : ℕ)
    (hcomm : ⁅H i, H i⁆ ≤ H (i + 1)) :
    ((H (i + 1)).comap (H i).subtype).Normal := by
  apply Subgroup.Normal.of_commutator_le
  apply Subgroup.map_le_iff_le_comap.mp
  rwa [(H i).map_subtype_commutator]

/-- The quotient of one subgroup by the pullback of the next is commutative exactly when the subgroup brackets into the next one. -/
@[source_ref "Chapter5/Definition5.4.1" (role := supporting)]
theorem quotient_isMulCommutative_iff_bracket_le {G : Type*} [Group G]
    (H : ℕ → Subgroup G) (i : ℕ)
    [((H (i + 1)).comap (H i).subtype).Normal]
    : IsMulCommutative ((H i) ⧸ (H (i + 1)).comap (H i).subtype) ↔
      ⁅H i, H i⁆ ≤ H (i + 1) := by
  constructor
  · intro hquot
    rw [← (H i).map_subtype_commutator]
    apply Subgroup.map_le_iff_le_comap.mpr
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquot
  · intro hcomm
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    apply Subgroup.map_le_iff_le_comap.mp
    rwa [(H i).map_subtype_commutator]

/-- The auxiliary group property is equivalent to solvability. -/
@[source_ref "Chapter5/Definition5.4.1" (role := supporting)]
theorem auxiliary_iff_isSolvable {G : Type*} [Group G] :
    Auxiliary G ↔ IsSolvable G := by
  constructor
  · rintro ⟨n, H, htop, hbot, hstep⟩
    refine ⟨⟨n, le_antisymm ?_ bot_le⟩⟩
    have hderived : ∀ i : ℕ, i ≤ n → derivedSeries G i ≤ H i := by
      intro i hi
      induction i with
      | zero => simp [htop]
      | succ i ih =>
          rw [derivedSeries_succ]
          exact (Subgroup.commutator_mono (ih (Nat.le_trans (Nat.le_succ i) hi))
            (ih (Nat.le_trans (Nat.le_succ i) hi))).trans
              (hstep i (Nat.lt_of_succ_le hi)).2
    exact (hderived n le_rfl).trans hbot.le
  · intro hsolvable
    obtain ⟨n, hn⟩ := hsolvable.solvable
    refine ⟨n, derivedSeries G, derivedSeries_zero G, hn, ?_⟩
    intro i _
    refine ⟨derivedSeries_antitone G (Nat.le_succ i), ?_⟩
    rw [derivedSeries_succ]

end RepresentationTheory.SolvableGroups.Series

example : IsSolvable (Equiv.Perm (Fin 3)) := by
  haveI : IsSolvable (alternatingGroup (Fin 3)) := by
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI := isCyclic_of_prime_card hcard
    letI := IsCyclic.commGroup (α := alternatingGroup (Fin 3))
    exact isSolvable_of_comm (fun a b => mul_comm a b)
  exact solvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype
    (Equiv.Perm.sign)
    (by rw [← alternatingGroup_eq_sign_ker]; exact fun x hx => ⟨⟨x, hx⟩, rfl⟩)
