import Mathlib

/-!
# Definition 5.4.1: Solvable Group

A group G is **solvable** if there exists a chain of subgroups
  {e} = G₁ ⊲ G₂ ⊲ ... ⊲ Gₙ = G
such that each quotient Gᵢ₊₁/Gᵢ is abelian.

Equivalently, the derived series G ⊃ [G,G] ⊃ [[G,G],[G,G]] ⊃ ... terminates at {e}.

## Mathlib correspondence

Exact match: `IsSolvable G` in Mathlib, defined via the derived series.
-/

namespace Etingof

/-- A finite abelian series, indexed downwards from `G` to the trivial subgroup.

The inclusions make this a nested series.  The commutator condition says precisely that each
successive quotient is abelian; see `abelianSeries_step_quotient_commutative`. -/
def HasAbelianSeries (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, ∃ H : ℕ → Subgroup G,
    H 0 = ⊤ ∧ H n = ⊥ ∧
      ∀ i : ℕ, i < n → H (i + 1) ≤ H i ∧ ⁅H i, H i⁆ ≤ H (i + 1)

/-- The commutator condition makes the intersection of the next subgroup with the preceding one
normal in the latter.  For a nested series this intersection is the next subgroup itself. -/
theorem abelianSeries_step_normal {G : Type*} [Group G] (H : ℕ → Subgroup G) (i : ℕ)
    (hcomm : ⁅H i, H i⁆ ≤ H (i + 1)) :
    ((H (i + 1)).comap (H i).subtype).Normal := by
  apply Subgroup.Normal.of_commutator_le
  apply Subgroup.map_le_iff_le_comap.mp
  rwa [(H i).map_subtype_commutator]

/-- Commutativity of a successive quotient is equivalent to the commutator containment used in
`HasAbelianSeries`, matching the quotient condition in the book's definition. -/
theorem abelianSeries_step_quotient_commutative_iff {G : Type*} [Group G]
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

/-- The book's finite-series definition of solvability is equivalent to Mathlib's derived-series
definition. (Etingof Definition 5.4.1) -/
theorem hasAbelianSeries_iff_isSolvable {G : Type*} [Group G] :
    HasAbelianSeries G ↔ IsSolvable G := by
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

end Etingof

/-- A group G is solvable iff its derived series terminates at the trivial subgroup.
This is `IsSolvable G` in Mathlib. (Etingof Definition 5.4.1)

Example: S₃ is solvable with chain {e} ⊲ A₃ ⊲ S₃. -/
example : IsSolvable (Equiv.Perm (Fin 3)) := by
  -- S₃ is solvable with derived series S₃ ⊃ A₃ ⊃ {e}.
  -- A₃ is commutative (order 3, cyclic), hence solvable.
  haveI : IsSolvable (alternatingGroup (Fin 3)) := by
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI := isCyclic_of_prime_card hcard
    -- v4.30: `mul_comm` on `A₃` needs a `CommGroup` instance; derive it from cyclicity.
    letI := IsCyclic.commGroup (α := alternatingGroup (Fin 3))
    exact isSolvable_of_comm (fun a b => mul_comm a b)
  exact solvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype
    (Equiv.Perm.sign)
    (by rw [← alternatingGroup_eq_sign_ker]; exact fun x hx => ⟨⟨x, hx⟩, rfl⟩)
