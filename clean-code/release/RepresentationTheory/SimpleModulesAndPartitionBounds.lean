/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Group.SimpleRepresentations
import RepresentationTheory.PartitionMonoidAlgebra
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich

set_option linter.style.openClassical false

namespace RepresentationTheory.SimpleModulesAndPartitionBounds

noncomputable section
open scoped Classical

open RepresentationTheory.FDRep.GroupAlgebraDecomposition
open RepresentationTheory.Group.SimpleRepresentations
open RepresentationTheory.PartitionMonoidAlgebra
open RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich
open RepresentationTheory.GeneralLinearGroup.WeightCharacter

universe u w

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev A' (n : ℕ) := MonoidAlgebra k (G' n)

/-! ### Counting bound `D.count ≤ |Nat.Partition n|` over a general field -/

/-- The injection from conjugacy classes of `S_n` to partitions of `n`, via cycle type.
This does not depend on the field. -/
private def conjClassToPartition (n : ℕ) :
    ConjClasses (Equiv.Perm (Fin n)) → Nat.Partition n :=
  Quotient.lift
    (fun σ => (Fintype.card_fin n) ▸ σ.partition)
    (fun _ _ h => congrArg (Fintype.card_fin n ▸ ·) (Equiv.Perm.partition_eq_of_isConj.mp h))

private lemma conjClassToPartition_injective (n : ℕ) :
    Function.Injective (conjClassToPartition n) := by
  intro a b h
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change (Fintype.card_fin n ▸ a.partition) = (Fintype.card_fin n ▸ b.partition) at h
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have : ∀ (m : ℕ) (hm : m = n) (p q : m.Partition),
      (hm ▸ p : Nat.Partition n) = (hm ▸ q : Nat.Partition n) → p = q := by
    intro m hm; subst hm; intro p q hpq; exact hpq
  exact this _ (Fintype.card_fin n) _ _ h

/-- `|ConjClasses(S_n)| ≤ |Nat.Partition n|`, via the injection by cycle type. -/
private lemma card_conjClasses_le_card_partition (n : ℕ) :
    Fintype.card (ConjClasses (Equiv.Perm (Fin n))) ≤ Fintype.card (Nat.Partition n) :=
  Fintype.card_le_of_injective _ (conjClassToPartition_injective n)

/-- For each specified input, its associated natural-number value is at most the cardinality of
`n.Partition`. -/
lemma auxiliary_value_le_partition_card (n : ℕ)
    (D : DecompositionData k (G' n)) :
    D.count ≤ Fintype.card (Nat.Partition n) := by
  haveI : Invertible (Fintype.card (G' n) : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
  obtain ⟨n_cc, V_cc, hV_simp, hV_inj, hV_surj, hn_cc⟩ := exists_simpleReps_card_eq_conjClasses
    (G := G' n) (k := k)
  suffices h_eq : D.count = n_cc by
    calc D.count = n_cc := h_eq
      _ = Fintype.card (ConjClasses (G' n)) := hn_cc
      _ ≤ Fintype.card (Nat.Partition n) := card_conjClasses_le_card_partition n
  have f : ∀ j : Fin D.count, ∃ i : Fin n_cc, Nonempty (D.representation j ≅ V_cc i) :=
    fun j => hV_surj (D.representation j) (D.simple_representation j)
  choose f hf using f
  have f_inj : Function.Injective f := by
    intro j₁ j₂ h
    exact D.representation_index_eq_of_iso j₁ j₂
      ⟨(hf j₁).some ≪≫ (h ▸ (hf j₂).some.symm)⟩
  obtain ⟨V_D, _, hD_inj, hD_surj⟩ := D.exists_completeSimpleFamily
  have g : ∀ i : Fin n_cc, ∃ j : Fin D.count, Nonempty (V_cc i ≅ V_D j) :=
    fun i => hD_surj (V_cc i) (hV_simp i)
  choose g hg using g
  have g_inj : Function.Injective g := by
    intro i₁ i₂ h
    exact hV_inj i₁ i₂ ⟨(hg i₁).some ≪≫ (h ▸ (hg i₂).some.symm)⟩
  have h1 : D.count ≤ n_cc := by
    have := Fintype.card_le_of_injective f f_inj
    simp only [Fintype.card_fin] at this; exact this
  have h2 : n_cc ≤ D.count := by
    have := Fintype.card_le_of_injective g g_inj
    simp only [Fintype.card_fin] at this; exact this
  omega

/-! ### Wedderburn block machinery -/

/-- Central idempotent for block `j` of the Wedderburn decomposition. -/
private noncomputable def centralIdem' (n : ℕ) (D : DecompositionData k (G' n)) (j : Fin D.count) :
    A' k n :=
  D.groupAlgebraEquivMatrix.symm (Pi.single j 1)

private lemma centralIdem'_sq (n : ℕ) (D : DecompositionData k (G' n)) (j : Fin D.count) :
    centralIdem' k n D j * centralIdem' k n D j = centralIdem' k n D j := by
  simp only [centralIdem']
  rw [← map_mul D.groupAlgebraEquivMatrix.symm]
  congr 1; ext i
  simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

private lemma centralIdem'_sum (n : ℕ) (D : DecompositionData k (G' n)) :
    ∑ j, centralIdem' k n D j = 1 := by
  simp only [centralIdem']
  rw [← map_sum D.groupAlgebraEquivMatrix.symm]
  conv_rhs => rw [← AlgEquiv.symm_apply_apply D.groupAlgebraEquivMatrix 1]
  congr 1
  ext i
  simp only [Finset.sum_apply, map_one, Pi.one_apply]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hji; simp [Pi.single_eq_of_ne (Ne.symm hji)]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma centralIdem'_orthog (n : ℕ) (D : DecompositionData k (G' n))
    (i j : Fin D.count) (hij : i ≠ j) :
    centralIdem' k n D i * centralIdem' k n D j = 0 := by
  simp only [centralIdem']
  rw [← map_mul D.groupAlgebraEquivMatrix.symm, ← map_zero D.groupAlgebraEquivMatrix.symm]
  congr 1; ext l
  simp only [Pi.mul_apply, Pi.zero_apply]
  by_cases hli : l = i
  · subst hli
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hij]
    simp
  · simp [Pi.single_eq_of_ne hli]

private lemma centralIdem'_comm (n : ℕ) (D : DecompositionData k (G' n))
    (j : Fin D.count) (a : A' k n) :
    centralIdem' k n D j * a = a * centralIdem' k n D j := by
  simp only [centralIdem']
  apply D.groupAlgebraEquivMatrix.injective
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  ext i
  simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

/-- For a simple `A'(n)`-module, exactly one central idempotent acts as identity. -/
private lemma exists_unique_block (n : ℕ) (D : DecompositionData k (G' n))
    (L : Type w) [AddCommGroup L] [Module (A' k n) L] [IsSimpleModule (A' k n) L] :
    ∃! j : Fin D.count, ∀ l : L, centralIdem' k n D j • l = l := by
  have hsum : ∀ l : L, l = ∑ j, centralIdem' k n D j • l := by
    intro l; conv_lhs => rw [← one_smul (A' k n) l, ← centralIdem'_sum k n D]; rw [Finset.sum_smul]
  have hact : ∀ j, (∀ l : L, centralIdem' k n D j • l = 0) ∨
                    (∀ l : L, centralIdem' k n D j • l = l) := by
    intro j
    let ker_j : Submodule (A' k n) L :=
      { carrier := {l | centralIdem' k n D j • l = l}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          change centralIdem' k n D j • (a + b) = a + b
          rw [smul_add, ha, hb]
        smul_mem' := fun a {l} hl => by
          change centralIdem' k n D j • (a • l) = a • l
          rw [← mul_smul, centralIdem'_comm, mul_smul, hl] }
    rcases IsSimpleOrder.eq_bot_or_eq_top ker_j with h | h
    · left; intro l
      have : centralIdem' k n D j • l ∈ ker_j := by
        change centralIdem' k n D j • (centralIdem' k n D j • l) = centralIdem' k n D j • l
        rw [← mul_smul, centralIdem'_sq]
      rw [h] at this; exact (Submodule.mem_bot (A' k n)).mp this
    · right; intro l
      have : l ∈ ker_j := h ▸ Submodule.mem_top
      exact this
  haveI := IsSimpleModule.nontrivial (R := A' k n) (M := L)
  obtain ⟨l₀, hl₀⟩ := exists_ne (0 : L)
  have hexists : ∃ j, ∀ l : L, centralIdem' k n D j • l = l := by
    by_contra hall
    push Not at hall
    have : ∀ j, ∀ l : L, centralIdem' k n D j • l = 0 := by
      intro j; exact (hact j).resolve_right (fun h => (hall j).elim (fun l hl => hl (h l)))
    exact hl₀ (by rw [hsum l₀, Finset.sum_eq_zero (fun j _ => this j l₀)])
  obtain ⟨j₀, hj₀⟩ := hexists
  refine ⟨j₀, hj₀, ?_⟩
  intro j hj
  by_contra hij
  have h1 : centralIdem' k n D j * centralIdem' k n D j₀ = 0 := centralIdem'_orthog k n D j j₀ hij
  have h2 : (centralIdem' k n D j * centralIdem' k n D j₀) • l₀ = l₀ := by
    rw [mul_smul, hj₀ l₀, hj l₀]
  rw [h1, zero_smul] at h2
  exact hl₀ h2.symm

/-- The block assignment for a simple submodule of `A'(n)`. -/
private noncomputable def blockOf (n : ℕ) (D : DecompositionData k (G' n))
    (L : Type w) [AddCommGroup L] [Module (A' k n) L] [IsSimpleModule (A' k n) L] :
    Fin D.count :=
  (exists_unique_block k n D L).choose

private lemma blockOf_spec (n : ℕ) (D : DecompositionData k (G' n))
    (L : Type w) [AddCommGroup L] [Module (A' k n) L] [IsSimpleModule (A' k n) L] :
    ∀ l : L, centralIdem' k n D (blockOf k n D L) • l = l :=
  (exists_unique_block k n D L).choose_spec.1

private lemma blockOf_unique (n : ℕ) (D : DecompositionData k (G' n))
    (L : Type w) [AddCommGroup L] [Module (A' k n) L] [IsSimpleModule (A' k n) L]
    (j : Fin D.count) (hj : ∀ l : L, centralIdem' k n D j • l = l) :
    j = blockOf k n D L :=
  (exists_unique_block k n D L).choose_spec.2 j hj

/-- For `x` in block `j₀`, the `A'(n)`-action factors:
`a * x = iso⁻¹(Pi.single j₀ (proj a)) * x`. -/
private lemma action_factors_block (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    {x : A' k n} (hx : centralIdem' k n D j₀ * x = x) (a : A' k n) :
    a * x = D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ a)) * x := by
  have key : a * centralIdem' k n D j₀ =
      D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ a)) := by
    apply D.groupAlgebraEquivMatrix.injective; rw [map_mul, AlgEquiv.apply_symm_apply]
    ext l; simp only [Pi.mul_apply, centralIdem', AlgEquiv.apply_symm_apply]
    by_cases hl : l = j₀
    · subst hl; simp [Pi.single_eq_same, DecompositionData.matrixBlockHom, Pi.evalRingHom]
    · simp [Pi.single_eq_of_ne hl]
  calc a * x = a * (centralIdem' k n D j₀ * x) := by rw [hx]
    _ = (a * centralIdem' k n D j₀) * x := by rw [mul_assoc]
    _ = D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ a)) * x := by rw [key]

/-- For block elements, `D.groupAlgebraEquivMatrix x = Pi.single j₀ (proj x)`. -/
private lemma iso_eq_single_of_block (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    {x : A' k n} (hx : centralIdem' k n D j₀ * x = x) :
    D.groupAlgebraEquivMatrix x = Pi.single j₀ (D.matrixBlockHom j₀ x) := by
  have h1 : D.groupAlgebraEquivMatrix (centralIdem' k n D j₀ * x) =
      D.groupAlgebraEquivMatrix x := by
    rw [hx]
  rw [map_mul] at h1; simp only [centralIdem', AlgEquiv.apply_symm_apply] at h1
  ext l; rw [← h1]; simp only [Pi.mul_apply]
  by_cases hl : l = j₀
  · subst hl; simp [Pi.single_eq_same, DecompositionData.matrixBlockHom, Pi.evalRingHom]
  · simp [Pi.single_eq_of_ne hl]

/-- For block elements, `iso.symm ∘ Pi.single j₀ ∘ proj = id`. -/
private lemma recover_block (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    {x : A' k n} (hx : centralIdem' k n D j₀ * x = x) :
    D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ x)) = x := by
  rw [← iso_eq_single_of_block k n D j₀ hx, D.groupAlgebraEquivMatrix.symm_apply_apply]

/-- `matrixBlockHom` is injective on block `j₀` elements. -/
private lemma proj_inj_on_block (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    {x : A' k n} (hx : centralIdem' k n D j₀ * x = x)
    (h0 : D.matrixBlockHom j₀ x = 0) : x = 0 := by
  rw [← recover_block k n D j₀ hx, h0, Pi.single_zero, map_zero]

/-- The image of a left ideal `L` (in block `j₀`) under `matrixBlockHom`, as a left ideal of
`Mat_{j₀}`. -/
private def projImage (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    (L : Submodule (A' k n) (A' k n)) : Submodule
      (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k)
      (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k) where
  carrier := {m | ∃ l ∈ L, D.matrixBlockHom j₀ l = m}
  zero_mem' := ⟨0, L.zero_mem, map_zero _⟩
  add_mem' := fun ⟨l₁, hl₁, he₁⟩ ⟨l₂, hl₂, he₂⟩ =>
    ⟨l₁ + l₂, L.add_mem hl₁ hl₂, by rw [map_add, he₁, he₂]⟩
  smul_mem' := fun m {x} hx => by
    obtain ⟨l, hl, he⟩ := hx
    obtain ⟨a, ha⟩ := D.matrixBlockHom_surjective j₀ m
    exact ⟨a * l, L.smul_mem a hl, by
      rw [map_mul, ha, he, smul_eq_mul]⟩

set_option maxHeartbeats 12800000 in
-- The nested pullback submodule construction elaborates slowly with opaque `MonoidAlgebra`.
/-- The `projImage` of a simple left ideal (in the correct block) is simple as a
`Mat_{j₀}`-module. -/
private lemma projImage_isSimple (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    (L : Submodule (A' k n) (A' k n)) [IsSimpleModule (A' k n) L]
    (hL : ∀ l : L, centralIdem' k n D j₀ * (l : A' k n) = ↑l) :
    IsSimpleModule
      (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k)
      (projImage k n D j₀ L) := by
  rw [isSimpleModule_iff_isAtom]
  constructor
  · intro h
    haveI := IsSimpleModule.nontrivial (R := A' k n) (M := L)
    obtain ⟨l, hl⟩ := exists_ne (0 : L)
    have : D.matrixBlockHom j₀ ↑l = 0 := by
      have hm : D.matrixBlockHom j₀ ↑l ∈ projImage k n D j₀ L := ⟨↑l, l.prop, rfl⟩
      rw [h] at hm; exact (Submodule.mem_bot _).mp hm
    exact hl (Subtype.ext (proj_inj_on_block k n D j₀ (hL l) this))
  · intro N hN
    by_contra hN_ne_bot
    have hN_le := le_of_lt hN
    set N' : Submodule (A' k n) L :=
      { carrier := {l : L | D.matrixBlockHom j₀ ↑l ∈ N}
        zero_mem' := by simp [N.zero_mem]
        add_mem' := fun {a b} ha hb => by
          change D.matrixBlockHom j₀ (↑a + ↑b) ∈ N
          rw [map_add]; exact N.add_mem ha hb
        smul_mem' := fun c {l} hl => by
          change D.matrixBlockHom j₀ (c * ↑l) ∈ N
          rw [map_mul]; exact N.smul_mem _ hl } with N'_def
    have hN'_ne_top : N' ≠ ⊤ := by
      intro h_eq
      apply ne_of_lt hN
      apply le_antisymm hN_le
      intro m hm
      obtain ⟨l, hl, he⟩ := hm
      have : (⟨l, hl⟩ : L) ∈ N' := h_eq ▸ Submodule.mem_top
      rw [N'_def] at this
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this
      rw [← he]; exact this
    have hN'_bot :=
      (IsSimpleOrder.eq_bot_or_eq_top N').resolve_right hN'_ne_top
    apply hN_ne_bot; rw [eq_bot_iff]
    intro m hmN
    have hm_pi := hN_le hmN
    obtain ⟨l, hl, he⟩ := hm_pi
    have : (⟨l, hl⟩ : L) ∈ N' := by
      rw [N'_def]
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      rw [he]; exact hmN
    rw [hN'_bot] at this
    rw [Submodule.mem_bot] at this
    have hl0 : l = 0 := congr_arg Subtype.val this
    rw [Submodule.mem_bot, ← he, hl0, map_zero]

/-- For `m` in `projImage` of `L` (in block `j₀`), `recover(m) ∈ L`. -/
private lemma recover_mem_of_projImage (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    (L : Submodule (A' k n) (A' k n))
    (hL : ∀ l : L, centralIdem' k n D j₀ * (l : A' k n) = ↑l)
    {m : Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k}
    (hm : m ∈ projImage k n D j₀ L) :
    D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m) ∈ L := by
  obtain ⟨l, hl, he⟩ := hm
  rw [← he, recover_block k n D j₀ (hL ⟨l, hl⟩)]
  exact hl

/-- Recovering from `projImage` is injective (follows from `iso.symm` injective). -/
private lemma recover_injective_on_projImage
    (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    {m₁ m₂ : Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k}
    (h : D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m₁) =
      D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m₂)) :
    m₁ = m₂ := by
  have h1 := D.groupAlgebraEquivMatrix.symm.injective h
  have h2 := congr_fun h1 j₀
  simp only [Pi.single_eq_same] at h2
  exact h2

/-- `proj ∘ recover = id` on `projImage` elements. -/
private lemma proj_recover (n : ℕ) (D : DecompositionData k (G' n)) (j₀ : Fin D.count)
    (m : Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k) :
    D.matrixBlockHom j₀ (D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m)) = m := by
  simp [DecompositionData.matrixBlockHom, Pi.evalRingHom, Pi.single_eq_same]

/-- Two simple left ideals of `A'(n)` in the same Wedderburn block are isomorphic. -/
private lemma same_block_iso (n : ℕ) (D : DecompositionData k (G' n))
    (L₁ L₂ : Submodule (A' k n) (A' k n))
    [IsSimpleModule (A' k n) L₁] [IsSimpleModule (A' k n) L₂]
    (hblock : blockOf k n D L₁ = blockOf k n D L₂) :
    Nonempty (L₁ ≃ₗ[A' k n] L₂) := by
  set j₀ := blockOf k n D L₁ with hj₀_def
  have hL₁ : ∀ l : L₁, centralIdem' k n D j₀ * (l : A' k n) = ↑l :=
    fun l => congr_arg Subtype.val (blockOf_spec k n D L₁ l)
  have hL₂ : ∀ l : L₂, centralIdem' k n D j₀ * (l : A' k n) = ↑l :=
    fun l => congr_arg Subtype.val (hblock ▸ blockOf_spec k n D L₂ l)
  haveI := projImage_isSimple k n D j₀ L₁ hL₁
  haveI := projImage_isSimple k n D j₀ L₂ hL₂
  haveI := D.dimension_neZero j₀
  haveI : IsSimpleRing (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k) :=
    IsSimpleRing.matrix ..
  haveI : IsArtinianRing (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k) := inferInstance
  obtain ⟨φ_mat⟩ := (IsSimpleRing.isIsotypic
    (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k)
    (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) k))
    (projImage k n D j₀ L₂) (projImage k n D j₀ L₁)
  let projElem (L : Submodule (A' k n) (A' k n)) (l : L) : projImage k n D j₀ L :=
    ⟨D.matrixBlockHom j₀ ↑l, ↑l, l.prop, rfl⟩
  set f : L₁ →ₗ[A' k n] L₂ :=
    { toFun := fun l₁ =>
        ⟨D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (φ_mat (projElem L₁ l₁)).val),
         recover_mem_of_projImage k n D j₀ L₂ hL₂ (φ_mat (projElem L₁ l₁)).prop⟩
      map_add' := fun l₁ l₂ => by
        apply Subtype.ext; apply D.groupAlgebraEquivMatrix.injective
        simp only [Submodule.coe_add, map_add, AlgEquiv.apply_symm_apply]
        have he : projElem L₁ (l₁ + l₂) = projElem L₁ l₁ + projElem L₁ l₂ := by
          ext; simp [projElem, map_add]
        rw [he, φ_mat.map_add, Submodule.coe_add, Pi.single_add]
      map_smul' := fun a l₁ => by
        apply Subtype.ext
        simp only [SetLike.val_smul, smul_eq_mul]
        set v := (φ_mat (projElem L₁ l₁)).val
        have e_smul : projElem L₁ (a • l₁) = D.matrixBlockHom j₀ a • projElem L₁ l₁ := by
          ext; simp [projElem, map_mul]
        have φ_smul : (φ_mat (projElem L₁ (a • l₁))).val = D.matrixBlockHom j₀ a * v := by
          rw [e_smul, φ_mat.map_smul]; rfl
        rw [show D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (φ_mat (projElem L₁ (a • l₁))).val) =
          D.groupAlgebraEquivMatrix.symm
            (Pi.single j₀ (D.matrixBlockHom j₀ a * v)) from by rw [φ_smul]]
        have hv_mem : D.groupAlgebraEquivMatrix.symm (Pi.single j₀ v) ∈ L₂ :=
          recover_mem_of_projImage k n D j₀ L₂ hL₂ (φ_mat (projElem L₁ l₁)).prop
        have hv_block : centralIdem' k n D j₀ * D.groupAlgebraEquivMatrix.symm (Pi.single j₀ v) =
            D.groupAlgebraEquivMatrix.symm (Pi.single j₀ v) := hL₂ ⟨_, hv_mem⟩
        simp only [RingHom.id_apply]
        rw [action_factors_block k n D j₀ hv_block a, ← map_mul D.groupAlgebraEquivMatrix.symm]
        congr 1; ext l; simp only [Pi.mul_apply]
        by_cases hl : l = j₀
        · subst hl; simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne hl] }
  have hf_ne : f ≠ 0 := by
    intro h
    haveI := IsSimpleModule.nontrivial (R := A' k n) (M := L₁)
    obtain ⟨l₁, hl₁⟩ := exists_ne (0 : L₁)
    have h1 : f l₁ = 0 := congr_fun (congr_arg DFunLike.coe h) l₁
    have h2 : D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (φ_mat (projElem L₁ l₁)).val) = 0 :=
      congr_arg Subtype.val h1
    have h3 : (φ_mat (projElem L₁ l₁)).val = 0 := by
      have h3a := D.groupAlgebraEquivMatrix.symm.injective
        (by rw [h2, map_zero] :
          D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (φ_mat (projElem L₁ l₁)).val) =
            D.groupAlgebraEquivMatrix.symm 0)
      have h3b := congr_fun h3a j₀
      simp only [Pi.single_eq_same, Pi.zero_apply] at h3b
      exact h3b
    have h4 : projElem L₁ l₁ = 0 := by
      have : φ_mat (projElem L₁ l₁) = 0 := Subtype.ext h3
      exact φ_mat.injective (by rw [this, map_zero])
    have h5 : (projElem L₁ l₁).val = 0 := congr_arg Subtype.val h4
    exact hl₁ (Subtype.ext (proj_inj_on_block k n D j₀ (hL₁ l₁) h5))
  exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf_ne)⟩

/-- The block map on Specht modules is injective: distinct partitions give distinct blocks. -/
private lemma blockOf_specht_injective_general (n : ℕ) (D : DecompositionData k (G' n))
    (la mu : Nat.Partition n)
    (hla : IsSimpleModule (A' k n) (partitionSubmodule k n la))
    (hmu : IsSimpleModule (A' k n) (partitionSubmodule k n mu))
    (hblock : blockOf k n D (partitionSubmodule k n la) =
      blockOf k n D (partitionSubmodule k n mu)) :
    la = mu := by
  by_contra h
  have ⟨φ⟩ := @same_block_iso k _ _ _ n D (partitionSubmodule k n la) (partitionSubmodule k n mu)
    hla hmu hblock
  exact (isEmpty_linearEquiv_between_subtypes_of_ne k n la mu h).false φ

/-- For any simple `k[S_n]`-module `M`, some Young symmetrizer acts nontrivially.
This follows from `#partitions(n) = #conjugacy_classes(S_n) = #Wedderburn_blocks(k[S_n])`,
ensuring that the Specht modules exhaust all Wedderburn blocks. -/
private lemma exists_young_symmetrizer_nontrivial_general (n : ℕ)
    (M : Type w) [AddCommGroup M] [Module (A' k n) M]
    [IsSimpleModule (A' k n) M] :
    ∃ la : Nat.Partition n, ∃ m : M, partitionSymmetrizer k n la • m ≠ 0 := by
  by_contra h
  push Not at h
  let D := DecompositionData.default (k := k) (G := G' n)
  set j₀ := blockOf k n D M
  have hspecht_simple : ∀ la : Nat.Partition n,
      IsSimpleModule (A' k n) (partitionSubmodule k n la) :=
    fun la => isSimpleModule_partitionSubmodule k n la
  let β : Nat.Partition n → Fin D.count :=
    fun la => @blockOf k _ _ _ n D (partitionSubmodule k n la) _ _ (hspecht_simple la)
  have β_inj : Function.Injective β := by
    intro la mu h
    exact blockOf_specht_injective_general k n D la mu (hspecht_simple la) (hspecht_simple mu) h
  have hn_le := auxiliary_value_le_partition_card k n D
  have hcard_eq : Fintype.card (Nat.Partition n) = Fintype.card (Fin D.count) := by
    apply le_antisymm
    · have := Fintype.card_le_of_injective β β_inj; exact this
    · rwa [Fintype.card_fin]
  have β_surj : Function.Surjective β :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard_eq)).mp β_inj
  obtain ⟨la₀, hla₀⟩ := β_surj j₀
  have hM_block := blockOf_spec k n D M
  haveI := hspecht_simple la₀
  have hiso : Nonempty (M ≃ₗ[A' k n] partitionSubmodule k n la₀) := by
    obtain ⟨I, ⟨φ_M⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (A' k n) M
    haveI : IsSimpleModule (A' k n) I := IsSimpleModule.congr φ_M.symm
    have hI_block : blockOf k n D I = j₀ := by
      apply (blockOf_unique k n D I j₀ _).symm
      intro l
      have := hM_block (φ_M.symm l)
      rw [← φ_M.symm.map_smul] at this
      exact φ_M.symm.injective this
    have hblock : blockOf k n D I = blockOf k n D (partitionSubmodule k n la₀) := by
      rw [hI_block]; exact hla₀.symm
    obtain ⟨ψ⟩ := same_block_iso k n D I (partitionSubmodule k n la₀) hblock
    exact ⟨φ_M.trans ψ⟩
  obtain ⟨φ⟩ := hiso
  set c := partitionSymmetrizer k n la₀
  have hc_mem : c ∈ partitionSubmodule k n la₀ := Submodule.subset_span rfl
  have hc_sq_mem : c * c ∈ partitionSubmodule k n la₀ :=
    (partitionSubmodule k n la₀).smul_mem c hc_mem
  have hc_sq_ne : (⟨c * c, hc_sq_mem⟩ : partitionSubmodule k n la₀) ≠ 0 := by
    intro h_eq; exact partitionIndexedElement_mul_self_ne_zero k n la₀ (Subtype.ext_iff.mp h_eq)
  have hpre_ne : φ.symm ⟨c * c, hc_sq_mem⟩ ≠ 0 := by
    intro h_eq; exact hc_sq_ne (φ.symm.injective (by simp [h_eq]))
  have h1 : c • (φ.symm ⟨c, hc_mem⟩) = 0 := h la₀ (φ.symm ⟨c, hc_mem⟩)
  have h2 : φ.symm ⟨c * c, hc_sq_mem⟩ = 0 := by
    rw [show (⟨c * c, hc_sq_mem⟩ : partitionSubmodule k n la₀) = c • ⟨c, hc_mem⟩ from rfl]
    rw [LinearEquiv.map_smul]
    exact h1
  exact hpre_ne h2

/-- The evaluation linear map from a Specht module `V_λ` to `M`, sending `v` to `v • m₀`.
This is `k[S_n]`-linear since the action on `V_λ ⊆ k[S_n]` is left multiplication. -/
private noncomputable def spechtEvalMap (n : ℕ) (la : Nat.Partition n)
    (M : Type w) [AddCommGroup M] [Module (A' k n) M] (m₀ : M) :
    (partitionSubmodule k n la) →ₗ[A' k n] M where
  toFun v := (v : A' k n) • m₀
  map_add' v w := by
    change ((v : A' k n) + (w : A' k n)) • m₀ = (v : A' k n) • m₀ + (w : A' k n) • m₀
    exact add_smul (v : A' k n) (w : A' k n) m₀
  map_smul' a v := by
    change (a * (v : A' k n)) • m₀ = a • ((v : A' k n) • m₀)
    exact mul_smul a (v : A' k n) m₀

/--
Every simple module over the auxiliary scalar type is linearly equivalent to one of the
specified membership subtypes.
-/
theorem exists_linear_equiv_membership_subtype_over_auxiliary_scalars
    (n : ℕ) (M : Type w) [AddCommGroup M] [Module (A' k n) M]
    [IsSimpleModule (A' k n) M] :
    ∃ la : Nat.Partition n,
      Nonempty (M ≃ₗ[A' k n] (partitionSubmodule k n la)) := by
  obtain ⟨la, m₀, hm₀⟩ := exists_young_symmetrizer_nontrivial_general k n M
  set f := spechtEvalMap k n la M m₀
  have hf_ne : f ≠ 0 := by
    intro h
    apply hm₀
    have : f ⟨partitionSymmetrizer k n la, Submodule.subset_span rfl⟩ = 0 :=
      congr_fun (congr_arg DFunLike.coe h) ⟨partitionSymmetrizer k n la, Submodule.subset_span rfl⟩
    exact this
  haveI : IsSimpleModule (A' k n) (partitionSubmodule k n la) :=
    isSimpleModule_partitionSubmodule k n la
  have hf_bij := LinearMap.bijective_of_ne_zero hf_ne
  exact ⟨la, ⟨(LinearEquiv.ofBijective f hf_bij).symm⟩⟩

/--
Every simple module over the monoid algebra of permutations of `Fin n` is linearly equivalent to
one of the specified membership subtypes.
-/
theorem exists_linear_equiv_membership_subtype_over_permutation_monoid_algebra
    (n : ℕ) (M : Type w) [AddCommGroup M]
    [Module (MonoidAlgebra k (Equiv.Perm (Fin n))) M]
    [IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) M] :
    ∃ la : Nat.Partition n,
      Nonempty (M ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))] partitionSubmodule k n la) :=
  exists_linear_equiv_membership_subtype_over_auxiliary_scalars k n M

end

end RepresentationTheory.SimpleModulesAndPartitionBounds
