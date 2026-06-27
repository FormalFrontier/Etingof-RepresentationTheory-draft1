import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2Core
import EtingofRepresentationTheory.Chapter5.SpechtBridgeGeneral
import EtingofRepresentationTheory.Chapter5.SchurWeylSpecialBlockGeneral

/-!
# Theorem 5.22.1 (Schur-Weyl L_i, part C-4a sub-A): the special Schur-Weyl block

This file isolates the one genuinely character-theoretic fact required to assemble
`schurModuleSubmodule_isSimple_centralizer` (the C-4a aggregation) from
`image_of_primitive_idempotent_isSimple_centralizer`: among the simple blocks of
the Schur-Weyl bimodule decomposition of `V^⊗n`, there is a **unique** block whose
Specht-module label is `weightToPartition N lam`.

The two halves of the statement reduce to:

* **Existence** of a `weightToPartition`-labelled block. By contraposition: if *every*
  block carried a label `≠ weightToPartition`, off-block vanishing
  (`youngSym_action_vanishes_off_block`) plus block factorization
  (`youngSym_block_factorization`) would force `youngSymEndomorphism ℂ N lam = 0`,
  contradicting `youngSymEndomorphism_ne_zero` (proved here from
  `schurModuleSubmodule_ne_bot`, i.e. the Weyl character formula `ch(L_λ) = s_λ ≠ 0`).

* **Uniqueness** (at most one `weightToPartition`-labelled block). Two simple
  `symGroupImage`-submodules with the same Specht character are isomorphic as
  `symGroupImage`-modules, hence equal by the decomposition's distinctness clause.
  This "character determines the module over ℂ" step is the single remaining gap,
  isolated as `simpleSymGroupImageSubmodule_iso_of_spechtCharacter_eq` below.
-/

noncomputable section

namespace Etingof

open scoped TensorProduct

/-! ## Nonvanishing of the Young symmetrizer endomorphism -/

/-- The Young symmetrizer endomorphism on `(ℂ^N)^{⊗n}` is nonzero whenever `lam` is
antitone. Its range is `SchurModuleSubmodule ℂ N lam`, which is nonzero by the Weyl
character formula `ch(L_λ) = s_λ ≠ 0` (`schurModuleSubmodule_ne_bot`). -/
theorem youngSymEndomorphism_ne_zero (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    youngSymEndomorphism ℂ N lam ≠ 0 := by
  intro h
  apply schurModuleSubmodule_ne_bot (k := ℂ) N lam hlam
  change LinearMap.range (youngSymEndomorphism ℂ N lam) = ⊥
  rw [h, LinearMap.range_zero]

/-! ## The character-determines-module gap (cited dependency)

This is the only genuinely character-theoretic ingredient of the special-block
lemma still open. Tracked as the dedicated follow-up issue #4679. -/

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Character determines the module over ℂ.** Two simple `symGroupImage`-submodules
`S, S' ≤ V^⊗n` whose `σ`-trace functions both equal `spechtModuleCharacter n la`
are isomorphic as `symGroupImage`-modules.

Route (deferred): transport `S.restrictScalars ℂ`, `S'.restrictScalars ℂ` to simple
`SymGroupAlgebra n`-modules (`submoduleAsSymGroupAlgebra_isSimpleModule`), classify
each as `spechtModule` of its label (Theorem 5.12.2), use linear independence of
irreducible characters to pin both labels to `la` (so the Specht modules coincide),
then transfer the resulting `SymGroupAlgebra`-iso back through the surjection
`symGroupAlgHomToImage` to a `symGroupImage`-iso. -/
theorem simpleSymGroupImageSubmodule_iso_of_spechtCharacter_eq
    {N n : ℕ}
    (S S' : Submodule (symGroupImage ℂ (Fin N → ℂ) n) (TensorPower ℂ (Fin N → ℂ) n))
    [IsSimpleModule (↥(symGroupImage ℂ (Fin N → ℂ) n)) ↥S]
    [IsSimpleModule (↥(symGroupImage ℂ (Fin N → ℂ) n)) ↥S']
    (la : Nat.Partition n)
    (hS : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace ℂ ↥(S.restrictScalars ℂ)
          ((symGroupAction ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
            (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S σ hv)) =
          spechtModuleCharacter n la σ)
    (hS' : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace ℂ ↥(S'.restrictScalars ℂ)
          ((symGroupAction ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
            (p := S'.restrictScalars ℂ) (q := S'.restrictScalars ℂ)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S' σ hv)) =
          spechtModuleCharacter n la σ) :
    Nonempty (↥S ≃ₗ[↥(symGroupImage ℂ (Fin N → ℂ) n)] ↥S') :=
  -- Proved in `Theorem5_22_1.lean` where the Specht-bridge infrastructure lives:
  -- classify each `restrictScalars` module as a Specht module, pin both labels
  -- to `la` by Specht character injectivity, then transfer the resulting
  -- `SymGroupAlgebra`-iso to a `symGroupImage`-iso through `symGroupAlgHomToImage`.
  simpleSubmodule_iso_of_spechtCharacter_eq S S' la hS hS'

/-! ## Existence and uniqueness of the special block -/

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1200000 in
/-- If `youngSymEndomorphism ℂ N lam` vanishes on every block `S i` of a bimodule
decomposition `e`, then it is the zero endomorphism. The block factorization
`youngSym_block_factorization` shows that, through `e`, `youngSymEndomorphism` acts on
block `i` by `(youngSymElement • -) ⊗ id`; vanishing on each `S i` kills the first
factor, hence the whole map on the spanning pure tensors `e.symm (of i (v ⊗ₜ l))`. -/
private theorem youngSymEndomorphism_eq_zero_of_blocks_vanish
    (N : ℕ) (lam : Fin N → ℕ)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule (symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))
      (TensorPower ℂ (Fin N → ℂ) (∑ i, lam i)))
    (e : TensorPower ℂ (Fin N → ℂ) (∑ i, lam i) ≃ₗ[ℂ]
      DirectSum ι (fun i => ↥(S i) ⊗[ℂ]
        (↥(S i) →ₗ[↥(symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))]
          TensorPower ℂ (Fin N → ℂ) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))]
          TensorPower ℂ (Fin N → ℂ) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[ℂ] l)) = l v)
    (hvanish : ∀ (i : ι) (v : ↥(S i)), youngSymEndomorphism ℂ N lam v.val = 0) :
    youngSymEndomorphism ℂ N lam = 0 := by
  have hcomp : (youngSymEndomorphism ℂ N lam) ∘ₗ e.symm.toLinearMap = 0 := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro v l
    simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply,
      DirectSum.lof_eq_of]
    have hbf := youngSym_block_factorization ℂ N lam S e he i v l
    have hzero : youngSymElement ℂ N lam • v = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_smul, ZeroMemClass.coe_zero, Subalgebra.smul_def,
        Module.End.smul_def, youngSymElement_val]
      exact hvanish i v
    rw [hzero, TensorProduct.zero_tmul, map_zero] at hbf
    have := congrArg e.symm hbf
    rwa [e.symm_apply_apply, map_zero] at this
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun hcomp (e x)
  rw [LinearMap.zero_apply, LinearMap.comp_apply] at hx
  rwa [LinearEquiv.coe_coe, e.symm_apply_apply] at hx

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The unique special Schur-Weyl block.**

Given the explicit bimodule decomposition `(S, hSimp, hDist, hSfin, e, he)` of
`V^⊗n` (from `Theorem5_18_4_bimodule_decomposition_explicit` over `ℂ`,
`V = Fin N → ℂ`), there is a unique block index `iLam` whose Specht-module label is
`weightToPartition N lam`: the trace on `S iLam` realises
`spechtModuleCharacter (∑ i, lam i) (weightToPartition N lam)`, while every other
block carries a label `≠ weightToPartition N lam`.

This is sub-A of the C-4a aggregation `schurModuleSubmodule_isSimple_centralizer`;
sub-B feeds the two conjuncts to the off-block (β.3) and rank-1 (γ) analyses. -/
theorem exists_unique_special_block
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule (symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))
      (TensorPower ℂ (Fin N → ℂ) (∑ i, lam i)))
    (hSimp : ∀ i, IsSimpleModule (↥(symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))) ↥(S i))
    (hDist : ∀ i j,
      Nonempty (↥(S i) ≃ₗ[↥(symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))] ↥(S j)) → i = j)
    (hSfin : ∀ i, Module.Finite ℂ ↥(S i))
    (e : TensorPower ℂ (Fin N → ℂ) (∑ i, lam i) ≃ₗ[ℂ]
      DirectSum ι (fun i => ↥(S i) ⊗[ℂ]
        (↥(S i) →ₗ[↥(symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))]
          TensorPower ℂ (Fin N → ℂ) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))]
          TensorPower ℂ (Fin N → ℂ) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[ℂ] l)) = l v) :
    ∃ iLam : ι,
      (∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace ℂ ↥((S iLam).restrictScalars ℂ)
          ((symGroupAction ℂ (Fin N → ℂ) (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S iLam).restrictScalars ℂ) (q := (S iLam).restrictScalars ℂ)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule (S iLam) σ hv)) =
          spechtModuleCharacter (∑ i, lam i) (weightToPartition N lam) σ) ∧
      (∀ i, i ≠ iLam → ∃ la' : Nat.Partition (∑ i, lam i),
        la' ≠ weightToPartition N lam ∧
        ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
          LinearMap.trace ℂ ↥((S i).restrictScalars ℂ)
            ((symGroupAction ℂ (Fin N → ℂ) (∑ i, lam i) σ).toLinearMap.restrict
              (p := (S i).restrictScalars ℂ) (q := (S i).restrictScalars ℂ)
              (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule (S i) σ hv)) =
            spechtModuleCharacter (∑ i, lam i) la' σ) := by
  -- Per-block Specht labels with the trace property (β.2).
  have hlabexists : ∀ i, ∃ la' : Nat.Partition (∑ i, lam i),
      ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace ℂ ↥((S i).restrictScalars ℂ)
          ((symGroupAction ℂ (Fin N → ℂ) (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S i).restrictScalars ℂ) (q := (S i).restrictScalars ℂ)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule (S i) σ hv)) =
          spechtModuleCharacter (∑ i, lam i) la' σ := by
    intro i
    haveI := hSimp i
    exact trace_symGroupAction_eq_spechtModuleCharacter (S i)
  choose lab hlab using hlabexists
  -- Uniqueness: distinct blocks carry distinct labels.
  have hUniq : ∀ i j, lab i = lab j → i = j := by
    intro i j hij
    haveI := hSimp i
    haveI := hSimp j
    apply hDist i j
    apply simpleSymGroupImageSubmodule_iso_of_spechtCharacter_eq (S i) (S j) (lab i)
      (hlab i)
    intro σ
    rw [hij]
    exact hlab j σ
  -- Existence: some block carries the label `weightToPartition N lam`.
  have hExists : ∃ iLam, lab iLam = weightToPartition N lam := by
    by_contra hcon
    push_neg at hcon
    -- Every block: `youngSymEndomorphism` vanishes on `S i` (β.3).
    have hvanish : ∀ (i : ι) (v : ↥(S i)),
        youngSymEndomorphism ℂ N lam v.val = 0 := by
      intro i v
      haveI := hSimp i
      haveI : Module.Finite ℂ ↥((S i).restrictScalars ℂ) := hSfin i
      have hr := youngSym_action_vanishes_off_block N lam (S i) (lab i) (hlab i) (hcon i)
      have hv0 := LinearMap.congr_fun hr v
      rw [LinearMap.zero_apply] at hv0
      have := congrArg Subtype.val hv0
      rwa [LinearMap.restrict_coe_apply, ZeroMemClass.coe_zero] at this
    -- Block factorization forces `youngSymEndomorphism ℂ N lam = 0`.
    exact youngSymEndomorphism_ne_zero N lam hlam
      (youngSymEndomorphism_eq_zero_of_blocks_vanish N lam S e he hvanish)
  obtain ⟨iLam, hLamEq⟩ := hExists
  refine ⟨iLam, ?_, ?_⟩
  · intro σ
    have := hlab iLam σ
    rwa [hLamEq] at this
  · intro i hi
    refine ⟨lab i, ?_, hlab i⟩
    intro hcontra
    exact hi (hUniq i iLam (hcontra.trans hLamEq.symm))

/-! ## General-`k` analogues

The three results above are hardcoded over ℂ. Below are their analogues over a general
characteristic-zero algebraically closed field `k`, built on:

* the general-`k` Specht bridge `trace_symGroupAction_eq_spechtModuleCharacterK` and the
  iso wrapper `simpleSymGroupImageSubmodule_iso_of_spechtCharacterK_eq`
  (`SpechtBridgeGeneral.lean`, #4992);
* the general-`k` off-block vanishing `youngSym_action_vanishes_off_block_general`
  (`SchurWeylSpecialBlockGeneral.lean`, #5004);
* the already-generic `youngSym_block_factorization` and `schurModuleSubmodule_ne_bot`.

The general-`k` Specht character `spechtModuleCharacterK` (bridge) and `spechtBlockCharacterK`
(off-block lemma) are definitionally equal, so the bridge's per-block label hypotheses feed the
off-block lemma directly. The ℂ results above are left untouched for their existing call-sites. -/

section General

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- General-`k` analogue of `youngSymEndomorphism_ne_zero`: the Young symmetrizer endomorphism on
`(k^N)^{⊗n}` is nonzero whenever `lam` is antitone, since its range
`SchurModuleSubmodule k N lam` is nonzero by the Weyl character formula. -/
theorem youngSymEndomorphism_ne_zero_general (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    youngSymEndomorphism k N lam ≠ 0 := by
  intro h
  apply schurModuleSubmodule_ne_bot (k := k) N lam hlam
  change LinearMap.range (youngSymEndomorphism k N lam) = ⊥
  rw [h, LinearMap.range_zero]

set_option maxHeartbeats 3200000 in
-- The `DirectSum`/`TensorProduct` extensionality reduction traverses the deep
-- `Subalgebra → Subsemiring → Module` instance chain for `symGroupImage`, exceeding defaults.
set_option synthInstance.maxHeartbeats 1200000 in
omit [IsAlgClosed k] [CharZero k] in
/-- General-`k` analogue of `youngSymEndomorphism_eq_zero_of_blocks_vanish`. -/
private theorem youngSymEndomorphism_eq_zero_of_blocks_vanish_general
    (N : ℕ) (lam : Fin N → ℕ)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule (symGroupImage k (Fin N → k) (∑ i, lam i))
      (TensorPower k (Fin N → k) (∑ i, lam i)))
    (e : TensorPower k (Fin N → k) (∑ i, lam i) ≃ₗ[k]
      DirectSum ι (fun i => ↥(S i) ⊗[k]
        (↥(S i) →ₗ[↥(symGroupImage k (Fin N → k) (∑ i, lam i))]
          TensorPower k (Fin N → k) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(symGroupImage k (Fin N → k) (∑ i, lam i))]
          TensorPower k (Fin N → k) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v)
    (hvanish : ∀ (i : ι) (v : ↥(S i)), youngSymEndomorphism k N lam v.val = 0) :
    youngSymEndomorphism k N lam = 0 := by
  have hcomp : (youngSymEndomorphism k N lam) ∘ₗ e.symm.toLinearMap = 0 := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro v l
    simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply,
      DirectSum.lof_eq_of]
    have hbf := youngSym_block_factorization k N lam S e he i v l
    have hzero : youngSymElement k N lam • v = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_smul, ZeroMemClass.coe_zero, Subalgebra.smul_def,
        Module.End.smul_def, youngSymElement_val]
      exact hvanish i v
    rw [hzero, TensorProduct.zero_tmul, map_zero] at hbf
    have := congrArg e.symm hbf
    rwa [e.symm_apply_apply, map_zero] at this
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun hcomp (e x)
  rw [LinearMap.zero_apply, LinearMap.comp_apply] at hx
  rwa [LinearEquiv.coe_coe, e.symm_apply_apply] at hx

set_option maxHeartbeats 1600000 in
-- Choosing per-block labels and discharging uniqueness/existence elaborates the deep
-- `symGroupImage` `Subalgebra → Subsemiring → Module` instance chain repeatedly.
set_option synthInstance.maxHeartbeats 400000 in
/-- **The unique special Schur-Weyl block (general `k`).** General-`k` analogue of
`exists_unique_special_block`: given the explicit bimodule decomposition of `V^⊗n`
(`V = Fin N → k`), there is a unique block index `iLam` whose Specht-module label is
`weightToPartition N lam`. -/
theorem exists_unique_special_block_general
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule (symGroupImage k (Fin N → k) (∑ i, lam i))
      (TensorPower k (Fin N → k) (∑ i, lam i)))
    (hSimp : ∀ i, IsSimpleModule (↥(symGroupImage k (Fin N → k) (∑ i, lam i))) ↥(S i))
    (hDist : ∀ i j,
      Nonempty (↥(S i) ≃ₗ[↥(symGroupImage k (Fin N → k) (∑ i, lam i))] ↥(S j)) → i = j)
    (hSfin : ∀ i, Module.Finite k ↥(S i))
    (e : TensorPower k (Fin N → k) (∑ i, lam i) ≃ₗ[k]
      DirectSum ι (fun i => ↥(S i) ⊗[k]
        (↥(S i) →ₗ[↥(symGroupImage k (Fin N → k) (∑ i, lam i))]
          TensorPower k (Fin N → k) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(symGroupImage k (Fin N → k) (∑ i, lam i))]
          TensorPower k (Fin N → k) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v) :
    ∃ iLam : ι,
      (∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥((S iLam).restrictScalars k)
          ((symGroupAction k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S iLam).restrictScalars k) (q := (S iLam).restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule (S iLam) σ hv)) =
          spechtModuleCharacterK k (∑ i, lam i) (weightToPartition N lam) σ) ∧
      (∀ i, i ≠ iLam → ∃ la' : Nat.Partition (∑ i, lam i),
        la' ≠ weightToPartition N lam ∧
        ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
          LinearMap.trace k ↥((S i).restrictScalars k)
            ((symGroupAction k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
              (p := (S i).restrictScalars k) (q := (S i).restrictScalars k)
              (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule (S i) σ hv)) =
            spechtModuleCharacterK k (∑ i, lam i) la' σ) := by
  -- Per-block Specht labels with the trace property (β.2).
  have hlabexists : ∀ i, ∃ la' : Nat.Partition (∑ i, lam i),
      ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥((S i).restrictScalars k)
          ((symGroupAction k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S i).restrictScalars k) (q := (S i).restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule (S i) σ hv)) =
          spechtModuleCharacterK k (∑ i, lam i) la' σ := by
    intro i
    haveI := hSimp i
    exact trace_symGroupAction_eq_spechtModuleCharacterK (S i)
  choose lab hlab using hlabexists
  -- Uniqueness: distinct blocks carry distinct labels.
  have hUniq : ∀ i j, lab i = lab j → i = j := by
    intro i j hij
    haveI := hSimp i
    haveI := hSimp j
    apply hDist i j
    apply simpleSymGroupImageSubmodule_iso_of_spechtCharacterK_eq (S i) (S j) (lab i)
      (hlab i)
    intro σ
    rw [hij]
    exact hlab j σ
  -- Existence: some block carries the label `weightToPartition N lam`.
  have hExists : ∃ iLam, lab iLam = weightToPartition N lam := by
    by_contra hcon
    push_neg at hcon
    -- Every block: `youngSymEndomorphism` vanishes on `S i` (β.3).
    have hvanish : ∀ (i : ι) (v : ↥(S i)),
        youngSymEndomorphism k N lam v.val = 0 := by
      intro i v
      haveI := hSimp i
      haveI : Module.Finite k ↥((S i).restrictScalars k) := hSfin i
      have hr := youngSym_action_vanishes_off_block_general N lam (S i) (lab i) (hlab i) (hcon i)
      have hv0 := LinearMap.congr_fun hr v
      rw [LinearMap.zero_apply] at hv0
      have := congrArg Subtype.val hv0
      rwa [LinearMap.restrict_coe_apply, ZeroMemClass.coe_zero] at this
    -- Block factorization forces `youngSymEndomorphism k N lam = 0`.
    exact youngSymEndomorphism_ne_zero_general N lam hlam
      (youngSymEndomorphism_eq_zero_of_blocks_vanish_general N lam S e he hvanish)
  obtain ⟨iLam, hLamEq⟩ := hExists
  refine ⟨iLam, ?_, ?_⟩
  · intro σ
    have := hlab iLam σ
    rwa [hLamEq] at this
  · intro i hi
    refine ⟨lab i, ?_, hlab i⟩
    intro hcontra
    exact hi (hUniq i iLam (hcontra.trans hLamEq.symm))

end General

end Etingof

end
