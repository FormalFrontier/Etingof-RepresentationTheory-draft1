import EtingofRepresentationTheory.Chapter2.Sl2SemisimpleDecomposition
import EtingofRepresentationTheory.Chapter2.Sl2NullitySequence

/-!
# Uniqueness of the `sl(2)`-structure from the raising operator (Problem 2.15.1(l), piece 4)

This file assembles the *uniqueness* half of Etingof Problem 2.15.1(l): a finite-dimensional
complex `sl(2)`-module is determined up to isomorphism by the nullity sequence
`k ↦ dim ker (E^k)` of its raising operator `E = ρ(e)`. The deliverable is

```
sl2Rep_iso_of_e_jordanType_eq :
  (∀ k, dim ker ((toEnd ℂ sl2 V e)^k) = dim ker ((toEnd ℂ sl2 W e)^k)) → Nonempty (V ≃ₗ⁅ℂ,sl2⁆ W).
```

The proof composes three previously landed structural pieces:

* **Semisimple decomposition** (`sl2Module_decomposition`, `Sl2SemisimpleDecomposition.lean`):
  `V ≃ₗ⁅ℂ,sl2⁆ ∀ i, V_{n i}` onto a block-diagonal sum of standard irreducibles.
* **Block-sum nullity** (`piMap_pow_ker_finrank`, `Sl2NullitySequence.lean`): the nullity of a
  block-diagonal power splits as a sum over the blocks.
* **Multiset inversion** (`nullitySeq_injective`, `Sl2NullitySequence.lean`): the nullity
  sequence is a complete invariant of the multiset of block sizes.

The glue supplied here:

* `intertwine_ker_finrank`: a linear equivalence intertwining two operators identifies their
  kernels, so kernel dimension is an intertwining invariant. Applied to the raising operator,
  the nullity sequence is an `sl(2)`-isomorphism invariant (`nullSeq_lieEquiv`) and, on the
  standard irreducible `V_d`, equals `k ↦ min k d` (`nullSeq_irrep`).
* `nullSeq_pi`: on a block-diagonal product the nullity sequence is `k ↦ ∑ i, min k (n i + 1)`,
  i.e. the nullity function of the multiset of block sizes.
* `exists_reindex`: two finite families of naturals with equal multisets of values are related
  by an index bijection; with `reindexPiLie`/`piCongrRightLie` this reindexes one product of
  irreducibles onto the other.
-/

open Etingof Etingof.Sl2Irrep
open LieModule Module

namespace Etingof.Sl2Irrep

/-! ## Kernel dimension is an intertwining invariant -/

section Intertwine

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- If a linear equivalence `φ` intertwines `A` and `B` (`B ∘ φ = φ ∘ A`), then `φ` maps `ker A`
isomorphically onto `ker B`, so the two kernels have the same dimension. -/
theorem intertwine_ker_finrank (φ : M ≃ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N)
    (h : B ∘ₗ (φ : M →ₗ[ℂ] N) = (φ : M →ₗ[ℂ] N) ∘ₗ A) :
    Module.finrank ℂ (LinearMap.ker A) = Module.finrank ℂ (LinearMap.ker B) := by
  have hmap : Submodule.map (φ : M →ₗ[ℂ] N) (LinearMap.ker A) = LinearMap.ker B := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hc := LinearMap.congr_fun h x
      simp only [LinearMap.comp_apply] at hc
      rw [hc, hx, map_zero]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      have hc := LinearMap.congr_fun h (φ.symm y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hc
      apply φ.injective
      rw [map_zero, ← hc]
      exact hy
  rw [← hmap]
  exact (Submodule.equivMapOfInjective (φ : M →ₗ[ℂ] N) φ.injective (LinearMap.ker A)).finrank_eq

/-- Intertwining is preserved by taking powers: if `B ∘ φ = φ ∘ A` then `B^k ∘ φ = φ ∘ A^k`. -/
theorem intertwine_pow (φ : M ≃ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N)
    (h : B ∘ₗ (φ : M →ₗ[ℂ] N) = (φ : M →ₗ[ℂ] N) ∘ₗ A) (k : ℕ) :
    (B ^ k) ∘ₗ (φ : M →ₗ[ℂ] N) = (φ : M →ₗ[ℂ] N) ∘ₗ (A ^ k) := by
  induction k with
  | zero => simp [pow_zero, Module.End.one_eq_id]
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_eq_comp]
    rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]

end Intertwine

/-! ## The nullity sequence of the raising operator -/

/-- The raising operator `E = ρ(e)` of an `sl(2)`-module. -/
noncomputable abbrev raising (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V] : Module.End ℂ V :=
  LieModule.toEnd ℂ sl2 V sl2_e

section NullSeq

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule sl2 V] [LieModule ℂ sl2 V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule sl2 W] [LieModule ℂ sl2 W]

/-- An `sl(2)`-module isomorphism intertwines the raising operators. -/
theorem raising_comp_lieEquiv (φ : V ≃ₗ⁅ℂ,sl2⁆ W) :
    raising W ∘ₗ (φ.toLinearEquiv : V →ₗ[ℂ] W)
      = (φ.toLinearEquiv : V →ₗ[ℂ] W) ∘ₗ raising V := by
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LieModuleEquiv.coe_toLinearEquiv,
    raising, LieModule.toEnd_apply_apply]
  exact ((φ : V →ₗ⁅ℂ,sl2⁆ W).map_lie sl2_e v).symm

/-- **The nullity sequence is an `sl(2)`-isomorphism invariant.** -/
theorem nullSeq_lieEquiv (φ : V ≃ₗ⁅ℂ,sl2⁆ W) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (raising V ^ k))
      = Module.finrank ℂ (LinearMap.ker (raising W ^ k)) :=
  intertwine_ker_finrank φ.toLinearEquiv (raising V ^ k) (raising W ^ k)
    (intertwine_pow φ.toLinearEquiv (raising V) (raising W) (raising_comp_lieEquiv φ) k)

end NullSeq

/-- On the standard irreducible `V_d = Fin d → ℂ`, the raising operator is `rhoLieHom d e`. -/
theorem raising_irrep (d : ℕ) : raising (Fin d → ℂ) = rhoLieHom d sl2_e := by
  refine LinearMap.ext fun v => ?_
  rw [raising, LieModule.toEnd_apply_apply]
  rfl

/-- **Single-block nullity sequence.** On the standard irreducible `V_d = Fin d → ℂ` the nullity
sequence of the raising operator is `k ↦ min k d`, matching the standard Jordan block. -/
theorem nullSeq_irrep (d k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (raising (Fin d → ℂ) ^ k)) = min k d := by
  -- `jordanShift d = factScale d ∘ rhoLieHom d e ∘ (factScale d)⁻¹`, so the two operators are
  -- conjugate and share their kernel dimensions.
  have hconj : jordanShift d ∘ₗ (factScale d : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
      = (factScale d : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ∘ₗ rhoLieHom d sl2_e := by
    have hb := sl2RepOfBlock_e d
    rw [sl2RepOfBlock_apply, LinearEquiv.conjAlgEquiv_apply] at hb
    -- hb : (factScale d) ∘ₗ rhoLieHom d e ∘ₗ (factScale d).symm = jordanShift d
    have hsymm : (factScale d).symm.toLinearMap ∘ₗ (factScale d : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
        = LinearMap.id := by ext v; simp
    rw [← hb]
    simp only [LinearMap.comp_assoc]
    rw [hsymm, LinearMap.comp_id]
  rw [raising_irrep,
    intertwine_ker_finrank (factScale d) (rhoLieHom d sl2_e ^ k) (jordanShift d ^ k)
      (intertwine_pow (factScale d) (rhoLieHom d sl2_e) (jordanShift d) hconj k),
    jordanShift_pow_ker_finrank]

/-! ## The nullity sequence of a block-diagonal product -/

section Pi

variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  [∀ i, LieRingModule sl2 (W i)] [∀ i, LieModule ℂ sl2 (W i)]

omit [Fintype ι] in
/-- On a product with the componentwise `sl(2)`-action, the raising operator is the
block-diagonal sum of the componentwise raising operators. -/
theorem raising_pi : raising (∀ i, W i) = LinearMap.piMap fun i => raising (W i) := by
  ext v j
  simp only [raising, LieModule.toEnd_apply_apply, LinearMap.coe_piMap, Pi.map_apply,
    pi_bracket_apply]

/-- **Block-diagonal nullity sequence.** On a product the nullity sequence splits over the
factors: `dim ker ((E_{∏W})^k) = ∑ i, dim ker ((E_{W i})^k)`. -/
theorem nullSeq_pi [∀ i, FiniteDimensional ℂ (W i)] (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (raising (∀ i, W i) ^ k))
      = ∑ i, Module.finrank ℂ (LinearMap.ker (raising (W i) ^ k)) := by
  rw [raising_pi, piMap_pow_ker_finrank]

end Pi

/-- The nullity sequence of the block-diagonal sum of standard irreducibles `∀ i, V_{n i}`. -/
theorem nullSeq_pi_irrep {ι : Type*} [Fintype ι] (n : ι → ℕ) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (raising (∀ i, (Fin (n i + 1) → ℂ)) ^ k))
      = ∑ i, min k (n i + 1) := by
  rw [nullSeq_pi]
  exact Finset.sum_congr rfl fun i _ => nullSeq_irrep (n i + 1) k

/-! ## Reindexing a product of irreducibles -/

section Reindex

variable {ι κ : Type*}

/-- A standard irreducible reindexed by a numerical equality: `V_a ≃ₗ⁅ℂ,sl2⁆ V_b` when `a = b`. -/
noncomputable def blockCastLie {a b : ℕ} (h : a = b) :
    (Fin (a + 1) → ℂ) ≃ₗ⁅ℂ,sl2⁆ (Fin (b + 1) → ℂ) := by
  subst h; exact LieModuleEquiv.refl

/-- Componentwise assembly: a family of `sl(2)`-module isomorphisms `e i : M i ≃ N i` assembles
into an isomorphism of products. -/
noncomputable def piCongrRightLie {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, LieRingModule sl2 (M i)] [∀ i, LieModule ℂ sl2 (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    [∀ i, LieRingModule sl2 (N i)] [∀ i, LieModule ℂ sl2 (N i)]
    (e : ∀ i, M i ≃ₗ⁅ℂ,sl2⁆ N i) : (∀ i, M i) ≃ₗ⁅ℂ,sl2⁆ (∀ i, N i) where
  toFun v i := e i (v i)
  invFun w i := (e i).symm (w i)
  map_add' u v := by funext i; simp
  map_smul' c v := by funext i; simp
  map_lie' := by
    intro x v; funext i
    exact (e i : M i →ₗ⁅ℂ,sl2⁆ N i).map_lie x (v i)
  left_inv v := by funext i; simp
  right_inv w := by funext i; simp

/-- Reindexing a product of `sl(2)`-modules along an index equivalence `σ : ι ≃ κ`. The clean
(cast-free) direction is the pullback `w ↦ w ∘ σ`. -/
noncomputable def reindexPiLie (σ : ι ≃ κ) (N : κ → Type*)
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
    [∀ j, LieRingModule sl2 (N j)] [∀ j, LieModule ℂ sl2 (N j)] :
    (∀ j, N j) ≃ₗ⁅ℂ,sl2⁆ (∀ i, N (σ.symm.symm i)) :=
  { LinearEquiv.piCongrLeft' ℂ N σ.symm with
    map_lie' := by intro x v; funext i; rfl }

end Reindex

/-! ## Extracting an index bijection from equal multisets of block sizes -/

/-- Two finite families of naturals with equal multisets of values are related by an index
equivalence: there is `σ : ι ≃ κ` with `f = g ∘ σ`. -/
theorem exists_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℕ) (g : κ → ℕ)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : ι ≃ κ, ∀ i, f i = g (σ i) := by
  classical
  -- Equal multisets have equal fibre cardinalities.
  have hcard : ∀ v : ℕ, Fintype.card {i // f i = v} = Fintype.card {j // g j = v} := by
    intro v
    have e := congrArg (Multiset.count v) h
    rw [Multiset.count_map, Multiset.count_map] at e
    rw [Fintype.card_subtype, Fintype.card_subtype,
      show (Finset.univ.filter fun i => f i = v)
        = (Finset.univ.filter fun i => v = f i) from
        Finset.filter_congr (by intro i _; rw [eq_comm]),
      show (Finset.univ.filter fun j => g j = v)
        = (Finset.univ.filter fun j => v = g j) from
        Finset.filter_congr (by intro j _; rw [eq_comm])]
    rw [← Finset.filter_val, ← Finset.filter_val] at e
    exact e
  -- Per-fibre equivalences assemble into the bijection via the fibration `α ≃ Σ v, fibre v`.
  let eqv : ∀ v : ℕ, {i // f i = v} ≃ {j // g j = v} := fun v => Fintype.equivOfCardEq (hcard v)
  set σ : ι ≃ κ := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight eqv).trans (Equiv.sigmaFiberEquiv g)) with hσdef
  refine ⟨σ, fun i => ?_⟩
  -- `σ i` lands in the fibre `g · = f i`, so `g (σ i) = f i`.
  have hval : σ i = (eqv (f i) ⟨i, rfl⟩).1 := rfl
  rw [hval]
  exact (eqv (f i) ⟨i, rfl⟩).2.symm

/-! ## The uniqueness theorem -/

/-- The multiset of block sizes of a block-diagonal decomposition `∀ i, V_{n i}`. -/
def blockMultiset {ι : Type*} [Fintype ι] (n : ι → ℕ) : Multiset ℕ :=
  Multiset.map (fun i => n i + 1) Finset.univ.val

theorem nullity_blockMultiset {ι : Type*} [Fintype ι] (n : ι → ℕ) (k : ℕ) :
    NullitySeq.nullity (blockMultiset n) k = ∑ i, min k (n i + 1) := by
  simp only [NullitySeq.nullity, blockMultiset, Multiset.map_map, Function.comp]
  rfl

theorem zero_notMem_blockMultiset {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    (0 : ℕ) ∉ blockMultiset n := by
  simp only [blockMultiset, Multiset.mem_map]
  rintro ⟨i, -, hi⟩
  omega

/-- **Uniqueness of the `sl(2)`-structure from the raising operator (Problem 2.15.1(l)).**
Two finite-dimensional complex `sl(2)`-modules whose raising operators `E = ρ(e)` have equal
nullity sequences `k ↦ dim ker (E^k)` are isomorphic as `sl(2)`-modules. -/
theorem sl2Rep_iso_of_e_jordanType_eq
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule sl2 W] [LieModule ℂ sl2 W]
    (h : ∀ k, Module.finrank ℂ (LinearMap.ker (raising V ^ k))
      = Module.finrank ℂ (LinearMap.ker (raising W ^ k))) :
    Nonempty (V ≃ₗ⁅ℂ,sl2⁆ W) := by
  obtain ⟨mV, nV, ⟨eV⟩⟩ := sl2Module_decomposition V
  obtain ⟨mW, nW, ⟨eW⟩⟩ := sl2Module_decomposition W
  -- Equal nullity sequences of the two block sums.
  have hnull : ∀ k, NullitySeq.nullity (blockMultiset nV) k
      = NullitySeq.nullity (blockMultiset nW) k := by
    intro k
    rw [nullity_blockMultiset, nullity_blockMultiset, ← nullSeq_pi_irrep, ← nullSeq_pi_irrep,
      ← nullSeq_lieEquiv eV, ← nullSeq_lieEquiv eW, h]
  -- Hence equal multisets of block sizes.
  have hmulti : blockMultiset nV = blockMultiset nW :=
    nullitySeq_injective (zero_notMem_blockMultiset nV) (zero_notMem_blockMultiset nW) hnull
  -- Reindex one product of irreducibles onto the other.
  obtain ⟨σ, hσ⟩ := exists_reindex (fun i => nV i + 1) (fun j => nW j + 1) hmulti
  have hσ' : ∀ i, nV i = nW (σ i) := fun i => by have := hσ i; omega
  refine ⟨eV.trans (((piCongrRightLie fun i => blockCastLie (hσ' i)).trans
    (reindexPiLie σ (fun j => (Fin (nW j + 1) → ℂ))).symm).trans eW.symm)⟩

end Etingof.Sl2Irrep
