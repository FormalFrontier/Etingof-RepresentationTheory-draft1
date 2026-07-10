import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_CountingBound
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_SplitSimples

/-!
# Field-general counting bound `#(simple k[G]-modules) ≤ #ConjClasses` (Exercise 4.2.3)

This file assembles the **field-general** upper bound

  `Nat.card (IrrepClasses k G) ≤ Nat.card (ConjClasses G)`

for the number of isomorphism classes of irreducible representations of a finite group `G`
over an **arbitrary** field `k` (only `[Field k]`; no `IsAlgClosed`, no invertibility of
`|G|`). It is the counting half of Exercise 4.2.3, in the indexing the assembly needs
(`IrrepClasses k G`, from `Exercise4_2_3.lean`; the `≤` here upgrades to the strict `<` of
`Exercise4_2_3` in the modular case, where a nonzero central nilpotent forces the drop).

## Why a base change is needed

Over a **non-splitting** field an individual cocenter trace form `τ_{S_i}` of a simple module
can be **identically zero** (`char k` dividing a Schur index, or an inseparable centre), so the
naive "the trace forms `τ_{S_i}` are `LinearIndependent`" hypothesis of
`CocenterMonoidAlgebra.card_le_conjClasses_of_traceForm_linearIndependent`
(`Exercise4_2_3_CountingBound.lean`) is **false** in general. The standard fix is to pass to a
splitting field `K ⊇ k` (here the algebraic closure), where every Wedderburn block of
`K[G]/rad` is a full matrix algebra `Matrix d_i(K)` with the ordinary trace, and to combine two
facts:

1. **Split-field bound.** Over an algebraically closed `K`,
   `Nat.card (IrrepClasses K G) ≤ Nat.card (ConjClasses G)`.
   (`K[G]/rad ≅ ∏ Matrix d_i(K)`, so `#(simple K[G]-modules) = #blocks`, and the block trace
   forms `E₁₁ ↦ 1` are linearly independent functionals on the cocenter `C = K[G]/[K[G],K[G]]`,
   whose dimension is `#ConjClasses` by `finrank_cocenter_eq_card_conjClasses`.)
2. **Base-change monotonicity.** For any field extension `K ⊇ k`,
   `Nat.card (IrrepClasses k G) ≤ Nat.card (IrrepClasses K G)`.
   (Scalar extension `K ⊗_k -` sends a simple `k[G]`-module to a nonzero semisimple `K[G]`-module,
   and non-isomorphic simples land in modules with disjoint simple constituents, so the induced
   map on iso-classes is injective.)

`Nat.card (ConjClasses G)` is **field-independent** — it never mentions the field — so no
transfer is needed on the right-hand side, and the two bounds compose by transitivity through
`K = AlgebraicClosure k`.

## Status

Top-down scaffold. The assembly (`natCard_irrepClasses_le_conjClasses`) is proved outright from
the two lemmas below; each lemma is stated precisely and its proof is deferred to a sibling
issue:

* `natCard_irrepClasses_le_conjClasses_of_isAlgClosed` — the split-field bound (step 1); #6126.
* `natCard_irrepClasses_le_of_ringHom_field` — base-change monotonicity (step 2); #6127.
-/

open CategoryTheory

-- `[Fintype G]` is used at proof time (cocenter dimension, finiteness of the class count) but
-- not in the statement types until the deferred proofs are filled in.
set_option linter.unusedFintypeInType false

namespace Etingof

universe u v

section IsAlgClosedBound

open CocenterMonoidAlgebra SplitSimples

/-- The cocenter trace form of a standard module `Std i` reads off the matrix trace of the block
projection: `traceForm K (Std i) x = trace (blockHom i x)`. The `K[G]`-action on `Std i` is `x • v =
(blockHom i x) *ᵥ v` (`smul_Std_eq`), so under the identity identification `Std i = Fin (d i) → K`
the endomorphism `moduleEnd K (Std i) x` is `Matrix.toLin' (blockHom i x)`, whose linear-algebra
trace is the matrix trace (`Matrix.trace_toLin'_eq`). The transport across the identity linear
equivalence `e` keeps the bespoke `Std`-instances and the `Pi`-instances from clashing. -/
private lemma traceForm_Std_eq_trace {K : Type u} {G : Type v}
    [Field K] [IsAlgClosed K] [Group G] [Fintype G]
    (D : SplitData K G) (i : Fin D.n) (x : MonoidAlgebra K G) :
    traceForm K (D.Std i) x = (D.blockHom i x).trace := by
  -- The identity `K`-linear equivalence `Std i ≃ₗ (Fin (d i) → K)` (the types are defeq).
  let e : D.Std i ≃ₗ[K] (Fin (D.d i) → K) :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hconj : e.conj (moduleEnd K (D.Std i) x) = (D.blockHom i x).toLin' := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply_apply, Matrix.toLin'_apply]
    rfl
  rw [traceForm_apply, ← LinearMap.trace_conj' (moduleEnd K (D.Std i) x) e, hconj]
  exact Matrix.trace_toLin'_eq (D.blockHom i x)

/-- **Split-field bound (step 1 of the base-change route).** Over an algebraically closed field
`K`, the number of isomorphism classes of irreducible representations of a finite group `G` is at
most the number of conjugacy classes of `G`.

The semisimple quotient `K[G]/rad(K[G])` is, by Artin–Wedderburn over the algebraically closed `K`,
a product `∏ Matrix d_i(K)` of full matrix algebras (bundled as `SplitData` in
`Exercise4_2_3_SplitSimples.lean`), so the number of iso-classes of simple `K[G]`-modules equals the
number `n` of blocks (`exists_splitSimples_count`). Each block's standard module `Std i` has cocenter
trace form sending a lift of its block matrix unit `E₁₁` to `1` and the other blocks' units to `0`
(`traceForm_Std_eq_trace`), so the `n` trace forms are linearly independent functionals on the
cocenter `C = K[G]/[K[G],K[G]]`. Feeding this into
`CocenterMonoidAlgebra.card_le_conjClasses_of_traceForm_linearIndependent` gives
`n ≤ Nat.card (ConjClasses G)`. -/
theorem natCard_irrepClasses_le_conjClasses_of_isAlgClosed
    (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G] :
    Nat.card (IrrepClasses K G) ≤ Nat.card (ConjClasses G) := by
  classical
  -- The standard-module enumeration: a `SplitData` and the count `#simples = n`.
  obtain ⟨D, hD⟩ := exists_splitSimples_count K G
  rw [card_irrepClasses_eq_card_simpleModuleClasses K G, hD]
  -- The `n` block trace forms `τ_{Std i}` are linearly independent: for block `j`, a `π`-preimage
  -- `xⱼ` of the matrix unit `E₁₁` in block `j` is a dual vector with `τ_{Std i}(xⱼ) = δ_{ij}`.
  have hindep : LinearIndependent K
      (fun i => (traceFormQ K (D.Std i) : Cocenter K G →ₗ[K] K)) := by
    refine Fintype.linearIndependent_iff.mpr (fun c hc j => ?_)
    haveI := D.d_pos j
    obtain ⟨xj, hxj⟩ := D.π_surj (Pi.single j (Matrix.single (0 : Fin (D.d j)) 0 (1 : K)))
    -- `τ_{Std i}` evaluated at the class of `xⱼ` is the Kronecker delta `δ_{ij}`.
    have hval : ∀ i, traceFormQ K (D.Std i) (Submodule.mkQ (commSubmodule K G) xj)
        = if i = j then 1 else 0 := by
      intro i
      rw [traceFormQ_mkQ, traceForm_Std_eq_trace D i xj]
      have hb : D.blockHom i xj
          = (Pi.single j (Matrix.single (0 : Fin (D.d j)) 0 (1 : K))
              : ∀ i, Matrix (Fin (D.d i)) (Fin (D.d i)) K) i := by
        simp only [SplitData.blockHom, AlgHom.comp_apply, hxj, Pi.evalAlgHom_apply]
      rw [hb]
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same, Matrix.trace_single_eq_same, if_pos rfl]
      · rw [Pi.single_eq_of_ne hij, Matrix.trace_zero, if_neg hij]
    -- Evaluate the vanishing combination at that class: it collapses to `c j = 0`.
    have happ := LinearMap.congr_fun hc (Submodule.mkQ (commSubmodule K G) xj)
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, hval, smul_eq_mul, mul_ite, mul_one,
      mul_zero, LinearMap.zero_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true] using happ
  -- Feed independence into the cocenter counting bound.
  have hcard := card_le_conjClasses_of_traceForm_linearIndependent (S := fun i => D.Std i) hindep
  simpa using hcard

end IsAlgClosedBound

/-- **Base-change monotonicity (step 2 of the base-change route).** For a field extension
`K ⊇ k` (any `k`-algebra structure making `K` a field), scalar extension only increases the
number of isomorphism classes of irreducible representations:
`Nat.card (IrrepClasses k G) ≤ Nat.card (IrrepClasses K G)`.

Proof route (deferred to #6127): via the base-change algebra isomorphism
`K ⊗_k k[G] ≅ K[G]`, a simple `k[G]`-module `M` base-changes to the nonzero
finite-dimensional `K[G]`-module `K ⊗_k M`, which is semisimple; non-isomorphic simple
`k[G]`-modules produce `K[G]`-modules with disjoint sets of simple constituents (any shared
constituent would, by adjunction, force a nonzero `k[G]`-hom between the two simples). Choosing
one constituent of each `K ⊗_k M` therefore defines an injection on isomorphism classes. -/
theorem natCard_irrepClasses_le_of_ringHom_field
    (k K : Type u) (G : Type v) [Field k] [Field K] [Algebra k K] [Group G] [Fintype G] :
    Nat.card (IrrepClasses k G) ≤ Nat.card (IrrepClasses K G) := by
  sorry

/-- **Field-general counting bound (Exercise 4.2.3, counting half).** For a finite group `G` over
an arbitrary field `k`, the number of isomorphism classes of irreducible representations of `G`
over `k` is at most the number of conjugacy classes of `G`:

  `Nat.card (IrrepClasses k G) ≤ Nat.card (ConjClasses G)`.

Field-general: only `[Field k]`, no `IsAlgClosed`, no invertibility of `|G|`. Assembled by base
change to the algebraic closure `K = AlgebraicClosure k`: monotonicity of the simple count under
`k → K` (`natCard_irrepClasses_le_of_ringHom_field`) followed by the split-field bound over the
algebraically closed `K` (`natCard_irrepClasses_le_conjClasses_of_isAlgClosed`). The right-hand
side `Nat.card (ConjClasses G)` is field-independent, so the two bounds compose directly. -/
theorem natCard_irrepClasses_le_conjClasses
    (k : Type u) (G : Type v) [Field k] [Group G] [Fintype G] :
    Nat.card (IrrepClasses k G) ≤ Nat.card (ConjClasses G) :=
  (natCard_irrepClasses_le_of_ringHom_field k (AlgebraicClosure k) G).trans
    (natCard_irrepClasses_le_conjClasses_of_isAlgClosed (AlgebraicClosure k) G)

end Etingof
