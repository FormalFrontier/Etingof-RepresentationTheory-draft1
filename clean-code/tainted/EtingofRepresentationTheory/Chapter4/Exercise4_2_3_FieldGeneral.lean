import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_CountingBound
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_SplitSimples
import EtingofRepresentationTheory.Chapter4.SimpleModuleClassesBaseChange
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_SemisimpleBaseChange

/-!
# Field-general counting bound `#(simple k[G]-modules) ≤ #ConjClasses` (Exercise 4.2.3)

This file proves the upper bound

  `Nat.card (IrrepClasses k G) ≤ Nat.card (ConjClasses G)`

for the number of isomorphism classes of irreducible representations of a finite group `G`
over an arbitrary field `k` (only `[Field k]`; no `IsAlgClosed`, no invertibility of
`|G|`). It is the counting half of Exercise 4.2.3, in the indexing used downstream
(`IrrepClasses k G`, from `Exercise4_2_3.lean`); the `≤` here upgrades to the strict `<` of
`Exercise4_2_3` in the modular case, where a nonzero central nilpotent forces the drop.

## Why a base change is needed

Over a non-splitting field an individual cocenter trace form `τ_{S_i}` of a simple module
can be identically zero (`char k` dividing a Schur index, or an inseparable centre), so the
naive hypothesis that the trace forms `τ_{S_i}` are `LinearIndependent`, required by
`CocenterMonoidAlgebra.card_le_conjClasses_of_traceForm_linearIndependent`
(`Exercise4_2_3_CountingBound.lean`), is false in general. The standard fix is to pass to a
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

`Nat.card (ConjClasses G)` is field-independent (it never mentions the field), so no transfer
is needed on the right-hand side, and the two bounds compose by transitivity through
`K = AlgebraicClosure k`. The two lemmas are:

* `natCard_irrepClasses_le_conjClasses_of_isAlgClosed`: the split-field bound (step 1);
* `natCard_irrepClasses_le_of_ringHom_field`: base-change monotonicity (step 2).
-/

open CategoryTheory
open scoped TensorProduct

-- `[Fintype G]` is used at proof time (cocenter dimension, finiteness of the class count) but
-- not in the statement types.
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

/-- The `n` block cocenter trace forms `τ_{Std i}` of a `SplitData` are linearly independent
functionals on the cocenter `C = K[G]/[K[G],K[G]]`. For block `j`, a `π`-preimage `xⱼ` of the
matrix unit `E₁₁` in block `j` is a dual vector reading off the Kronecker delta:
`τ_{Std i}(x̄ⱼ) = δ_{ij}` (`traceForm_Std_eq_trace` plus `Matrix.trace_single_eq_same`). This is
the independence input shared by both the split-field `≤` bound
(`natCard_irrepClasses_le_conjClasses_of_isAlgClosed`) and its strict `<` counterpart in the
modular case (`natCard_irrepClasses_lt_conjClasses_of_isAlgClosed`, in
`Exercise4_2_3_Assembly.lean`). -/
theorem traceFormQ_Std_linearIndependent {K : Type u} {G : Type v}
    [Field K] [IsAlgClosed K] [Group G] [Fintype G] (D : SplitData K G) :
    LinearIndependent K (fun i => (traceFormQ K (D.Std i) : Cocenter K G →ₗ[K] K)) := by
  classical
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

/-- **Split-field bound (step 1 of the base-change argument).** Over an algebraically closed field
`K`, the number of isomorphism classes of irreducible representations of a finite group `G` is at
most the number of conjugacy classes of `G`.

The semisimple quotient `K[G]/rad(K[G])` is, by Artin–Wedderburn over the algebraically closed `K`,
a product `∏ Matrix d_i(K)` of full matrix algebras (bundled as `SplitData` in
`Exercise4_2_3_SplitSimples.lean`), so the number of iso-classes of simple `K[G]`-modules equals the
number `n` of blocks (`exists_splitSimples_count`). Each block's standard module `Std i` has cocenter
trace form sending a lift of its block matrix unit `E₁₁` to `1` and the other blocks' units to `0`
(`traceForm_Std_eq_trace`), so the `n` trace forms are linearly independent functionals on the
cocenter `C = K[G]/[K[G],K[G]]`. Applying
`CocenterMonoidAlgebra.card_le_conjClasses_of_traceForm_linearIndependent` gives
`n ≤ Nat.card (ConjClasses G)`. -/
theorem natCard_irrepClasses_le_conjClasses_of_isAlgClosed
    (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G] :
    Nat.card (IrrepClasses K G) ≤ Nat.card (ConjClasses G) := by
  classical
  -- The standard-module enumeration: a `SplitData` and the count `#simples = n`.
  obtain ⟨D, hD⟩ := exists_splitSimples_count K G
  rw [card_irrepClasses_eq_card_simpleModuleClasses K G, hD]
  -- Apply the cocenter counting bound to the independence of the `n` block trace forms.
  have hcard := card_le_conjClasses_of_traceForm_linearIndependent (S := fun i => D.Std i)
    (traceFormQ_Std_linearIndependent D)
  simpa using hcard

end IsAlgClosedBound

/-- **Base-change monotonicity (step 2 of the base-change argument).** For a field extension
`K ⊇ k` (any `k`-algebra structure making `K` a field), scalar extension only increases the
number of isomorphism classes of irreducible representations:
`Nat.card (IrrepClasses k G) ≤ Nat.card (IrrepClasses K G)`.

Separability-free proof, via the radical-quotient chain on the simple-module counts
(`IrrepClasses k G` and `SimpleModuleClasses (k[G])` are in bijection by
`card_irrepClasses_eq_card_simpleModuleClasses`):
```
#simple(k[G]) = #simple(k[G]/rad)          -- radical-quotient invariance
             ≤ #simple(K ⊗_k (k[G]/rad))   -- semisimple base-change count (the main step)
             ≤ #simple(K[G]).              -- surjection K[G] ↠ K ⊗_k (k[G]/rad)
```
The first step is `natCard_simpleModuleClasses_quotient_jacobson`; the middle is the main step
`natCard_simpleModuleClasses_le_baseChange_of_isSemisimpleRing` (`k[G]/rad` is semisimple); the
last is `natCard_simpleModuleClasses_le_of_surjective` applied to the surjective `K`-algebra map
`K[G] ↠ K ⊗_k (k[G]/rad)` built here by lifting `g ↦ 1 ⊗ mk (single g 1)`. The group `G` shares
the fields' universe (as in `Exercise4_2_3`), so `k[G]`, `K[G]` and `k[G]/rad` all live in
`Type u`, matching the base-change lemmas. -/
theorem natCard_irrepClasses_le_of_ringHom_field
    (k K G : Type u) [Field k] [Field K] [Algebra k K] [Group G] [Fintype G] :
    Nat.card (IrrepClasses k G) ≤ Nat.card (IrrepClasses K G) := by
  classical
  -- Finiteness of the two group algebras over their base fields.
  haveI : Module.Finite k (MonoidAlgebra k G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G k)
  haveI : Module.Finite K (MonoidAlgebra K G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G K)
  -- The semisimple radical quotient `A = k[G]/rad(k[G])`.
  set J : Ideal (MonoidAlgebra k G) := Ring.jacobson (MonoidAlgebra k G) with hJ
  haveI : IsArtinianRing (MonoidAlgebra k G) := IsArtinianRing.of_finite k (MonoidAlgebra k G)
  haveI : IsSemiprimaryRing (MonoidAlgebra k G) := inferInstance
  haveI : IsSemisimpleRing (MonoidAlgebra k G ⧸ J) := IsSemiprimaryRing.isSemisimpleRing
  haveI : Module.Finite k (MonoidAlgebra k G ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k J).toLinearMap
      Ideal.Quotient.mk_surjective
  -- The base-changed algebra `K ⊗_k A` and the surjection `K[G] ↠ K ⊗_k A`.
  -- `ψ : k[G] →ₐ[k] K ⊗_k A` sends `p ↦ 1 ⊗ mk p`.
  set ψ : MonoidAlgebra k G →ₐ[k] K ⊗[k] (MonoidAlgebra k G ⧸ J) :=
    (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ k J) with hψ
  -- `φ : K[G] →ₐ[K] K ⊗_k A` is the `K`-linear extension of `g ↦ 1 ⊗ mk (single g 1)`.
  set mh : G →* K ⊗[k] (MonoidAlgebra k G ⧸ J) :=
    ψ.toRingHom.toMonoidHom.comp (MonoidAlgebra.of k G) with hmh
  set φ : MonoidAlgebra K G →ₐ[K] K ⊗[k] (MonoidAlgebra k G ⧸ J) :=
    MonoidAlgebra.lift K (K ⊗[k] (MonoidAlgebra k G ⧸ J)) G mh with hφ
  -- Coefficient-extension algebra hom `ι : k[G] →ₐ[k] K[G]`.
  set ι : MonoidAlgebra k G →ₐ[k] MonoidAlgebra K G :=
    MonoidAlgebra.lift k (MonoidAlgebra K G) G (MonoidAlgebra.of K G) with hι
  -- `φ ∘ ι = ψ`: both are `k`-algebra maps `k[G] → K ⊗_k A`, agreeing on group elements.
  have hcomp : (φ.restrictScalars k).comp ι = ψ := by
    refine MonoidAlgebra.algHom_ext (M := G) (fun g => ?_) ?_
    · have hιg : ι (MonoidAlgebra.single g (1 : k)) = MonoidAlgebra.single g (1 : K) := by
        rw [hι, MonoidAlgebra.lift_single, one_smul, MonoidAlgebra.of_apply]
      have hφg : φ (MonoidAlgebra.single g (1 : K)) =
          ψ (MonoidAlgebra.single g (1 : k)) := by
        rw [hφ, MonoidAlgebra.lift_single, one_smul, hmh, MonoidHom.coe_comp,
          Function.comp_apply, MonoidAlgebra.of_apply]
        rfl
      rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hιg, hφg]
    · ext
  -- Every pure tensor `1 ⊗ x` is in the range of `φ` (via `ι` on a lift of `x`).
  have hone : ∀ x : MonoidAlgebra k G ⧸ J, (1 : K) ⊗ₜ[k] x ∈ φ.range := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨ι p, ?_⟩
    change φ (ι p) = (1 : K) ⊗ₜ[k] Ideal.Quotient.mk J p
    have := AlgHom.congr_fun hcomp p
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [this, hψ, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Ideal.Quotient.mkₐ_eq_mk]
  -- `φ` is surjective: its range is a `K`-subalgebra containing every `1 ⊗ x`, hence all `a ⊗ x`.
  have hsurj : Function.Surjective (φ : MonoidAlgebra K G → K ⊗[k] (MonoidAlgebra k G ⧸ J)) := by
    rw [← AlgHom.range_eq_top, eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a x =>
        have hax : a ⊗ₜ[k] x = a • ((1 : K) ⊗ₜ[k] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hax]
        exact Subalgebra.smul_mem φ.range (hone x) a
    | add x y hx hy => exact add_mem hx hy
  -- Assemble the count chain, converting both ends to simple-module class counts.
  rw [card_irrepClasses_eq_card_simpleModuleClasses k G,
      card_irrepClasses_eq_card_simpleModuleClasses K G]
  calc Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra k G))
      = Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra k G ⧸ J)) :=
        (natCard_simpleModuleClasses_quotient_jacobson k).symm
    _ ≤ Nat.card (SimpleModuleClasses.{u} (K ⊗[k] (MonoidAlgebra k G ⧸ J))) :=
        natCard_simpleModuleClasses_le_baseChange_of_isSemisimpleRing k K
    _ ≤ Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra K G)) :=
        natCard_simpleModuleClasses_le_of_surjective K φ.toRingHom hsurj

/-- **Field-general counting bound (Exercise 4.2.3, counting half).** For a finite group `G` over
an arbitrary field `k`, the number of isomorphism classes of irreducible representations of `G`
over `k` is at most the number of conjugacy classes of `G`:

  `Nat.card (IrrepClasses k G) ≤ Nat.card (ConjClasses G)`.

Field-general: only `[Field k]`, no `IsAlgClosed`, no invertibility of `|G|`. Proved by base
change to the algebraic closure `K = AlgebraicClosure k`: monotonicity of the simple count under
`k → K` (`natCard_irrepClasses_le_of_ringHom_field`) followed by the split-field bound over the
algebraically closed `K` (`natCard_irrepClasses_le_conjClasses_of_isAlgClosed`). The right-hand
side `Nat.card (ConjClasses G)` is field-independent, so the two bounds compose directly. -/
theorem natCard_irrepClasses_le_conjClasses
    (k G : Type u) [Field k] [Group G] [Fintype G] :
    Nat.card (IrrepClasses k G) ≤ Nat.card (ConjClasses G) :=
  (natCard_irrepClasses_le_of_ringHom_field k (AlgebraicClosure k) G).trans
    (natCard_irrepClasses_le_conjClasses_of_isAlgClosed (AlgebraicClosure k) G)

end Etingof
