import Mathlib
import EtingofRepresentationTheory.Chapter9.Definition9_5_1
import EtingofRepresentationTheory.Chapter9.Problem9_5_3

/-!
# Problem 9.5.3 (iii): the blocks of `k[S₃]` in characteristic `2`

This file discharges part **(iii)** of Etingof Problem 9.5.3 (deferred by
`Problem9_5_3.lean`): *determine the blocks of the category of left `A`-modules for
`A = k[S₃]` with `char k = 2`*.

## The answer (Etingof's modular computation)

`|S₃| = 6 = 2 · 3`, so in characteristic `2` the group algebra `k[S₃]` is **not** semisimple
(the prime `2` divides the group order) and the Sylow `2`-subgroup has order `2`. There are
exactly two `2`-regular (odd-order) conjugacy classes of `S₃`, namely `{e}` and `{(123),(132)}`,
so over a splitting field of characteristic `2` there are exactly **two** simple `k[S₃]`-modules:

* the **trivial** simple, `1`-dimensional — in characteristic `2` the sign representation
  collapses onto the trivial one (`-1 = 1`), so the two char-`0` lines fuse into a single simple;
* the **standard** simple, `2`-dimensional — it stays irreducible because `3` is invertible, and
  it is the sum-zero subrepresentation of the permutation representation on `Fin 3 → k`.

The standard simple has dimension `2 = |Syl₂(S₃)|`, hence is **projective**: it is a block of
**defect `0`**, contributing a matrix factor `M₂(k)` of dimension `4`. The remaining
**principal block** has dimension `6 − 4 = 2`; it is the local algebra `k[t]/(t²) ≅ k[C₂]`, whose
unique simple is the trivial module. Altogether

  `k[S₃] ≅ M₂(k) × k[t]/(t²)`  (as `k`-algebras),

so `k[S₃]` has exactly two blocks, represented by the trivial and standard simples, and these two
simples are **not** `Etingof.AreLinked`.

## Status

This is a faithful **statement pass**. All module and algebra *data* below are constructed
genuinely (no `sorry` in any `def`): the trivial and standard representations are real objects,
built over an arbitrary field of characteristic `2` by generalizing the char-`0` `S₃` catalogue in
`Chapter4/Example4_3_S3.lean` off `ℂ`. The classification *theorems* — simplicity of the two
modules, the non-linkage that separates the two blocks, the block count, and the algebra
decomposition — are stated faithfully with `sorry` proofs; discharging them (in particular the
algebra isomorphism `k[S₃] ≅ M₂(k) × k[t]/(t²)` via the two central idempotents) is left to a
follow-up. See the block framework in `Definition9_5_1.lean` and `Problem9_5_3.lean` for the
`Etingof.Block` / `Etingof.AreLinked` machinery reused here.
-/

open CategoryTheory
open scoped MonoidAlgebra

namespace Etingof.Problem953.S3Char2

/-- `S₃`, realized as the symmetric group on `Fin 3`. -/
abbrev S3 : Type := Equiv.Perm (Fin 3)

variable (k : Type) [Field k] [CharP k 2]

/-! ## Genuine module data

The two simple `k[S₃]`-modules, over an arbitrary field `k` of characteristic `2`. These are the
char-`2` analogues of `trivRep` and `stdRep` from `Chapter4/Example4_3_S3.lean`, built here off a
general base field rather than `ℂ`. -/

/-- The **trivial** representation of `S₃` on `k`: every permutation acts as the identity. -/
def trivRepr : Representation k S3 k := Representation.trivial k S3 k

/-- The **permutation** representation of `S₃` on `Fin 3 → k`: `σ` acts by `f ↦ f ∘ σ⁻¹`. -/
def permRepr : Representation k S3 (Fin 3 → k) where
  toFun σ := LinearMap.funLeft k k (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

omit [CharP k 2] in
@[simp] lemma permRepr_apply (σ : S3) (f : Fin 3 → k) (i : Fin 3) :
    permRepr k σ f i = f (σ⁻¹ i) := rfl

/-- The sum map `(Fin 3 → k) →ₗ[k] k`, `f ↦ ∑ i, f i`. -/
def sumLM : (Fin 3 → k) →ₗ[k] k := ∑ i, LinearMap.proj i

omit [CharP k 2] in
@[simp] lemma sumLM_apply (f : Fin 3 → k) : sumLM k f = ∑ i, f i := by
  simp [sumLM, Finset.sum_apply]

/-- The **standard** representation as the sum-zero subrepresentation of `permRepr`. In
characteristic `2` the all-ones vector is *not* sum-zero (`1 + 1 + 1 = 3 = 1 ≠ 0`), so this is a
genuine `2`-dimensional complement, and it is irreducible because `3` is invertible. -/
def stdSubr : Subrepresentation (permRepr k) where
  toSubmodule := LinearMap.ker (sumLM k)
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, sumLM_apply] at hf ⊢
    calc ∑ i, permRepr k σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [permRepr_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 3)) f
      _ = 0 := hf

/-- The standard (`2`-dimensional) representation `k²` of `S₃`. -/
def stdRepr : Representation k S3 (stdSubr k).toSubmodule := (stdSubr k).toRepresentation

/-! ### The two simples as `k[S₃]`-modules

Via `Representation.asModule`, each representation becomes a genuine module over
`A = k[S₃] = MonoidAlgebra k S₃`, i.e. an object of `ModuleCat A`. These are the block
representatives. -/

/-- The trivial simple as an object of `ModuleCat (k[S₃])`. -/
noncomputable def trivMod : ModuleCat (MonoidAlgebra k S3) :=
  ModuleCat.of (MonoidAlgebra k S3) (trivRepr k).asModule

/-- The standard simple as an object of `ModuleCat (k[S₃])`. -/
noncomputable def stdMod : ModuleCat (MonoidAlgebra k S3) :=
  ModuleCat.of (MonoidAlgebra k S3) (stdRepr k).asModule

/-! ### The two-block algebra `M₂(k) × k[t]/(t²)` -/

/-- The local algebra `k[t]/(t²)`, the principal block of `k[S₃]` in characteristic `2`. -/
abbrev kt2 : Type := Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}

/-! ## The classification (statement pass; proofs deferred) -/

/-- **The trivial module is simple.** In characteristic `2`, `triv = sign`, so the two char-`0`
one-dimensional simples collapse to this single simple `k[S₃]`-module. -/
theorem trivMod_isSimpleModule : IsSimpleModule (MonoidAlgebra k S3) (trivRepr k).asModule :=
  { toIsSimpleOrder := is_simple_module_of_finrank_eq_one (K := k)
      (by rw [(trivRepr k).asModuleEquiv.finrank_eq, Module.finrank_self]) }

/-- **The standard module is simple.** The `2`-dimensional standard representation stays
irreducible in characteristic `2` because `3` is invertible. -/
theorem stdMod_isSimpleModule : IsSimpleModule (MonoidAlgebra k S3) (stdRepr k).asModule := by
  sorry

/-- **Exactly two simples.** `S₃` has two `2`-regular classes (`{e}` and `{(123),(132)}`), so over
a splitting field of characteristic `2` there are exactly two isomorphism classes of simple
`k[S₃]`-modules: the trivial one and the standard one, and every simple is one of these. -/
theorem simple_iff_triv_or_std (S : ModuleCat.{0} (MonoidAlgebra k S3))
    (hS : IsSimpleModule (MonoidAlgebra k S3) S) :
    Nonempty (S ≅ trivMod k) ∨ Nonempty (S ≅ stdMod k) := by
  sorry

/-- **The two blocks are distinct.** The trivial and standard simples are *not* linked, so they
lie in different blocks — the principal block and a defect-`0` block respectively. This is exactly
the statement that `k[S₃]` has (at least) two blocks. -/
theorem not_areLinked_triv_std :
    ¬ Etingof.AreLinked (MonoidAlgebra k S3) (trivMod k) (stdMod k) := by
  sorry

/-- **`k[S₃]` has exactly two blocks** in characteristic `2`: the linkage classes of simple
modules form a two-element set, represented by the trivial and standard simples. -/
theorem block_card_eq_two :
    Nat.card (Etingof.Block.{0} (MonoidAlgebra k S3)) = 2 := by
  sorry

/-- **The block decomposition of `k[S₃]` in characteristic `2`:**
`k[S₃] ≅ M₂(k) × k[t]/(t²)` as `k`-algebras. The matrix factor `M₂(k)` (dimension `4`) is the
defect-`0` block carrying the standard simple; the local factor `k[t]/(t²)` (dimension `2`) is the
principal block carrying the trivial simple. Dimensions check: `4 + 2 = 6 = |S₃|`. -/
theorem algebra_decomposition :
    Nonempty (MonoidAlgebra k S3 ≃ₐ[k] Matrix (Fin 2) (Fin 2) k × kt2 k) := by
  sorry

end Etingof.Problem953.S3Char2
