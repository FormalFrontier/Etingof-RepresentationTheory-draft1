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

omit [CharP k 2] in
/-- **The trivial module is simple.** In characteristic `2`, `triv = sign`, so the two char-`0`
one-dimensional simples collapse to this single simple `k[S₃]`-module. -/
theorem trivMod_isSimpleModule : IsSimpleModule (MonoidAlgebra k S3) (trivRepr k).asModule :=
  { toIsSimpleOrder := is_simple_module_of_finrank_eq_one (K := k)
      (by rw [(trivRepr k).asModuleEquiv.finrank_eq, Module.finrank_self]) }

omit [CharP k 2] in
open Module in
/-- The underlying vector of `stdRepr k g x` is `permRepr k g` applied to the underlying vector. -/
private lemma stdRepr_val (g : S3) (x : ↥(stdSubr k).toSubmodule) :
    ((stdRepr k g x : ↥(stdSubr k).toSubmodule) : Fin 3 → k) = permRepr k g (x : Fin 3 → k) :=
  rfl

open Module in
/-- The standard representation is `2`-dimensional. -/
private lemma finrank_stdSub : finrank k ↥(stdSubr k).toSubmodule = 2 := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have hpi : finrank k (Fin 3 → k) = 3 := by
    simp
  have hrange : finrank k ↥(LinearMap.range (sumLM k)) = 1 := by
    have hr : LinearMap.range (sumLM k) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨Pi.single 0 c, by simp [sumLM_apply, Finset.sum_pi_single']⟩
    rw [hr, finrank_top, Module.finrank_self]
  have hsum := LinearMap.finrank_range_add_finrank_ker (sumLM k)
  rw [hrange, hpi] at hsum
  -- `hsum : 1 + finrank ↥(ker (sumLM k)) = 3`
  change finrank k ↥(LinearMap.ker (sumLM k)) = 2
  omega

/-- **The standard module is simple.** The `2`-dimensional standard representation stays
irreducible in characteristic `2` because `3` is invertible. -/
theorem stdMod_isSimpleModule : IsSimpleModule (MonoidAlgebra k S3) (stdRepr k).asModule := by
  classical
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  set V := ↥(stdSubr k).toSubmodule with hV
  have hdimV : Module.finrank k V = 2 := finrank_stdSub k
  -- Nontriviality of the carrier: `![1,1,0]` is a nonzero sum-zero vector.
  have hnt : Nontrivial V := by
    refine ⟨⟨![1, 1, 0], ?_⟩, 0, ?_⟩
    · have hmem : ![1, 1, 0] ∈ LinearMap.ker (sumLM k) := by
        rw [LinearMap.mem_ker, sumLM_apply, Fin.sum_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, add_zero]
        rw [one_add_one_eq_two, h2]
      exact hmem
    · intro h
      have := congrArg (fun x : V => (x : Fin 3 → k) 0) h
      simp only [Matrix.cons_val_zero, ZeroMemClass.coe_zero, Pi.zero_apply] at this
      exact one_ne_zero this
  haveI : Nontrivial V := hnt
  -- reduce to `IsSimpleOrder` of the lattice of invariant submodules
  suffices hSO : IsSimpleOrder (stdRepr k).invtSubmodule by
    exact { toIsSimpleOrder := (stdRepr k).mapSubmodule.isSimpleOrder_iff.mp hSO }
  refine ⟨fun a => ?_⟩
  -- invariance of `a`
  have hinv : ∀ (g : S3) (x : V), x ∈ (a : Submodule k V) → stdRepr k g x ∈ (a : Submodule k V) :=
    fun g => (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (stdRepr k g)).mp
      ((stdRepr k).mem_invtSubmodule.mp a.2 g)
  rcases eq_or_ne (a : Submodule k V) ⊥ with hbot | hbot
  · left; exact Subtype.ext (hbot.trans (Representation.invtSubmodule.coe_bot _).symm)
  -- `a ≠ ⊥`: pick a nonzero `w ∈ a`
  obtain ⟨w, hw_mem, hw_ne⟩ := (Submodule.ne_bot_iff _).mp hbot
  right
  refine Subtype.ext ?_
  rw [Representation.invtSubmodule.coe_top]
  -- Two independent vectors in `a` force `a = ⊤`.
  have topOfIndep : ∀ u : V, u ∈ (a : Submodule k V) → u ∉ Submodule.span k {w} →
      (a : Submodule k V) = ⊤ := by
    intro u hu hunotin
    by_contra htop
    have hlt : (a : Submodule k V) < ⊤ := lt_of_le_of_ne le_top htop
    have hfa : Module.finrank k ↥(a : Submodule k V) < 2 := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rwa [finrank_top, hdimV] at this
    have hwle : Submodule.span k {w} ≤ (a : Submodule k V) :=
      (Submodule.span_singleton_le_iff_mem w _).mpr hw_mem
    have h1 : Module.finrank k ↥(Submodule.span k {w}) = 1 := finrank_span_singleton hw_ne
    have hmono := Submodule.finrank_mono hwle
    rw [h1] at hmono
    have hfa1 : Module.finrank k ↥(a : Submodule k V) = 1 := by omega
    have hspaneq : Submodule.span k {w} = (a : Submodule k V) :=
      Submodule.eq_of_le_of_finrank_eq hwle (by rw [h1, hfa1])
    rw [← hspaneq] at hu
    exact hunotin hu
  -- For an involution `s`, if `stdRepr s w` lies on the line `k·w`, then it fixes `w`.
  have key : ∀ (s : S3), s * s = 1 → stdRepr k s w ∈ Submodule.span k {w} →
      stdRepr k s w = w := by
    intro s hs hmem
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
    -- `stdRepr s (stdRepr s w) = w`
    have hss : stdRepr k s (stdRepr k s w) = w := by
      have hmm : stdRepr k (s * s) = stdRepr k s * stdRepr k s := map_mul _ _ _
      rw [hs, map_one] at hmm
      have := LinearMap.congr_fun hmm.symm w
      simpa [Module.End.mul_apply] using this
    -- `μ² • w = w`
    have e1 : stdRepr k s (stdRepr k s w) = (μ * μ) • w := by
      conv_lhs => rw [← hμ]
      rw [map_smul, ← hμ, smul_smul]
    rw [hss] at e1
    -- `μ = 1` in characteristic `2`
    have hmuw : (μ * μ) • w = w := e1.symm
    have hmm : μ * μ = 1 := by
      have hz : ((μ * μ) - 1) • w = 0 := by rw [sub_smul, one_smul, hmuw, sub_self]
      rcases smul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hw_ne
    have hsq : (μ - 1) * (μ - 1) = 0 := by linear_combination hmm + (1 - μ) * h2
    have hμ1 : μ = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
    rw [← hμ, hμ1, one_smul]
  -- Case analysis on whether `swap 0 1` and `swap 1 2` move `w` off the line.
  by_cases hτ : stdRepr k (Equiv.swap (0 : Fin 3) 1) w ∈ Submodule.span k {w}
  · by_cases hτ' : stdRepr k (Equiv.swap (1 : Fin 3) 2) w ∈ Submodule.span k {w}
    · -- both fix `w` ⟹ `w` is constant ⟹ `w = 0`, contradiction
      exfalso
      have hfτ : stdRepr k (Equiv.swap (0 : Fin 3) 1) w = w := key _ (by decide) hτ
      have hfτ' : stdRepr k (Equiv.swap (1 : Fin 3) 2) w = w := key _ (by decide) hτ'
      -- underlying vector equations
      have e0 : permRepr k (Equiv.swap (0 : Fin 3) 1) (w : Fin 3 → k) = (w : Fin 3 → k) := by
        rw [← stdRepr_val]; exact congrArg (fun x : V => (x : Fin 3 → k)) hfτ
      have e1' : permRepr k (Equiv.swap (1 : Fin 3) 2) (w : Fin 3 → k) = (w : Fin 3 → k) := by
        rw [← stdRepr_val]; exact congrArg (fun x : V => (x : Fin 3 → k)) hfτ'
      have h01 : (w : Fin 3 → k) 1 = (w : Fin 3 → k) 0 := by
        have := congr_fun e0 0
        rwa [permRepr_apply, show (Equiv.swap (0 : Fin 3) 1)⁻¹ 0 = 1 from by decide] at this
      have h12 : (w : Fin 3 → k) 2 = (w : Fin 3 → k) 1 := by
        have := congr_fun e1' 1
        rwa [permRepr_apply, show (Equiv.swap (1 : Fin 3) 2)⁻¹ 1 = 2 from by decide] at this
      -- sum-zero forces `w = 0`
      have hz : sumLM k (w : Fin 3 → k) = 0 := w.2
      rw [sumLM_apply, Fin.sum_univ_three, h12, h01] at hz
      -- `w 0 + w 0 + w 0 = w 0 = 0`
      have hw0 : (w : Fin 3 → k) 0 = 0 := by
        have hsum3 : (w : Fin 3 → k) 0 + (w : Fin 3 → k) 0 + (w : Fin 3 → k) 0 = 0 := hz
        linear_combination hsum3 - (w : Fin 3 → k) 0 * h2
      have hw1 : (w : Fin 3 → k) 1 = 0 := h01.trans hw0
      have hw2 : (w : Fin 3 → k) 2 = 0 := h12.trans hw1
      apply hw_ne
      refine Subtype.ext ?_
      rw [ZeroMemClass.coe_zero]
      funext i
      simp only [Pi.zero_apply]
      fin_cases i
      · exact hw0
      · exact hw1
      · exact hw2
    · exact topOfIndep _ (hinv _ w hw_mem) hτ'
  · exact topOfIndep _ (hinv _ w hw_mem) hτ

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
