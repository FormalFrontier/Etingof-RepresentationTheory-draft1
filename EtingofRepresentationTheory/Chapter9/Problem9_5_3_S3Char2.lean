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

/-! ## Block separation via the `3`-cycle class sum

The class sum `e = (123) + (132)` of the two `3`-cycles is a **central idempotent** of `k[S₃]` in
characteristic `2`. It acts as `0` on the trivial simple (each group element acts as `1`, and
`1 + 1 = 0`) and as the identity on the standard simple (on a sum-zero vector `v`,
`ρ c · v + ρ c² · v = -v = v`). The two simples therefore have different central characters and lie
in different blocks. -/

/-- A fixed `3`-cycle of `S₃`, realized as `finRotate 3` (`0 ↦ 1 ↦ 2 ↦ 0`). -/
def thc : S3 := finRotate 3

/-- The class sum `e = (123) + (132)` of the two `3`-cycles, as an element of `k[S₃]`. -/
noncomputable def eStd : MonoidAlgebra k S3 :=
  MonoidAlgebra.single thc 1 + MonoidAlgebra.single (thc ^ 2) 1

/-- `e` is idempotent: `e² = e`. The cross terms `c·c² = c²·c = 1` contribute `1 + 1 = 0`, while
`c·c = c²` and `c²·c² = c` reproduce `e`. -/
lemma eStd_isIdempotent : IsIdempotentElem (eStd k) := by
  have p1 : (thc * thc : S3) = thc ^ 2 := by rw [← sq]
  have p2 : (thc * thc ^ 2 : S3) = 1 := by decide
  have p3 : (thc ^ 2 * thc : S3) = 1 := by decide
  have p4 : (thc ^ 2 * thc ^ 2 : S3) = thc := by decide
  have h0 : MonoidAlgebra.single (1 : S3) (1 : k) + MonoidAlgebra.single (1 : S3) 1 = 0 := by
    rw [← MonoidAlgebra.single_add, CharTwo.add_self_eq_zero, MonoidAlgebra.single_zero]
  change eStd k * eStd k = eStd k
  have expand : eStd k * eStd k =
      MonoidAlgebra.single (thc * thc) (1 : k) + MonoidAlgebra.single (thc * thc ^ 2) 1
        + (MonoidAlgebra.single (thc ^ 2 * thc) 1
          + MonoidAlgebra.single (thc ^ 2 * thc ^ 2) 1) := by
    rw [eStd, add_mul, mul_add, mul_add, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single]
    simp only [mul_one]
  rw [expand, p1, p2, p3, p4, eStd]
  calc MonoidAlgebra.single (thc ^ 2) (1 : k) + MonoidAlgebra.single 1 1
          + (MonoidAlgebra.single 1 1 + MonoidAlgebra.single thc 1)
        = MonoidAlgebra.single thc 1 + MonoidAlgebra.single (thc ^ 2) 1
          + (MonoidAlgebra.single (1 : S3) 1 + MonoidAlgebra.single 1 1) := by abel
    _ = MonoidAlgebra.single thc 1 + MonoidAlgebra.single (thc ^ 2) 1 + 0 := by rw [h0]
    _ = MonoidAlgebra.single thc 1 + MonoidAlgebra.single (thc ^ 2) 1 := by rw [add_zero]

omit [CharP k 2] in
/-- `e` commutes with every `single g 1`: conjugation by `g` permutes the `3`-cycle class
`{c, c²}`, so `e` is fixed. -/
lemma eStd_comm_single (g : S3) :
    eStd k * MonoidAlgebra.single g 1 = MonoidAlgebra.single g 1 * eStd k := by
  have hcomm : ∀ g : S3,
      (thc * g = g * thc ∧ thc ^ 2 * g = g * thc ^ 2) ∨
      (thc * g = g * thc ^ 2 ∧ thc ^ 2 * g = g * thc) := by decide
  rw [eStd, add_mul, mul_add, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
  simp only [mul_one]
  rcases hcomm g with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

omit [CharP k 2] in
/-- `e` is central in `k[S₃]`. -/
lemma eStd_central (y : MonoidAlgebra k S3) : eStd k * y = y * eStd k := by
  induction y using MonoidAlgebra.induction_on with
  | hM g => rw [MonoidAlgebra.of_apply]; exact eStd_comm_single k g
  | hadd a b ha hb => rw [mul_add, add_mul, ha, hb]
  | hsmul r a ha => rw [mul_smul_comm, ha, smul_mul_assoc]

/-- `e`, packaged as a central idempotent of `k[S₃]`. -/
noncomputable def eStdCI : Etingof.Problem953.CentralIdempotent (MonoidAlgebra k S3) :=
  ⟨eStd k, eStd_isIdempotent k, eStd_central k⟩

/-- `e` acts as `0` on the trivial simple: each `g` acts as `1`, and `1 + 1 = 0` in char `2`. -/
lemma eStd_smul_triv (m : (trivRepr k).asModule) : eStd k • m = 0 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hg : ∀ g : S3, MonoidAlgebra.single g (1 : k) • m = m := by
    intro g
    rw [Representation.single_smul, one_smul, trivRepr, Representation.trivial_apply]
    rfl
  rw [eStd, add_smul, hg, hg, ← two_smul k m, h2, zero_smul]

/-- `e` acts as the identity on the standard simple: for a sum-zero vector `v`,
`v (c⁻¹ i) + v (c⁻² i) = -v i = v i` at each coordinate. -/
lemma eStd_smul_std (m : (stdRepr k).asModule) : eStd k • m = m := by
  set v : (stdSubr k).toSubmodule := m with hv
  have hsum : (v : Fin 3 → k) 0 + (v : Fin 3 → k) 1 + (v : Fin 3 → k) 2 = 0 := by
    have hm := v.2
    simpa only [stdSubr, LinearMap.mem_ker, sumLM_apply, Fin.sum_univ_three] using hm
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have key : ∀ g : S3, MonoidAlgebra.single g (1 : k) • m = stdRepr k g v := by
    intro g; rw [Representation.single_smul, one_smul]; rfl
  have coe_std : ∀ (g : S3) (i : Fin 3),
      ((stdRepr k g v : (stdSubr k).toSubmodule) : Fin 3 → k) i
        = (v : Fin 3 → k) (g⁻¹ i) := fun g i => rfl
  obtain ⟨a0, a1, a2, b0, b1, b2⟩ :
      thc⁻¹ (0 : Fin 3) = 2 ∧ thc⁻¹ (1 : Fin 3) = 0 ∧ thc⁻¹ (2 : Fin 3) = 1 ∧
      (thc ^ 2)⁻¹ (0 : Fin 3) = 1 ∧ (thc ^ 2)⁻¹ (1 : Fin 3) = 2 ∧
      (thc ^ 2)⁻¹ (2 : Fin 3) = 0 := by decide
  rw [eStd, add_smul, key, key]
  refine Subtype.ext (funext fun i => ?_)
  rw [Submodule.coe_add, Pi.add_apply, coe_std, coe_std]
  fin_cases i
  · change (v : Fin 3 → k) (thc⁻¹ 0) + (v : Fin 3 → k) ((thc ^ 2)⁻¹ 0) = (v : Fin 3 → k) 0
    rw [a0, b0]; linear_combination hsum - (v : Fin 3 → k) 0 * h2
  · change (v : Fin 3 → k) (thc⁻¹ 1) + (v : Fin 3 → k) ((thc ^ 2)⁻¹ 1) = (v : Fin 3 → k) 1
    rw [a1, b1]; linear_combination hsum - (v : Fin 3 → k) 1 * h2
  · change (v : Fin 3 → k) (thc⁻¹ 2) + (v : Fin 3 → k) ((thc ^ 2)⁻¹ 2) = (v : Fin 3 → k) 2
    rw [a2, b2]; linear_combination hsum - (v : Fin 3 → k) 2 * h2

theorem not_areLinked_triv_std :
    ¬ Etingof.AreLinked (MonoidAlgebra k S3) (trivMod k) (stdMod k) := by
  intro h
  have key := Etingof.Problem953.actsAsId_iff_of_areLinked (MonoidAlgebra k S3) (eStdCI k) h
  have hstd : ∀ m : (stdMod k : Type), (eStdCI k).1 • m = m := eStd_smul_std k
  have htriv : ∀ m : (trivMod k : Type), (eStdCI k).1 • m = m := key.mpr hstd
  haveI : Nontrivial (trivMod k : Type) := inferInstanceAs (Nontrivial k)
  obtain ⟨x, hx⟩ := exists_ne (0 : (trivMod k : Type))
  exact hx ((htriv x).symm.trans (eStd_smul_triv k x))

/-- **`k[S₃]` has exactly two blocks** in characteristic `2`: the linkage classes of simple
modules form a two-element set, represented by the trivial and standard simples. -/
theorem block_card_eq_two :
    Nat.card (Etingof.Block.{0} (MonoidAlgebra k S3)) = 2 := by
  classical
  have htriv : IsSimpleModule (MonoidAlgebra k S3) (trivMod k) := trivMod_isSimpleModule k
  have hstd : IsSimpleModule (MonoidAlgebra k S3) (stdMod k) := stdMod_isSimpleModule k
  -- The two representatives have opposite central characters at `e = (123)+(132)`.
  have cc_triv :
      Etingof.Problem953.centralCharacter (MonoidAlgebra k S3) htriv (eStdCI k) = false := by
    rw [Etingof.Problem953.centralCharacter_eq_false_iff]; exact eStd_smul_triv k
  have cc_std :
      Etingof.Problem953.centralCharacter (MonoidAlgebra k S3) hstd (eStdCI k) = true := by
    rw [Etingof.Problem953.centralCharacter_eq_true_iff]; exact eStd_smul_std k
  -- The central character is invariant under isomorphism of simples.
  have cc_iso : ∀ {X Y : ModuleCat.{0} (MonoidAlgebra k S3)}
      (hX : IsSimpleModule (MonoidAlgebra k S3) X) (hY : IsSimpleModule (MonoidAlgebra k S3) Y),
      Nonempty (X ≅ Y) →
      Etingof.Problem953.centralCharacter (MonoidAlgebra k S3) hX (eStdCI k)
        = Etingof.Problem953.centralCharacter (MonoidAlgebra k S3) hY (eStdCI k) := by
    rintro X Y hX hY ⟨e⟩
    exact Etingof.Problem953.centralCharacter_eq_of_areLinked (MonoidAlgebra k S3) hX hY _
      (Etingof.areLinked_of_iso (MonoidAlgebra k S3) hX hY e)
  -- The invariant descends to blocks: `f ⟦S⟧ = centralCharacter S`.
  set g : Etingof.SimpleObj.{0} (MonoidAlgebra k S3) → Bool := fun S =>
    Etingof.Problem953.centralCharacter (MonoidAlgebra k S3) S.2 (eStdCI k) with hg_def
  have hg : ∀ a b : Etingof.SimpleObj.{0} (MonoidAlgebra k S3),
      (Etingof.blockSetoid (MonoidAlgebra k S3)).r a b → g a = g b :=
    fun a b hab =>
      Etingof.Problem953.centralCharacter_eq_of_areLinked (MonoidAlgebra k S3) a.2 b.2 _ hab
  set f : Etingof.Block.{0} (MonoidAlgebra k S3) → Bool := Quotient.lift g hg with hf_def
  -- `f` is a bijection onto `Bool`.
  have hsurj : Function.Surjective f := by
    intro b
    cases b
    · exact ⟨Quotient.mk _ ⟨trivMod k, htriv⟩, cc_triv⟩
    · exact ⟨Quotient.mk _ ⟨stdMod k, hstd⟩, cc_std⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    refine Quotient.sound (show Etingof.AreLinked (MonoidAlgebra k S3) a.1 b.1 from ?_)
    have hab' : g a = g b := hxy
    rcases simple_iff_triv_or_std k a.1 a.2 with ha | ha <;>
      rcases simple_iff_triv_or_std k b.1 b.2 with hb | hb
    · exact Etingof.areLinked_of_iso _ a.2 b.2 (ha.some ≪≫ hb.some.symm)
    · exact absurd (((cc_iso a.2 htriv ha).trans cc_triv).symm.trans
        (hab'.trans ((cc_iso b.2 hstd hb).trans cc_std))) (by decide)
    · exact absurd (((cc_iso a.2 hstd ha).trans cc_std).symm.trans
        (hab'.trans ((cc_iso b.2 htriv hb).trans cc_triv))) (by decide)
    · exact Etingof.areLinked_of_iso _ a.2 b.2 (ha.some ≪≫ hb.some.symm)
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_bool]

/-! ### The local factor `k[S₃] → k[t]/(t²)` via the sign character

The augmentation-to-the-principal-block map sends `g ↦ 1 + sgn(g)·t`, i.e. it collapses `S₃`
through its sign to the two units `{1, 1 + t}` of `k[t]/(t²)`. The odd permutations hit the
nontrivial involution `u = 1 + t` (which squares to `1` since `t² = 0` and `2 = 0`). -/

/-- The nilpotent generator `t` of `k[t]/(t²)`, as the image of `X`. -/
noncomputable def t2gen : kt2 k := AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ 2)

/-- `t² = 0`. -/
lemma t2gen_sq : (t2gen k) ^ 2 = 0 := by
  have h : AdjoinRoot.mk ((Polynomial.X : Polynomial k) ^ 2)
      ((Polynomial.X : Polynomial k) ^ 2) = 0 := AdjoinRoot.mk_self
  rwa [map_pow, AdjoinRoot.mk_X] at h

/-- `1 + 1 = 0` in `k[t]/(t²)` (characteristic `2` passes to the algebra). -/
lemma one_add_one_kt2 : (1 : kt2 k) + 1 = 0 := by
  have hk : (1 : k) + 1 = 0 := by
    have := CharTwo.two_eq_zero (R := k); rw [← one_add_one_eq_two] at this; exact this
  rw [← map_one (algebraMap k (kt2 k)), ← map_add, hk, map_zero]

/-- The involution `u = 1 + t` squares to `1`. -/
lemma u_sq : (1 + t2gen k) * (1 + t2gen k) = 1 := by
  have ht := t2gen_sq k
  have hk := one_add_one_kt2 k
  linear_combination (t2gen k) * hk + ht

/-- The monoid hom `ℤˣ →* k[t]/(t²)` sending `-1 ↦ u = 1 + t`. -/
noncomputable def uHom : ℤˣ →* kt2 k where
  toFun s := if s = 1 then 1 else 1 + t2gen k
  map_one' := by simp
  map_mul' a b := by
    rcases Int.units_eq_one_or a with ha | ha <;> rcases Int.units_eq_one_or b with hb | hb
    · subst ha; subst hb; simp
    · subst ha; subst hb; simp [show (-1 : ℤˣ) ≠ 1 from by decide]
    · subst ha; subst hb; simp [show (-1 : ℤˣ) ≠ 1 from by decide]
    · subst ha; subst hb
      rw [show ((-1 : ℤˣ) * -1) = 1 from by decide, if_pos rfl,
        if_neg (show (-1 : ℤˣ) ≠ 1 from by decide)]
      exact (u_sq k).symm

@[simp] lemma uHom_one : uHom k 1 = 1 := by simp [uHom]

@[simp] lemma uHom_neg_one : uHom k (-1) = 1 + t2gen k := by
  show (if (-1 : ℤˣ) = 1 then (1 : kt2 k) else 1 + t2gen k) = 1 + t2gen k
  rw [if_neg (show (-1 : ℤˣ) ≠ 1 from by decide)]

/-- The sign character of `S₃`, valued in `{1, 1 + t} ⊆ k[t]/(t²)`. -/
noncomputable def sgnHom : S3 →* kt2 k := (uHom k).comp (Equiv.Perm.sign)

/-- The **local-factor projection** `k[S₃] → k[t]/(t²)`, `g ↦ 1 + sgn(g)·t`. -/
noncomputable def psi : MonoidAlgebra k S3 →ₐ[k] kt2 k :=
  MonoidAlgebra.lift k (kt2 k) S3 (sgnHom k)

@[simp] lemma psi_single (g : S3) :
    psi k (MonoidAlgebra.single g 1) = uHom k (Equiv.Perm.sign g) := by
  rw [psi, MonoidAlgebra.lift_single, one_smul]; rfl

/-- `psi` is surjective: its image contains `t`, and `k[t]/(t²)` is generated by `t`. -/
lemma psi_surjective : Function.Surjective (psi k) := by
  intro y
  have hmem : y ∈ (⊤ : Subalgebra k (kt2 k)) := Algebra.mem_top
  rw [← AdjoinRoot.adjoinRoot_eq_top (f := (Polynomial.X : Polynomial k) ^ 2)] at hmem
  have hle : Algebra.adjoin k {AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ 2)}
      ≤ (psi k).range := by
    rw [Algebra.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    show t2gen k ∈ (psi k).range
    have ht1 : (1 + t2gen k) ∈ (psi k).range :=
      (psi k).mem_range.mpr ⟨MonoidAlgebra.single (Equiv.swap 0 1) 1, by
        rw [psi_single, Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 by decide), uHom_neg_one]⟩
    have hsub := sub_mem ht1 (one_mem (psi k).range)
    simpa using hsub
  obtain ⟨x, hx⟩ := hle hmem
  exact ⟨x, hx⟩

/-! ### The matrix factor `k[S₃] → M₂(k)` via the standard representation

The standard `2`-dimensional representation gives an algebra map `k[S₃] → End_k(V) ≅ M₂(k)`. We
coordinatize `V = {v : Fin 3 → k | ∑ vᵢ = 0}` by `v ↦ (v 0, v 2)` (the middle coordinate is
forced: `v 1 = v 0 + v 2` in characteristic `2`), turning each group element into an explicit
`2×2` matrix. The six matrices span `M₂(k)`, so the map is surjective. -/

/-- Coordinatization `V ≃ k²`, `v ↦ (v 0, v 2)`. In characteristic `2`, `v 1 = v 0 + v 2` on the
sum-zero subspace, so the inverse sends `(a, b) ↦ (a, a + b, b)`. -/
def coordEquiv : (stdSubr k).toSubmodule ≃ₗ[k] (Fin 2 → k) where
  toFun v := ![(v : Fin 3 → k) 0, (v : Fin 3 → k) 2]
  map_add' a b := by
    ext i; fin_cases i <;> simp [Submodule.coe_add]
  map_smul' r a := by
    ext i; fin_cases i <;> simp [Submodule.coe_smul]
  invFun c := ⟨![c 0, c 0 + c 1, c 1], by
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    simp only [stdSubr, LinearMap.mem_ker, sumLM_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    linear_combination (c 0 + c 1) * h2⟩
  left_inv v := by
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    have hv : (v : Fin 3 → k) 0 + (v : Fin 3 → k) 1 + (v : Fin 3 → k) 2 = 0 := by
      have := v.2
      simpa only [stdSubr, LinearMap.mem_ker, sumLM_apply, Fin.sum_univ_three] using this
    apply Subtype.ext; funext i; fin_cases i
    · rfl
    · show (v : Fin 3 → k) 0 + (v : Fin 3 → k) 2 = (v : Fin 3 → k) 1
      linear_combination hv - (v : Fin 3 → k) 1 * h2
    · rfl
  right_inv c := by
    funext i; fin_cases i <;> rfl

@[simp] lemma coordEquiv_apply_zero (v : (stdSubr k).toSubmodule) :
    coordEquiv k v 0 = (v : Fin 3 → k) 0 := rfl

@[simp] lemma coordEquiv_apply_one (v : (stdSubr k).toSubmodule) :
    coordEquiv k v 1 = (v : Fin 3 → k) 2 := rfl

/-- The coordinate basis of `V` induced by `coordEquiv`. -/
noncomputable def bV : Module.Basis (Fin 2) k (stdSubr k).toSubmodule :=
  Module.Basis.ofEquivFun (coordEquiv k)

/-- The **matrix-factor map** `k[S₃] → M₂(k)`, the standard representation in coordinates. -/
noncomputable def rhoStd : MonoidAlgebra k S3 →ₐ[k] Matrix (Fin 2) (Fin 2) k :=
  (LinearMap.toMatrixAlgEquiv (bV k)).toAlgHom.comp (stdRepr k).asAlgebraHom

lemma rhoStd_single (g : S3) :
    rhoStd k (MonoidAlgebra.single g 1) = LinearMap.toMatrix (bV k) (bV k) (stdRepr k g) := by
  rw [rhoStd, AlgHom.comp_apply, Representation.asAlgebraHom_single, one_smul]
  rfl

/-- Entry formula: `rhoStd (single g 1) i j = (g · bⱼ)` read in coordinate `i`. -/
lemma rhoStd_entry (g : S3) (i j : Fin 2) :
    rhoStd k (MonoidAlgebra.single g 1) i j
      = coordEquiv k (stdRepr k g ((coordEquiv k).symm (Pi.single j 1))) i := by
  rw [rhoStd_single, LinearMap.toMatrix_apply]
  simp only [bV, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]

@[simp] lemma coordEquiv_symm_val (c : Fin 2 → k) :
    (((coordEquiv k).symm c : (stdSubr k).toSubmodule) : Fin 3 → k) = ![c 0, c 0 + c 1, c 1] := rfl

lemma rhoStd_one : rhoStd k (MonoidAlgebra.single (1 : S3) 1) = 1 := by
  ext i j
  rw [rhoStd_entry, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply,
    Pi.single_apply, Matrix.one_apply]

lemma rhoStd_thc : rhoStd k (MonoidAlgebra.single thc 1) = !![0, 1; 1, 1] := by
  have e0 : thc⁻¹ (0 : Fin 3) = 2 := by decide
  have e2 : thc⁻¹ (2 : Fin 3) = 1 := by decide
  ext i j
  rw [rhoStd_entry]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2]

lemma rhoStd_swap01 : rhoStd k (MonoidAlgebra.single (Equiv.swap 0 1) 1) = !![1, 1; 0, 1] := by
  have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  ext i j
  rw [rhoStd_entry]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2]

lemma rhoStd_swap02 : rhoStd k (MonoidAlgebra.single (Equiv.swap 0 2) 1) = !![0, 1; 1, 0] := by
  have e0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  ext i j
  rw [rhoStd_entry]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2]

/-- The six group matrices span `M₂(k)`, so `rhoStd` is **surjective**. The four matrix units are
`k`-combinations of `ρ(1), ρ((123)), ρ((01)), ρ((02))` (in characteristic `2`, using `-1 = 1`). -/
lemma rhoStd_surjective : Function.Surjective (rhoStd k) := by
  have m1 : (1 : Matrix (Fin 2) (Fin 2) k) ∈ (rhoStd k).range :=
    rhoStd_one k ▸ (rhoStd k).mem_range_self _
  have mA : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) k) ∈ (rhoStd k).range :=
    rhoStd_thc k ▸ (rhoStd k).mem_range_self _
  have mC : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) ∈ (rhoStd k).range :=
    rhoStd_swap01 k ▸ (rhoStd k).mem_range_self _
  have mE : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) k) ∈ (rhoStd k).range :=
    rhoStd_swap02 k ▸ (rhoStd k).mem_range_self _
  have u00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k) ∈ (rhoStd k).range := by
    have h : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k)
        = 1 + !![0, 1; 1, 1] + !![0, 1; 1, 0] := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [Matrix.single_apply, Matrix.one_apply, CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem (add_mem m1 mA) mE
  have u01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k) ∈ (rhoStd k).range := by
    have h : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k) = !![1, 1; 0, 1] + 1 := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [Matrix.single_apply, Matrix.one_apply, CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem mC m1
  have u10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : k) ∈ (rhoStd k).range := by
    have h : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : k)
        = !![0, 1; 1, 0] + !![1, 1; 0, 1] + 1 := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [Matrix.single_apply, Matrix.one_apply, CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem (add_mem mE mC) m1
  have u11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : k) ∈ (rhoStd k).range := by
    have h : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : k) = !![0, 1; 1, 1] + !![0, 1; 1, 0] := by
      ext a b; fin_cases a <;> fin_cases b <;>
        simp [Matrix.single_apply, Matrix.one_apply, CharTwo.add_self_eq_zero]
    rw [h]; exact add_mem mA mE
  have huniv : ∀ (i j : Fin 2) (x : k), Matrix.single i j x ∈ (rhoStd k).range := by
    intro i j x
    have hsmul : Matrix.single i j x = x • Matrix.single i j (1 : k) := by
      ext a b; simp [Matrix.single_apply, Matrix.smul_apply, mul_ite, mul_one, mul_zero]
    rw [hsmul]
    refine Subalgebra.smul_mem _ ?_ x
    fin_cases i <;> fin_cases j <;> assumption
  intro m
  refine (rhoStd k).mem_range.mp ?_
  rw [Matrix.matrix_eq_sum_single m]
  exact sum_mem fun i _ => sum_mem fun j _ => huniv i j (m i j)

lemma rhoStd_thc_sq : rhoStd k (MonoidAlgebra.single (thc ^ 2) 1) = !![1, 1; 1, 0] := by
  have e0 : (thc ^ 2)⁻¹ (0 : Fin 3) = 1 := by decide
  have e2 : (thc ^ 2)⁻¹ (2 : Fin 3) = 0 := by decide
  ext i j
  rw [rhoStd_entry]
  fin_cases i <;> fin_cases j <;>
    simp [stdRepr_val, e0, e2, -map_pow]

/-! ### Compatibilities of the two factors with the central idempotent -/

/-- `rhoStd` sends the central idempotent `e = (123) + (132)` to the identity matrix (both
`3`-cycle matrices sum to the identity in characteristic `2`). -/
lemma rhoStd_eStd : rhoStd k (eStd k) = 1 := by
  rw [eStd]
  simp only [map_add, rhoStd_thc, rhoStd_thc_sq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.one_apply, CharTwo.add_self_eq_zero]

/-- `psi` sends `e = (123) + (132)` to `0` (both `3`-cycles are even). -/
lemma psi_eStd : psi k (eStd k) = 0 := by
  have hs1 : Equiv.Perm.sign thc = 1 := by decide
  have hs2 : Equiv.Perm.sign (thc ^ 2) = 1 := by decide
  rw [eStd]
  simp only [map_add, psi_single, hs1, hs2, uHom_one]
  exact one_add_one_kt2 k

/-- **The block decomposition of `k[S₃]` in characteristic `2`:**
`k[S₃] ≅ M₂(k) × k[t]/(t²)` as `k`-algebras. The matrix factor `M₂(k)` (dimension `4`) is the
defect-`0` block carrying the standard simple; the local factor `k[t]/(t²)` (dimension `2`) is the
principal block carrying the trivial simple. Dimensions check: `4 + 2 = 6 = |S₃|`. -/
theorem algebra_decomposition :
    Nonempty (MonoidAlgebra k S3 ≃ₐ[k] Matrix (Fin 2) (Fin 2) k × kt2 k) := by
  sorry

end Etingof.Problem953.S3Char2
