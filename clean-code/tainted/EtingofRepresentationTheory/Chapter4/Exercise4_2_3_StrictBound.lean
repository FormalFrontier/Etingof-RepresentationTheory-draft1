import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_CountingBound

/-!
# The strict counting drop in the modular case (Exercise 4.2.3)

In the modular case (`|G| = 0` in `k`) the counting bound
`#(simple k[G]-modules) ≤ #ConjClasses` sharpens to a strict inequality
`#(simple k[G]-modules) < #ConjClasses`. This file establishes that strict drop, in parallel
with the non-strict bound in `Exercise4_2_3_CountingBound.lean`.

The mechanism is the nonzero central nilpotent `P = ∑_{g} g` (`Etingof.groupSum`, from
`Exercise4_2_3.lean`). Write `P̄` for its image in the cocenter `C = k[G] / [k[G], k[G]]`.

* **`groupSum_mkQ_ne_zero`.** `P̄ ≠ 0` in `C`: the class-coefficient functional
  `classCoeffQ` sends `P̄` to the indicator of the identity conjugacy class, whose value at
  `{1}` is `1 ≠ 0`.
* **`traceForm_groupSum_eq_zero`.** For a simple finite-dimensional
  `k[G]`-module `M`, the trace form annihilates `P`: `τ_M(P̄) = trace(P acting on M) = 0`. The
  action of the central element `P` is a `k[G]`-linear endomorphism `e` of `M` with `e² = 0`
  (as `P² = 0`), so by simplicity (its kernel is `⊥` or `⊤`) `e = 0`, hence its trace vanishes.
* **`card_lt_finrank_of_linearIndependent_of_apply_eq_zero`.** A `LinearIndependent` family of
  functionals on a finite-dimensional space that all vanish at a common nonzero vector `v` has
  strictly fewer members than `finrank`: adjoining a functional `g` with `g v ≠ 0` keeps the
  family independent, so its size `+1 ≤ finrank`.
* **`card_lt_conjClasses_of_traceForm_linearIndependent`.** Combining the three facts above: if
  the cocenter trace forms of a finite family of simple finite-dimensional `k[G]`-modules are
  linearly independent and `|G| = 0` in `k`, then the family has strictly fewer than
  `Nat.card (ConjClasses G)` members. All of them annihilate the nonzero vector `P̄`, so they
  lie in a hyperplane of `C`.

These are all field-general (only `[Field k]`). The remaining, field-sensitive content,
producing a linearly independent family of trace forms of size `Nat.card (IrrepClasses k G)`,
holds after base change to a splitting field and is handled in
`Exercise4_2_3_FieldGeneral.lean` (via the split-field bound and base-change monotonicity). Once
that family is available over a splitting field, applying
`card_lt_conjClasses_of_traceForm_linearIndependent` yields the strict bound there, and base
change transports it back to `k` to close `Etingof.Exercise4_2_3`.
-/

open MonoidAlgebra

-- `[Fintype G]`/`[DecidableEq G]` are used at proof time (class-coefficient functionals, cocenter
-- dimension) but not in the statement types.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Etingof

namespace CocenterMonoidAlgebra

variable {k G : Type*} [Field k] [Group G] [Fintype G]

/-! ### `P̄ ≠ 0` in the cocenter -/

/-- The image `P̄` of the group sum `P = ∑_g g` in the cocenter
`C = k[G] / [k[G], k[G]]` is nonzero. The class-coefficient functional `classCoeffQ` sends `P̄`
to the coordinate function of conjugacy classes; its value at the identity class `{1}` is `1`
(only `g = 1` is conjugate to `1`), so `P̄` cannot be zero. Field-general. -/
theorem groupSum_mkQ_ne_zero [DecidableEq G] :
    (Submodule.mkQ (commSubmodule k G) (groupSum k G) : Cocenter k G) ≠ 0 := by
  intro h
  have hcc : classCoeff k G (groupSum k G) = 0 := by
    have hq : classCoeffQ k G (Submodule.mkQ (commSubmodule k G) (groupSum k G)) = 0 := by
      rw [h, map_zero]
    rwa [classCoeffQ, Submodule.mkQ_apply, Submodule.liftQ_apply] at hq
  have hval : classCoeff k G (groupSum k G) (ConjClasses.mk 1) = 1 := by
    simp only [classCoeff, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single (1 : G)]
    · rw [if_pos rfl, groupSum_apply]
    · intro b _ hb
      rw [if_neg]
      intro hmk
      exact hb (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hmk))
    · intro hb; exact absurd (Finset.mem_univ 1) hb
  rw [hcc, Pi.zero_apply] at hval
  exact zero_ne_one hval

/-! ### The trace form annihilates `P` on every simple module -/

section SimpleModule

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M] [Module.Finite k M]
  [IsSimpleModule (MonoidAlgebra k G) M]

/-- The action of the central element `P = ∑_g g` on a `k[G]`-module `M`, as a
`k[G]`-linear endomorphism `e : M →ₗ[k[G]] M`, `m ↦ P • m`. It is `k[G]`-linear precisely
because `P` is central (`groupSum_mem_center`). -/
private noncomputable def groupSumEnd : M →ₗ[MonoidAlgebra k G] M where
  toFun m := groupSum k G • m
  map_add' a b := smul_add _ _ _
  map_smul' y m := by
    change groupSum k G • (y • m) = y • (groupSum k G • m)
    rw [smul_smul, smul_smul, Subalgebra.mem_center_iff.mp groupSum_mem_center y]

omit [Module.Finite k M] in
/-- For a simple finite-dimensional `k[G]`-module `M` in the modular case
(`|G| = 0` in `k`), the trace form of `M` vanishes on `P = ∑_g g`, i.e. the character value of
`P` on `M` is `0`. The central nilpotent `P` acts by a `k[G]`-endomorphism `e` with `e² = 0`;
by simplicity `e = 0`, so its trace is `0`. Field-general. -/
theorem traceForm_groupSum_eq_zero (hcard : (Fintype.card G : k) = 0) :
    traceForm k M (groupSum k G) = 0 := by
  -- `e = (P • ·)` squares to zero because `P² = 0`.
  have hee : ∀ m : M, groupSum k G • (groupSum k G • m) = 0 := fun m => by
    rw [smul_smul, groupSum_mul_self hcard, zero_smul]
  -- By simplicity, `ker e` is `⊥` or `⊤`; either way `e = 0`.
  have hzero : ∀ m : M, groupSum k G • m = 0 := by
    let e := groupSumEnd (k := k) (G := G) M
    rcases eq_bot_or_eq_top (LinearMap.ker e) with hk | hk
    · -- `ker e = ⊥`: `e` is injective, and `e (e m) = 0 = e 0` forces `e m = 0`.
      have hinj : Function.Injective e := LinearMap.ker_eq_bot.mp hk
      intro m
      have hm : e (e m) = e 0 := by rw [map_zero]; exact hee m
      exact hinj hm
    · -- `ker e = ⊤`: every `m` is in the kernel, so `e m = 0`.
      intro m
      exact LinearMap.mem_ker.mp (hk ▸ Submodule.mem_top)
  have hend : moduleEnd k M (groupSum k G) = 0 := by
    ext m
    rw [moduleEnd_apply, LinearMap.zero_apply]
    exact hzero m
  rw [traceForm_apply, hend, map_zero]

end SimpleModule

/-! ### The strict counting bound -/

/-- **Linear-algebra core.** A `LinearIndependent` family `f` of linear
functionals on a finite-dimensional vector space `V`, all of which vanish at a common **nonzero**
vector `v`, has strictly fewer members than `finrank k V`. Adjoining a functional `g` with
`g v ≠ 0` (which exists since `v ≠ 0`) keeps the family linearly independent, so its cardinality
plus one is at most `finrank k V`. -/
theorem card_lt_finrank_of_linearIndependent_of_apply_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] [Fintype ι]
    {f : ι → (V →ₗ[k] k)} (hf : LinearIndependent k f) {v : V} (hv : v ≠ 0)
    (h0 : ∀ i, f i v = 0) :
    Fintype.card ι < Module.finrank k V := by
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero k hv
  -- Extend `f` by `g` over `Option ι`.
  set F : Option ι → (V →ₗ[k] k) := fun o => o.elim g f with hF
  have hFind : LinearIndependent k F := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    -- Evaluate `∑ o, c o • F o = 0` at `v`; all `f i v = 0`, leaving `c none * g v = 0`.
    have hcv : ∑ o : Option ι, c o * (F o) v = 0 := by
      have h2 : (∑ o : Option ι, c o • F o) v = 0 := by rw [hc, LinearMap.zero_apply]
      simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        using h2
    rw [Fintype.sum_option] at hcv
    simp only [hF, Option.elim_none, Option.elim_some, h0, mul_zero, Finset.sum_const_zero,
      add_zero] at hcv
    have hnone : c none = 0 := by
      rcases mul_eq_zero.mp hcv with h | h
      · exact h
      · exact absurd h hg
    -- With `c none = 0`, independence of `f` gives `c (some i) = 0` for all `i`.
    have hsome : ∀ i, c (some i) = 0 := by
      have hsum : ∑ i, c (some i) • f i = 0 := by
        have h3 := hc
        rw [Fintype.sum_option] at h3
        simpa only [hF, Option.elim_none, Option.elim_some, hnone, zero_smul, zero_add]
          using h3
      exact fun i => Fintype.linearIndependent_iff.mp hf (fun i => c (some i)) hsum i
    rintro (_ | i)
    · exact hnone
    · exact hsome i
  have hcard : Fintype.card (Option ι) ≤ Module.finrank k (V →ₗ[k] k) :=
    hFind.fintype_card_le_finrank
  rw [Module.finrank_linearMap_self, Fintype.card_option] at hcard
  omega

/-- **Strict counting bound.** In the modular case (`|G| = 0` in `k`),
if the cocenter trace forms `τ_{S i}` of a finite family of simple finite-dimensional
`k[G]`-modules `S i` are linearly independent over `k`, then the family has **strictly** fewer
than `Nat.card (ConjClasses G)` members. All the trace forms annihilate the nonzero cocenter
vector `P̄` (`traceForm_groupSum_eq_zero`, `groupSum_mkQ_ne_zero`), so they span a subspace of the
hyperplane `{φ | φ(P̄) = 0}` of dimension `finrank k C - 1 = Nat.card (ConjClasses G) - 1`.

This is the strict counterpart of
`card_le_conjClasses_of_traceForm_linearIndependent`; specialised to the family of all
non-isomorphic simple `k[G]`-modules (over a splitting field, where their trace forms are
independent) it gives `#(simple k[G]-modules) < Nat.card (ConjClasses G)`. -/
theorem card_lt_conjClasses_of_traceForm_linearIndependent [DecidableEq G]
    {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module (MonoidAlgebra k G) (S i)] [∀ i, IsScalarTower k (MonoidAlgebra k G) (S i)]
    [∀ i, Module.Finite k (S i)] [∀ i, IsSimpleModule (MonoidAlgebra k G) (S i)]
    (hcard : (Fintype.card G : k) = 0)
    (h : LinearIndependent k (fun i => (traceFormQ k (S i) : Cocenter k G →ₗ[k] k))) :
    Fintype.card ι < Nat.card (ConjClasses G) := by
  have h0 : ∀ i, (traceFormQ k (S i)) (Submodule.mkQ (commSubmodule k G) (groupSum k G)) = 0 :=
    fun i => by rw [traceFormQ_mkQ]; exact traceForm_groupSum_eq_zero (S i) hcard
  have hlt := card_lt_finrank_of_linearIndependent_of_apply_eq_zero h
    (groupSum_mkQ_ne_zero (k := k) (G := G)) h0
  rwa [finrank_cocenter_eq_card_conjClasses] at hlt

end CocenterMonoidAlgebra

end Etingof
