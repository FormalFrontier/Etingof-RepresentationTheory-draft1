import EtingofRepresentationTheory.Chapter2.Problem2_7_4
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Problem 2.7.4(c): classification of the irreducible Weyl-algebra modules in characteristic `p`

`Problem2_7_4.lean` proves (`Etingof.Problem2_7_4.finrank_irreducible_charP`) that over an
algebraically closed field `k` of characteristic `p` every finite dimensional irreducible module
over the Weyl algebra `A = Etingof.WeylAlgebra k` has dimension exactly `p`. That is a dimension
statement, not a classification. This file constructs the family that does the classifying and
proves it is a complete, irredundant list: `existsUnique_toFamEquiv` says every finite
dimensional irreducible `A`-module is isomorphic to exactly one member of the family.

## The family

The book's model is `k[t]/(t^p - α)` with `x` acting by multiplication by `t` and `y` acting by
`d/dt + c`. Concretely, on `Fin p → k` with standard basis `e₀, …, e_{p-1}` (thought of as
`1, t, …, t^{p-1}`) we take

* `x` acting as the twisted cyclic shift `Xlin α`: `x·eⱼ = e_{j+1}` for `j < p-1`, and
  `x·e_{p-1} = α·e₀`;
* `y` acting as `Ylin c`: `y·eⱼ = j·e_{j-1} + c·eⱼ`.

These satisfy the defining relation `y x = x y + 1` (`famRel`), so by the universal property of
`WeylAlgebra k` they make `Fin p → k` into an `A`-module `V(α,c)` (`famModule`).

The central elements `xᵖ` and `yᵖ` (Problem 2.7.4(b)) act on `V(α,c)` by the scalars `α` and `cᵖ`
respectively (`Xlin_pow_char`, `Ylin_pow_char`); the pair `(α, cᵖ)` is the *central character* of
`V(α,c)`. Since `k` is algebraically closed of characteristic `p` the Frobenius `c ↦ cᵖ` is a
bijection (`exists_unique_pow_char`), so `(α, c) ↦ (α, cᵖ)` parameterizes all central characters
exactly once.

## Main definitions and results

* `Etingof.Problem2_7_4.Xlin` / `Ylin` — the operators realizing `x` and `y`.
* `Etingof.Problem2_7_4.famRel` — the defining relation `Ylin ∘ Xlin = Xlin ∘ Ylin + 1`.
* `Etingof.Problem2_7_4.famRep` — the induced algebra map `WeylAlgebra k →ₐ[k] End k (Fin p → k)`.
* `Etingof.Problem2_7_4.famModule` — the `A`-module `V(α,c)`, of dimension `p`.
* `Etingof.Problem2_7_4.Xlin_pow_char` / `Ylin_pow_char` — the central-scalar actions
  `Xᵖ = α·1`, `Yᵖ = cᵖ·1`.
* `Etingof.Problem2_7_4.exists_unique_pow_char` — every central character `(α, β)` is `(α, cᵖ)`
  for a unique `c`.
* `Etingof.Problem2_7_4.famModule_isSimpleModule` — `V(α,c)` is irreducible, for every `α` and
  `c` (including `α = 0`, where `x` acts nilpotently).
* `Etingof.Problem2_7_4.FamEquiv` — the type of `WeylAlgebra k`-linear equivalences
  `V(α,c) ≃ V(α',c')`.
* `Etingof.Problem2_7_4.famEquiv_nonempty_iff` — the isomorphism criterion
  `V(α,c) ≅ V(α',c') ↔ α = α' ∧ c = c'`, so the family lists each isomorphism class at most once.
* `Etingof.Problem2_7_4.exists_toFamEquiv` — exhaustiveness: every finite dimensional irreducible
  `A`-module is isomorphic to some `V(α,c)`, so the family lists each isomorphism class at least
  once.
* `Etingof.Problem2_7_4.existsUnique_toFamEquiv` — the classification endpoint: the parameter pair
  `(α, c)` of an irreducible module exists and is unique.
* `Etingof.Problem2_7_4.finrank_eq_of_classification` — the book's dimension answer `dim V = p`
  read back off the classification.
-/

namespace Etingof.Problem2_7_4

open Etingof Finset
open scoped Fin.NatCast

section Family

variable (k : Type*) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]

private lemma p_pos : 0 < p := (Fact.out : p.Prime).pos

/-- A prime characteristic parameter is nonzero. -/
instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-! ### The twisted cyclic shift `x` -/

/-- The weight of the twisted shift `x` at index `j`: `α` when the shift wraps around (`j = 0`),
otherwise `1`. -/
def wX (α : k) (j : Fin p) : k := if j = 0 then α else 1

/-- The twisted cyclic shift operator `x`: `(x·f) j = wX j · f (j-1)`, i.e. `x·eⱼ = e_{j+1}` for
`j < p-1` and `x·e_{p-1} = α·e₀`. -/
def Xlin (α : k) : (Fin p → k) →ₗ[k] (Fin p → k) where
  toFun f := fun j => wX k p α j * f (j - 1)
  map_add' f g := by funext j; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [CharP k p] in
/-- The twisted shift at coordinate `j` uses the weight at `j` and the preceding coordinate. -/
@[simp] theorem Xlin_apply (α : k) (f : Fin p → k) (j : Fin p) :
    Xlin k p α f j = wX k p α j * f (j - 1) := rfl

/-! ### The operator `y` -/

/-- The lowering weight of `y` at index `j`: the image of `j+1` in `k`, so that
`y·eⱼ = j·e_{j-1} + c·eⱼ`. Note that it vanishes at `j = p-1`, which is what makes the
cyclic wraparound harmless. -/
def wY (j : Fin p) : k := (((j + 1 : Fin p) : ℕ) : k)

/-- The operator `y`: `(y·f) j = c · f j + wY j · f (j+1)`. -/
def Ylin (c : k) : (Fin p → k) →ₗ[k] (Fin p → k) where
  toFun f := fun j => c * f j + wY k p j * f (j + 1)
  map_add' f g := by funext j; simp only [Pi.add_apply]; ring
  map_smul' a f := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [CharP k p] in
/-- At coordinate `j`, `Ylin` is the sum of the scalar and cyclic lowering terms. -/
@[simp] theorem Ylin_apply (c : k) (f : Fin p → k) (j : Fin p) :
    Ylin k p c f j = c * f j + wY k p j * f (j + 1) := rfl

/-- In characteristic `p` the cyclic weight `wY j` is just `j + 1`. -/
theorem wY_eq (j : Fin p) : wY k p j = ((j : ℕ) : k) + 1 := by
  have h1 : ((1 : Fin p) : ℕ) ≡ 1 [MOD p] := by
    rw [Fin.val_one']; exact Nat.mod_modEq 1 p
  have h : ((j + 1 : Fin p) : ℕ) ≡ (j : ℕ) + 1 [MOD p] := by
    rw [Fin.val_add]
    exact (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ h1)
  have := (CharP.natCast_eq_natCast k p).mpr h
  rw [wY, this]; push_cast; ring

omit [CharP k p] in
/-- The weight of `y` one step down: `wY (j-1) = j`. -/
theorem wY_pred (j : Fin p) : wY k p (j - 1) = ((j : ℕ) : k) := by
  rw [wY, sub_add_cancel]

/-! ### The defining relation -/

omit [CharP k p] in
/-- Wraparound absorption for `x` above `y`: the factor `wX (j+1)` is invisible because `wY j`
vanishes exactly where `wX (j+1)` is nontrivial. -/
theorem wY_mul_wX_succ (α : k) (j : Fin p) :
    wY k p j * wX k p α (j + 1) = wY k p j := by
  by_cases h : j + 1 = 0
  · rw [wY, h]; simp
  · rw [wX, if_neg h, mul_one]

omit [CharP k p] in
/-- Wraparound absorption for `y` below `x`: the factor `wX j` is invisible because `wY (j-1)`
vanishes exactly where `wX j` is nontrivial. -/
theorem wX_mul_wY_pred (α : k) (j : Fin p) :
    wX k p α j * wY k p (j - 1) = wY k p (j - 1) := by
  by_cases h : j = 0
  · rw [wY_pred, h]; simp
  · rw [wX, if_neg h, one_mul]

/-- **Defining relation of the family.** The operators `Ylin c` and `Xlin α` satisfy
`y x = x y + 1`, the defining relation of `WeylAlgebra k`. -/
theorem famRel (α c : k) :
    Ylin k p c * Xlin k p α = Xlin k p α * Ylin k p c + 1 := by
  refine LinearMap.ext fun f => ?_
  funext j
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, Pi.add_apply,
    Xlin_apply, Ylin_apply, add_sub_cancel_right]
  have hX : wY k p j * wX k p α (j + 1) = wY k p j := wY_mul_wX_succ k p α j
  have hY : wX k p α j * wY k p (j - 1) = wY k p (j - 1) := wX_mul_wY_pred k p α j
  have hw : wY k p j = wY k p (j - 1) + 1 := by rw [wY_eq, wY_pred]
  rw [sub_add_cancel]
  linear_combination (f j) * hX - (f j) * hY + (f j) * hw

/-! ### The module `V(α,c)` -/

/-- Generator assignment: `x ↦ Xlin α`, `y ↦ Ylin c`. -/
private def famRepGen (α c : k) : Fin 2 → Module.End k (Fin p → k) :=
  ![Xlin k p α, Ylin k p c]

private noncomputable def famRepFree (α c : k) :
    FreeAlgebra k (Fin 2) →ₐ[k] Module.End k (Fin p → k) :=
  FreeAlgebra.lift k (famRepGen k p α c)

private lemma famRep_rel (α c : k) :
    ∀ ⦃a b⦄, WeylAlgebraRel k a b → famRepFree k p α c a = famRepFree k p α c b := by
  intro a b ⟨ha, hb⟩
  subst ha; subst hb
  simp only [famRepFree, map_mul, map_add, map_one, FreeAlgebra.lift_ι_apply, famRepGen,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact famRel k p α c

/-- The representation of `WeylAlgebra k` on `Fin p → k` sending `x` to the twisted cyclic shift
`Xlin α` and `y` to `Ylin c`. This is the book's `k[t]/(t^p - α)` with `y` acting by `d/dt + c`. -/
noncomputable def famRep (α c : k) : WeylAlgebra k →ₐ[k] Module.End k (Fin p → k) :=
  RingQuot.liftAlgHom k ⟨famRepFree k p α c, famRep_rel k p α c⟩

/-- The family representation sends the Weyl generator `x` to the twisted shift. -/
@[simp] theorem famRep_x (α c : k) : famRep k p α c (WeylAlgebra.x k) = Xlin k p α := by
  simp [famRep, WeylAlgebra.x, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply, famRepFree,
    FreeAlgebra.lift_ι_apply, famRepGen]

/-- The family representation sends the Weyl generator `y` to the lowering operator. -/
@[simp] theorem famRep_y (α c : k) : famRep k p α c (WeylAlgebra.y k) = Ylin k p c := by
  simp [famRep, WeylAlgebra.y, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply, famRepFree,
    FreeAlgebra.lift_ι_apply, famRepGen]

/-- The classifying module `V(α,c)`: the `WeylAlgebra k`-module structure on `Fin p → k`
determined by `x ↦ Xlin α`, `y ↦ Ylin c`. -/
@[reducible] noncomputable def famModule (α c : k) : Module (WeylAlgebra k) (Fin p → k) :=
  Module.compHom (Fin p → k) (famRep k p α c).toRingHom

/-- Scalar action in the family module is evaluation of the family representation. -/
theorem famModule_smul (α c : k) (a : WeylAlgebra k) (f : Fin p → k) :
    letI := famModule k p α c
    a • f = famRep k p α c a f := rfl

/-- `V(α,c)` is compatible with the ambient `k`-action, so it is a representation in the sense
used by `Problem2_7_4.lean`. -/
theorem famModule_isScalarTower (α c : k) :
    letI := famModule k p α c
    IsScalarTower k (WeylAlgebra k) (Fin p → k) := by
  letI := famModule k p α c
  refine ⟨fun a b f => ?_⟩
  change famRep k p α c (a • b) f = a • (famRep k p α c b f)
  rw [map_smul, LinearMap.smul_apply]

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- `V(α,c)` has dimension `p` over `k`. -/
theorem famModule_finrank : Module.finrank k (Fin p → k) = p := by simp

/-! ### The central-scalar actions `xᵖ = α`, `yᵖ = cᵖ` -/

omit [CharP k p] in
private theorem Xlin_pow_apply (α : k) (m : ℕ) (f : Fin p → k) (j : Fin p) :
    (Xlin k p α ^ m) f j
      = (∏ t ∈ range m, wX k p α (j - (t : Fin p))) * f (j - ((m : ℕ) : Fin p)) := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    have hshift : ∀ t : ℕ, j - ((t + 1 : ℕ) : Fin p) = (j - 1) - (t : Fin p) := by
      intro t; rw [Nat.cast_add_one]; abel
    have hprod : ∏ t ∈ range (m + 1), wX k p α (j - (t : Fin p))
        = wX k p α j * ∏ t ∈ range m, wX k p α ((j - 1) - (t : Fin p)) := by
      rw [Finset.prod_range_succ', Finset.prod_congr rfl (fun t _ => by rw [hshift t] :
        ∀ t ∈ range m, wX k p α (j - ((t + 1 : ℕ) : Fin p))
          = wX k p α ((j - 1) - (t : Fin p)))]
      simp only [Nat.cast_zero, sub_zero]
      ring
    rw [pow_succ', Module.End.mul_apply, Xlin_apply, ih (j - 1), hprod, hshift m]
    ring

omit [CharP k p] in
/-- `Xᵖ` acts on `V(α,c)` by the scalar `α`: this is the central character value of `xᵖ`. -/
theorem Xlin_pow_char (α : k) : Xlin k p α ^ p = α • 1 := by
  refine LinearMap.ext fun f => ?_
  funext j
  rw [Xlin_pow_apply]
  have hself : j - ((p : ℕ) : Fin p) = j := by simp
  rw [hself, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  have hsingle : ∀ t ∈ range p, t ≠ (j : ℕ) → wX k p α (j - (t : Fin p)) = 1 := by
    intro t ht hne
    have hlt : t < p := Finset.mem_range.mp ht
    have hne' : j - (t : Fin p) ≠ 0 := by
      intro h
      apply hne
      have hjt : (t : Fin p) = j := by rw [sub_eq_zero] at h; exact h.symm
      have := congrArg Fin.val hjt
      rwa [Fin.val_cast_of_lt hlt] at this
    rw [wX, if_neg hne']
  rw [Finset.prod_eq_single_of_mem ((j : ℕ)) (Finset.mem_range.mpr j.isLt) hsingle,
    Fin.cast_val_eq_self, sub_self, wX, if_pos rfl]

omit [CharP k p] in
private theorem Ylin_zero_pow_apply (m : ℕ) (f : Fin p → k) (j : Fin p) :
    (Ylin k p 0 ^ m) f j
      = (∏ t ∈ range m, wY k p (j + (t : Fin p))) * f (j + ((m : ℕ) : Fin p)) := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    have hshift : ∀ t : ℕ, j + ((t + 1 : ℕ) : Fin p) = (j + 1) + (t : Fin p) := by
      intro t; rw [Nat.cast_add_one]; abel
    have hprod : ∏ t ∈ range (m + 1), wY k p (j + (t : Fin p))
        = wY k p j * ∏ t ∈ range m, wY k p ((j + 1) + (t : Fin p)) := by
      rw [Finset.prod_range_succ', Finset.prod_congr rfl (fun t _ => by rw [hshift t] :
        ∀ t ∈ range m, wY k p (j + ((t + 1 : ℕ) : Fin p))
          = wY k p ((j + 1) + (t : Fin p)))]
      simp only [Nat.cast_zero, add_zero]
      ring
    rw [pow_succ', Module.End.mul_apply, Ylin_apply, ih (j + 1), hprod, hshift m]
    ring

omit [CharP k p] in
/-- The `c = 0` operator is nilpotent, which is what makes `yᵖ` a scalar. -/
theorem Ylin_zero_pow_char : Ylin k p 0 ^ p = 0 := by
  refine LinearMap.ext fun f => ?_
  funext j
  rw [Ylin_zero_pow_apply]
  have hzero : ∏ t ∈ range p, wY k p (j + (t : Fin p)) = 0 := by
    refine Finset.prod_eq_zero (i := ((((-1 : Fin p) - j : Fin p) : ℕ)))
      (Finset.mem_range.mpr (Fin.isLt _)) ?_
    have harg : j + (((((-1 : Fin p) - j : Fin p) : ℕ) : Fin p)) + 1 = 0 := by
      rw [Fin.cast_val_eq_self]; abel
    simp only [wY, harg]
    simp
  rw [hzero]
  simp

/-- `Yᵖ` acts on `V(α,c)` by the scalar `cᵖ`: this is the central character value of `yᵖ`. -/
theorem Ylin_pow_char (c : k) : Ylin k p c ^ p = (c ^ p) • 1 := by
  have hsplit : Ylin k p c = c • (1 : Module.End k (Fin p → k)) + Ylin k p 0 := by
    refine LinearMap.ext fun f => ?_
    funext j
    simp only [Ylin_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add]
  haveI : Nontrivial (Fin p → k) := by
    haveI : Nonempty (Fin p) := ⟨⟨0, p_pos p⟩⟩
    infer_instance
  haveI : CharP (Module.End k (Fin p → k)) p :=
    charP_of_injective_algebraMap (algebraMap k (Module.End k (Fin p → k))).injective p
  haveI : ExpChar (Module.End k (Fin p → k)) p := ExpChar.prime Fact.out
  have hcomm : Commute (c • (1 : Module.End k (Fin p → k))) (Ylin k p 0) :=
    (Commute.one_left (Ylin k p 0)).smul_left c
  rw [hsplit, add_pow_char_of_commute p hcomm, Ylin_zero_pow_char, add_zero,
    smul_pow, one_pow]

/-! ### Irreducibility of `V(α,c)`

The book's argument, in these coordinates: let `f ≠ 0` and let `m` be the largest index with
`f m ≠ 0`. Applying `y - c` (which acts by `Ylin 0`) exactly `m` times collapses `f` onto
`m! · f m · e₀`, and `m!` is invertible because `m < p`. Then `x^i` carries `e₀` to `eᵢ`,
so the submodule generated by `f` is all of `V(α,c)`. Note that this works for every `α`,
including `α = 0` where `x` is nilpotent: the wraparound scalar `α` is never reached.
-/

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- A nonzero vector of `Fin p → k` has a largest index at which it is nonzero. -/
private lemma exists_top_index (f : Fin p → k) (hf : f ≠ 0) :
    ∃ m : Fin p, f m ≠ 0 ∧ ∀ j, m < j → f j = 0 := by
  classical
  have hne : (Finset.univ.filter fun j : Fin p => f j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hf
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by simpa using hj⟩⟩
  refine ⟨_, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2, fun j hj => ?_⟩
  by_contra h0
  exact absurd (Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h0⟩))
    (not_le.mpr hj)

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- Rescaling a standard basis vector. -/
private lemma smul_single_one (a : k) (j : Fin p) :
    a • Pi.single j (1 : k) = Pi.single j a := by
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

/-- **Lowering to the bottom.** If `m` is the largest index at which `f` is nonzero, then
`m` applications of the nilpotent operator `Ylin 0` collapse `f` onto the multiple
`m! · f m` of the bottom basis vector `e₀`.

At index `0` the accumulated weight is `∏_{t < m} (t+1) = m!`; at any other index `j` either
`j + m` overshoots `m` without wrapping around (so `f (j+m) = 0` by maximality) or the sum
wraps around, and then the weight `wY (-1) = 0` occurs in the product. -/
theorem Ylin_zero_pow_max (f : Fin p → k) (m : Fin p) (hmax : ∀ j, m < j → f j = 0) :
    (Ylin k p 0 ^ (m : ℕ)) f
      = ((Nat.factorial (m : ℕ) : k) * f m) • Pi.single (0 : Fin p) (1 : k) := by
  funext j
  rw [Ylin_zero_pow_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = 0
  · subst hj
    have hprod : ∏ t ∈ range (m : ℕ), wY k p ((0 : Fin p) + ((t : ℕ) : Fin p))
        = (Nat.factorial (m : ℕ) : k) := by
      have hcongr : ∀ t ∈ range (m : ℕ),
          wY k p ((0 : Fin p) + ((t : ℕ) : Fin p)) = ((t + 1 : ℕ) : k) := by
        intro t ht
        have htp : t < p := lt_trans (Finset.mem_range.mp ht) m.isLt
        rw [zero_add, wY_eq, Fin.val_cast_of_lt htp]
        push_cast
        ring
      rw [Finset.prod_congr rfl hcongr, ← Nat.cast_prod,
        Finset.prod_range_add_one_eq_factorial]
    rw [hprod, Pi.single_eq_same, mul_one, zero_add, Fin.cast_val_eq_self]
  · simp only [Pi.single_apply, if_neg hj, mul_zero]
    have hjne : (j : ℕ) ≠ 0 := by
      intro h
      exact hj (by ext; simp [h])
    have hjlt : (j : ℕ) < p := j.isLt
    have hmlt : (m : ℕ) < p := m.isLt
    rcases lt_or_ge ((j : ℕ) + (m : ℕ)) p with hlt | hge
    · -- no wraparound: `j + m` sits strictly above the top index `m`, so `f` vanishes there
      have hval : ((j + (((m : ℕ) : ℕ) : Fin p) : Fin p) : ℕ) = (j : ℕ) + (m : ℕ) := by
        rw [Fin.val_add, Fin.val_cast_of_lt hmlt, Nat.mod_eq_of_lt hlt]
      have hgt : m < j + (((m : ℕ) : ℕ) : Fin p) := by
        rw [Fin.lt_def, hval]; omega
      rw [hmax _ hgt, mul_zero]
    · -- wraparound: the vanishing weight `wY (-1)` occurs in the product
      set t₀ := p - 1 - (j : ℕ) with ht₀
      have ht₀m : t₀ < (m : ℕ) := by omega
      have hsum : ((j : ℕ) : Fin p) + ((t₀ : ℕ) : Fin p) + 1 = 0 := by
        have hcast : (((j : ℕ) + t₀ + 1 : ℕ) : Fin p)
            = ((j : ℕ) : Fin p) + ((t₀ : ℕ) : Fin p) + 1 := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        rw [← hcast, show (j : ℕ) + t₀ + 1 = p by omega]
        simp
      rw [Fin.cast_val_eq_self] at hsum
      have hzero : wY k p (j + ((t₀ : ℕ) : Fin p)) = 0 := by rw [wY, hsum]; simp
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr ht₀m) hzero, zero_mul]

omit [CharP k p] in
/-- **Raising from the bottom.** For `i < p` the operator `Xlin α ^ i` carries the bottom basis
vector `e₀` to `eᵢ`: the twisting scalar `α` is only picked up on wraparound, which needs `p`
steps. In particular this holds for `α = 0`, where `Xlin 0` is nilpotent. -/
theorem Xlin_pow_single (α : k) (i : ℕ) (hi : i < p) :
    (Xlin k p α ^ i) (Pi.single (0 : Fin p) (1 : k)) = Pi.single ((i : ℕ) : Fin p) (1 : k) := by
  funext j
  rw [Xlin_pow_apply]
  by_cases hj : j = ((i : ℕ) : Fin p)
  · subst hj
    have hprod : ∏ t ∈ range i, wX k p α (((i : ℕ) : Fin p) - ((t : ℕ) : Fin p)) = 1 := by
      refine Finset.prod_eq_one fun t ht => ?_
      have htlt : t < i := Finset.mem_range.mp ht
      have hne : ((i : ℕ) : Fin p) - ((t : ℕ) : Fin p) ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        have hv := congrArg Fin.val h
        rw [Fin.val_cast_of_lt hi, Fin.val_cast_of_lt (htlt.trans hi)] at hv
        omega
      rw [wX, if_neg hne]
    rw [hprod, one_mul, sub_self]
    simp
  · have hsub : j - ((i : ℕ) : Fin p) ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hj h
    simp [hsub, hj]

/-- The element `y - c` of `WeylAlgebra k` acts on `V(α,c)` by the nilpotent operator
`Ylin 0`, which is the lowering operator of the book's model `d/dt`. -/
theorem famRep_y_sub (α c : k) :
    famRep k p α c (WeylAlgebra.y k - c • 1) = Ylin k p 0 := by
  rw [map_sub, map_smul, map_one, famRep_y]
  refine LinearMap.ext fun f => ?_
  funext j
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Ylin_apply, zero_mul, zero_add]
  ring

/-- The `WeylAlgebra k`-action on `V(α,c)` commutes with the ambient `k`-action, because
`famRep a` is a `k`-linear map. -/
theorem famModule_smulCommClass (α c : k) :
    letI := famModule k p α c
    SMulCommClass k (WeylAlgebra k) (Fin p → k) := by
  letI := famModule k p α c
  refine ⟨fun a b f => ?_⟩
  change a • famRep k p α c b f = famRep k p α c b (a • f)
  rw [map_smul]

/-- **Irreducibility of the family (Problem 2.7.4(c)).** For every pair of parameters `α c : k`
the module `V(α,c)` is a simple `WeylAlgebra k`-module. Together with
`Etingof.Problem2_7_4.finrank_irreducible_charP` (every finite dimensional irreducible module
has dimension `p`) this is the classification statement's existence half. -/
theorem famModule_isSimpleModule (α c : k) :
    letI := famModule k p α c
    IsSimpleModule (WeylAlgebra k) (Fin p → k) := by
  letI := famModule k p α c
  haveI := famModule_isScalarTower k p α c
  haveI := famModule_smulCommClass k p α c
  haveI : Nontrivial (Fin p → k) := by
    haveI : Nonempty (Fin p) := ⟨⟨0, p_pos p⟩⟩
    infer_instance
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, fun f hf z => ?_⟩
  obtain ⟨m, hfm, hmax⟩ := exists_top_index k p f hf
  -- the scalar produced by lowering `f` all the way to the bottom
  set s : k := (Nat.factorial (m : ℕ) : k) * f m with hs
  have hs0 : s ≠ 0 := by
    rw [hs]
    refine mul_ne_zero (fun h => ?_) hfm
    have hd : p ∣ Nat.factorial (m : ℕ) := (CharP.cast_eq_zero_iff k p _).mp h
    exact absurd ((Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hd) (not_le.mpr m.isLt)
  set y₀ : WeylAlgebra k := WeylAlgebra.y k - c • 1 with hy₀
  have key : (y₀ ^ (m : ℕ)) • f = s • (Pi.single (0 : Fin p) (1 : k) : Fin p → k) := by
    rw [hs, hy₀, famModule_smul, map_pow, famRep_y_sub]
    exact Ylin_zero_pow_max k p f m hmax
  have hx : ∀ j : Fin p,
      (WeylAlgebra.x k ^ (j : ℕ)) • (Pi.single (0 : Fin p) (1 : k) : Fin p → k)
        = (Pi.single j (1 : k) : Fin p → k) := by
    intro j
    rw [famModule_smul, map_pow, famRep_x, Xlin_pow_single k p α (j : ℕ) j.isLt,
      Fin.cast_val_eq_self]
  refine ⟨∑ j : Fin p, (s⁻¹ * z j) • (WeylAlgebra.x k ^ (j : ℕ) * y₀ ^ (m : ℕ)), ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Finset.sum_smul]
  have step : ∀ j : Fin p,
      ((s⁻¹ * z j) • (WeylAlgebra.x k ^ (j : ℕ) * y₀ ^ (m : ℕ))) • f
        = (Pi.single j (z j) : Fin p → k) := by
    intro j
    have e1 : ((s⁻¹ * z j) • (WeylAlgebra.x k ^ (j : ℕ) * y₀ ^ (m : ℕ))) • f
        = (s⁻¹ * z j) • ((WeylAlgebra.x k ^ (j : ℕ) * y₀ ^ (m : ℕ)) • f) := smul_assoc _ _ _
    have e2 : (WeylAlgebra.x k ^ (j : ℕ) * y₀ ^ (m : ℕ)) • f
        = (WeylAlgebra.x k ^ (j : ℕ)) • ((y₀ ^ (m : ℕ)) • f) := mul_smul _ _ _
    have e3 : s • ((WeylAlgebra.x k ^ (j : ℕ)) •
          (Pi.single (0 : Fin p) (1 : k) : Fin p → k))
        = (WeylAlgebra.x k ^ (j : ℕ)) • (s • (Pi.single (0 : Fin p) (1 : k) : Fin p → k)) :=
      smul_comm _ _ _
    rw [e1, e2, key, ← e3, hx j, smul_smul (s⁻¹ * z j) s,
      show s⁻¹ * z j * s = z j by
        rw [mul_comm s⁻¹ (z j), mul_assoc, inv_mul_cancel₀ hs0, mul_one],
      smul_single_one]
  rw [Finset.sum_congr rfl fun j _ => step j]
  exact Finset.univ_sum_single z

/-! ### Central characters -/

/-- Every central character `(α, β)` arises as `(α, cᵖ)` for a unique parameter `c`: over an
algebraically closed field of characteristic `p` the Frobenius is a bijection. So the family
`V(α,c)` is indexed by central characters without repetition. -/
theorem exists_unique_pow_char [IsAlgClosed k] (β : k) : ∃! c : k, c ^ p = β := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq β (p_pos p)
  refine ⟨c, hc, fun d hd => ?_⟩
  have : (d - c) ^ p = 0 := by
    rw [sub_pow_char, hd, hc, sub_self]
  have hdc : d - c = 0 := pow_eq_zero_iff (n := p) (Fact.out : p.Prime).ne_zero |>.mp this
  exact sub_eq_zero.mp hdc

/-- Frobenius is injective on a field of characteristic `p`, so a `p`-th power determines its
root. No algebraic closure is needed for this direction. -/
theorem pow_char_inj {c c' : k} (h : c ^ p = c' ^ p) : c = c' := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  have h0 : (c - c') ^ p = 0 := by rw [sub_pow_char, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := p) (Fact.out : p.Prime).ne_zero |>.mp h0)

/-! ### The isomorphism criterion `V(α,c) ≅ V(α',c') ↔ α = α' ∧ c = c'`

The family is *classifying* only if it lists each isomorphism class at most once. That is what
this section proves: two members are isomorphic exactly when their parameters agree. The central
character does all the work — `xᵖ` and `yᵖ` are central (Problem 2.7.4(b)), so any `A`-linear
map intertwines their actions, which are the scalars `α` and `cᵖ`. -/

/-- The type of `WeylAlgebra k`-linear equivalences `V(α,c) ≃ V(α',c')`.

Both members of the family have the same carrier `Fin p → k` and differ only in their
`WeylAlgebra k`-module structure, so the two `Module` instances must be supplied explicitly
rather than found by instance resolution. -/
abbrev FamEquiv (α c α' c' : k) : Type _ :=
  @LinearEquiv (WeylAlgebra k) (WeylAlgebra k) _ _
    (RingHom.id (WeylAlgebra k)) (RingHom.id (WeylAlgebra k)) _ _
    (Fin p → k) (Fin p → k) _ _ (famModule k p α c) (famModule k p α' c')

variable {k p}

/-- Unfolding of `A`-linearity for a `FamEquiv`: it intertwines the two representations. -/
theorem famEquiv_intertwines {α c α' c' : k} (e : FamEquiv k p α c α' c') (a : WeylAlgebra k)
    (f : Fin p → k) : e (famRep k p α c a f) = famRep k p α' c' a (e f) :=
  map_smulₛₗ e a f

/-- A `FamEquiv` is automatically `k`-linear: scalars act through
`algebraMap k (WeylAlgebra k)`, whose action an `A`-linear map already respects. -/
theorem famEquiv_map_smul_field {α c α' c' : k} (e : FamEquiv k p α c α' c') (a : k)
    (f : Fin p → k) : e (a • f) = a • e f := by
  have h := famEquiv_intertwines e (algebraMap k (WeylAlgebra k) a) f
  simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using h

variable (k p)

/-- **Isomorphism criterion for the family.** Two members of the family `V(α,c)` are isomorphic
as `WeylAlgebra k`-modules if and only if their parameters coincide.

The interesting direction is `→`: an arbitrary `A`-linear equivalence recovers `(α, c)`. It
intertwines the central elements `xᵖ` and `yᵖ`, which act by the scalars `α` and `cᵖ`
(`Xlin_pow_char`, `Ylin_pow_char`); since it is also `k`-linear and nonzero this forces `α = α'`
and `cᵖ = c'ᵖ`, and Frobenius injectivity (`pow_char_inj`) upgrades the latter to `c = c'`.

Combined with irreducibility and exhaustiveness this says the family enumerates the
finite-dimensional irreducible `WeylAlgebra k`-modules without repetition. -/
theorem famEquiv_nonempty_iff (α c α' c' : k) :
    Nonempty (FamEquiv k p α c α' c') ↔ α = α' ∧ c = c' := by
  constructor
  · rintro ⟨e⟩
    -- Pick a vector `g` in the target with a nonzero coordinate, and its preimage `f`.
    haveI : Nonempty (Fin p) := ⟨⟨0, p_pos p⟩⟩
    obtain ⟨g, hg⟩ := exists_ne (0 : Fin p → k)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hg
    rw [Pi.zero_apply] at hj
    obtain ⟨f, rfl⟩ : ∃ f, e f = g := ⟨e.symm g, e.apply_symm_apply g⟩
    -- `xᵖ` acts by `α` on the source and by `α'` on the target.
    have hx := famEquiv_intertwines e (WeylAlgebra.x k ^ p) f
    -- `yᵖ` acts by `cᵖ` on the source and by `c'ᵖ` on the target.
    have hy := famEquiv_intertwines e (WeylAlgebra.y k ^ p) f
    simp only [map_pow, famRep_x, famRep_y, Xlin_pow_char, Ylin_pow_char, LinearMap.smul_apply,
      Module.End.one_apply, famEquiv_map_smul_field e] at hx hy
    refine ⟨?_, pow_char_inj k p ?_⟩
    · have := congrFun hx j
      simpa only [Pi.smul_apply, smul_eq_mul] using mul_right_cancel₀ hj this
    · have := congrFun hy j
      simpa only [Pi.smul_apply, smul_eq_mul] using mul_right_cancel₀ hj this
  · rintro ⟨rfl, rfl⟩
    exact ⟨@LinearEquiv.refl (WeylAlgebra k) (Fin p → k) _ _ (famModule k p α c)⟩

/-! ### Exhaustiveness: every finite dimensional irreducible module is in the family

The other half of the classification. `Problem2_7_4.exists_normalForm` puts an arbitrary finite
dimensional simple `WeylAlgebra k`-module `V` in the book's normal form: a basis `b₀, …, b_{p-1}`
with `x · bᵢ = b_{i+1}` cyclically (wraparound scalar `α`) and `y · bᵢ = c · bᵢ + i · b_{i-1}`.
Those are exactly the matrices of `Xlin α` and `Ylin c`, so the coordinate isomorphism
`b.equivFun` is an isomorphism of `WeylAlgebra k`-modules `V ≅ V(α,c)`. -/

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- A `k`-linear map between two `WeylAlgebra k`-modules that intertwines the actions of the
generators `x` and `y` intertwines the action of every algebra element: `x` and `y` generate
`WeylAlgebra k`. -/
theorem smul_comm_of_gens {V W : Type*}
    [AddCommGroup V] [Module k V] [Module (WeylAlgebra k) V] [IsScalarTower k (WeylAlgebra k) V]
    [AddCommGroup W] [Module k W] [Module (WeylAlgebra k) W] [IsScalarTower k (WeylAlgebra k) W]
    (e : V →ₗ[k] W)
    (hx : ∀ z : V, e (WeylAlgebra.x k • z) = WeylAlgebra.x k • e z)
    (hy : ∀ z : V, e (WeylAlgebra.y k • z) = WeylAlgebra.y k • e z) :
    ∀ (a : WeylAlgebra k) (z : V), e (a • z) = a • e z := by
  intro a
  obtain ⟨a', rfl⟩ := RingQuot.mkAlgHom_surjective k (WeylAlgebraRel k) a
  have ha' : a' ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k)) := by
    rw [FreeAlgebra.adjoin_range_ι]; exact Algebra.mem_top
  induction ha' using Algebra.adjoin_induction with
  | mem g hg =>
      obtain ⟨idx, rfl⟩ := hg
      intro z
      fin_cases idx
      · exact hx z
      · exact hy z
  | algebraMap r =>
      intro z
      rw [AlgHom.commutes, algebraMap_smul, algebraMap_smul, map_smul]
  | add u v _ _ ihu ihv =>
      intro z
      rw [map_add, add_smul, map_add, ihu, ihv, add_smul]
  | mul u v _ _ ihu ihv =>
      intro z
      rw [map_mul, mul_smul, ihu, ihv, mul_smul]

/-- The type of `WeylAlgebra k`-linear equivalences from a module `V` onto the family member
`V(α,c)`. As with `FamEquiv`, the module structure on the target is `famModule`, which is not an
instance, so it has to be supplied explicitly. -/
abbrev ToFamEquiv (V : Type*) [AddCommGroup V] [Module (WeylAlgebra k) V] (α c : k) : Type _ :=
  @LinearEquiv (WeylAlgebra k) (WeylAlgebra k) _ _
    (RingHom.id (WeylAlgebra k)) (RingHom.id (WeylAlgebra k)) _ _
    V (Fin p → k) _ _ inferInstance (famModule k p α c)

/-- **Exhaustiveness of the family.** Over an algebraically closed field of characteristic `p`,
every finite dimensional irreducible `WeylAlgebra k`-module is isomorphic to a member `V(α,c)`
of the family — with `α` the scalar by which the central element `xᵖ` acts and `c` an eigenvalue
of `y`. -/
theorem exists_toFamEquiv [IsAlgClosed k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (WeylAlgebra k) V] [IsScalarTower k (WeylAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (WeylAlgebra k) V] :
    ∃ α c : k, Nonempty (ToFamEquiv k p V α c) := by
  obtain ⟨α, c, b, hbx, hby⟩ := exists_normalForm k p V
  refine ⟨α, c, ?_⟩
  letI := famModule k p α c
  haveI := famModule_isScalarTower k p α c
  -- The coordinate isomorphism, viewed as a map *into* `V`.
  set ψ : (Fin p → k) ≃ₗ[k] V := b.equivFun.symm
  have hψ : ∀ f : Fin p → k, ψ f = ∑ j, f j • b j := fun f => b.equivFun_symm_apply f
  -- Shifting the summation index by one; used to line the two cyclic patterns up.
  have reindex : ∀ g : Fin p → V, ∑ j, g j = ∑ i : Fin p, g (i + 1) := by
    intro g
    exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin p)) (fun i => g (i + 1)) g
      (fun i => by simp)).symm
  have hx : ∀ f : Fin p → k, ψ (WeylAlgebra.x k • f) = WeylAlgebra.x k • ψ f := by
    intro f
    have hsm : (WeylAlgebra.x k • f : Fin p → k) = Xlin k p α f := by
      rw [famModule_smul k p α c, famRep_x]
    rw [hsm, hψ, hψ, Finset.smul_sum, reindex fun j => Xlin k p α f j • b j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, hbx i, smul_smul, Xlin_apply, add_sub_cancel_right, wX, mul_comm]
  have hy : ∀ f : Fin p → k, ψ (WeylAlgebra.y k • f) = WeylAlgebra.y k • ψ f := by
    intro f
    have hsm : (WeylAlgebra.y k • f : Fin p → k) = Ylin k p c f := by
      rw [famModule_smul k p α c, famRep_y]
    -- Both sides split as (the `c`-part) + (the lowering part); the `c`-parts differ by a shift.
    have hR : ∑ j, WeylAlgebra.y k • (f j • b j)
        = ∑ i : Fin p, ((c * f (i + 1)) • b (i + 1) + (wY k p i * f (i + 1)) • b i) := by
      rw [reindex fun j => WeylAlgebra.y k • (f j • b j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, hby i, smul_add, smul_smul, smul_smul, wY_eq]
      push_cast
      rw [mul_comm (f (i + 1)) c, mul_comm (f (i + 1)) (((i : ℕ) : k) + 1)]
    have hL : ∑ j, Ylin k p c f j • b j
        = ∑ j : Fin p, ((c * f j) • b j + (wY k p j * f (j + 1)) • b j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Ylin_apply, add_smul]
    rw [hsm, hψ, hψ, Finset.smul_sum, hR, hL, Finset.sum_add_distrib, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (reindex fun j => (c * f j) • b j) rfl
  have hlin := smul_comm_of_gens k (ψ : (Fin p → k) →ₗ[k] V) hx hy
  exact ⟨(show @LinearEquiv (WeylAlgebra k) (WeylAlgebra k) _ _
      (RingHom.id (WeylAlgebra k)) (RingHom.id (WeylAlgebra k)) _ _
      (Fin p → k) V _ _ (famModule k p α c) _ from
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := hlin
      invFun := ψ.symm, left_inv := ψ.left_inv, right_inv := ψ.right_inv }).symm⟩

variable {k p}

/-- A `WeylAlgebra k`-linear equivalence onto a family member is automatically `k`-linear:
scalars act through `algebraMap k (WeylAlgebra k)`. -/
theorem toFamEquiv_map_smul_field {V : Type*} [AddCommGroup V] [Module k V]
    [Module (WeylAlgebra k) V] [IsScalarTower k (WeylAlgebra k) V] {α c : k}
    (e : ToFamEquiv k p V α c) (a : k) (z : V) : e (a • z) = a • e z := by
  letI := famModule k p α c
  have h : e (algebraMap k (WeylAlgebra k) a • z) = algebraMap k (WeylAlgebra k) a • e z :=
    map_smulₛₗ e _ z
  rw [algebraMap_smul] at h
  rw [h, famModule_smul k p α c, AlgHom.commutes, Module.algebraMap_end_apply]

variable (k p)

/-- The `k`-linear equivalence underlying a `WeylAlgebra k`-linear equivalence onto `V(α,c)`. -/
noncomputable def toFamEquivToLinearEquiv {V : Type*} [AddCommGroup V] [Module k V]
    [Module (WeylAlgebra k) V] [IsScalarTower k (WeylAlgebra k) V] {α c : k}
    (e : ToFamEquiv k p V α c) : V ≃ₗ[k] (Fin p → k) :=
  letI := famModule k p α c
  { toFun := e
    map_add' := e.map_add
    map_smul' := fun a z => toFamEquiv_map_smul_field e a z
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- **Classification of the finite dimensional irreducible representations of the Weyl algebra
in characteristic `p`** (Etingof, Problem 2.7.4(c)).

Over an algebraically closed field `k` of characteristic `p`, the family `V(α,c)` of
`Problem2_7_4_Family.lean` is a complete, irredundant list of the finite dimensional irreducible
`WeylAlgebra k`-modules: every such module is isomorphic to exactly one `V(α,c)`.

Existence is `exists_toFamEquiv` (via the normal form `Problem2_7_4.exists_normalForm`);
uniqueness of the parameter pair is `famEquiv_nonempty_iff`, the isomorphism criterion for the
family. Each `V(α,c)` really is irreducible (`famModule_isSimpleModule`) and `p`-dimensional
(`famModule_finrank`), so the list is exactly the isomorphism classes. -/
theorem existsUnique_toFamEquiv [IsAlgClosed k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (WeylAlgebra k) V] [IsScalarTower k (WeylAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (WeylAlgebra k) V] :
    ∃! q : k × k, Nonempty (ToFamEquiv k p V q.1 q.2) := by
  obtain ⟨α, c, ⟨e⟩⟩ := exists_toFamEquiv k p V
  refine ⟨(α, c), ⟨e⟩, ?_⟩
  rintro ⟨α', c'⟩ ⟨e'⟩
  obtain ⟨h1, h2⟩ := (famEquiv_nonempty_iff k p α' c' α c).mp ⟨e'.symm.trans e⟩
  exact Prod.ext h1 h2

/-- The dimension statement `Problem2_7_4.finrank_irreducible_charP`, read off from the
classification: an irreducible module is some `V(α,c)`, and every member of the family has
dimension `p`. This is a non-vacuity check on the classification endpoint. -/
theorem finrank_eq_of_classification [IsAlgClosed k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (WeylAlgebra k) V] [IsScalarTower k (WeylAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (WeylAlgebra k) V] :
    Module.finrank k V = p := by
  obtain ⟨α, c, ⟨e⟩⟩ := exists_toFamEquiv k p V
  rw [(toFamEquivToLinearEquiv k p e).finrank_eq, famModule_finrank k p]

end Family

end Etingof.Problem2_7_4

-- The leaf names follow Mathlib conventions; the underscores come solely from the
-- book-number namespace `Problem2_7_4`, which is part of this project's public API.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_7_4.wX Etingof.Problem2_7_4.Xlin
  Etingof.Problem2_7_4.wY Etingof.Problem2_7_4.Ylin
  Etingof.Problem2_7_4.famRep Etingof.Problem2_7_4.famModule
  Etingof.Problem2_7_4.FamEquiv Etingof.Problem2_7_4.ToFamEquiv
  Etingof.Problem2_7_4.toFamEquivToLinearEquiv
