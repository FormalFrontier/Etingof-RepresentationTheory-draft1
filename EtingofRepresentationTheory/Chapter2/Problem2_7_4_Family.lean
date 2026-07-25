import Mathlib
import EtingofRepresentationTheory.Chapter2.Problem2_7_4

/-!
# Problem 2.7.4(c): the classifying family of irreducible Weyl-algebra modules in characteristic `p`

`Problem2_7_4.lean` proves (`Etingof.Problem2_7_4.finrank_irreducible_charP`) that over an
algebraically closed field `k` of characteristic `p` every finite dimensional irreducible module
over the Weyl algebra `A = Etingof.WeylAlgebra k` has dimension exactly `p`. That is a dimension
statement, not a classification. This file constructs the family that does the classifying.

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
* `Etingof.Problem2_7_4.FamEquiv` — the type of `WeylAlgebra k`-linear equivalences
  `V(α,c) ≃ V(α',c')`.
* `Etingof.Problem2_7_4.famEquiv_nonempty_iff` — the isomorphism criterion
  `V(α,c) ≅ V(α',c') ↔ α = α' ∧ c = c'`, so the family lists each isomorphism class at most once.

Irreducibility of `V(α,c)` and exhaustiveness are follow-up work.
-/

namespace Etingof.Problem2_7_4

open Etingof Finset
open scoped Fin.NatCast

section Family

variable (k : Type*) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]

private lemma p_pos : 0 < p := (Fact.out : p.Prime).pos

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

@[simp] theorem famRep_x (α c : k) : famRep k p α c (WeylAlgebra.x k) = Xlin k p α := by
  simp [famRep, WeylAlgebra.x, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply, famRepFree,
    FreeAlgebra.lift_ι_apply, famRepGen]

@[simp] theorem famRep_y (α c : k) : famRep k p α c (WeylAlgebra.y k) = Ylin k p c := by
  simp [famRep, WeylAlgebra.y, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply, famRepFree,
    FreeAlgebra.lift_ι_apply, famRepGen]

/-- The classifying module `V(α,c)`: the `WeylAlgebra k`-module structure on `Fin p → k`
determined by `x ↦ Xlin α`, `y ↦ Ylin c`. -/
@[reducible] noncomputable def famModule (α c : k) : Module (WeylAlgebra k) (Fin p → k) :=
  Module.compHom (Fin p → k) (famRep k p α c).toRingHom

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

end Family

end Etingof.Problem2_7_4
