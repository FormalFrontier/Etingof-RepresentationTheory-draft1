import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.DirectSum.Module
import EtingofRepresentationTheory.Chapter2.Sl2Irrep

/-!
# Jacobson–Morozov for a single Jordan block (Problem 2.15.1(l))

Part (l) of Etingof Problem 2.15.1 is the `sl(2)` special case of the
Jacobson–Morozov lemma: for a finite dimensional complex vector space `V` and a
nilpotent operator `A : V → V`, there is a representation of `sl(2)` on `V` with
`E = A`, unique up to isomorphism. The book's route is: put `A` in Jordan normal
form, give each nilpotent Jordan block `J_{0,n}` an `sl(2)`-structure coming from
the irreducible `V_n`, and assemble the direct sum; uniqueness then follows from
the classification of representations (part (f)).

This file formalizes the **existence** half of part (l), in full generality.

We first exhibit, for every `n`, an `sl(2)`-representation on `V_n = Fin n → ℂ`
whose raising operator `E = ρ(e)` is *exactly* the standard nilpotent Jordan shift
`J_{0,n}` (`e_i ↦ e_{i-1}`, `e_0 ↦ 0`), obtained by conjugating the irreducible
representation `rhoLieHom n` (from `Sl2Irrep.lean`) by the diagonal rescaling
`e_k ↦ k! · e_k`.

We then handle an *arbitrary* finite dimensional `V` and nilpotent
`A : Module.End ℂ V` (`exists_sl2Rep_of_nilpotent`). Since Mathlib has no explicit
Jordan-basis decomposition of a nilpotent endomorphism, we build one from the PID
structure theorem: viewing `V` as a torsion `ℂ[X]`-module with `X` acting as `A`
(`Module.AEval' A`), `Module.torsion_by_prime_power_decomposition` for the prime `X`
splits it into cyclic blocks `ℂ[X] ⧸ (Xᵉⁱ)`, each of which is `Fin eᵢ → ℂ` with `X`
acting as `jordanShift eᵢ` (`blockQuotEquiv`). The block-diagonal assembly and
transport (`sl2Pi`, `sl2Transport`, `exists_sl2Rep_of_conj_piShift`) then finish.

## Scope

Existence is complete for arbitrary nilpotent `A`. The remaining piece — uniqueness
up to isomorphism via the classification (part (f)) — additionally depends on the
`sl₂` complete-reducibility results (parts (h)–(k)), and is tracked as follow-up
work.
-/

open Etingof
open Etingof.Sl2Irrep

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Etingof.Sl2Irrep

/-! ## The standard nilpotent Jordan block -/

/-- The standard nilpotent Jordan block `J_{0,n}` on `V_n = Fin n → ℂ`:
`(J v)_k = v_{k+1}` (with `v_n = 0`), i.e. `J e_i = e_{i-1}` and `J e_0 = 0`. -/
noncomputable def jordanShift (n : ℕ) : Module.End ℂ (Fin n → ℂ) where
  toFun v k := if h : (k : ℕ) + 1 < n then v ⟨(k : ℕ) + 1, h⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> simp
  map_smul' c v := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> simp

theorem jordanShift_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    jordanShift n v k = if h : (k : ℕ) + 1 < n then v ⟨(k : ℕ) + 1, h⟩ else 0 := rfl

/-- Action of `J_{0,n}` on a basis vector: `J e_k = e_{k-1}` for `k ≥ 1`, `0` else. -/
theorem jordanShift_e_basis (n : ℕ) (k : Fin n) :
    jordanShift n (e_basis n k)
      = if h : 0 < (k : ℕ) then e_basis n ⟨(k : ℕ) - 1, by omega⟩ else 0 := by
  ext j
  rw [jordanShift_apply]
  by_cases hk : 0 < (k : ℕ)
  · simp only [hk, dite_true]
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [hj, dite_true, e_basis_apply, Fin.ext_iff]
      by_cases hjk : (j : ℕ) + 1 = (k : ℕ)
      · rw [if_pos hjk, if_pos (by omega)]
      · rw [if_neg hjk, if_neg (by omega)]
    · simp only [hj, dite_false, e_basis_apply, Fin.ext_iff]
      rw [if_neg (by omega)]
  · simp only [hk, dite_false, Pi.zero_apply]
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [hj, dite_true, e_basis_apply, Fin.ext_iff]
      rw [if_neg (by omega)]
    · simp only [hj, dite_false]

/-! ## Nilpotency of the Jordan block -/

/-- Powers of the shift: `(J^m v)_k = v_{k+m}` (with out-of-range entries `0`). -/
theorem jordanShift_pow_apply (n m : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (jordanShift n ^ m) v k
      = if h : (k : ℕ) + m < n then v ⟨(k : ℕ) + m, h⟩ else 0 := by
  induction m generalizing k with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.add_zero]
    rw [dif_pos k.isLt]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, jordanShift_apply]
    by_cases hk1 : (k : ℕ) + 1 < n
    · rw [dif_pos hk1, ih ⟨(k : ℕ) + 1, hk1⟩]
      by_cases hkm : (k : ℕ) + 1 + m < n
      · rw [dif_pos hkm, dif_pos (by omega)]
        exact congrArg v (Fin.ext (show (k : ℕ) + 1 + m = (k : ℕ) + (m + 1) by omega))
      · rw [dif_neg hkm, dif_neg (by omega)]
    · rw [dif_neg hk1, dif_neg (by omega)]

/-- The Jordan block `J_{0,n}` is nilpotent: `J^n = 0`. -/
theorem jordanShift_pow_eq_zero (n : ℕ) : jordanShift n ^ n = 0 := by
  apply LinearMap.ext
  intro v
  funext k
  rw [jordanShift_pow_apply, dif_neg (by omega), LinearMap.zero_apply, Pi.zero_apply]

theorem jordanShift_isNilpotent (n : ℕ) : IsNilpotent (jordanShift n) :=
  ⟨n, jordanShift_pow_eq_zero n⟩

/-! ## The diagonal factorial rescaling -/

/-- The diagonal rescaling `e_k ↦ k! · e_k` of `V_n`, a linear automorphism. -/
noncomputable def factScale (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun v k := ((k : ℕ).factorial : ℂ) * v k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' c v := by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  invFun v k := (((k : ℕ).factorial : ℂ))⁻¹ * v k
  left_inv v := by
    ext k
    have hfac : ((k : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  right_inv v := by
    ext k
    have hfac : ((k : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

theorem factScale_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    factScale n v k = ((k : ℕ).factorial : ℂ) * v k := rfl

theorem factScale_symm_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (factScale n).symm v k = (((k : ℕ).factorial : ℂ))⁻¹ * v k := rfl

/-- `factScale` scales the basis vector `e_k` by `k!`. -/
theorem factScale_e_basis (n : ℕ) (k : Fin n) :
    factScale n (e_basis n k) = ((k : ℕ).factorial : ℂ) • e_basis n k := by
  ext j
  rw [factScale_apply, Pi.smul_apply, smul_eq_mul, e_basis_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-- `factScale.symm` scales the basis vector `e_k` by `(k!)⁻¹`. -/
theorem factScale_symm_e_basis (n : ℕ) (k : Fin n) :
    (factScale n).symm (e_basis n k) = (((k : ℕ).factorial : ℂ))⁻¹ • e_basis n k := by
  ext j
  rw [factScale_symm_apply, Pi.smul_apply, smul_eq_mul, e_basis_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-! ## The single-block `sl(2)`-representation -/

/-- The `sl(2)`-representation on `V_n` obtained by conjugating the irreducible
representation `rhoLieHom n` by the factorial rescaling `factScale n`. Its raising
operator `ρ(e)` is the standard Jordan block `J_{0,n}` (see `sl2RepOfBlock_e`). -/
noncomputable def sl2RepOfBlock (n : ℕ) : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ) :=
  ((factScale n).conjAlgEquiv ℂ : _ →ₐ[ℂ] _).toLieHom.comp (rhoLieHom n)

theorem sl2RepOfBlock_apply (n : ℕ) (x : sl2) :
    sl2RepOfBlock n x = (factScale n).conjAlgEquiv ℂ (rhoLieHom n x) := rfl

/-- **Single-block Jacobson–Morozov (Problem 2.15.1(l)).** On `V_n = Fin n → ℂ`
the representation `sl2RepOfBlock n` sends the standard generator `e` to the
standard nilpotent Jordan block `J_{0,n}`. Equivalently: every single Jordan block
carries an `sl(2)`-structure with `E` equal to that block. -/
theorem sl2RepOfBlock_e (n : ℕ) : sl2RepOfBlock n sl2_e = jordanShift n := by
  refine (Pi.basisFun ℂ (Fin n)).ext fun k => ?_
  rw [Pi.basisFun_apply]
  change sl2RepOfBlock n sl2_e (e_basis n k) = jordanShift n (e_basis n k)
  -- the action of `ρ(e)` on a basis vector, via the public API of `Sl2Irrep`
  have he : rhoLieHom n sl2_e (e_basis n k)
      = ((k : ℕ) : ℂ) • e_basis n ⟨(k : ℕ) - 1, by omega⟩ := by
    have h := lie_sl2_e_e_basis n (k : ℕ) k.isLt
    rw [Fin.eta] at h
    rw [← lie_eq_rhoLieHom]
    exact h
  rw [sl2RepOfBlock_apply, LinearEquiv.conjAlgEquiv_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [factScale_symm_e_basis, map_smul, he]
  simp only [map_smul, factScale_e_basis]
  rw [jordanShift_e_basis]
  by_cases hk : 0 < (k : ℕ)
  · rw [dif_pos hk, smul_smul, smul_smul]
    -- scalar (k!)⁻¹ * k * (k-1)! = 1
    have hscalar : (((k : ℕ).factorial : ℂ))⁻¹ * ((k : ℕ) : ℂ)
        * (((k : ℕ) - 1).factorial : ℂ) = 1 := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (k : ℕ) ≠ 0)
      rw [hm, Nat.factorial_succ]
      have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
      have hmf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      push_cast
      field_simp
    rw [hscalar, one_smul]
  · rw [dif_neg hk]
    have hk0 : (k : ℕ) = 0 := by omega
    simp [hk0]

/-- **Existence for a single block.** For every `n`, there is an
`sl(2)`-representation on `V_n` whose `E` operator is the standard nilpotent
Jordan block `J_{0,n}`. -/
theorem exists_sl2Rep_jordanShift (n : ℕ) :
    ∃ ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ), ρ sl2_e = jordanShift n :=
  ⟨sl2RepOfBlock n, sl2RepOfBlock_e n⟩

/-! ## Assembling representations: block-diagonal sum and transport

Two operations turn the single-block structure into the general case. First,
`sl2Pi` assembles a finite family of `sl(2)`-representations `ρ i` on spaces `W i`
into a single representation on the product `Π i, W i`, acting block-diagonally.
Second, `sl2Transport` moves a representation across a linear isomorphism.

Together they reduce **general existence** (Problem 2.15.1(l) for an arbitrary
nilpotent `A`) to the Jordan normal form theorem: once a nilpotent `A` is conjugate
to a block-diagonal sum of standard shifts `⨁ᵢ J_{0,nᵢ}` — which is exactly the
statement that `A` has a Jordan basis — it carries an `sl(2)`-structure with `E = A`.
This is `exists_sl2Rep_of_conj_piShift`. The remaining ingredient — an explicit
Jordan-basis decomposition of a nilpotent endomorphism, absent from Mathlib — is
built below from the PID structure theorem via the `ℂ[X]`-module `Module.AEval`,
completing general existence in `exists_sl2Rep_of_nilpotent`. -/

/-- **Block-diagonal assembly.** A finite (indeed arbitrary) family of
`sl(2)`-representations `ρ i` on spaces `W i` assembles into an
`sl(2)`-representation on the product `Π i, W i`, acting on each factor
independently: `(sl2Pi ρ x v) i = ρ i x (v i)`. -/
noncomputable def sl2Pi {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, sl2 →ₗ⁅ℂ⁆ Module.End ℂ (W i)) :
    sl2 →ₗ⁅ℂ⁆ Module.End ℂ (∀ i, W i) where
  toFun x := LinearMap.piMap fun i => ρ i x
  map_add' x y := by
    apply LinearMap.ext; intro v; funext j
    simp only [LinearMap.coe_piMap, Pi.map_apply, map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' r x := by
    apply LinearMap.ext; intro v; funext j
    simp only [LinearMap.coe_piMap, Pi.map_apply, map_smul, RingHom.id_apply,
      LinearMap.smul_apply, Pi.smul_apply]
  map_lie' {x y} := by
    apply LinearMap.ext; intro v; funext j
    simp only [LinearMap.coe_piMap, Pi.map_apply, LieHom.map_lie,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Pi.sub_apply,
      Module.End.mul_apply]

@[simp]
theorem sl2Pi_apply {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, sl2 →ₗ⁅ℂ⁆ Module.End ℂ (W i)) (x : sl2) (v : ∀ i, W i) (j : ι) :
    sl2Pi ρ x v j = ρ j x (v j) := rfl

/-- The raising operator of the assembled representation is the block-diagonal sum
of the individual raising operators. -/
theorem sl2Pi_e {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, sl2 →ₗ⁅ℂ⁆ Module.End ℂ (W i)) :
    sl2Pi ρ sl2_e = LinearMap.piMap fun i => ρ i sl2_e := rfl

/-- **Transport along an isomorphism.** A linear isomorphism `e : V ≃ₗ W` carries an
`sl(2)`-representation `ρ` on `W` to one on `V`, by conjugation. -/
noncomputable def sl2Transport {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ W) : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V :=
  (e.symm.lieConj.toLieHom).comp ρ

theorem sl2Transport_apply {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ W) (x : sl2) :
    sl2Transport e ρ x = e.symm.lieConj (ρ x) := rfl

/-- **General existence, reduced to Jordan normal form.** If a nilpotent operator
`A` on `V` is conjugate (via a linear iso `e`) to the block-diagonal sum of standard
shifts `⨁ᵢ J_{0,nᵢ}` — i.e. `A` has a Jordan basis — then `V` carries an
`sl(2)`-representation with `E = A`. This is the assembly step of Problem 2.15.1(l);
the outstanding input is the existence of such a Jordan basis for every nilpotent
`A`, which is the Jordan normal form theorem. -/
theorem exists_sl2Rep_of_conj_piShift {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (n : ι → ℕ) (A : Module.End ℂ V)
    (e : V ≃ₗ[ℂ] ∀ i, Fin (n i) → ℂ)
    (hA : ∀ v, e (A v) = LinearMap.piMap (fun i => jordanShift (n i)) (e v)) :
    ∃ ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V, ρ sl2_e = A := by
  refine ⟨sl2Transport e (sl2Pi fun i => sl2RepOfBlock (n i)), ?_⟩
  have hE : (sl2Pi fun i => sl2RepOfBlock (n i)) sl2_e
      = LinearMap.piMap fun i => jordanShift (n i) := by
    rw [sl2Pi_e]
    congr 1; funext i; exact sl2RepOfBlock_e (n i)
  apply LinearMap.ext; intro v
  rw [sl2Transport_apply, hE, LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_symm, ← hA v, LinearEquiv.symm_apply_apply]

/-! ## The Jordan basis of a nilpotent operator, via the `ℂ[X]`-module structure

To turn an *arbitrary* nilpotent `A : Module.End ℂ V` into a block-diagonal sum of
standard shifts, we build a Jordan basis. Mathlib has no explicit Jordan-basis
decomposition of a nilpotent endomorphism, so we construct it here from the PID
structure theorem, following the route flagged in the item.

Give `V` the `ℂ[X]`-module structure in which `X` acts as `A` (`Module.AEval' A`).
Nilpotency of `A` makes this module torsion (annihilated by `Xⁿ`), so
`Module.torsion_by_prime_power_decomposition` with the prime `X` decomposes it as a
finite direct sum of cyclic modules `ℂ[X] ⧸ (Xᵉ)`. Each such cyclic quotient is,
`ℂ`-linearly, the block space `Fin e → ℂ` on which multiplication by `X` becomes the
standard nilpotent shift `jordanShift e` (`blockQuotEquiv`). Transporting `A` across
the assembled equivalence realises it as the block-diagonal sum
`⨁ᵢ jordanShift (eᵢ)`, which is exactly the Jordan-basis hypothesis consumed by
`exists_sl2Rep_of_conj_piShift`.
-/

open Polynomial
open scoped DirectSum

/-- The `ℂ`-linear map reading off the reversed low-degree coefficients of a polynomial:
`p ↦ (fun k => p.coeff (e-1-k))`. This is the coordinate map of the block basis
`X^{e-1}, X^{e-2}, …, X, 1`; multiplication by `X` becomes the standard shift under it. -/
noncomputable def blockCoeffMap (e : ℕ) : Polynomial ℂ →ₗ[ℂ] (Fin e → ℂ) :=
  LinearMap.pi fun k : Fin e => Polynomial.lcoeff ℂ (e - 1 - (k : ℕ))

@[simp] theorem blockCoeffMap_apply (e : ℕ) (p : Polynomial ℂ) (k : Fin e) :
    blockCoeffMap e p k = p.coeff (e - 1 - (k : ℕ)) := rfl

/-- The ideal `(Xᵉ) ≤ ℂ[X]` annihilates the reversed low-degree coefficients. -/
theorem blockSpan_le_ker_blockCoeffMap (e : ℕ) :
    ((Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}).restrictScalars ℂ)
      ≤ LinearMap.ker (blockCoeffMap e) := by
  intro x hx
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.mem_ker]
  ext k
  simp only [blockCoeffMap_apply, Pi.zero_apply]
  have hdvd : (X : Polynomial ℂ) ^ e ∣ c • (X : Polynomial ℂ) ^ e :=
    ⟨c, by rw [smul_eq_mul]; ring⟩
  exact (Polynomial.X_pow_dvd_iff.mp hdvd) _ (by omega)

/-- The forward block map, descended to the cyclic quotient `ℂ[X] ⧸ (Xᵉ)`. -/
noncomputable def blockForward (e : ℕ) :
    (Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) →ₗ[ℂ] (Fin e → ℂ) :=
  Submodule.liftQ ((Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}).restrictScalars ℂ)
    (blockCoeffMap e) (blockSpan_le_ker_blockCoeffMap e)

@[simp] theorem blockForward_mk (e : ℕ) (p : Polynomial ℂ) :
    blockForward e (Submodule.Quotient.mk p) = blockCoeffMap e p := rfl

/-- The inverse block map: a coefficient vector `v` to the truncated polynomial
`∑ⱼ v j · X^{e-1-j}`, then to its class in `ℂ[X] ⧸ (Xᵉ)`. -/
noncomputable def blockPolyOf (e : ℕ) : (Fin e → ℂ) →ₗ[ℂ] Polynomial ℂ :=
  ∑ j : Fin e, (Polynomial.monomial (e - 1 - (j : ℕ))).comp (LinearMap.proj j)

theorem blockPolyOf_apply (e : ℕ) (v : Fin e → ℂ) :
    blockPolyOf e v = ∑ j : Fin e, Polynomial.monomial (e - 1 - (j : ℕ)) (v j) := by
  simp only [blockPolyOf, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem blockPolyOf_coeff (e : ℕ) (v : Fin e → ℂ) (d : ℕ) :
    (blockPolyOf e v).coeff d = ∑ j : Fin e, (if e - 1 - (j : ℕ) = d then v j else 0) := by
  rw [blockPolyOf_apply, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun j _ => Polynomial.coeff_monomial

/-- The inverse block map as a `ℂ`-linear map `(Fin e → ℂ) → ℂ[X] ⧸ (Xᵉ)`. -/
noncomputable def blockBackward (e : ℕ) :
    (Fin e → ℂ) →ₗ[ℂ] (Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :=
  ((Submodule.mkQ _).restrictScalars ℂ).comp (blockPolyOf e)

@[simp] theorem blockBackward_apply (e : ℕ) (v : Fin e → ℂ) :
    blockBackward e v = Submodule.Quotient.mk (blockPolyOf e v) := rfl

theorem blockForward_backward (e : ℕ) (v : Fin e → ℂ) :
    blockForward e (blockBackward e v) = v := by
  ext k
  rw [blockBackward_apply, blockForward_mk, blockCoeffMap_apply, blockPolyOf_coeff]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro j _ hjk
    refine if_neg fun h => hjk ?_
    have hj := j.isLt; have hk := k.isLt
    exact Fin.ext (by omega)
  · intro h; exact absurd (Finset.mem_univ k) h

theorem blockBackward_forward (e : ℕ)
    (q : Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :
    blockBackward e (blockForward e q) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H p =>
    rw [blockForward_mk, blockBackward_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton]
    have hdvd : (X : Polynomial ℂ) ^ e ∣ (blockPolyOf e (blockCoeffMap e p) - p) := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rw [Polynomial.coeff_sub, blockPolyOf_coeff]
      simp only [blockCoeffMap_apply]
      rw [Finset.sum_eq_single (⟨e - 1 - d, by omega⟩ : Fin e)]
      · simp only []
        rw [if_pos (by omega)]
        have : e - 1 - (e - 1 - d) = d := by omega
        rw [this]; ring
      · intro j _ hj
        refine if_neg fun h => hj (Fin.ext ?_)
        simp only []; omega
      · intro h; exact absurd (Finset.mem_univ _) h
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by rw [smul_eq_mul, mul_comm]; exact hc.symm⟩

/-- The block coordinate identification `ℂ[X] ⧸ (Xᵉ) ≃ₗ[ℂ] Fin e → ℂ`. Under it,
multiplication by `X` corresponds to the standard nilpotent shift `jordanShift e`
(see `blockQuotEquiv_X_smul`). -/
noncomputable def blockQuotEquiv (e : ℕ) :
    (Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) ≃ₗ[ℂ] (Fin e → ℂ) :=
  { blockForward e with
    invFun := blockBackward e
    left_inv := blockBackward_forward e
    right_inv := blockForward_backward e }

@[simp] theorem blockQuotEquiv_apply (e : ℕ)
    (q : Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :
    blockQuotEquiv e q = blockForward e q := rfl

/-- Multiplication by `X` on the cyclic quotient `ℂ[X] ⧸ (Xᵉ)` becomes the standard
nilpotent Jordan shift `jordanShift e` under the block identification. -/
theorem blockQuotEquiv_X_smul (e : ℕ)
    (q : Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :
    blockQuotEquiv e ((X : Polynomial ℂ) • q) = jordanShift e (blockQuotEquiv e q) := by
  induction q using Submodule.Quotient.induction_on with
  | H p =>
    simp only [blockQuotEquiv_apply]
    rw [show (X : Polynomial ℂ) • (Submodule.Quotient.mk p :
          Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e})
          = Submodule.Quotient.mk (X * p) from by
        rw [← Submodule.Quotient.mk_smul]; congr 1]
    rw [blockForward_mk, blockForward_mk]
    ext k
    rw [blockCoeffMap_apply, jordanShift_apply]
    by_cases hk : (k : ℕ) + 1 < e
    · rw [dif_pos hk, blockCoeffMap_apply]
      have : e - 1 - (k : ℕ) = (e - 1 - ((k : ℕ) + 1)) + 1 := by omega
      rw [this, coeff_X_mul]
    · rw [dif_neg hk]
      have h0 : e - 1 - (k : ℕ) = 0 := by omega
      rw [h0]; exact coeff_X_mul_zero p

/-! ## General existence via the PID structure theorem -/

/-- Nilpotency of `A` makes the `ℂ[X]`-module `Module.AEval' A` (where `X` acts as `A`)
a torsion module for the prime `X`: every element is annihilated by a power of `X`. -/
theorem aeval'_isTorsion {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (hA : IsNilpotent A) :
    Module.IsTorsion' (Module.AEval' A) (Submonoid.powers (X : Polynomial ℂ)) := by
  obtain ⟨N, hN⟩ := hA
  intro x
  refine ⟨⟨(X : Polynomial ℂ) ^ N, N, rfl⟩, ?_⟩
  obtain ⟨m, rfl⟩ := (Module.AEval'.of A).surjective x
  change (X : Polynomial ℂ) ^ N • Module.AEval'.of A m = 0
  rw [Module.AEval'.X_pow_smul_of]
  have : A ^ N • m = (0 : V) := by rw [hN]; simp
  rw [this, map_zero]

/-- **General existence (Jacobson–Morozov, Problem 2.15.1(l)).** For a finite dimensional
complex vector space `V` and *any* nilpotent operator `A : V → V`, there is an
`sl(2)`-representation `ρ` on `V` with `ρ(e) = A`.

The proof produces a Jordan basis: viewing `V` as a torsion `ℂ[X]`-module with `X` acting
as `A`, the PID structure theorem splits it into cyclic blocks `ℂ[X] ⧸ (Xᵉⁱ)`, each of
which is `Fin eᵢ → ℂ` with `X` acting as the standard shift `jordanShift eᵢ`
(`blockQuotEquiv`). The resulting linear isomorphism intertwines `A` with the
block-diagonal sum `⨁ᵢ jordanShift eᵢ`, and `exists_sl2Rep_of_conj_piShift` assembles the
representation. -/
theorem exists_sl2Rep_of_nilpotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) (hA : IsNilpotent A) :
    ∃ ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V, ρ sl2_e = A := by
  -- Decompose the torsion `ℂ[X]`-module `AEval' A` into cyclic blocks `ℂ[X] ⧸ (X^{k i})`.
  obtain ⟨d, k, ⟨Ψ⟩⟩ := Module.torsion_by_prime_power_decomposition (R := Polynomial ℂ)
    (M := Module.AEval' A) Polynomial.irreducible_X (aeval'_isTorsion A hA)
  -- The block-diagonal `ℂ`-linear Jordan-basis isomorphism `V ≃ₗ[ℂ] Π i, Fin (k i) → ℂ`.
  set funOn := DirectSum.linearEquivFunOnFintype (Polynomial ℂ) (Fin d)
    (fun i => Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ (k i)}) with hfunOn
  set e : V ≃ₗ[ℂ] (∀ i : Fin d, Fin (k i) → ℂ) :=
    (Module.AEval'.of A) ≪≫ₗ (Ψ.restrictScalars ℂ) ≪≫ₗ (funOn.restrictScalars ℂ) ≪≫ₗ
      (LinearEquiv.piCongrRight fun i => blockQuotEquiv (k i)) with he
  refine exists_sl2Rep_of_conj_piShift k A e ?_
  intro v
  funext i
  simp only [he, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.piCongrRight_apply, LinearMap.coe_piMap, Pi.map_apply]
  rw [show Module.AEval'.of A (A v) = (X : Polynomial ℂ) • Module.AEval'.of A v from
      (Module.AEval'.X_smul_of A v).symm, map_smul, map_smul, Pi.smul_apply,
      blockQuotEquiv_X_smul]

end Etingof.Sl2Irrep
