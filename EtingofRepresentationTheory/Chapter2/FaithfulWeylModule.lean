import EtingofRepresentationTheory.Chapter2.Proposition2_7_1
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Finsupp.Basic

/-!
# Faithful Weyl-algebra module `E = tᵃ k[a][t, t⁻¹]` in arbitrary characteristic

This file constructs the representation `E = tᵃ k[a][t, t⁻¹]` of the Weyl algebra used in the
proof of Proposition 2.7.1, and proves that it is **faithful in any characteristic**.

The polynomial representation on `k[t]` (`x ↦ t·`, `y ↦ d/dt`) used in `Proposition2_7_1.lean`
is faithful only when `k` has characteristic zero: in characteristic `p`, `(d/dt)^p Q = 0` for
every polynomial `Q`. The module `E` repairs this. Here `a` is a formal parameter, `t` is
invertible, and the formal symbol `tᵃ` lets the derivative act by

  `d(t^{a+n})/dt = (a + n) · t^{a+n-1}`,

so the coefficient `(a)(a-1)⋯(a-j+1)` produced by `(d/dt)^j` on `tᵃ` is a *nonzero polynomial in
`a`* of degree `j` (monic) regardless of the characteristic of `k`. This is the genuine content:
char-free faithfulness.

## Model

We take `R = k[a] = Polynomial k` and model `E = tᵃ k[a][t, t⁻¹]` as the free `R`-module on the
formal symbols `t^{a+n}` for `n ∈ ℤ`, i.e. as `E = ℤ →₀ Polynomial k`, where `Finsupp.single n c`
stands for `c · t^{a+n}`. The Weyl-algebra generators act `k`-linearly by

  `x ↦ mulX`   (multiplication by `t`):       `t^{a+n} ↦ t^{a+n+1}`,
  `y ↦ D`      (twisted derivative `d/dt`):    `t^{a+n} ↦ (a + n) · t^{a+n-1}`.

These satisfy the Weyl relation `D ∘ mulX = mulX ∘ D + 1`, giving an algebra homomorphism
`repE : WeylAlgebra k →ₐ[k] Module.End k E`. The main theorem `WeylAlgebra.repE_injective` shows
`repE` is injective over any nontrivial commutative ring `k`.
-/

namespace Etingof

open Polynomial

variable (k : Type*) [CommRing k]

/-- The module `E = tᵃ k[a][t, t⁻¹]`, modelled as the free `k[a]`-module on the formal symbols
`{t^{a+n} : n ∈ ℤ}`. `Finsupp.single n c` stands for `c · t^{a+n}`. -/
abbrev WeylE : Type _ := ℤ →₀ Polynomial k

/-- Action of `x` on `E`: multiplication by `t`, sending `t^{a+n} ↦ t^{a+n+1}`. -/
noncomputable def mulX : Module.End k (WeylE k) :=
  Finsupp.lsum k (fun n => Finsupp.lsingle (n + 1))

/-- Action of `y` on `E`: the twisted derivative `d/dt`, sending
`c · t^{a+n} ↦ c · (a + n) · t^{a+n-1}`. -/
noncomputable def weylD : Module.End k (WeylE k) :=
  Finsupp.lsum k (fun n => (Finsupp.lsingle (n - 1)).comp
    (LinearMap.mulLeft k (Polynomial.X + (n : Polynomial k))))

@[simp] lemma mulX_single (n : ℤ) (c : Polynomial k) :
    mulX k (Finsupp.single n c) = Finsupp.single (n + 1) c := by
  simp only [mulX, Finsupp.lsum_apply, Finsupp.sum_single_index, map_zero, Finsupp.lsingle_apply]

@[simp] lemma weylD_single (n : ℤ) (c : Polynomial k) :
    weylD k (Finsupp.single n c) =
      Finsupp.single (n - 1) ((Polynomial.X + (n : Polynomial k)) * c) := by
  simp only [weylD, Finsupp.lsum_apply, Finsupp.sum_single_index, map_zero,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, Finsupp.lsingle_apply]

/-- The Weyl relation on `E`: `D ∘ mulX = mulX ∘ D + 1`. -/
lemma weylD_mulX :
    weylD k * mulX k = mulX k * weylD k + 1 := by
  apply Finsupp.lhom_ext
  intro n c
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, mulX_single,
    weylD_single]
  rw [show (n : ℤ) + 1 - 1 = n from by ring, show (n : ℤ) - 1 + 1 = n from by ring,
    ← Finsupp.single_add]
  congr 1
  push_cast
  ring

/-- Generator assignment: `x ↦ mulX` (multiply by `t`), `y ↦ D` (twisted derivative). -/
noncomputable def weylRepGen : Fin 2 → Module.End k (WeylE k) :=
  ![mulX k, weylD k]

private noncomputable def weylRepFree :
    FreeAlgebra k (Fin 2) →ₐ[k] Module.End k (WeylE k) :=
  FreeAlgebra.lift k (weylRepGen k)

private lemma weylRep_rel :
    ∀ ⦃a b⦄, WeylAlgebraRel k a b → weylRepFree k a = weylRepFree k b := by
  intro a b ⟨ha, hb⟩
  subst ha; subst hb
  simp only [weylRepFree, map_mul, map_add, map_one, FreeAlgebra.lift_ι_apply,
    weylRepGen, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact weylD_mulX k

/-- The representation `E = tᵃ k[a][t, t⁻¹]` of the Weyl algebra, as an algebra homomorphism
`WeylAlgebra k →ₐ[k] Module.End k E`. -/
noncomputable def repE :
    WeylAlgebra k →ₐ[k] Module.End k (WeylE k) :=
  RingQuot.liftAlgHom k ⟨weylRepFree k, weylRep_rel k⟩

@[simp] lemma repE_x : repE k (WeylAlgebra.x k) = mulX k := by
  simp [repE, WeylAlgebra.x, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    weylRepFree, FreeAlgebra.lift_ι_apply, weylRepGen]

@[simp] lemma repE_y : repE k (WeylAlgebra.y k) = weylD k := by
  simp [repE, WeylAlgebra.y, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    weylRepFree, FreeAlgebra.lift_ι_apply, weylRepGen]

-- === The falling-factorial polynomial a(a-1)⋯(a-j+1) ===

/-- The falling-factorial polynomial `descPoly k j = a(a-1)⋯(a-j+1) = ∏_{l<j} (X - l)`.
This is the coefficient produced by `(d/dt)^j` acting on `tᵃ`. It is monic of degree `j`,
hence nonzero in *any* characteristic — the key to char-free faithfulness. -/
noncomputable def descPoly (j : ℕ) : Polynomial k :=
  ∏ l ∈ Finset.range j, (Polynomial.X - Polynomial.C (l : k))

@[simp] lemma descPoly_zero : descPoly k 0 = 1 := by
  simp [descPoly]

lemma descPoly_succ (j : ℕ) :
    descPoly k (j + 1) = descPoly k j * (Polynomial.X - Polynomial.C (j : k)) := by
  simp [descPoly, Finset.prod_range_succ]

lemma descPoly_monic (j : ℕ) : (descPoly k j).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro l _
  exact Polynomial.monic_X_sub_C _

variable [Nontrivial k]

lemma descPoly_natDegree (j : ℕ) : (descPoly k j).natDegree = j := by
  rw [descPoly, Polynomial.natDegree_prod_of_monic _ _ (fun l _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]

lemma descPoly_coeff_self (j : ℕ) : (descPoly k j).coeff j = 1 := by
  have h := (descPoly_monic k j).coeff_natDegree
  rwa [descPoly_natDegree] at h

-- === Powers of the generators and the key evaluation at `tᵃ` ===

omit [Nontrivial k] in
lemma mulX_pow_single (i : ℕ) (n : ℤ) (c : Polynomial k) :
    (mulX k ^ i) (Finsupp.single n c) = Finsupp.single (n + i) c := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, mulX_single]
    congr 1
    push_cast; ring

omit [Nontrivial k] in
/-- `(d/dt)^j` applied to the generator `tᵃ = single 0 1` produces the falling factorial:
`(d/dt)^j tᵃ = a(a-1)⋯(a-j+1) · t^{a-j}`. -/
lemma weylD_pow_single0 (j : ℕ) :
    (weylD k ^ j) (Finsupp.single 0 1) = Finsupp.single (-(j : ℤ)) (descPoly k j) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, weylD_single, descPoly_succ]
    rw [show (-(n : ℤ)) - 1 = -((n + 1 : ℕ) : ℤ) from by push_cast; ring]
    congr 1
    simp only [Polynomial.C_eq_natCast]
    push_cast; ring

omit [Nontrivial k] in
/-- **Key evaluation.** The basis monomial `xⁱyʲ` of the Weyl algebra acts on the generator
`tᵃ = single 0 1` by
`ρ(xⁱyʲ) tᵃ = a(a-1)⋯(a-j+1) · t^{a + i - j}`,
with coefficient the falling-factorial polynomial `descPoly k j`, which is *nonzero in any
characteristic*. -/
theorem repE_monomial_apply_t0 (i j : ℕ) :
    repE k (WeylAlgebra.monomial k i j) (Finsupp.single 0 1) =
      Finsupp.single ((i : ℤ) - j) (descPoly k j) := by
  simp only [WeylAlgebra.monomial, map_mul, map_pow, repE_x, repE_y, Module.End.mul_apply]
  rw [weylD_pow_single0, mulX_pow_single]
  congr 1
  ring

-- === Char-free linear independence and faithfulness ===

/-- The images of the basis monomials, evaluated at `tᵃ`, namely
`xⁱyʲ ↦ t^{a+i-j} · descPoly j`, are linearly independent over `k`.

This is the char-free crux: the elements `t^{a+i-j} · descPoly j` are separated first by the
power `i - j` of `t` (the `Finsupp` coordinate), and within a fixed power by the *degree `j`* of
the monic polynomial `descPoly j` in `a` — a separation that survives in any characteristic. -/
theorem evalImage_linearIndependent :
    LinearIndependent k
      (fun p : ℕ × ℕ => Finsupp.single ((p.1 : ℤ) - p.2) (descPoly k p.2)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum p₀ hp₀
  set m₀ : ℤ := (p₀.1 : ℤ) - p₀.2 with hm₀
  -- Evaluate the relation at the `Finsupp` coordinate `m₀`.
  have hval := congrArg (fun e : WeylE k => e m₀) hsum
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply, smul_ite, smul_zero,
    ← Finset.sum_filter] at hval
  -- `hval` is now a sum over the fiber of `t` of fixed `t`-power `m₀`.
  set t : Finset (ℕ × ℕ) := s.filter (fun p => (p.1 : ℤ) - p.2 = m₀) with ht
  have hp₀t : p₀ ∈ t := Finset.mem_filter.mpr ⟨hp₀, hm₀.symm⟩
  -- On `t`, the second coordinate determines the pair.
  have hinj : ∀ p ∈ t, ∀ q ∈ t, p.2 = q.2 → p = q := by
    intro p hp q hq h2
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    refine Prod.ext ?_ h2
    omega
  -- All coefficients on the fiber vanish, by a maximal-degree argument.
  have hall : ∀ p ∈ t, g p = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨q, hqt, hq0⟩ := hcon
    set B : Finset (ℕ × ℕ) := t.filter (fun p => g p ≠ 0) with hB
    have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hqt, hq0⟩
    obtain ⟨pmax, hpmaxB, hsup⟩ := Finset.exists_mem_eq_sup' ⟨q, hqB⟩ (fun p => p.2)
    have hpmaxt : pmax ∈ t := (Finset.mem_filter.mp hpmaxB).1
    have hpmax0 : g pmax ≠ 0 := (Finset.mem_filter.mp hpmaxB).2
    -- Extract the coefficient of degree `pmax.2`.
    have hco : (∑ p ∈ t, g p • descPoly k p.2).coeff pmax.2 = 0 := by
      rw [hval, Polynomial.coeff_zero]
    rw [Polynomial.finsetSum_coeff] at hco
    simp only [Polynomial.coeff_smul, smul_eq_mul] at hco
    rw [Finset.sum_eq_single pmax ?_ ?_] at hco
    · rw [descPoly_coeff_self, mul_one] at hco
      exact hpmax0 hco
    · intro p hpt hne
      rcases lt_trichotomy p.2 pmax.2 with hlt | heq | hgt
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [descPoly_natDegree]; exact hlt),
          mul_zero]
      · exact absurd (hinj p hpt pmax hpmaxt heq) hne
      · have hgp0 : g p = 0 := by
          by_contra hgp
          have hpB : p ∈ B := Finset.mem_filter.mpr ⟨hpt, hgp⟩
          have hle := (Finset.le_sup' (fun p => p.2) hpB).trans hsup.le
          omega
        rw [hgp0, zero_mul]
    · intro hpmaxnotin; exact absurd hpmaxt hpmaxnotin
  exact hall p₀ hp₀t

/-- **Char-free faithfulness (Discussion after Proposition 2.7.1).** The representation
`E = tᵃ k[a][t, t⁻¹]` of the Weyl algebra is *faithful in any characteristic*: the algebra
homomorphism `repE : WeylAlgebra k →ₐ[k] Module.End k E` is injective, over any nontrivial
commutative ring `k`.

Unlike the polynomial representation on `k[t]` (`Proposition2_7_1.linearIndep`), which is
faithful only when `k` has characteristic zero, this holds in every characteristic, because the
falling-factorial coefficient `descPoly j = a(a-1)⋯(a-j+1)` is a nonzero (monic) polynomial in
the formal parameter `a` regardless of `char k`. -/
theorem repE_injective : Function.Injective (repE k) := by
  classical
  set mono : ℕ × ℕ → WeylAlgebra k := fun p => WeylAlgebra.monomial k p.1 p.2 with hmono
  -- The monomials span (char-free), so taking linear combinations is surjective.
  have hsurj : Function.Surjective (Finsupp.linearCombination k mono) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp (WeylAlgebra.monomials_span k)
  -- Their images under `repE` are linearly independent (the char-free crux).
  have hli : LinearIndependent k (fun p : ℕ × ℕ => repE k (mono p)) := by
    have hΦ := evalImage_linearIndependent k
    refine LinearIndependent.of_comp
      (LinearMap.applyₗ (Finsupp.single (0 : ℤ) (1 : Polynomial k))) ?_
    convert hΦ using 1
    funext p
    simp only [Function.comp_apply, LinearMap.applyₗ_apply_apply, hmono]
    exact repE_monomial_apply_t0 k p.1 p.2
  rw [injective_iff_map_eq_zero (repE k)]
  intro w hw
  obtain ⟨f, rfl⟩ := hsurj w
  have h0 : Finsupp.linearCombination k (fun p => repE k (mono p)) f = 0 := by
    have hap : repE k (Finsupp.linearCombination k mono f)
        = Finsupp.linearCombination k (fun p => repE k (mono p)) f := by
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp only [map_smul]
    rw [← hap]; exact hw
  have hf : f = 0 :=
    hli.finsuppLinearCombination_injective (h0.trans (map_zero _).symm)
  rw [hf, map_zero]

end Etingof
