import Mathlib
import EtingofRepresentationTheory.Infrastructure.RegularCharacter
import EtingofRepresentationTheory.Chapter5.Proposition5_2_5

/-!
# Lemma 5.4.7: Existence of Nonzero Character Value

In the context of Theorem 5.4.6's proof: let `g ≠ 1` be an element whose conjugacy
class has size `p ^ k` (`p` prime, `k > 0`). Splitting `Irr G` into the trivial
representation, the set `D` of irreducibles whose dimension is divisible by `p`, and
the set `N` of nontrivial irreducibles whose dimension is not divisible by `p`, the
lemma asserts that there exists `V ∈ N` with `χ_V(g) ≠ 0`.

## Book proof (Etingof Lemma 5.4.7)

For `V ∈ D`, the number `(1/p) · dim(V) · χ_V(g)` is an algebraic integer (since
`p ∣ dim V` makes `dim V / p` an integer and character values are algebraic integers),
so `a = ∑_{V ∈ D} (1/p) dim(V) χ_V(g)` is an algebraic integer. By column orthogonality
(5.4.1),

`0 = χ_triv(g) + ∑_{V ∈ D} dim V · χ_V(g) + ∑_{V ∈ N} dim V · χ_V(g) = 1 + p·a + ∑_{V ∈ N} …`.

Were the last summand zero we would get `a = -1/p`, a rational number that is not an
integer, contradicting that `a` is an algebraic integer. Hence some `V ∈ N` has
`χ_V(g) ≠ 0`.

## Mathlib correspondence

Built on the Wedderburn enumeration of irreducibles (`IrrepDecomp`), the column
orthogonality identity `sum_dim_character_eq_zero`, integrality of character values,
and `Etingof.Proposition5_2_5` (a rational algebraic integer is an integer).
-/

open Representation CategoryTheory Finset

namespace Etingof.Lemma5_4_7Aux

variable (G : Type) [Group G] [Fintype G] [DecidableEq G]

/-- Character values of representations of finite groups are algebraic integers. -/
private lemma character_isIntegral (V : FDRep ℂ G) (g : G) :
    IsIntegral ℤ (V.character g) := by
  -- Character = trace of ρ(g), which equals the sum of eigenvalues (roots of charpoly)
  -- Each eigenvalue satisfies λ^|G| = 1, hence is integral over ℤ
  let b := Module.Free.chooseBasis ℂ V
  set M := LinearMap.toMatrix b b (V.ρ g) with hM_def
  set n := Fintype.card G
  -- character = matrix trace = sum of charpoly roots
  have htrace : V.character g = M.trace :=
    LinearMap.trace_eq_matrix_trace ℂ b _
  rw [htrace, Matrix.trace_eq_sum_roots_charpoly M]
  -- Each root of the charpoly is integral over ℤ
  apply IsIntegral.multiset_sum
  intro r hr
  have hr_root : M.charpoly.IsRoot r :=
    (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hr
  -- M^n = 1 since g^n = 1 in a finite group
  have hρ_pow : (V.ρ g) ^ n = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  have hMn : M ^ n = 1 := by
    rw [hM_def, LinearMap.toMatrix_pow, hρ_pow, LinearMap.toMatrix_one]
  -- Derive Nonempty and Nontrivial from the existence of a root
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℂ V) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : M.charpoly = 1 := by simp [Matrix.charpoly, Matrix.det_isEmpty]
    simp [this] at hr
  -- r^n = 1 via spectrum
  have h_spec : r ∈ spectrum ℂ M :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hr_root
  have h_pow : r ^ n ∈ spectrum ℂ (M ^ n) :=
    spectrum.pow_mem_pow M n h_spec
  rw [hMn, spectrum.one_eq] at h_pow
  have hrn : r ^ n = 1 := Set.mem_singleton_iff.mp h_pow
  -- r is integral: root of the monic polynomial X^n - 1 over ℤ
  refine ⟨Polynomial.X ^ n - 1,
    Polynomial.monic_X_pow_sub_C 1 Fintype.card_pos.ne', ?_⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_one, hrn, sub_self]

/-- The trivial representation character at any g is 1. -/
private lemma trivial_character_eq_one (g : G) :
    (FDRep.of (Representation.trivial ℂ G ℂ)).character g = 1 := by
  change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) g) = 1
  simp [Representation.trivial]

/-- The trivial FDRep is simple. -/
private lemma trivialFDRep_simple :
    Simple (FDRep.of (Representation.trivial ℂ G ℂ)) := by
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  haveI : IsSimpleModule (MonoidAlgebra ℂ G)
      (Representation.trivial ℂ G ℂ).asModule := by
    rw [isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one (Module.finrank_self ℂ)
  infer_instance

/-- The conjugacy class of 1 is {1}, so has cardinality 1. -/
private lemma card_conjClass_one :
    Fintype.card { h : G // IsConj (1 : G) h } = 1 := by
  have : Unique { h : G // IsConj (1 : G) h } := by
    refine ⟨⟨⟨1, IsConj.refl 1⟩⟩, ?_⟩
    rintro ⟨h, hh⟩
    simp only [Subtype.mk.injEq]
    rwa [isConj_one_right] at hh
  exact Fintype.card_unique

end Etingof.Lemma5_4_7Aux

open Etingof.Lemma5_4_7Aux

/-- **Lemma 5.4.7.** Let `g` be an element of `G` whose conjugacy class has size
`p ^ k` with `p` prime and `k > 0`. Then there exists a nontrivial irreducible
representation `V` whose dimension is not divisible by `p` and with `χ_V(g) ≠ 0`.
(Etingof Lemma 5.4.7) -/
theorem Etingof.Lemma5_4_7
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G) (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    ∃ V : FDRep ℂ G, Simple V ∧
      ¬ Nonempty (V ≅ FDRep.of (Representation.trivial ℂ G ℂ)) ∧
      ¬ (p ∣ Module.finrank ℂ V) ∧
      V.character g ≠ 0 := by
  -- g ≠ 1 since its conjugacy class has size p^k ≥ 2
  have hg_ne : g ≠ 1 := by
    intro heq; subst heq
    rw [card_conjClass_one] at hconj
    have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
    omega
  haveI : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  let D := IrrepDecomp.mk' (k := ℂ) (G := G)
  -- Column orthogonality: ∑_i d_i * χ_{V_i}(g) = 0
  have hsum : ∑ i : Fin D.n, (D.d i : ℂ) * (D.columnFDRep i).character g = 0 := by
    have := sum_dim_character_eq_zero D D.columnFDRep D.columnFDRep_simple
      D.columnFDRep_injective g hg_ne
    simp_rw [D.finrank_columnFDRep] at this
    exact this
  -- Find the trivial representation in the enumeration
  obtain ⟨i₀, ⟨iso₀⟩⟩ := D.columnFDRep_surjective _ (trivialFDRep_simple G)
  have hd_triv : D.d i₀ = 1 := by
    rw [← D.finrank_columnFDRep i₀]
    have := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv iso₀)
    simp [FDRep.of, Module.finrank_self] at this
    omega
  have hchar_triv : (D.columnFDRep i₀).character g = 1 := by
    have h := FDRep.char_iso iso₀
    rw [← congr_fun h g]
    exact trivial_character_eq_one G g
  -- Suppose no nontrivial irrep with p ∤ dim has nonzero character; derive a contradiction
  by_contra hcon
  rw [not_exists] at hcon
  -- Every nontrivial irrep `V_i` (i ≠ i₀) with p ∤ d_i has χ_{V_i}(g) = 0
  have hcoprime_vanish : ∀ i : Fin D.n, i ≠ i₀ →
      ¬(p ∣ D.d i) → (D.columnFDRep i).character g = 0 := by
    intro i hi hndvd
    haveI := D.columnFDRep_simple i
    by_contra hne
    refine hcon (D.columnFDRep i) ⟨D.columnFDRep_simple i, ?_, ?_, hne⟩
    · exact fun ⟨f⟩ => hi (D.columnFDRep_injective i i₀ ⟨f ≪≫ iso₀⟩)
    · rwa [D.finrank_columnFDRep]
  -- Separate the trivial term: it contributes 1
  have hterm_i₀ : (D.d i₀ : ℂ) * (D.columnFDRep i₀).character g = 1 := by
    rw [hd_triv, hchar_triv]; simp
  -- The remaining terms sum to -1
  have hrest_sum : ∑ i ∈ Finset.univ.erase i₀,
      (D.d i : ℂ) * (D.columnFDRep i).character g = -1 := by
    have h := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h
    rw [hterm_i₀] at h
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  -- Only the p-divisible terms survive (the rest vanish by `hcoprime_vanish`)
  have honly_dvd : ∑ i ∈ (Finset.univ.erase i₀).filter (fun i => p ∣ D.d i),
      (D.d i : ℂ) * (D.columnFDRep i).character g = -1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i₀)
      (fun i => p ∣ D.d i) (fun i => (D.d i : ℂ) * (D.columnFDRep i).character g)
    have hzero : ∑ i ∈ (Finset.univ.erase i₀).filter (fun i => ¬(p ∣ D.d i)),
        (D.d i : ℂ) * (D.columnFDRep i).character g = 0 := by
      apply Finset.sum_eq_zero
      intro i hi; rw [Finset.mem_filter] at hi
      rw [hcoprime_vanish i (Finset.ne_of_mem_erase hi.1) hi.2, mul_zero]
    rw [hzero, add_zero] at hsplit
    rw [hsplit]; exact hrest_sum
  -- Factor out p: the surviving sum equals p * S with S an algebraic integer
  set S_set := (Finset.univ.erase i₀).filter (fun i => p ∣ D.d i)
  set S := ∑ i ∈ S_set, ((D.d i / p : ℕ) : ℂ) * (D.columnFDRep i).character g
  have hfactor : ∑ i ∈ S_set, (D.d i : ℂ) * (D.columnFDRep i).character g =
      (p : ℂ) * S := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_filter] at hi
    have : (D.d i : ℂ) = (p : ℂ) * ((D.d i / p : ℕ) : ℂ) := by
      have hdi : D.d i = p * (D.d i / p) := Nat.eq_mul_of_div_eq_right hi.2 rfl
      exact_mod_cast hdi
    rw [this]; ring
  have hpS : (p : ℂ) * S = -1 := by rw [← hfactor]; exact honly_dvd
  have hS_int : IsIntegral ℤ S := IsIntegral.sum _ fun i _ =>
    (isIntegral_algebraMap (R := ℤ)).mul (character_isIntegral G (D.columnFDRep i) g)
  -- S = -1/p, a rational that is not an integer
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hS_val : S = -(1 / (p : ℂ)) := by
    field_simp
    linear_combination hpS
  have h_rat_eq : algebraMap ℚ ℂ (-(1 / (p : ℚ))) = -(1 / (p : ℂ)) := by push_cast; ring
  have h_integral : IsIntegral ℤ (algebraMap ℚ ℂ (-(1 / (p : ℚ)))) := by
    rw [h_rat_eq, ← hS_val]; exact hS_int
  obtain ⟨n, hn⟩ := (Etingof.Proposition5_2_5 _).mp h_integral
  have h1 : (n : ℚ) * p = -1 := by
    have hp_ne_q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have := hn; field_simp at this; linarith
  have h2 : n * (p : ℤ) = -1 := by exact_mod_cast h1
  have h3 : (p : ℤ) ∣ 1 := ⟨-n, by linear_combination h2⟩
  have h4 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h3
  have h5 : 1 < (p : ℤ) := by exact_mod_cast hp.one_lt
  omega
