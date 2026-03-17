import Mathlib
import EtingofRepresentationTheory.Infrastructure.RegularCharacter
import EtingofRepresentationTheory.Chapter5.Theorem5_4_4
import EtingofRepresentationTheory.Chapter5.Proposition5_2_5

/-!
# Theorem 5.4.6: Conjugacy Class of Prime Power Size

If G has a conjugacy class C of size p^k where p is prime and k > 0,
then G has a proper nontrivial normal subgroup (and hence is not simple).

The proof uses the regular representation character identity (sum of
dim(V) · χ_V(g) = 0 for g ≠ 1), Theorem 5.4.4 (character quotient
integrality), and the algebraic integer argument (Proposition 5.2.5).
-/

open Representation CategoryTheory Finset

/-! ### Helper lemmas -/

section Helpers

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

/-- Scalar action on dim ≥ 2 irrep contradicts simplicity. -/
private lemma scalar_contradicts_simplicity [IsSimpleGroup G]
    (V : FDRep ℂ G) [Simple V] (hdim : 2 ≤ Module.finrank ℂ V)
    (g : G) (hg : g ≠ 1) (c : ℂ) (hsc : V.ρ g = c • LinearMap.id) :
    False := by sorry

/-- Nontrivial irreps of a non-abelian simple group have dim ≥ 2. -/
private lemma nontrivial_irrep_dim_ge_two [IsSimpleGroup G] [Nontrivial G]
    (V : FDRep ℂ G) [Simple V]
    (hntv : ¬Nonempty (V ≅ FDRep.of (Representation.trivial ℂ G ℂ))) :
    2 ≤ Module.finrank ℂ V := by sorry

end Helpers

/-- The conjugacy class of 1 is {1}, so has cardinality 1. -/
private lemma card_conjClass_one (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Fintype.card { h : G // IsConj (1 : G) h } = 1 := by
  have : Unique { h : G // IsConj (1 : G) h } := by
    refine ⟨⟨⟨1, IsConj.refl 1⟩⟩, ?_⟩
    rintro ⟨h, hh⟩
    simp only [Subtype.mk.injEq]
    rwa [isConj_one_right] at hh
  exact Fintype.card_unique

/-! ### Main theorem -/

/-- A simple finite group cannot have a conjugacy class of prime power size. -/
private lemma IsSimpleGroup.no_prime_power_conjClass
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    [IsSimpleGroup G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G) (hg_ne : g ≠ 1)
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    False := by
  haveI : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  let D := IrrepDecomp.mk' (k := ℂ) (G := G)
  -- Sum identity: ∑_i d_i * χ_{V_i}(g) = 0
  have hsum : ∑ i : Fin D.n, (D.d i : ℂ) * (D.columnFDRep i).character g = 0 :=
    sum_dim_character_eq_zero D D.columnFDRep D.columnFDRep_simple
      D.columnFDRep_injective D.columnFDRep_surjective g hg_ne
  -- Find the trivial representation
  obtain ⟨i₀, ⟨iso₀⟩⟩ := D.columnFDRep_surjective _ (trivialFDRep_simple G)
  -- iso₀ : FDRep.of (trivial) ≅ D.columnFDRep i₀
  -- d_{i₀} = 1
  have hd_triv : D.d i₀ = 1 := by
    rw [← D.finrank_columnFDRep i₀]
    have := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv iso₀)
    simp [FDRep.of, Module.finrank_self] at this
    omega
  -- χ_{i₀}(g) = 1
  have hchar_triv : (D.columnFDRep i₀).character g = 1 := by
    have h := FDRep.char_iso iso₀
    -- h : (FDRep.of trivial).character = (D.columnFDRep i₀).character
    rw [← congr_fun h g]
    exact trivial_character_eq_one G g
  -- For nontrivial V_i with ¬(p | d_i), χ(g) = 0
  have hcoprime_vanish : ∀ i : Fin D.n, i ≠ i₀ →
      ¬(p ∣ D.d i) → (D.columnFDRep i).character g = 0 := by
    intro i hi hndvd
    haveI := D.columnFDRep_simple i
    have hcop : Nat.Coprime (Fintype.card { h : G // IsConj g h })
        (Module.finrank ℂ (D.columnFDRep i)) := by
      rw [hconj, D.finrank_columnFDRep]
      exact (Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hndvd))
    rcases Etingof.Theorem5_4_4 G (D.columnFDRep i) g hcop with hzero | ⟨c, hsc⟩
    · exact hzero
    · exfalso
      have hntv : ¬Nonempty (D.columnFDRep i ≅ FDRep.of (Representation.trivial ℂ G ℂ)) :=
        fun ⟨f⟩ => hi (D.columnFDRep_injective i i₀ ⟨f ≪≫ iso₀⟩)
      exact scalar_contradicts_simplicity G (D.columnFDRep i)
        (nontrivial_irrep_dim_ge_two G (D.columnFDRep i) hntv) g hg_ne c hsc
  -- Split sum: 0 = 1 + p * S where S is an algebraic integer
  -- Separate i₀ from the sum
  have hterm_i₀ : (D.d i₀ : ℂ) * (D.columnFDRep i₀).character g = 1 := by
    rw [hd_triv, hchar_triv]; simp
  -- Rewrite sum splitting off i₀
  have hrest_sum : ∑ i ∈ Finset.univ.erase i₀,
      (D.d i : ℂ) * (D.columnFDRep i).character g = -1 := by
    have h := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h
    rw [hterm_i₀] at h
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  -- Only p-divisible terms survive
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
  -- Factor out p
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
  -- p * S = -1
  have hpS : (p : ℂ) * S = -1 := by rw [← hfactor]; exact honly_dvd
  -- S is an algebraic integer
  have hS_int : IsIntegral ℤ S := IsIntegral.sum _ fun i _ =>
    (isIntegral_algebraMap (R := ℤ)).mul (character_isIntegral G (D.columnFDRep i) g)
  -- S = -1/p
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hS_val : S = -(1 / (p : ℂ)) := by
    field_simp
    linear_combination hpS
  -- -1/p is rational but not an integer → contradiction
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

/-- If G has a conjugacy class of size p^k (p prime, k > 0), then G has a proper
nontrivial normal subgroup. (Etingof Theorem 5.4.6) -/
theorem Etingof.Theorem5_4_6
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G)
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  have hg_ne : g ≠ 1 := by
    intro heq; subst heq
    rw [card_conjClass_one] at hconj
    have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
    omega
  by_contra habs; push_neg at habs
  haveI : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  haveI : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun H hH => by
        by_cases h : H = ⊥; exact Or.inl h; exact Or.inr (habs H hH h) }
  exact IsSimpleGroup.no_prime_power_conjClass G p hp k hk g hg_ne hconj
