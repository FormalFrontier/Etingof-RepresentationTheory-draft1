import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_3_2
import EtingofRepresentationTheory.Chapter5.Proposition5_2_5

/-!
# Theorem 5.3.1: Dimension Divides Group Order

For any irreducible representation `V` of a finite group `G` over `ℂ`:
  `dim V ∣ |G|`.

## Book proof (Etingof Theorem 5.3.1)

Let `C₁, …, Cₙ` be the conjugacy classes of `G` with representatives `gᵢ`, and set
`λᵢ = χ_V(gᵢ) · |Cᵢ| / dim V`.  Consider
`Σᵢ λᵢ · conj(χ_V(gᵢ))`.

This is an algebraic integer, because each `λᵢ` is one (Proposition 5.3.2), each
`conj(χ_V(gᵢ))` is a sum of roots of unity hence an algebraic integer, and the algebraic
integers form a ring (Proposition 5.2.4).  On the other hand, summing over the whole group
and using `(χ_V, χ_V) = 1` (orthogonality of characters, irreducible `V`), the same sum
equals `|G| / dim V`.  Since `|G| / dim V` is rational and an algebraic integer, it is an
integer (Proposition 5.2.5), i.e. `dim V ∣ |G|`.

In the formalization we sum over the whole group throughout: the algebraic-integer side is
the regrouping of `Σ_{g ∈ G} χ_V(g) · χ_V(g⁻¹) / dim V` over conjugacy classes (each class
contributes `λ · χ_V(g⁻¹)`), and the rational side is `|G| / dim V`, the two being equal by
`FDRep.char_orthonormal`.  We use `χ_V(g⁻¹)` in place of `conj(χ_V(g))`; both are sums of
roots of unity, and this is exactly the factor appearing in Mathlib's orthogonality relation.

## Mathlib correspondence

Uses `FDRep.character`, `FDRep.char_orthonormal`, `IsIntegral ℤ`, Proposition 5.3.2, and
Proposition 5.2.5.
-/

set_option linter.unusedFintypeInType false in
open CategoryTheory Polynomial Matrix in
/-- The value of the character of a finite-dimensional representation of a finite group at any
element is an algebraic integer: it is the sum of the eigenvalues of `V.ρ g`, each of which is
a root of unity (since `g` has finite order). -/
theorem FDRep.character_isIntegral
    {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (g : G) :
    IsIntegral ℤ (V.character g) := by
  classical
  set N := Fintype.card G with hN
  have hNpos : 0 < N := Fintype.card_pos
  -- `f = V.ρ g` has finite order: `f ^ N = 1`.
  set f : Module.End ℂ V := V.ρ g with hf
  have hfN : f ^ N = 1 := by rw [hf, ← map_pow, pow_card_eq_one, map_one]
  -- The character is the trace of `f`, which (charpoly splits over `ℂ`) is the sum of the
  -- roots of its characteristic polynomial.
  have hchar : V.character g = f.charpoly.roots.sum := by
    rw [FDRep.character,
      Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits f.charpoly)]
  rw [hchar]
  -- Each root of the charpoly is an eigenvalue of `f`, hence (as `f ^ N = 1`) a root of unity.
  have hroot : ∀ r ∈ f.charpoly.roots, IsIntegral ℤ r := by
    intro r hr
    -- `r` is a genuine root, hence an eigenvalue of `f`.
    have hr0 : f.charpoly.IsRoot r :=
      (Polynomial.mem_roots (f.charpoly_monic.ne_zero)).mp hr
    have heig : f.HasEigenvalue r :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f r).mpr hr0
    -- Then `r ^ N` is an eigenvalue of `f ^ N = 1`, so `r ^ N = 1`.
    have heigN : (1 : Module.End ℂ V).HasEigenvalue (r ^ N) := by
      have := heig.pow N
      rwa [hfN] at this
    have hrN : r ^ N = 1 := by
      obtain ⟨v, hv⟩ := heigN.exists_hasEigenvector
      -- `(1 : End) v = r ^ N • v`, i.e. `v = r ^ N • v`.
      have happ : v = r ^ N • v := by
        have h := hv.apply_eq_smul
        rwa [Module.End.one_apply] at h
      have : (r ^ N - 1) • v = 0 := by
        rw [sub_smul, one_smul, ← happ, sub_self]
      rcases smul_eq_zero.mp this with hz | hz
      · exact sub_eq_zero.mp hz
      · exact absurd hz hv.2
    -- A root of `X ^ N - 1` (monic, with integer coefficients) is integral over `ℤ`.
    refine ⟨X ^ N - C 1, Polynomial.monic_X_pow_sub_C 1 hNpos.ne', ?_⟩
    simp [hrN]
  -- The algebraic integers form a subalgebra; the sum of integral elements is integral.
  have hmem : f.charpoly.roots.sum ∈ integralClosure ℤ ℂ :=
    (integralClosure ℤ ℂ).multiset_sum_mem (fun r hr => hroot r hr)
  exact hmem

open CategoryTheory in
/-- **Theorem 5.3.1.** The dimension of an irreducible complex representation `V` of a finite
group `G` divides the order of `G`. (Etingof Theorem 5.3.1) -/
theorem Etingof.Theorem5_3_1
    (G : Type) [Group G] [Fintype G]
    (V : FDRep ℂ G) [Simple V] :
    Module.finrank ℂ V ∣ Fintype.card G := by
  classical
  have hN0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hN0
  -- Orthonormality of characters: `∑_{g ∈ G} χ_V(g) · χ_V(g⁻¹) = |G|`.
  have hortho : ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
    have h := FDRep.char_orthonormal V V
    rw [if_pos ⟨Iso.refl V⟩] at h
    have h2 := congrArg (fun x => (Fintype.card G : ℂ) • x) h
    simpa using h2
  -- `V` is simple, hence its underlying space is nontrivial and `dim V > 0`.
  have hdpos : 0 < Module.finrank ℂ V := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with hfr0 | hpos
    · exfalso
      haveI : Subsingleton V := Module.finrank_zero_iff.mp hfr0
      have hzero : ∀ g : G, V.character g = 0 := fun g => by
        rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
      rw [Finset.sum_congr rfl (fun g _ => by rw [hzero g, zero_mul]),
        Finset.sum_const_zero] at hortho
      exact hN0 hortho.symm
    · exact hpos
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  -- The integral combination `T = ∑_C λ_C · χ_V(g_C⁻¹)`, one term per conjugacy class `C`.
  set T : ℂ := ∑ K : ConjClasses G,
      ((Fintype.card {h // IsConj K.out h} : ℂ) * V.character K.out
          / (Module.finrank ℂ V : ℂ)) * V.character (K.out)⁻¹ with hT_def
  -- Each term is a product of two algebraic integers (Prop. 5.3.2 and `character_isIntegral`),
  -- so `T` is an algebraic integer.
  have hT_int : IsIntegral ℤ T := by
    rw [hT_def]
    refine (integralClosure ℤ ℂ).sum_mem (fun K _ => ?_)
    exact (Etingof.Proposition5_3_2 G V K.out hdpos).mul (FDRep.character_isIntegral V (K.out)⁻¹)
  -- Regrouping `∑_{g ∈ G}` over conjugacy classes, then using `χ_V` is a class function.
  have hregroup : ∑ g : G, V.character g * V.character g⁻¹
      = ∑ K : ConjClasses G,
          (Fintype.card {h // IsConj K.out h} : ℂ)
            * (V.character K.out * V.character (K.out)⁻¹) := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (ConjClasses G)))
          (g := ConjClasses.mk) (f := fun g => V.character g * V.character g⁻¹)
          (fun g _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    have hmkout : ConjClasses.mk K.out = K := Quotient.out_eq K
    -- On the fiber of `K`, the summand is constant, equal to the value at the representative.
    have hconst : ∀ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = K),
        V.character g * V.character g⁻¹
          = V.character K.out * V.character (K.out)⁻¹ := by
      intro g hg
      rw [Finset.mem_filter] at hg
      have hconj : IsConj g K.out :=
        ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [hmkout]; exact hg.2)
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have e1 : V.character K.out = V.character g := by
        rw [← hc]; exact V.char_conj g c
      have e2 : V.character (K.out)⁻¹ = V.character g⁻¹ := by
        rw [← hc, show (c * g * c⁻¹)⁻¹ = c * g⁻¹ * c⁻¹ by group]
        exact V.char_conj g⁻¹ c
      rw [e1, e2]
    have hfilt : Finset.univ.filter (fun g => ConjClasses.mk g = K)
        = Finset.univ.filter (fun h => IsConj K.out h) := by
      apply Finset.filter_congr
      intro g _
      have hiff : (ConjClasses.mk g = K) ↔ (ConjClasses.mk g = ConjClasses.mk K.out) := by
        rw [hmkout]
      rw [hiff, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]
    have hcard : (Finset.univ.filter (fun g => ConjClasses.mk g = K)).card
        = Fintype.card {h // IsConj K.out h} := by
      rw [hfilt, ← Fintype.card_subtype]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcard]
  -- Therefore `|G|/dim V = T`, an algebraic integer.
  have hdT : (Module.finrank ℂ V : ℂ) * T = (Fintype.card G : ℂ) := by
    rw [hT_def, Finset.mul_sum]
    have hstep : ∀ K : ConjClasses G,
        (Module.finrank ℂ V : ℂ)
            * (((Fintype.card {h // IsConj K.out h} : ℂ) * V.character K.out
                  / (Module.finrank ℂ V : ℂ)) * V.character (K.out)⁻¹)
          = (Fintype.card {h // IsConj K.out h} : ℂ)
              * (V.character K.out * V.character (K.out)⁻¹) := by
      intro K
      field_simp
    rw [Finset.sum_congr rfl (fun K _ => hstep K), ← hregroup, hortho]
  -- `T = |G|/dim V` is rational; an algebraic integer that is rational is an integer (Prop. 5.2.5).
  set q : ℚ := (Fintype.card G : ℚ) / (Module.finrank ℂ V : ℚ) with hq_def
  have hq_c : algebraMap ℚ ℂ q = (Fintype.card G : ℂ) / (Module.finrank ℂ V : ℂ) := by
    rw [hq_def, map_div₀, map_natCast, map_natCast]
  have hT_c : T = (Fintype.card G : ℂ) / (Module.finrank ℂ V : ℂ) := by
    rw [eq_div_iff hd0, mul_comm]; exact hdT
  have hqint : ∃ n : ℤ, q = n := by
    rw [← Etingof.Proposition5_2_5 q, hq_c, ← hT_c]; exact hT_int
  obtain ⟨n, hn⟩ := hqint
  -- `|G| = n · dim V`, hence `dim V ∣ |G|`.
  rw [hq_def, div_eq_iff (by exact_mod_cast hdpos.ne')] at hn
  have hZ : (Fintype.card G : ℤ) = n * (Module.finrank ℂ V : ℤ) := by exact_mod_cast hn
  have : (Module.finrank ℂ V : ℤ) ∣ (Fintype.card G : ℤ) := ⟨n, by rw [hZ]; ring⟩
  exact_mod_cast this
