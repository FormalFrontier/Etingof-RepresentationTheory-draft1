import Mathlib

/-!
# The dimension of a complex irreducible representation divides `|G|`

This file works toward the classical theorem of Frobenius: the dimension of a
complex irreducible representation of a finite group `G` divides the order of
`G`. It is the general, reusable ingredient behind the odd-order crux of
Problem 6.1.6(c) (`isCyclic_of_odd_card`): a group of odd order has no
`2`-dimensional irreducible representation, because `2 ∤ |G|`.

The development is top-down (see the project's `CLAUDE.md`): the headline
theorem `finrank_dvd_card_of_irreducible` is stated with a `sorry` proof, while
the two central-character ingredients (`FDRep.isIntegral_character` and
`FDRep.isIntegral_classSum_scalar`) are proved here in full.

## Main results

* `isIntegral_int_of_pow_eq_one`: a complex root of unity is an algebraic
  integer (root of the monic `X ^ n - 1`).
* `FDRep.isIntegral_character`: **character values are algebraic integers.**
  The eigenvalues of `ρ g` are roots of unity (`ρ g` has finite order), and the
  character `χ_V(g)` is their sum, hence integral over `ℤ`.
* `FDRep.isIntegral_classSum_scalar`: **the central-character value on a class
  sum is an algebraic integer.**
* `finrank_dvd_card_of_irreducible` (`sorry`): the Frobenius divisibility
  theorem itself.

## References

Etingof et al., *Introduction to Representation Theory*; the theorem is standard
(Frobenius). Building blocks used: `Matrix.trace_eq_sum_roots_charpoly`,
`Matrix.eval_charpoly`, `Matrix.exists_mulVec_eq_zero_iff`,
`IsIntegrallyClosed`/`Niven` (rational algebraic integers are integers),
`FDRep.scalar_product_char_eq_finrank_equivariant`.
-/

open Polynomial Matrix Module CategoryTheory

/-- A complex number `r` with `r ^ n = 1` for some `0 < n` is integral over `ℤ`:
it is a root of the monic integer polynomial `X ^ n - 1`. -/
theorem isIntegral_int_of_pow_eq_one {r : ℂ} {n : ℕ} (hn : 0 < n) (h : r ^ n = 1) :
    IsIntegral ℤ r := by
  refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 hn.ne', ?_⟩
  simp [h]

namespace FDRep

variable {G : Type*} [Group G] [Finite G]

/-- **Character values are algebraic integers.**

For a finite group `G`, a complex representation `V`, and `g : G`, the character
value `χ_V(g) = tr(ρ g)` is integral over `ℤ`.

Proof: `ρ g` has finite order `n` (as `G` is finite), so, in a basis, its matrix
`A` satisfies `A ^ n = 1`. Over `ℂ` the trace equals the sum of the roots of the
characteristic polynomial; each such root `r` is an eigenvalue, so `A *ᵥ v = r • v`
for some `v ≠ 0`, whence `r ^ n • v = (A ^ n) *ᵥ v = v` forces `r ^ n = 1`. Thus
every root is a root of unity, hence an algebraic integer, and their sum `χ_V(g)`
is too. -/
theorem isIntegral_character (V : FDRep ℂ G) (g : G) : IsIntegral ℤ (V.character g) := by
  classical
  -- `ρ g` has finite order `n`, and `(ρ g) ^ n = 1`.
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  set n := orderOf g with hn
  have hn0 : 0 < n := hfin.orderOf_pos
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hρ : (V.ρ g) ^ n = 1 := by rw [← map_pow, hgn, map_one]
  -- Work in a finite basis; let `A` be the matrix of `ρ g`.
  set d := finrank ℂ V with hd
  set b := Module.finBasis ℂ V with hb
  set A : Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix b b (V.ρ g) with hA
  have hAn : A ^ n = 1 := by
    rw [hA, LinearMap.toMatrix_pow, hρ, LinearMap.toMatrix_one]
  -- The character is the matrix trace, hence the sum of the charpoly roots.
  have htr : V.character g = A.trace := by
    rw [show V.character g = LinearMap.trace ℂ V (V.ρ g) from rfl,
      LinearMap.trace_eq_matrix_trace ℂ b (V.ρ g)]
  have hsum : V.character g = (A.charpoly.roots).sum := by
    rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  -- Each root of the charpoly is a root of unity, hence integral over `ℤ`.
  have hroot : ∀ r ∈ A.charpoly.roots, IsIntegral ℤ r := by
    intro r hr
    -- `r` is a genuine root of the characteristic polynomial.
    have hIsRoot : A.charpoly.IsRoot r := (Polynomial.mem_roots'.mp hr).2
    -- so `det (scalar r - A) = 0`, giving an eigenvector `v ≠ 0` with `A *ᵥ v = r • v`.
    have hdet : (Matrix.scalar (Fin d) r - A).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact hIsRoot
    obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hscal : (Matrix.scalar (Fin d) r) *ᵥ v = r • v := by
      rw [Matrix.scalar_apply]
      funext x
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    have hev : A *ᵥ v = r • v := by
      have hsub : (Matrix.scalar (Fin d) r) *ᵥ v - A *ᵥ v = 0 := by
        rw [← Matrix.sub_mulVec]; exact hMv
      rw [hscal] at hsub
      exact (sub_eq_zero.mp hsub).symm
    -- iterate the eigenvalue relation: `(A ^ k) *ᵥ v = r ^ k • v`.
    have hpow : ∀ k, (A ^ k) *ᵥ v = r ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
    -- `r ^ n • v = (A ^ n) *ᵥ v = 1 *ᵥ v = v`, and `v ≠ 0` forces `r ^ n = 1`.
    have hrn : r ^ n = 1 := by
      have he := hpow n
      rw [hAn, Matrix.one_mulVec] at he
      have hz : (r ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← he, sub_self]
      rcases smul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv0
    exact isIntegral_int_of_pow_eq_one hn0 hrn
  -- the sum of algebraic integers is an algebraic integer
  rw [hsum]
  exact IsIntegral.multiset_sum hroot

/-- **Central character integrality (Frobenius, step 2).**

For an irreducible `V` and a conjugacy class with representative `g₀` and size
`c`, the scalar `ω = c · χ_V(g₀) / d` by which the class sum acts on `V` is
integral over `ℤ`.

Proof: let `z = ∑_{x ∼ g₀} x` be the class sum inside the integral group ring
`ℤ[G]`. Since `G` is finite, `ℤ[G]` is module-finite over `ℤ`, so `z` is integral
over `ℤ` (`IsIntegral.of_finite`). Let `Φ : ℤ[G] →ₐ[ℤ] End ℂ V` extend the
representation. As conjugation permutes the class, `Φ z = ∑_{x ∼ g₀} ρ x` commutes
with every `ρ g`, hence is a `V`-endomorphism; by Schur's lemma over the
algebraically closed field `ℂ` it is a scalar `Φ z = c • id`. Taking traces,
`c · d = tr(Φ z) = ∑_{x ∼ g₀} χ_V(x) = |C| · χ_V(g₀)`, so `c = ω`. Finally `Φ z`
is integral over `ℤ` (`IsIntegral.map`), and `Φ z = c • id = algebraMap ℂ ω`,
so `ω` is integral over `ℤ` (`isIntegral_algebraMap_iff`, the algebra map being
injective on the nonzero space `V`). -/
theorem isIntegral_classSum_scalar (V : FDRep ℂ G) [Simple V] (g₀ : G) :
    IsIntegral ℤ ((Nat.card {x // IsConj g₀ x} : ℂ) * V.character g₀ / (finrank ℂ V : ℂ)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- `V` is nonzero, hence has positive dimension and a nonzero-scalar-faithful action.
  have hpos : 0 < finrank ℂ V := by
    by_contra h
    have h0 : finrank ℂ V = 0 := by omega
    have hsub : Subsingleton (V : Type) := Module.finrank_zero_iff.mp h0
    have hsub2 : Subsingleton (V ⟶ V) :=
      ⟨fun f g => Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext fun x => hsub.elim _ _))⟩
    have hSS : finrank ℂ (V ⟶ V) = 1 := by rw [FDRep.finrank_hom_simple_simple]; simp
    have : finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
    omega
  haveI : Nontrivial (V : Type) := (finrank_pos_iff (R := ℂ)).mp hpos
  have hfr0 : (finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  -- The conjugacy class of `g₀`, as a finset, and its class sum in `ℤ[G]`.
  set C : Finset G := Finset.univ.filter (fun x => IsConj g₀ x) with hC
  set z : MonoidAlgebra ℤ G := ∑ x ∈ C, MonoidAlgebra.single x 1 with hz
  -- The algebra hom `ℤ[G] →ₐ[ℤ] End ℂ V` extending the representation.
  set Φ : MonoidAlgebra ℤ G →ₐ[ℤ] Module.End ℂ (V : Type) :=
    MonoidAlgebra.lift ℤ (Module.End ℂ V) G V.ρ with hΦ
  have hΦz : Φ z = ∑ x ∈ C, V.ρ x := by
    rw [hz, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hΦ, MonoidAlgebra.lift_single, one_smul]
  -- `Φ z` commutes with every `V.ρ g`: conjugation permutes the class.
  have hcomm : ∀ g : G, V.ρ g * Φ z = Φ z * V.ρ g := by
    intro g
    rw [hΦz, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_nbij' (fun x => g * x * g⁻¹) (fun x => g⁻¹ * x * g) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.trans (isConj_iff.mpr ⟨g, rfl⟩)
    · intro a ha
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    · intro a _; group
    · intro a _; group
    · intro a _
      simp only [← MonoidHom.map_mul]
      congr 1
      group
  -- Package `Φ z` as an endomorphism of `V` in `FDRep ℂ G`, then apply Schur's lemma.
  have hf : ∀ g : G, (Φ z) ∘ₗ V.ρ g = V.ρ g ∘ₗ (Φ z) := fun g => (hcomm g).symm
  let φ : V ⟶ V :=
    { hom := FGModuleCat.ofHom (Φ z)
      comm := fun g => by ext v; exact LinearMap.congr_fun (hf g) v }
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ φ
  -- Extract the underlying scalar identity `Φ z = c • id`.
  have hΦz_scalar : Φ z = c • LinearMap.id := by
    have key : (FGModuleCat.ofHom (Φ z)).hom.hom = (c • 𝟙 V).hom.hom.hom :=
      congrArg (fun ψ : V ⟶ V => ψ.hom.hom.hom) hc.symm
    rw [show (FGModuleCat.ofHom (Φ z)).hom.hom = Φ z from rfl] at key
    rw [key, Action.smul_hom, Action.id_hom]
    rfl
  -- Compute the scalar via the trace: `tr (Φ z) = |C| · χ(g₀)` and `tr (c • id) = c · d`.
  have htr : LinearMap.trace ℂ (V : Type) (Φ z) = (C.card : ℂ) * V.character g₀ := by
    rw [hΦz, map_sum]
    have hconst : ∀ x ∈ C, LinearMap.trace ℂ (V : Type) (V.ρ x) = V.character g₀ := by
      intro x hx
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h, rfl⟩ := isConj_iff.mp hx
      exact V.char_conj g₀ h
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have htr2 : LinearMap.trace ℂ (V : Type) (Φ z) = c * (finrank ℂ V : ℂ) := by
    rw [hΦz_scalar, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hcd : (C.card : ℂ) * V.character g₀ = c * (finrank ℂ V : ℂ) := htr.symm.trans htr2
  -- Identify the target scalar with `c`.
  have hcard : Nat.card {x // IsConj g₀ x} = C.card := by
    rw [Nat.card_eq_fintype_card, hC, Fintype.card_subtype]
  have hω : (Nat.card {x // IsConj g₀ x} : ℂ) * V.character g₀ / (finrank ℂ V : ℂ) = c := by
    rw [show ((Nat.card {x // IsConj g₀ x} : ℕ) : ℂ) = (C.card : ℂ) by rw [hcard]]
    rw [hcd, mul_div_assoc, div_self hfr0, mul_one]
  rw [hω]
  -- `z` is integral over `ℤ` (`ℤ[G]` is module-finite over `ℤ`), so `Φ z = c • id` is too.
  have hz_int : IsIntegral ℤ z := by
    haveI : Module.Finite ℤ (MonoidAlgebra ℤ G) := Module.Finite.of_basis Finsupp.basisSingleOne
    exact IsIntegral.of_finite ℤ z
  have hΦz_int : IsIntegral ℤ (Φ z) := IsIntegral.map Φ hz_int
  rw [hΦz_scalar, ← Module.algebraMap_end_eq_smul_id] at hΦz_int
  -- Descend integrality of `c • id = algebraMap c` to integrality of `c`.
  have hinj : Function.Injective (algebraMap ℂ (Module.End ℂ (V : Type))) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hk := Module.ker_algebraMap_end ℂ (V : Type) r hr0
    rw [hr, LinearMap.ker_zero] at hk
    exact absurd hk top_ne_bot
  exact (isIntegral_algebraMap_iff hinj).mp hΦz_int

end FDRep

/-- **Frobenius' theorem: the dimension of a complex irreducible representation of
a finite group divides the group order.**

Proof (top-down; see #6714): with `d = finrank ℂ V` and `χ = V.character`, Schur
orthogonality `⟨χ, χ⟩ = 1` gives `|G| = ∑_C c · |χ(g_C)|²`, so
`|G| / d = ∑_C ω_C · conj(χ(g_C))` with `ω_C = c · χ(g_C) / d`. Each `ω_C`
(`FDRep.isIntegral_classSum_scalar`) and each `conj(χ(g_C))`
(`FDRep.isIntegral_character`, closed under complex conjugation) is an algebraic
integer, so `|G| / d ∈ ℚ` is an algebraic integer, hence an integer
(`ℤ` is integrally closed in `ℚ`); therefore `d ∣ |G|`. -/
theorem finrank_dvd_card_of_irreducible {G : Type*} [Group G] [Fintype G]
    (V : FDRep ℂ G) [Simple V] : Module.finrank ℂ V ∣ Fintype.card G := by
  sorry
