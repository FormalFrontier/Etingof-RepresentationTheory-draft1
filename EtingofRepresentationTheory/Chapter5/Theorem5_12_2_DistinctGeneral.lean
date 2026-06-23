import EtingofRepresentationTheory.Chapter5.Lemma5_13_2
import EtingofRepresentationTheory.Infrastructure.SpechtModuleSimple

/-!
# Theorem 5.12.2 (Part 2), general field: Distinctness over a general field

For distinct partitions `λ ≠ μ`, the Specht modules `SpechtModuleK k n λ` and
`SpechtModuleK k n μ` are not isomorphic as `k[S_n]`-modules, for any field `k`
of characteristic zero. This is the general-field version of
`Theorem5_12_2_distinct` (which is hardcoded over ℂ).

The proof ports the Young-projector vanishing chain (`RowSymmetrizer`,
`ColumnAntisymmetrizer`, Lemma 5.13.1, Lemma 5.13.2) from ℂ to a general field,
reusing the field-free combinatorial core `pigeonhole_transposition_general`.
The only field-specific input is `(2 : k) ≠ 0`, supplied by `CharZero`.

## Main results

* `RowSymmetrizerK`, `ColumnAntisymmetrizerK` — the symmetrizer factors over `k`
* `Lemma5_13_2_K` — `a_λ · x · b_μ = 0` when `μ` does not dominate `λ`
* `youngSymmetrizerK_sq_ne_zero` — `c_λ² ≠ 0`
* `Theorem5_12_2_distinct_general` — distinctness of Specht modules over `k`
-/

namespace Etingof

noncomputable section
open scoped Classical

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)

/-! ### Symmetrizer factors over a general commutative ring -/

/-- The row symmetrizer `a_λ = ∑_{g ∈ P_λ} g` in `k[S_n]`, over a general
commutative ring `k`. This is the right-hand factor of `YoungSymmetrizerK`. -/
def RowSymmetrizerK (k : Type*) [CommRing k] (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (G' n) :=
  haveI : DecidablePred (· ∈ RowSubgroup n la) := Classical.decPred _
  ∑ g : (RowSubgroup n la), MonoidAlgebra.of k _ g.val

/-- The column antisymmetrizer `b_λ = ∑_{g ∈ Q_λ} sign(g) · g` in `k[S_n]`,
over a general commutative ring `k`. This is the left-hand factor of
`YoungSymmetrizerK`. -/
def ColumnAntisymmetrizerK (k : Type*) [CommRing k] (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (G' n) :=
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  ∑ g : (ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • MonoidAlgebra.of k _ g.val

/-- The Young symmetrizer factors as `c_λ = b_λ · a_λ` over a general ring. -/
theorem youngSymmetrizerK_eq_factored (k : Type*) [CommRing k] (n : ℕ)
    (la : Nat.Partition n) :
    YoungSymmetrizerK k n la = ColumnAntisymmetrizerK k n la * RowSymmetrizerK k n la :=
  rfl

/-! ### Absorption lemmas (Lemma 5.13.1 over a general ring) -/

/-- The row symmetrizer absorbs row group elements on the right:
`a_λ * of(p) = a_λ` for `p ∈ P_λ`. -/
theorem RowSymmetrizerK_mul_of_row {k : Type*} [CommRing k] {n : ℕ} {la : Nat.Partition n}
    (p : G' n) (hp : p ∈ RowSubgroup n la) :
    RowSymmetrizerK k n la * MonoidAlgebra.of k (G' n) p = RowSymmetrizerK k n la := by
  classical
  simp only [RowSymmetrizerK]
  rw [Finset.sum_mul]
  simp_rw [← (MonoidAlgebra.of k (G' n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- Column group elements are absorbed on the left of `b_λ` with sign:
`of(q) * b_λ = sign(q) • b_λ` for `q ∈ Q_λ`. -/
theorem of_col_mul_ColumnAntisymmetrizerK {k : Type*} [CommRing k] {n : ℕ}
    {la : Nat.Partition n} (q : G' n) (hq : q ∈ ColumnSubgroup n la) :
    MonoidAlgebra.of k (G' n) q * ColumnAntisymmetrizerK k n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : k)) • ColumnAntisymmetrizerK k n la := by
  classical
  simp only [ColumnAntisymmetrizerK]
  rw [Finset.mul_sum, Finset.smul_sum]
  simp_rw [Algebra.mul_smul_comm, ← (MonoidAlgebra.of k (G' n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  congr 1
  have hZ : ((↑(Equiv.Perm.sign q) : ℤ)) * ((↑(Equiv.Perm.sign q) : ℤ)) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : k)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : k)) = 1 := by
    rw [← Int.cast_mul, hZ, Int.cast_one]
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, hsqq, one_mul]

/-! ### Young projector vanishing (Lemma 5.13.2 over a general field) -/

/-- Generalized basis vanishing over a field of characteristic zero:
if `μ` does NOT dominate `λ`, then `a_λ · of(σ) · b_μ = 0` for any basis element. -/
theorem basis_vanishing_K (k : Type*) [Field k] [CharZero k] (n : ℕ)
    (la mu : Nat.Partition n) (h : ¬ mu.Dominates la) (σ : Equiv.Perm (Fin n)) :
    RowSymmetrizerK k n la * MonoidAlgebra.of k (G' n) σ *
      ColumnAntisymmetrizerK k n mu = 0 := by
  obtain ⟨t, ht_row, hconj_col, ht_sign⟩ := pigeonhole_transposition_general n la mu h σ
  let of' := MonoidAlgebra.of k (G' n)
  set a := RowSymmetrizerK k n la
  set b := ColumnAntisymmetrizerK k n mu
  set val := a * of' σ * b
  have hconj_sign : (↑(↑(Equiv.Perm.sign (σ⁻¹ * t * σ)) : ℤ) : k) = -1 := by
    simp [Equiv.Perm.sign_mul, ht_sign]
  have hab : a * of' t = a := RowSymmetrizerK_mul_of_row t ht_row
  have hcol := of_col_mul_ColumnAntisymmetrizerK (k := k) (σ⁻¹ * t * σ) hconj_col
  have hval_neg : val = (-1 : k) • val := by
    have step : a * of' σ = a * of' σ * of' (σ⁻¹ * t * σ) := by
      conv_lhs => rw [show a = a * of' t from hab.symm]
      rw [mul_assoc a (of' t) (of' σ), ← map_mul of' t σ,
          show t * σ = σ * (σ⁻¹ * t * σ) from by group,
          map_mul of' σ (σ⁻¹ * t * σ), ← mul_assoc]
    change a * of' σ * b = (-1 : k) • (a * of' σ * b)
    conv_lhs => rw [step, mul_assoc (a * of' σ) (of' (σ⁻¹ * t * σ)) b, hcol]
    rw [mul_smul_comm, hconj_sign]
  rw [neg_one_smul] at hval_neg
  have hadd : val + val = 0 := by nth_rw 1 [hval_neg]; exact neg_add_cancel val
  have h2 : (2 : k) • val = 0 := by rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Generalized vanishing over a field of characteristic zero: if `μ` does NOT
dominate `λ`, then `a_λ · x · b_μ = 0` for all `x ∈ k[S_n]`. -/
theorem Lemma5_13_2_K (k : Type*) [Field k] [CharZero k] (n : ℕ)
    (la mu : Nat.Partition n) (h : ¬ mu.Dominates la)
    (x : MonoidAlgebra k (G' n)) :
    RowSymmetrizerK k n la * x * ColumnAntisymmetrizerK k n mu = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy, add_zero]
  | single g c =>
    have hsg : (Finsupp.single g c : MonoidAlgebra k (G' n)) =
        c • MonoidAlgebra.of k (G' n) g := by
      simp [MonoidAlgebra.of_apply, mul_one]
    rw [hsg, mul_smul_comm, smul_mul_assoc, basis_vanishing_K k n la mu h g, smul_zero]

/-! ### `c_λ² ≠ 0` over a general field -/

/-- The Young symmetrizer square is nonzero over a field of characteristic zero. -/
theorem youngSymmetrizerK_sq_ne_zero (k : Type*) [Field k] [CharZero k] (n : ℕ)
    (la : Nat.Partition n) :
    YoungSymmetrizerK k n la * YoungSymmetrizerK k n la ≠ 0 := by
  obtain ⟨α, hα⟩ := YoungSymmetrizerK_sq_scalar k n la
  have hα_ne := YoungSymmetrizerK_sq_scalar_ne_zero_general k n la α hα
  intro hsq0
  have hαc : α • YoungSymmetrizerK k n la = 0 := by rw [← hα, hsq0]
  have hc0 : YoungSymmetrizerK k n la = 0 :=
    (smul_eq_zero.mp hαc).resolve_left hα_ne
  have hone : (YoungSymmetrizerK k n la) 1 = 1 := by
    rw [YoungSymmetrizerK_eq_mapRange k n la]
    simp [MonoidAlgebra.mapRingHom_apply, YoungSymmetrizerZ_apply_one]
  rw [hc0] at hone
  simp at hone

/-! ### Annihilation and distinctness -/

/-- The Young symmetrizer `c_λ` annihilates `SpechtModuleK k n μ` when `μ` does
not dominate `λ`: `c_λ · v = 0` for all `v ∈ V_μ`. -/
theorem youngSymmetrizerK_annihilates_specht (k : Type*) [Field k] [CharZero k]
    (n : ℕ) (la mu : Nat.Partition n) (h : ¬ mu.Dominates la)
    (v : SpechtModuleK k n mu) :
    YoungSymmetrizerK k n la * (v : MonoidAlgebra k (G' n)) = 0 := by
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp v.2
  rw [← hx]
  change YoungSymmetrizerK k n la * (x * YoungSymmetrizerK k n mu) = 0
  rw [youngSymmetrizerK_eq_factored k n la, youngSymmetrizerK_eq_factored k n mu]
  rw [show ColumnAntisymmetrizerK k n la * RowSymmetrizerK k n la *
    (x * (ColumnAntisymmetrizerK k n mu * RowSymmetrizerK k n mu)) =
    ColumnAntisymmetrizerK k n la *
      (RowSymmetrizerK k n la * x * ColumnAntisymmetrizerK k n mu) *
      RowSymmetrizerK k n mu from by simp only [mul_assoc],
    Lemma5_13_2_K k n la mu h, mul_zero, zero_mul]

/-- For distinct partitions `λ ≠ μ`, the Specht modules `V_λ` and `V_μ` are not
isomorphic as `k[S_n]`-modules, for any field `k` of characteristic zero.
(General-field version of `Theorem5_12_2_distinct`.) -/
theorem Theorem5_12_2_distinct_general (k : Type*) [Field k] [CharZero k]
    (n : ℕ) (la mu : Nat.Partition n) (h : la ≠ mu) :
    IsEmpty ((SpechtModuleK k n la) ≃ₗ[MonoidAlgebra k (G' n)] (SpechtModuleK k n mu)) := by
  have hdom_or : ¬ mu.Dominates la ∨ ¬ la.Dominates mu := by
    by_contra hall
    push_neg at hall
    exact h (hall.1.antisymm hall.2).symm
  constructor
  intro φ
  set c_la := YoungSymmetrizerK k n la
  set c_mu := YoungSymmetrizerK k n mu
  have hc_la_mem : c_la ∈ SpechtModuleK k n la := Submodule.subset_span rfl
  have hc_mu_mem : c_mu ∈ SpechtModuleK k n mu := Submodule.subset_span rfl
  suffices ∀ (V V' : Submodule (MonoidAlgebra k (G' n)) (MonoidAlgebra k (G' n)))
      (c : MonoidAlgebra k (G' n)) (hc_mem : c ∈ V')
      (hc_sq : c * c ≠ 0)
      (hvanish : ∀ v : V, c * (v : MonoidAlgebra k (G' n)) = 0)
      (ψ : V' ≃ₗ[MonoidAlgebra k (G' n)] V), False by
    rcases hdom_or with h1 | h2
    · exact this (SpechtModuleK k n mu) (SpechtModuleK k n la) c_la hc_la_mem
        (youngSymmetrizerK_sq_ne_zero k n la)
        (fun v => youngSymmetrizerK_annihilates_specht k n la mu h1 v) φ
    · exact this (SpechtModuleK k n la) (SpechtModuleK k n mu) c_mu hc_mu_mem
        (youngSymmetrizerK_sq_ne_zero k n mu)
        (fun v => youngSymmetrizerK_annihilates_specht k n mu la h2 v) φ.symm
  intro V V' c hc_mem hc_sq hvanish ψ
  have hc_sq_mem : c * c ∈ V' := V'.smul_mem c hc_mem
  have h1 : c * (ψ ⟨c, hc_mem⟩ : MonoidAlgebra k (G' n)) = 0 := hvanish (ψ ⟨c, hc_mem⟩)
  have h2 : c * (ψ ⟨c, hc_mem⟩ : MonoidAlgebra k (G' n)) =
      (ψ ⟨c * c, hc_sq_mem⟩ : MonoidAlgebra k (G' n)) := by
    change (c • ψ ⟨c, hc_mem⟩ : V).val = (ψ ⟨c * c, hc_sq_mem⟩ : V).val
    congr 1
    rw [← ψ.map_smul]; rfl
  have h3 : (ψ ⟨c * c, hc_sq_mem⟩ : MonoidAlgebra k (G' n)) = 0 := h2 ▸ h1
  have h4 : (⟨c * c, hc_sq_mem⟩ : V') = 0 :=
    ψ.injective (Subtype.ext (by simp [h3, map_zero]))
  exact hc_sq (congr_arg Subtype.val h4)

end

end Etingof
