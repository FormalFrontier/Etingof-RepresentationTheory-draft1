import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_SourceIdeal

/-!
# Lemma 5.13.3: exact Young-projector scalar

This file completes the early proportionality statement `Lemma5_13_3` after the Specht module
and its source-order realization have become available.  It proves the book's exact scalar for
the normalized projector `youngProjector`.
-/

namespace Etingof

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)
private abbrev A (n : ℕ) := MonoidAlgebra ℂ (G n)

local instance lemma5133ExactCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

/-- The trace of right multiplication by a group-algebra element is the group order times its
identity coefficient. -/
private lemma trace_mulRight_monoidAlgebra
    {H : Type*} [Group H] [Fintype H] (x : MonoidAlgebra ℂ H) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ H) (LinearMap.mulRight ℂ x) =
      Fintype.card H * x 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis H ℂ)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  have hdiag : ∀ g : H,
      (MonoidAlgebra.basis H ℂ).repr
          (LinearMap.mulRight ℂ x ((MonoidAlgebra.basis H ℂ) g)) g = x 1 := by
    intro g
    change (MonoidAlgebra.single g 1 * x : MonoidAlgebra ℂ H) g = x 1
    rw [MonoidAlgebra.single_mul_apply]
    simp
  simp_rw [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Right multiplication has the same trace on the two factor orders `a_λ b_λ` and
`b_λ a_λ`. -/
private lemma trace_mulRight_rowCol_eq_colRow (n : ℕ) (la : Nat.Partition n) :
    LinearMap.trace ℂ (A n)
        (LinearMap.mulRight ℂ (RowSymmetrizer n la * ColumnAntisymmetrizer n la)) =
      LinearMap.trace ℂ (A n)
        (LinearMap.mulRight ℂ (ColumnAntisymmetrizer n la * RowSymmetrizer n la)) := by
  let Ra := LinearMap.mulRight ℂ (RowSymmetrizer n la)
  let Rb := LinearMap.mulRight ℂ (ColumnAntisymmetrizer n la)
  have hab : LinearMap.mulRight ℂ (RowSymmetrizer n la * ColumnAntisymmetrizer n la) =
      Rb.comp Ra := by
    ext x
    simp only [Ra, Rb, LinearMap.mulRight_apply, LinearMap.comp_apply, mul_assoc]
  have hba : LinearMap.mulRight ℂ (ColumnAntisymmetrizer n la * RowSymmetrizer n la) =
      Ra.comp Rb := by
    ext x
    simp only [Ra, Rb, LinearMap.mulRight_apply, LinearMap.comp_apply, mul_assoc]
  rw [hab, hba]
  exact LinearMap.trace_comp_comm' Ra Rb

/-- The trace of right multiplication by the normalized source-order Young projector is
`n! / (|P_λ| |Q_λ|)`. -/
private lemma trace_mulRight_youngProjector (n : ℕ) (la : Nat.Partition n) :
    LinearMap.trace ℂ (A n) (LinearMap.mulRight ℂ (youngProjector n la)) =
      (Nat.factorial n : ℂ) /
        ((Nat.card (RowSubgroup n la) : ℂ) *
          (Nat.card (ColumnSubgroup n la) : ℂ)) := by
  let t : ℂ := ((Nat.card (RowSubgroup n la) : ℂ) *
    (Nat.card (ColumnSubgroup n la) : ℂ))⁻¹
  have hc : youngProjector n la =
      t • (RowSymmetrizer n la * ColumnAntisymmetrizer n la) := by
    simp only [youngProjector, youngProjectorRow, youngProjectorCol,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, t]
    congr 1
    rw [mul_inv]
    ring
  rw [hc]
  have hmap : LinearMap.mulRight ℂ
      (t • (RowSymmetrizer n la * ColumnAntisymmetrizer n la)) =
      t • LinearMap.mulRight ℂ (RowSymmetrizer n la * ColumnAntisymmetrizer n la) := by
    apply LinearMap.ext
    intro x
    change x * (t • (RowSymmetrizer n la * ColumnAntisymmetrizer n la)) =
      t • (x * (RowSymmetrizer n la * ColumnAntisymmetrizer n la))
    exact Algebra.mul_smul_comm t x _
  rw [hmap]
  rw [map_smul, trace_mulRight_rowCol_eq_colRow,
    trace_mulRight_monoidAlgebra, show
      ColumnAntisymmetrizer n la * RowSymmetrizer n la = YoungSymmetrizer n la from rfl,
    youngSymmetrizer_identity_coeff, mul_one, Fintype.card_perm, Fintype.card_fin]
  simp only [smul_eq_mul, t, div_eq_mul_inv]
  ring

/-- **Lemma 5.13.3 (source-faithful exact form).** For Etingof's normalized Young projector
`c_λ = a_λ b_λ`,
`c_λ² = n! / (|P_λ| |Q_λ| dim V_λ) · c_λ`. -/
theorem Lemma5_13_3_exact (n : ℕ) (la : Nat.Partition n) :
    youngProjector n la * youngProjector n la =
      ((Nat.factorial n : ℂ) /
        ((Nat.card (RowSubgroup n la) : ℂ) *
          (Nat.card (ColumnSubgroup n la) : ℂ) *
          (Module.finrank ℂ (SpechtModule n la) : ℂ))) • youngProjector n la := by
  obtain ⟨β, hβne, hβsq⟩ := rowCol_sq_scalar n la
  let t : ℂ := ((Nat.card (RowSubgroup n la) : ℂ) *
    (Nat.card (ColumnSubgroup n la) : ℂ))⁻¹
  let γ : ℂ := t * β
  let c : A n := youngProjector n la
  have hc : c = t • (RowSymmetrizer n la * ColumnAntisymmetrizer n la) := by
    simp only [c, youngProjector, youngProjectorRow, youngProjectorCol,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, t]
    congr 1
    rw [mul_inv]
    ring
  have htne : t ≠ 0 := by
    apply inv_ne_zero
    exact mul_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hγne : γ ≠ 0 := mul_ne_zero htne hβne
  have hcsq : c * c = γ • c := by
    let r : A n := RowSymmetrizer n la * ColumnAntisymmetrizer n la
    calc
      c * c = (t • r) * (t • r) := by rw [hc]
      _ = (t * t) • (r * r) := by
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      _ = (t * t) • (β • r) := by rw [hβsq]
      _ = (t * β) • (t • r) := by
        simp only [smul_smul]
        congr 1
        ring
      _ = γ • c := by rw [hc]
  let R : A n →ₗ[ℂ] A n := LinearMap.mulRight ℂ c
  let e : A n →ₗ[ℂ] A n := γ⁻¹ • R
  have hproj : LinearMap.IsProj ((youngProjectorLeftIdeal n la).restrictScalars ℂ) e := by
    apply LinearMap.IsProj.mk
    · intro x
      simp only [e, R, LinearMap.smul_apply, LinearMap.mulRight_apply]
      apply Submodule.smul_mem
      change x * c ∈ youngProjectorLeftIdeal n la
      exact (youngProjectorLeftIdeal n la).smul_mem x (Submodule.subset_span rfl)
    · intro x hx
      simp only [e, R, LinearMap.smul_apply, LinearMap.mulRight_apply]
      change x ∈ youngProjectorLeftIdeal n la at hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      dsimp [c] at hcsq ⊢
      rw [mul_assoc, hcsq, Algebra.mul_smul_comm, smul_smul,
        inv_mul_cancel₀ hγne, one_smul]
  have htrace := hproj.trace
  have hfin : Module.finrank ℂ ((youngProjectorLeftIdeal n la).restrictScalars ℂ) =
      Module.finrank ℂ (SpechtModule n la) := by
    exact LinearEquiv.finrank_eq
      ((spechtModule_linearEquiv_youngProjectorLeftIdeal n la).restrictScalars ℂ).symm
  have htraceR : LinearMap.trace ℂ (A n) R =
      (Nat.factorial n : ℂ) /
        ((Nat.card (RowSubgroup n la) : ℂ) *
          (Nat.card (ColumnSubgroup n la) : ℂ)) := by
    simpa only [R, c] using trace_mulRight_youngProjector n la
  have htraceE : LinearMap.trace ℂ (A n) e = γ⁻¹ *
      ((Nat.factorial n : ℂ) /
        ((Nat.card (RowSubgroup n la) : ℂ) *
          (Nat.card (ColumnSubgroup n la) : ℂ))) := by
    simp only [e, map_smul, htraceR, smul_eq_mul]
  rw [htraceE, hfin] at htrace
  have hcne : YoungSymmetrizer n la ≠ 0 := by
    intro h
    exact young_symmetrizer_sq_ne_zero n la (by rw [h, mul_zero])
  haveI : Nontrivial (SpechtModule n la) := by
    refine ⟨⟨⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩, 0, ?_⟩⟩
    intro h
    apply hcne
    simpa using congrArg Subtype.val h
  have hdimne : (Module.finrank ℂ (SpechtModule n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hγ : γ =
      ((Nat.factorial n : ℂ) /
        ((Nat.card (RowSubgroup n la) : ℂ) *
          (Nat.card (ColumnSubgroup n la) : ℂ))) /
          (Module.finrank ℂ (SpechtModule n la) : ℂ) := by
    rw [inv_mul_eq_iff_eq_mul₀ hγne] at htrace
    rw [eq_div_iff hdimne]
    exact htrace.symm
  change c * c = _
  rw [hcsq, hγ]
  congr 1
  field_simp

end Etingof
