import Mathlib
import EtingofRepresentationTheory.Chapter5.LocalizationGLRightAction
import EtingofRepresentationTheory.Chapter5.KernelLemmaKPrime

/-!
# The det-power filtration of `O = A[det⁻¹]` and its `GL_N`-equivariant subquotients

This file builds the **det-power filtration** of the localization
`O = A[det⁻¹] = Localization.Away (detPoly k N)` carrying the right-translation
`GL_N`-representation `localRightRep` (`LocalizationGLRightAction.lean`), and
identifies its successive subquotients with the twisted quotient
`(A/det) ⊗ χ⁻ʳ = quotDetTwistRep` of `KernelLemmaKPrime.lean`. This is the
geometric heart of the (K) ⟸ (K′) reduction in the det⁻¹-elimination kernel
lemma (issue #4694, route doc `progress/kernel-lemma-K-route.md`).

## The filtration

For `r : ℕ` the **filtration submodule** is
`A_r := det⁻ʳ · A = { f : O | detExp f ≤ r }` (`filtrA`), the image of the
`k`-linear map `numToFiltr r : A → O`, `Q ↦ algebraMap Q · det⁻ʳ`. We show:

* `mem_filtrA_iff_detExp` — `f ∈ A_r ↔ detExp f ≤ r`, so `A_r` is exactly the
  set of localization elements whose reduced det-power exponent is at most `r`.
* `filtrA_zero` — `A_0 = range (algebraMap A O)`: the bottom of the filtration is
  the polynomial subring.
* `filtrA_mono` — `A_{r-1} ≤ A_r`, an increasing filtration.
* `iSup_filtrA` — `⨆ r, A_r = ⊤`: every localization element has finite
  det-power, so the filtration exhausts `O`.

## `GL_N`-stability

* `localRightRep_numToFiltr` — the exact transformation law:
  `R_g (Q · det⁻ʳ) = (det g)⁻ʳ · (R_g Q · det⁻ʳ)`, the `det⁻ʳ` factor scaling by
  the inverse determinant character `χ⁻ʳ` (`localRightRep_invSelf`) while the
  numerator transforms by `polyRightRep`.
* `localRightRep_mem_filtrA` — consequently each `A_r` is a right-`GL_N`-stable
  subspace of `O`: `localRightRep g` maps `A_r` into `A_r`.

## The equivariant subquotient `A_r / A_{r-1} ≅ (A/det) ⊗ χ⁻ʳ`

The numerator `Q` in `f = Q · det⁻ʳ` is *uniquely* determined by `f` and `r`
(`det⁻ʳ` is a unit, so `numToFiltr r` is injective). Reducing `Q` modulo `det`
gives a `k`-linear surjection `A_r ↠ A/det` whose kernel is exactly `A_{r-1}`
(`numToFiltr` carries the ideal `(det)` onto `A_{r-1}`), and the transformation
law `localRightRep_numToFiltr` makes it intertwine `localRightRep` with the
`χ⁻ʳ`-twisted quotient action `quotDetTwistRep`. Packaged as
`filtrQuotEquiv : (A/det) ≃ₗ[k] A_r ⧸ A_{r-1}` together with the equivariance
lemma `filtrQuotEquiv_equivariant`.
-/

namespace Etingof.DetPowerFiltration

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
  Etingof.LocalizationGLAction Etingof.KernelLemmaKPrime

variable {k : Type*} [Field k] {N : ℕ}

/-! ### The filtration submodule `A_r = det⁻ʳ · A` -/

/-- The `k`-linear map `A → O`, `Q ↦ algebraMap Q · det⁻ʳ`. Its range is the
filtration submodule `A_r = det⁻ʳ · A`. -/
noncomputable def numToFiltr (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    MvPolynomial (Fin N × Fin N) k →ₗ[k] Localization.Away (detPoly k N) :=
  (LinearMap.mulRight k (IsLocalization.Away.invSelf (detPoly k N) ^ r)).comp
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (detPoly k N))).toLinearMap

@[simp] theorem numToFiltr_apply (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k) :
    numToFiltr k N r Q =
      algebraMap _ (Localization.Away (detPoly k N)) Q
        * IsLocalization.Away.invSelf (detPoly k N) ^ r := by
  rw [numToFiltr, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']

/-- `numToFiltr r` is injective: `det⁻ʳ` is a unit, so multiplication by it is
injective, and `algebraMap A O` is injective (`detPoly` a nonzerodivisor). Hence
the numerator `Q` of `f = Q · det⁻ʳ` is uniquely determined by `f` and `r`. -/
theorem numToFiltr_injective (r : ℕ) :
    Function.Injective (numToFiltr (k := k) (N := N) r) := by
  intro Q₁ Q₂ h
  rw [numToFiltr_apply, numToFiltr_apply] at h
  apply algebraMap_away_injective
  have key := congrArg
    (· * algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N))
        (detPoly k N) ^ r) h
  simpa only [mul_assoc, mul_comm (IsLocalization.Away.invSelf (detPoly k N) ^ r),
    algebraMap_detPoly_pow_mul_invSelf_pow, mul_one] using key

/-- **The filtration submodule** `A_r := det⁻ʳ · A`, the range of `numToFiltr r`.
Equivalently `{ f : O | detExp f ≤ r }` (`mem_filtrA_iff_detExp`). -/
noncomputable def filtrA (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    Submodule k (Localization.Away (detPoly k N)) :=
  LinearMap.range (numToFiltr k N r)

theorem mem_filtrA_iff_exists (r : ℕ) (f : Localization.Away (detPoly k N)) :
    f ∈ filtrA k N r ↔ ∃ Q : MvPolynomial (Fin N × Fin N) k,
      f = algebraMap _ (Localization.Away (detPoly k N)) Q
        * IsLocalization.Away.invSelf (detPoly k N) ^ r := by
  simp only [filtrA, LinearMap.mem_range, numToFiltr_apply]
  exact ⟨fun ⟨Q, hQ⟩ => ⟨Q, hQ.symm⟩, fun ⟨Q, hQ⟩ => ⟨Q, hQ.symm⟩⟩

/-- **`A_r` is the set of elements of det-power exponent `≤ r`.** This is the
predicate the filtration keys on (`detExp f ≤ r`, with `A_0` the honest
polynomials by `detExp_eq_zero_iff`). -/
theorem mem_filtrA_iff_detExp (r : ℕ) (f : Localization.Away (detPoly k N)) :
    f ∈ filtrA k N r ↔ detExp f ≤ r := by
  rw [mem_filtrA_iff_exists]
  constructor
  · rintro ⟨Q, hQ⟩
    exact detExp_le ⟨Q, hQ⟩
  · intro hle
    obtain ⟨Q, hQ⟩ := detExp_spec f
    obtain ⟨s, hs⟩ : ∃ s, detExp f = s := ⟨_, rfl⟩
    rw [hs] at hQ hle
    refine ⟨Q * detPoly k N ^ (r - s), ?_⟩
    rw [hQ, map_mul, map_pow, mul_assoc,
      show IsLocalization.Away.invSelf (detPoly k N) ^ r
          = IsLocalization.Away.invSelf (detPoly k N) ^ (r - s)
            * IsLocalization.Away.invSelf (detPoly k N) ^ s
        from by rw [← pow_add]; congr 1; omega,
      ← mul_assoc (algebraMap (MvPolynomial (Fin N × Fin N) k) _ (detPoly k N) ^ (r - s)),
      algebraMap_detPoly_pow_mul_invSelf_pow, one_mul]

/-- `numToFiltr r` at `r = 0` is the structure map `A → O` (as a `k`-linear map):
`det⁻⁰ = 1`. -/
theorem numToFiltr_zero :
    numToFiltr k N 0 =
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (detPoly k N))).toLinearMap :=
  LinearMap.ext fun Q => by
    rw [numToFiltr_apply, pow_zero, mul_one, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom']

/-- **`A_0 = range (algebraMap A O)`.** The bottom of the filtration is the
polynomial subring `A ↪ O`. -/
theorem filtrA_zero :
    filtrA k N 0 = LinearMap.range
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (detPoly k N))).toLinearMap := by
  rw [filtrA, numToFiltr_zero]

/-- **The filtration is increasing**: `A_{r₁} ≤ A_{r₂}` for `r₁ ≤ r₂`. -/
theorem filtrA_mono : Monotone (filtrA k N) := by
  intro r₁ r₂ hr f hf
  rw [mem_filtrA_iff_detExp] at hf ⊢
  omega

/-- **The filtration exhausts `O`**: `⨆ r, A_r = ⊤`. Every localization element
has a finite det-power (`exists_invSelf_normalForm`), so lies in some `A_r`. -/
theorem iSup_filtrA : (⨆ r, filtrA k N r) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  exact Submodule.mem_iSup_of_mem (detExp f)
    ((mem_filtrA_iff_detExp _ f).mpr le_rfl)

/-! ### `GL_N`-stability of the filtration -/

/-- **The transformation law of a filtration element.** Right translation sends
`Q · det⁻ʳ` to `(det g)⁻ʳ · (R_g Q · det⁻ʳ)`: the numerator transforms by
`polyRightRep` while the `det⁻ʳ` factor scales by the inverse determinant
character `χ⁻ʳ` (`localRightRep_invSelf`). -/
theorem localRightRep_numToFiltr (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    localRightRep k N g (numToFiltr k N r Q)
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
          numToFiltr k N r (polyRightRep k N g Q) := by
  rw [numToFiltr_apply, numToFiltr_apply, localRightRep_apply, map_mul,
    localRightAlgHom_algebraMap, map_pow, ← localRightRep_apply, localRightRep_invSelf,
    smul_pow, mul_smul_comm]
  rfl

/-- **Each `A_r` is right-`GL_N`-stable.** `localRightRep g` maps `A_r` into
`A_r`: the transformation law `localRightRep_numToFiltr` keeps the `det⁻ʳ` factor
(scaling only by a unit) and sends the numerator into `A`. -/
theorem localRightRep_mem_filtrA (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    {x : Localization.Away (detPoly k N)} (hx : x ∈ filtrA k N r) :
    localRightRep k N g x ∈ filtrA k N r := by
  obtain ⟨Q, rfl⟩ := LinearMap.mem_range.mp hx
  rw [localRightRep_numToFiltr]
  exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

/-! ### The equivariant subquotient `A_r / A_{r-1} ≅ (A/det) ⊗ χ⁻ʳ` -/

/-- Membership in the determinant submodule `(det) ⊆ A` is divisibility by
`detPoly`. -/
theorem mem_detSubmodule_iff (Q : MvPolynomial (Fin N × Fin N) k) :
    Q ∈ detSubmodule k N ↔ detPoly k N ∣ Q := by
  rw [detSubmodule, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  exact Iff.rfl

/-- **The kernel characterisation of the filtration step** (`r ≥ 1`):
`Q · det⁻ʳ ∈ A_{r-1} ↔ detPoly ∣ Q`. A numerator divisible by `det` cancels one
`det⁻¹`, dropping the exponent; conversely a normal form of exponent `≤ r-1`
forces `det ∣ Q` after clearing denominators. -/
theorem numToFiltr_mem_filtrA_sub_one (r : ℕ) (hr : 1 ≤ r)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    numToFiltr k N r Q ∈ filtrA k N (r - 1) ↔ detPoly k N ∣ Q := by
  rw [mem_filtrA_iff_exists]
  constructor
  · rintro ⟨Q', hQ'⟩
    -- clear denominators with `algebraMap_num_eq` at both exponents `r` and `r-1`.
    have e1 : algebraMap _ (Localization.Away (detPoly k N)) Q
        = numToFiltr k N r Q
          * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ r :=
      algebraMap_num_eq (numToFiltr_apply r Q)
    have e2 : algebraMap _ (Localization.Away (detPoly k N)) Q'
        = numToFiltr k N r Q
          * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ (r - 1) :=
      algebraMap_num_eq hQ'
    refine ⟨Q', algebraMap_away_injective ?_⟩
    have hpow : algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ r
        = algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N)
          * algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N) ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e1, map_mul, e2, hpow]; ring
  · rintro ⟨Q', rfl⟩
    refine ⟨Q', ?_⟩
    have hsucc : (IsLocalization.Away.invSelf (detPoly k N) : Localization.Away (detPoly k N)) ^ r
        = IsLocalization.Away.invSelf (detPoly k N)
          * IsLocalization.Away.invSelf (detPoly k N) ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [numToFiltr_apply, map_mul, hsucc,
      show algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N)
          * algebraMap _ (Localization.Away (detPoly k N)) Q'
          * (IsLocalization.Away.invSelf (detPoly k N)
            * IsLocalization.Away.invSelf (detPoly k N) ^ (r - 1))
        = (algebraMap _ (Localization.Away (detPoly k N)) (detPoly k N)
            * IsLocalization.Away.invSelf (detPoly k N))
          * (algebraMap _ (Localization.Away (detPoly k N)) Q'
            * IsLocalization.Away.invSelf (detPoly k N) ^ (r - 1)) from by ring,
      IsLocalization.Away.mul_invSelf, one_mul]

/-- The numerator extraction `A ≃ₗ A_r`: `numToFiltr r` is an injective linear
map, so it is a linear isomorphism onto its range `A_r`. The inverse recovers the
unique numerator `Q` of `f = Q · det⁻ʳ`. -/
noncomputable def numEquiv (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    MvPolynomial (Fin N × Fin N) k ≃ₗ[k] ↥(filtrA k N r) :=
  LinearEquiv.ofInjective (numToFiltr k N r) (numToFiltr_injective r)

@[simp] theorem numEquiv_coe_apply (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k) :
    ((numEquiv k N r Q : ↥(filtrA k N r)) : Localization.Away (detPoly k N))
      = numToFiltr k N r Q :=
  rfl

/-- **The subquotient map** `A_r ↠ A/det`: extract the numerator `Q` of
`f = Q · det⁻ʳ` and reduce modulo `det`. Surjective with kernel `A_{r-1}`
(`ker_filtrToQuot`), and `GL_N`-equivariant for the `χ⁻ʳ`-twisted action
(`filtrToQuot_equivariant`). -/
noncomputable def filtrToQuot (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    ↥(filtrA k N r) →ₗ[k] (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) :=
  (detSubmodule k N).mkQ.comp (numEquiv k N r).symm.toLinearMap

@[simp] theorem filtrToQuot_numToFiltr (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k) :
    filtrToQuot k N r ⟨numToFiltr k N r Q, LinearMap.mem_range_self _ _⟩
      = Submodule.Quotient.mk Q := by
  rw [filtrToQuot, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply]
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext (numEquiv_coe_apply r Q).symm

theorem filtrToQuot_surjective (r : ℕ) :
    Function.Surjective (filtrToQuot k N r) :=
  (Submodule.mkQ_surjective _).comp (numEquiv k N r).symm.surjective

/-- **The kernel of the subquotient map is exactly `A_{r-1}`** (as a submodule of
`A_r`). Combined with surjectivity this yields the iso `A_r / A_{r-1} ≅ A/det`. -/
theorem ker_filtrToQuot (r : ℕ) (hr : 1 ≤ r) :
    LinearMap.ker (filtrToQuot k N r)
      = (filtrA k N (r - 1)).comap (filtrA k N r).subtype := by
  ext x
  obtain ⟨Q, rfl⟩ := (numEquiv k N r).surjective x
  rw [LinearMap.mem_ker,
    show filtrToQuot k N r (numEquiv k N r Q)
        = Submodule.Quotient.mk Q from filtrToQuot_numToFiltr r Q,
    Submodule.Quotient.mk_eq_zero, mem_detSubmodule_iff, Submodule.mem_comap,
    Submodule.coe_subtype, numEquiv_coe_apply, numToFiltr_mem_filtrA_sub_one r hr]

/-- **The subquotient isomorphism** `A_r / A_{r-1} ≃ₗ A/det`. The underlying
module of `(A/det) ⊗ χ⁻ʳ = quotDetTwistRep` is `A/det`; the `χ⁻ʳ` twist enters
the `GL_N`-action, recorded in `filtrToQuot_equivariant`. -/
noncomputable def filtrQuotEquiv (k : Type*) [Field k] (N : ℕ) (r : ℕ) (hr : 1 ≤ r) :
    (↥(filtrA k N r) ⧸ (filtrA k N (r - 1)).comap (filtrA k N r).subtype)
      ≃ₗ[k] (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) :=
  (Submodule.quotEquivOfEq _ _ (ker_filtrToQuot (k := k) (N := N) r hr).symm).trans
    (LinearMap.quotKerEquivOfSurjective (filtrToQuot k N r) (filtrToQuot_surjective r))

/-- The twisting scalar of `quotDetTwistRep` at `g`: the inverse determinant
character `χ⁻ʳ` evaluates to `(det g)⁻ʳ`. -/
theorem detChar_zpow_neg_apply (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ) :
    ((detChar k N ^ (-(r : ℤ))) g : k) = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r := by
  have happ : (detChar k N ^ (-(r : ℤ))) g = (detChar k N g) ^ (-(r : ℤ)) := rfl
  rw [happ, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    ← inv_pow]
  rfl

/-- **`GL_N`-equivariance of the subquotient map.** `filtrToQuot` intertwines the
right-translation action `localRightRep` on `A_r` with the `χ⁻ʳ`-twisted quotient
action `quotDetTwistRep = (A/det) ⊗ χ⁻ʳ` on `A/det`: the `det⁻ʳ` factor of a
filtration element contributes exactly the `χ⁻ʳ` twist. -/
theorem filtrToQuot_equivariant (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    (x : ↥(filtrA k N r)) :
    filtrToQuot k N r
        ⟨localRightRep k N g (x : Localization.Away (detPoly k N)),
          localRightRep_mem_filtrA g r x.2⟩
      = quotDetTwistRep k N r g (filtrToQuot k N r x) := by
  obtain ⟨Q, rfl⟩ := (numEquiv k N r).surjective x
  have hval : localRightRep k N g ((numEquiv k N r Q : ↥(filtrA k N r)) :
        Localization.Away (detPoly k N))
      = numToFiltr k N r
          (((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r • polyRightRep k N g Q) := by
    rw [numEquiv_coe_apply, localRightRep_numToFiltr, map_smul]
  rw [show (⟨localRightRep k N g ((numEquiv k N r Q : ↥(filtrA k N r)) :
            Localization.Away (detPoly k N)),
          localRightRep_mem_filtrA g r (numEquiv k N r Q).2⟩ : ↥(filtrA k N r))
        = ⟨numToFiltr k N r (((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r • polyRightRep k N g Q),
            LinearMap.mem_range_self _ _⟩ from Subtype.ext hval,
    filtrToQuot_numToFiltr,
    show filtrToQuot k N r (numEquiv k N r Q)
        = Submodule.Quotient.mk Q from filtrToQuot_numToFiltr r Q,
    quotDetTwistRep, charTwistRep_apply, detChar_zpow_neg_apply, quotDetRep_mk,
    Submodule.Quotient.mk_smul]

end Etingof.DetPowerFiltration
