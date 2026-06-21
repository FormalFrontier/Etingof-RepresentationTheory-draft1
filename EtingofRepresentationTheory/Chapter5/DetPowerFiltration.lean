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

end Etingof.DetPowerFiltration
