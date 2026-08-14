import Mathlib
import RepresentationTheory.Matrix.MvPolynomialRightMul
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

open MvPolynomial
open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
open RepresentationTheory.GeneralLinearGroup.WeightCharacter

variable {k : Type*} [CommRing k] {N : ℕ}

/-- Defines a submodule of multivariate polynomials whose variables are indexed by pairs of elements of `Fin N`. -/
noncomputable def matrixIndexedPolynomialSubmodule (k : Type*) [CommRing k] (N : ℕ) :
    Submodule k (MvPolynomial (Fin N × Fin N) k) :=
  (Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)}).restrictScalars k

/-- The displayed general linear group action preserves the specified polynomial submodule. -/
theorem matrixIndexedPolynomialSubmodule_stable (g : Matrix.GeneralLinearGroup (Fin N) k)
    {f : MvPolynomial (Fin N × Fin N) k} (hf : f ∈ matrixIndexedPolynomialSubmodule k N) :
    generalLinearGroupMvPolynomialRightMul k N g f ∈ matrixIndexedPolynomialSubmodule k N := by
  rw [matrixIndexedPolynomialSubmodule, Submodule.restrictScalars_mem] at hf ⊢
  exact mvPolynomialRightMul_mapsTo_detIdeal _ hf

/-- Provides a representation on the quotient of a matrix-indexed polynomial space by the given submodule. -/
noncomputable def matrixPolynomialQuotientRepresentation (k : Type*) [CommRing k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) where
  toFun g := Submodule.mapQ _ _ (generalLinearGroupMvPolynomialRightMul k N g)
    (fun _ hx => matrixIndexedPolynomialSubmodule_stable g hx)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, map_one]
    rfl
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, map_mul]
    simp only [Module.End.mul_apply, Submodule.mapQ_apply]

/-- The quotient representation sends the class of a polynomial to the class of its image under the displayed action. -/
@[simp] theorem matrixPolynomialQuotientRepresentation_apply_mk (g : Matrix.GeneralLinearGroup (Fin N) k)
    (f : MvPolynomial (Fin N × Fin N) k) :
    matrixPolynomialQuotientRepresentation k N g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (generalLinearGroupMvPolynomialRightMul k N g f) :=
  rfl

variable {G V : Type*} [Monoid G] [AddCommMonoid V] [Module k V]

/-- Twists a monoid representation by a character with values in the units of the coefficient ring. -/
noncomputable def twistByCharacter (c : G →* kˣ) (ρ : Representation k G V) :
    Representation k G V where
  toFun g := (c g : k) • ρ g
  map_one' := by simp
  map_mul' g₁ g₂ := by
    simp only [map_mul, Units.val_mul, smul_mul_smul_comm]

/-- In a character-twisted representation, the action is the original action scaled by the character value. -/
@[simp] theorem twistByCharacter_apply (c : G →* kˣ) (ρ : Representation k G V)
    (g : G) (v : V) : twistByCharacter c ρ g v = (c g : k) • ρ g v :=
  rfl

/-- Twisting successively by two characters agrees with twisting by their product. -/
theorem twistByCharacter_mul (c₁ c₂ : G →* kˣ) (ρ : Representation k G V) :
    twistByCharacter c₁ (twistByCharacter c₂ ρ) = twistByCharacter (c₁ * c₂) ρ := by
  ext g v
  simp only [twistByCharacter_apply, MonoidHom.mul_apply, Units.val_mul, smul_smul]

/-- Provides a monoid homomorphism from a general linear group to the units of its coefficient ring. -/
noncomputable def generalLinearGroupToUnits (k : Type*) [CommRing k] (N : ℕ) :
    Matrix.GeneralLinearGroup (Fin N) k →* kˣ :=
  Matrix.GeneralLinearGroup.det

/-- Provides a natural-number-indexed family of representations on the specified polynomial quotient. -/
noncomputable def naturalIndexedQuotientRepresentation (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
  twistByCharacter (generalLinearGroupToUnits k N ^ (-(r : ℤ))) (matrixPolynomialQuotientRepresentation k N)

/-- Associates an integer-valued tuple with a submodule for a representation of a general linear group. -/
noncomputable def integerTupleSubmodule (k : Type*) [Field k] (N : ℕ) {V : Type*}
    [AddCommGroup V] [Module k V]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (μ : Fin N → ℤ) : Submodule k V :=
  ⨅ (i : Fin N) (t : kˣ),
    LinearMap.ker (ρ (diagonalUnit k N i t) - (((t ^ μ i : kˣ) : k)) • LinearMap.id)

/-- A nonzero member attached to a tuple with a negative entry is not contained in the supremum indexed by naturally cast tuples. -/
theorem integerTupleSubmodule_not_mem_iSup_natCast_of_exists_neg (k : Type*) [Field k] [CharZero k]
    (N : ℕ) (r : ℕ) (μ : Fin N → ℤ) (hμ : ∃ i, μ i < 0)
    {v : MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N}
    (hv0 : v ≠ 0) (hv : v ∈ integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N r) μ) :
    v ∉ ⨆ (ν : Fin N → ℕ),
      integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N r) (fun i => (ν i : ℤ)) := by
  obtain ⟨i, hi⟩ := hμ
  set ρ := naturalIndexedQuotientRepresentation k N r with hρ


  set t₀ : kˣ := Units.mk0 (2 : k) (by norm_num) with ht₀def
  have hcoe : ((t₀ : k)) = 2 := by rw [ht₀def]; rfl
  set T : Module.End k (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
    ρ (diagonalUnit k N i t₀) with hT

  set e : ℤ → k := fun a => ((t₀ ^ a : kˣ) : k) with he

  have key : ∀ (w : MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) (η : Fin N → ℤ),
      w ∈ integerTupleSubmodule k N ρ η → T w = e (η i) • w := by
    intro w η hw
    have hw' : w ∈ LinearMap.ker (ρ (diagonalUnit k N i t₀)
        - (((t₀ ^ η i : kˣ) : k)) • LinearMap.id) :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hw i) t₀
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hw'
    exact hw'

  have he_inj : Function.Injective e := by
    have htrans : ∀ n : ℤ, (2 : k) ^ n = algebraMap ℚ k ((2 : ℚ) ^ n) := by
      intro n; rw [map_zpow₀, map_ofNat]
    intro a b hab
    have h2 : (2 : k) ^ a = (2 : k) ^ b := by
      simpa only [he, Units.val_zpow_eq_zpow_val, hcoe] using hab
    rw [htrans, htrans] at h2
    have hQ : (2 : ℚ) ^ a = (2 : ℚ) ^ b := (algebraMap ℚ k).injective h2
    exact zpow_right_injective₀ (by norm_num) (by norm_num) hQ


  intro hv_sup
  have hμ_eig : v ∈ Module.End.eigenspace T (e (μ i)) :=
    Module.End.mem_eigenspace_iff.2 (key v μ hv)
  have hsup_le : (⨆ (ν : Fin N → ℕ), integerTupleSubmodule k N ρ (fun j => (ν j : ℤ)))
      ≤ ⨆ c ∈ Set.range (fun m : ℕ => e (m : ℤ)), Module.End.eigenspace T c := by
    refine iSup_le fun ν w hw => ?_
    refine Submodule.mem_iSup_of_mem (e ((ν i : ℤ))) ?_
    exact Submodule.mem_iSup_of_mem ⟨ν i, rfl⟩
      (Module.End.mem_eigenspace_iff.2 (key w (fun j => (ν j : ℤ)) hw))
  have hnot : e (μ i) ∉ Set.range (fun m : ℕ => e (m : ℤ)) := by
    rintro ⟨m, hm⟩
    have := he_inj hm
    omega
  have hdis := (Module.End.eigenspaces_iSupIndep T).disjoint_biSup hnot
  have hbot := disjoint_iff.1 hdis
  have : v ∈ (⊥ : Submodule k _) :=
    hbot ▸ Submodule.mem_inf.2 ⟨hμ_eig, hsup_le hv_sup⟩
  exact hv0 ((Submodule.mem_bot _).1 this)

/-- Identifies the submodule for the natural-number-indexed representation with a coordinatewise shifted submodule for the quotient representation. -/
theorem integerTupleSubmodule_naturalIndexedRepresentation (k : Type*) [Field k] (N : ℕ) (r : ℕ)
    (μ : Fin N → ℤ) :
    integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N r) μ =
      integerTupleSubmodule k N (matrixPolynomialQuotientRepresentation k N) (fun i => μ i + r) := by
  simp only [integerTupleSubmodule]
  refine iInf_congr fun i => iInf_congr fun t => ?_
  set g := diagonalUnit k N i t with hg

  have hdet : generalLinearGroupToUnits k N g = t := by
    ext
    change Matrix.det g.val = (t : k)
    simp only [hg, diagonalUnit, Matrix.det_diagonal,
      Finset.prod_update_of_mem (Finset.mem_univ i), Pi.one_apply]
    simp [Finset.prod_eq_one (fun j _ => rfl)]
  set c : k := ((t ^ (-(r : ℤ)) : kˣ) : k) with hc
  have hcne : c ≠ 0 := Units.ne_zero _
  have htwist : naturalIndexedQuotientRepresentation k N r g = c • matrixPolynomialQuotientRepresentation k N g := by
    change ((generalLinearGroupToUnits k N ^ (-(r : ℤ))) g : k) • matrixPolynomialQuotientRepresentation k N g = _
    rw [MonoidHom.zpow_apply, hdet]

  have hscal : c * ((t ^ (μ i + (r : ℤ)) : kˣ) : k) = ((t ^ μ i : kˣ) : k) := by
    have hexp : (-(r : ℤ)) + (μ i + (r : ℤ)) = μ i := by ring
    rw [hc, ← Units.val_mul, ← zpow_add, hexp]

  have factored : naturalIndexedQuotientRepresentation k N r g - ((t ^ μ i : kˣ) : k) • LinearMap.id =
      c • (matrixPolynomialQuotientRepresentation k N g - ((t ^ (μ i + (r : ℤ)) : kˣ) : k) • LinearMap.id) := by
    rw [htwist, smul_sub, smul_smul, hscal]
  rw [factored, LinearMap.ker_smul _ _ hcne]

end RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
