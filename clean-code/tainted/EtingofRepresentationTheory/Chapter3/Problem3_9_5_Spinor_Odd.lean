import EtingofRepresentationTheory.Chapter3.Problem3_9_5_Spinor_Transport
import EtingofRepresentationTheory.Chapter3.Theorem3_3_1

/-!
# Problem 3.9.5: explicit odd spinor modules

The odd-dimensional Clifford algebra has two irreducible spinor modules.  On
the hyperbolic summand both use the exterior-algebra action; the remaining
orthogonal generator acts by the parity involution with opposite signs.
-/

namespace Etingof.Problem3_9_5

open LinearMap

/-- The standard odd quadratic space, with one unit-norm vector adjoined to the
hyperbolic space. -/
abbrev OddStandardSpace (n : ℕ) := HyperbolicSpace n × ℂ

/-- The standard odd quadratic form `Q(x, z) = hyperbolicQ x + z²`. -/
noncomputable def oddStandardQ (n : ℕ) :
    QuadraticForm ℂ (OddStandardSpace n) :=
  (hyperbolicQ n).prod (QuadraticMap.sq : QuadraticForm ℂ ℂ)

/-- The line spanned by parity inside the spinor endomorphism algebra. -/
noncomputable def parityLine (n : ℕ) :
    ℂ →ₗ[ℂ] Module.End ℂ (Spinor n) where
  toFun z := z • spinorParity n
  map_add' x y := add_smul x y _
  map_smul' x y := by
    simp only [RingHom.id_apply]
    exact (smul_smul x y (spinorParity n)).symm

/-- Hyperbolic action extended by `σ · parity` on the extra line. -/
noncomputable def oddStandardAction (n : ℕ) (σ : ℂ) :
    OddStandardSpace n →ₗ[ℂ] Module.End ℂ (Spinor n) :=
  LinearMap.coprod (hyperbolicAction n) (σ • parityLine n)

/-- The extended action obeys the Clifford square relation when `σ² = 1`. -/
theorem oddStandardAction_sq (n : ℕ) (σ : ℂ) (hσ : σ * σ = 1)
    (x : OddStandardSpace n) :
    oddStandardAction n σ x * oddStandardAction n σ x =
      oddStandardQ n x • (1 : Module.End ℂ (Spinor n)) := by
  rcases x with ⟨v, z⟩
  simp only [oddStandardAction, oddStandardQ, LinearMap.coprod_apply,
    LinearMap.smul_apply, parityLine, QuadraticMap.prod_apply,
    QuadraticMap.sq_apply]
  change (hyperbolicAction n v + σ • (z • spinorParity n)) *
      (hyperbolicAction n v + σ • (z • spinorParity n)) =
    (hyperbolicQ n v + z * z) •
      (1 : Module.End ℂ (Spinor n))
  rw [smul_smul]
  have hcross :
      hyperbolicAction n v * ((σ * z) • spinorParity n) +
        ((σ * z) • spinorParity n) * hyperbolicAction n v = 0 := by
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add,
      spinorParity_hyperbolicAction_anticomm]
    simp
  have hlast :
      ((σ * z) • spinorParity n) * ((σ * z) • spinorParity n) =
        ((σ * z) * (σ * z)) •
          (1 : Module.End ℂ (Spinor n)) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, spinorParity_sq]
  calc
    (hyperbolicAction n v + (σ * z) • spinorParity n) *
        (hyperbolicAction n v + (σ * z) • spinorParity n) =
      hyperbolicAction n v * hyperbolicAction n v +
        (hyperbolicAction n v * ((σ * z) • spinorParity n) +
          ((σ * z) • spinorParity n) * hyperbolicAction n v) +
        ((σ * z) • spinorParity n) * ((σ * z) • spinorParity n) := by
      rw [add_mul, mul_add, mul_add]
      ac_rfl
    _ = hyperbolicQ n v • (1 : Module.End ℂ (Spinor n)) +
        ((σ * z) * (σ * z)) • (1 : Module.End ℂ (Spinor n)) := by
      rw [hyperbolicAction_sq, hcross, hlast, add_zero]
    _ = (hyperbolicQ n v + z * z) •
        (1 : Module.End ℂ (Spinor n)) := by
      rw [← add_smul]
      congr 1
      rw [mul_mul_mul_comm, hσ, one_mul]

/-- The standard odd representation with positive parity action. -/
noncomputable def oddHyperbolicSpinRepPlus (n : ℕ) :
    CliffordAlgebra (oddStandardQ n) →ₐ[ℂ] Module.End ℂ (Spinor n) :=
  CliffordAlgebra.lift _
    ⟨oddStandardAction n 1, oddStandardAction_sq n 1 (by simp)⟩

/-- The standard odd representation with negative parity action. -/
noncomputable def oddHyperbolicSpinRepMinus (n : ℕ) :
    CliffordAlgebra (oddStandardQ n) →ₐ[ℂ] Module.End ℂ (Spinor n) :=
  CliffordAlgebra.lift _
    ⟨oddStandardAction n (-1), oddStandardAction_sq n (-1) (by simp)⟩

/-- The hyperbolic summand acts in the positive module by the even action. -/
@[simp]
theorem oddHyperbolicSpinRepPlus_ι_hyperbolic
    (n : ℕ) (x : HyperbolicSpace n) :
    oddHyperbolicSpinRepPlus n
        (CliffordAlgebra.ι (oddStandardQ n) (x, 0)) =
      hyperbolicAction n x := by
  rw [oddHyperbolicSpinRepPlus, CliffordAlgebra.lift_ι_apply]
  simp [oddStandardAction]

/-- The hyperbolic summand acts in the negative module by the even action. -/
@[simp]
theorem oddHyperbolicSpinRepMinus_ι_hyperbolic
    (n : ℕ) (x : HyperbolicSpace n) :
    oddHyperbolicSpinRepMinus n
        (CliffordAlgebra.ι (oddStandardQ n) (x, 0)) =
      hyperbolicAction n x := by
  rw [oddHyperbolicSpinRepMinus, CliffordAlgebra.lift_ι_apply]
  simp [oddStandardAction]

/-- The extra unit vector acts by positive parity. -/
@[simp]
theorem oddHyperbolicSpinRepPlus_ι_extra (n : ℕ) :
    oddHyperbolicSpinRepPlus n
        (CliffordAlgebra.ι (oddStandardQ n) (0, 1)) =
      spinorParity n := by
  rw [oddHyperbolicSpinRepPlus, CliffordAlgebra.lift_ι_apply]
  simp [oddStandardAction, parityLine]

/-- The extra unit vector acts by negative parity. -/
@[simp]
theorem oddHyperbolicSpinRepMinus_ι_extra (n : ℕ) :
    oddHyperbolicSpinRepMinus n
        (CliffordAlgebra.ι (oddStandardQ n) (0, 1)) =
      -spinorParity n := by
  rw [oddHyperbolicSpinRepMinus, CliffordAlgebra.lift_ι_apply]
  simp [oddStandardAction, parityLine]

/-- Inclusion of the even hyperbolic Clifford algebra into the standard odd
Clifford algebra. -/
noncomputable def evenToOddClifford (n : ℕ) :
    CliffordAlgebra (hyperbolicQ n) →ₐ[ℂ]
      CliffordAlgebra (oddStandardQ n) :=
  CliffordAlgebra.map
    (QuadraticMap.Isometry.inl (hyperbolicQ n)
      (QuadraticMap.sq : QuadraticForm ℂ ℂ))

/-- The even-to-odd inclusion sends a generator to the corresponding vector
in the hyperbolic summand. -/
@[simp]
theorem evenToOddClifford_ι (n : ℕ) (x : HyperbolicSpace n) :
    evenToOddClifford n (CliffordAlgebra.ι (hyperbolicQ n) x) =
      CliffordAlgebra.ι (oddStandardQ n) (x, 0) := by
  rw [evenToOddClifford, CliffordAlgebra.map_apply_ι]
  rfl

/-- Restricting the positive odd representation to the even hyperbolic
subalgebra recovers the explicit even representation. -/
theorem oddHyperbolicSpinRepPlus_comp_evenToOdd (n : ℕ) :
    (oddHyperbolicSpinRepPlus n).comp (evenToOddClifford n) =
      hyperbolicSpinRep n := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change ((oddHyperbolicSpinRepPlus n).comp (evenToOddClifford n))
      (CliffordAlgebra.ι (hyperbolicQ n) x) =
    hyperbolicSpinRep n (CliffordAlgebra.ι (hyperbolicQ n) x)
  rw [AlgHom.comp_apply, evenToOddClifford_ι,
    oddHyperbolicSpinRepPlus_ι_hyperbolic,
    hyperbolicSpinRep, CliffordAlgebra.lift_ι_apply]

/-- Restricting the negative odd representation to the even hyperbolic
subalgebra also recovers the explicit even representation. -/
theorem oddHyperbolicSpinRepMinus_comp_evenToOdd (n : ℕ) :
    (oddHyperbolicSpinRepMinus n).comp (evenToOddClifford n) =
      hyperbolicSpinRep n := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change ((oddHyperbolicSpinRepMinus n).comp (evenToOddClifford n))
      (CliffordAlgebra.ι (hyperbolicQ n) x) =
    hyperbolicSpinRep n (CliffordAlgebra.ι (hyperbolicQ n) x)
  rw [AlgHom.comp_apply, evenToOddClifford_ι,
    oddHyperbolicSpinRepMinus_ι_hyperbolic,
    hyperbolicSpinRep, CliffordAlgebra.lift_ι_apply]

/-- The positive standard odd representation is surjective. -/
theorem oddHyperbolicSpinRepPlus_surjective (n : ℕ) :
    Function.Surjective (oddHyperbolicSpinRepPlus n) := by
  intro f
  obtain ⟨c, rfl⟩ := (hyperbolicSpinRep_bijective n).2 f
  exact ⟨evenToOddClifford n c,
    AlgHom.congr_fun (oddHyperbolicSpinRepPlus_comp_evenToOdd n) c⟩

/-- The negative standard odd representation is surjective. -/
theorem oddHyperbolicSpinRepMinus_surjective (n : ℕ) :
    Function.Surjective (oddHyperbolicSpinRepMinus n) := by
  intro f
  obtain ⟨c, rfl⟩ := (hyperbolicSpinRep_bijective n).2 f
  exact ⟨evenToOddClifford n c,
    AlgHom.congr_fun (oddHyperbolicSpinRepMinus_comp_evenToOdd n) c⟩

/-- The associated form of the standard odd quadratic form is separating. -/
theorem oddStandardQ_separatingLeft (n : ℕ) :
    (QuadraticMap.associated (R := ℂ) (oddStandardQ n)).SeparatingLeft := by
  intro x hx
  rcases x with ⟨v, z⟩
  apply Prod.ext
  · apply hyperbolicQ_separatingLeft n
    intro y
    have h := hx (y, 0)
    simpa [oddStandardQ, QuadraticMap.associated_apply] using h
  · have h := hx (0, 1)
    simpa [oddStandardQ, QuadraticMap.associated_apply] using h

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A noncanonical isometry from an arbitrary nondegenerate odd-dimensional
complex quadratic space to the standard odd space. -/
noncomputable def oddSpinIsometry
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    (quadForm B).IsometryEquiv (oddStandardQ n) := by
  let e₀ : V ≃ₗ[ℂ] OddStandardSpace n :=
    LinearEquiv.ofFinrankEq V (OddStandardSpace n) (by
      rw [hdim]
      simp [OddStandardSpace, HyperbolicSpace, Module.finrank_prod]
      omega)
  let Q₀ : QuadraticForm ℂ V :=
    (oddStandardQ n).comp e₀.toLinearMap
  have hB : (QuadraticMap.associated (R := ℂ) (quadForm B)).SeparatingLeft := by
    rw [QuadraticMap.associated_left_inverse ℂ hsymm]
    exact hnd.1
  have hQ₀ : (QuadraticMap.associated (R := ℂ) Q₀).SeparatingLeft := by
    intro x hx
    apply e₀.injective
    rw [map_zero]
    apply oddStandardQ_separatingLeft n
    intro y
    obtain ⟨z, rfl⟩ := e₀.surjective y
    have := hx z
    simpa [Q₀, QuadraticMap.associated_comp] using this
  let e₁ : (quadForm B).IsometryEquiv Q₀ :=
    Classical.choice
      (QuadraticForm.equivalent_of_isAlgClosed (quadForm B) Q₀ hB hQ₀)
  exact e₁.trans
    (QuadraticMap.isometryEquivOfCompLinearEquiv
      (oddStandardQ n) e₀).symm

/-- The positive odd spinor representation transported to `(V, B)`. -/
noncomputable def oddSpinRepPlus
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    CliffAlg B →ₐ[ℂ] Module.End ℂ (Spinor n) :=
  (oddHyperbolicSpinRepPlus n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddSpinIsometry B hsymm hnd n hdim)).toAlgHom

/-- The negative odd spinor representation transported to `(V, B)`. -/
noncomputable def oddSpinRepMinus
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    CliffAlg B →ₐ[ℂ] Module.End ℂ (Spinor n) :=
  (oddHyperbolicSpinRepMinus n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddSpinIsometry B hsymm hnd n hdim)).toAlgHom

/-- A generator acts in the positive module by the transported odd action. -/
@[simp]
theorem oddSpinRepPlus_ι
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) (x : V) :
    oddSpinRepPlus B hsymm hnd n hdim
        (CliffordAlgebra.ι (quadForm B) x) =
      oddStandardAction n 1
        (oddSpinIsometry B hsymm hnd n hdim x) := by
  simp [oddSpinRepPlus, oddHyperbolicSpinRepPlus]

/-- A generator acts in the negative module by the transported odd action. -/
@[simp]
theorem oddSpinRepMinus_ι
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) (x : V) :
    oddSpinRepMinus B hsymm hnd n hdim
        (CliffordAlgebra.ι (quadForm B) x) =
      oddStandardAction n (-1)
        (oddSpinIsometry B hsymm hnd n hdim x) := by
  simp [oddSpinRepMinus, oddHyperbolicSpinRepMinus]

/-- The pulled-back extra unit vector. -/
noncomputable def oddSpinExtra
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) : V :=
  (oddSpinIsometry B hsymm hnd n hdim).symm (0, 1)

/-- The extra generator acts by positive parity. -/
@[simp]
theorem oddSpinRepPlus_ι_extra
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    oddSpinRepPlus B hsymm hnd n hdim
        (CliffordAlgebra.ι (quadForm B)
          (oddSpinExtra B hsymm hnd n hdim)) =
      spinorParity n := by
  rw [oddSpinRepPlus_ι]
  simp [oddSpinExtra, oddStandardAction, parityLine]

/-- The extra generator acts by negative parity. -/
@[simp]
theorem oddSpinRepMinus_ι_extra
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    oddSpinRepMinus B hsymm hnd n hdim
        (CliffordAlgebra.ι (quadForm B)
          (oddSpinExtra B hsymm hnd n hdim)) =
      -spinorParity n := by
  rw [oddSpinRepMinus_ι]
  simp [oddSpinExtra, oddStandardAction, parityLine]

/-- The transported positive odd representation is surjective. -/
theorem oddSpinRepPlus_surjective
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Function.Surjective (oddSpinRepPlus B hsymm hnd n hdim) :=
  (oddHyperbolicSpinRepPlus_surjective n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddSpinIsometry B hsymm hnd n hdim)).surjective

/-- The transported negative odd representation is surjective. -/
theorem oddSpinRepMinus_surjective
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Function.Surjective (oddSpinRepMinus B hsymm hnd n hdim) :=
  (oddHyperbolicSpinRepMinus_surjective n).comp
    (CliffordAlgebra.equivOfIsometry
      (oddSpinIsometry B hsymm hnd n hdim)).surjective

/-- The positive exterior spinor action is irreducible. -/
theorem oddSpinorPlus_irreducible
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    @IsSimpleModule (CliffAlg B) _ (Spinor n) _
      (Module.compHom (Spinor n)
        (oddSpinRepPlus B hsymm hnd n hdim).toRingHom) := by
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  letI : Module (CliffAlg B) (Spinor n) :=
    Module.compHom (Spinor n)
      (oddSpinRepPlus B hsymm hnd n hdim).toRingHom
  letI : RingHomSurjective
      (oddSpinRepPlus B hsymm hnd n hdim).toRingHom :=
    ⟨oddSpinRepPlus_surjective B hsymm hnd n hdim⟩
  let e : Spinor n →ₛₗ[
      (oddSpinRepPlus B hsymm hnd n hdim).toRingHom] Spinor n :=
    { AddMonoidHom.id (Spinor n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- The negative exterior spinor action is irreducible. -/
theorem oddSpinorMinus_irreducible
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    @IsSimpleModule (CliffAlg B) _ (Spinor n) _
      (Module.compHom (Spinor n)
        (oddSpinRepMinus B hsymm hnd n hdim).toRingHom) := by
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  letI : Module (CliffAlg B) (Spinor n) :=
    Module.compHom (Spinor n)
      (oddSpinRepMinus B hsymm hnd n hdim).toRingHom
  letI : RingHomSurjective
      (oddSpinRepMinus B hsymm hnd n hdim).toRingHom :=
    ⟨oddSpinRepMinus_surjective B hsymm hnd n hdim⟩
  let e : Spinor n →ₛₗ[
      (oddSpinRepMinus B hsymm hnd n hdim).toRingHom] Spinor n :=
    { AddMonoidHom.id (Spinor n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- A type-distinct copy of the exterior spinor for the positive odd action. -/
def SpinorPlus
    (B : LinearMap.BilinForm ℂ V)
    (_hsymm : ∀ x y, B x y = B y x)
    (_hnd : B.Nondegenerate) (n : ℕ)
    (_hdim : Module.finrank ℂ V = 2 * n + 1) :=
  Spinor n

/-- A type-distinct copy of the exterior spinor for the negative odd action. -/
def SpinorMinus
    (B : LinearMap.BilinForm ℂ V)
    (_hsymm : ∀ x y, B x y = B y x)
    (_hnd : B.Nondegenerate) (n : ℕ)
    (_hdim : Module.finrank ℂ V = 2 * n + 1) :=
  Spinor n

instance spinorPlusAddCommGroup
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    AddCommGroup (SpinorPlus B hsymm hnd n hdim) :=
  inferInstanceAs (AddCommGroup (Spinor n))

instance spinorPlusComplexModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module ℂ (SpinorPlus B hsymm hnd n hdim) :=
  inferInstanceAs (Module ℂ (Spinor n))

instance spinorMinusAddCommGroup
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    AddCommGroup (SpinorMinus B hsymm hnd n hdim) :=
  inferInstanceAs (AddCommGroup (Spinor n))

instance spinorMinusComplexModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module ℂ (SpinorMinus B hsymm hnd n hdim) :=
  inferInstanceAs (Module ℂ (Spinor n))

/-- Identification of the exterior model with the positive carrier. -/
noncomputable def spinorEquivPlus
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Spinor n ≃ₗ[ℂ] SpinorPlus B hsymm hnd n hdim :=
  LinearEquiv.refl ℂ (Spinor n)

/-- Identification of the exterior model with the negative carrier. -/
noncomputable def spinorEquivMinus
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Spinor n ≃ₗ[ℂ] SpinorMinus B hsymm hnd n hdim :=
  LinearEquiv.refl ℂ (Spinor n)

/-- The positive representation on its type-distinct carrier. -/
noncomputable def oddSpinorRepresentationPlus
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    CliffAlg B →ₐ[ℂ]
      Module.End ℂ (SpinorPlus B hsymm hnd n hdim) :=
  (spinorEquivPlus B hsymm hnd n hdim).conjAlgEquiv ℂ
    |>.toAlgHom.comp (oddSpinRepPlus B hsymm hnd n hdim)

/-- The negative representation on its type-distinct carrier. -/
noncomputable def oddSpinorRepresentationMinus
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    CliffAlg B →ₐ[ℂ]
      Module.End ℂ (SpinorMinus B hsymm hnd n hdim) :=
  (spinorEquivMinus B hsymm hnd n hdim).conjAlgEquiv ℂ
    |>.toAlgHom.comp (oddSpinRepMinus B hsymm hnd n hdim)

/-- The positive Clifford-module structure. -/
noncomputable instance spinorPlusCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module (CliffAlg B) (SpinorPlus B hsymm hnd n hdim) :=
  Module.compHom _ (oddSpinorRepresentationPlus B hsymm hnd n hdim).toRingHom

/-- The negative Clifford-module structure. -/
noncomputable instance spinorMinusCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    Module (CliffAlg B) (SpinorMinus B hsymm hnd n hdim) :=
  Module.compHom _ (oddSpinorRepresentationMinus B hsymm hnd n hdim).toRingHom

/-- The positive odd spinor module is irreducible. -/
theorem spinorPlus_isSimpleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    IsSimpleModule (CliffAlg B)
      (SpinorPlus B hsymm hnd n hdim) := by
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  letI : Nontrivial (SpinorPlus B hsymm hnd n hdim) :=
    (spinorEquivPlus B hsymm hnd n hdim).symm.toEquiv.nontrivial
  letI : RingHomSurjective
      (oddSpinorRepresentationPlus B hsymm hnd n hdim).toRingHom := by
    refine ⟨?_⟩
    exact (spinorEquivPlus B hsymm hnd n hdim).conjAlgEquiv ℂ
      |>.surjective.comp
      (oddSpinRepPlus_surjective B hsymm hnd n hdim)
  let e : SpinorPlus B hsymm hnd n hdim →ₛₗ[
      (oddSpinorRepresentationPlus B hsymm hnd n hdim).toRingHom]
      SpinorPlus B hsymm hnd n hdim :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- The negative odd spinor module is irreducible. -/
theorem spinorMinus_isSimpleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    IsSimpleModule (CliffAlg B)
      (SpinorMinus B hsymm hnd n hdim) := by
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  letI : Nontrivial (SpinorMinus B hsymm hnd n hdim) :=
    (spinorEquivMinus B hsymm hnd n hdim).symm.toEquiv.nontrivial
  letI : RingHomSurjective
      (oddSpinorRepresentationMinus B hsymm hnd n hdim).toRingHom := by
    refine ⟨?_⟩
    exact (spinorEquivMinus B hsymm hnd n hdim).conjAlgEquiv ℂ
      |>.surjective.comp
      (oddSpinRepMinus_surjective B hsymm hnd n hdim)
  let e : SpinorMinus B hsymm hnd n hdim →ₛₗ[
      (oddSpinorRepresentationMinus B hsymm hnd n hdim).toRingHom]
      SpinorMinus B hsymm hnd n hdim :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- The element of the arbitrary Clifford algebra obtained from an element of
the even-dimensional hyperbolic subalgebra. -/
noncomputable def oddSpinEvenElement
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (c : CliffordAlgebra (hyperbolicQ n)) : CliffAlg B :=
  (CliffordAlgebra.equivOfIsometry
    (oddSpinIsometry B hsymm hnd n hdim)).symm
      (evenToOddClifford n c)

@[simp]
theorem oddSpinRepPlus_evenElement
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (c : CliffordAlgebra (hyperbolicQ n)) :
    oddSpinRepPlus B hsymm hnd n hdim
        (oddSpinEvenElement B hsymm hnd n hdim c) =
      hyperbolicSpinRep n c := by
  change oddHyperbolicSpinRepPlus n
      ((CliffordAlgebra.equivOfIsometry
        (oddSpinIsometry B hsymm hnd n hdim))
          ((CliffordAlgebra.equivOfIsometry
            (oddSpinIsometry B hsymm hnd n hdim)).symm
              (evenToOddClifford n c))) =
    hyperbolicSpinRep n c
  rw [AlgEquiv.apply_symm_apply]
  exact AlgHom.congr_fun
    (oddHyperbolicSpinRepPlus_comp_evenToOdd n) c

@[simp]
theorem oddSpinRepMinus_evenElement
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (c : CliffordAlgebra (hyperbolicQ n)) :
    oddSpinRepMinus B hsymm hnd n hdim
        (oddSpinEvenElement B hsymm hnd n hdim c) =
      hyperbolicSpinRep n c := by
  change oddHyperbolicSpinRepMinus n
      ((CliffordAlgebra.equivOfIsometry
        (oddSpinIsometry B hsymm hnd n hdim))
          ((CliffordAlgebra.equivOfIsometry
            (oddSpinIsometry B hsymm hnd n hdim)).symm
              (evenToOddClifford n c))) =
    hyperbolicSpinRep n c
  rw [AlgEquiv.apply_symm_apply]
  exact AlgHom.congr_fun
    (oddHyperbolicSpinRepMinus_comp_evenToOdd n) c

/-- The two odd spinor modules are not isomorphic. Any intertwiner must commute
with parity because the even action is surjective, but the extra generator
forces it to anticommute with parity. -/
theorem oddSpinors_nonisomorphic
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1) :
    IsEmpty
      (SpinorPlus B hsymm hnd n hdim ≃ₗ[CliffAlg B]
        SpinorMinus B hsymm hnd n hdim) := by
  constructor
  intro e
  obtain ⟨c, hc⟩ :=
    (hyperbolicSpinRep_bijective n).2 (spinorParity n)
  let a := oddSpinEvenElement B hsymm hnd n hdim c
  let z := CliffordAlgebra.ι (quadForm B)
    (oddSpinExtra B hsymm hnd n hdim)
  have hcomm (x : SpinorPlus B hsymm hnd n hdim) :
      e (spinorParity n x) = spinorParity n (e x) := by
    have h := e.map_smul a x
    change e ((oddSpinRepPlus B hsymm hnd n hdim a) x) =
      (oddSpinRepMinus B hsymm hnd n hdim a) (e x) at h
    rw [oddSpinRepPlus_evenElement, oddSpinRepMinus_evenElement, hc] at h
    exact h
  have hanti (x : SpinorPlus B hsymm hnd n hdim) :
      e (spinorParity n x) = -spinorParity n (e x) := by
    have h := e.map_smul z x
    change e ((oddSpinRepPlus B hsymm hnd n hdim z) x) =
      (oddSpinRepMinus B hsymm hnd n hdim z) (e x) at h
    rw [oddSpinRepPlus_ι_extra, oddSpinRepMinus_ι_extra] at h
    exact h
  have hzero (x : SpinorPlus B hsymm hnd n hdim) :
      spinorParity n (e x) = 0 := by
    have h := (hcomm x).symm.trans (hanti x)
    have htwo : (2 : ℂ) • spinorParity n (e x) = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  let y : SpinorMinus B hsymm hnd n hdim :=
    spinorEquivMinus B hsymm hnd n hdim (1 : Spinor n)
  have hy : y ≠ 0 := by
    change (1 : Spinor n) ≠ 0
    exact one_ne_zero
  have hp : spinorParity n y = y := by
    change CliffordAlgebra.involute (1 : Spinor n) = 1
    exact map_one _
  have hz := hzero (e.symm y)
  rw [e.apply_symm_apply, hp] at hz
  exact hy hz

/-- Every finite-dimensional irreducible module for an odd-dimensional
nondegenerate complex Clifford algebra is one of the two explicit spinors. -/
theorem odd_every_finiteDimensional_irreducible_iso
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (W : Type*) [AddCommGroup W] [Module ℂ W] [Module (CliffAlg B) W]
    [IsScalarTower ℂ (CliffAlg B) W] [FiniteDimensional ℂ W]
    [IsSimpleModule (CliffAlg B) W] :
    Nonempty
        (W ≃ₗ[CliffAlg B] SpinorPlus B hsymm hnd n hdim) ∨
      Nonempty
        (W ≃ₗ[CliffAlg B] SpinorMinus B hsymm hnd n hdim) := by
  classical
  obtain ⟨d, hd, ⟨eA⟩⟩ :=
    odd_exists_pi_matrix B hsymm hnd n hdim
  let P := MatProd ℂ d
  letI : ∀ i, NeZero (d i) := fun i => ⟨Nat.ne_of_gt (hd i)⟩
  letI : Module P W :=
    Module.compHom W eA.symm.toRingHom
  letI : IsScalarTower ℂ P W := by
    constructor
    intro c a w
    change eA.symm (c • a) • w = c • (eA.symm a • w)
    rw [map_smul, smul_assoc]
  letI : RingHomSurjective eA.symm.toRingHom :=
    ⟨eA.symm.surjective⟩
  let lW : W →ₛₗ[eA.symm.toRingHom] W :=
    { AddMonoidHom.id W with map_smul' := fun _ _ => rfl }
  letI : IsSimpleModule P W :=
    (lW.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      inferInstance
  let Splus := SpinorPlus B hsymm hnd n hdim
  let Sminus := SpinorMinus B hsymm hnd n hdim
  letI : Module.Finite ℂ (Spinor n) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n)))
  letI : IsScalarTower ℂ (CliffAlg B) Splus := by
    constructor
    intro c a s
    change
      (oddSpinorRepresentationPlus B hsymm hnd n hdim (c • a)) s =
        c • (oddSpinorRepresentationPlus B hsymm hnd n hdim a) s
    rw [map_smul]
    rfl
  letI : FiniteDimensional ℂ Splus :=
    Module.Finite.equiv
      (spinorEquivPlus B hsymm hnd n hdim)
  letI : Module P Splus :=
    Module.compHom Splus eA.symm.toRingHom
  letI : IsScalarTower ℂ P Splus := by
    constructor
    intro c a s
    change eA.symm (c • a) • s = c • (eA.symm a • s)
    rw [map_smul, smul_assoc]
  let lPlus : Splus →ₛₗ[eA.symm.toRingHom] Splus :=
    { AddMonoidHom.id Splus with map_smul' := fun _ _ => rfl }
  letI : IsSimpleModule P Splus :=
    (lPlus.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      (spinorPlus_isSimpleModule B hsymm hnd n hdim)
  letI : IsScalarTower ℂ (CliffAlg B) Sminus := by
    constructor
    intro c a s
    change
      (oddSpinorRepresentationMinus B hsymm hnd n hdim (c • a)) s =
        c • (oddSpinorRepresentationMinus B hsymm hnd n hdim a) s
    rw [map_smul]
    rfl
  letI : FiniteDimensional ℂ Sminus :=
    Module.Finite.equiv
      (spinorEquivMinus B hsymm hnd n hdim)
  letI : Module P Sminus :=
    Module.compHom Sminus eA.symm.toRingHom
  letI : IsScalarTower ℂ P Sminus := by
    constructor
    intro c a s
    change eA.symm (c • a) • s = c • (eA.symm a • s)
    rw [map_smul, smul_assoc]
  let lMinus : Sminus →ₛₗ[eA.symm.toRingHom] Sminus :=
    { AddMonoidHom.id Sminus with map_smul' := fun _ _ => rfl }
  letI : IsSimpleModule P Sminus :=
    (lMinus.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      (spinorMinus_isSimpleModule B hsymm hnd n hdim)
  obtain ⟨iW, ⟨eW⟩⟩ :=
    exists_iso_vModuleProd (k := ℂ) (d := d) W
  obtain ⟨iP, ⟨eP⟩⟩ :=
    exists_iso_vModuleProd (k := ℂ) (d := d) Splus
  obtain ⟨iM, ⟨eM⟩⟩ :=
    exists_iso_vModuleProd (k := ℂ) (d := d) Sminus
  have hPM : iP ≠ iM := by
    intro h
    subst h
    let f := eP.trans eM.symm
    let fA : Splus ≃ₗ[CliffAlg B] Sminus :=
      { f.toAddEquiv with
        map_smul' := fun a s => by
          have hmap := f.map_smul (eA a) s
          change f (eA.symm (eA a) • s) =
            eA.symm (eA a) • f s at hmap
          rw [eA.symm_apply_apply] at hmap
          exact hmap }
    exact (oddSpinors_nonisomorphic B hsymm hnd n hdim).false fA
  have hW : iW = iP ∨ iW = iM := by
    fin_cases iW <;> fin_cases iP <;> fin_cases iM <;> simp_all
  rcases hW with hW | hW
  · subst hW
    left
    let f := eW.trans eP.symm
    exact ⟨
      { f.toAddEquiv with
        map_smul' := fun a w => by
          have hmap := f.map_smul (eA a) w
          change f (eA.symm (eA a) • w) =
            eA.symm (eA a) • f w at hmap
          rw [eA.symm_apply_apply] at hmap
          exact hmap }⟩
  · subst hW
    right
    let f := eW.trans eM.symm
    exact ⟨
      { f.toAddEquiv with
        map_smul' := fun a w => by
          have hmap := f.map_smul (eA a) w
          change f (eA.symm (eA a) • w) =
            eA.symm (eA a) • f w at hmap
          rw [eA.symm_apply_apply] at hmap
          exact hmap }⟩

/-- Every irreducible module for an odd-dimensional nondegenerate complex
Clifford algebra is one of the two explicit spinors. Finite dimensionality is
derived from simplicity and the finite-dimensional Clifford algebra. -/
theorem odd_every_irreducible_iso
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n + 1)
    (W : Type*) [AddCommGroup W] [Module (CliffAlg B) W]
    [IsSimpleModule (CliffAlg B) W] :
    Nonempty
        (W ≃ₗ[CliffAlg B] SpinorPlus B hsymm hnd n hdim) ∨
      Nonempty
        (W ≃ₗ[CliffAlg B] SpinorMinus B hsymm hnd n hdim) := by
  letI : Module ℂ W :=
    Module.compHom W (algebraMap ℂ (CliffAlg B))
  letI : IsScalarTower ℂ (CliffAlg B) W := by
    constructor
    intro c a w
    change (algebraMap ℂ (CliffAlg B) c * a) • w =
      (algebraMap ℂ (CliffAlg B) c) • (a • w)
    rw [mul_smul]
  letI : Module.Finite (CliffAlg B) W := by
    haveI := IsSimpleModule.nontrivial (CliffAlg B) W
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hmem : w ∈ Submodule.span (CliffAlg B) {w} :=
      Submodule.mem_span_singleton_self w
    have hspan : Submodule.span (CliffAlg B) {w} = ⊤ := by
      rcases eq_bot_or_eq_top (Submodule.span (CliffAlg B) {w}) with h | h
      · rw [h, Submodule.mem_bot] at hmem
        exact absurd hmem hw
      · exact h
    rw [Module.finite_def, ← hspan]
    exact Submodule.fg_span (Set.finite_singleton w)
  letI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  letI : Module.Finite ℂ (ExteriorAlgebra ℂ V) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Module.finBasis ℂ V))
  letI : Module.Finite ℂ (CliffAlg B) :=
    Module.Finite.equiv
      (CliffordAlgebra.equivExterior (quadForm B)).symm
  letI : FiniteDimensional ℂ W :=
    Module.Finite.trans (CliffAlg B) W
  exact
    odd_every_finiteDimensional_irreducible_iso
      B hsymm hnd n hdim W

end Etingof.Problem3_9_5
