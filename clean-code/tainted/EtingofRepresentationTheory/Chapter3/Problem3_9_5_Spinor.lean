import EtingofRepresentationTheory.Chapter3.Problem3_9_5
import Mathlib.LinearAlgebra.QuadraticForm.Dual

/-!
# Problem 3.9.5: the explicit hyperbolic spinor module

For the standard hyperbolic quadratic space `U* × U`, the exterior algebra `⋀ U`
carries the Clifford action in which `U` acts by exterior multiplication and `U*`
acts by contraction.  This file constructs that action, proves the canonical
anticommutation relations and parity identities, and identifies the resulting
representation with the full endomorphism algebra.

The construction is kept separate from the abstract Wedderburn--Artin proof in
`Problem3_9_5.lean`: downstream files can use the explicit model without changing
the module structures used by that proof.
-/

namespace Etingof.Problem3_9_5

open LinearMap

/-- The exterior-algebra spinor space on `n` generators. -/
abbrev Spinor (n : ℕ) := ExteriorAlgebra ℂ (Fin n → ℂ)

/-- The standard `2n`-dimensional hyperbolic space `U* × U`. -/
abbrev HyperbolicSpace (n : ℕ) :=
  Module.Dual ℂ (Fin n → ℂ) × (Fin n → ℂ)

/-- The standard hyperbolic quadratic form, `(f, u) ↦ f u`. -/
noncomputable def hyperbolicQ (n : ℕ) : QuadraticForm ℂ (HyperbolicSpace n) :=
  QuadraticForm.dualProd ℂ (Fin n → ℂ)

/-- Creation by exterior multiplication. -/
noncomputable def creation (n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (Spinor n) :=
  (Algebra.lmul ℂ (Spinor n)).toLinearMap.comp (ExteriorAlgebra.ι ℂ)

/-- Annihilation by left contraction. -/
noncomputable def contraction (n : ℕ) :
    Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (Spinor n) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Fin n → ℂ)))

/-- Two creations by the same vector vanish. -/
@[simp]
theorem creation_sq_zero (n : ℕ) (u : Fin n → ℂ) :
    creation n u * creation n u = 0 := by
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ u * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- Two contractions by the same covector vanish. -/
@[simp]
theorem contraction_sq_zero (n : ℕ) (f : Module.Dual ℂ (Fin n → ℂ)) :
    contraction n f * contraction n f = 0 := by
  apply LinearMap.ext
  intro x
  change CliffordAlgebra.contractLeft f
    (CliffordAlgebra.contractLeft f x) = 0
  exact CliffordAlgebra.contractLeft_contractLeft f x

/-- The mixed canonical anticommutation relation. -/
theorem contraction_creation_add (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) (u : Fin n → ℂ) (x : Spinor n) :
    contraction n f (creation n u x) + creation n u (contraction n f x) = f u • x := by
  change CliffordAlgebra.contractLeft f (ExteriorAlgebra.ι ℂ u * x)
    + ExteriorAlgebra.ι ℂ u * CliffordAlgebra.contractLeft f x = f u • x
  rw [CliffordAlgebra.contractLeft_ι_mul]
  module

/-- The mixed CAR as an identity of endomorphisms. -/
theorem contraction_mul_creation_add (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) (u : Fin n → ℂ) :
    contraction n f * creation n u + creation n u * contraction n f =
      f u • (1 : Module.End ℂ (Spinor n)) := by
  apply LinearMap.ext
  intro x
  exact contraction_creation_add n f u x

/-- The combined contraction/creation action of the hyperbolic space. -/
noncomputable def hyperbolicAction (n : ℕ) :
    HyperbolicSpace n →ₗ[ℂ] Module.End ℂ (Spinor n) :=
  LinearMap.coprod (contraction n) (creation n)

/-- The hyperbolic action satisfies the Clifford square relation. -/
theorem hyperbolicAction_sq (n : ℕ) (x : HyperbolicSpace n) :
    hyperbolicAction n x * hyperbolicAction n x =
      hyperbolicQ n x • (1 : Module.End ℂ (Spinor n)) := by
  apply LinearMap.ext
  intro y
  rcases x with ⟨f, u⟩
  change ((contraction n f + creation n u) *
      (contraction n f + creation n u)) y = f u • y
  simp only [Module.End.mul_apply, LinearMap.add_apply]
  have hc := LinearMap.congr_fun (creation_sq_zero n u) y
  have ha := LinearMap.congr_fun (contraction_sq_zero n f) y
  change creation n u (creation n u y) = 0 at hc
  change contraction n f (contraction n f y) = 0 at ha
  rw [map_add, map_add, ha, hc, zero_add, add_zero, contraction_creation_add]

/-- The explicit spinor representation of the standard hyperbolic Clifford algebra. -/
noncomputable def hyperbolicSpinRep (n : ℕ) :
    CliffordAlgebra (hyperbolicQ n) →ₐ[ℂ] Module.End ℂ (Spinor n) :=
  CliffordAlgebra.lift _ ⟨hyperbolicAction n, hyperbolicAction_sq n⟩

/-- A covector generator acts by contraction. -/
@[simp]
theorem hyperbolicSpinRep_ι_fst (n : ℕ) (f : Module.Dual ℂ (Fin n → ℂ)) :
    hyperbolicSpinRep n
        (CliffordAlgebra.ι (hyperbolicQ n) (f, 0)) =
      contraction n f := by
  rw [hyperbolicSpinRep, CliffordAlgebra.lift_ι_apply]
  simp [hyperbolicAction]

/-- A vector generator acts by creation. -/
@[simp]
theorem hyperbolicSpinRep_ι_snd (n : ℕ) (u : Fin n → ℂ) :
    hyperbolicSpinRep n
        (CliffordAlgebra.ι (hyperbolicQ n) (0, u)) =
      creation n u := by
  rw [hyperbolicSpinRep, CliffordAlgebra.lift_ι_apply]
  simp [hyperbolicAction]

/-- The spinor space has dimension `2^n`. -/
@[simp]
theorem finrank_spinor (n : ℕ) :
    Module.finrank ℂ (Spinor n) = 2 ^ n := by
  rw [Module.finrank_eq_card_basis
    (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n))),
    Fintype.card_finset, Fintype.card_fin]

/-- Exterior-degree parity, realized by the grade involution. -/
noncomputable def spinorParity (n : ℕ) : Module.End ℂ (Spinor n) :=
  CliffordAlgebra.involute.toLinearMap

/-- Parity is an involution. -/
@[simp]
theorem spinorParity_sq (n : ℕ) :
    spinorParity n * spinorParity n = 1 := by
  apply LinearMap.ext
  intro x
  exact CliffordAlgebra.involute_involute x

/-- Contraction anticommutes with the grade involution. -/
theorem contraction_involute (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) (x : Spinor n) :
    contraction n f (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (contraction n f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [contraction]
  | add x y hx hy =>
      simp only [map_add, hx, hy, neg_add]
  | ι_mul x u hx =>
      change CliffordAlgebra.contractLeft f (CliffordAlgebra.involute x) =
        -CliffordAlgebra.involute (CliffordAlgebra.contractLeft f x) at hx
      rw [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg]
      change -(CliffordAlgebra.contractLeft f
        (ExteriorAlgebra.ι ℂ u * CliffordAlgebra.involute x)) =
        -CliffordAlgebra.involute
          (CliffordAlgebra.contractLeft f (ExteriorAlgebra.ι ℂ u * x))
      rw [CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
        CliffordAlgebra.involute_ι, hx]
      noncomm_ring

/-- Parity anticommutes with creation. -/
theorem spinorParity_creation_anticomm (n : ℕ) (u : Fin n → ℂ) :
    spinorParity n * creation n u = -(creation n u * spinorParity n) := by
  apply LinearMap.ext
  intro x
  change CliffordAlgebra.involute (ExteriorAlgebra.ι ℂ u * x) =
    -(ExteriorAlgebra.ι ℂ u * CliffordAlgebra.involute x)
  rw [map_mul, CliffordAlgebra.involute_ι, neg_mul]

/-- Parity anticommutes with contraction. -/
theorem spinorParity_contraction_anticomm (n : ℕ)
    (f : Module.Dual ℂ (Fin n → ℂ)) :
    spinorParity n * contraction n f = -(contraction n f * spinorParity n) := by
  apply LinearMap.ext
  intro x
  change CliffordAlgebra.involute (contraction n f x) =
    -contraction n f (CliffordAlgebra.involute x)
  rw [contraction_involute]
  simp

/-- Parity anticommutes with every degree-one hyperbolic action. -/
theorem spinorParity_hyperbolicAction_anticomm (n : ℕ) (x : HyperbolicSpace n) :
    spinorParity n * hyperbolicAction n x =
      -(hyperbolicAction n x * spinorParity n) := by
  rcases x with ⟨f, u⟩
  change spinorParity n * (contraction n f + creation n u) =
    -((contraction n f + creation n u) * spinorParity n)
  rw [mul_add, add_mul, spinorParity_contraction_anticomm,
    spinorParity_creation_anticomm, neg_add]

/-- The symmetric bilinear form associated to the hyperbolic quadratic form. -/
private noncomputable def hyperbolicB (n : ℕ) :
    LinearMap.BilinForm ℂ (HyperbolicSpace n) :=
  QuadraticMap.associated (R := ℂ) (hyperbolicQ n)

/-- The standard hyperbolic bilinear form is nondegenerate. -/
private theorem hyperbolicB_nondegenerate (n : ℕ) :
    (hyperbolicB n).Nondegenerate := by
  have hB : QuadraticMap.associated (R := ℂ) (hyperbolicQ n) =
      (2 : ℂ)⁻¹ • LinearMap.dualProd ℂ (Fin n → ℂ) := by
    apply LinearMap.ext₂
    intro x y
    rcases x with ⟨f, u⟩
    rcases y with ⟨g, v⟩
    simp [hyperbolicQ, QuadraticMap.associated_apply,
      QuadraticForm.dualProd, LinearMap.dualProd]
    ring
  change (QuadraticMap.associated (R := ℂ) (hyperbolicQ n)).Nondegenerate
  rw [(QuadraticForm.associated_isSymm ℂ
    (hyperbolicQ n)).isRefl.nondegenerate_iff_separatingLeft]
  intro x hx
  apply (LinearMap.separatingLeft_dualProd
    (R := ℂ) (M := Fin n → ℂ)).2 (Module.eval_apply_injective ℂ)
  intro y
  have hxy := hx y
  rw [hB] at hxy
  simp only [LinearMap.smul_apply, smul_eq_mul] at hxy
  exact (mul_eq_zero.mp hxy).resolve_left (inv_ne_zero two_ne_zero)

/-- The standard even hyperbolic Clifford algebra is a simple ring.

This is extracted from `even_isMatrixAlgebra`: the abstract matrix model has
positive finite dimension, hence its endomorphism algebra is a matrix ring over
`ℂ`, and simplicity transports back across the algebra equivalence. -/
theorem hyperbolicClifford_isSimpleRing (n : ℕ) :
    IsSimpleRing (CliffordAlgebra (hyperbolicQ n)) := by
  have hdim : Module.finrank ℂ (HyperbolicSpace n) = 2 * n := by
    simp [HyperbolicSpace, Module.finrank_prod]
    omega
  obtain ⟨S, instAdd, instModule, hS, ⟨e⟩⟩ :=
    even_isMatrixAlgebra (V := HyperbolicSpace n) (hyperbolicB n)
      (QuadraticMap.associated_isSymm ℂ (hyperbolicQ n))
      (hyperbolicB_nondegenerate n) n hdim
  letI : AddCommGroup S := instAdd
  letI : Module ℂ S := instModule
  have hpos : 0 < Module.finrank ℂ S := by rw [hS]; positivity
  letI : Module.Finite ℂ S := Module.finite_of_finrank_pos hpos
  letI : Nontrivial S := Module.nontrivial_of_finrank_pos hpos
  letI : Nonempty (Fin (Module.finrank ℂ S)) := ⟨⟨0, hpos⟩⟩
  have hEnd : IsSimpleRing (Module.End ℂ S) :=
    IsSimpleRing.of_ringEquiv
      (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ S)).symm.toRingEquiv
      (inferInstance : IsSimpleRing
        (Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ))
  have hCliff : IsSimpleRing (CliffAlg (hyperbolicB n)) :=
    IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hEnd
  have hq : quadForm (hyperbolicB n) = hyperbolicQ n := by
    exact QuadraticMap.toQuadraticMap_associated ℂ (hyperbolicQ n)
  rw [← hq]
  exact hCliff

/-- The source and target of the explicit spinor representation have equal dimension. -/
private theorem finrank_hyperbolicClifford_eq_end (n : ℕ) :
    Module.finrank ℂ (CliffordAlgebra (hyperbolicQ n)) =
      Module.finrank ℂ (Module.End ℂ (Spinor n)) := by
  have hq : quadForm (hyperbolicB n) = hyperbolicQ n := by
    exact QuadraticMap.toQuadraticMap_associated ℂ (hyperbolicQ n)
  have hdim : Module.finrank ℂ (HyperbolicSpace n) = 2 * n := by
    simp [HyperbolicSpace, Module.finrank_prod]
    omega
  have hsource :
      Module.finrank ℂ (CliffordAlgebra (hyperbolicQ n)) = 2 ^ (2 * n) := by
    rw [← hq]
    simpa [hdim] using
      finrank_cliffAlg (hyperbolicB n)
        (Module.finBasis ℂ (HyperbolicSpace n))
  letI : Module.Finite ℂ (Spinor n) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n)))
  rw [hsource, Module.finrank_linearMap, finrank_spinor,
    mul_comm 2 n, pow_mul]
  simp [pow_two]

/-- The explicit spinor representation fills the full endomorphism algebra. -/
theorem hyperbolicSpinRep_bijective (n : ℕ) :
    Function.Bijective (hyperbolicSpinRep n) := by
  letI : IsSimpleRing (CliffordAlgebra (hyperbolicQ n)) :=
    hyperbolicClifford_isSimpleRing n
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  have hinj : Function.Injective (hyperbolicSpinRep n) :=
    RingHom.injective (hyperbolicSpinRep n).toRingHom
  refine ⟨hinj, ?_⟩
  letI : Module.Finite ℂ (CliffordAlgebra (hyperbolicQ n)) := by
    haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
    haveI : Module.Finite ℂ (ExteriorAlgebra ℂ (HyperbolicSpace n)) :=
      Module.Finite.of_basis
        (Module.Basis.ExteriorAlgebra
          (Module.finBasis ℂ (HyperbolicSpace n)))
    exact Module.Finite.equiv
      (CliffordAlgebra.equivExterior (hyperbolicQ n)).symm
  letI : Module.Finite ℂ (Spinor n) :=
    Module.Finite.of_basis
      (Module.Basis.ExteriorAlgebra (Pi.basisFun ℂ (Fin n)))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (hyperbolicSpinRep n).toLinearMap)
    (finrank_hyperbolicClifford_eq_end n)).mp hinj

/-- The explicit spinor space is irreducible for the pulled-back Clifford action.

The module structure is stated explicitly instead of being installed globally,
so downstream constructions of the two odd spinor modules can choose their own
actions without an instance conflict. -/
theorem hyperbolicSpinor_irreducible (n : ℕ) :
    @IsSimpleModule (CliffordAlgebra (hyperbolicQ n)) _ (Spinor n) _
      (Module.compHom (Spinor n) (hyperbolicSpinRep n).toRingHom) := by
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  letI : Module (CliffordAlgebra (hyperbolicQ n)) (Spinor n) :=
    Module.compHom (Spinor n) (hyperbolicSpinRep n).toRingHom
  letI : RingHomSurjective (hyperbolicSpinRep n).toRingHom :=
    ⟨(hyperbolicSpinRep_bijective n).2⟩
  let e : Spinor n →ₛₗ[(hyperbolicSpinRep n).toRingHom] Spinor n :=
    { AddMonoidHom.id (Spinor n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

end Etingof.Problem3_9_5
