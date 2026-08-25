import EtingofRepresentationTheory.Chapter3.Problem3_9_5_Spinor
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed

/-!
# Problem 3.9.5: transport of the explicit even spinor module

Over `ℂ`, every nondegenerate quadratic form of dimension `2n` is isometric to
the standard hyperbolic form.  This file chooses such an isometry, pulls the
standard hyperbolic basis back to the original quadratic space, and transports
the explicit exterior-algebra spinor representation along it.
-/

namespace Etingof.Problem3_9_5

open LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The standard hyperbolic quadratic form has separating associated form. -/
theorem hyperbolicQ_separatingLeft (n : ℕ) :
    (QuadraticMap.associated (R := ℂ) (hyperbolicQ n)).SeparatingLeft := by
  intro x hx
  rcases x with ⟨f, u⟩
  apply Prod.ext
  · apply LinearMap.ext
    intro v
    have h := hx (0, v)
    simpa [hyperbolicQ, QuadraticMap.associated_apply,
      QuadraticForm.dualProd, LinearMap.dualProd] using h
  · apply funext
    intro i
    let g : Module.Dual ℂ (Fin n → ℂ) :=
      LinearMap.proj i
    have h := hx (g, 0)
    simpa [g, hyperbolicQ, QuadraticMap.associated_apply,
      QuadraticForm.dualProd, LinearMap.dualProd] using h

/-- A noncanonical isometry from an arbitrary nondegenerate even-dimensional
complex quadratic space to the standard hyperbolic space. -/
noncomputable def evenSpinIsometry
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    (quadForm B).IsometryEquiv (hyperbolicQ n) := by
  let e₀ : V ≃ₗ[ℂ] HyperbolicSpace n :=
    LinearEquiv.ofFinrankEq V (HyperbolicSpace n) (by
      rw [hdim]
      simp [HyperbolicSpace, Module.finrank_prod]
      omega)
  let Q₀ : QuadraticForm ℂ V :=
    (hyperbolicQ n).comp e₀.toLinearMap
  have hB : (QuadraticMap.associated (R := ℂ) (quadForm B)).SeparatingLeft := by
    rw [QuadraticMap.associated_left_inverse ℂ hsymm]
    exact hnd.1
  have hQ₀ : (QuadraticMap.associated (R := ℂ) Q₀).SeparatingLeft := by
    intro x hx
    apply e₀.injective
    rw [map_zero]
    apply hyperbolicQ_separatingLeft n
    intro y
    obtain ⟨z, rfl⟩ := e₀.surjective y
    have := hx z
    simpa [Q₀, QuadraticMap.associated_comp] using this
  let e₁ : (quadForm B).IsometryEquiv Q₀ :=
    Classical.choice
      (QuadraticForm.equivalent_of_isAlgClosed (quadForm B) Q₀ hB hQ₀)
  exact e₁.trans
    (QuadraticMap.isometryEquivOfCompLinearEquiv
      (hyperbolicQ n) e₀).symm

/-- The `i`-th standard vector of `ℂⁿ`. -/
def evenSpinStandardVector (n : ℕ) (i : Fin n) : Fin n → ℂ :=
  fun j => if i = j then 1 else 0

/-- The `i`-th coordinate covector of `ℂⁿ`. -/
def evenSpinStandardCovector (n : ℕ) (i : Fin n) :
    Module.Dual ℂ (Fin n → ℂ) :=
  LinearMap.proj i

/-- The pulled-back isotropic vector whose standard action is creation. -/
noncomputable def evenSpinA
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) : V :=
  (evenSpinIsometry B hsymm hnd n hdim).symm
    (0, evenSpinStandardVector n i)

/-- The pulled-back isotropic vector whose standard action is contraction. -/
noncomputable def evenSpinB
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) : V :=
  (evenSpinIsometry B hsymm hnd n hdim).symm
    (evenSpinStandardCovector n i, 0)

/-- The chosen isometry identifies `B` with the associated hyperbolic form. -/
theorem evenSpinIsometry_pairing
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (x y : V) :
    B x y =
      QuadraticMap.associated (R := ℂ) (hyperbolicQ n)
        (evenSpinIsometry B hsymm hnd n hdim x)
        (evenSpinIsometry B hsymm hnd n hdim y) := by
  let e := evenSpinIsometry B hsymm hnd n hdim
  change B x y =
    QuadraticMap.associated (R := ℂ) (hyperbolicQ n) (e x) (e y)
  calc
    B x y =
        QuadraticMap.associated (R := ℂ) (quadForm B) x y := by
      rw [QuadraticMap.associated_left_inverse ℂ hsymm]
    _ = QuadraticMap.associated (R := ℂ) (hyperbolicQ n) (e x) (e y) := by
      have hxy :
          hyperbolicQ n (e x + e y) = quadForm B (x + y) := by
        calc
          hyperbolicQ n (e x + e y) =
              hyperbolicQ n (e (x + y)) :=
            congrArg (hyperbolicQ n) (e.toLinearEquiv.map_add x y).symm
          _ = quadForm B (x + y) := e.map_app (x + y)
      simp only [QuadraticMap.associated_apply]
      rw [hxy, e.map_app, e.map_app]

/-- The pulled-back creation vectors are mutually isotropic. -/
@[simp]
theorem evenSpinA_pair
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i j : Fin n) :
    B (evenSpinA B hsymm hnd n hdim i)
      (evenSpinA B hsymm hnd n hdim j) = 0 := by
  rw [evenSpinIsometry_pairing B hsymm hnd n hdim]
  simp only [evenSpinA, QuadraticMap.IsometryEquiv.apply_symm_apply]
  simp [hyperbolicQ, QuadraticMap.associated_apply,
    QuadraticForm.dualProd]

/-- The pulled-back contraction vectors are mutually isotropic. -/
@[simp]
theorem evenSpinB_pair
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i j : Fin n) :
    B (evenSpinB B hsymm hnd n hdim i)
      (evenSpinB B hsymm hnd n hdim j) = 0 := by
  rw [evenSpinIsometry_pairing B hsymm hnd n hdim]
  simp only [evenSpinB, QuadraticMap.IsometryEquiv.apply_symm_apply]
  simp [hyperbolicQ, QuadraticMap.associated_apply,
    QuadraticForm.dualProd]

/-- The two pulled-back isotropic families have the book's normalization. -/
@[simp]
theorem evenSpinA_pair_evenSpinB
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i j : Fin n) :
    B (evenSpinA B hsymm hnd n hdim i)
      (evenSpinB B hsymm hnd n hdim j) =
        if i = j then (2 : ℂ)⁻¹ else 0 := by
  rw [evenSpinIsometry_pairing B hsymm hnd n hdim]
  simp only [evenSpinA, evenSpinB,
    QuadraticMap.IsometryEquiv.apply_symm_apply]
  simp [evenSpinStandardVector, evenSpinStandardCovector,
    hyperbolicQ, QuadraticMap.associated_apply, QuadraticForm.dualProd]

/-- The explicit spinor representation transported to `(V, B)`. -/
noncomputable def evenSpinRep
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    CliffAlg B →ₐ[ℂ] Module.End ℂ (Spinor n) :=
  (hyperbolicSpinRep n).comp
    (CliffordAlgebra.equivOfIsometry
      (evenSpinIsometry B hsymm hnd n hdim)).toAlgHom

/-- A Clifford generator acts through the image of the chosen isometry. -/
@[simp]
theorem evenSpinRep_ι
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (x : V) :
    evenSpinRep B hsymm hnd n hdim
        (CliffordAlgebra.ι (quadForm B) x) =
      hyperbolicAction n (evenSpinIsometry B hsymm hnd n hdim x) := by
  simp [evenSpinRep, hyperbolicSpinRep]

/-- The pulled-back `aᵢ` acts by exterior creation. -/
@[simp]
theorem evenSpinRep_ι_evenSpinA
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) :
    evenSpinRep B hsymm hnd n hdim
        (CliffordAlgebra.ι (quadForm B)
          (evenSpinA B hsymm hnd n hdim i)) =
      creation n (evenSpinStandardVector n i) := by
  rw [evenSpinRep_ι]
  simp [evenSpinA, hyperbolicAction]

/-- The pulled-back `bᵢ` acts by contraction. -/
@[simp]
theorem evenSpinRep_ι_evenSpinB
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) (i : Fin n) :
    evenSpinRep B hsymm hnd n hdim
        (CliffordAlgebra.ι (quadForm B)
          (evenSpinB B hsymm hnd n hdim i)) =
      contraction n (evenSpinStandardCovector n i) := by
  rw [evenSpinRep_ι]
  simp [evenSpinB, hyperbolicAction]

/-- The transported spinor representation is bijective. -/
theorem evenSpinRep_bijective
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    Function.Bijective (evenSpinRep B hsymm hnd n hdim) :=
  (hyperbolicSpinRep_bijective n).comp
    (CliffordAlgebra.equivOfIsometry
      (evenSpinIsometry B hsymm hnd n hdim)).bijective

/-- The transported representation as an explicit algebra equivalence. -/
noncomputable def evenSpinAlgEquiv
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    CliffAlg B ≃ₐ[ℂ] Module.End ℂ (Spinor n) :=
  AlgEquiv.ofBijective (evenSpinRep B hsymm hnd n hdim)
    (evenSpinRep_bijective B hsymm hnd n hdim)

/-- The exterior spinor is irreducible for the transported action.  The action
is supplied explicitly so this theorem does not install a global Clifford
module instance on `Spinor n`. -/
theorem evenSpinor_irreducible
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    @IsSimpleModule (CliffAlg B) _ (Spinor n) _
      (Module.compHom (Spinor n)
        (evenSpinRep B hsymm hnd n hdim).toRingHom) := by
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  letI : Module (CliffAlg B) (Spinor n) :=
    Module.compHom (Spinor n)
      (evenSpinRep B hsymm hnd n hdim).toRingHom
  letI : RingHomSurjective
      (evenSpinRep B hsymm hnd n hdim).toRingHom :=
    ⟨(evenSpinRep_bijective B hsymm hnd n hdim).2⟩
  let e : Spinor n →ₛₗ[
      (evenSpinRep B hsymm hnd n hdim).toRingHom] Spinor n :=
    { AddMonoidHom.id (Spinor n) with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- A type-distinct copy of the exterior spinor carrying the transported
`CliffAlg B`-module structure.  Keeping this copy distinct avoids installing a
global Clifford action on the reusable type `Spinor n`. -/
def EvenSpinor
    (B : LinearMap.BilinForm ℂ V)
    (_hsymm : ∀ x y, B x y = B y x)
    (_hnd : B.Nondegenerate) (n : ℕ)
    (_hdim : Module.finrank ℂ V = 2 * n) :=
  ULift (Spinor n)

instance evenSpinorAddCommGroup
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    AddCommGroup (EvenSpinor B hsymm hnd n hdim) :=
  inferInstanceAs (AddCommGroup (ULift (Spinor n)))

instance evenSpinorComplexModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    Module ℂ (EvenSpinor B hsymm hnd n hdim) :=
  inferInstanceAs (Module ℂ (ULift (Spinor n)))

/-- The canonical linear identification of the bundled transported spinor with
the exterior-algebra model. -/
noncomputable def spinorEquivEvenSpinor
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    Spinor n ≃ₗ[ℂ] EvenSpinor B hsymm hnd n hdim :=
  ULift.moduleEquiv.symm

/-- The transported representation on the bundled `EvenSpinor` type. -/
noncomputable def evenSpinorRepresentation
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    CliffAlg B →ₐ[ℂ]
      Module.End ℂ (EvenSpinor B hsymm hnd n hdim) :=
  (spinorEquivEvenSpinor B hsymm hnd n hdim).conjAlgEquiv ℂ
    |>.toAlgHom.comp (evenSpinRep B hsymm hnd n hdim)

/-- The canonical Clifford-module action on the bundled transported spinor. -/
noncomputable instance evenSpinorCliffordModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    Module (CliffAlg B) (EvenSpinor B hsymm hnd n hdim) :=
  Module.compHom _ (evenSpinorRepresentation B hsymm hnd n hdim).toRingHom

/-- The bundled transported spinor is irreducible. -/
theorem evenSpinor_isSimpleModule
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n) :
    IsSimpleModule (CliffAlg B) (EvenSpinor B hsymm hnd n hdim) := by
  letI : Nontrivial (Spinor n) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinor]; positivity)
  letI : Nontrivial (EvenSpinor B hsymm hnd n hdim) :=
    (spinorEquivEvenSpinor B hsymm hnd n hdim).symm.toEquiv.nontrivial
  letI : RingHomSurjective
      (evenSpinorRepresentation B hsymm hnd n hdim).toRingHom := by
    refine ⟨?_⟩
    exact
      (spinorEquivEvenSpinor B hsymm hnd n hdim).conjAlgEquiv ℂ
        |>.surjective.comp
          (evenSpinRep_bijective B hsymm hnd n hdim).2
  let e : EvenSpinor B hsymm hnd n hdim →ₛₗ[
      (evenSpinorRepresentation B hsymm hnd n hdim).toRingHom]
      EvenSpinor B hsymm hnd n hdim :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  rw [e.isSimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- Every irreducible module for an even-dimensional nondegenerate complex
Clifford algebra is isomorphic to the explicit transported spinor. -/
theorem even_every_irreducible_iso_spinor
    (B : LinearMap.BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (n : ℕ)
    (hdim : Module.finrank ℂ V = 2 * n)
    (W : Type*) [AddCommGroup W] [Module (CliffAlg B) W]
    [IsSimpleModule (CliffAlg B) W] :
    Nonempty
      (W ≃ₗ[CliffAlg B] EvenSpinor B hsymm hnd n hdim) := by
  letI : IsSimpleRing (CliffAlg B) :=
    IsSimpleRing.of_ringEquiv
      (CliffordAlgebra.equivOfIsometry
        (evenSpinIsometry B hsymm hnd n hdim)).symm.toRingEquiv
      (hyperbolicClifford_isSimpleRing n)
  letI : IsArtinianRing (CliffAlg B) :=
    IsArtinianRing.of_finite ℂ (CliffAlg B)
  letI : IsSimpleModule (CliffAlg B)
      (EvenSpinor B hsymm hnd n hdim) :=
    evenSpinor_isSimpleModule B hsymm hnd n hdim
  obtain ⟨I, ⟨eW⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      (CliffAlg B) W
  obtain ⟨J, ⟨eS⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      (CliffAlg B) (EvenSpinor B hsymm hnd n hdim)
  letI : IsSimpleModule (CliffAlg B) I :=
    eW.isSimpleModule_iff.mp inferInstance
  letI : IsSimpleModule (CliffAlg B) J :=
    eS.isSimpleModule_iff.mp inferInstance
  let eJI : J ≃ₗ[CliffAlg B] I :=
    ((IsSimpleRing.isIsotypic (CliffAlg B) (CliffAlg B)) I J).some
  exact ⟨eW.trans (eJI.symm.trans eS.symm)⟩

end Etingof.Problem3_9_5
