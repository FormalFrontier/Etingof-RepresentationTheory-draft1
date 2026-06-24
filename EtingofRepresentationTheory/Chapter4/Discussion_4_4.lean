import Mathlib
import EtingofRepresentationTheory.Chapter4.Corollary4_2_4

/-!
# Discussion 4.4: Duals and tensor products of representations

For a representation `V` of a group `G`:

* the dual `V*` is a representation via `ρ_{V*}(g) = ρ_V(g⁻¹)*`, with character
  `χ_{V*}(g) = χ_V(g⁻¹)`;
* for complex representations of a finite group the eigenvalues of `ρ(g)` are roots
  of unity, so `χ_{V*}(g) = χ_V(g⁻¹) = conj χ_V(g)`, and consequently `V ≅ V*` as
  representations if and only if `χ_V(g) ∈ ℝ` for all `g`;
* the tensor product `V ⊗ W` is a representation via `ρ_{V⊗W}(g) = ρ_V(g) ⊗ ρ_W(g)`,
  with character `χ_{V⊗W}(g) = χ_V(g) χ_W(g)`.

## Mathlib correspondence

`FDRep.char_dual` and `FDRep.char_tensor` supply the dual- and tensor-character
formulas. The identity `χ_V(g⁻¹) = conj χ_V(g)` for complex finite-group
representations (the roots-of-unity step) is proved here as
`Etingof.char_inv_eq_conj`.
-/

open FDRep CategoryTheory CategoryTheory.MonoidalCategory Representation
open scoped Matrix ComplexOrder

universe u

namespace Etingof

variable {k G : Type u} [Field k] [Group G]

/-- Tensor-product character formula (Etingof §4.4):
`χ_{V⊗W}(g) = χ_V(g)·χ_W(g)`. -/
theorem Discussion_4_4_char_tensor (V W : FDRep k G) (g : G) :
    (V ⊗ W).character g = V.character g * W.character g := by
  rw [FDRep.char_tensor]; rfl

/-- Dual character formula (Etingof §4.4): `χ_{V*}(g) = χ_V(g⁻¹)`,
where `V*` is the dual representation `of (dual V.ρ)`. -/
theorem Discussion_4_4_char_dual (V : FDRep k G) (g : G) :
    (of (dual V.ρ)).character g = V.character g⁻¹ :=
  FDRep.char_dual V g

section Complex

variable [Fintype G]

/-- Complex-conjugate character identity (Etingof §4.4): for a finite-dimensional
complex representation `V` of a finite group `G`, the eigenvalues of `ρ_V(g)` are
roots of unity (since `ρ_V(g)^|G|` need only be a root-of-unity power: `ρ_V(g)` has
finite order dividing `orderOf g`), and `λ⁻¹ = conj λ` for each. Hence

  `χ_V(g⁻¹) = Σ λᵢ⁻¹ = Σ conj λᵢ = conj χ_V(g)`.

Equivalently, via the unitarizability of `V` (Theorem 4.6.2): a `G`-invariant
positive-definite Hermitian form makes each `ρ_V(g)` unitary, so its adjoint equals
its inverse, and `trace(adjoint f) = conj(trace f)` for any operator on a
finite-dimensional inner product space (`LinearMap.toMatrix_adjoint` together with
`Matrix.trace_conjTranspose`). -/
theorem char_inv_eq_conj (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = (starRingEnd ℂ) (V.character g) := by
  classical
  haveI : Nonempty G := ⟨1⟩
  -- Work with the matrix of `ρ_V` in a chosen basis.
  let b := Module.finBasis ℂ V
  set M : G → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun h => LinearMap.toMatrix b b (V.ρ h) with hM
  have hM_mul : ∀ a c : G, M (a * c) = M a * M c := by
    intro a c; simp only [hM, map_mul, LinearMap.toMatrix_mul]
  have hM_one : M 1 = 1 := by simp only [hM, map_one, LinearMap.toMatrix_one]
  have hchar : ∀ h : G, V.character h = (M h).trace := by
    intro h; simp only [FDRep.character, hM]; rw [LinearMap.trace_eq_matrix_trace ℂ b]
  have hunit : ∀ h : G, IsUnit (M h) := fun h =>
    ⟨⟨M h, M h⁻¹, by rw [← hM_mul, mul_inv_cancel, hM_one],
      by rw [← hM_mul, inv_mul_cancel, hM_one]⟩, rfl⟩
  have hdet : ∀ h : G, IsUnit (M h).det :=
    fun h => (Matrix.isUnit_iff_isUnit_det _).mp (hunit h)
  have hginv : (M g)⁻¹ = M g⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [← hM_mul, inv_mul_cancel, hM_one])
  -- The averaged Hermitian form `H = Σ_h (ρ h)ᴴ (ρ h)` is positive definite (hence invertible)
  -- and `G`-invariant: `(ρ g)ᴴ H (ρ g) = H`. This is the unitarization of Theorem 4.6.2.
  set H : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    ∑ h : G, (M h)ᴴ * M h with hH
  have hH_pd : H.PosDef := by
    rw [hH]
    refine Matrix.posDef_sum Finset.univ_nonempty (fun h _ => ?_)
    have := (Matrix.IsUnit.posDef_star_left_conjugate_iff (hunit h)).mpr Matrix.PosDef.one
    simpa [Matrix.star_eq_conjTranspose] using this
  have hH_det : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hH_pd.isUnit
  have hinv : (M g)ᴴ * H * M g = H := by
    have step : ∀ h : G, (M g)ᴴ * ((M h)ᴴ * M h) * M g = (M (h * g))ᴴ * M (h * g) := by
      intro h; rw [hM_mul, Matrix.conjTranspose_mul]; simp only [mul_assoc]
    calc (M g)ᴴ * H * M g
        = ∑ h : G, (M g)ᴴ * ((M h)ᴴ * M h) * M g := by rw [hH, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ h : G, (M (h * g))ᴴ * M (h * g) := Finset.sum_congr rfl (fun h _ => step h)
      _ = ∑ h : G, (M h)ᴴ * M h := Equiv.sum_comp (Equiv.mulRight g) fun h => (M h)ᴴ * M h
      _ = H := rfl
  -- Solve for `(ρ g)ᴴ`: it is conjugate to `(ρ g)⁻¹` by `H`.
  have e1 : (M g)ᴴ * H = H * (M g)⁻¹ := by
    have h2 : (M g)ᴴ * H * M g * (M g)⁻¹ = H * (M g)⁻¹ := by rw [hinv]
    rwa [mul_assoc ((M g)ᴴ * H) (M g) (M g)⁻¹, Matrix.mul_nonsing_inv _ (hdet g), mul_one] at h2
  have hconj : (M g)ᴴ = H * (M g)⁻¹ * H⁻¹ := by
    calc (M g)ᴴ = (M g)ᴴ * H * H⁻¹ := by
          rw [mul_assoc, Matrix.mul_nonsing_inv _ hH_det, mul_one]
      _ = H * (M g)⁻¹ * H⁻¹ := by rw [e1]
  -- Conclude: `conj χ(g) = trace (ρ g)ᴴ = trace (ρ g)⁻¹ = χ(g⁻¹)`.
  rw [hchar g⁻¹, hchar g, starRingEnd_apply, ← Matrix.trace_conjTranspose, hconj,
    Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hH_det, one_mul, hginv]

/-- Self-dual ⟺ real character (Etingof §4.4): a finite-dimensional complex
representation `V` of a finite group is isomorphic to its dual `V*` (as
representations) if and only if its character is real-valued. -/
theorem self_dual_iff_char_real {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) :
    Nonempty (of (dual V.ρ) ≅ V) ↔
      ∀ g : G, (starRingEnd ℂ) (V.character g) = V.character g := by
  constructor
  · rintro ⟨e⟩ g
    have h : V.character g⁻¹ = V.character g := by
      have h0 := congrFun (FDRep.char_iso e) g
      rwa [FDRep.char_dual] at h0
    rw [← char_inv_eq_conj, h]
  · intro hreal
    -- A real character forces `χ_{V*} = χ_V`: indeed `χ_{V*}(g) = χ_V(g⁻¹) = conj χ_V(g) = χ_V(g)`.
    -- Over `ℂ`, equal characters force an isomorphism of representations
    -- (`Etingof.Corollary4_2_4`, characters determine the representation).
    classical
    have hchar_eq : FDRep.character (of (dual V.ρ)) = FDRep.character V := by
      funext g
      rw [Discussion_4_4_char_dual V g, char_inv_eq_conj V g]
      exact hreal g
    exact Etingof.Corollary4_2_4 G (of (dual V.ρ)) V hchar_eq

end Complex

end Etingof
