import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Proposition 5.22.2: Twisting by Determinant

`L_{λ + 1^N} ≅ L_λ ⊗ ∧^N V`, where `1^N = (1, 1, …, 1)`.

The top exterior power `∧^N V` is the one-dimensional determinant representation
of `GL_N(k)`. Tensoring by it shifts every part of the highest weight by 1.
This follows from the inclusion `L_λ ⊗ ∧^N V ⊂ V^{⊗(n+N)}` and the
uniqueness of the component with the given character.

## Mathlib correspondence

Uses the Schur module from `Theorem5_22_1`. The tensor product of `FDRep` objects
uses the monoidal category structure on `FDRep k G`.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Etingof

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- The determinant representation of `GL_N(k)`: the one-dimensional representation
given by `g ↦ det(g)`. This is isomorphic to the top exterior power `∧^N(k^N)` as
a `GL_N`-representation. Not yet in Mathlib. -/
noncomputable def detRep (N : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  FDRep.of (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
    Matrix.GeneralLinearGroup.det)

/-- The determinant-twisted Schur module representation: `g ↦ det(g) • schurModuleRep(g)`.
This is the representation on the same underlying vector space as `L_λ`, but with the
GL_N action twisted by the determinant character. -/
def detTwistedSchurModuleRep (N : ℕ) (lam : Fin N → ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (SchurModuleSubmodule k N lam) where
  toFun g := (Matrix.GeneralLinearGroup.det g : k) • schurModuleRep k N lam g
  map_one' := by simp [map_one]
  map_mul' g₁ g₂ := by
    have hdet : (Matrix.GeneralLinearGroup.det (g₁ * g₂) : k) =
      (Matrix.GeneralLinearGroup.det g₁ : k) * (Matrix.GeneralLinearGroup.det g₂ : k) := by
      simp [map_mul]
    have hmul : (schurModuleRep k N lam) (g₁ * g₂) = (schurModuleRep k N lam) g₁ *
      (schurModuleRep k N lam) g₂ := map_mul _ _ _
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, hdet, hmul]
    rw [mul_smul]
    simp only [map_smul, Submodule.coe_smul_of_tower]

/-! ### Schur polynomial shift identity

The Schur polynomial for the shifted partition `λ + (1,…,1)` equals
`(∏ Xᵢ) · S_λ`. This follows from the alternant determinant row-scaling
identity: multiplying each row i by `Xᵢ` shifts all exponents by 1. -/

/-- The shifted exponents for `λ + (1,…,1)` equal the original shifted exponents plus 1. -/
private lemma shiftedExps_shift (N : ℕ) (lam : Fin N → ℕ) :
    shiftedExps N (fun i => lam i + 1) = fun j => shiftedExps N lam j + 1 := by
  ext j; simp [shiftedExps]; omega

/-- The alternant matrix with all exponents incremented by 1 equals the diagonal matrix
`diag(X₀, …, X_{N-1})` times the original alternant matrix. -/
private lemma alternantMatrix_shift (N : ℕ) (e : Fin N → ℕ) :
    alternantMatrix N (fun j => e j + 1) =
      Matrix.diagonal (fun i => MvPolynomial.X i) * alternantMatrix N e := by
  ext i j
  simp [alternantMatrix, Matrix.of_apply, Matrix.diagonal_mul, pow_succ, mul_comm]

/-- Row-scaling identity: incrementing all exponents multiplies the alternant
determinant by `∏ Xᵢ`. -/
private lemma alternant_det_shift (N : ℕ) (e : Fin N → ℕ) :
    (alternantMatrix N (fun j => e j + 1)).det =
      (∏ i : Fin N, MvPolynomial.X i) * (alternantMatrix N e).det := by
  rw [alternantMatrix_shift, Matrix.det_mul, Matrix.det_diagonal]

/-- **Schur polynomial shift**: `S_{λ+(1,…,1)} = (∏ Xᵢ) · S_λ`.
Adding 1 to every part of the partition multiplies the Schur polynomial
by the monomial `x₁ · x₂ · ⋯ · x_N`. -/
theorem schurPoly_shift (N : ℕ) (lam : Fin N → ℕ) :
    schurPoly N (fun i => lam i + 1) =
      (∏ i : Fin N, MvPolynomial.X i) * schurPoly N lam := by
  have hΔ := alternantMatrix_vandermondeExps_det_ne_zero N
  apply mul_right_cancel₀ hΔ
  rw [mul_assoc, schurPoly_mul_vandermonde, schurPoly_mul_vandermonde,
      ← alternant_det_shift, shiftedExps_shift]

/-! ### Character theory for the determinant twist -/

/-- The determinant of `diagUnit k N i t` is `t`. -/
private lemma det_diagUnit (N : ℕ) (i : Fin N) (t : kˣ) :
    (Matrix.GeneralLinearGroup.det (diagUnit k N i t) : k) = t := by
  change Matrix.det (Matrix.diagonal (Function.update 1 i (t : k))) = t
  rw [Matrix.det_diagonal]
  simp only [Finset.prod_update_of_mem (Finset.mem_univ i), Pi.one_apply, Finset.prod_const_one,
    mul_one]

/-- The formal character of `L_{λ+(1,…,1)}` equals `(∏ Xᵢ) · char(L_λ)`.
This follows from Theorem 5.22.1 (Weyl character formula) and schurPoly_shift. -/
theorem formalCharacter_schurModule_shift (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    formalCharacter k N (SchurModule k N (fun i => lam i + 1)) =
      (∏ i : Fin N, MvPolynomial.X i) * formalCharacter k N (SchurModule k N lam) := by
  have hlam' : Antitone (fun i => lam i + 1) := fun i j hij => Nat.add_le_add_right (hlam hij) 1
  rw [Theorem5_22_1 k N _ hlam', Theorem5_22_1 k N lam hlam, schurPoly_shift]

/-! ### Weight space analysis for the determinant twist

The determinant twist shifts every weight by `(1,…,1)`: if `v` has weight `ν` under
the original representation, then `v` has weight `ν + 1` under the det-twisted
representation (because `det(diagUnit(i,t)) = t`, so the action gains a factor of `t`). -/

/-- The det-twisted action of `diagUnit(i,t)` equals `t` times the original action. -/
private lemma detTwist_diagUnit (N : ℕ) (lam : Fin N → ℕ) (i : Fin N) (t : kˣ) :
    detTwistedSchurModuleRep k N lam (diagUnit k N i t) =
      (t : k) • schurModuleRep k N lam (diagUnit k N i t) := by
  unfold detTwistedSchurModuleRep
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  exact det_diagUnit k N i t

-- The `iInf_congr` + `ker_smul` rewriting is expensive because the kernel
-- of a linear map on `SchurModuleSubmodule` involves `PiTensorProduct.map`.
set_option maxHeartbeats 800000 in
/-- The weight space at `ν + 1` in the det-twisted rep equals the weight space at `ν`
in the original Schur module. Both are submodules of the same underlying vector space. -/
private theorem glWeightSpace_detTwist_shift (N : ℕ) (lam : Fin N → ℕ) (ν : Fin N → ℕ) :
    glWeightSpace k N (FDRep.of (detTwistedSchurModuleRep k N lam)) (fun i => ν i + 1) =
      glWeightSpace k N (SchurModule k N lam) ν := by
  simp only [glWeightSpace]
  apply iInf_congr; intro i
  apply iInf_congr; intro t
  -- detTwist.ρ(diagUnit(i,t)) = t • original.ρ(diagUnit(i,t))  [by det_diagUnit]
  have hρ : (FDRep.of (detTwistedSchurModuleRep k N lam)).ρ (diagUnit k N i t) =
      (t : k) • (SchurModule k N lam).ρ (diagUnit k N i t) := by
    change detTwistedSchurModuleRep k N lam (diagUnit k N i t) =
      (t : k) • schurModuleRep k N lam (diagUnit k N i t)
    exact detTwist_diagUnit k N lam i t
  -- t • f - t^{ν+1} • id = t • (f - t^ν • id), so ker is the same (t is a unit)
  rw [hρ]
  have factor : (↑t : k) • (SchurModule k N lam).ρ (diagUnit k N i t) -
      (↑t : k) ^ (ν i + 1) • LinearMap.id =
    (↑t : k) • ((SchurModule k N lam).ρ (diagUnit k N i t) -
      (↑t : k) ^ ν i • LinearMap.id) := by
    rw [smul_sub, pow_succ', mul_smul]
  rw [factor, LinearMap.ker_smul _ _ (Units.ne_zero t)]

/-- Two polynomial `GL_N`-representations with the same formal character are isomorphic.

This follows from complete reducibility of polynomial representations of `GL_N(k)`
over algebraically closed fields: both decompose as direct sums of simple modules,
and simple polynomial `GL_N`-representations are classified by their highest weight,
which is determined by the formal character.

TODO: requires complete reducibility of `GL_N`-representations (Schur–Weyl duality
or reductive group theory). See #1788 for related infrastructure. -/
private theorem glRep_iso_of_formalCharacter_eq (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M₁ = formalCharacter k N M₂) :
    Nonempty (M₁ ≅ M₂) := by
  sorry

/-- The formal character of the det-twisted Schur module equals `(∏ Xᵢ) · char(L_λ)`.

The determinant twist shifts every weight by `(1,…,1)`, which multiplies the
formal character by the monomial `∏ Xᵢ`. -/
private theorem formalCharacter_detTwist (N : ℕ) (lam : Fin N → ℕ) :
    formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      (∏ i : Fin N, MvPolynomial.X i) * formalCharacter k N (SchurModule k N lam) := by
  sorry

/-- Key isomorphism: the Schur module `L_{λ+(1,…,1)}` is isomorphic (as a GL_N-representation)
to the determinant-twisted Schur module `det ⊗ L_λ`.

Both representations have the same formal character: `(∏ Xᵢ) · char(L_λ)`.
The isomorphism follows from the fact that polynomial `GL_N`-representations
are determined by their formal character. -/
theorem schurModule_shift_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (FDRep.of (schurModuleRep k N (fun i => lam i + 1)) ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  apply glRep_iso_of_formalCharacter_eq
  change formalCharacter k N (SchurModule k N (fun i => lam i + 1)) =
    formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam))
  rw [formalCharacter_schurModule_shift k N lam hlam, formalCharacter_detTwist]

/-- The `TensorProduct.rid` intertwines the tensor action `rep(g) ⊗ det(g)·id` with
the determinant-twisted action `det(g) · rep(g)`. -/
theorem tensorRid_comm_detTwist (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    (TensorProduct.rid k (SchurModuleSubmodule k N lam)).toLinearMap ∘ₗ
      TensorProduct.map (schurModuleRep k N lam g)
        (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
          Matrix.GeneralLinearGroup.det g) =
    (detTwistedSchurModuleRep k N lam g) ∘ₗ
      (TensorProduct.rid k (SchurModuleSubmodule k N lam)).toLinearMap := by
  apply TensorProduct.ext'
  intro v c
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul, detTwistedSchurModuleRep]
  -- LHS: (det(g)·c) • rep(g) v   RHS: det(g) • rep(g) (c • v)
  -- LHS: (↑(lsmul).toRingHom ↑(det g)) c • rep(g) v  = (↑(det g) * c) • rep(g) v
  -- RHS: det(g) • rep(g) (c • v) = det(g) • c • rep(g) v
  change ((↑(Matrix.GeneralLinearGroup.det g) : k) * c) • ((schurModuleRep k N lam) g) v =
    (↑(Matrix.GeneralLinearGroup.det g) : k) • ((schurModuleRep k N lam) g) (c • v)
  rw [map_smul, mul_smul, smul_comm]

/-- The FDRep tensor product `L_λ ⊗ det` is isomorphic to the determinant-twisted
representation. For any 1-dimensional representation `χ`, `M ⊗ χ` is isomorphic
to `M` with the action twisted by `χ`. -/
theorem schurModule_tensor_det_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) :
    Nonempty (SchurModule k N lam ⊗ detRep k N ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  -- The underlying linear iso is TensorProduct.rid: M ⊗ k ≅ M
  refine ⟨Action.mkIso
    ((TensorProduct.rid k (SchurModuleSubmodule k N lam)).toFGModuleCatIso) (fun g => ?_)⟩
  ext : 1
  exact tensorRid_comm_detTwist k N lam g

/-- **Determinant twist**: `L_{λ+(1,…,1)} ≅ L_λ ⊗ ∧^N V` as `GL_N(k)`-representations.

Tensoring with the one-dimensional determinant representation shifts every part
of the highest weight by 1.
(Etingof Proposition 5.22.2) -/
theorem Proposition5_22_2
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (SchurModule k N (fun i => lam i + 1) ≅
      SchurModule k N lam ⊗ detRep k N) := by
  -- Decompose into two steps:
  -- (1) L_{λ+1^N} ≅ det-twisted L_λ  (character argument)
  -- (2) det-twisted L_λ ≅ L_λ ⊗ det  (categorical tensor/twist equivalence)
  obtain ⟨iso₁⟩ := schurModule_shift_iso_detTwist k N lam hlam
  obtain ⟨iso₂⟩ := schurModule_tensor_det_iso_detTwist k N lam
  exact ⟨iso₁ ≪≫ iso₂.symm⟩

end Etingof
