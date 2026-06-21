import EtingofRepresentationTheory.Chapter6.Problem6_1_5_OrbitSpace
import Mathlib

/-!
# Problem 6.1.5, Step 2(b) (continued): the orbit-map comorphism

This file is part of the orbit-counting redirect for the Chapter 6 infinite-type
direction (directive #4777). It continues **step 2(b)** of Etingof Problem 6.1.2
(#4783): the field-embedding bridge `Problem6_1_5_FieldEmbedding` reduces the
dimension bound `N ≤ M` to *injectivity of the orbit-map comorphism*; this file
**constructs that comorphism concretely** on `W(m)` / `G(m)` from S0
(`Problem6_1_5_OrbitSpace`).

## What this file provides

* `GIdx m` and `WIdx m`: the concrete coordinate index types of the group ambient
  space `∏ᵢ Matrix (Fin mᵢ) (Fin mᵢ)` (so `k[G] = MvPolynomial (GIdx m) k`,
  `M = card = ∑ᵢ mᵢ²`, `gIdx_card`) and of the representation space `W(m)` (so
  `k[W] = MvPolynomial (WIdx m) k`, `N = card = ∑ᵢⱼ bᵢⱼ mᵢ mⱼ`, `wIdx_card`).
* `genMat m i`: the **generic matrix** at vertex `i` over `k[gₚᵩ] = MvPolynomial
  (GIdx m) k`, whose `(a,b)` entry is the coordinate generator `X ⟨i,(a,b)⟩`.
* `detProd m = ∏ᵢ det(genMat m i)`, with `detProd_ne_zero`: it is a nonzero
  polynomial (it evaluates to `det 1 = 1` at the identity point), so the localization
  `k[gₚᵩ, detProd⁻¹]` — the coordinate ring of the principal open `G = {det ≠ 0}` —
  is a domain and `detProd` is inverted there.
* over an abstract localization `B` of `k[gₚᵩ]` at the powers of `detProd`
  (the principal-open coordinate ring): `genMatB m i` (the generic matrix over `B`),
  `isUnit_det_genMatB` (its determinant is a unit, because `det(genMat m i)`
  divides the inverted `detProd`), and its inverse `genMatBInv m i` with
  `genMatB_mul_inv`.
* `orbitComorphism v₀ : MvPolynomial (WIdx m) k →ₐ[k] B`: the genuine `k`-algebra
  **orbit-map comorphism** for the base point `v₀`, sending the coordinate
  `X⟨i,j,e,(a,b)⟩` of `W(m)` to the `(a,b)` entry of the generic base-change
  `Gⱼ · (v₀)ᵢⱼₑ · Gᵢ⁻¹` (the `Gᵢ⁻¹` is exactly why the target is the `detProd⁻¹`
  localization, matching the principal-open case of the field-embedding bridge,
  `Etingof.Problem6_1_5.exists_field_embedding_of_injective_isLocalization`).

## What remains (tracked as follow-ups to #4803)

* **Injectivity of `orbitComorphism` from Zariski-density of the orbit** (the genuine
  geometric input, Problem 6.1.2(a)). Over an infinite field a polynomial vanishing
  on a Zariski-dense set is zero; converting S2a's topological density
  (`Problem6_1_5_DenseOrbit.exists_dense_orbit_point`) to this algebraic statement
  needs the Zariski topology on `𝔸ᴺ` pinned down and polynomial-evaluation
  faithfulness. Filed separately.
* **The dimension-bound assembly** `N ≤ M`: feed an injective `orbitComorphism` to
  `Etingof.Problem6_1_5.dim_le_of_injective_comorphism_isLocalization`, transporting
  the `GIdx m`-indexing to `Fin M` via `MvPolynomial.renameEquiv`. Filed separately.
-/

open Matrix MvPolynomial

namespace Etingof.Problem6_1_5

variable {k : Type} [Field k] {n : ℕ}

/-! ## Coordinate index types -/

/-- Coordinate index for the group ambient space `∏ᵢ Matrix (Fin mᵢ) (Fin mᵢ)`:
a vertex `i` together with a matrix position `(a,b)` in block `i`. Its cardinality
is `∑ᵢ mᵢ²` (`gIdx_card`), so `k[G] = MvPolynomial (GIdx m) k` with `M = dim G`
variables. -/
abbrev GIdx (m : Fin n → ℕ) : Type := Σ i : Fin n, Fin (m i) × Fin (m i)

/-- Coordinate index for the representation space `W(m)`: an arrow `e : i ⟶ j`
together with a matrix position `(a,b)` in the `i→j` block. Its cardinality is
`∑ᵢⱼ bᵢⱼ mᵢ mⱼ` (`wIdx_card`), so `k[W] = MvPolynomial (WIdx m) k` with `N = dim W`
variables. -/
abbrev WIdx [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] (m : Fin n → ℕ) : Type :=
  Σ i : Fin n, Σ j : Fin n, (i ⟶ j) × (Fin (m j) × Fin (m i))

/-- `M = card (GIdx m) = ∑ᵢ mᵢ²` = `repGroup_ambient_finrank`. -/
theorem gIdx_card (m : Fin n → ℕ) :
    Fintype.card (GIdx m) = ∑ i : Fin n, (m i) ^ 2 := by
  simp only [GIdx, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_congr rfl fun i _ => (pow_two (m i)).symm

/-- `N = card (WIdx m) = ∑ᵢⱼ bᵢⱼ mᵢ mⱼ` = `repSpace_finrank`. -/
theorem wIdx_card [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] (m : Fin n → ℕ) :
    Fintype.card (WIdx m) = ∑ i : Fin n, ∑ j : Fin n, arrowCount i j * (m i * m j) := by
  simp only [WIdx]
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, arrowCount,
    mul_comm (m j) (m i)]

/-! ## The generic matrices over `k[gₚᵩ]` -/

/-- The **generic matrix** at vertex `i` over `k[gₚᵩ] = MvPolynomial (GIdx m) k`:
its `(a,b)` entry is the coordinate generator `X ⟨i,(a,b)⟩`. -/
noncomputable def genMat (m : Fin n → ℕ) (i : Fin n) :
    Matrix (Fin (m i)) (Fin (m i)) (MvPolynomial (GIdx m) k) :=
  fun a b => X ⟨i, (a, b)⟩

/-- `detProd m = ∏ᵢ det(genMat m i)`, the product of all the vertex determinants.
Inverting it cuts out the principal open `G = {det ≠ 0}`. -/
noncomputable def detProd (m : Fin n → ℕ) : MvPolynomial (GIdx m) k :=
  ∏ i : Fin n, (genMat (k := k) m i).det

/-- Evaluate every coordinate generator at the identity matrix: `X⟨i,(a,b)⟩ ↦ δₐᵦ`.
Used to certify `detProd m ≠ 0` (it evaluates to `det 1 = 1`). -/
noncomputable def evalId (m : Fin n → ℕ) : MvPolynomial (GIdx m) k →ₐ[k] k :=
  aeval (fun w : GIdx m => if w.2.1 = w.2.2 then (1 : k) else 0)

theorem genMat_map_evalId (m : Fin n → ℕ) (i : Fin n) :
    (evalId m).mapMatrix (genMat (k := k) m i) = 1 := by
  ext a b
  simp [genMat, evalId, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]

theorem evalId_detProd (m : Fin n → ℕ) : evalId m (detProd (k := k) m) = 1 := by
  rw [detProd, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [AlgHom.map_det, genMat_map_evalId, Matrix.det_one]

theorem detProd_ne_zero (m : Fin n → ℕ) :
    detProd (k := k) m ≠ (0 : MvPolynomial (GIdx m) k) := by
  intro h
  have h1 := evalId_detProd (k := k) m
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

/-! ## The generic matrices over the `detProd⁻¹` localization, and their inverses -/

section Comorphism

variable (m : Fin n → ℕ)
variable {B : Type} [CommRing B]
  [Algebra (MvPolynomial (GIdx m) k) B]
  [IsLocalization (Submonoid.powers (detProd (k := k) m)) B]

/-- The generic matrix at vertex `i` over the principal-open coordinate ring `B`
(a localization of `k[gₚᵩ]` at `detProd`), obtained by mapping `genMat m i` along
the localization map. -/
noncomputable def genMatB (i : Fin n) : Matrix (Fin (m i)) (Fin (m i)) B :=
  (genMat (k := k) m i).map (algebraMap (MvPolynomial (GIdx m) k) B)

/-- Over the localization `B`, the determinant of each generic matrix is a unit:
`det(genMat m i)` divides the inverted `detProd m`. -/
theorem isUnit_det_genMatB (i : Fin n) : IsUnit ((genMatB (k := k) (B := B) m i).det) := by
  have hmap : (genMatB (k := k) (B := B) m i).det
      = algebraMap (MvPolynomial (GIdx m) k) B ((genMat (k := k) m i).det) := by
    unfold genMatB
    exact (RingHom.map_det _ _).symm
  rw [hmap]
  have hdvd : (genMat (k := k) m i).det ∣ detProd (k := k) m :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hunit : IsUnit (algebraMap (MvPolynomial (GIdx m) k) B (detProd (k := k) m)) :=
    IsLocalization.map_units B ⟨detProd (k := k) m, Submonoid.mem_powers _⟩
  exact isUnit_of_dvd_unit (map_dvd _ hdvd) hunit

/-- The inverse of the generic matrix `genMatB m i` over the localization `B`. -/
noncomputable def genMatBInv (i : Fin n) : Matrix (Fin (m i)) (Fin (m i)) B :=
  (genMatB (k := k) (B := B) m i)⁻¹

theorem genMatB_mul_inv (i : Fin n) :
    genMatB (k := k) (B := B) m i * genMatBInv (k := k) (B := B) m i = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_genMatB m i)

/-! ## The orbit-map comorphism -/

variable [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] [Algebra k B]
  [IsScalarTower k (MvPolynomial (GIdx m) k) B]

/-- **The orbit-map comorphism** `φ* : k[W(m)] → B` for the base point `v₀`.

It is the comorphism of the orbit map `g ↦ g • v₀`, sending the coordinate
`X⟨i,j,e,(a,b)⟩` of `W(m)` to the `(a,b)` entry of the generic base-change
`Gⱼ · (v₀)ᵢⱼₑ · Gᵢ⁻¹` (cf. `repSpace_smul_apply`). The inverse `Gᵢ⁻¹` is why the
target must be the `detProd⁻¹` localization `B`. Injectivity of this map is
Zariski-density of the orbit (Problem 6.1.2(a)); feeding it to
`exists_field_embedding_of_injective_isLocalization` yields `N ≤ M`. -/
noncomputable def orbitComorphism (v₀ : repSpace (k := k) m) :
    MvPolynomial (WIdx m) k →ₐ[k] B :=
  aeval (fun w : WIdx m =>
    (genMatB (k := k) (B := B) m w.2.1 *
        (v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k B) *
        genMatBInv (k := k) (B := B) m w.1) w.2.2.2.1 w.2.2.2.2)

omit [IsScalarTower k (MvPolynomial (GIdx m) k) B]
  [IsLocalization (Submonoid.powers (detProd (k := k) m)) B] in
@[simp]
theorem orbitComorphism_X (v₀ : repSpace (k := k) m) (w : WIdx m) :
    orbitComorphism (B := B) m v₀ (X w) =
      (genMatB (k := k) (B := B) m w.2.1 *
          (v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k B) *
          genMatBInv (k := k) (B := B) m w.1) w.2.2.2.1 w.2.2.2.2 := by
  rw [orbitComorphism, aeval_X]

end Comorphism

end Etingof.Problem6_1_5
