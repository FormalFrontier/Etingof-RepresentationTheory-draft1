import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import Mathlib

/-!
# Problem 6.1.5 S0: the representation space `W(m)`, the group `G(m)`, and orbits

This file sets up the geometric side of the orbit-counting route to Gabriel's theorem
(directive #4777). Fix a quiver `Q` on `Fin n` and a dimension vector `m : Fin n → ℕ`
over a field `k`.

* `Etingof.repSpace Q m` is the affine space of representations of dimension vector `m`:
  to each arrow `e : i ⟶ j` it assigns a matrix `Matrix (Fin (m j)) (Fin (m i)) k`,
  i.e. a linear map `kᵐⁱ → kᵐʲ`. Its dimension is `∑ᵢⱼ bᵢⱼ · mᵢ · mⱼ` where
  `bᵢⱼ = #(i ⟶ j)` (`repSpace_finrank`).
* `Etingof.repGroup m = ∏ᵢ GLₘᵢ(k)` acts on `repSpace Q m` by base change at each
  vertex: `g` sends the `i → j` block `M` to `g j · M · (g i)⁻¹` (`repSpace_smul_apply`).
  The ambient matrix space of the group has dimension `∑ᵢ mᵢ²`
  (`repGroup_ambient_finrank`) — this is the variable count `M = dim G` consumed by the
  transcendence-degree step (Problem 6.1.1).
* `Etingof.repOfPoint` turns a point of `repSpace Q m` into a genuine
  `QuiverRepresentation`, and `Etingof.orbit_iff_isomorphic` is the linchpin:
  two points lie in the same `G(m)`-orbit **iff** the represented representations are
  isomorphic. This is what S1/S2 consume to translate "finitely many orbits" into
  "finitely many isomorphism classes".

The dimension formulas are `sorry`-free; `orbit_iff_isomorphic` is the data linchpin
described in #4780.
-/

namespace Etingof

open Matrix

universe u

variable {k : Type u} [Field k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- The **representation space** at dimension vector `m`: a point assigns to each arrow
`e : i ⟶ j` a matrix `Matrix (Fin (m j)) (Fin (m i)) k`, viewed as a linear map
`kᵐⁱ → kᵐʲ`. As a `k`-vector space its dimension is `∑ᵢⱼ bᵢⱼ mᵢ mⱼ`. -/
abbrev repSpace (m : Fin n → ℕ) : Type u :=
  ∀ i j : Fin n, (i ⟶ j) → Matrix (Fin (m j)) (Fin (m i)) k

/-- The **base-change group** `G(m) = ∏ᵢ GLₘᵢ(k)`. -/
abbrev repGroup (k : Type u) [Field k] {n : ℕ} (m : Fin n → ℕ) : Type u :=
  ∀ i : Fin n, GL (Fin (m i)) k

/-- The number of arrows `i → j`, written `bᵢⱼ` in the book. -/
def arrowCount [∀ i j : Fin n, Fintype (i ⟶ j)] (i j : Fin n) : ℕ := Fintype.card (i ⟶ j)

/-! ## Dimension of the representation space -/

/-- `dim W(m) = ∑ᵢⱼ bᵢⱼ mᵢ mⱼ`. -/
theorem repSpace_finrank [∀ i j : Fin n, Fintype (i ⟶ j)] (m : Fin n → ℕ) :
    Module.finrank k (repSpace (k := k) m) =
      ∑ i : Fin n, ∑ j : Fin n, arrowCount i j * (m i * m j) := by
  classical
  rw [Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Module.finrank_pi_fintype k]
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, arrowCount, Fintype.card_fin]
  ring

/-! ## Dimension of the group -/

omit [Quiver.{0} (Fin n)] in
/-- The ambient matrix space of `G(m) = ∏ᵢ GLₘᵢ(k)` is `∏ᵢ Matrix (Fin mᵢ) (Fin mᵢ) k`,
whose dimension is `∑ᵢ mᵢ²`. This is the variable count `dim G` (the number of matrix
entries `g_{pq}`) used in the transcendence-degree step of Problem 6.1.1. -/
theorem repGroup_ambient_finrank (m : Fin n → ℕ) :
    Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k) =
      ∑ i : Fin n, (m i) ^ 2 := by
  rw [Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin, pow_two]

/-! ## The base-change action -/

/-- Base-change action of `G(m)` on `W(m)`: `g` acts on the `i → j` block `M` by
`g j · M · (g i)⁻¹`. -/
instance repSpaceSMul (m : Fin n → ℕ) : SMul (repGroup k m) (repSpace (k := k) m) where
  smul g x := fun i j e =>
    (↑(g j) : Matrix (Fin (m j)) (Fin (m j)) k) * x i j e *
      (↑(g i)⁻¹ : Matrix (Fin (m i)) (Fin (m i)) k)

@[simp]
theorem repSpace_smul_apply (m : Fin n → ℕ) (g : repGroup k m) (x : repSpace (k := k) m)
    (i j : Fin n) (e : i ⟶ j) :
    (g • x) i j e =
      (↑(g j) : Matrix (Fin (m j)) (Fin (m j)) k) * x i j e *
        (↑(g i)⁻¹ : Matrix (Fin (m i)) (Fin (m i)) k) := rfl

instance repSpaceMulAction (m : Fin n → ℕ) :
    MulAction (repGroup k m) (repSpace (k := k) m) where
  one_smul x := by
    funext i j e
    rw [repSpace_smul_apply]
    simp
  mul_smul g h x := by
    funext i j e
    rw [repSpace_smul_apply, repSpace_smul_apply, repSpace_smul_apply]
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_assoc]

/-! ## From a point to a representation -/

/-- The quiver representation determined by a point of `W(m)`: the space at vertex `i`
is `kᵐⁱ`, and the arrow `e : i ⟶ j` acts by the linear map of the matrix `x i j e`. -/
noncomputable def repOfPoint (m : Fin n → ℕ) (x : repSpace (k := k) m) :
    QuiverRepresentation k (Fin n) where
  obj := fun i => Fin (m i) → k
  mapLinear := fun {i j} e => Matrix.toLin' (x i j e)

@[simp]
theorem repOfPoint_obj (m : Fin n → ℕ) (x : repSpace (k := k) m) (i : Fin n) :
    (repOfPoint m x).obj i = (Fin (m i) → k) := rfl

@[simp]
theorem repOfPoint_mapLinear (m : Fin n → ℕ) (x : repSpace (k := k) m)
    {i j : Fin n} (e : i ⟶ j) :
    (repOfPoint m x).mapLinear e = Matrix.toLin' (x i j e) := rfl

/-- The `≃ₗ` attached to an element of `GLₚ(k)`, given by its matrix and the inverse
matrix. -/
noncomputable def glLinearEquiv {p : ℕ} (g : GL (Fin p) k) :
    (Fin p → k) ≃ₗ[k] (Fin p → k) :=
  LinearEquiv.ofLinear (Matrix.toLin' (g : Matrix _ _ k))
    (Matrix.toLin' ((g⁻¹ : GL (Fin p) k) : Matrix _ _ k))
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.toLin'_one])

@[simp]
theorem glLinearEquiv_toLinearMap {p : ℕ} (g : GL (Fin p) k) :
    (glLinearEquiv g).toLinearMap = Matrix.toLin' (g : Matrix _ _ k) := rfl

/-- The element of `GLₚ(k)` attached to a linear automorphism of `kᵖ`, via its matrix
and the matrix of its inverse. -/
noncomputable def glOfLinearEquiv {p : ℕ} (e : (Fin p → k) ≃ₗ[k] (Fin p → k)) :
    GL (Fin p) k :=
  ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by
      rw [← LinearMap.toMatrix'_comp,
        show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from by ext x; simp,
        LinearMap.toMatrix'_id],
    by
      rw [← LinearMap.toMatrix'_comp,
        show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from by ext x; simp,
        LinearMap.toMatrix'_id]⟩

@[simp]
theorem glOfLinearEquiv_coe {p : ℕ} (e : (Fin p → k) ≃ₗ[k] (Fin p → k)) :
    (glOfLinearEquiv e : Matrix (Fin p) (Fin p) k) = LinearMap.toMatrix' e.toLinearMap := rfl

/-! ## Orbit ↔ isomorphism -/

/-- **The linchpin (Problem 6.1.5, step 1).** Two points of `W(m)` lie in the same
`G(m)`-orbit iff the represented quiver representations are isomorphic.

The base-change action `g j · M · (g i)⁻¹` is exactly the intertwining condition for an
isomorphism whose vertex equivalences are the `g i`. -/
theorem orbit_iff_isomorphic (m : Fin n → ℕ) (x y : repSpace (k := k) m) :
    (∃ g : repGroup k m, g • x = y) ↔
      (repOfPoint m x).AreIsomorphic (repOfPoint m y) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun i => glLinearEquiv (g i), ?_⟩
    intro a b f
    rw [repOfPoint_mapLinear, repOfPoint_mapLinear, glLinearEquiv_toLinearMap,
      glLinearEquiv_toLinearMap, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      repSpace_smul_apply]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
  · rintro ⟨e, he⟩
    -- Package the vertex equivalences `e i` into `GLₘᵢ(k)`; the intertwining condition
    -- `he` is exactly the base-change relation `g j · x · (g i)⁻¹ = y`.
    refine ⟨fun v => glOfLinearEquiv (e v), ?_⟩
    funext i j f
    -- Read the matrix identity `A j · x = y · A i` off `he` by applying `toMatrix'`.
    have key : LinearMap.toMatrix' (e j).toLinearMap * x i j f
        = y i j f * LinearMap.toMatrix' (e i).toLinearMap := by
      have h := he f
      apply_fun LinearMap.toMatrix' at h
      rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
        repOfPoint_mapLinear, repOfPoint_mapLinear, LinearMap.toMatrix'_toLin',
        LinearMap.toMatrix'_toLin'] at h
    rw [repSpace_smul_apply, glOfLinearEquiv_coe, key, ← glOfLinearEquiv_coe,
      Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]

end Etingof
