/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
import RepresentationTheory.MvPolynomial.Vanishing
import RepresentationTheory.LinearAlgebra.MatrixAction
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

set_option linter.dupNamespace false

namespace RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients

open scoped TensorProduct
open MvPolynomial
open RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.LinearAlgebra.MatrixAction

variable (k : Type) [Field k] (N n : ℕ)

namespace Auxiliary

/-- An auxiliary linear equivalence from the displayed space to functions from `Fin n → Fin
N` into the indicated tensor-product space. -/
noncomputable def tensorCoordinateLinearEquiv :
    Auxiliary k N n ≃ₗ[k] ((Fin n → Fin N) → auxiliarySpace k (AuxiliaryFactor k N) n) :=
  let bDual : Module.Basis (Fin n → Fin N) k
      (auxiliarySpace k (Module.Dual k (AuxiliaryFactor k N)) n) :=
    Basis.piTensorProduct (fun _ : Fin n => auxiliaryFactorDualBasis k N)
  LinearEquiv.lTensor _ bDual.equivFun ≪≫ₗ
    TensorProduct.piScalarRight k k _ (Fin n → Fin N)

end Auxiliary

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The linear map whose value in row `a` is the sum of each basis coordinate of a vector
multiplied by the polynomial in row `a` and the corresponding column. -/
noncomputable def polynomialCoordinateLinearMap {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k) (a : Fin d) :
    M →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  ∑ c : Fin d, LinearMap.smulRight (b.coord c) (P a c)

/-- The polynomial-coordinate linear map is the sum of the basis coordinates of its argument
multiplied by the corresponding row polynomials. -/
@[simp]
lemma polynomialCoordinateLinearMap_apply {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k) (a : Fin d) (x : M) :
    polynomialCoordinateLinearMap k N b P a x = ∑ c : Fin d, (b.coord c x) • P a c := by
  unfold polynomialCoordinateLinearMap
  rw [LinearMap.sum_apply]
  rfl

/-- If every polynomial entry has degree `n`, then every value of the polynomial-coordinate
linear map belongs to the degree-`n` homogeneous submodule. -/
lemma polynomialCoordinateLinearMap_mem_homogeneousSubmodule {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) (x : M) :
    polynomialCoordinateLinearMap k N b P a x ∈
      MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n := by
  rw [polynomialCoordinateLinearMap_apply]
  refine Submodule.sum_mem _ ?_
  intro c _
  exact Submodule.smul_mem _ _ (hhom a c)

/-- If evaluating each polynomial matrix coefficient gives the corresponding basis coordinate
of a linear map, then evaluating the associated polynomial-coordinate map gives that coordinate
on every vector. -/
lemma eval_polynomialCoordinateLinearMap_eq_coord {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (T : M →ₗ[k] M) (s : Fin N × Fin N → k)
    (hP : ∀ a c, b.coord a (T (b c)) = MvPolynomial.eval s (P a c))
    (a : Fin d) (x : M) :
    MvPolynomial.eval s (polynomialCoordinateLinearMap k N b P a x) = b.coord a (T x) := by
  classical
  rw [polynomialCoordinateLinearMap_apply, map_sum]
  have hx_repr : x = ∑ c : Fin d, b.coord c x • b c := by
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Module.Basis.coord_apply]
  conv_rhs => rw [hx_repr, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [MvPolynomial.smul_eval]
  rw [show T ((b.coord c) x • b c) = (b.coord c) x • T (b c) from
        T.map_smul _ _,
      show (b.coord a) ((b.coord c) x • T (b c)) =
             (b.coord c) x • (b.coord a) (T (b c)) from
        (b.coord a).map_smul _ _,
      smul_eq_mul, hP]

namespace Auxiliary

/-- For each basis index, an auxiliary linear map from the module to the displayed space
determined by homogeneous polynomial matrix entries. -/
noncomputable def tensorCoordinateLinearMap {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) :
    M →ₗ[k] Auxiliary k N n :=
  (homogeneousToAuxiliary k N n).comp <|
    LinearMap.codRestrict
      (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
      (polynomialCoordinateLinearMap k N b P a)
      (polynomialCoordinateLinearMap_mem_homogeneousSubmodule k N n b P hhom a)

/-- For each row and vector, the auxiliary tensor-coordinate map vanishes exactly when the
associated polynomial-coordinate map vanishes. -/
lemma tensorCoordinateLinearMap_eq_zero_iff {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) (x : M) :
    tensorCoordinateLinearMap k N n b P hhom a x = 0 ↔
      polynomialCoordinateLinearMap k N b P a x = 0 := by
  unfold tensorCoordinateLinearMap
  rw [LinearMap.comp_apply,
    show ((homogeneousToAuxiliary k N n)
            (LinearMap.codRestrict
              (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
              (polynomialCoordinateLinearMap k N b P a)
              (polynomialCoordinateLinearMap_mem_homogeneousSubmodule k N n b P hhom a) x) = 0) ↔
          (LinearMap.codRestrict
              (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
              (polynomialCoordinateLinearMap k N b P a)
              (polynomialCoordinateLinearMap_mem_homogeneousSubmodule k N n b P hhom a) x = 0) from
      ⟨fun h => (homogeneousToAuxiliary_injective k N n)
        (h.trans (map_zero _).symm),
       fun h => h ▸ map_zero _⟩]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg Subtype.val h
    simpa [LinearMap.codRestrict] using this
  · apply Subtype.ext
    simpa [LinearMap.codRestrict] using h

/-- An auxiliary linear map from a based module to a family indexed by a basis index and a
function from `Fin n` to `Fin N`, constructed from homogeneous polynomial entries. -/
noncomputable def tensorCoordinateFamilyLinearMap {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) :
    M →ₗ[k] (Fin d × (Fin n → Fin N) → auxiliarySpace k (AuxiliaryFactor k N) n) :=
  LinearMap.pi fun p =>
    ((LinearMap.proj p.2 :
        ((Fin n → Fin N) → auxiliarySpace k (AuxiliaryFactor k N) n) →ₗ[k]
        auxiliarySpace k (AuxiliaryFactor k N) n).comp
      ((tensorCoordinateLinearEquiv k N n).toLinearMap.comp
        (tensorCoordinateLinearMap k N n b P hhom p.1)))

/-- The auxiliary tensor-coordinate family map at a pair of indices is obtained by applying
the auxiliary linear equivalence to the corresponding component map. -/
lemma tensorCoordinateFamilyLinearMap_apply {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (x : M)
    (p : Fin d × (Fin n → Fin N)) :
    tensorCoordinateFamilyLinearMap k N n b P hhom x p =
      (tensorCoordinateLinearEquiv k N n) (tensorCoordinateLinearMap k N n b P hhom p.1 x) p.2 := by
  rfl

/-- Given the auxiliary predicate on a finite-dimensional action and homogeneous polynomial
formulas for its matrix coefficients, there is an injective linear map into a finite family of
the displayed spaces. -/
theorem exists_injective_tensorFamilyMap
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (_halg : HasAuxiliaryMapProperty N (ρ : _ → _))
    (hpoly : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c))) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n)),
      Function.Injective φ := by
  classical
  obtain ⟨d, b, P, hhom, hP⟩ := hpoly
  let m := Fintype.card (Fin d × (Fin n → Fin N))
  let e : Fin d × (Fin n → Fin N) ≃ Fin m := Fintype.equivFin _
  let reindex :
      (Fin d × (Fin n → Fin N) → auxiliarySpace k (AuxiliaryFactor k N) n) ≃ₗ[k]
        (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n) :=
    LinearEquiv.piCongrLeft k (fun _ : Fin m => auxiliarySpace k (AuxiliaryFactor k N) n) e
  let φ : M →ₗ[k] (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n) :=
    reindex.toLinearMap.comp (tensorCoordinateFamilyLinearMap k N n b P hhom)
  refine ⟨m, φ, ?_⟩
  rw [show Function.Injective φ ↔
      Function.Injective (tensorCoordinateFamilyLinearMap k N n b P hhom) from
    by simp [φ, LinearMap.coe_comp, reindex.injective.of_comp_iff]]
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx_pt : ∀ p : Fin d × (Fin n → Fin N),
      tensorCoordinateFamilyLinearMap k N n b P hhom x p = 0 :=
    fun p => congrFun hx p
  have hx_split : ∀ a : Fin d,
      (tensorCoordinateLinearEquiv k N n) (tensorCoordinateLinearMap k N n b P hhom a x) = 0 := by
    intro a
    funext j
    have := hx_pt (a, j)
    rw [tensorCoordinateFamilyLinearMap_apply] at this
    simpa using this
  have hx_row : ∀ a : Fin d, tensorCoordinateLinearMap k N n b P hhom a x = 0 :=
    fun a => (tensorCoordinateLinearEquiv k N n).map_eq_zero_iff.mp (hx_split a)
  have hx_poly : ∀ a : Fin d, polynomialCoordinateLinearMap k N b P a x = 0 :=
    fun a => (tensorCoordinateLinearMap_eq_zero_iff k N n b P hhom a x).mp (hx_row a)
  have hcoord_zero : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d),
      b.coord a (ρ g x) = 0 := by
    intro g a
    have hP_g : ∀ a' c', b.coord a' ((ρ g) (b c')) =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a' c') := by
      intro a' c'
      have h := hP g a' c'
      rwa [Module.Basis.coord_apply]
    have h := eval_polynomialCoordinateLinearMap_eq_coord k N b P (ρ g)
      (fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) hP_g a x
    rw [hx_poly a, map_zero] at h
    exact h.symm
  have hρ_zero : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ρ g x = 0 := by
    intro g
    apply b.repr.injective
    ext a
    rw [LinearEquiv.map_zero, Finsupp.zero_apply]
    have := hcoord_zero g a
    rwa [Module.Basis.coord_apply] at this
  have hone : ρ 1 = LinearMap.id := ρ.map_one
  have h := hρ_zero 1
  rw [hone, LinearMap.id_apply] at h
  exact h

/-- The auxiliary tensor-coordinate linear equivalence carries the auxiliary matrix action to
the pointwise tensor-product action induced by the matrix. -/
lemma tensorCoordinateLinearEquiv_map (g : Matrix (Fin N) (Fin N) k)
    (z : Auxiliary k N n) (j : Fin n → Fin N) :
    tensorCoordinateLinearEquiv k N n (secondFactorMatrixAction k N n g z) j =
      PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' g)
        (tensorCoordinateLinearEquiv k N n z j) := by
  classical
  suffices h :
      ((LinearMap.proj j :
          ((Fin n → Fin N) → auxiliarySpace k (AuxiliaryFactor k N) n) →ₗ[k]
              auxiliarySpace k (AuxiliaryFactor k N) n).comp
          (tensorCoordinateLinearEquiv k N n).toLinearMap).comp
        (secondFactorMatrixAction k N n g) =
        (PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' g)).comp
          ((LinearMap.proj j).comp (tensorCoordinateLinearEquiv k N n).toLinearMap) by
    have := congrArg (fun f => f z) h
    simpa using this
  apply TensorProduct.ext'
  intro u v
  simp only [LinearMap.comp_apply, tensorCoordinateLinearEquiv, secondFactorMatrixAction,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearEquiv.lTensor_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, LinearMap.proj_apply, map_smul]

/-- When the polynomial entries describe the matrix coefficients of an action and obey the
displayed transform identity, the polynomial-coordinate linear map intertwines that action with
the auxiliary polynomial transform. -/
lemma polynomialCoordinateLinearMap_equivariant {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      secondCoordinateMatrixAlgHom k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d) (x : M) :
    polynomialCoordinateLinearMap k N b P a (ρ g x) =
      secondCoordinateMatrixAlgHom k N
        (g : Matrix (Fin N) (Fin N) k) (polynomialCoordinateLinearMap k N b P a x) := by
  classical
  set eg : MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
    secondCoordinateMatrixAlgHom k N (g : Matrix (Fin N) (Fin N) k) with hegd
  set eval_g : MvPolynomial (Fin N × Fin N) k → k :=
    fun p => MvPolynomial.eval
      (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) p with hevalg
  have hrepr : ∀ c' : Fin d,
      b.coord c' (ρ g x) = ∑ c : Fin d, b.coord c x * eval_g (P c' c) := by
    intro c'
    have hx : x = ∑ c : Fin d, b.coord c x • b c := by
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Module.Basis.coord_apply]
    conv_lhs => rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [(ρ g).map_smul, (b.coord c').map_smul, smul_eq_mul]
    congr 1
    have := hP g c' c
    rwa [Module.Basis.coord_apply]
  have hLHS :
      polynomialCoordinateLinearMap k N b P a (ρ g x) =
        ∑ c : Fin d, b.coord c x • eg (P a c) := by
    rw [polynomialCoordinateLinearMap_apply]
    simp_rw [hrepr]
    have hswap :
        (∑ c' : Fin d, (∑ c : Fin d, b.coord c x * eval_g (P c' c)) • P a c') =
          (∑ c : Fin d, b.coord c x • (∑ c' : Fin d, eval_g (P c' c) • P a c')) := by
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← smul_smul, ← mul_smul, mul_comm]
    rw [hswap]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [hP_mul g a c]
  have hRHS : eg (polynomialCoordinateLinearMap k N b P a x) =
      ∑ c : Fin d, b.coord c x • eg (P a c) := by
    rw [polynomialCoordinateLinearMap_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]
  rw [hLHS, hRHS]

/-- Under the displayed matrix-coefficient and transform identities, each auxiliary
tensor-coordinate map intertwines the given action with the auxiliary matrix action on its
codomain. -/
lemma tensorCoordinateLinearMap_equivariant [CharZero k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      secondCoordinateMatrixAlgHom k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d) (x : M) :
    tensorCoordinateLinearMap k N n b P hhom a (ρ g x) =
      secondFactorMatrixAction k N n (g : Matrix (Fin N) (Fin N) k)
        (tensorCoordinateLinearMap k N n b P hhom a x) := by
  unfold tensorCoordinateLinearMap
  simp only [LinearMap.comp_apply]
  have hmc := polynomialCoordinateLinearMap_equivariant k N b P ρ hP hP_mul g a x
  have heq :
      (LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
          (polynomialCoordinateLinearMap k N b P a)
          (polynomialCoordinateLinearMap_mem_homogeneousSubmodule k N n b P hhom a)) (ρ g x) =
      ⟨secondCoordinateMatrixAlgHom k N (g : Matrix (Fin N) (Fin N) k)
          ((LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
            (polynomialCoordinateLinearMap k N b P a)
            (polynomialCoordinateLinearMap_mem_homogeneousSubmodule k N n b P hhom a)) x).val,
       secondCoordinateMatrixAlgHom_isHomogeneous (k := k) (N := N) (m := n)
         (g : Matrix (Fin N) (Fin N) k)
         ((LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
            (polynomialCoordinateLinearMap k N b P a)
            (polynomialCoordinateLinearMap_mem_homogeneousSubmodule
              k N n b P hhom a)) x).property⟩ := by
    apply Subtype.ext
    simpa [LinearMap.codRestrict] using hmc
  rw [heq,
    homogeneousToAuxiliary_commutes (k := k) (N := N) (n := n)
      (g := (g : Matrix (Fin N) (Fin N) k))]

/-- Under the displayed matrix-coefficient and transform identities, the auxiliary
tensor-coordinate family map intertwines the given general linear group action with the
pointwise tensor-product action. -/
lemma tensorCoordinateFamilyLinearMap_equivariant [CharZero k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      secondCoordinateMatrixAlgHom k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M)
    (p : Fin d × (Fin n → Fin N)) :
    tensorCoordinateFamilyLinearMap k N n b P hhom (ρ g x) p =
      PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
        (tensorCoordinateFamilyLinearMap k N n b P hhom x p) := by
  rw [tensorCoordinateFamilyLinearMap_apply, tensorCoordinateFamilyLinearMap_apply,
    tensorCoordinateLinearMap_equivariant (k := k) (N := N) (n := n) b P hhom ρ hP hP_mul g p.1 x,
    tensorCoordinateLinearEquiv_map k N n (g : Matrix (Fin N) (Fin N) k)
      (tensorCoordinateLinearMap k N n b P hhom p.1 x) p.2]

/-- Given the auxiliary predicate on a finite-dimensional action and homogeneous polynomial
matrix coefficients satisfying both displayed covariance identities, there is an injective
linear map into a finite family of tensor-power spaces that intertwines the actions. -/
theorem exists_injective_equivariant_tensorFamilyMap_of_covariant_coefficients
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (_halg : HasAuxiliaryMapProperty N (ρ : _ → _))
    (hpoly : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c)) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
           secondCoordinateMatrixAlgHom k N
               (g : Matrix (Fin N) (Fin N) k) (P a c') =
             ∑ c, MvPolynomial.eval
                    (fun ij : Fin N × Fin N =>
                      (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
                    (P c c') • P a c)) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n)),
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M) (i : Fin m),
        φ (ρ g x) i =
          PiTensorProduct.map
            (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
            (φ x i)) := by
  classical
  obtain ⟨d, b, P, hhom, hP, hP_mul⟩ := hpoly
  let m := Fintype.card (Fin d × (Fin n → Fin N))
  let e : Fin d × (Fin n → Fin N) ≃ Fin m := Fintype.equivFin _
  let reindex :
      (Fin d × (Fin n → Fin N) → auxiliarySpace k (AuxiliaryFactor k N) n) ≃ₗ[k]
        (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n) :=
    LinearEquiv.funCongrLeft k (auxiliarySpace k (AuxiliaryFactor k N) n) e.symm
  let φ : M →ₗ[k] (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n) :=
    reindex.toLinearMap.comp (tensorCoordinateFamilyLinearMap k N n b P hhom)
  refine ⟨m, φ, ?_, ?_⟩
  · rw [show Function.Injective φ ↔
          Function.Injective (tensorCoordinateFamilyLinearMap k N n b P hhom) from by
      simp [φ, LinearMap.coe_comp, reindex.injective.of_comp_iff]]
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx_pt : ∀ p : Fin d × (Fin n → Fin N),
        tensorCoordinateFamilyLinearMap k N n b P hhom x p = 0 :=
      fun p => congrFun hx p
    have hx_split : ∀ a : Fin d,
        (tensorCoordinateLinearEquiv k N n) (tensorCoordinateLinearMap k N n b P hhom a x) = 0 := by
      intro a
      funext j
      have := hx_pt (a, j)
      rw [tensorCoordinateFamilyLinearMap_apply] at this
      simpa using this
    have hx_row : ∀ a : Fin d, tensorCoordinateLinearMap k N n b P hhom a x = 0 :=
      fun a => (tensorCoordinateLinearEquiv k N n).map_eq_zero_iff.mp (hx_split a)
    have hx_poly : ∀ a : Fin d, polynomialCoordinateLinearMap k N b P a x = 0 :=
      fun a => (tensorCoordinateLinearMap_eq_zero_iff k N n b P hhom a x).mp (hx_row a)
    have hcoord_zero : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d),
        b.coord a (ρ g x) = 0 := by
      intro g a
      have hP_g : ∀ a' c', b.coord a' ((ρ g) (b c')) =
          MvPolynomial.eval
            (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
            (P a' c') := by
        intro a' c'
        have h := hP g a' c'
        rwa [Module.Basis.coord_apply]
      have h := eval_polynomialCoordinateLinearMap_eq_coord k N b P (ρ g)
        (fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) hP_g a x
      rw [hx_poly a, map_zero] at h
      exact h.symm
    have hρ_zero : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ρ g x = 0 := by
      intro g
      apply b.repr.injective
      ext a
      rw [LinearEquiv.map_zero, Finsupp.zero_apply]
      have := hcoord_zero g a
      rwa [Module.Basis.coord_apply] at this
    have hone : ρ 1 = LinearMap.id := ρ.map_one
    have h := hρ_zero 1
    rw [hone, LinearMap.id_apply] at h
    exact h
  · intro g x i
    change tensorCoordinateFamilyLinearMap k N n b P hhom (ρ g x) (e.symm i) =
      PiTensorProduct.map (fun _ => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
        (tensorCoordinateFamilyLinearMap k N n b P hhom x (e.symm i))
    exact tensorCoordinateFamilyLinearMap_equivariant
      (k := k) (N := N) (n := n) b P hhom ρ hP hP_mul
      g x (e.symm i)

open RepresentationTheory.LinearAlgebra.MatrixAction

variable (k : Type) [Field k] (N : ℕ)

/-- Evaluating the auxiliary transform of a multivariate polynomial at a matrix agrees with
evaluating the original polynomial at the corresponding matrix product. -/
lemma eval_polynomialTransform
    (g h : Matrix (Fin N) (Fin N) k) (p : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.eval (fun ij : Fin N × Fin N => h ij.1 ij.2)
        (secondCoordinateMatrixAlgHom k N g p) =
      MvPolynomial.eval (fun ij : Fin N × Fin N => (h * g) ij.1 ij.2) p := by
  classical
  suffices halgs :
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => h ij.1 ij.2)).comp
        (secondCoordinateMatrixAlgHom k N g) =
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => (h * g) ij.1 ij.2) :
        MvPolynomial (Fin N × Fin N) k →ₐ[k] k) by
    have := AlgHom.congr_fun halgs p
    simpa [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using this
  apply MvPolynomial.algHom_ext
  intro ij
  rw [AlgHom.comp_apply, secondCoordinateMatrixAlgHom_X, map_sum,
    MvPolynomial.aeval_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Algebra.algebraMap_self_apply]

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- Polynomial matrix coefficients of a general linear group action satisfy the displayed
transformation formula under the auxiliary polynomial transform. -/
lemma polynomialTransform_matrixCoefficient [Infinite k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c))
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a c' : Fin d) :
    secondCoordinateMatrixAlgHom k N
        (g : Matrix (Fin N) (Fin N) k) (P a c') =
      ∑ c, MvPolynomial.eval
             (fun ij : Fin N × Fin N =>
               (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
             (P c c') • P a c := by
  classical
  have hP_coord : ∀ (e : Matrix.GeneralLinearGroup (Fin N) k) (a c : Fin d),
      MvPolynomial.eval
          (fun ij : Fin N × Fin N => (e : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c) = b.coord a (ρ e (b c)) :=
    fun e a c => by rw [← hP e a c, Module.Basis.coord_apply]
  apply MvPolynomial.eq_of_eval_eq_on_gl
  intro h
  rw [eval_polynomialTransform k N (g : Matrix (Fin N) (Fin N) k)
       (h : Matrix (Fin N) (Fin N) k) (P a c'), map_sum]
  simp only [MvPolynomial.smul_eval]
  have hLHS : MvPolynomial.eval
                (fun ij : Fin N × Fin N =>
                  ((h : Matrix (Fin N) (Fin N) k) * (g : Matrix (Fin N) (Fin N) k))
                    ij.1 ij.2) (P a c') =
              b.coord a (ρ h (ρ g (b c'))) := by
    have hPhg := hP_coord (h * g) a c'
    rwa [ρ.map_mul, Module.End.mul_apply] at hPhg
  rw [hLHS]
  simp_rw [hP_coord]
  conv_lhs =>
    rw [show ρ g (b c') = ∑ c : Fin d, b.coord c (ρ g (b c')) • b c from by
      simp_rw [Module.Basis.coord_apply]; exact (b.sum_repr _).symm]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(ρ h).map_smul, (b.coord a).map_smul, smul_eq_mul]

/-- Given the auxiliary predicate on a finite-dimensional action and homogeneous polynomial
formulas for its matrix coefficients, there is an injective equivariant linear map into a finite
family of tensor-power spaces. -/
theorem exists_injective_equivariant_tensorFamilyMap (n : ℕ)
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (halg : HasAuxiliaryMapProperty N (ρ : _ → _))
    (hpoly' : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c))) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n)),
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M) (i : Fin m),
        φ (ρ g x) i =
          PiTensorProduct.map
            (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
            (φ x i)) := by
  obtain ⟨d, b, P, hhom, hP⟩ := hpoly'
  exact exists_injective_equivariant_tensorFamilyMap_of_covariant_coefficients k N n ρ halg
    ⟨d, b, P, hhom, hP,
      fun g a c' => polynomialTransform_matrixCoefficient k N b P ρ hP g a c'⟩

/-- An auxiliary map from units of the field to the general linear group indexed by `Fin N`. -/
noncomputable def unitToGeneralLinearGroup (t : kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal fun _ => (t : k)
  inv := Matrix.diagonal fun _ => ((t⁻¹ : kˣ) : k)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv]
    exact Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.inv_mul]
    exact Matrix.diagonal_one

private lemma unitToGeneralLinearGroup_eq_noncommProd (t : kˣ) :
    unitToGeneralLinearGroup k N t
      = Finset.univ.noncommProd (fun i => diagonalUnit k N i t)
          (fun i _ j _ _ => diagonalUnit_comm k N i t j t) := by
  apply Units.ext
  have gen : ∀ (s : Finset (Fin N))
      (comm : (↑s : Set (Fin N)).Pairwise
        fun a b => Commute (diagonalUnit k N a t) (diagonalUnit k N b t)),
      (s.noncommProd (fun i => diagonalUnit k N i t) comm).val
        = Matrix.diagonal (fun j => if j ∈ s then (t : k) else 1) := by
    intro s
    induction s using Finset.induction with
    | empty => intro comm; simp [Matrix.diagonal_one]
    | @insert a s ha ih =>
        intro comm
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Units.val_mul, ih]
        change Matrix.diagonal (Function.update (1 : Fin N → k) a (t : k))
            * Matrix.diagonal (fun j => if j ∈ s then (t : k) else 1)
            = Matrix.diagonal (fun j => if j ∈ insert a s then (t : k) else 1)
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hja : j = a
        · subst hja; simp [Function.update_self, ha]
        · rw [Function.update_of_ne hja]; simp [Finset.mem_insert, hja]
  rw [gen Finset.univ]
  change Matrix.diagonal (fun _ => (t : k))
      = Matrix.diagonal (fun j => if j ∈ (Finset.univ : Finset (Fin N)) then (t : k) else 1)
  simp

private theorem unitToGeneralLinearGroup_acts_as_pow (n : ℕ)
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (_halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n)
    (t : kˣ) :
    M.ρ (unitToGeneralLinearGroup k N t) = ((t : k) ^ n) • LinearMap.id := by
  rw [← sub_eq_zero]
  set L : M →ₗ[k] M :=
    M.ρ (unitToGeneralLinearGroup k N t) - ((t : k) ^ n) • LinearMap.id with hL
  have hker :
      (⨆ μ : Fin N →₀ ℕ, weightSpace k N M (fun i => μ i)) ≤ LinearMap.ker L := by
    rw [iSup_le_iff]
    intro μ w hw
    rw [LinearMap.mem_ker]
    by_cases hw0 : w = 0
    · simp [hw0]
    · have heig : ∀ i : Fin N,
          M.ρ (diagonalUnit k N i t) w = ((t : k) ^ μ i) • w := by
        intro i
        have hmem : w ∈ weightSpace k N M (fun j => μ j) := hw
        rw [weightSpace, Submodule.mem_iInf] at hmem
        have h2 := (Submodule.mem_iInf _).1 (hmem i) t
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
          LinearMap.smul_apply, LinearMap.id_apply] at h2
        exact h2
      have act : ∀ (s : Finset (Fin N))
          (comm : (↑s : Set (Fin N)).Pairwise
            fun a b => Commute (M.ρ (diagonalUnit k N a t)) (M.ρ (diagonalUnit k N b t))),
          (s.noncommProd (fun i => M.ρ (diagonalUnit k N i t)) comm) w
            = (∏ i ∈ s, (t : k) ^ μ i) • w := by
        intro s
        induction s using Finset.induction with
        | empty => intro comm; simp
        | @insert a s ha ih =>
            intro comm
            rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Module.End.mul_apply, ih,
              Finset.prod_insert ha, map_smul, heig a, smul_smul, mul_comm]
      have hprod : M.ρ (unitToGeneralLinearGroup k N t) w = ((t : k) ^ (∑ i, μ i)) • w := by
        rw [unitToGeneralLinearGroup_eq_noncommProd, Finset.map_noncommProd, act Finset.univ,
          Finset.prod_pow_eq_pow_sum]
      have hne : weightSpace k N M (fun i => μ i) ≠ ⊥ := by
        intro h; exact hw0 ((Submodule.mem_bot k).1 (h ▸ hw))
      have hsum : ∑ i, μ i = n := h_homog (fun i => μ i) hne
      rw [hL, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hprod, hsum,
        sub_self]
  rw [h_span, top_le_iff, LinearMap.ker_eq_top] at hker
  exact hker

private lemma eval_mul_pow_of_isHomogeneous {i : ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p.IsHomogeneous i)
    (c : k) (x : Fin N × Fin N → k) :
    MvPolynomial.eval (fun s => c * x s) p = c ^ i * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPolynomial.mem_support_iff] at hd
  have hdeg : d.degree = i := by by_contra h; exact hd (hp.coeff_eq_zero h)
  have hsum : (∑ s ∈ d.support, d s) = i := by rw [← hdeg]; rfl
  rw [Finset.prod_congr rfl (fun s _ => mul_pow c (x s) (d s)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hsum]
  ring

private lemma isHomogeneous_of_gl_scaling [Infinite k] {n : ℕ}
    (Q : MvPolynomial (Fin N × Fin N) k)
    (hsc : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (t : kˣ),
       MvPolynomial.eval (fun ij : Fin N × Fin N =>
           (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q
       = (t : k) ^ n *
         MvPolynomial.eval (fun ij : Fin N × Fin N =>
           (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q) :
    Q.IsHomogeneous n := by
  classical
  have key : ∀ i, i ≠ n → MvPolynomial.homogeneousComponent i Q = 0 := by
    intro i hi
    apply MvPolynomial.eq_of_eval_eq_on_gl
    intro g
    rw [map_zero]
    set G : Fin N × Fin N → k :=
      fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2 with hG
    set td := Q.totalDegree with htd
    set c : ℕ → k :=
      fun e => MvPolynomial.eval G (MvPolynomial.homogeneousComponent e Q) with hc
    have hsum_id : ∀ t : k, MvPolynomial.eval (fun ij => t * G ij) Q
        = ∑ e ∈ Finset.range (td+1), c e * t^e := by
      intro t
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [eval_mul_pow_of_isHomogeneous k N
        (MvPolynomial.homogeneousComponent_isHomogeneous e Q) t G]
      rw [hc]; ring
    by_cases hile : i ≤ td
    · set P : Polynomial k :=
        (∑ e ∈ Finset.range (td+1), Polynomial.C (c e) * Polynomial.X ^ e)
          - Polynomial.C (MvPolynomial.eval G Q) * Polynomial.X ^ n with hP
      have hroot : ∀ t : k, t ≠ 0 → P.IsRoot t := by
        intro t ht
        have hu : MvPolynomial.eval (fun ij => ((Units.mk0 t ht : kˣ):k) * G ij) Q
            = ((Units.mk0 t ht : kˣ):k)^n * MvPolynomial.eval G Q := hsc g (Units.mk0 t ht)
        simp only [Units.val_mk0] at hu
        have key2 : (∑ e ∈ Finset.range (td+1), c e * t^e) = t^n * MvPolynomial.eval G Q := by
          rw [← hsum_id t]; exact hu
        rw [Polynomial.IsRoot.def, hP]
        simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [key2]; ring
      have hinf : Set.Infinite {t : k | P.IsRoot t} := by
        apply Set.Infinite.mono _ ((Set.finite_singleton (0:k)).infinite_compl)
        intro t ht
        exact hroot t (by simpa using ht)
      have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinf
      have hcoeff : P.coeff i = c i := by
        rw [hP]
        simp only [Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq (Finset.range (td+1)) i (fun e => c e)]
        simp only [Finset.mem_range, Nat.lt_succ_iff, hile, if_true]
        rw [if_neg hi]
        ring
      rw [hP0] at hcoeff
      simpa [hc] using hcoeff.symm
    · rw [show MvPolynomial.homogeneousComponent i Q = 0 from
          MvPolynomial.homogeneousComponent_eq_zero (φ := Q) (n := i) (by omega), map_zero]
  have hQeq : Q = MvPolynomial.homogeneousComponent n Q := by
    ext d
    rw [MvPolynomial.coeff_homogeneousComponent]
    by_cases hd : d.degree = n
    · rw [if_pos hd]
    · rw [if_neg hd]
      have h0 := key d.degree hd
      have h2 : MvPolynomial.coeff d (MvPolynomial.homogeneousComponent d.degree Q)
          = MvPolynomial.coeff d Q := by
        rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl]
      rw [h0, MvPolynomial.coeff_zero] at h2
      exact h2.symm
  rw [hQeq]
  exact MvPolynomial.homogeneousComponent_isHomogeneous n Q

private theorem exists_polynomial_matrixCoefficients_of_auxiliarySpan
    (n : ℕ) [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (Q a c) := by
  exact exists_basis_with_polynomial_matrix_coefficients n M halg h_span

private theorem polynomialMatrixCoefficient_isHomogeneous (n : ℕ) [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_scalar : ∀ t : kˣ, M.ρ (unitToGeneralLinearGroup k N t) = ((t : k) ^ n) • LinearMap.id)
    {d : ℕ} (b : Module.Basis (Fin d) k M)
    (Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hQ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (Q a c))
    (a c : Fin d) : (Q a c).IsHomogeneous n := by
  apply isHomogeneous_of_gl_scaling
  intro g t
  have hmatrix : ∀ ij : Fin N × Fin N,
      ((unitToGeneralLinearGroup k N t * g : Matrix.GeneralLinearGroup (Fin N) k) :
          Matrix (Fin N) (Fin N) k) ij.1 ij.2
        = (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2 := by
    intro ij
    change ((unitToGeneralLinearGroup k N t : Matrix (Fin N) (Fin N) k) *
        (g : Matrix (Fin N) (Fin N) k)) ij.1 ij.2 = _
    rw [show (unitToGeneralLinearGroup k N t : Matrix (Fin N) (Fin N) k)
          = Matrix.diagonal (fun _ => (t : k)) from rfl, Matrix.diagonal_mul]
  have hpt : (fun ij : Fin N × Fin N => (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
      = (fun ij : Fin N × Fin N =>
          ((unitToGeneralLinearGroup k N t * g : Matrix.GeneralLinearGroup (Fin N) k) :
            Matrix (Fin N) (Fin N) k) ij.1 ij.2) := by
    funext ij; exact (hmatrix ij).symm
  have hL : MvPolynomial.eval (fun ij : Fin N × Fin N =>
        (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) (Q a c)
      = b.repr (M.ρ (unitToGeneralLinearGroup k N t * g) (b c)) a := by
    rw [hpt]; exact (hQ (unitToGeneralLinearGroup k N t * g) a c).symm
  rw [hL, map_mul, h_scalar t, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, hQ g a c]

private theorem exists_homogeneous_matrixCoefficients_of_unitAction (n : ℕ)
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h_scalar : ∀ t : kˣ,
      M.ρ (unitToGeneralLinearGroup k N t) = ((t : k) ^ n) • LinearMap.id) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c)) := by
  obtain ⟨d, b, Q, hQ⟩ :=
    exists_polynomial_matrixCoefficients_of_auxiliarySpan k N n M halg h_span
  exact ⟨d, b, Q,
    fun a c => polynomialMatrixCoefficient_isHomogeneous k N n M h_scalar b Q hQ a c, hQ⟩

/-- If the displayed auxiliary submodules span a representation and every nonzero indexed
submodule has total index `n`, then some basis has degree-`n` homogeneous polynomial formulas
for all action matrix coefficients. -/
theorem exists_homogeneous_matrixCoefficients_of_auxiliarySubmodules
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c)) :=
  exists_homogeneous_matrixCoefficients_of_unitAction k N n M halg h_span
    (fun t => unitToGeneralLinearGroup_acts_as_pow k N n M halg h_span h_homog t)

/-- Under the auxiliary action predicate and the stated spanning and fixed-total-index
conditions, there is an injective equivariant linear map from the representation into a finite
family of tensor-power spaces. -/
theorem exists_injective_equivariant_tensorFamilyMap_of_auxiliarySubmodules
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → auxiliarySpace k (AuxiliaryFactor k N) n)),
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M) (i : Fin m),
        φ (M.ρ g x) i =
          PiTensorProduct.map
            (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
            (φ x i)) := by
  obtain ⟨d, b, P, hhom, hP⟩ :=
    exists_homogeneous_matrixCoefficients_of_auxiliarySubmodules
      (k := k) (N := N) n M halg h_span h_homog
  exact exists_injective_equivariant_tensorFamilyMap k N n M.ρ halg ⟨d, b, P, hhom, hP⟩

end Auxiliary

end RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients
