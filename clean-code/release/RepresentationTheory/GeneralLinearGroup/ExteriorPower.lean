/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryCharacter
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
import RepresentationTheory.MvPolynomial.UniformIndexShift
import RepresentationTheory.GeneralLinear.AuxiliaryDecomposition
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.Alignment.Attribute

open CategoryTheory MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace RepresentationTheory.GeneralLinearGroup.ExteriorPower

open RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.GeneralLinear.AuxiliaryDecomposition
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.MvPolynomial.UniformIndexShift
open RepresentationTheory.SymmetricPolynomials.Alternant

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- The additive commutative group structure on the auxiliary membership subtype. -/
noncomputable local instance (priority := high) auxiliarySubtypeAddCommGroup
    (N : ℕ) (lam : Fin N → ℕ) : AddCommGroup (schurSubmodule k N lam) :=
  { Module.addCommMonoidToAddCommGroup k with
    toAddCommMonoid := (schurSubmodule k N lam).addCommMonoid }

/-- An auxiliary finite-dimensional representation of the general linear group. -/
noncomputable def auxiliaryFiniteDimensionalRepresentation (N : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  FDRep.of (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
    Matrix.GeneralLinearGroup.det)

/-- The representation of the general linear group on the specified exterior-power subtype. -/
def exteriorPowerRepresentation (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k) (⋀[k]^N (Fin N → k)) where
  toFun g := exteriorPower.map N (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) k))
  map_one' := by
    simp only [Units.val_one, Matrix.mulVecLin_one, exteriorPower.map_id]
    rfl
  map_mul' g h := by
    simp only [Units.val_mul, Matrix.mulVecLin_mul, exteriorPower.map_comp]
    rfl

/-- A second auxiliary finite-dimensional representation of the general linear group. -/
noncomputable def auxiliaryFiniteDimensionalRepresentationPrime (N : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  FDRep.of (exteriorPowerRepresentation k N)

omit [IsAlgClosed k] [CharZero k] in
private lemma exteriorPowerAlternatingMap_map_mulVecLin (N : ℕ) (A : Matrix (Fin N) (Fin N) k)
    (x : ⋀[k]^N (Fin N → k)) :
    exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det
        (exteriorPower.map N (Matrix.mulVecLin A) x) =
      A.det • exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det x := by
  set b := Pi.basisFun k (Fin N) with hb
  have hdetlin : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [show Matrix.mulVecLin A = Matrix.toLin' A from (Matrix.toLin'_apply' A).symm,
      LinearMap.det_toLin']
  have key : (exteriorPower.alternatingMapLinearEquiv (n := N) b.det) ∘ₗ
      exteriorPower.map N (Matrix.mulVecLin A) =
      A.det • (exteriorPower.alternatingMapLinearEquiv (n := N) b.det) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, LinearMap.smul_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [b.det_comp, hdetlin, smul_eq_mul]
  exact LinearMap.congr_fun key x

/-- A linear equivalence from the specified exterior-power subtype to the base field. -/
noncomputable def exteriorPowerLinearEquiv (N : ℕ) : (⋀[k]^N (Fin N → k)) ≃ₗ[k] k := by
  have hω : exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det
      (exteriorPower.ιMulti k N (⇑(Pi.basisFun k (Fin N)))) = 1 := by
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact (Pi.basisFun k (Fin N)).det_self
  have hsurj : Function.Surjective
      (exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det) := by
    intro c
    refine ⟨c • exteriorPower.ιMulti k N (⇑(Pi.basisFun k (Fin N))), ?_⟩
    rw [map_smul, hω, smul_eq_mul, mul_one]
  have hdim : Module.finrank k (⋀[k]^N (Fin N → k)) = Module.finrank k k := by
    rw [exteriorPower.finrank_eq, Module.finrank_fin_fun, Module.finrank_self, Nat.choose_self]
  exact LinearEquiv.ofBijective _
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩

omit [CharZero k] in
/-- The exterior-power linear equivalence evaluates through the alternating map associated with
the standard basis determinant. -/
@[simp]
lemma exteriorPowerLinearEquiv_apply (N : ℕ) (x : ⋀[k]^N (Fin N → k)) :
    exteriorPowerLinearEquiv k N x =
      exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det x := rfl

omit [CharZero k] in
/-- The exterior-power representation acts by scalar multiplication by the determinant. -/
@[source_ref"Chapter5/Proposition5.22.2"(role:=primary)]
lemma exteriorPowerRepresentation_apply (N : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    exteriorPowerRepresentation k N g =
      (↑(Matrix.GeneralLinearGroup.det g) : k) • LinearMap.id := by
  refine LinearMap.ext fun x => (exteriorPowerLinearEquiv k N).injective ?_
  simp only [exteriorPowerLinearEquiv_apply, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq, map_smul]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact exteriorPowerAlternatingMap_map_mulVecLin k N _ x

omit [CharZero k] in
/-- The exterior-power linear equivalence intertwines the exterior-power action with
multiplication by the determinant. -/
theorem exteriorPowerLinearEquiv_intertwines (N : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    (exteriorPowerLinearEquiv k N).toLinearMap ∘ₗ (exteriorPowerRepresentation k N g) =
      ((((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
        Matrix.GeneralLinearGroup.det) g) ∘ₗ (exteriorPowerLinearEquiv k N).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have hL : exteriorPowerLinearEquiv k N (exteriorPowerRepresentation k N g x) =
      (g : Matrix (Fin N) (Fin N) k).det • exteriorPowerLinearEquiv k N x := by
    rw [exteriorPowerLinearEquiv_apply, exteriorPowerLinearEquiv_apply]
    exact exteriorPowerAlternatingMap_map_mulVecLin k N _ x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hL]
  -- RHS is `Algebra.lsmul k k k ↑(det g) (exteriorPowerLinearEquiv x) =
  -- ↑(det g) • exteriorPowerLinearEquiv x`
  -- definitionally; convert and match scalars via `val_det_apply`.
  change (g : Matrix (Fin N) (Fin N) k).det • exteriorPowerLinearEquiv k N x
    = (↑(Matrix.GeneralLinearGroup.det g) : k) • exteriorPowerLinearEquiv k N x
  rw [Matrix.GeneralLinearGroup.val_det_apply]

/-- An isomorphism between the two auxiliary finite-dimensional representations. -/
@[source_ref"Chapter5/Proposition5.22.2"(role:=primary)]
noncomputable def auxiliaryFiniteDimensionalRepresentationsIso (N : ℕ) :
    auxiliaryFiniteDimensionalRepresentationPrime k N ≅
      auxiliaryFiniteDimensionalRepresentation k N :=
  Action.mkIso (exteriorPowerLinearEquiv k N).toFGModuleCatIso (fun g => by
    ext : 1
    exact exteriorPowerLinearEquiv_intertwines k N g)

set_option synthInstance.maxHeartbeats 80000 in
-- Slower instance search needs a larger synthesis budget for the `det • End` smul synthesis.
/-- An auxiliary representation on a subtype defined by membership in an indexed collection. -/
def auxiliarySubtypeRepresentation (N : ℕ) (lam : Fin N → ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (schurSubmodule k N lam) where
  toFun g := (Matrix.GeneralLinearGroup.det g : k) • schurSubmoduleRepresentation k N lam g
  map_one' := by simp [map_one]
  map_mul' g₁ g₂ := by
    have hdet : (Matrix.GeneralLinearGroup.det (g₁ * g₂) : k) =
      (Matrix.GeneralLinearGroup.det g₁ : k) * (Matrix.GeneralLinearGroup.det g₂ : k) := by
      simp [map_mul]
    have hmul : (schurSubmoduleRepresentation k N lam) (g₁ * g₂) =
        (schurSubmoduleRepresentation k N lam) g₁ *
          (schurSubmoduleRepresentation k N lam) g₂ := map_mul _ _ _
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, hdet, hmul]
    rw [mul_smul]
    simp only [map_smul, Submodule.coe_smul_of_tower]

/-- Incrementing every index multiplies the auxiliary polynomial by the product of the polynomial
variables. -/
theorem auxiliaryPolynomial_shift_eq_mul (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    weightCharacter k N (schurRepresentation k N (fun i => lam i + 1)) =
      (∏ i : Fin N, MvPolynomial.X i) * weightCharacter k N (schurRepresentation k N lam) := by
  have hlam' : Antitone (fun i => lam i + 1) := fun i j hij => Nat.add_le_add_right (hlam hij) 1
  rw [weightCharacter_schurRepresentation_eq k N _ hlam',
    weightCharacter_schurRepresentation_eq k N lam hlam, auxiliary_eq_prod_variables_mul]

omit [IsAlgClosed k] [CharZero k] in
private lemma det_diagonalUnit (N : ℕ) (i : Fin N) (t : kˣ) :
    Matrix.GeneralLinearGroup.det (diagonalUnit k N i t) = t := by
  ext
  change Matrix.det (diagonalUnit k N i t).val = (t : k)
  simp only [diagonalUnit, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i),
    Pi.one_apply]
  simp [Finset.prod_eq_one (fun j _ => rfl)]

omit [IsAlgClosed k] [CharZero k] in
private lemma det_diagonalUnit_val (N : ℕ) (i : Fin N) (t : kˣ) :
    (Matrix.GeneralLinearGroup.det (diagonalUnit k N i t) : k) = (t : k) :=
  congr_arg Units.val (det_diagonalUnit k N i t)

set_option linter.style.setOption false in
omit [CharZero k] in
/-- The auxiliary invariant of the subtype representation with shifted parameter agrees with that
of the corresponding finite-dimensional representation. -/
lemma auxiliaryInvariant_ofSubtypeRepresentation_shift
    (N : ℕ) (lam : Fin N → ℕ) (μ : Fin N → ℕ) :
    weightSpace k N (FDRep.of (auxiliarySubtypeRepresentation k N lam)) (fun j => μ j + 1) =
      weightSpace k N (schurRepresentation k N lam) μ :=
    set_option maxHeartbeats 800000 in
    set_option synthInstance.maxHeartbeats 80000 in by
  -- The initial `simp only [weightSpace, ...]` unfold is expensive.
  -- Slower instance search needs a larger synthesis budget for the `t • End` smul synthesis.
  -- Unfold definitions to iInf over kernels
  simp only [weightSpace, schurRepresentation, FDRep.of_ρ']
  -- detTwisted(g) = t • orig(g), so the linear maps factor:
  -- detTwisted(g) - t^(μ+1)•id = t•(orig(g) - t^μ•id)
  -- Hence ker(detTwisted(g) - t^(μ+1)•id) = ker(orig(g) - t^μ•id)
  apply iInf_congr; intro i; apply iInf_congr; intro t
  have hdt : (auxiliarySubtypeRepresentation k N lam (diagonalUnit k N i t)) =
      (t : k) • (schurSubmoduleRepresentation k N lam (diagonalUnit k N i t)) := by
    change (Matrix.GeneralLinearGroup.det (diagonalUnit k N i t) : k) •
      (schurSubmoduleRepresentation k N lam) (diagonalUnit k N i t) = _
    rw [det_diagonalUnit_val]
  have factored : (auxiliarySubtypeRepresentation k N lam (diagonalUnit k N i t)) -
      ((↑t : k) ^ (μ i + 1)) • LinearMap.id =
    (↑t : k) • ((schurSubmoduleRepresentation k N lam (diagonalUnit k N i t)) -
      ((↑t : k) ^ μ i) • LinearMap.id) := by
    rw [hdt, smul_sub, pow_succ, mul_comm, mul_smul]
  calc LinearMap.ker ((auxiliarySubtypeRepresentation k N lam (diagonalUnit k N i t)) -
        ((↑t : k) ^ (μ i + 1)) • LinearMap.id)
      = LinearMap.ker ((↑t : k) •
          ((schurSubmoduleRepresentation k N lam (diagonalUnit k N i t)) -
          ((↑t : k) ^ μ i) • LinearMap.id)) := congr_arg LinearMap.ker factored
    _ = LinearMap.ker ((schurSubmoduleRepresentation k N lam (diagonalUnit k N i t)) -
          ((↑t : k) ^ μ i) • LinearMap.id) := LinearMap.ker_smul _ _ (Units.ne_zero t)

private lemma finrank_submodule_congr {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {S₁ S₂ : Submodule R M} (h : S₁ = S₂) :
    Module.finrank R S₁ = Module.finrank R S₂ := by subst h; rfl

private noncomputable abbrev tensorPowerBasis (N n : ℕ) :=
  (_root_.Basis.piTensorProduct (R := k) (fun _ : Fin n => Pi.basisFun k (Fin N)))

omit [IsAlgClosed k] [CharZero k] in
private lemma tensorPowerRepresentation_diagonalUnit_tensorPowerBasis
    (N n : ℕ) (i : Fin N) (t : kˣ)
    (f : Fin n → Fin N) :
    (tensorPowerRepresentation k N n (diagonalUnit k N i t)) (tensorPowerBasis (k := k) N n f) =
      ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
        tensorPowerBasis (k := k) N n f := by
  change PiTensorProduct.map (fun _ => Matrix.mulVecLin (diagonalUnit k N i t).val)
      (tensorPowerBasis (k := k) N n f) =
    ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
      tensorPowerBasis (k := k) N n f
  simp only [tensorPowerBasis, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
  -- Matrix.mulVecLin(diagonalUnit) on basis vector = scalar • basis vector
  have haction : ∀ (m : Fin n),
      Matrix.mulVecLin (R := k) (diagonalUnit k N i t).val (Pi.basisFun k (Fin N) (f m)) =
        (Function.update (1 : Fin N → k) i (t : k)) (f m) •
          Pi.basisFun k (Fin N) (f m) := by
    intro m
    simp only [diagonalUnit, Matrix.mulVecLin_apply, Pi.basisFun_apply]
    rw [Matrix.mulVec_single]
    ext x
    simp only [Pi.smul_apply, smul_eq_mul,
      Function.update_apply, Pi.single_apply, Pi.one_apply]
    by_cases hm : f m = i <;> by_cases hx : x = f m <;> simp_all
  simp_rw [haction]
  rw [(PiTensorProduct.tprod k).map_smul_univ
    (fun j => (Function.update (1 : Fin N → k) i (t : k)) (f j))
    (fun j => Pi.basisFun k (Fin N) (f j))]
  congr 1
  simp only [Function.update_apply, Pi.one_apply]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

omit [IsAlgClosed k] [CharZero k] in
private lemma repr_tensorPowerRepresentation_diagonalUnit_local (N n : ℕ) (i : Fin N) (t : kˣ)
    (v : auxiliarySpace k (Fin N → k) n) (f : Fin n → Fin N) :
    (tensorPowerBasis (k := k) N n).repr
        ((tensorPowerRepresentation k N n (diagonalUnit k N i t)) v) f =
      ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) *
        (tensorPowerBasis (k := k) N n).repr v f := by
  set b := tensorPowerBasis (k := k) N n
  set c := ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card)
  -- Both sides are linear in v; reduce to basis elements via LinearMap equality
  have h_eq : (Finsupp.lapply f).comp (b.repr.toLinearMap.comp
      (tensorPowerRepresentation k N n (diagonalUnit k N i t))) =
      c • ((Finsupp.lapply f).comp b.repr.toLinearMap) := by
    apply b.ext; intro g
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.smul_apply,
      smul_eq_mul, Finsupp.lapply_apply]
    rw [tensorPowerRepresentation_diagonalUnit_tensorPowerBasis, map_smul,
      Finsupp.smul_apply, smul_eq_mul, b.repr_self_apply]
    by_cases hgf : g = f <;> simp [hgf, c]
  exact LinearMap.congr_fun h_eq v

set_option synthInstance.maxHeartbeats 80000 in
-- Synthesizing `Module.Free k (weightSpace …)` requires a larger instance-search budget.
private theorem auxiliaryPolynomial_auxiliarySubtypeRepresentation_eq_shift
    (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    weightCharacter k N (FDRep.of (auxiliarySubtypeRepresentation k N lam)) =
      weightCharacter k N (schurRepresentation k N (fun i => lam i + 1)) := by
  rw [auxiliaryPolynomial_shift_eq_mul k N lam hlam]
  exact auxiliaryPolynomial_eq_product_X_mul_of_weightSpaceShift k N _ _
    (fun ν => finrank_submodule_congr
      (auxiliaryInvariant_ofSubtypeRepresentation_shift k N lam ν))
    (fun μ hμ => by
      -- The det-twisted Schur module has no weight spaces at zero-component weights.
      obtain ⟨i₀, hi₀⟩ := hμ
      suffices h : weightSpace k N (FDRep.of (auxiliarySubtypeRepresentation k N lam)) μ = ⊥ by
        simp [h]
      rw [Submodule.eq_bot_iff]
      intro v hv
      simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv
      -- For all t: ρ(diagonalUnit(i₀, t)) v = t^(μ i₀) • v = v  (since μ i₀ = 0)
      have hv_fix : ∀ t : kˣ,
          (FDRep.of (auxiliarySubtypeRepresentation k N lam)).ρ
            (diagonalUnit k N i₀ t) v = v := by
        intro t; have := hv i₀ t; rw [hi₀, pow_zero, one_smul] at this
        exact eq_of_sub_eq_zero this
      -- v is in schurSubmodule, a subtype of the tensor power
      -- Show (v : auxiliarySpace) = 0 using the tensor basis diagonal action
      set n := ∑ i, lam i
      set b := tensorPowerBasis (k := k) N n
      -- Extract the underlying tensor power element
      set vt : auxiliarySpace k (Fin N → k) n :=
        (v : schurSubmodule k N lam).val with hvt_def
      -- It suffices to show all basis coordinates of v (in the tensor power) are zero
      suffices hv_val : vt = 0 by
        exact SetCoe.ext hv_val
      rw [← b.repr.map_eq_zero_iff]
      ext f
      simp only [Finsupp.zero_apply]
      by_contra hcf
      -- The f-th basis coefficient is nonzero; derive contradiction
      set m := (Finset.univ.filter (fun j => f j = i₀)).card
      -- Pick t₀ with t₀^(m+1) ≠ 1 (exists since k is algebraically closed, hence infinite)
      obtain ⟨t₀, ht₀⟩ := exists_unit_pow_ne_one k (m + 1) (by omega)
      -- From weight space condition at (i₀, t₀):
      -- detTwistedRep(g) v = det(g) • schurSubmoduleRepresentation(g) v
      -- On the tensor power level:
      -- t₀ • tensorPowerRepresentation(diagonalUnit(i₀, t₀)) vt = vt
      have hfix_val :
          (t₀ : k) •
              (tensorPowerRepresentation k N n (diagonalUnit k N i₀ t₀)) vt = vt := by
        have h := congr_arg Subtype.val (hv_fix t₀)
        -- h : ↑(ρ(g) v) = ↑v at the FDRep level
        -- Unfold through FDRep.of_ρ', auxiliarySubtypeRepresentation, smul, restrict,
        -- and tensorPowerRepresentation.
        simp only [FDRep.of_ρ'] at h
        -- The coercions (smul_apply, restrict_coe_apply, coe_smul) are all rfl,
        -- so h is definitionally: det(g) • tensorPowerRepresentation(g) vt = vt
        have h2 : (Matrix.GeneralLinearGroup.det (diagonalUnit k N i₀ t₀) : k) •
            (tensorPowerRepresentation k N n (diagonalUnit k N i₀ t₀)) vt = vt := h
        rw [det_diagonalUnit_val] at h2
        exact h2
      -- Extract f-th basis coordinate: t₀^(m+1) * c_f = c_f
      have hcoord : (t₀ : k) ^ (m + 1) * b.repr vt f = b.repr vt f := by
        have h1 := congr_arg (fun w => b.repr w f) hfix_val
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
        rw [repr_tensorPowerRepresentation_diagonalUnit_local, ← mul_assoc, ← pow_succ'] at h1
        exact h1
      -- (t₀^(m+1) - 1) * c_f = 0, contradicting both ≠ 0
      have h_zero : ((t₀ : k) ^ (m + 1) - 1) * b.repr vt f = 0 := by
        rw [sub_mul, one_mul, hcoord, sub_self]
      exact (mul_eq_zero.mp h_zero).elim (sub_ne_zero.mpr ht₀) hcf)

omit [CharZero k] in
private theorem weightSpace_disjoint (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    {μ ν : Fin N → ℕ} (hne : μ ≠ ν) :
    Disjoint (weightSpace k N M μ) (weightSpace k N M ν) := by
  rw [Function.ne_iff] at hne; obtain ⟨i₀, hi₀⟩ := hne
  rw [Submodule.disjoint_def]
  intro v hv_μ hv_ν
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv_μ hv_ν
  obtain ⟨t₀, ht₀⟩ := exists_unit_pow_ne_pow k hi₀
  have h1 : M.ρ (diagonalUnit k N i₀ t₀) v = ((t₀ : k) ^ μ i₀) • v :=
    sub_eq_zero.mp (hv_μ i₀ t₀)
  have h2 : M.ρ (diagonalUnit k N i₀ t₀) v = ((t₀ : k) ^ ν i₀) • v :=
    sub_eq_zero.mp (hv_ν i₀ t₀)
  have h3 : (((t₀ : k) ^ μ i₀) - ((t₀ : k) ^ ν i₀)) • v = 0 := by
    rw [sub_smul]; exact sub_eq_zero.mpr (h1.symm.trans h2)
  rw [smul_eq_zero, sub_eq_zero] at h3
  exact h3.resolve_left ht₀

/-- The finite-dimensional representation for the incremented index is isomorphic to the auxiliary
subtype representation. -/
theorem shiftedAuxiliarySubtypeRepresentationIsoNonempty
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (FDRep.of (schurSubmoduleRepresentation k N (fun i => lam i + 1)) ≅
      FDRep.of (auxiliarySubtypeRepresentation k N lam)) := by
  have hlam' : Antitone (fun i => lam i + 1) :=
    fun i j hij => Nat.add_le_add_right (hlam hij) 1
  -- The det-twisted Schur module has the same formal character as the shifted Schur module
  have h_char : weightCharacter k N (FDRep.of (auxiliarySubtypeRepresentation k N lam)) =
      partitionPolynomial N (fun i => lam i + 1) := by
    rw [auxiliaryPolynomial_auxiliarySubtypeRepresentation_eq_shift k N lam hlam,
        weightCharacter_schurRepresentation_eq k N _ hlam']
  -- The det-twisted rep has the same dimension as the shifted Schur module.
  -- Both are polynomial GL_N reps (ℕ-valued weight spaces span everything),
  -- so their dimensions equal the total mass of the Schur polynomial.
  -- Since S_{λ+(1,...,1)} = (∏ Xᵢ) · S_λ and ∏ Xᵢ preserves total mass,
  -- dim L_λ = dim L_{λ+(1,...,1)}.
  -- The det-twisted rep is polynomial: its ℕ-valued weight spaces span everything. Its
  -- Weight spaces at (μ+1) match the indexed representation's weight spaces at μ
  -- (`auxiliaryInvariant_ofSubtypeRepresentation_shift`),
  -- and the schurRepresentation is polynomial. (Hoisted out so it is in scope as `h_span` below.)
  have h₁_top : ⨆ (μ : Fin N →₀ ℕ),
      weightSpace k N (FDRep.of (auxiliarySubtypeRepresentation k N lam))
        (fun i => μ i) = ⊤ := by
    rw [eq_top_iff, ← auxiliarySup_eq_top_for_auxiliaryRepresentation k N lam]
    apply iSup_le
    intro μ
    -- Map μ to its shift (i ↦ μ i + 1) as a Fin N →₀ ℕ
    set μ_shift : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => μ i + 1) with hμs
    refine le_trans ?_ (le_iSup _ μ_shift)
    -- auxiliaryInvariant_ofSubtypeRepresentation_shift gives equality
    -- (M₁ at μ+1) = (schurRepresentation at μ).
    have h_shift := auxiliaryInvariant_ofSubtypeRepresentation_shift k N lam (fun i => μ i)
    have h_apply : (fun i => μ_shift i) = (fun i => μ i + 1) := by
      ext i; simp [μ_shift]
    rw [h_apply, h_shift]
  -- The determinant-twisted representation is algebraic, assembled from the general
  -- algebraicity infrastructure and inlined here.
  have halg : HasAuxiliaryMapProperty N
      (FDRep.of (auxiliarySubtypeRepresentation k N lam)).ρ := by
    rw [FDRep.of_ρ']
    exact ((auxiliaryRepresentation_property k N (∑ i, lam i)).auxiliary_restrict
      (schurSubmodule k N lam)
      (fun g v hv => schurSubmodule_invariant k N lam g v hv)).auxiliary_det_smul
  have h_dim : Module.finrank k (FDRep.of (auxiliarySubtypeRepresentation k N lam)) =
      Module.finrank k (schurRepresentation k N (fun i => lam i + 1)) := by
    -- The schurRepresentation for λ+1 is polynomial (ℕ-valued weight spaces span).
    have h₂_top : ⨆ (μ : Fin N →₀ ℕ),
        weightSpace k N (schurRepresentation k N (fun i => lam i + 1)) (fun i => μ i) = ⊤ :=
      auxiliarySup_eq_top_for_auxiliaryRepresentation k N (fun i => lam i + 1)
    -- Formal characters agree (the det-twist shifts the character by the product of Xᵢ)
    have h_char_eq : weightCharacter k N (FDRep.of (auxiliarySubtypeRepresentation k N lam)) =
        weightCharacter k N (schurRepresentation k N (fun i => lam i + 1)) :=
      auxiliaryPolynomial_auxiliarySubtypeRepresentation_eq_shift k N lam hlam
    exact finrank_eq_of_auxiliaryPolynomial_eq k N _ _ h₁_top h₂_top h_char_eq
  -- By iso_of_auxiliaryConditions_and_finrank_eq, the determinant-twisted representation
  -- is isomorphic to schurRepresentation k N (λ+1).
  obtain ⟨iso⟩ := iso_of_auxiliaryConditions_and_finrank_eq k N (fun i => lam i + 1) hlam'
    _ halg h₁_top h_char h_dim
  exact ⟨iso.symm⟩

omit [IsAlgClosed k] [CharZero k] in
/-- The right tensor unitor intertwines the indicated auxiliary subtype action with the
tensor-product action. -/
theorem auxiliarySubtypeRepresentation_tensorRightUnitor_naturality (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    (TensorProduct.rid k (schurSubmodule k N lam)).toLinearMap ∘ₗ
      TensorProduct.map (schurSubmoduleRepresentation k N lam g)
        (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
          Matrix.GeneralLinearGroup.det g) =
    (auxiliarySubtypeRepresentation k N lam g) ∘ₗ
      (TensorProduct.rid k (schurSubmodule k N lam)).toLinearMap := by
  apply TensorProduct.ext'
  intro v c
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul, auxiliarySubtypeRepresentation]
  -- LHS: (det(g)·c) • rep(g) v   RHS: det(g) • rep(g) (c • v)
  -- LHS: (↑(lsmul).toRingHom ↑(det g)) c • rep(g) v  = (↑(det g) * c) • rep(g) v
  -- RHS: det(g) • rep(g) (c • v) = det(g) • c • rep(g) v
  change ((↑(Matrix.GeneralLinearGroup.det g) : k) * c) •
      ((schurSubmoduleRepresentation k N lam) g) v =
    (↑(Matrix.GeneralLinearGroup.det g) : k) •
      ((schurSubmoduleRepresentation k N lam) g) (c • v)
  rw [map_smul, mul_smul, smul_comm]

omit [CharZero k] in
/-- The tensor product of an indexed representation with an auxiliary representation is isomorphic
to the auxiliary subtype representation. -/
theorem tensorAuxiliaryRepresentationIsoNonempty (N : ℕ) (lam : Fin N → ℕ) :
    Nonempty (schurRepresentation k N lam ⊗ auxiliaryFiniteDimensionalRepresentation k N ≅
      FDRep.of (auxiliarySubtypeRepresentation k N lam)) := by
  -- The underlying linear iso is TensorProduct.rid: M ⊗ k ≅ M
  refine ⟨Action.mkIso
    ((TensorProduct.rid k (schurSubmodule k N lam)).toFGModuleCatIso) (fun g => ?_)⟩
  ext : 1
  exact auxiliarySubtypeRepresentation_tensorRightUnitor_naturality k N lam g

/-- The successor-indexed representation is isomorphic to the tensor product of the original
representation and an auxiliary representation. -/
@[source_ref"Chapter5/Proposition5.22.2"(role:=primary)]
theorem shiftedAuxiliaryRepresentationTensorIsoNonempty
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (schurRepresentation k N (fun i => lam i + 1) ≅
      schurRepresentation k N lam ⊗ auxiliaryFiniteDimensionalRepresentation k N) := by
  -- Decompose into two steps:
  -- (1) L_{λ+1^N} ≅ det-twisted L_λ  (character argument)
  -- (2) det-twisted L_λ ≅ L_λ ⊗ det  (categorical tensor/twist equivalence)
  obtain ⟨iso₁⟩ := shiftedAuxiliarySubtypeRepresentationIsoNonempty k N lam hlam
  obtain ⟨iso₂⟩ := tensorAuxiliaryRepresentationIsoNonempty k N lam
  exact ⟨iso₁ ≪≫ iso₂.symm⟩

/-- The representation indexed by the pointwise successor is isomorphic to the tensor product of
the original representation with an auxiliary finite-dimensional representation. -/
@[source_ref"Chapter5/Proposition5.22.2"(role:=primary)]
theorem shiftedAuxiliaryRepresentationTensorAuxiliaryIsoNonempty
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (schurRepresentation k N (fun i => lam i + 1) ≅
      schurRepresentation k N lam ⊗ auxiliaryFiniteDimensionalRepresentationPrime k N) := by
  obtain ⟨iso⟩ := shiftedAuxiliaryRepresentationTensorIsoNonempty k N lam hlam
  -- Replace auxiliaryFiniteDimensionalRepresentation by the top exterior power in the
  -- tensor factor.
  exact ⟨iso ≪≫ (whiskerLeftIso (schurRepresentation k N lam)
    (auxiliaryFiniteDimensionalRepresentationsIso k N)).symm⟩

end RepresentationTheory.GeneralLinearGroup.ExteriorPower
