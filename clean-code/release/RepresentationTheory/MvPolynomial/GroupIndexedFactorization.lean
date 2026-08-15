/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Group.IndexedPolynomial
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.AuxiliaryMatrixDeterminantIrreducibility
import RepresentationTheory.Alignment.Attribute

/-!
# Group-indexed polynomial factorization
-/


universe u

open MvPolynomial Matrix Finset

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]

/-- Supplies evaluation of a monoid-algebra element as its coefficient function on the group. -/
local instance RepresentationTheory.MvPolynomial.GroupIndexedFactorization.instCoeFunMonoidAlgebraToCoeffFunction : CoeFun (MonoidAlgebra k G) (fun _ => G → k) := ⟨fun a => a.coeff⟩

set_option linter.unusedSectionVars false


/-- Associates a group-indexed multivariate polynomial to an auxiliary datum and a finite index. -/
noncomputable def RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i : Fin D.count) : MvPolynomial G k :=
  det (of fun (a b : Fin (D.dimension i)) =>
    ∑ g : G, C (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b) * X g)


section NormHelpers

variable (R : Type*) [CommRing R]


private lemma Algebra.norm_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by

  apply Fintype.induction_empty_option
    (P := fun (ι : Type _) [Fintype ι] => ∀ (A : ι → Type _) [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
        [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (x : ∀ i, A i),
        Algebra.norm R x = ∏ i, Algebra.norm R (x i))
  ·
    intro α β hβ e IH A hRingA hAlgA hFreeA hFiniteA x
    let eA : (∀ i : α, A (e i)) ≃ₐ[R] (∀ i : β, A i) := AlgEquiv.piCongrLeft R A e
    have hkey : Algebra.norm R (eA.symm x) = Algebra.norm R x :=
      Algebra.norm_eq_of_algEquiv eA.symm x
    have hval : eA.symm x = fun i => x (e i) := by
      ext i
      rw [show (eA.symm x) i = ((Equiv.piCongrLeft (fun j => A j) e).symm x) i from rfl]
      rw [Equiv.piCongrLeft_symm_apply]
    rw [← hkey, hval]
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [IH (A := fun i => A (e i)) (x := fun i => x (e i))]
    exact Fintype.prod_equiv e (fun i => Algebra.norm R (x (e i)))
      (fun i => Algebra.norm R (x i)) (fun i => rfl)
  ·
    intro A _ _ _ _ x
    simp only [Fintype.prod_empty]
    have hx : x = 1 := by ext i; exact PEmpty.elim i
    rw [hx, map_one]
  ·
    intro ι' _ IH A _ _ _ _ x
    haveI : DecidableEq ι' := Classical.decEq ι'

    let e : (∀ i : Option ι', A i) ≃ₐ[R] A none × (∀ i, A (some i)) :=
      { RingEquiv.piOptionEquivProd with
        commutes' := fun r => by
          ext i
          · simp [RingEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]
          · simp [RingEquiv.piOptionEquivProd, Equiv.piOptionEquivProd] }
    have hstep : Algebra.norm R (e x) = Algebra.norm R x := Algebra.norm_eq_of_algEquiv e x
    have IHsome := IH (A := fun i => A (some i))

    have norm_pair : Algebra.norm R (e x) = Algebra.norm R (e x).1 * Algebra.norm R (e x).2 := by
      simp only [Algebra.norm_apply]
      rw [show Algebra.lmul R (A none × (∀ i, A (some i))) (e x) =
          LinearMap.prodMap (Algebra.lmul R (A none) (e x).1)
            (Algebra.lmul R (∀ i, A (some i)) (e x).2) from ?hlmul]
      · exact LinearMap.det_prodMap _ _
      case hlmul =>
        apply LinearMap.ext; intro ⟨a, b⟩
        simp only [Algebra.coe_lmul_eq_mul, LinearMap.prodMap_apply]; rfl
    rw [← hstep]
    rw [norm_pair]
    simp only [show (e x).1 = x none from rfl, show (e x).2 = fun i => x (some i) from rfl]
    rw [IHsome, Fintype.prod_option]


private lemma Algebra.norm_matrix {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) R) :
    Algebra.norm R M = M.det ^ n := by
  open Kronecker in
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis R (Fin n) (Fin n))]
  have hkron : Algebra.leftMulMatrix (Matrix.stdBasis R (Fin n) (Fin n)) M =
      M ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [Algebra.leftMulMatrix_eq_repr_mul, Matrix.kroneckerMap_apply, Matrix.one_apply,
               Matrix.stdBasis_eq_single]
    have hmul : M * Matrix.single i₂ j₂ (1 : R) =
        Matrix.of (fun r c => M r i₂ * if c = j₂ then 1 else 0) := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single i₂]
      · simp [eq_comm]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    rw [hmul]
    simp [Matrix.stdBasis, Equiv.sigmaEquivProd_symm_apply, Pi.basis_repr, Pi.basisFun_repr,
          Matrix.ofLinearEquiv]
  open Kronecker in
  rw [hkron, Matrix.det_kronecker, Matrix.det_one, Fintype.card_fin, one_pow, mul_one]

end NormHelpers


private lemma leftMulMatrix_monoidAlgebra_entry
    (a : MonoidAlgebra k G) (g h : G) :
    Algebra.leftMulMatrix (MonoidAlgebra.basis G k) a g h =
      a (g * h⁻¹) := by
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  exact (a.coeff_mul_single_eq_coeff_mul (g * h⁻¹)
    (fun m' _ => eq_mul_inv_iff_mul_eq.symm)).trans (mul_one _)


private lemma RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.projRingHom_smul' [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i : Fin D.count)
    (r : k) (a : MonoidAlgebra k G) :
    D.matrixBlockHom i (r • a) = r • D.matrixBlockHom i a := by
  simp [RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.matrixBlockHom]


/-- The auxiliary group-indexed polynomial equals the product of the indexed auxiliary polynomials to their prescribed powers, scaled by the sign of inversion. -/
@[source_ref "Chapter4/Theorem4.10.2" (role := primary),
  source_ref "Chapter4/Discussion_proof_Theorem4.10.2" (role := supporting)]
lemma RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryGroupPolynomial_eq_sign_smul_prod_auxiliaryPolynomial_pow [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) :
    RepresentationTheory.Group.IndexedPolynomial.groupIndexedPolynomial k G =
      ((Equiv.Perm.sign (Equiv.inv G) : ℤ) : k) • ∏ i : Fin D.count, D.auxiliaryPolynomial i ^ D.dimension i := by

  haveI : Infinite k := IsAlgClosed.instInfinite
  apply MvPolynomial.funext
  intro σ

  set a : MonoidAlgebra k G := ∑ s : G, σ s • MonoidAlgebra.of k G s with ha_def

  have hLHS : MvPolynomial.eval σ (RepresentationTheory.Group.IndexedPolynomial.groupIndexedPolynomial k G) =
      (Matrix.of fun g h : G => σ (g * h)).det := by
    unfold RepresentationTheory.Group.IndexedPolynomial.groupIndexedPolynomial
    rw [RingHom.map_det]
    congr 1; ext g h; simp [Matrix.map, Matrix.of_apply, MvPolynomial.eval_X]

  have hPerm : (Matrix.of fun g h : G => σ (g * h)).det =
      ((Equiv.Perm.sign (Equiv.inv G) : ℤ) : k) *
        (Matrix.of fun g h : G => σ (g * h⁻¹)).det := by
    have hsub : (Matrix.of fun g h : G => σ (g * h)) =
        (Matrix.of fun g h : G => σ (g * h⁻¹)).submatrix id (Equiv.inv G) := by
      ext g h
      simp [Matrix.submatrix_apply, Equiv.inv_apply]
    rw [hsub]
    exact Matrix.det_permute' (Equiv.inv G) _

  have hRHS : MvPolynomial.eval σ (∏ i : Fin D.count, D.auxiliaryPolynomial i ^ D.dimension i) =
      ∏ i : Fin D.count, (MvPolynomial.eval σ (D.auxiliaryPolynomial i)) ^ D.dimension i := by
    rw [map_prod]; congr 1; ext i; rw [map_pow]

  have hblock_eq : ∀ i : Fin D.count, MvPolynomial.eval σ (D.auxiliaryPolynomial i) =
      (D.matrixBlockHom i a).det := by
    intro i
    unfold RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial
    rw [RingHom.map_det]
    congr 1
    funext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [ha_def, map_sum]
    simp only [D.projRingHom_smul' i, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro g _; ring

  have hLHS_eq : (Matrix.of fun g h : G => σ (g * h⁻¹)).det = Algebra.norm k a := by
    rw [Algebra.norm_eq_matrix_det (MonoidAlgebra.basis G k)]
    congr 1
    funext g h
    rw [of_apply, leftMulMatrix_monoidAlgebra_entry]
    change σ (g * h⁻¹) =
      (∑ s : G, σ s • MonoidAlgebra.of k G s : MonoidAlgebra k G).coeff (g * h⁻¹)
    rw [MonoidAlgebra.coeff_sum]
    simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply,
      MonoidAlgebra.single, MonoidAlgebra.coeff_ofCoeff, smul_eq_mul, mul_one]
    simpa using Finsupp.ext_iff.mp
      (Finsupp.univ_sum_single (Finsupp.equivFunOnFinite.symm σ)).symm (g * h⁻¹)

  have hsmul : MvPolynomial.eval σ
      (((Equiv.Perm.sign (Equiv.inv G) : ℤ) : k) • ∏ i : Fin D.count, D.auxiliaryPolynomial i ^ D.dimension i) =
      ((Equiv.Perm.sign (Equiv.inv G) : ℤ) : k) *
        MvPolynomial.eval σ (∏ i : Fin D.count, D.auxiliaryPolynomial i ^ D.dimension i) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]

  rw [hLHS, hPerm, hLHS_eq, hsmul]
  congr 1

  rw [hRHS]
  simp_rw [hblock_eq]
  rw [show Algebra.norm k a = Algebra.norm k (D.groupAlgebraEquivMatrix a) from
    (Algebra.norm_eq_of_algEquiv D.groupAlgebraEquivMatrix a).symm]
  rw [Algebra.norm_pi k]
  congr 1; ext i
  haveI := D.dimension_neZero i
  rw [Algebra.norm_matrix k]

  congr 2


section GenericDet

variable {k' : Type*} [Field k'] {σ : Type*} [DecidableEq σ]


private lemma vars_sub_mul_left {a b : MvPolynomial σ k'} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.vars ⊆ (a * b).vars := by
  intro x hx
  simp only [MvPolynomial.vars_def] at hx ⊢
  rw [Multiset.mem_toFinset] at hx ⊢
  rw [← Multiset.count_pos] at hx ⊢
  rw [← MvPolynomial.degreeOf_def] at hx ⊢
  have := MvPolynomial.degreeOf_mul_eq ha hb (n := x)
  omega


private lemma rename_irred {τ : Type*} [DecidableEq τ]
    {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ k'} (hp : Irreducible p) :
    Irreducible (MvPolynomial.rename f p) := by
  constructor
  · intro h
    exact hp.1 ((MvPolynomial.killCompl_rename_app hf p) ▸
      h.map (MvPolynomial.killCompl hf).toRingHom)
  · intro a b hab
    have hne : MvPolynomial.rename f p ≠ 0 :=
      (MvPolynomial.rename_injective f hf).ne hp.ne_zero
    have ha : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hne)
    have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hne)
    have hvars_rfp : ∀ x ∈ (MvPolynomial.rename f p).vars, x ∈ Set.range f := by
      intro x hx; obtain ⟨y, _, rfl⟩ := MvPolynomial.mem_vars_rename f p hx
      exact Set.mem_range_self y
    have hvars_a : ↑a.vars ⊆ Set.range f := by
      intro x hx; exact hvars_rfp x (hab ▸ vars_sub_mul_left ha hb hx)
    have hvars_b : ↑b.vars ⊆ Set.range f := by
      intro x hx; exact hvars_rfp x (hab ▸ mul_comm a b ▸ vars_sub_mul_left hb ha hx)
    obtain ⟨a', rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range a f hf hvars_a
    obtain ⟨b', rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range b f hf hvars_b
    rw [← map_mul] at hab
    have hab' : p = a' * b' := (MvPolynomial.rename_injective f hf) hab
    exact (hp.isUnit_or_isUnit hab').imp
      (·.map (MvPolynomial.rename f).toRingHom) (·.map (MvPolynomial.rename f).toRingHom)

end GenericDet


private lemma genDet_irreducible (k' : Type*) [Field k'] (n : ℕ) (hn : 0 < n) :
    Irreducible (det (mvPolynomialX (Fin n) (Fin n) k')) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hdet : det (mvPolynomialX (Fin 1) (Fin 1) k') = MvPolynomial.X ((0 : Fin 1), (0 : Fin 1)) := by
        rw [det_fin_one]; rfl
      rw [hdet]
      exact MvPolynomial.irreducible_of_totalDegree_eq_one
        (MvPolynomial.totalDegree_X _)
        (fun x hx => isUnit_of_dvd_one (by
          have := hx (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) 1)

          rw [MvPolynomial.coeff_X, if_pos rfl] at this
          exact this))
    | succ n =>
      have ih' := ih (by omega)

      set M := mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) k' with hM_def

      have hsub_rename : ∀ c : Fin (n + 2),
          det (M.submatrix Fin.succ (Fin.succAbove c)) =
          MvPolynomial.rename (Prod.map Fin.succ (Fin.succAbove c))
            (det (mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) k')) := by
        intro c; rw [AlgHom.map_det]; congr 1; funext i j
        simp only [submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
          hM_def, mvPolynomialX_apply, MvPolynomial.rename_X, Prod.map]

      have hsub_vars : ∀ c : Fin (n + 2), ∀ v ∈
          (det (M.submatrix Fin.succ (Fin.succAbove c))).vars, v.1 ≠ 0 := by
        intro c v hv; rw [hsub_rename c] at hv
        obtain ⟨⟨a, b⟩, _, hab⟩ := MvPolynomial.mem_vars_rename _ _ hv
        exact hab ▸ Fin.succ_ne_zero a

      have hf_ne : det (M.submatrix Fin.succ (Fin.succAbove 0)) ≠ 0 := by
        rw [hsub_rename 0]
        exact (MvPolynomial.rename_injective _
          (Prod.map_injective.mpr ⟨Fin.succ_injective _, Fin.succAbove_right_injective⟩)).ne
          (det_mvPolynomialX_ne_zero (Fin (n + 1)) k')

      have hf_vars : ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
          (det (M.submatrix Fin.succ (Fin.succAbove 0))).vars := by
        intro h; exact absurd rfl (hsub_vars 0 _ h)

      have hg_vars : ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))).vars := by
        intro h
        have h' := MvPolynomial.vars_sum_subset (Finset.univ) _ h
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h'
        obtain ⟨j, hj⟩ := h'
        have hj' := MvPolynomial.vars_mul _ _ hj
        simp only [Finset.mem_union] at hj'
        rcases hj' with hj' | hj'
        · have hj'' := MvPolynomial.vars_mul _ _ hj'
          simp only [Finset.mem_union] at hj''
          rcases hj'' with hj'' | hj''
          · exact absurd (MvPolynomial.vars_pow _ _ hj'') (by simp)
          · rw [MvPolynomial.vars_X] at hj''
            simp only [Finset.mem_singleton] at hj''
            exact absurd (congr_arg Prod.snd hj'').symm (Fin.succ_ne_zero j)
        · exact absurd rfl (hsub_vars j.succ _ hj')

      have hf_irr : Irreducible (det (M.submatrix Fin.succ (Fin.succAbove 0))) := by
        rw [hsub_rename 0]; simp only [Fin.succAbove_zero]
        exact rename_irred (Prod.map_injective.mpr
          ⟨Fin.succ_injective _, Fin.succ_injective _⟩) ih'

      have hf1_irr : Irreducible (det (M.submatrix Fin.succ
          (Fin.succAbove (1 : Fin (n + 2))))) := by
        rw [hsub_rename 1]
        exact rename_irred (Prod.map_injective.mpr
          ⟨Fin.succ_injective _, Fin.succAbove_right_injective⟩) ih'

      have hrel : IsRelPrime
          (det (M.submatrix Fin.succ (Fin.succAbove 0)))
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))) := by
        rw [hf_irr.isRelPrime_iff_not_dvd]

        let φ : (Fin (n + 2) × Fin (n + 2)) → MvPolynomial (Fin (n + 2) × Fin (n + 2)) k' :=
          fun v => if v.1 = 0 then (if v.2 = 1 then 1 else 0) else MvPolynomial.X v
        have aeval_X_id : ∀ (p : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k'),
            MvPolynomial.aeval (MvPolynomial.X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') p = p := by
          have : MvPolynomial.aeval (MvPolynomial.X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') =
              AlgHom.id k' _ := by ext i; simp
          intro p; rw [this]; simp

        have hφ_fix : ∀ (c : Fin (n + 2)),
            MvPolynomial.aeval φ (det (M.submatrix Fin.succ (Fin.succAbove c))) =
            det (M.submatrix Fin.succ (Fin.succAbove c)) := by
          intro c
          have hφ_eq : ∀ v ∈ (det (M.submatrix Fin.succ (Fin.succAbove c))).vars,
              φ v = MvPolynomial.X v := by
            intro v hv; simp only [φ, if_neg (hsub_vars c v hv)]
          rw [show MvPolynomial.aeval φ (det (M.submatrix Fin.succ (Fin.succAbove c))) =
            MvPolynomial.aeval MvPolynomial.X (det (M.submatrix Fin.succ (Fin.succAbove c))) from
            MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hφ_eq i hi) rfl]
          exact aeval_X_id _

        have hφ_X : ∀ j : Fin (n + 1),
            φ ((0 : Fin (n + 2)), j.succ) = if j = 0 then 1 else 0 := by
          intro j; simp only [φ, ite_true]
          rcases Decidable.eq_or_ne j 0 with rfl | hj
          · simp [show Fin.succ (0 : Fin (n + 1)) = (1 : Fin (n + 2)) from rfl]
          · simp [show Fin.succ j ≠ (1 : Fin (n + 2)) from by
              rwa [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Ne, Fin.succ_inj], hj]

        intro ⟨q, hq⟩

        have hφ_rest : MvPolynomial.aeval φ (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))) =
            -det (M.submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))) := by
          simp only [map_sum, map_mul, map_pow, map_neg, map_one, MvPolynomial.aeval_X,
            hφ_fix, hφ_X]; rw [Fin.sum_univ_succ]; simp

        have hdvd : det (M.submatrix Fin.succ (Fin.succAbove 0)) ∣
            det (M.submatrix Fin.succ (Fin.succAbove 1)) := by
          have h1 : MvPolynomial.aeval φ (det (M.submatrix Fin.succ (Fin.succAbove 0))) ∣
              MvPolynomial.aeval φ (∑ j : Fin (n + 1),
                (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
                MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
                det (M.submatrix Fin.succ (Fin.succAbove j.succ))) :=
            (MvPolynomial.aeval φ).toRingHom.map_dvd ⟨q, hq⟩
          rw [hφ_fix 0, hφ_rest] at h1; exact dvd_neg.mp h1

        have hassoc := hf_irr.associated_of_dvd hf1_irr hdvd
        obtain ⟨u, hu⟩ := hassoc

        have hmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∈
            (det (M.submatrix Fin.succ (Fin.succAbove 0))).vars := by
          by_contra habs
          let g₁ : Fin (n + 2) × Fin (n + 2) → k' := fun ⟨i, j⟩ => if i = j then 1 else 0
          let g₂ : Fin (n + 2) × Fin (n + 2) → k' := Function.update g₁ (1, 1) 0
          have hag : ∀ i ∈ (det (M.submatrix Fin.succ (Fin.succAbove 0))).vars,
              g₁ i = g₂ i := by
            intro i hi; exact (Function.update_of_ne (ne_of_mem_of_not_mem hi habs) _ _).symm
          have heq : MvPolynomial.eval g₁ (det (M.submatrix Fin.succ (Fin.succAbove 0))) =
              MvPolynomial.eval g₂ (det (M.submatrix Fin.succ (Fin.succAbove 0))) :=
            MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hag i hi) rfl
          have hev1 : MvPolynomial.eval g₁
              (det (M.submatrix Fin.succ (Fin.succAbove 0))) = 1 := by
            rw [show MvPolynomial.eval g₁ (det (M.submatrix Fin.succ (Fin.succAbove 0))) =
              det ((MvPolynomial.eval g₁).mapMatrix
                (M.submatrix Fin.succ (Fin.succAbove 0))) from RingHom.map_det _ _]
            have : (MvPolynomial.eval g₁).mapMatrix
                (M.submatrix Fin.succ (Fin.succAbove 0)) =
                (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k') := by
              ext i j
              simp only [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply,
                hM_def, mvPolynomialX_apply, MvPolynomial.eval_X, Fin.succAbove_zero, one_apply]
              simp only [g₁, Fin.succ_inj]
            rw [this, det_one]
          have hev0 : MvPolynomial.eval g₂
              (det (M.submatrix Fin.succ (Fin.succAbove 0))) = 0 := by
            rw [show MvPolynomial.eval g₂ (det (M.submatrix Fin.succ (Fin.succAbove 0))) =
              det ((MvPolynomial.eval g₂).mapMatrix
                (M.submatrix Fin.succ (Fin.succAbove 0))) from RingHom.map_det _ _]
            apply det_eq_zero_of_row_eq_zero (0 : Fin (n + 1))
            intro j
            simp only [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply,
              hM_def, mvPolynomialX_apply, MvPolynomial.eval_X, Fin.succAbove_zero]
            simp only [g₂, g₁, Function.update_apply, Prod.mk.injEq]
            by_cases hj : j = 0
            · subst hj; simp
            · have hjs1 : ¬(j.succ : Fin (n + 2)) = (1 : Fin (n + 2)) := by
                intro h; exact hj (Fin.succ_injective _ h)
              simp [hjs1, show (Fin.succ (0 : Fin (n + 1)) : Fin (n + 2)) =
                (1 : Fin (n + 2)) from rfl, Ne.symm (show ¬j.succ = (1 : Fin (n + 2)) from hjs1)]
          exact absurd (hev1.symm.trans (heq.trans hev0)) one_ne_zero
        have hnotmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∉
            (det (M.submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2))))).vars := by
          rw [hsub_rename 1]; intro h
          obtain ⟨⟨a, b⟩, _, hab⟩ := MvPolynomial.mem_vars_rename _ _ h
          simp only [Prod.map, Prod.mk.injEq] at hab
          exact absurd hab.2 (Fin.succAbove_ne 1 b)
        exact hnotmem (hu ▸ vars_sub_mul_left hf_irr.ne_zero (Units.ne_zero u) hmem)

      have heq : det M =
          det (M.submatrix Fin.succ (Fin.succAbove 0)) *
          MvPolynomial.X ((0 : Fin (n + 2)), (0 : Fin (n + 2))) +
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))) := by
        rw [det_succ_row_zero, Fin.sum_univ_succ]
        simp only [hM_def, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, mvPolynomialX_apply,
          Fin.val_succ]
        ring
      rw [heq]
      exact MvPolynomial.irreducible_mul_X_add _ _ _ hf_ne hf_vars hg_vars hrel


/-- The total degree of an auxiliary polynomial equals the corresponding auxiliary natural number. -/
@[source_ref "Chapter4/Discussion_proof_Theorem4.10.2" (role := supporting)]
lemma RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.totalDegree_auxiliaryPolynomial [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i : Fin D.count) :
    (D.auxiliaryPolynomial i).totalDegree = D.dimension i := by
  apply le_antisymm
  ·
    unfold RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial
    let M := of fun (a b : Fin (D.dimension i)) =>
      ∑ g : G, C (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b) * X g
    change (det M).totalDegree ≤ D.dimension i
    rw [det_apply]
    apply (totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro σ _
    have hsmul : (Equiv.Perm.sign σ • ∏ a, M (σ a) a).totalDegree =
        (∏ a, M (σ a) a).totalDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · simp [h]
      · simp [h, totalDegree_neg]
    rw [hsmul]
    calc (∏ a, M (σ a) a).totalDegree
        ≤ ∑ a, (M (σ a) a).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ _a : Fin (D.dimension i), 1 := by
          apply Finset.sum_le_sum; intro a _
          change (∑ g : G, C (D.matrixBlockHom i (MonoidAlgebra.of k G g) (σ a) a) *
            X g).totalDegree ≤ 1
          apply (totalDegree_finsetSum _ _).trans
          apply Finset.sup_le; intro g _
          calc MvPolynomial.totalDegree (C _ * X g)
              ≤ MvPolynomial.totalDegree (C _) +
                MvPolynomial.totalDegree (X g) := totalDegree_mul _ _
            _ = 0 + 1 := by rw [totalDegree_C, totalDegree_X]
            _ = 1 := by ring
      _ = D.dimension i := by simp
  ·

    have hentry : ∀ (a b : Fin (D.dimension i)),
        (∑ g : G, C (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b) *
          X g).IsHomogeneous 1 :=
      fun a b => IsHomogeneous.sum _ _ _ fun g _ =>
        (MvPolynomial.isHomogeneous_C (σ := G)
          (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b)).mul
          (MvPolynomial.isHomogeneous_X (R := k) g)

    have hhom : (D.auxiliaryPolynomial i).IsHomogeneous (D.dimension i) := by
      unfold RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial; rw [det_apply]
      apply IsHomogeneous.sum; intro σ _
      have hprod : IsHomogeneous (∏ a : Fin (D.dimension i),
          of (fun a b => ∑ g : G,
            C (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b) * X g)
          (σ a) a) (∑ _a : Fin (D.dimension i), 1) := by
        apply IsHomogeneous.prod; intro a _
        exact hentry (σ a) a
      simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one] at hprod
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]; exact hprod
      · simp only [h, Units.smul_def] at *
        rw [show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_one_zsmul]
        exact (homogeneousSubmodule G k (D.dimension i)).neg_mem hprod

    have hne : D.auxiliaryPolynomial i ≠ 0 := by
      intro h
      have heval : MvPolynomial.eval
          (fun g => if g = (1 : G) then (1 : k) else 0) (D.auxiliaryPolynomial i) = 1 := by
        unfold RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial
        rw [show MvPolynomial.eval _ (det _) = det
          ((MvPolynomial.eval _).mapMatrix _) from RingHom.map_det _ _]
        have hmat : (MvPolynomial.eval
            (fun g => if g = (1 : G) then (1 : k) else 0)).mapMatrix
            (of fun a b => ∑ g : G,
              C (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b) * X g) =
            (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) := by
          ext a b
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply,
            map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
            one_apply]
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true]
          have : D.matrixBlockHom i (MonoidAlgebra.of k G 1) = 1 := by
            have h1 : MonoidAlgebra.of k G (1 : G) = 1 := map_one _
            rw [h1, map_one]
          rw [this]; simp [one_apply]
        rw [hmat, det_one]
      rw [h, map_zero] at heval; exact one_ne_zero heval.symm

    exact (hhom.totalDegree hne).symm.le


private lemma totalDegree_aeval_le_of_deg_le_one
    {σ τ : Type*} [DecidableEq τ] {k' : Type*} [CommSemiring k']
    {f : σ → MvPolynomial τ k'} (hf : ∀ s, (f s).totalDegree ≤ 1)
    (p : MvPolynomial σ k') :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by

  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le; intro d hd

  rw [MvPolynomial.aeval_monomial]
  simp only [MvPolynomial.algebraMap_eq]
  calc (MvPolynomial.C (MvPolynomial.coeff d p) *
        d.prod fun i k => f i ^ k).totalDegree
      ≤ (MvPolynomial.C (MvPolynomial.coeff d p)).totalDegree +
        (d.prod fun i k => f i ^ k).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + (d.prod fun i k => f i ^ k).totalDegree := by
          simp [MvPolynomial.totalDegree_C]
    _ = (d.prod fun i k => f i ^ k).totalDegree := by ring
    _ = (∏ s ∈ d.support, f s ^ d s).totalDegree := by rfl
    _ ≤ ∑ s ∈ d.support, (f s ^ d s).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ s ∈ d.support, d s := by
          apply Finset.sum_le_sum; intro s _
          calc (f s ^ d s).totalDegree
              ≤ d s * (f s).totalDegree := MvPolynomial.totalDegree_pow _ _
            _ ≤ d s * 1 := Nat.mul_le_mul_left _ (hf s)
            _ = d s := mul_one _
    _ = d.sum fun _ n => n := by rfl
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

/-- Each auxiliary polynomial in the finite indexed family is irreducible. -/
@[source_ref "Chapter4/Discussion_proof_Theorem4.10.2/Derived2" (role := supporting)]
lemma RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial_irreducible [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i : Fin D.count) :
    Irreducible (D.auxiliaryPolynomial i) := by
  haveI := D.dimension_neZero i

  set di := D.dimension i with hdi_def

  have hirr_gen := genDet_irreducible k di (Nat.pos_of_ne_zero (NeZero.ne _))
  set genD := det (mvPolynomialX (Fin di) (Fin di) k) with hgenD_def

  let φ : Fin di × Fin di → MvPolynomial G k :=
    fun ⟨a, b⟩ => ∑ g : G, C (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b) * X g

  have hbp : D.auxiliaryPolynomial i = MvPolynomial.aeval φ genD := by
    unfold RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial; rw [AlgHom.map_det]; congr 1; ext a b
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, mvPolynomialX_apply,
      MvPolynomial.aeval_X]; rfl


  let sect : Fin di → Fin di → MonoidAlgebra k G :=
    fun a b => D.groupAlgebraEquivMatrix.symm (Pi.single i (Matrix.single a b 1))
  have hsect : ∀ a b, D.matrixBlockHom i (sect a b) = Matrix.single a b 1 := by
    intro a b; simp [sect, RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.matrixBlockHom, Pi.evalRingHom, Pi.single]

  let ψ : G → MvPolynomial (Fin di × Fin di) k :=
    fun g => ∑ a : Fin di, ∑ b : Fin di,
      C ((sect a b : MonoidAlgebra k G) g) * X (a, b)

  have hψ_deg : ∀ g : G, (ψ g).totalDegree ≤ 1 := by
    intro g
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    apply Finset.sup_le; intro a _
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    apply Finset.sup_le; intro b _
    calc (C ((sect a b : MonoidAlgebra k G) g) * X (a, b)).totalDegree
        ≤ (C _).totalDegree + (X (a, b)).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 0 + 1 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
      _ = 1 := by ring

  have hretract : ∀ v : Fin di × Fin di, MvPolynomial.aeval ψ (φ v) = X v := by
    intro ⟨a, b⟩
    simp only [φ, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      MvPolynomial.algebraMap_eq]


    have hcoeff : ∀ r c, ∑ g : G, D.matrixBlockHom i (MonoidAlgebra.of k G g) a b *
        (sect r c : MonoidAlgebra k G) g =
        (D.matrixBlockHom i (sect r c)) a b := by
      intro r c
      have hsrc : sect r c = ∑ g : G, (sect r c) g • MonoidAlgebra.of k G g := by
        apply MonoidAlgebra.coeff_injective
        ext h
        simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
      conv_rhs => rw [hsrc]
      rw [map_sum]; simp_rw [D.projRingHom_smul' i]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

    simp only [ψ]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext r; rw [Finset.sum_comm]


    simp_rw [← Finset.sum_mul, ← map_sum]

    simp_rw [hcoeff, hsect, Matrix.single_apply]
    rw [Finset.sum_eq_single a _ (fun h => absurd (Finset.mem_univ _) h),
      Finset.sum_eq_single b _ (fun h => absurd (Finset.mem_univ _) h)]
    · simp
    · intro c _ hc; simp [hc]
    · intro r _ hr
      apply Finset.sum_eq_zero; intro c _
      simp [hr]

  have hid : ∀ p : MvPolynomial (Fin di × Fin di) k,
      MvPolynomial.aeval ψ (MvPolynomial.aeval φ p) = p := by
    intro p
    have h : (MvPolynomial.aeval ψ).comp (MvPolynomial.aeval φ) =
        AlgHom.id k _ := by
      apply MvPolynomial.algHom_ext; intro v
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.id_apply]
      exact hretract v
    change ((MvPolynomial.aeval ψ).comp (MvPolynomial.aeval φ)) p = p
    rw [h]; rfl

  have hφ_deg : ∀ v : Fin di × Fin di, (φ v).totalDegree ≤ 1 := by
    intro ⟨a, b⟩
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    apply Finset.sup_le; intro g _
    calc (C (D.matrixBlockHom i (MonoidAlgebra.of k G g) a b) * X g).totalDegree
        ≤ (C _).totalDegree + (X g).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 0 + 1 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
      _ = 1 := by ring

  have htd_genD : genD.totalDegree = di := by
    apply le_antisymm
    ·
      calc genD.totalDegree
          = (MvPolynomial.aeval ψ (MvPolynomial.aeval φ genD)).totalDegree := by rw [hid]
        _ ≤ (MvPolynomial.aeval φ genD).totalDegree :=
              totalDegree_aeval_le_of_deg_le_one hψ_deg _
        _ = (D.auxiliaryPolynomial i).totalDegree := by rw [← hbp]
        _ = di := D.totalDegree_auxiliaryPolynomial i
    ·
      calc di = (D.auxiliaryPolynomial i).totalDegree := (D.totalDegree_auxiliaryPolynomial i).symm
        _ = (MvPolynomial.aeval φ genD).totalDegree := by rw [← hbp]
        _ ≤ genD.totalDegree := totalDegree_aeval_le_of_deg_le_one hφ_deg _

  have hbp_ne : D.auxiliaryPolynomial i ≠ 0 := by
    intro h; have := D.totalDegree_auxiliaryPolynomial i
    rw [h, MvPolynomial.totalDegree_zero] at this
    exact absurd this.symm (Nat.pos_of_ne_zero (NeZero.ne _)).ne'

  constructor
  ·
    intro h
    have htd := D.totalDegree_auxiliaryPolynomial i
    have hunit_td := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h).2
    have hdi_pos : 0 < di := Nat.pos_of_ne_zero (NeZero.ne _)
    omega
  ·
    intro a b hab
    have ha : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hbp_ne)
    have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hbp_ne)

    have hfact : genD = MvPolynomial.aeval ψ a * MvPolynomial.aeval ψ b := by
      have h1 := congr_arg (MvPolynomial.aeval ψ) (hbp ▸ hab)
      rwa [map_mul, hid] at h1

    have htd_ab : a.totalDegree + b.totalDegree = di := by
      rw [← MvPolynomial.totalDegree_mul_of_isDomain ha hb, ← hab,
        D.totalDegree_auxiliaryPolynomial]


    rcases hirr_gen.isUnit_or_isUnit hfact with hunit | hunit
    ·
      left
      have htd_ψa : (MvPolynomial.aeval ψ a).totalDegree = 0 :=
        (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
      have hψb_ne : MvPolynomial.aeval ψ b ≠ 0 := by
        intro h; rw [h, mul_zero] at hfact; exact hirr_gen.ne_zero hfact
      have htd_ψb : (MvPolynomial.aeval ψ b).totalDegree = di := by
        have := MvPolynomial.totalDegree_mul_of_isDomain hunit.ne_zero hψb_ne
        rw [← hfact, htd_genD] at this; omega
      have : a.totalDegree = 0 := by
        have := totalDegree_aeval_le_of_deg_le_one hψ_deg b; omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp this] at ha ⊢
      have : a.coeff 0 ≠ 0 := by rwa [ne_eq, MvPolynomial.C_eq_zero] at ha
      exact this.isUnit.map MvPolynomial.C
    ·
      right
      have htd_ψb : (MvPolynomial.aeval ψ b).totalDegree = 0 :=
        (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
      have hψa_ne : MvPolynomial.aeval ψ a ≠ 0 := by
        intro h; rw [h, zero_mul] at hfact; exact hirr_gen.ne_zero hfact
      have htd_ψa : (MvPolynomial.aeval ψ a).totalDegree = di := by
        have := MvPolynomial.totalDegree_mul_of_isDomain hψa_ne hunit.ne_zero
        rw [← hfact, htd_genD] at this; omega
      have : b.totalDegree = 0 := by
        have := totalDegree_aeval_le_of_deg_le_one hψ_deg a; omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp this] at hb ⊢
      have : b.coeff 0 ≠ 0 := by rwa [ne_eq, MvPolynomial.C_eq_zero] at hb
      exact this.isUnit.map MvPolynomial.C


/-- Auxiliary polynomials at distinct indices are not associated. -/
@[source_ref "Chapter4/Discussion_proof_Theorem4.10.2/Derived2" (role := supporting)]
lemma RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial_not_associated [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i j : Fin D.count) (hij : i ≠ j) :
    ¬Associated (D.auxiliaryPolynomial i) (D.auxiliaryPolynomial j) := by
  intro ⟨u, hu⟩

  set e := D.groupAlgebraEquivMatrix.symm (Pi.single i (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)) with he_def
  set σ : G → k := fun g => e g with hσ_def

  have ha_eq : ∑ g : G, σ g • MonoidAlgebra.of k G g = e := by
    conv_rhs => rw [show e = MonoidAlgebra.ofCoeff (∑ g : G, Finsupp.single g (e.coeff g)) by
      rw [Finsupp.univ_sum_single, MonoidAlgebra.ofCoeff_coeff]]
    congr 1; ext g
    simp [hσ_def, MonoidAlgebra.of_apply, mul_one]

  have heval_eq : ∀ l : Fin D.count, MvPolynomial.eval σ (D.auxiliaryPolynomial l) =
      (D.matrixBlockHom l e).det := by
    intro l
    unfold RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryPolynomial
    rw [RingHom.map_det]
    congr 1; ext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    conv_rhs => rw [show e = ∑ s : G, σ s • MonoidAlgebra.of k G s from ha_eq.symm]
    simp only [map_sum, D.projRingHom_smul' l, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1; ext g; ring

  have hei : D.matrixBlockHom i e = 1 := by
    simp [he_def, RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.matrixBlockHom, Pi.evalRingHom, Pi.single, Function.update]

  have hej : D.matrixBlockHom j e = 0 := by
    simp [he_def, RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.matrixBlockHom, Pi.evalRingHom, Pi.single, Function.update,
      Ne.symm hij]

  have heval_i : MvPolynomial.eval σ (D.auxiliaryPolynomial i) = 1 := by
    rw [heval_eq, hei, det_one]

  have heval_j : MvPolynomial.eval σ (D.auxiliaryPolynomial j) = 0 := by
    rw [heval_eq, hej]
    haveI := D.dimension_neZero j
    haveI : Nonempty (Fin (D.dimension j)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    exact Matrix.det_zero

  have heval_u : MvPolynomial.eval σ (↑u : MvPolynomial G k) = 0 := by
    have h := congr_arg (MvPolynomial.eval σ) hu
    simp only [map_mul, heval_i, heval_j, one_mul] at h
    exact h

  exact (u.isUnit.map (MvPolynomial.eval σ).toMonoidHom).ne_zero heval_u


private lemma RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.n_eq_card_conjClasses [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) :
    D.count = Fintype.card (ConjClasses G) := by

  have h_center_kG : Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k G)) =
      Fintype.card (ConjClasses G) := by


    have center_conj_inv : ∀ {a : MonoidAlgebra k G},
        a ∈ Subalgebra.center k (MonoidAlgebra k G) → ∀ g h : G, a (g * h * g⁻¹) = a h := by
      intro a ha g h
      rw [Subalgebra.mem_center_iff] at ha
      have key := congr_fun (congr_arg (⇑) (ha (MonoidAlgebra.of k G g))) (g * h)
      change (MonoidAlgebra.single g 1 * a).coeff (g * h) =
        (a * MonoidAlgebra.single g 1).coeff (g * h) at key
      rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply] at key
      simp only [one_mul, mul_one, inv_mul_cancel_left] at key
      exact key.symm
    have conj_inv_center : ∀ (a : MonoidAlgebra k G),
        (∀ g h : G, a (g * h * g⁻¹) = a h) → a ∈ Subalgebra.center k (MonoidAlgebra k G) := by
      intro a ha
      rw [Subalgebra.mem_center_iff]; intro b
      induction b using MonoidAlgebra.induction_on with
      | hM g =>
        ext x
        simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
          MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one]
        have h1 := ha g⁻¹ (x * g⁻¹)
        simp only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h1
        exact h1
      | hadd b₁ b₂ hb₁ hb₂ => rw [mul_add, add_mul, hb₁, hb₂]
      | hsmul r b hb => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hb]
    let fwd : ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₗ[k] (ConjClasses G → k) :=
      { toFun := fun a C => (a : MonoidAlgebra k G) (Quotient.out C)
        map_add' := fun _ _ => funext fun _ => Finsupp.add_apply _ _ _
        map_smul' := fun _ _ => funext fun _ => Finsupp.smul_apply _ _ _ }
    let bwd : (ConjClasses G → k) →ₗ[k] ↥(Subalgebra.center k (MonoidAlgebra k G)) :=
      { toFun := fun f => ⟨MonoidAlgebra.ofCoeff (Finsupp.onFinset Finset.univ
            (fun g => f (ConjClasses.mk g)) (fun _ _ => Finset.mem_univ _)),
          conj_inv_center _ (fun g h => by
            simp only [Finsupp.onFinset_apply]; congr 1
            rw [ConjClasses.mk_eq_mk_iff_isConj]
            exact isConj_iff.mpr ⟨g⁻¹, by group⟩)⟩
        map_add' := fun f₁ f₂ => Subtype.ext (MonoidAlgebra.coeff_injective
          (Finsupp.ext fun g => by simp [Finsupp.onFinset_apply]))
        map_smul' := fun r f => Subtype.ext (MonoidAlgebra.coeff_injective
          (Finsupp.ext fun g => by simp [Finsupp.onFinset_apply])) }
    have hfb : ∀ f, fwd (bwd f) = f := fun f => funext fun C => by
      simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
      congr 1; exact Quotient.out_eq C
    have hbf : ∀ a : ↥(Subalgebra.center k (MonoidAlgebra k G)), bwd (fwd a) = a :=
      fun ⟨a, ha⟩ => by
      ext g
      simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
      have hconj : IsConj (Quotient.out (ConjClasses.mk g) : G) g := by
        have h := Quotient.out_eq (ConjClasses.mk g)
        rw [ConjClasses.quotient_mk_eq_mk] at h
        exact ConjClasses.mk_eq_mk_iff_isConj.mp h
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [show a (Quotient.out (ConjClasses.mk g)) =
          a (c * Quotient.out (ConjClasses.mk g) * c⁻¹) from
        (center_conj_inv ha c _).symm, hc]
    have e : ↥(Subalgebra.center k (MonoidAlgebra k G)) ≃ₗ[k] (ConjClasses G → k) :=
      { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
    have : Module.finrank k (ConjClasses G → k) = Fintype.card (ConjClasses G) :=
      Module.finrank_fintype_fun_eq_card k
    linarith [e.finrank_eq]

  have h_center_pi : Module.finrank k ↥(Subalgebra.center k
      (∀ i : Fin D.count, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)) = D.count := by
    let PiMat := (∀ i : Fin D.count, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)
    let fwd : ↥(Subalgebra.center k PiMat) →ₗ[k] (Fin D.count → k) :=
      { toFun := fun a i =>
          haveI := D.dimension_neZero i
          (a : PiMat) i ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
            ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
        map_add' := fun _ _ => funext fun _ => rfl
        map_smul' := fun _ _ => funext fun _ => rfl }
    let bwd_fun : (Fin D.count → k) → PiMat :=
      fun c i => c i • (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)
    have bwd_mem : ∀ c, bwd_fun c ∈ Subalgebra.center k PiMat := fun c => by
      rw [Subalgebra.mem_center_iff]; intro N; ext i : 1
      change N i * (c i • 1) = (c i • 1) * N i
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    let bwd : (Fin D.count → k) →ₗ[k] ↥(Subalgebra.center k PiMat) :=
      { toFun := fun c => ⟨bwd_fun c, bwd_mem c⟩
        map_add' := fun c₁ c₂ => by
          apply Subtype.ext; funext i
          change (c₁ i + c₂ i) • (1 : Matrix _ _ k) = _
          rw [add_smul]; rfl
        map_smul' := fun r c => by
          apply Subtype.ext; funext i
          change (r * c i) • (1 : Matrix _ _ k) = (r • fun i => c i • (1 : Matrix _ _ k)) i
          simp [Pi.smul_apply, smul_smul] }
    have hfb : ∀ c, fwd (bwd c) = c := fun c => funext fun i => by
      simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
      simp [Matrix.smul_apply]
    have hbf : ∀ x : ↥(Subalgebra.center k PiMat), bwd (fwd x) = x := fun ⟨f, hf⟩ => by
      apply Subtype.ext; ext i a b
      simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
      have hfc : f i ∈ Subalgebra.center k (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) := by
        rw [Subalgebra.mem_center_iff]; intro M
        have hf' : ∀ b : PiMat, b * f = f * b := Subalgebra.mem_center_iff.mp hf
        have h := hf' (Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M)
        have lhs : (Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M * f) i =
            M * f i := by rw [Pi.mul_apply, Pi.single_eq_same]
        have rhs : (f * Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M) i =
            f i * M := by rw [Pi.mul_apply, Pi.single_eq_same]
        rw [show M * f i = (Pi.single (M := fun j => Matrix (Fin (D.dimension j)) (Fin (D.dimension j)) k) i M * f) i
          from lhs.symm, h, rhs]
      rw [Algebra.IsCentral.center_eq_bot] at hfc
      rw [Algebra.mem_bot] at hfc
      obtain ⟨c, hc⟩ := Set.mem_range.mp hfc
      have hfi : f i = c • (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) := by
        rw [← hc, Algebra.algebraMap_eq_smul_one]
      rw [hfi]; simp [Matrix.smul_apply, Matrix.one_apply]
    have e : ↥(Subalgebra.center k PiMat) ≃ₗ[k] (Fin D.count → k) :=
      { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
    have : Module.finrank k (Fin D.count → k) = D.count := by
      rw [Module.finrank_fintype_fun_eq_card k, Fintype.card_fin]
    linarith [e.finrank_eq]

  have h_iso : Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k G)) =
      Module.finrank k ↥(Subalgebra.center k
        (∀ i : Fin D.count, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)) := by
    let e_center : ↥(Subalgebra.center k (MonoidAlgebra k G)) ≃ₗ[k]
        ↥(Subalgebra.center k (∀ i : Fin D.count, Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k)) :=
      { toFun := fun ⟨a, ha⟩ => ⟨D.groupAlgebraEquivMatrix a, by
          rw [Subalgebra.mem_center_iff] at ha ⊢
          intro b; obtain ⟨a', rfl⟩ := D.groupAlgebraEquivMatrix.surjective b
          simp [← map_mul, ha a']⟩
        invFun := fun ⟨b, hb⟩ => ⟨D.groupAlgebraEquivMatrix.symm b, by
          rw [Subalgebra.mem_center_iff] at hb ⊢
          intro a; apply D.groupAlgebraEquivMatrix.injective
          simp [map_mul, hb (D.groupAlgebraEquivMatrix a)]⟩
        left_inv := by intro ⟨a, _⟩; ext; simp
        right_inv := by intro ⟨b, _⟩; ext; simp
        map_add' := by intro ⟨a, _⟩ ⟨b, _⟩; ext; simp [map_add]
        map_smul' := by
          intro r ⟨a, _⟩; apply Subtype.ext
          change D.groupAlgebraEquivMatrix (r • a) = r • D.groupAlgebraEquivMatrix a
          rw [map_smul] }
    exact e_center.finrank_eq

  linarith


/-- The auxiliary group-indexed polynomial factors into powers of pairwise nonassociated irreducible polynomials, with the number of factors equal to the number of conjugacy classes. -/
@[source_ref "Chapter4/Discussion_proof_Theorem4.10.2/Derived3" (role := primary),
  source_ref "Chapter4/Discussion_proof_Theorem4.10.2/Derived4" (role := supporting)]
theorem RepresentationTheory.MvPolynomial.GroupIndexedFactorization.exists_irreducible_factorization_of_auxiliaryGroupPolynomial
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [DecidableEq G]
    [Invertible (Fintype.card G : k)] :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial G k),
      (∀ j, Irreducible (P j)) ∧
      (∀ i j, i ≠ j → ¬Associated (P i) (P j)) ∧
      RepresentationTheory.Group.IndexedPolynomial.groupIndexedPolynomial k G = ∏ j : Fin r, P j ^ (P j).totalDegree ∧
      r = Fintype.card (ConjClasses G) := by

  haveI : NeZero (Nat.card G : k) := by
    refine ⟨?_⟩
    have h : (Nat.card G : k) = (Fintype.card G : k) := by
      simp only [Nat.card_eq_fintype_card]
    rw [h]; exact (isUnit_of_invertible _).ne_zero

  let D := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default (k := k) (G := G)

  set s : k := ((Equiv.Perm.sign (Equiv.inv G) : ℤ) : k) with hs_def
  have hsne : s ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv G)) with h | h <;>
      simp [hs_def, h]


  have hn : 0 < D.count := by
    rw [D.n_eq_card_conjClasses]
    haveI : Nonempty (ConjClasses G) := ⟨ConjClasses.mk 1⟩
    exact Fintype.card_pos
  set j0 : Fin D.count := ⟨0, hn⟩ with hj0_def
  haveI := D.dimension_neZero j0
  have hd0 : 0 < D.dimension j0 := Nat.pos_of_ne_zero (NeZero.ne _)


  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq s hd0
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow hd0.ne'] at hc; exact hsne hc.symm
  have hCc : IsUnit (C c : MvPolynomial G k) := (Ne.isUnit hc0).map MvPolynomial.C

  set P : Fin D.count → MvPolynomial G k :=
    Function.update D.auxiliaryPolynomial j0 (C c * D.auxiliaryPolynomial j0) with hP_def

  have hPassoc : ∀ j, Associated (P j) (D.auxiliaryPolynomial j) := by
    intro j
    by_cases hj : j = j0
    · subst hj; rw [hP_def, Function.update_self]
      exact associated_unit_mul_left _ _ hCc
    · rw [hP_def, Function.update_of_ne hj]

  have hle1 : (C c * D.auxiliaryPolynomial j0).totalDegree ≤ (D.auxiliaryPolynomial j0).totalDegree := by
    have h := totalDegree_mul (C c) (D.auxiliaryPolynomial j0)
    rwa [totalDegree_C, zero_add] at h
  have hle2 : (D.auxiliaryPolynomial j0).totalDegree ≤ (C c * D.auxiliaryPolynomial j0).totalDegree := by
    have hrw : D.auxiliaryPolynomial j0 = C c⁻¹ * (C c * D.auxiliaryPolynomial j0) := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0, C_1, one_mul]
    have h := totalDegree_mul (C c⁻¹) (C c * D.auxiliaryPolynomial j0)
    rw [totalDegree_C, zero_add] at h
    rwa [← hrw] at h
  have hPdeg0 : (C c * D.auxiliaryPolynomial j0).totalDegree = (D.auxiliaryPolynomial j0).totalDegree :=
    le_antisymm hle1 hle2

  have hexp : ∀ j, (P j).totalDegree = D.dimension j := by
    intro j
    by_cases hj : j = j0
    · subst hj; rw [hP_def, Function.update_self, hPdeg0, D.totalDegree_auxiliaryPolynomial]
    · rw [hP_def, Function.update_of_ne hj, D.totalDegree_auxiliaryPolynomial]

  refine ⟨D.count, P, ?_, ?_, ?_, D.n_eq_card_conjClasses⟩
  ·
    intro j
    by_cases hj : j = j0
    · subst hj; rw [hP_def, Function.update_self]
      exact (irreducible_isUnit_mul hCc).mpr (D.auxiliaryPolynomial_irreducible j0)
    · rw [hP_def, Function.update_of_ne hj]; exact D.auxiliaryPolynomial_irreducible j
  ·
    intro i j hij hassoc
    exact D.auxiliaryPolynomial_not_associated i j hij
      (((hPassoc i).symm.trans hassoc).trans (hPassoc j))
  ·
    have hprodexp : (∏ j : Fin D.count, P j ^ (P j).totalDegree)
        = ∏ j : Fin D.count, P j ^ D.dimension j :=
      Finset.prod_congr rfl (fun j _ => by rw [hexp j])
    have hPj0 : P j0 = C c * D.auxiliaryPolynomial j0 := by rw [hP_def, Function.update_self]
    have herase : (∏ j ∈ Finset.univ.erase j0, P j ^ D.dimension j)
        = ∏ j ∈ Finset.univ.erase j0, D.auxiliaryPolynomial j ^ D.dimension j :=
      Finset.prod_congr rfl (fun j hj => by
        rw [hP_def, Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    rw [D.auxiliaryGroupPolynomial_eq_sign_smul_prod_auxiliaryPolynomial_pow, ← hs_def, hprodexp]
    symm
    calc ∏ j : Fin D.count, P j ^ D.dimension j
        = P j0 ^ D.dimension j0 * ∏ j ∈ Finset.univ.erase j0, P j ^ D.dimension j :=
          (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0)).symm
      _ = (C c * D.auxiliaryPolynomial j0) ^ D.dimension j0 *
            ∏ j ∈ Finset.univ.erase j0, D.auxiliaryPolynomial j ^ D.dimension j := by rw [hPj0, herase]
      _ = C s * (D.auxiliaryPolynomial j0 ^ D.dimension j0 *
            ∏ j ∈ Finset.univ.erase j0, D.auxiliaryPolynomial j ^ D.dimension j) := by
          rw [mul_pow, ← C_pow, hc, mul_assoc]
      _ = C s * ∏ j : Fin D.count, D.auxiliaryPolynomial j ^ D.dimension j := by
          rw [Finset.mul_prod_erase Finset.univ (fun j => D.auxiliaryPolynomial j ^ D.dimension j)
            (Finset.mem_univ j0)]
      _ = s • ∏ j : Fin D.count, D.auxiliaryPolynomial j ^ D.dimension j := C_mul'
