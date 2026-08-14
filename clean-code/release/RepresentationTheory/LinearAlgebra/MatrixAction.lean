/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib
import RepresentationTheory.Auxiliary.MutualCentralizers

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.cdot false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open MvPolynomial RepresentationTheory.Auxiliary.MutualCentralizers

namespace RepresentationTheory.LinearAlgebra.MatrixAction

universe u

variable (k : Type u) [Field k] (N n : ℕ)

/-- An auxiliary factor type indexed by a field and a natural number. -/
abbrev AuxiliaryFactor (k : Type u) [Field k] (N : ℕ) : Type u := Fin N → k

/-- A module basis for the auxiliary factor type indexed by a finite type. -/
noncomputable abbrev auxiliaryFactorBasis : Module.Basis (Fin N) k (AuxiliaryFactor k N) := Pi.basisFun k (Fin N)

/-- A module basis for the dual of the auxiliary factor type indexed by a finite type. -/
noncomputable def auxiliaryFactorDualBasis : Module.Basis (Fin N) k (Module.Dual k (AuxiliaryFactor k N)) :=
  (auxiliaryFactorBasis k N).dualBasis

/-- An auxiliary type indexed by a field and two natural numbers. -/
abbrev Auxiliary : Type u :=
  auxiliarySpace k (AuxiliaryFactor k N) n ⊗[k] auxiliarySpace k (Module.Dual k (AuxiliaryFactor k N)) n

/-- Constructs an auxiliary element from a length-indexed family of pairs. -/
noncomputable def ofFinPair (f : Fin n → Fin N × Fin N) : Auxiliary k N n :=
  (PiTensorProduct.tprod k (fun i => auxiliaryFactorBasis k N (f i).2)) ⊗ₜ[k]
    (PiTensorProduct.tprod k (fun i => auxiliaryFactorDualBasis k N (f i).1))

/-- Constructs an auxiliary element from a length-indexed family of pairs. -/
noncomputable def symmetricOfFinPair (f : Fin n → Fin N × Fin N) : Auxiliary k N n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), ofFinPair k N n (f ∘ σ)

/-- The pair-family construction is unchanged after precomposition by a permutation of its finite index type. -/
lemma symmetricOfFinPair_perm (f : Fin n → Fin N × Fin N) (τ : Equiv.Perm (Fin n)) :
    symmetricOfFinPair k N n (f ∘ τ) = symmetricOfFinPair k N n f := by
  unfold symmetricOfFinPair
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ ?_
  intro σ
  simp only [Equiv.coe_mulLeft]
  rfl

/-- Enumerates a finitely supported family of pairs whose coefficients have prescribed total sum. -/
noncomputable def finsuppToFin (s : (Fin N × Fin N) →₀ ℕ)
    (hs : s.sum (fun _ => id) = n) : Fin n → Fin N × Fin N := fun i =>
  (Finsupp.toMultiset s).toList.get ⟨i.val, by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hs ▸ i.isLt⟩

/-- Constructs an auxiliary element from a finitely supported natural-valued family of pairs. -/
noncomputable def finsuppToAuxiliary (s : (Fin N × Fin N) →₀ ℕ) : Auxiliary k N n :=
  if hs : s.sum (fun _ => id) = n then symmetricOfFinPair k N n (finsuppToFin N n s hs) else 0

/-- A linear map from multivariate polynomials to an auxiliary type at a fixed degree. -/
noncomputable def polynomialToAuxiliary :
    MvPolynomial (Fin N × Fin N) k →ₗ[k] Auxiliary k N n :=
  (MvPolynomial.basisMonomials _ _).constr k (finsuppToAuxiliary k N n)

/-- A linear map from homogeneous multivariate polynomials of a fixed degree to an auxiliary type. -/
noncomputable def homogeneousToAuxiliary :
    MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n →ₗ[k] Auxiliary k N n :=
  (polynomialToAuxiliary k N n).comp
    (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n).subtype

/-- A module basis for the auxiliary type indexed by pairs of finite-indexed functions. -/
noncomputable def Auxiliary.basis :
    Module.Basis ((Fin n → Fin N) × (Fin n → Fin N)) k (Auxiliary k N n) :=
  (Basis.piTensorProduct (fun _ : Fin n => auxiliaryFactorBasis k N)).tensorProduct
    (Basis.piTensorProduct (fun _ : Fin n => auxiliaryFactorDualBasis k N))

/-- A linear map from the auxiliary type to multivariate polynomials. -/
noncomputable def auxiliaryToPolynomial :
    Auxiliary k N n →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  (Auxiliary.basis k N n).constr k fun ij =>
    ∏ l : Fin n, MvPolynomial.X (R := k) (ij.2 l, ij.1 l)

/-- Computes an auxiliary basis vector as the tensor product of a Pi tensor product of auxiliary-factor basis vectors and a Pi tensor product of auxiliary-factor dual-basis vectors. -/
@[simp]
lemma Auxiliary.basis_apply (ij : (Fin n → Fin N) × (Fin n → Fin N)) :
    Auxiliary.basis k N n ij =
      (PiTensorProduct.tprod k (fun l => auxiliaryFactorBasis k N (ij.1 l))) ⊗ₜ[k]
        (PiTensorProduct.tprod k (fun l => auxiliaryFactorDualBasis k N (ij.2 l))) := by
  simp [Auxiliary.basis, Module.Basis.tensorProduct_apply']

/-- Expresses the auxiliary element from a pair family in the module basis indexed by the two coordinate functions in reversed order. -/
lemma ofFinPair_eq_basis (f : Fin n → Fin N × Fin N) :
    ofFinPair k N n f = Auxiliary.basis k N n (fun l => (f l).2, fun l => (f l).1) := by
  simp [ofFinPair, Auxiliary.basis_apply]

/-- Computes the polynomial image of the auxiliary element constructed from a pair family. -/
lemma auxiliaryToPolynomial_ofFinPair (f : Fin n → Fin N × Fin N) :
    auxiliaryToPolynomial k N n (ofFinPair k N n f) = ∏ l : Fin n, MvPolynomial.X (R := k) (f l) := by
  rw [show ofFinPair k N n f =
        Auxiliary.basis k N n (fun l => (f l).2, fun l => (f l).1) from
      by simp [ofFinPair, Auxiliary.basis_apply]]
  unfold auxiliaryToPolynomial
  rw [Module.Basis.constr_basis]

variable [CharZero k]

/-- Computes the polynomial image of the permutation-invariant pair-family construction. -/
lemma auxiliaryToPolynomial_symmetricOfFinPair (f : Fin n → Fin N × Fin N) :
    auxiliaryToPolynomial k N n (symmetricOfFinPair k N n f) = ∏ l : Fin n, MvPolynomial.X (R := k) (f l) := by
  unfold symmetricOfFinPair
  rw [LinearMap.map_smul, map_sum]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      auxiliaryToPolynomial k N n (ofFinPair k N n (f ∘ σ)) =
        ∏ l : Fin n, MvPolynomial.X (R := k) (f l) := by
    intro σ
    rw [auxiliaryToPolynomial_ofFinPair]

    exact Fintype.prod_equiv σ _ _ (fun _ => rfl)
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

omit [CharZero k] in

/-- Identifies a product of variables indexed by a finite-support enumeration with the corresponding coefficient-one monomial. -/
lemma prod_X_finsuppToFin (s : (Fin N × Fin N) →₀ ℕ) (hs : s.sum (fun _ => id) = n) :
    (∏ l : Fin n, MvPolynomial.X (R := k) (finsuppToFin N n s hs l)) =
      MvPolynomial.monomial s (1 : k) := by
  classical

  rw [← List.prod_ofFn (f := fun l : Fin n => MvPolynomial.X (R := k)
        (finsuppToFin N n s hs l))]

  have hcard : Multiset.card (Finsupp.toMultiset s) = n := by
    rw [Finsupp.card_toMultiset]; exact hs

  have hmap : (List.ofFn fun l : Fin n =>
      MvPolynomial.X (R := k) (finsuppToFin N n s hs l)) =
    (Finsupp.toMultiset s).toList.map (MvPolynomial.X (R := k)) := by
    apply List.ext_getElem
    · simp [Multiset.length_toList, hcard]
    · intro i h1 h2
      simp [finsuppToFin, List.getElem_ofFn, List.getElem_map]
  rw [hmap]

  rw [show ((Finsupp.toMultiset s).toList.map (MvPolynomial.X (R := k))).prod =
         ((Finsupp.toMultiset s).map (MvPolynomial.X (R := k))).prod from by
    conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset s)]
    rw [Multiset.map_coe, Multiset.prod_coe]]

  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index_inj MvPolynomial.X_injective]

  exact MvPolynomial.prod_X_pow_eq_monomial

/-- Computes the polynomial image of an auxiliary element from finite support, with zero outside the specified total degree. -/
lemma auxiliaryToPolynomial_finsuppToAuxiliary (s : (Fin N × Fin N) →₀ ℕ) :
    auxiliaryToPolynomial k N n (finsuppToAuxiliary k N n s) =
      if s.sum (fun _ => id) = n then MvPolynomial.monomial s (1 : k) else 0 := by
  unfold finsuppToAuxiliary
  split_ifs with hs
  · rw [auxiliaryToPolynomial_symmetricOfFinPair, prod_X_finsuppToFin (k := k) (N := N) (n := n) s hs]
  · simp

/-- The composite of the two displayed linear maps is the identity on homogeneous polynomials of the specified degree. -/
lemma auxiliaryToPolynomial_comp_polynomialToAuxiliary (p : MvPolynomial (Fin N × Fin N) k)
    (hp : p.IsHomogeneous n) :
    auxiliaryToPolynomial k N n (polynomialToAuxiliary k N n p) = p := by
  classical

  conv_rhs => rw [p.as_sum]
  rw [show auxiliaryToPolynomial k N n (polynomialToAuxiliary k N n p) =
      auxiliaryToPolynomial k N n (polynomialToAuxiliary k N n
        (∑ v ∈ p.support, MvPolynomial.monomial v (MvPolynomial.coeff v p))) from by
    congr 2; exact p.as_sum]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs

  have hcoeff_ne : MvPolynomial.coeff s p ≠ 0 := MvPolynomial.mem_support_iff.mp hs

  have hsn : s.sum (fun _ => id) = n := by
    have hw := hp hcoeff_ne

    rw [Finsupp.weight_apply] at hw

    simp only [Pi.one_apply, smul_eq_mul, mul_one] at hw
    exact hw

  rw [show MvPolynomial.monomial s (MvPolynomial.coeff s p) =
        MvPolynomial.coeff s p • MvPolynomial.monomial s (1 : k) from by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [LinearMap.map_smul, LinearMap.map_smul]
  congr 1

  rw [show polynomialToAuxiliary k N n (MvPolynomial.monomial s 1) = finsuppToAuxiliary k N n s from by
    unfold polynomialToAuxiliary
    rw [show (MvPolynomial.monomial s 1 : MvPolynomial (Fin N × Fin N) k) =
         MvPolynomial.basisMonomials (Fin N × Fin N) k s from rfl,
      Module.Basis.constr_basis]]
  rw [auxiliaryToPolynomial_finsuppToAuxiliary, if_pos hsn]

/-- The linear map from homogeneous polynomials to the auxiliary type is injective. -/
theorem homogeneousToAuxiliary_injective :
    Function.Injective (homogeneousToAuxiliary k N n) := by
  intro p q hpq
  apply Subtype.ext
  have hp := auxiliaryToPolynomial_comp_polynomialToAuxiliary k N n p.val p.property
  have hq := auxiliaryToPolynomial_comp_polynomialToAuxiliary k N n q.val q.property
  have heq : auxiliaryToPolynomial k N n (polynomialToAuxiliary k N n p.val) =
      auxiliaryToPolynomial k N n (polynomialToAuxiliary k N n q.val) := by
    unfold homogeneousToAuxiliary at hpq
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hpq
    rw [hpq]
  rw [hp, hq] at heq
  exact heq

omit [CharZero k] in

/-- The multivariate-polynomial algebra homomorphism induced by right multiplication on the second coordinate by a square matrix. -/
noncomputable def secondCoordinateMatrixAlgHom (g : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval fun ij : Fin N × Fin N =>
    ∑ l : Fin N, MvPolynomial.X (R := k) (ij.1, l) * MvPolynomial.C (g l ij.2)

omit [CharZero k] in

/-- The linear endomorphism of the auxiliary type induced by the column action of a square matrix on its second factor. -/
noncomputable def secondFactorMatrixAction (g : Matrix (Fin N) (Fin N) k) :
    Auxiliary k N n →ₗ[k] Auxiliary k N n :=
  TensorProduct.map (PiTensorProduct.map fun _ : Fin n => g.toLin') LinearMap.id

omit [CharZero k] in

/-- Computes Matrix.toLin' on an auxiliary-factor basis vector as the sum of basis vectors with coefficients from the corresponding matrix column. -/
lemma Matrix.toLin'_apply_auxiliaryFactorBasis (g : Matrix (Fin N) (Fin N) k) (j : Fin N) :
    Matrix.toLin' g (auxiliaryFactorBasis k N j) = ∑ b : Fin N, g b j • auxiliaryFactorBasis k N b := by
  classical
  ext i
  rw [auxiliaryFactorBasis, Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single,
    MulOpposite.op_one, one_smul]
  simp only [Matrix.col_apply, Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [CharZero k] in

/-- Expands the second-factor matrix action on an auxiliary element constructed from a pair family. -/
lemma secondFactorMatrixAction_ofFinPair (g : Matrix (Fin N) (Fin N) k) (f : Fin n → Fin N × Fin N) :
    secondFactorMatrixAction k N n g (ofFinPair k N n f) =
      ∑ b : Fin n → Fin N, (∏ l, g (b l) (f l).2) •
        ofFinPair k N n (fun l => ((f l).1, b l)) := by
  classical
  unfold secondFactorMatrixAction ofFinPair
  rw [TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod]

  simp_rw [Matrix.toLin'_apply_auxiliaryFactorBasis]

  rw [MultilinearMap.map_sum (PiTensorProduct.tprod k)
        (g := fun (l : Fin n) (b : Fin N) => g b (f l).2 • auxiliaryFactorBasis k N b)]

  simp_rw [MultilinearMap.map_smul_univ (PiTensorProduct.tprod k)]

  rw [TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [TensorProduct.smul_tmul']

omit [CharZero k] in

/-- Expands the second-factor matrix action on the permutation-invariant pair-family construction. -/
lemma secondFactorMatrixAction_symmetricOfFinPair (g : Matrix (Fin N) (Fin N) k) (f : Fin n → Fin N × Fin N) :
    secondFactorMatrixAction k N n g (symmetricOfFinPair k N n f) =
      ∑ c : Fin n → Fin N, (∏ l, g (c l) (f l).2) •
        symmetricOfFinPair k N n (fun l => ((f l).1, c l)) := by
  classical

  unfold symmetricOfFinPair
  rw [LinearMap.map_smul, map_sum]
  simp_rw [secondFactorMatrixAction_ofFinPair]

  simp_rw [smul_comm _ ((n.factorial : k)⁻¹), ← Finset.smul_sum]
  congr 1

  simp_rw [Finset.smul_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Fin N)))]
  refine Finset.sum_congr rfl fun τ _ => ?_

  refine Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl (Fin N))) _ _ ?_
  intro b
  simp only [Function.comp_apply]
  congr 1
  ·
    refine Fintype.prod_equiv τ _ _ ?_
    intro l
    simp [Equiv.arrowCongr_apply]
  ·
    congr 1
    funext l
    simp [Equiv.arrowCongr_apply]

omit [CharZero k] in

private lemma prod_X_eq_monomial_fn (f : Fin n → Fin N × Fin N) :
    (∏ l : Fin n, MvPolynomial.X (R := k) (f l)) =
      MvPolynomial.monomial (∑ l : Fin n, Finsupp.single (f l) 1) (1 : k) := by
  classical
  have key : ∀ s : Finset (Fin n),
      (∏ l ∈ s, MvPolynomial.X (R := k) (f l)) =
        MvPolynomial.monomial (∑ l ∈ s, Finsupp.single (f l) 1) (1 : k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.sum_insert has, ih,
        show MvPolynomial.X (R := k) (f a) =
            MvPolynomial.monomial (Finsupp.single (f a) 1) (1 : k) from rfl,
        MvPolynomial.monomial_mul, mul_one]
  exact key _

omit [CharZero k] in

/-- Computes the image of a polynomial variable under the second-coordinate matrix algebra homomorphism. -/
@[simp]
lemma secondCoordinateMatrixAlgHom_X (g : Matrix (Fin N) (Fin N) k) (ij : Fin N × Fin N) :
    secondCoordinateMatrixAlgHom k N g (MvPolynomial.X ij) =
      ∑ l : Fin N,
        MvPolynomial.X (R := k) (ij.1, l) * MvPolynomial.C (g l ij.2) := by
  unfold secondCoordinateMatrixAlgHom
  rw [MvPolynomial.aeval_X]

omit [CharZero k] in

/-- Expands the image of a finite product of polynomial variables under the second-coordinate matrix algebra homomorphism. -/
lemma secondCoordinateMatrixAlgHom_prod_X (g : Matrix (Fin N) (Fin N) k) (f : Fin n → Fin N × Fin N) :
    secondCoordinateMatrixAlgHom k N g (∏ l : Fin n, MvPolynomial.X (R := k) (f l)) =
      ∑ c : Fin n → Fin N,
        MvPolynomial.C (∏ l : Fin n, g (c l) (f l).2) *
          (∏ l : Fin n, MvPolynomial.X (R := k) ((f l).1, c l)) := by
  classical
  rw [map_prod]
  simp_rw [secondCoordinateMatrixAlgHom_X]

  rw [Finset.prod_univ_sum
    (t := fun (_ : Fin n) => (Finset.univ : Finset (Fin N)))
    (f := fun l j => MvPolynomial.X (R := k) ((f l).1, j) *
                     MvPolynomial.C (g j (f l).2))]
  rw [show (Fintype.piFinset fun (_ : Fin n) => (Finset.univ : Finset (Fin N))) =
        (Finset.univ : Finset (Fin n → Fin N)) from Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun c _ => ?_

  rw [Finset.prod_mul_distrib]
  rw [show (∏ l : Fin n, MvPolynomial.C (R := k) (g (c l) (f l).2)) =
      MvPolynomial.C (∏ l : Fin n, g (c l) (f l).2) from

    (map_prod (M := k) (MvPolynomial.C (R := k) (σ := Fin N × Fin N)) _ _).symm]
  ring

private noncomputable def matchingPerm {α : Type*} [DecidableEq α] :
    ∀ {n : ℕ} (f g : Fin n → α),
      Multiset.map f (Finset.univ : Finset (Fin n)).val =
        Multiset.map g (Finset.univ : Finset (Fin n)).val →
      {σ : Equiv.Perm (Fin n) // g = f ∘ σ}
  | 0, _, g, _ => ⟨Equiv.refl _, funext fun i => i.elim0⟩
  | n + 1, f, g, h =>
      let hg0_mem : g 0 ∈ Multiset.map f (Finset.univ : Finset (Fin (n+1))).val := by
        rw [h]; exact Multiset.mem_map.mpr ⟨0, Finset.mem_univ_val _, rfl⟩
      let l₀ : Fin (n+1) := Classical.choose (Multiset.mem_map.mp hg0_mem)
      let l₀_spec :
        l₀ ∈ (Finset.univ : Finset (Fin (n+1))).val ∧ f l₀ = g 0 :=
        Classical.choose_spec (Multiset.mem_map.mp hg0_mem)
      let hl₀ : f l₀ = g 0 := l₀_spec.2
      let f' : Fin n → α := f ∘ l₀.succAbove
      let g' : Fin n → α := g ∘ Fin.succ
      let hpeel_f : Multiset.map f (Finset.univ : Finset (Fin (n+1))).val =
          f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin n)).val := by
        conv_lhs => rw [Fin.univ_succAbove n l₀]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb]
        rfl
      let hpeel_g : Multiset.map g (Finset.univ : Finset (Fin (n+1))).val =
          g 0 ::ₘ Multiset.map g' (Finset.univ : Finset (Fin n)).val := by
        conv_lhs => rw [Fin.univ_succAbove n 0]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb, Fin.succAbove_zero]
        rfl
      let hms : Multiset.map f' (Finset.univ : Finset (Fin n)).val =
          Multiset.map g' (Finset.univ : Finset (Fin n)).val := by
        have hh : f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin n)).val =
            f l₀ ::ₘ Multiset.map g' (Finset.univ : Finset (Fin n)).val := by
          rw [← hpeel_f, h, hpeel_g, hl₀]
        exact (Multiset.cons_inj_right _).mp hh
      let σ'_pkg := matchingPerm f' g' hms
      let σ' : Equiv.Perm (Fin n) := σ'_pkg.1
      let hσ' : g' = f' ∘ σ' := σ'_pkg.2
      let σ_fn : Fin (n+1) → Fin (n+1) :=
        Fin.cases l₀ (fun j => l₀.succAbove (σ' j))
      let hinj : Function.Injective σ_fn := by
        intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => rfl
          | succ b =>
            exfalso
            change l₀ = l₀.succAbove (σ' b) at hij
            exact (Fin.succAbove_ne l₀ (σ' b)) hij.symm
        | succ a =>
          induction j using Fin.cases with
          | zero =>
            exfalso
            change l₀.succAbove (σ' a) = l₀ at hij
            exact (Fin.succAbove_ne l₀ (σ' a)) hij
          | succ b =>
            change l₀.succAbove (σ' a) = l₀.succAbove (σ' b) at hij
            have h1 : σ' a = σ' b := l₀.succAbove_right_injective hij
            have h2 : a = b := σ'.injective h1
            exact congrArg Fin.succ h2
      let hbij : Function.Bijective σ_fn :=
        Finite.injective_iff_bijective.mp hinj
      ⟨Equiv.ofBijective σ_fn hbij, by
        funext i
        induction i using Fin.cases with
        | zero =>
          change g 0 = f (σ_fn 0)
          change g 0 = f l₀
          exact hl₀.symm
        | succ j =>
          change g (Fin.succ j) = f (σ_fn (Fin.succ j))
          change g (Fin.succ j) = f (l₀.succAbove (σ' j))
          have := congrFun hσ' j
          change g' j = f' (σ' j)
          exact this⟩

omit [CharZero k] in

/-- Equal multisets of pair-family values give equal auxiliary elements. -/
lemma symmetricOfFinPair_eq_of_multiset_eq (f g : Fin n → Fin N × Fin N)
    (h : Multiset.map f (Finset.univ : Finset (Fin n)).val =
         Multiset.map g (Finset.univ : Finset (Fin n)).val) :
    symmetricOfFinPair k N n f = symmetricOfFinPair k N n g := by
  classical
  obtain ⟨σ, hσ⟩ := matchingPerm f g h
  rw [hσ, symmetricOfFinPair_perm]

omit [CharZero k] in

private lemma toMultiset_sum_single_fn {α : Type*} (g : Fin n → α) :
    Finsupp.toMultiset (∑ l : Fin n, Finsupp.single (g l) (1 : ℕ)) =
      Multiset.map g (Finset.univ : Finset (Fin n)).val := by
  classical
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]

  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Finset.insert_val, Multiset.ndinsert_of_notMem ha,
      Multiset.map_cons, Multiset.singleton_add]

/-- Evaluates the polynomial-to-auxiliary map on a finite product of variables. -/
lemma polynomialToAuxiliary_prod_X (f : Fin n → Fin N × Fin N) :
    polynomialToAuxiliary k N n (∏ l : Fin n, MvPolynomial.X (R := k) (f l)) =
      symmetricOfFinPair k N n f := by
  classical
  rw [prod_X_eq_monomial_fn]
  set s : (Fin N × Fin N) →₀ ℕ := ∑ l : Fin n, Finsupp.single (f l) 1 with hs_def

  have hpt : polynomialToAuxiliary k N n (MvPolynomial.monomial s 1) = finsuppToAuxiliary k N n s := by
    unfold polynomialToAuxiliary
    rw [show (MvPolynomial.monomial s 1 : MvPolynomial (Fin N × Fin N) k) =
         MvPolynomial.basisMonomials (Fin N × Fin N) k s from rfl,
       Module.Basis.constr_basis]
  rw [hpt]

  have hf_multi : Finsupp.toMultiset s = Multiset.map f (Finset.univ : Finset (Fin n)).val := by
    rw [hs_def]; exact toMultiset_sum_single_fn n f

  have hsn : s.sum (fun _ => id) = n := by
    have hcard := congrArg Multiset.card hf_multi
    rw [Finsupp.card_toMultiset] at hcard
    rw [hcard]; simp
  unfold finsuppToAuxiliary
  rw [dif_pos hsn]

  refine symmetricOfFinPair_eq_of_multiset_eq k N n _ _ ?_

  have hcard : Multiset.card (Finsupp.toMultiset s) = n := by
    rw [Finsupp.card_toMultiset]; exact hsn
  have hofFn : List.ofFn (finsuppToFin N n s hsn) = (Finsupp.toMultiset s).toList := by
    apply List.ext_getElem
    · simp [Multiset.length_toList, hcard]
    · intro i h1 h2
      simp [finsuppToFin]
  have huniv_map : Multiset.map (finsuppToFin N n s hsn)
      (Finset.univ : Finset (Fin n)).val =
      ((List.ofFn (finsuppToFin N n s hsn) : List _) : Multiset _) := by
    rw [show (Finset.univ : Finset (Fin n)).val = ((List.finRange n : List _) : Multiset _) from by
      simp [List.finRange]; rfl]
    rw [Multiset.map_coe, ← List.ofFn_eq_map]
  rw [huniv_map, hofFn, Multiset.coe_toList, hf_multi]

omit [CharZero k] in

/-- The second-coordinate matrix algebra homomorphism preserves homogeneous degree. -/
lemma secondCoordinateMatrixAlgHom_isHomogeneous (g : Matrix (Fin N) (Fin N) k) {m : ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p.IsHomogeneous m) :
    (secondCoordinateMatrixAlgHom k N g p).IsHomogeneous m := by
  have hgens : ∀ ij : Fin N × Fin N,
      (∑ l : Fin N,
          MvPolynomial.X (R := k) (ij.1, l) * MvPolynomial.C (g l ij.2)).IsHomogeneous 1 := by
    intro ij
    refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
    intro l _
    have := MvPolynomial.IsHomogeneous.mul (MvPolynomial.isHomogeneous_X (R := k) (ij.1, l))
      (MvPolynomial.isHomogeneous_C (σ := Fin N × Fin N) (g l ij.2))
    simpa using this
  have h := hp.aeval (fun ij => ∑ l : Fin N, MvPolynomial.X (R := k) (ij.1, l) *
    MvPolynomial.C (g l ij.2)) hgens
  simpa [secondCoordinateMatrixAlgHom, one_mul] using h

/-- The polynomial-to-auxiliary map commutes with the displayed matrix-induced maps on homogeneous inputs. -/
theorem polynomialToAuxiliary_commutes (g : Matrix (Fin N) (Fin N) k)
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p.IsHomogeneous n) :
    polynomialToAuxiliary k N n (secondCoordinateMatrixAlgHom k N g p) =
      secondFactorMatrixAction k N n g (polynomialToAuxiliary k N n p) := by
  classical

  conv_lhs => rw [p.as_sum, map_sum (secondCoordinateMatrixAlgHom k N g), map_sum (polynomialToAuxiliary k N n)]
  conv_rhs => rw [p.as_sum, map_sum (polynomialToAuxiliary k N n), map_sum (secondFactorMatrixAction k N n g)]
  apply Finset.sum_congr rfl
  intro s hs

  have hsn : s.sum (fun _ => id) = n := by
    have hcoeff : MvPolynomial.coeff s p ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hw := hp hcoeff
    rw [Finsupp.weight_apply] at hw

    simp only [Pi.one_apply, smul_eq_mul, mul_one] at hw
    exact hw

  rw [show MvPolynomial.monomial s (MvPolynomial.coeff s p) =
        (MvPolynomial.coeff s p) • MvPolynomial.monomial s (1 : k) from by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul (secondCoordinateMatrixAlgHom k N g), map_smul (polynomialToAuxiliary k N n),
      map_smul (polynomialToAuxiliary k N n), map_smul (secondFactorMatrixAction k N n g)]
  congr 1

  rw [show MvPolynomial.monomial s (1 : k) =
        ∏ l : Fin n, MvPolynomial.X (R := k) (finsuppToFin N n s hsn l) from
      (prod_X_finsuppToFin (k := k) (N := N) (n := n) s hsn).symm]
  set f := finsuppToFin N n s hsn with hf_def
  rw [secondCoordinateMatrixAlgHom_prod_X, map_sum]

  have step : ∀ c : Fin n → Fin N,
      polynomialToAuxiliary k N n (MvPolynomial.C (R := k) (∏ l, g (c l) (f l).2) *
          (∏ l, MvPolynomial.X (R := k) ((f l).1, c l))) =
        (∏ l, g (c l) (f l).2) • symmetricOfFinPair k N n (fun l => ((f l).1, c l)) := by
    intro c
    rw [show MvPolynomial.C (R := k) (∏ l, g (c l) (f l).2) *
          (∏ l, MvPolynomial.X (R := k) ((f l).1, c l)) =
        (∏ l, g (c l) (f l).2) • (∏ l, MvPolynomial.X (R := k) ((f l).1, c l)) from
      (MvPolynomial.smul_eq_C_mul _ _).symm]
    rw [LinearMap.map_smul, polynomialToAuxiliary_prod_X]
  simp_rw [step]

  rw [polynomialToAuxiliary_prod_X, secondFactorMatrixAction_symmetricOfFinPair]

/-- The homogeneous-polynomial linear map commutes with the displayed matrix-induced maps. -/
theorem homogeneousToAuxiliary_commutes (g : Matrix (Fin N) (Fin N) k)
    (p : MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n) :
    homogeneousToAuxiliary k N n
        ⟨secondCoordinateMatrixAlgHom k N g p.val,
          secondCoordinateMatrixAlgHom_isHomogeneous (k := k) (N := N) (m := n) g p.property⟩ =
      secondFactorMatrixAction k N n g (homogeneousToAuxiliary k N n p) := by
  unfold homogeneousToAuxiliary
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  exact polynomialToAuxiliary_commutes (k := k) (N := N) (n := n) g p.property

end RepresentationTheory.LinearAlgebra.MatrixAction
