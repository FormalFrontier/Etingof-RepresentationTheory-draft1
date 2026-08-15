/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.PolynomialEvaluationModules
import RepresentationTheory.Alignment.Attribute
import Mathlib.Algebra.DualNumber

/-! # Two-Dimensional Polynomial Modules

Normal forms and isomorphism criteria for two-dimensional modules over a finite-variable
complex polynomial algebra.
-/

namespace RepresentationTheory.Algebra.Module.TwoDimensionalPolynomialModules

open RepresentationTheory.Algebra.Module.PolynomialEvaluationModules
open MvPolynomial
open DualNumber

/-! ## The generators as `ℂ`-linear endomorphisms -/

section GenEnd

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (PolynomialAlgebra n) M]
  [IsScalarTower ℂ (PolynomialAlgebra n) M]

/-- Polynomial-algebra and complex scalar multiplication commute on a compatible module. -/
lemma polynomialComplexSmulCommClass : SMulCommClass (PolynomialAlgebra n) ℂ M :=
  ⟨fun q r m => by
    rw [← algebraMap_smul (PolynomialAlgebra n) r m, ← mul_smul, ← algebraMap_smul (PolynomialAlgebra n) r (q • m),
      ← mul_smul, Algebra.commutes]⟩

/-- The complex-linear endomorphism given by the action of a polynomial generator. -/
noncomputable def generatorAction (i : Fin n) : Module.End ℂ M :=
  letI := polynomialComplexSmulCommClass (n := n) (M := M)
  { toFun := fun m => (X i : PolynomialAlgebra n) • m
    map_add' := fun x y => smul_add _ _ _
    map_smul' := fun r m => by
      simp only [RingHom.id_apply]
      exact smul_comm (X i : PolynomialAlgebra n) r m }

/-- The generator-action endomorphism evaluates as scalar multiplication by the corresponding polynomial variable. -/
@[simp] lemma generatorAction_apply (i : Fin n) (m : M) : generatorAction i m = (X i : PolynomialAlgebra n) • m := rfl

end GenEnd

/-! ## `ℂ`-linear equivalences commuting with the generators are `A`-linear -/

/-- A complex-linear equivalence that intertwines every polynomial generator action induces a polynomial-linear equivalence. -/
theorem nonempty_polynomialLinearEquiv_of_map_X_smul {n : ℕ} {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [Module (PolynomialAlgebra n) M] [IsScalarTower ℂ (PolynomialAlgebra n) M]
    [AddCommGroup N] [Module ℂ N] [Module (PolynomialAlgebra n) N] [IsScalarTower ℂ (PolynomialAlgebra n) N]
    (e : M ≃ₗ[ℂ] N)
    (h : ∀ (i : Fin n) (m : M), e ((X i : PolynomialAlgebra n) • m) = (X i : PolynomialAlgebra n) • e m) :
    Nonempty (M ≃ₗ[PolynomialAlgebra n] N) := by
  have key : ∀ (p : PolynomialAlgebra n) (m : M), e (p • m) = p • e m := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      intro m
      rw [← MvPolynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul]
    | add p q hp hq => intro m; rw [add_smul, map_add, hp, hq, add_smul]
    | mul_X p i hp => intro m; rw [mul_smul, hp, h, ← mul_smul]
  exact ⟨{ e with map_smul' := key }⟩

/-- It suffices for a complex-linear equivalence to intertwine every polynomial generator on a basis in order to induce a polynomial-linear equivalence. -/
theorem nonempty_polynomialLinearEquiv_of_map_X_smul_basis {n : ℕ} {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [Module (PolynomialAlgebra n) M] [IsScalarTower ℂ (PolynomialAlgebra n) M]
    [AddCommGroup N] [Module ℂ N] [Module (PolynomialAlgebra n) N] [IsScalarTower ℂ (PolynomialAlgebra n) N]
    {ι : Type*} (B : Module.Basis ι ℂ M) (e : M ≃ₗ[ℂ] N)
    (h : ∀ (i : Fin n) (j : ι), e ((X i : PolynomialAlgebra n) • B j) = (X i : PolynomialAlgebra n) • e (B j)) :
    Nonempty (M ≃ₗ[PolynomialAlgebra n] N) := by
  refine nonempty_polynomialLinearEquiv_of_map_X_smul e fun i m => ?_
  have hmaps : (e.toLinearMap ∘ₗ generatorAction (M := M) i) = (generatorAction (M := N) i ∘ₗ e.toLinearMap) :=
    B.ext fun j => by simpa using h i j
  simpa using LinearMap.congr_fun hmaps m

/-! ## The dual-number normal form `DualNumberModule a c` -/

/-- A two-dimensional complex module parameterized by two tuples, with a distinguished square-zero element. -/
def DualNumberModule {n : ℕ} (_a _c : Fin n → ℂ) : Type := DualNumber ℂ

namespace DualNumberModule

variable {n : ℕ} (a c : Fin n → ℂ)

/-- The commutative ring structure on a dual-number module. -/
instance instCommRing : CommRing (DualNumberModule a c) := inferInstanceAs (CommRing (DualNumber ℂ))
/-- The complex algebra structure on a dual-number module. -/
instance instAlgebra : Algebra ℂ (DualNumberModule a c) := inferInstanceAs (Algebra ℂ (DualNumber ℂ))
/-- A dual-number module is finite as a module over the complex numbers. -/
instance moduleFinite : Module.Finite ℂ (DualNumberModule a c) := inferInstanceAs (Module.Finite ℂ (ℂ × ℂ))
/-- A dual-number module is nontrivial. -/
instance instNontrivial : Nontrivial (DualNumberModule a c) := inferInstanceAs (Nontrivial (ℂ × ℂ))
/-- A dual-number module is finite-dimensional over the complex numbers. -/
instance finiteDimensional : FiniteDimensional ℂ (DualNumberModule a c) := inferInstanceAs (FiniteDimensional ℂ (ℂ × ℂ))

/-- The distinguished square-zero element of a dual-number module. -/
def epsilon : DualNumberModule a c := (ε : DualNumber ℂ)

/-- The square of the distinguished element is zero. -/
@[simp] theorem epsilon_sq : epsilon a c * epsilon a c = 0 := DualNumber.eps_mul_eps

/-- The scalar coefficient of an element in the basis consisting of one and the distinguished element. -/
def scalarPart (x : DualNumberModule a c) : ℂ := TrivSqZeroExt.fst (x : DualNumber ℂ)

/-- The coefficient of the distinguished square-zero element in a dual-number module element. -/
def nilpotentPart (x : DualNumberModule a c) : ℂ := TrivSqZeroExt.snd (x : DualNumber ℂ)

/-- The scalar part of zero is zero. -/
@[simp] theorem scalarPart_zero : scalarPart a c 0 = 0 := rfl
/-- The nilpotent part of zero is zero. -/
@[simp] theorem nilpotentPart_zero : nilpotentPart a c 0 = 0 := rfl
/-- The scalar part of one is one. -/
@[simp] theorem scalarPart_one : scalarPart a c 1 = 1 := rfl
/-- The nilpotent part of one is zero. -/
@[simp] theorem nilpotentPart_one : nilpotentPart a c 1 = 0 := rfl
/-- The scalar part of the distinguished element is zero. -/
@[simp] theorem scalarPart_epsilon : scalarPart a c (epsilon a c) = 0 := rfl
/-- The nilpotent part of the distinguished element is one. -/
@[simp] theorem nilpotentPart_epsilon : nilpotentPart a c (epsilon a c) = 1 := rfl

/-- The scalar part of a sum is the sum of the scalar parts. -/
@[simp] theorem scalarPart_add (x y : DualNumberModule a c) : scalarPart a c (x + y) = scalarPart a c x + scalarPart a c y := rfl
/-- The nilpotent part of a sum is the sum of the nilpotent parts. -/
@[simp] theorem nilpotentPart_add (x y : DualNumberModule a c) : nilpotentPart a c (x + y) = nilpotentPart a c x + nilpotentPart a c y := rfl
/-- The scalar part commutes with complex scalar multiplication. -/
@[simp] theorem scalarPart_smul (r : ℂ) (x : DualNumberModule a c) : scalarPart a c (r • x) = r * scalarPart a c x := rfl
/-- The nilpotent part commutes with complex scalar multiplication. -/
@[simp] theorem nilpotentPart_smul (r : ℂ) (x : DualNumberModule a c) : nilpotentPart a c (r • x) = r * nilpotentPart a c x := rfl

/-- Two elements are equal when both their scalar and nilpotent parts agree. -/
theorem ext {x y : DualNumberModule a c} (h1 : scalarPart a c x = scalarPart a c y) (h2 : nilpotentPart a c x = nilpotentPart a c y) : x = y :=
  TrivSqZeroExt.ext h1 h2

/-- Every element decomposes as its scalar part times one plus its nilpotent part times the distinguished element. -/
theorem decompose (x : DualNumberModule a c) :
    x = scalarPart a c x • (1 : DualNumberModule a c) + nilpotentPart a c x • epsilon a c := by
  refine ext a c ?_ ?_ <;> simp

end DualNumberModule

private theorem dualNumber_eps_mul (x : DualNumber ℂ) :
    (ε : DualNumber ℂ) * x = TrivSqZeroExt.fst x • (ε : DualNumber ℂ) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;>
    simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]

/-- Left multiplication by the distinguished element extracts the scalar part and multiplies the distinguished element by it. -/
theorem DualNumberModule.epsilon_mul {n : ℕ} (a c : Fin n → ℂ) (x : DualNumberModule a c) :
    epsilon a c * x = scalarPart a c x • epsilon a c :=
  dualNumber_eps_mul x

/-- The complex-algebra homomorphism defining the polynomial action on a dual-number module. -/
noncomputable def polynomialActionAlgHom {n : ℕ} (a c : Fin n → ℂ) : PolynomialAlgebra n →ₐ[ℂ] DualNumberModule a c :=
  MvPolynomial.aeval fun i => algebraMap ℂ (DualNumberModule a c) (a i) + c i • DualNumberModule.epsilon a c

/-- A polynomial generator maps to its first parameter as a scalar plus its second parameter times the distinguished element. -/
@[simp] theorem polynomialActionAlgHom_X {n : ℕ} (a c : Fin n → ℂ) (i : Fin n) :
    polynomialActionAlgHom a c (X i) = algebraMap ℂ (DualNumberModule a c) (a i) + c i • DualNumberModule.epsilon a c := by
  simp [polynomialActionAlgHom]

/-- The polynomial-algebra module structure on a dual-number module. -/
noncomputable instance dualNumberModulePolynomialModule {n : ℕ} (a c : Fin n → ℂ) : Module (PolynomialAlgebra n) (DualNumberModule a c) :=
  Module.compHom (DualNumberModule a c) (polynomialActionAlgHom a c).toRingHom

/-- Polynomial scalar multiplication agrees with multiplication by the image under the polynomial-action algebra homomorphism. -/
theorem smul_eq_polynomialActionAlgHom_mul {n : ℕ} (a c : Fin n → ℂ) (p : PolynomialAlgebra n) (x : DualNumberModule a c) :
    p • x = polynomialActionAlgHom a c p * x := rfl

/-- The complex and polynomial-algebra actions on a dual-number module form a scalar tower. -/
instance dualNumberModuleIsScalarTower {n : ℕ} (a c : Fin n → ℂ) : IsScalarTower ℂ (PolynomialAlgebra n) (DualNumberModule a c) :=
  ⟨fun r p x => by rw [smul_eq_polynomialActionAlgHom_mul, smul_eq_polynomialActionAlgHom_mul, map_smul, smul_mul_assoc]⟩

/-- A dual-number module has complex dimension two. -/
theorem finrank_eq_two {n : ℕ} (a c : Fin n → ℂ) : Module.finrank ℂ (DualNumberModule a c) = 2 := by
  change Module.finrank ℂ (ℂ × ℂ) = 2
  rw [Module.finrank_prod, Module.finrank_self]

/-- A polynomial generator acts by its first parameter plus its second parameter times multiplication by the distinguished element. -/
theorem X_smul {n : ℕ} (a c : Fin n → ℂ) (i : Fin n) (x : DualNumberModule a c) :
    (X i : PolynomialAlgebra n) • x = a i • x + c i • (DualNumberModule.epsilon a c * x) := by
  rw [smul_eq_polynomialActionAlgHom_mul, polynomialActionAlgHom_X, add_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_mul_assoc]

/-- A polynomial generator sends one to its scalar parameter plus its nilpotent parameter times the distinguished element. -/
@[simp] theorem X_smul_one {n : ℕ} (a c : Fin n → ℂ) (i : Fin n) :
    (X i : PolynomialAlgebra n) • (1 : DualNumberModule a c) = a i • (1 : DualNumberModule a c) + c i • DualNumberModule.epsilon a c := by
  rw [X_smul, mul_one]

/-- A polynomial generator acts on the distinguished element by its first parameter. -/
@[simp] theorem X_smul_epsilon {n : ℕ} (a c : Fin n → ℂ) (i : Fin n) :
    (X i : PolynomialAlgebra n) • DualNumberModule.epsilon a c = a i • DualNumberModule.epsilon a c := by
  rw [X_smul, DualNumberModule.epsilon_sq, smul_zero, add_zero]

/-- The distinguished square-zero element is nonzero. -/
theorem epsilon_ne_zero {n : ℕ} (a c : Fin n → ℂ) : DualNumberModule.epsilon a c ≠ 0 := by
  intro h
  have := congrArg (DualNumberModule.nilpotentPart a c) h
  simp at this

/-- The complex basis of a dual-number module indexed by a two-element finite type. -/
noncomputable def dualNumberBasis {n : ℕ} (a c : Fin n → ℂ) :
    Module.Basis (Fin 2) ℂ (DualNumberModule a c) := by
  refine basisOfLinearIndependentOfCardEqFinrank
    (b := ![(1 : DualNumberModule a c), DualNumberModule.epsilon a c]) ?_ ?_
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (DualNumberModule.scalarPart a c) hst
    have h2 := congrArg (DualNumberModule.nilpotentPart a c) hst
    simp only [DualNumberModule.scalarPart_add, DualNumberModule.nilpotentPart_add, DualNumberModule.scalarPart_smul, DualNumberModule.nilpotentPart_smul, DualNumberModule.scalarPart_one,
      DualNumberModule.nilpotentPart_one, DualNumberModule.scalarPart_epsilon, DualNumberModule.nilpotentPart_epsilon, mul_one, mul_zero, add_zero, zero_add,
      DualNumberModule.scalarPart_zero, DualNumberModule.nilpotentPart_zero] at h1 h2
    exact ⟨h1, h2⟩
  · rw [Fintype.card_fin, finrank_eq_two]

/-- The dual-number basis consists of one followed by the distinguished element. -/
@[simp] theorem dualNumberBasis_apply {n : ℕ} (a c : Fin n → ℂ) (j : Fin 2) :
    dualNumberBasis a c j = ![(1 : DualNumberModule a c), DualNumberModule.epsilon a c] j := by
  rw [dualNumberBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The basis vector at index zero is one. -/
theorem dualNumberBasis_apply_zero {n : ℕ} (a c : Fin n → ℂ) : dualNumberBasis a c 0 = (1 : DualNumberModule a c) := by
  rw [dualNumberBasis_apply]; rfl

/-- The basis vector at index one is the distinguished element. -/
theorem dualNumberBasis_apply_one {n : ℕ} (a c : Fin n → ℂ) : dualNumberBasis a c 1 = DualNumberModule.epsilon a c := by
  rw [dualNumberBasis_apply]; rfl

/-! ## Weight lines -/

section WeightLine

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U] [Module (PolynomialAlgebra n) U]
  [IsScalarTower ℂ (PolynomialAlgebra n) U]

/-- For a simultaneous generator eigenvector, the polynomial span restricted to complex scalars equals its complex span. -/
lemma restrictScalars_span_eq_span_of_eigenvector (b : Fin n → ℂ) (w : U)
    (hb : ∀ i, (X i : PolynomialAlgebra n) • w = b i • w) :
    (Submodule.span (PolynomialAlgebra n) {w}).restrictScalars ℂ = Submodule.span ℂ {w} := by
  apply le_antisymm
  · rw [SetLike.le_def]
    intro x hx
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [smul_eq_aeval_smul_of_generator_smul b w hb p]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  · rw [Submodule.span_le]
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, Submodule.restrictScalars_mem]
    exact Submodule.mem_span_singleton_self w

/-- The polynomial span of a nonzero simultaneous generator eigenvector is linearly equivalent to the corresponding evaluation module. -/
noncomputable def spanLinearEquivEvaluationModuleOfEigenvector (b : Fin n → ℂ) (w : U) (hw : w ≠ 0)
    (hb : ∀ i, (X i : PolynomialAlgebra n) • w = b i • w) :
    ↥(Submodule.span (PolynomialAlgebra n) {w}) ≃ₗ[PolynomialAlgebra n] EvaluationModule b := by
  have hrs := restrictScalars_span_eq_span_of_eigenvector b w hb
  have h1 : Module.finrank ℂ ↥((Submodule.span (PolynomialAlgebra n) {w}).restrictScalars ℂ) = 1 := by
    rw [hrs]; exact finrank_span_singleton hw
  have h1' : Module.finrank ℂ ↥(Submodule.span (PolynomialAlgebra n) {w}) = 1 := h1
  haveI : FiniteDimensional ℂ ↥(Submodule.span (PolynomialAlgebra n) {w}) :=
    FiniteDimensional.of_finrank_pos (by rw [h1']; norm_num)
  refine linearEquivEvaluationModuleOfEigenvector b (⟨w, Submodule.mem_span_singleton_self w⟩) ?_ h1' ?_
  · rw [Ne, Submodule.mk_eq_zero]; exact hw
  · intro i
    apply Subtype.ext
    change (X i : PolynomialAlgebra n) • w = b i • w
    exact hb i

/-- A polynomial submodule is closed under complex scalar multiplication. -/
lemma complex_smul_mem_polynomialSubmodule {S : Submodule (PolynomialAlgebra n) U} (r : ℂ) {x : U} (hx : x ∈ S) : r • x ∈ S := by
  rw [← algebraMap_smul (PolynomialAlgebra n) r x]
  exact Submodule.smul_mem _ _ hx

end WeightLine

/-! ## Exhaustiveness of the normal forms -/

/-- Every two-dimensional complex polynomial module is equivalent either to a product of evaluation modules at distinct points or to a dual-number module. -/
@[source_ref "Chapter3/Problem3.9.2" (role := primary)]
theorem finrank_two_linearEquiv_prod_or_dualNumberModule {n : ℕ} (U : Type)
    [AddCommGroup U] [Module ℂ U] [Module (PolynomialAlgebra n) U] [IsScalarTower ℂ (PolynomialAlgebra n) U]
    [FiniteDimensional ℂ U] (hdim : Module.finrank ℂ U = 2) :
    (∃ b a : Fin n → ℂ, b ≠ a ∧ Nonempty (U ≃ₗ[PolynomialAlgebra n] EvaluationModule b × EvaluationModule a)) ∨
      (∃ a c : Fin n → ℂ, Nonempty (U ≃ₗ[PolynomialAlgebra n] DualNumberModule a c)) := by
  haveI : SMulCommClass (PolynomialAlgebra n) ℂ U := polynomialComplexSmulCommClass
  obtain ⟨b, v, hv, hb⟩ := exists_common_eigenvector_of_finrank_two (n := n) U hdim
  -- A vector outside the `ℂ`-line of `v`.
  obtain ⟨u, hu⟩ : ∃ u : U, u ∉ Submodule.span ℂ {v} := by
    by_contra hcon
    have htop : Submodule.span ℂ ({v} : Set U) = ⊤ :=
      eq_top_iff.mpr fun x _ => not_not.mp fun hx => hcon ⟨x, hx⟩
    have hcg : Module.finrank ℂ ↥(Submodule.span ℂ ({v} : Set U))
        = Module.finrank ℂ ↥(⊤ : Submodule ℂ U) :=
      congrArg (fun S : Submodule ℂ U => Module.finrank ℂ ↥S) htop
    rw [finrank_span_singleton hv, finrank_top, hdim] at hcg
    omega
  -- `u, v` is a `ℂ`-basis of `U`.
  have hindep : LinearIndependent ℂ ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, zero_add] at hst
      exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right hv⟩
    · exfalso
      apply hu
      have h1 : s • u = -(t • v) := eq_neg_of_add_eq_zero_left hst
      have h2 : u = (-(s⁻¹ * t)) • v := by
        rw [neg_smul, ← smul_smul, ← smul_neg, ← h1, inv_smul_smul₀ hs]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  obtain ⟨B, hBcoe⟩ : ∃ B : Module.Basis (Fin 2) ℂ U, ⇑B = ![u, v] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hindep (by rw [Fintype.card_fin, hdim]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hBu : B 0 = u := by rw [hBcoe]; rfl
  have hBv : B 1 = v := by rw [hBcoe]; rfl
  have hcoord : ∀ x : U, x = B.repr x 0 • u + B.repr x 1 • v := by
    intro x
    have h := B.sum_repr x
    rw [Fin.sum_univ_two, hBu, hBv] at h
    exact h.symm
  have hpair : ∀ s₁ t₁ s₂ t₂ : ℂ, s₁ • u + t₁ • v = s₂ • u + t₂ • v → s₁ = s₂ ∧ t₁ = t₂ := by
    intro s₁ t₁ s₂ t₂ h
    have h0 : (s₁ - s₂) • u + (t₁ - t₂) • v = 0 := by
      have h' : (s₁ • u + t₁ • v) - (s₂ • u + t₂ • v) = 0 := sub_eq_zero_of_eq h
      rw [← h']; module
    obtain ⟨hs, ht⟩ := LinearIndependent.pair_iff.mp hindep _ _ h0
    exact ⟨sub_eq_zero.mp hs, sub_eq_zero.mp ht⟩
  -- The matrix of the action in the basis `u, v`: `xᵢ • u = αᵢ u + γᵢ v`.
  obtain ⟨α, γ, hXu⟩ : ∃ α γ : Fin n → ℂ, ∀ i, (X i : PolynomialAlgebra n) • u = α i • u + γ i • v :=
    ⟨fun i => B.repr ((X i : PolynomialAlgebra n) • u) 0, fun i => B.repr ((X i : PolynomialAlgebra n) • u) 1,
      fun i => hcoord _⟩
  have hXsmul : ∀ (i : Fin n) (r : ℂ) (x : U),
      (X i : PolynomialAlgebra n) • (r • x) = r • ((X i : PolynomialAlgebra n) • x) := fun i r x => smul_comm _ _ _
  have hexp : ∀ i j : Fin n, (X i : PolynomialAlgebra n) • ((X j : PolynomialAlgebra n) • u)
      = (α j * α i) • u + (α j * γ i + γ j * b i) • v := by
    intro i j
    rw [hXu j, smul_add, hXsmul, hXsmul, hXu i, hb i]
    module
  -- Commutativity of the generators forces `γᵢ (b_j − α_j) = γ_j (b_i − α_i)`.
  have hrel : ∀ i j : Fin n, α j * γ i + γ j * b i = α i * γ j + γ i * b j := by
    intro i j
    have h1 : (X i : PolynomialAlgebra n) • ((X j : PolynomialAlgebra n) • u)
        = (X j : PolynomialAlgebra n) • ((X i : PolynomialAlgebra n) • u) := by
      rw [← mul_smul, ← mul_smul, mul_comm]
    rw [hexp i j, hexp j i] at h1
    exact (hpair _ _ _ _ h1).2
  by_cases hαb : α = b
  · -- Equal weights: a dual-number module.
    right
    refine ⟨α, γ, ?_⟩
    have hvα : ∀ i, (X i : PolynomialAlgebra n) • v = α i • v := by rw [hαb]; exact hb
    set e := B.equiv (dualNumberBasis α γ) (Equiv.refl (Fin 2)) with he
    have he0 : e (B 0) = (1 : DualNumberModule α γ) := by
      rw [he, Module.Basis.equiv_apply, Equiv.refl_apply, dualNumberBasis_apply]; rfl
    have he1 : e (B 1) = DualNumberModule.epsilon α γ := by
      rw [he, Module.Basis.equiv_apply, Equiv.refl_apply, dualNumberBasis_apply]; rfl
    refine nonempty_polynomialLinearEquiv_of_map_X_smul_basis B e ?_
    intro i j
    have h0 : e ((X i : PolynomialAlgebra n) • B 0) = (X i : PolynomialAlgebra n) • e (B 0) := by
      rw [hBu, hXu i, map_add, map_smul, map_smul, ← hBu, ← hBv, he0, he1, X_smul_one,
        add_comm]
    have h1 : e ((X i : PolynomialAlgebra n) • B 1) = (X i : PolynomialAlgebra n) • e (B 1) := by
      rw [hBv, hvα i, map_smul, ← hBv, he1, X_smul_epsilon]
    fin_cases j
    · exact h0
    · exact h1
  · -- Distinct weights: the extension splits.
    left
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hαb
    have hbk : b k - α k ≠ 0 := sub_ne_zero_of_ne (Ne.symm hk)
    obtain ⟨t, ht⟩ : ∃ t : ℂ, t = γ k / (b k - α k) := ⟨_, rfl⟩
    obtain ⟨u', hu'def⟩ : ∃ u' : U, u' = u - t • v := ⟨_, rfl⟩
    -- Shifting `u` by the right multiple of `v` produces a weight vector of weight `α`.
    have hXu' : ∀ i, (X i : PolynomialAlgebra n) • u' = α i • u' := by
      intro i
      have hti : t * (b i - α i) = γ i := by
        rw [ht, div_mul_eq_mul_div, div_eq_iff hbk]
        linear_combination hrel i k
      rw [hu'def, smul_sub, hXsmul, hXu i, hb i]
      match_scalars
      · ring
      · linear_combination -hti
    have hu'ne : u' ≠ 0 := by
      intro h
      rw [hu'def] at h
      apply hu
      rw [sub_eq_zero.mp h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hindep' : LinearIndependent ℂ ![v, u'] := by
      rw [LinearIndependent.pair_iff]
      intro s r hsr
      rw [hu'def] at hsr
      have h0 : r • u + (s - r * t) • v = 0 := by rw [← hsr]; module
      obtain ⟨hr, hs⟩ := LinearIndependent.pair_iff.mp hindep _ _ h0
      rw [hr, zero_mul, sub_zero] at hs
      exact ⟨hs, hr⟩
    have hspan' : ∀ x : U, ∃ s r : ℂ, x = s • v + r • u' := by
      intro x
      obtain ⟨p, q, hpq⟩ : ∃ p q : ℂ, x = p • u + q • v := ⟨_, _, hcoord x⟩
      exact ⟨q + p * t, p, by rw [hpq, hu'def]; module⟩
    have hdisj : Disjoint (Submodule.span (PolynomialAlgebra n) ({v} : Set U))
        (Submodule.span (PolynomialAlgebra n) ({u'} : Set U)) := by
      rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have hx1' : x ∈ Submodule.span ℂ ({v} : Set U) := by
        rw [← restrictScalars_span_eq_span_of_eigenvector b v hb, Submodule.restrictScalars_mem]; exact hx1
      have hx2' : x ∈ Submodule.span ℂ ({u'} : Set U) := by
        rw [← restrictScalars_span_eq_span_of_eigenvector α u' hXu', Submodule.restrictScalars_mem]; exact hx2
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hx1'
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx2'
      have h0 : s • v + (-r) • u' = 0 := by rw [hs, ← hr]; module
      obtain ⟨hs0, _⟩ := LinearIndependent.pair_iff.mp hindep' _ _ h0
      rw [← hs, hs0, zero_smul]
    have hcodisj : Codisjoint (Submodule.span (PolynomialAlgebra n) ({v} : Set U))
        (Submodule.span (PolynomialAlgebra n) ({u'} : Set U)) := by
      rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨s, r, hsr⟩ := hspan' x
      rw [hsr]
      exact Submodule.add_mem_sup
        (complex_smul_mem_polynomialSubmodule s (Submodule.mem_span_singleton_self v))
        (complex_smul_mem_polynomialSubmodule r (Submodule.mem_span_singleton_self u'))
    refine ⟨b, α, fun h => hk (by rw [h]), ?_⟩
    exact ⟨(Submodule.prodEquivOfIsCompl _ _ ⟨hdisj, hcodisj⟩).symm.trans
      ((spanLinearEquivEvaluationModuleOfEigenvector b v hv hb).prodCongr (spanLinearEquivEvaluationModuleOfEigenvector α u' hu'ne hXu'))⟩

/-! ## The isomorphism criterion -/

section DualNumberModuleIso

variable {n : ℕ}

/-- A polynomial-linear equivalence commutes with scalar multiplication by complex numbers. -/
lemma linearEquiv_map_smul_complex {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [Module (PolynomialAlgebra n) M] [IsScalarTower ℂ (PolynomialAlgebra n) M]
    [AddCommGroup N] [Module ℂ N] [Module (PolynomialAlgebra n) N] [IsScalarTower ℂ (PolynomialAlgebra n) N]
    (φ : M ≃ₗ[PolynomialAlgebra n] N) (r : ℂ) (x : M) : φ (r • x) = r • φ x := by
  rw [← algebraMap_smul (PolynomialAlgebra n) r x, map_smul, algebraMap_smul]

/-- Subtracting an arbitrary scalar action from a generator action separates into the scalar-parameter difference and the nilpotent contribution. -/
theorem X_sub_smul (a c : Fin n → ℂ) (i : Fin n) (r : ℂ) (x : DualNumberModule a c) :
    (X i : PolynomialAlgebra n) • x - r • x = (a i - r) • x + c i • (DualNumberModule.epsilon a c * x) := by
  rw [X_smul]; module

/-- A complex scalar multiple of the distinguished element is zero exactly when the scalar is zero. -/
theorem smul_epsilon_eq_zero_iff (a c : Fin n → ℂ) (r : ℂ) :
    r • DualNumberModule.epsilon a c = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zero_smul]⟩
  have h2 := congrArg (DualNumberModule.nilpotentPart a c) h
  simpa using h2

/-- For each generator, applying its action minus the scalar parameter twice gives zero. -/
theorem X_sub_parameter_sq_smul (a c : Fin n → ℂ) (i : Fin n) (x : DualNumberModule a c) :
    (X i : PolynomialAlgebra n) • ((X i : PolynomialAlgebra n) • x - a i • x)
      - a i • ((X i : PolynomialAlgebra n) • x - a i • x) = 0 := by
  have h : ∀ z : DualNumberModule a c, (X i : PolynomialAlgebra n) • z - a i • z = c i • (DualNumberModule.epsilon a c * z) := by
    intro z; rw [X_sub_smul]; simp
  rw [h, h, mul_smul_comm, ← mul_assoc, DualNumberModule.epsilon_sq, zero_mul, smul_zero, smul_zero]

/-- A polynomial-linear equivalence of dual-number modules forces their scalar parameter tuples to agree. -/
theorem parameter_eq_of_linearEquiv (a c a' c' : Fin n → ℂ) (φ : DualNumberModule a c ≃ₗ[PolynomialAlgebra n] DualNumberModule a' c') :
    a = a' := by
  funext i
  have hstep : ∀ x : DualNumberModule a c, φ ((X i : PolynomialAlgebra n) • x - a' i • x)
      = (X i : PolynomialAlgebra n) • φ x - a' i • φ x := by
    intro x; rw [map_sub, map_smul, linearEquiv_map_smul_complex]
  have hsrc : (X i : PolynomialAlgebra n) • ((X i : PolynomialAlgebra n) • (1 : DualNumberModule a c) - a' i • (1 : DualNumberModule a c))
      - a' i • ((X i : PolynomialAlgebra n) • (1 : DualNumberModule a c) - a' i • (1 : DualNumberModule a c)) = 0 := by
    apply φ.injective
    rw [map_zero, hstep, hstep]
    exact X_sub_parameter_sq_smul a' c' i (φ 1)
  rw [X_sub_smul, X_sub_smul, mul_one] at hsrc
  have hfst := congrArg (DualNumberModule.scalarPart a c) hsrc
  simp only [DualNumberModule.epsilon_mul, DualNumberModule.scalarPart_add, DualNumberModule.scalarPart_smul, DualNumberModule.scalarPart_one, DualNumberModule.scalarPart_epsilon,
    DualNumberModule.scalarPart_zero, mul_zero, add_zero, mul_one] at hfst
  have hd : a i - a' i = 0 := by
    rcases mul_eq_zero.mp hfst with h' | h' <;> exact h'
  exact sub_eq_zero.mp hd

/-- If every polynomial generator acts everywhere by its scalar parameter, then the nilpotent parameter tuple is zero. -/
theorem parameter_eq_zero_of_X_smul_eq (a c : Fin n → ℂ)
    (h : ∀ (i : Fin n) (x : DualNumberModule a c), (X i : PolynomialAlgebra n) • x = a i • x) : c = 0 := by
  funext i
  have h1 := h i 1
  rw [X_smul_one] at h1
  have h2 : c i • DualNumberModule.epsilon a c = 0 :=
    calc c i • DualNumberModule.epsilon a c
        = (a i • (1 : DualNumberModule a c) + c i • DualNumberModule.epsilon a c) - a i • (1 : DualNumberModule a c) := by abel
      _ = a i • (1 : DualNumberModule a c) - a i • (1 : DualNumberModule a c) := by rw [h1]
      _ = 0 := by abel
  simpa using (smul_epsilon_eq_zero_iff a c (c i)).mp h2

/-- A polynomial-linear equivalence to a dual-number module with zero nilpotent parameter forces the source parameter to be zero. -/
theorem parameter_eq_zero_of_linearEquiv_zero (a c c' : Fin n → ℂ) (hc' : c' = 0)
    (φ : DualNumberModule a c ≃ₗ[PolynomialAlgebra n] DualNumberModule a c') : c = 0 := by
  subst hc'
  refine parameter_eq_zero_of_X_smul_eq a c fun i x => ?_
  apply φ.injective
  rw [map_smul, linearEquiv_map_smul_complex, X_smul]
  simp

/-- If the target nilpotent parameter is nonzero and the corresponding modules are equivalent, then it is a nonzero scalar multiple of the source parameter. -/
theorem exists_eq_smul_of_linearEquiv (a c c' : Fin n → ℂ) (hc' : c' ≠ 0)
    (φ : DualNumberModule a c ≃ₗ[PolynomialAlgebra n] DualNumberModule a c') : ∃ lam : ℂ, lam ≠ 0 ∧ c' = lam • c := by
  -- The nilpotent parts of the two actions intertwine.
  have hN : ∀ (i : Fin n) (x : DualNumberModule a c),
      φ (c i • (DualNumberModule.epsilon a c * x)) = c' i • (DualNumberModule.epsilon a c' * φ x) := by
    intro i x
    have h1 : ∀ z : DualNumberModule a c, c i • (DualNumberModule.epsilon a c * z)
        = (X i : PolynomialAlgebra n) • z - a i • z := by
      intro z; rw [X_sub_smul]; simp
    have h2 : ∀ z : DualNumberModule a c', c' i • (DualNumberModule.epsilon a c' * z)
        = (X i : PolynomialAlgebra n) • z - a i • z := by
      intro z; rw [X_sub_smul]; simp
    rw [h1, h2, map_sub, map_smul, linearEquiv_map_smul_complex]
  obtain ⟨s, hs⟩ : ∃ s, DualNumberModule.scalarPart a c' (φ 1) = s := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', DualNumberModule.scalarPart a c' (φ (DualNumberModule.epsilon a c)) = s' := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t', DualNumberModule.nilpotentPart a c' (φ (DualNumberModule.epsilon a c)) = t' := ⟨_, rfl⟩
  -- Testing the intertwining on `ε` kills the `1`-coordinate of `φ ε`.
  have hs'zero : s' = 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc'
    have hi' : c' i ≠ 0 := by simpa using hi
    have h := hN i (DualNumberModule.epsilon a c)
    rw [DualNumberModule.epsilon_sq, smul_zero, map_zero, DualNumberModule.epsilon_mul, hs', smul_smul] at h
    have h2 := (smul_epsilon_eq_zero_iff a c' (c' i * s')).mp h.symm
    exact (mul_eq_zero.mp h2).resolve_left hi'
  have hepsimg : φ (DualNumberModule.epsilon a c) = t' • DualNumberModule.epsilon a c' := by
    have h := DualNumberModule.decompose a c' (φ (DualNumberModule.epsilon a c))
    rw [hs', ht', hs'zero, zero_smul, zero_add] at h
    exact h
  have ht'ne : t' ≠ 0 := by
    intro h
    rw [h, zero_smul] at hepsimg
    exact epsilon_ne_zero a c (φ.injective (by rw [hepsimg, map_zero]))
  -- Surjectivity forces the `1`-coordinate of `φ 1` to be nonzero.
  have hsne : s ≠ 0 := by
    intro h
    obtain ⟨t, htdef⟩ : ∃ t, DualNumberModule.nilpotentPart a c' (φ 1) = t := ⟨_, rfl⟩
    have honeimg : φ 1 = t • DualNumberModule.epsilon a c' := by
      have h0 := DualNumberModule.decompose a c' (φ 1)
      rw [hs, htdef, h, zero_smul, zero_add] at h0
      exact h0
    obtain ⟨x, hx⟩ := φ.surjective (1 : DualNumberModule a c')
    obtain ⟨p, q, hpq⟩ : ∃ p q : ℂ, x = p • (1 : DualNumberModule a c) + q • DualNumberModule.epsilon a c :=
      ⟨_, _, DualNumberModule.decompose a c x⟩
    rw [hpq, map_add, linearEquiv_map_smul_complex, linearEquiv_map_smul_complex, honeimg, hepsimg, smul_smul,
      smul_smul, ← add_smul] at hx
    have hf := congrArg (DualNumberModule.scalarPart a c') hx
    simp at hf
  -- Testing the intertwining on `1` pins the scalar.
  have hkey : ∀ i, c i * t' = c' i * s := by
    intro i
    have h := hN i 1
    rw [mul_one, linearEquiv_map_smul_complex, hepsimg, smul_smul, DualNumberModule.epsilon_mul, hs, smul_smul] at h
    have h2 : (c i * t' - c' i * s) • DualNumberModule.epsilon a c' = 0 := by rw [sub_smul, h, sub_self]
    exact sub_eq_zero.mp ((smul_epsilon_eq_zero_iff a c' _).mp h2)
  refine ⟨t' / s, div_ne_zero ht'ne hsne, funext fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -hkey i

/-- A nonzero scalar relation between nilpotent parameters yields an equivalence of dual-number polynomial modules with the same scalar parameter. -/
theorem nonempty_linearEquiv_of_eq_smul (a c c' : Fin n → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hc' : c' = lam • c) :
    Nonempty (DualNumberModule a c ≃ₗ[PolynomialAlgebra n] DualNumberModule a c') := by
  subst hc'
  set B' := (dualNumberBasis a (lam • c)).unitsSMul ![1, Units.mk0 lam hlam] with hB'
  set e := (dualNumberBasis a c).equiv B' (Equiv.refl (Fin 2)) with he
  have hB'0 : B' 0 = (1 : DualNumberModule a (lam • c)) := by
    rw [hB', Module.Basis.unitsSMul_apply, dualNumberBasis_apply_zero]
    simp
  have hB'1 : B' 1 = lam • DualNumberModule.epsilon a (lam • c) := by
    rw [hB', Module.Basis.unitsSMul_apply, dualNumberBasis_apply_one]
    simp [Units.smul_def]
  have he0b : e (dualNumberBasis a c 0) = (1 : DualNumberModule a (lam • c)) := by
    rw [he, Module.Basis.equiv_apply, Equiv.refl_apply, hB'0]
  have he1b : e (dualNumberBasis a c 1) = lam • DualNumberModule.epsilon a (lam • c) := by
    rw [he, Module.Basis.equiv_apply, Equiv.refl_apply, hB'1]
  have he0 : e (1 : DualNumberModule a c) = (1 : DualNumberModule a (lam • c)) := by
    rw [dualNumberBasis_apply_zero a c] at he0b; exact he0b
  have he1 : e (DualNumberModule.epsilon a c) = lam • DualNumberModule.epsilon a (lam • c) := by
    rw [dualNumberBasis_apply_one a c] at he1b; exact he1b
  haveI : SMulCommClass (PolynomialAlgebra n) ℂ (DualNumberModule a (lam • c)) := polynomialComplexSmulCommClass
  refine nonempty_polynomialLinearEquiv_of_map_X_smul_basis (dualNumberBasis a c) e fun i j => ?_
  have h0 : e ((X i : PolynomialAlgebra n) • dualNumberBasis a c 0)
      = (X i : PolynomialAlgebra n) • e (dualNumberBasis a c 0) := by
    rw [he0b, X_smul_one a (lam • c) i, dualNumberBasis_apply_zero a c, X_smul_one a c i,
      map_add, map_smul, map_smul, he0, he1]
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
    module
  have h1 : e ((X i : PolynomialAlgebra n) • dualNumberBasis a c 1)
      = (X i : PolynomialAlgebra n) • e (dualNumberBasis a c 1) := by
    rw [he1b, smul_comm (X i : PolynomialAlgebra n) lam (DualNumberModule.epsilon a (lam • c)),
      X_smul_epsilon a (lam • c) i, dualNumberBasis_apply_one a c, X_smul_epsilon a c i, map_smul, he1]
    module
  fin_cases j
  · exact h0
  · exact h1

end DualNumberModuleIso

/-- Two dual-number polynomial modules are equivalent exactly when their scalar parameters agree and their nilpotent parameters differ by a nonzero scalar. -/
@[source_ref "Chapter3/Problem3.9.2" (role := primary)]
theorem nonempty_linearEquiv_iff {n : ℕ} (a c a' c' : Fin n → ℂ) :
    Nonempty (DualNumberModule a c ≃ₗ[PolynomialAlgebra n] DualNumberModule a' c') ↔
      a = a' ∧ ∃ lam : ℂ, lam ≠ 0 ∧ c' = lam • c := by
  constructor
  · rintro ⟨φ⟩
    have haa : a = a' := parameter_eq_of_linearEquiv a c a' c' φ
    subst haa
    refine ⟨rfl, ?_⟩
    by_cases hc' : c' = 0
    · have hc : c = 0 := parameter_eq_zero_of_linearEquiv_zero a c c' hc' φ
      exact ⟨1, one_ne_zero, by rw [hc, hc', smul_zero]⟩
    · exact exists_eq_smul_of_linearEquiv a c c' hc' φ
  · rintro ⟨rfl, lam, hlam, hc'⟩
    exact nonempty_linearEquiv_of_eq_smul a c c' lam hlam hc'

/-! ## jointEigenvalueSet as an isomorphism invariant -/

section jointEigenvalueSet

variable {n : ℕ}

/-- The set of complex tuples occurring as simultaneous eigenvalues of the polynomial generators on a module. -/
def jointEigenvalueSet (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (PolynomialAlgebra n) M] :
    Set (Fin n → ℂ) :=
  {a | ∃ m : M, m ≠ 0 ∧ ∀ i, (X i : PolynomialAlgebra n) • m = a i • m}

variable {M N : Type*}
  [AddCommGroup M] [Module ℂ M] [Module (PolynomialAlgebra n) M] [IsScalarTower ℂ (PolynomialAlgebra n) M]
  [AddCommGroup N] [Module ℂ N] [Module (PolynomialAlgebra n) N] [IsScalarTower ℂ (PolynomialAlgebra n) N]

/-- A polynomial-linear equivalence gives inclusion of the source joint eigenvalue set in the target set. -/
theorem jointEigenvalueSet_mono_of_linearEquiv (φ : M ≃ₗ[PolynomialAlgebra n] N) :
    jointEigenvalueSet (n := n) M ⊆ jointEigenvalueSet (n := n) N := by
  rintro a ⟨m, hm, ha⟩
  refine ⟨φ m, fun h => hm (φ.injective (by rw [h, map_zero])), fun i => ?_⟩
  rw [← map_smul, ha i, linearEquiv_map_smul_complex]

/-- Polynomial-linearly equivalent modules have equal sets of joint generator eigenvalues. -/
theorem jointEigenvalueSet_eq_of_linearEquiv (φ : M ≃ₗ[PolynomialAlgebra n] N) :
    jointEigenvalueSet (n := n) M = jointEigenvalueSet (n := n) N :=
  Set.Subset.antisymm (jointEigenvalueSet_mono_of_linearEquiv φ)
    (jointEigenvalueSet_mono_of_linearEquiv φ.symm)

end jointEigenvalueSet

/-- The joint eigenvalue set of a dual-number module is the singleton containing its scalar parameter. -/
theorem jointEigenvalueSet_dualNumberModule {n : ℕ} (a c : Fin n → ℂ) : jointEigenvalueSet (DualNumberModule a c) = {a} := by
  apply Set.Subset.antisymm
  · rintro w ⟨x, hx, hw⟩
    funext i
    have h := hw i
    rw [X_smul, DualNumberModule.epsilon_mul, smul_smul] at h
    have h1 := congrArg (DualNumberModule.scalarPart a c) h
    have h2 := congrArg (DualNumberModule.nilpotentPart a c) h
    simp only [DualNumberModule.scalarPart_add, DualNumberModule.nilpotentPart_add, DualNumberModule.scalarPart_smul, DualNumberModule.nilpotentPart_smul, DualNumberModule.scalarPart_epsilon,
      DualNumberModule.nilpotentPart_epsilon, mul_zero, mul_one, add_zero] at h1 h2
    by_cases hfx : DualNumberModule.scalarPart a c x = 0
    · have hsx : DualNumberModule.nilpotentPart a c x ≠ 0 := by
        intro hs
        exact hx (DualNumberModule.ext a c (by simp [hfx]) (by simp [hs]))
      rw [hfx, mul_zero, add_zero] at h2
      exact (mul_right_cancel₀ hsx h2).symm
    · exact (mul_right_cancel₀ hfx h1).symm
  · rintro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact ⟨DualNumberModule.epsilon a c, epsilon_ne_zero a c, fun i => X_smul_epsilon a c i⟩

/-- The joint eigenvalue set of a product of two evaluation modules consists of their two evaluation points. -/
theorem jointEigenvalueSet_prod_evaluationModule {n : ℕ} (b a : Fin n → ℂ) :
    jointEigenvalueSet (EvaluationModule b × EvaluationModule a) = {b, a} := by
  have hXb : ∀ (i : Fin n) (x : EvaluationModule b), (X i : PolynomialAlgebra n) • x = b i • x := by
    intro i x; rw [smul_eq_aeval_smul]; simp
  have hXa : ∀ (i : Fin n) (y : EvaluationModule a), (X i : PolynomialAlgebra n) • y = a i • y := by
    intro i y; rw [smul_eq_aeval_smul]; simp
  apply Set.Subset.antisymm
  · rintro w ⟨⟨x, y⟩, hxy, hw⟩
    by_cases hx : x = 0
    · have hy : y ≠ 0 := fun h => hxy (Prod.ext hx h)
      refine Or.inr (funext fun i => ?_)
      have h2 : (X i : PolynomialAlgebra n) • y = w i • y := congrArg Prod.snd (hw i)
      rw [hXa i y] at h2
      have h3 : (a i - w i) • y = 0 := by rw [sub_smul, h2, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy)).symm
    · refine Or.inl (funext fun i => ?_)
      have h1 : (X i : PolynomialAlgebra n) • x = w i • x := congrArg Prod.fst (hw i)
      rw [hXb i x] at h1
      have h3 : (b i - w i) • x = 0 := by rw [sub_smul, h1, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hx)).symm
  · rintro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · subst w
      refine ⟨(Submodule.Quotient.mk 1, 0), fun h => ?_, fun i => ?_⟩
      · exact quotientMkOne_ne_zero b (Prod.mk_eq_zero.mp h).1
      · exact Prod.ext (hXb i _) (by simp)
    · subst w
      refine ⟨(0, Submodule.Quotient.mk 1), fun h => ?_, fun i => ?_⟩
      · exact quotientMkOne_ne_zero a (Prod.mk_eq_zero.mp h).2
      · exact Prod.ext (by simp) (hXa i _)

/-- Two products of evaluation modules are polynomial-linearly equivalent exactly when their two evaluation points agree in the same order or in the opposite order. -/
@[source_ref "Chapter3/Problem3.9.2" (role := primary)]
theorem nonempty_prod_evaluationModule_linearEquiv_iff {n : ℕ} (b a b' a' : Fin n → ℂ) :
    Nonempty ((EvaluationModule b × EvaluationModule a) ≃ₗ[PolynomialAlgebra n] EvaluationModule b' × EvaluationModule a') ↔
      (b = b' ∧ a = a') ∨ (b = a' ∧ a = b') := by
  constructor
  · rintro ⟨φ⟩
    have h := jointEigenvalueSet_eq_of_linearEquiv φ
    rw [jointEigenvalueSet_prod_evaluationModule, jointEigenvalueSet_prod_evaluationModule] at h
    exact Set.pair_eq_pair_iff.mp h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨LinearEquiv.refl _ _⟩
    · exact ⟨LinearEquiv.prodComm (PolynomialAlgebra n) (EvaluationModule b) (EvaluationModule a)⟩

/-- A product of evaluation modules at distinct points is not polynomial-linearly equivalent to a dual-number module. -/
@[source_ref "Chapter3/Problem3.9.2" (role := primary)]
theorem not_nonempty_prod_linearEquiv_dualNumberModule_of_ne {n : ℕ} (b a a' c' : Fin n → ℂ) (hba : b ≠ a) :
    ¬ Nonempty ((EvaluationModule b × EvaluationModule a) ≃ₗ[PolynomialAlgebra n] DualNumberModule a' c') := by
  rintro ⟨φ⟩
  have h := jointEigenvalueSet_eq_of_linearEquiv φ
  rw [jointEigenvalueSet_prod_evaluationModule, jointEigenvalueSet_dualNumberModule] at h
  have hmem : ∀ w : Fin n → ℂ, w ∈ ({b, a} : Set (Fin n → ℂ)) → w = a' := by
    intro w hwmem
    rw [h, Set.mem_singleton_iff] at hwmem
    exact hwmem
  exact hba ((hmem b (by simp)).trans (hmem a (by simp)).symm)

end RepresentationTheory.Algebra.Module.TwoDimensionalPolynomialModules
