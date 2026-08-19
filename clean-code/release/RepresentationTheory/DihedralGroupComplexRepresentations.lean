/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.PermutationDegreeThree
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Group.CharacterAuxiliary
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Alignment.Attribute

open Real

noncomputable section

namespace RepresentationTheory.DihedralGroupComplexRepresentations

variable {N : ℕ}

/-- An auxiliary complex scalar associated with each natural number. -/
noncomputable def auxiliaryRootOfUnity (N : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / N)

/-- A finite-dimensional simple complex representation of a dihedral group has dimension one or two. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem finrank_eq_one_or_two_of_isSimpleModule [NeZero N]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (DihedralGroup N) W)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) ρ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = 2 := by
  classical
  haveI : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) ρ.asModule := hρ
  haveI : Nontrivial W :=
    IsSimpleModule.nontrivial (R := MonoidAlgebra ℂ (DihedralGroup N)) (M := ρ.asModule)
  -- Irreducibility of `ρ`: the lattice of subrepresentations is simple.
  haveI hirr : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  -- An eigenvector `v` of the rotation `ρ (r 1)`.
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (ρ (DihedralGroup.r 1))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  -- The reflection applied to `v`.
  set w₀ : W := ρ (DihedralGroup.sr 0) v with hw₀
  -- The rotation `r j` acts on the eigenvector by the scalar `μ ^ j.val`.
  have hA : ∀ j : ZMod N, ρ (DihedralGroup.r j) v = μ ^ j.val • v := by
    intro j
    have hj : DihedralGroup.r j = (DihedralGroup.r 1 : DihedralGroup N) ^ j.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [hj, map_pow]
    exact hv.pow_apply j.val
  -- The reflection `sr j = sr 0 * r j` sends `v` to `μ ^ j.val • w₀`.
  have hB : ∀ j : ZMod N, ρ (DihedralGroup.sr j) v = μ ^ j.val • w₀ := by
    intro j
    have hj : DihedralGroup.sr j = DihedralGroup.sr 0 * DihedralGroup.r j := by
      rw [DihedralGroup.sr_mul_r, zero_add]
    rw [hj, map_mul, Module.End.mul_apply, hA j, map_smul, hw₀]
  -- The two generators of the span, as members.
  have hvU : v ∈ Submodule.span ℂ ({v, w₀} : Set W) := Submodule.subset_span (by simp)
  have hw₀U : w₀ ∈ Submodule.span ℂ ({v, w₀} : Set W) := Submodule.subset_span (by simp)
  -- `ρ g` on `w₀` is `ρ (g * sr 0)` on `v`.
  have hgsv : ∀ g : DihedralGroup N, ρ g w₀ = ρ (g * DihedralGroup.sr 0) v := by
    intro g; rw [hw₀, map_mul, Module.End.mul_apply]
  -- `span {v, w₀}` is a subrepresentation.
  let Sub : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ ({v, w₀} : Set W)
      apply_mem_toSubmodule := by
        intro g x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · cases g with
              | r k => rw [hA k]; exact Submodule.smul_mem _ _ hvU
              | sr k => rw [hB k]; exact Submodule.smul_mem _ _ hw₀U
            · rw [hgsv g]
              cases g with
              | r k =>
                  rw [DihedralGroup.r_mul_sr, hB (0 - k)]; exact Submodule.smul_mem _ _ hw₀U
              | sr k =>
                  rw [DihedralGroup.sr_mul_sr, hA (0 - k)]; exact Submodule.smul_mem _ _ hvU
        | zero => simp
        | add a b _ _ iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb
        | smul c a _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih }
  -- Irreducibility forces the subrepresentation to be everything.
  have hSubTop : Sub.toSubmodule = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top Sub with h | h
    · exfalso
      apply hv0
      have hbot : Sub.toSubmodule = ⊥ := by rw [h]; rfl
      have hv' : v ∈ (⊥ : Submodule ℂ W) := by rw [← hbot]; exact hvU
      rwa [Submodule.mem_bot] at hv'
    · rw [h]; rfl
  have hspan : Submodule.span ℂ ({v, w₀} : Set W) = ⊤ := hSubTop
  -- Two generators, so the dimension is at most `2`.
  have hrange : Set.range ![v, w₀] = ({v, w₀} : Set W) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hle : Module.finrank ℂ W ≤ 2 := by
    have h := finrank_le_of_span_eq_top (R := ℂ) (v := ![v, w₀]) (by rw [hrange]; exact hspan)
    simpa using h
  have hpos : 0 < Module.finrank ℂ W := Module.finrank_pos
  omega

/-- A third auxiliary complex-valued function on each dihedral group. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
noncomputable def auxiliaryClassFunctionC (N : ℕ) : DihedralGroup N → ℂ
  | .r k => auxiliaryRootOfUnity N ^ k.val + (auxiliaryRootOfUnity N)⁻¹ ^ k.val
  | .sr _ => 0

/-- A second auxiliary complex-valued function on each dihedral group. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
def auxiliaryClassFunctionB (N : ℕ) : DihedralGroup N → ℂ
  | .r _ => 1
  | .sr _ => -1

/-- An auxiliary complex-valued function on each dihedral group. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
noncomputable def auxiliaryClassFunctionA (N : ℕ) : DihedralGroup N → ℂ
  | .r k => auxiliaryRootOfUnity N ^ (2 * k.val) + (auxiliaryRootOfUnity N)⁻¹ ^ (2 * k.val)
  | .sr _ => 0

/-- The square of the third auxiliary class function is one plus the second and first auxiliary class functions. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem auxiliaryClassFunctionC_sq (N : ℕ) (g : DihedralGroup N) :
    auxiliaryClassFunctionC N g ^ 2 = 1 + auxiliaryClassFunctionB N g + auxiliaryClassFunctionA N g := by
  cases g with
  | r k =>
    simp only [auxiliaryClassFunctionC, auxiliaryClassFunctionB, auxiliaryClassFunctionA]
    have hz : auxiliaryRootOfUnity N ≠ 0 := by unfold auxiliaryRootOfUnity; exact Complex.exp_ne_zero _
    have hab : auxiliaryRootOfUnity N ^ k.val * (auxiliaryRootOfUnity N)⁻¹ ^ k.val = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    have ha2 : auxiliaryRootOfUnity N ^ (2 * k.val) = (auxiliaryRootOfUnity N ^ k.val) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm]
    have hb2 : (auxiliaryRootOfUnity N)⁻¹ ^ (2 * k.val) = ((auxiliaryRootOfUnity N)⁻¹ ^ k.val) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm]
    rw [ha2, hb2]
    linear_combination (2 : ℂ) * hab
  | sr k =>
    simp only [auxiliaryClassFunctionC, auxiliaryClassFunctionB, auxiliaryClassFunctionA]
    ring

/-!
## Part (a): explicit construction and classification of all irreducibles

We build, for each `j : ZMod N`, an explicit `2`-dimensional representation `twoDimensionalRepresentation N j` on
`Fin 2 → ℂ` where the rotation `r 1` acts diagonally by `diag(ζ^j, ζ^{-j})` and the reflection
`sr 0` swaps the two coordinates. These are irreducible exactly when `2·j ≠ 0` (equivalently
`ζ^j ≠ ζ^{-j}`), and together with the one-dimensional characters they exhaust the irreducibles.
-/

/-- The auxiliary complex scalar is nonzero for every natural index. -/
theorem auxiliaryRootOfUnity_ne_zero (N : ℕ) : auxiliaryRootOfUnity N ≠ 0 := by
  unfold auxiliaryRootOfUnity; exact Complex.exp_ne_zero _

/-- For nonzero order, the corresponding auxiliary complex scalar raised to that order is one. -/
theorem auxiliaryRootOfUnity_pow_order [NeZero N] : auxiliaryRootOfUnity N ^ N = 1 := by
  unfold auxiliaryRootOfUnity
  rw [← Complex.exp_nat_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [show (N : ℂ) * (2 * π * Complex.I / N) = 2 * π * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- For nonzero order, powers of the corresponding auxiliary complex scalar depend only on the exponent modulo that order. -/
theorem auxiliaryRootOfUnity_pow_mod [NeZero N] (k : ℕ) : auxiliaryRootOfUnity N ^ (k % N) = auxiliaryRootOfUnity N ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k N, pow_add, pow_mul, auxiliaryRootOfUnity_pow_order, one_pow, mul_one]

/-- Powers of the auxiliary complex scalar at residue representatives convert addition modulo the order into multiplication. -/
theorem auxiliaryRootOfUnity_pow_zmod_add_val [NeZero N] (a b : ZMod N) :
    auxiliaryRootOfUnity N ^ (a + b).val = auxiliaryRootOfUnity N ^ a.val * auxiliaryRootOfUnity N ^ b.val := by
  rw [ZMod.val_add, auxiliaryRootOfUnity_pow_mod, pow_add]

/-- An auxiliary complex phase depending on three residue parameters. -/
noncomputable def cyclicPhase (N : ℕ) (j m : ZMod N) : ℂ := auxiliaryRootOfUnity N ^ (j * m).val

/-- The cyclic phase at zero is one. -/
@[simp] theorem cyclicPhase_zero (N : ℕ) (j : ZMod N) : cyclicPhase N j 0 = 1 := by
  simp [cyclicPhase]

/-- Every value of the cyclic phase is nonzero. -/
theorem cyclicPhase_ne_zero (N : ℕ) (j m : ZMod N) : cyclicPhase N j m ≠ 0 :=
  pow_ne_zero _ (auxiliaryRootOfUnity_ne_zero N)

/-- The cyclic phase converts addition in its final residue argument into multiplication. -/
theorem cyclicPhase_add [NeZero N] (j m m' : ZMod N) :
    cyclicPhase N j (m + m') = cyclicPhase N j m * cyclicPhase N j m' := by
  unfold cyclicPhase
  rw [mul_add, auxiliaryRootOfUnity_pow_zmod_add_val]

/-- The cyclic phase at the negated residue is the inverse of the original phase. -/
theorem cyclicPhase_neg [NeZero N] (j m : ZMod N) : cyclicPhase N j (-m) = (cyclicPhase N j m)⁻¹ := by
  rw [inv_eq_one_div, eq_div_iff (cyclicPhase_ne_zero N j m), ← cyclicPhase_add, neg_add_cancel, cyclicPhase_zero]

/-- The cyclic phase of a difference is the first phase multiplied by the inverse of the second. -/
theorem cyclicPhase_sub [NeZero N] (j m m' : ZMod N) :
    cyclicPhase N j (m - m') = cyclicPhase N j m * (cyclicPhase N j m')⁻¹ := by
  rw [sub_eq_add_neg, cyclicPhase_add, cyclicPhase_neg]

/-- A two-by-two complex matrix associated with a residue index and a dihedral group element. -/
noncomputable def twoDimensionalRepresentationMatrix (N : ℕ) (j : ZMod N) : DihedralGroup N → Matrix (Fin 2) (Fin 2) ℂ
  | .r k => !![cyclicPhase N j k, 0; 0, (cyclicPhase N j k)⁻¹]
  | .sr k => !![0, (cyclicPhase N j k)⁻¹; cyclicPhase N j k, 0]

/-- The matrix associated with the identity element is the identity matrix. -/
theorem twoDimensionalRepresentationMatrix_one [NeZero N] (j : ZMod N) : twoDimensionalRepresentationMatrix N j 1 = 1 := by
  rw [DihedralGroup.one_def]
  change (!![cyclicPhase N j 0, 0; 0, (cyclicPhase N j 0)⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) = 1
  rw [cyclicPhase_zero, inv_one, Matrix.one_fin_two]

/-- The matrix associated with a product of dihedral elements is the product of their associated matrices. -/
theorem twoDimensionalRepresentationMatrix_mul [NeZero N] (j : ZMod N) (g h : DihedralGroup N) :
    twoDimensionalRepresentationMatrix N j (g * h) = twoDimensionalRepresentationMatrix N j g * twoDimensionalRepresentationMatrix N j h := by
  cases g with
  | r a =>
    cases h with
    | r b =>
      rw [DihedralGroup.r_mul_r]
      change (!![cyclicPhase N j (a + b), 0; 0, (cyclicPhase N j (a + b))⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![cyclicPhase N j a, 0; 0, (cyclicPhase N j a)⁻¹] * !![cyclicPhase N j b, 0; 0, (cyclicPhase N j b)⁻¹]
      rw [Matrix.mul_fin_two, cyclicPhase_add, mul_inv]
      ext i k; fin_cases i <;> fin_cases k <;> simp
    | sr b =>
      rw [DihedralGroup.r_mul_sr]
      change (!![0, (cyclicPhase N j (b - a))⁻¹; cyclicPhase N j (b - a), 0] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![cyclicPhase N j a, 0; 0, (cyclicPhase N j a)⁻¹] * !![0, (cyclicPhase N j b)⁻¹; cyclicPhase N j b, 0]
      rw [Matrix.mul_fin_two, cyclicPhase_sub]
      ext i k; fin_cases i <;> fin_cases k <;> simp [mul_comm]
  | sr a =>
    cases h with
    | r b =>
      rw [DihedralGroup.sr_mul_r]
      change (!![0, (cyclicPhase N j (a + b))⁻¹; cyclicPhase N j (a + b), 0] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![0, (cyclicPhase N j a)⁻¹; cyclicPhase N j a, 0] * !![cyclicPhase N j b, 0; 0, (cyclicPhase N j b)⁻¹]
      rw [Matrix.mul_fin_two, cyclicPhase_add, mul_inv]
      ext i k; fin_cases i <;> fin_cases k <;> simp
    | sr b =>
      rw [DihedralGroup.sr_mul_sr]
      change (!![cyclicPhase N j (b - a), 0; 0, (cyclicPhase N j (b - a))⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![0, (cyclicPhase N j a)⁻¹; cyclicPhase N j a, 0] * !![0, (cyclicPhase N j b)⁻¹; cyclicPhase N j b, 0]
      rw [Matrix.mul_fin_two, cyclicPhase_sub]
      ext i k; fin_cases i <;> fin_cases k <;> simp [mul_comm]

/-- A two-dimensional complex representation of a dihedral group, indexed by a residue modulo its rotation order. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
noncomputable def twoDimensionalRepresentation (N : ℕ) [NeZero N] (j : ZMod N) :
    Representation ℂ (DihedralGroup N) (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' (twoDimensionalRepresentationMatrix N j g)
  map_one' := by rw [twoDimensionalRepresentationMatrix_one]; exact Matrix.toLin'_one
  map_mul' g h := by rw [twoDimensionalRepresentationMatrix_mul, Matrix.toLin'_mul]; rfl

/-- The action of the two-dimensional representation is multiplication by its associated two-by-two matrix. -/
theorem twoDimensionalRepresentation_apply (N : ℕ) [NeZero N] (j : ZMod N) (g : DihedralGroup N)
    (v : Fin 2 → ℂ) : twoDimensionalRepresentation N j g v = (twoDimensionalRepresentationMatrix N j g).mulVec v :=
  Matrix.toLin'_apply _ _

/-- At coordinate zero, a rotation acts by the phase associated with the indices. -/
@[simp] theorem twoDimensionalRepresentation_rotation_apply_zero (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    twoDimensionalRepresentation N j (DihedralGroup.r k) v 0 = cyclicPhase N j k * v 0 := by
  rw [twoDimensionalRepresentation_apply]; simp [twoDimensionalRepresentationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- At coordinate one, a rotation acts by the inverse phase associated with the indices. -/
@[simp] theorem twoDimensionalRepresentation_rotation_apply_one (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    twoDimensionalRepresentation N j (DihedralGroup.r k) v 1 = (cyclicPhase N j k)⁻¹ * v 1 := by
  rw [twoDimensionalRepresentation_apply]; simp [twoDimensionalRepresentationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- At coordinate zero, a reflection sends the one coordinate to the inverse-phase-scaled value. -/
@[simp] theorem twoDimensionalRepresentation_reflection_apply_zero (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    twoDimensionalRepresentation N j (DihedralGroup.sr k) v 0 = (cyclicPhase N j k)⁻¹ * v 1 := by
  rw [twoDimensionalRepresentation_apply]; simp [twoDimensionalRepresentationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- At coordinate one, a reflection sends the zero coordinate to the phase-scaled value. -/
@[simp] theorem twoDimensionalRepresentation_reflection_apply_one (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    twoDimensionalRepresentation N j (DihedralGroup.sr k) v 1 = cyclicPhase N j k * v 0 := by
  rw [twoDimensionalRepresentation_apply]; simp [twoDimensionalRepresentationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- For every nonzero order, the associated auxiliary complex scalar is a primitive root of that order. -/
theorem auxiliaryRootOfUnity_isPrimitiveRoot [NeZero N] : IsPrimitiveRoot (auxiliaryRootOfUnity N) N := by
  unfold auxiliaryRootOfUnity; exact Complex.isPrimitiveRoot_exp N (NeZero.ne N)

/-- When twice the residue index is nonzero, the module associated with the indexed dihedral representation is simple. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem twoDimensionalRepresentation_isSimpleModule [NeZero N] (j : ZMod N) (hj : (2 : ZMod N) * j ≠ 0) :
    IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) (twoDimensionalRepresentation N j).asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hα0 : cyclicPhase N j 1 ≠ 0 := cyclicPhase_ne_zero N j 1
  -- `ζ^j ≠ ζ^{-j}` because `2·j ≠ 0`.
  have hsq : (cyclicPhase N j 1) ^ 2 ≠ 1 := by
    rw [sq, ← cyclicPhase_add]
    intro h
    apply hj
    unfold cyclicPhase at h
    have hdvd : N ∣ (j * (1 + 1)).val := (auxiliaryRootOfUnity_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp h
    have hz : (j * (1 + 1) : ZMod N) = 0 := by
      have h2 := (ZMod.natCast_eq_zero_iff (j * (1 + 1)).val N).mpr hdvd
      rwa [ZMod.natCast_zmod_val] at h2
    rw [show (2 : ZMod N) * j = j * (1 + 1) by ring]
    exact hz
  have hαsub : cyclicPhase N j 1 - (cyclicPhase N j 1)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h; apply hsq
    rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel₀ hα0
  -- The reflection `sr 0` swaps the two coordinate axes.
  have hswap0 : twoDimensionalRepresentation N j (DihedralGroup.sr 0) ![1, 0] = ![0, 1] := by
    funext i; fin_cases i <;> simp [cyclicPhase_zero]
  have hswap1 : twoDimensionalRepresentation N j (DihedralGroup.sr 0) ![0, 1] = ![1, 0] := by
    funext i; fin_cases i <;> simp [cyclicPhase_zero]
  have hNT : Nontrivial (Subrepresentation (twoDimensionalRepresentation N j)) := by
    refine ⟨⊥, ⊤, ?_⟩
    intro h
    exact absurd (congrArg Subrepresentation.toSubmodule h) bot_ne_top
  refine { toNontrivial := hNT, eq_bot_or_eq_top := fun σ => ?_ }
  rcases eq_or_ne σ.toSubmodule ⊥ with hbot | hne
  · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    -- From a nonzero vector we extract a coordinate axis, then the swap gives the other.
    have hget0 : v 0 ≠ 0 → ![(1 : ℂ), 0] ∈ σ.toSubmodule := by
      intro hv0'
      have hD : twoDimensionalRepresentation N j (DihedralGroup.r 1) v - (cyclicPhase N j 1)⁻¹ • v ∈ σ.toSubmodule :=
        Submodule.sub_mem _ (σ.apply_mem_toSubmodule _ hv) (Submodule.smul_mem _ _ hv)
      have heq : twoDimensionalRepresentation N j (DihedralGroup.r 1) v - (cyclicPhase N j 1)⁻¹ • v
          = ((cyclicPhase N j 1 - (cyclicPhase N j 1)⁻¹) * v 0) • ![(1 : ℂ), 0] := by
        funext i
        fin_cases i <;> (simp [Pi.smul_apply, Pi.sub_apply]; try ring)
      rw [heq] at hD
      have hc : (cyclicPhase N j 1 - (cyclicPhase N j 1)⁻¹) * v 0 ≠ 0 := mul_ne_zero hαsub hv0'
      have := Submodule.smul_mem σ.toSubmodule
        (((cyclicPhase N j 1 - (cyclicPhase N j 1)⁻¹) * v 0)⁻¹) hD
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hget1 : v 1 ≠ 0 → ![(0 : ℂ), 1] ∈ σ.toSubmodule := by
      intro hv1'
      have hD : twoDimensionalRepresentation N j (DihedralGroup.r 1) v - (cyclicPhase N j 1) • v ∈ σ.toSubmodule :=
        Submodule.sub_mem _ (σ.apply_mem_toSubmodule _ hv) (Submodule.smul_mem _ _ hv)
      have heq : twoDimensionalRepresentation N j (DihedralGroup.r 1) v - (cyclicPhase N j 1) • v
          = (((cyclicPhase N j 1)⁻¹ - cyclicPhase N j 1) * v 1) • ![(0 : ℂ), 1] := by
        funext i
        fin_cases i <;> (simp [Pi.smul_apply, Pi.sub_apply]; try ring)
      rw [heq] at hD
      have hc : ((cyclicPhase N j 1)⁻¹ - cyclicPhase N j 1) * v 1 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr (sub_ne_zero.mp hαsub).symm) hv1'
      have := Submodule.smul_mem σ.toSubmodule
        ((((cyclicPhase N j 1)⁻¹ - cyclicPhase N j 1) * v 1)⁻¹) hD
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    -- Both coordinate axes lie in `σ`.
    have hbasis : ![(1 : ℂ), 0] ∈ σ.toSubmodule ∧ ![(0 : ℂ), 1] ∈ σ.toSubmodule := by
      by_cases h0 : v 0 = 0
      · have hv1 : v 1 ≠ 0 := by
          intro h1; apply hv0; funext i; fin_cases i <;> simp_all
        have he1 := hget1 hv1
        exact ⟨by rw [← hswap1]; exact σ.apply_mem_toSubmodule _ he1, he1⟩
      · have he0 := hget0 h0
        exact ⟨he0, by rw [← hswap0]; exact σ.apply_mem_toSubmodule _ he0⟩
    -- Hence `σ` is everything.
    change σ.toSubmodule = (⊤ : Submodule ℂ (Fin 2 → ℂ))
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • ![(1 : ℂ), 0] + x 1 • ![(0 : ℂ), 1] := by
      funext i; fin_cases i <;> simp
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hbasis.1)
      (Submodule.smul_mem _ _ hbasis.2)

/-- The trace of a rotation action is the associated phase plus its inverse. -/
theorem trace_twoDimensionalRepresentation_rotation [NeZero N] (j k : ZMod N) :
    LinearMap.trace ℂ (Fin 2 → ℂ) (twoDimensionalRepresentation N j (DihedralGroup.r k)) =
      cyclicPhase N j k + (cyclicPhase N j k)⁻¹ := by
  have hrfl : twoDimensionalRepresentation N j (DihedralGroup.r k) = Matrix.toLin' (twoDimensionalRepresentationMatrix N j (DihedralGroup.r k)) := rfl
  rw [hrfl, Matrix.trace_toLin'_eq]
  simp [twoDimensionalRepresentationMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- If the displayed phase sums for two indices differ, no linear equivalence intertwines the corresponding representations at every group element. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem twoDimensionalRepresentations_not_equivalent_of_trace_ne [NeZero N] {j j' : ZMod N}
    (hne : cyclicPhase N j 1 + (cyclicPhase N j 1)⁻¹ ≠ cyclicPhase N j' 1 + (cyclicPhase N j' 1)⁻¹) :
    ¬ ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
        ∀ g, T.toLinearMap.comp (twoDimensionalRepresentation N j g) = (twoDimensionalRepresentation N j' g).comp T.toLinearMap := by
  rintro ⟨T, hT⟩
  have hconj : T.conj (twoDimensionalRepresentation N j (DihedralGroup.r 1)) = twoDimensionalRepresentation N j' (DihedralGroup.r 1) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply]
    have h := LinearMap.congr_fun (hT (DihedralGroup.r 1)) (T.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    exact h
  have htr := LinearMap.trace_conj' (twoDimensionalRepresentation N j (DihedralGroup.r 1)) T
  rw [hconj, trace_twoDimensionalRepresentation_rotation, trace_twoDimensionalRepresentation_rotation] at htr
  exact hne htr.symm

/-!
## Part (a): the one-dimensional characters and their count

A one-dimensional complex representation of `DihedralGroup N` is a group homomorphism
`χ : DihedralGroup N →* ℂˣ`.  Such a `χ` is determined by the two values `u = χ (r 1)` and
`w = χ (sr 0)` on the generators, subject to `u ^ N = 1` (the order of `r`), `w ^ 2 = 1` (the
order of `sr`), and `u ^ 2 = 1` (the dihedral relation `sr · r · sr = r⁻¹` forces
`χ (r 1) = χ (r 1)⁻¹`).  Conversely every such pair `(u, w)` extends to a character.  Counting
the pairs gives `2` characters for odd `N` and `4` for even `N`.
-/

section OneDim

variable [NeZero N]

omit [NeZero N] in
/-- If the Nth power of a complex unit is one, reducing a natural exponent modulo N does not change the resulting power. -/
theorem unit_pow_mod_eq_pow_of_pow_eq_one (u : ℂˣ) (hu : u ^ N = 1) (k : ℕ) : u ^ (k % N) = u ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k N, pow_add, pow_mul, hu, one_pow, mul_one]

/-- If a complex unit has Nth power one, exponentiation by representatives of residues modulo N converts residue addition into multiplication. -/
theorem unit_pow_zmod_add_val (u : ℂˣ) (hu : u ^ N = 1) (a b : ZMod N) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  rw [ZMod.val_add, unit_pow_mod_eq_pow_of_pow_eq_one u hu, pow_add]

/-- A complex-unit-valued homomorphism on a dihedral group constructed from two units satisfying the required order-two and order-N relations. -/
def linearCharacterOfUnitPair (u w : ℂˣ) (huN : u ^ N = 1) (hu2 : u ^ 2 = 1) (hw2 : w ^ 2 = 1) :
    DihedralGroup N →* ℂˣ where
  toFun g := match g with
    | .r k => u ^ k.val
    | .sr k => w * u ^ k.val
  map_one' := by change u ^ (0 : ZMod N).val = 1; rw [ZMod.val_zero, pow_zero]
  map_mul' g h := by
    have hadd : ∀ a b : ZMod N, u ^ (a + b).val = u ^ a.val * u ^ b.val := unit_pow_zmod_add_val u huN
    have hself : ∀ a : ZMod N, u ^ a.val * u ^ a.val = 1 := fun a => by
      rw [← pow_add, ← two_mul, pow_mul, hu2, one_pow]
    have hsub : ∀ a b : ZMod N, u ^ (a - b).val = u ^ a.val * u ^ b.val := by
      intro a b
      have h1 : u ^ ((-b).val) * u ^ b.val = 1 := by
        rw [← hadd, neg_add_cancel, ZMod.val_zero, pow_zero]
      have hnb : u ^ ((-b).val) = u ^ b.val :=
        mul_right_cancel (h1.trans (hself b).symm)
      rw [sub_eq_add_neg, hadd, hnb]
    have hww : w * w = 1 := by rw [← pow_two, hw2]
    cases g with
    | r a => cases h with
      | r b =>
        rw [DihedralGroup.r_mul_r]
        change u ^ (a + b).val = u ^ a.val * u ^ b.val
        exact hadd a b
      | sr b =>
        rw [DihedralGroup.r_mul_sr]
        change w * u ^ (b - a).val = u ^ a.val * (w * u ^ b.val)
        rw [hsub]; ac_rfl
    | sr a => cases h with
      | r b =>
        rw [DihedralGroup.sr_mul_r]
        change w * u ^ (a + b).val = (w * u ^ a.val) * u ^ b.val
        rw [hadd]; ac_rfl
      | sr b =>
        rw [DihedralGroup.sr_mul_sr]
        change u ^ (b - a).val = (w * u ^ a.val) * (w * u ^ b.val)
        rw [hsub, show (w * u ^ a.val) * (w * u ^ b.val)
              = (w * w) * (u ^ a.val * u ^ b.val) from by ac_rfl, hww, one_mul]
        ac_rfl

/-- The homomorphism constructed from a unit pair sends a rotation to the corresponding power of the first unit. -/
@[simp] theorem linearCharacterOfUnitPair_rotation (u w : ℂˣ) (huN : u ^ N = 1) (hu2 : u ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (k : ZMod N) : linearCharacterOfUnitPair u w huN hu2 hw2 (DihedralGroup.r k) = u ^ k.val := rfl

/-- The homomorphism constructed from a unit pair sends a reflection to the second unit times the corresponding power of the first. -/
@[simp] theorem linearCharacterOfUnitPair_reflection (u w : ℂˣ) (huN : u ^ N = 1) (hu2 : u ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (k : ZMod N) : linearCharacterOfUnitPair u w huN hu2 hw2 (DihedralGroup.sr k) = w * u ^ k.val := rfl

/-- Complex-unit-valued homomorphisms from a dihedral group are equivalent to pairs of units satisfying the displayed power constraints. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
def linearCharactersEquivUnitPairs (N : ℕ) [NeZero N] :
    (DihedralGroup N →* ℂˣ) ≃
      {p : ℂˣ × ℂˣ // (p.1 ^ N = 1 ∧ p.1 ^ 2 = 1) ∧ p.2 ^ 2 = 1} where
  toFun χ := by
    refine ⟨(χ (DihedralGroup.r 1), χ (DihedralGroup.sr 0)), ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [← map_pow, DihedralGroup.r_one_pow_n, map_one]
    · -- the dihedral relation forces `χ (r 1) ^ 2 = 1`
      have hs2 : χ (DihedralGroup.sr 0) * χ (DihedralGroup.sr 0) = 1 := by
        rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
      have hrel : (DihedralGroup.r 1 : DihedralGroup N)⁻¹
          = DihedralGroup.sr 0 * DihedralGroup.r 1 * DihedralGroup.sr 0 := by
        rw [DihedralGroup.inv_r, DihedralGroup.sr_mul_r, zero_add, DihedralGroup.sr_mul_sr]
        congr 1; ring
      have key : χ (DihedralGroup.sr 0) * χ (DihedralGroup.r 1) * χ (DihedralGroup.sr 0)
          = χ (DihedralGroup.r 1) := by rw [mul_right_comm, hs2, one_mul]
      have hinv : (χ (DihedralGroup.r 1))⁻¹ = χ (DihedralGroup.r 1) := by
        rw [← map_inv, hrel, map_mul, map_mul, key]
      rw [pow_two]; nth_rewrite 2 [← hinv]; exact mul_inv_cancel _
    · rw [← map_pow, pow_two, DihedralGroup.sr_mul_self, map_one]
  invFun p := linearCharacterOfUnitPair p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2
  left_inv χ := by
    ext g
    cases g with
    | r k =>
      simp only [linearCharacterOfUnitPair_rotation]
      rw [← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    | sr k =>
      simp only [linearCharacterOfUnitPair_reflection]
      rw [← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, ← map_mul,
        DihedralGroup.sr_mul_r, zero_add]
  right_inv p := by
    obtain ⟨⟨u, w⟩, ⟨⟨huN, hu2⟩, hw2⟩⟩ := p
    apply Subtype.ext
    have hval1 : (1 : ZMod N).val = 1 % N := by
      rw [← Nat.cast_one (R := ZMod N), ZMod.val_natCast]
    refine Prod.ext ?_ ?_
    · change linearCharacterOfUnitPair u w huN hu2 hw2 (DihedralGroup.r 1) = u
      rw [linearCharacterOfUnitPair_rotation, hval1, unit_pow_mod_eq_pow_of_pow_eq_one u huN, pow_one]
    · change linearCharacterOfUnitPair u w huN hu2 hw2 (DihedralGroup.sr 0) = w
      rw [linearCharacterOfUnitPair_reflection, ZMod.val_zero, pow_zero, mul_one]

/-- There are exactly two complex units whose square is one. -/
theorem card_complexUnits_sq_eq_one : Nat.card {w : ℂˣ // w ^ 2 = 1} = 2 := by
  have e : {w : ℂˣ // w ^ 2 = 1} ≃ (rootsOfUnity 2 ℂ) :=
    Equiv.subtypeEquivRight (fun w => (mem_rootsOfUnity 2 w).symm)
  rw [Nat.card_congr e, Complex.card_rootsOfUnity]

omit [NeZero N] in
/-- For an odd exponent, exactly one complex unit has both the given power and its square equal to one. -/
theorem card_complexUnits_pow_eq_one_and_sq_eq_one_of_odd (hodd : Odd N) : Nat.card {u : ℂˣ // u ^ N = 1 ∧ u ^ 2 = 1} = 1 := by
  have hforce : ∀ u : ℂˣ, u ^ N = 1 → u ^ 2 = 1 → u = 1 := by
    intro u huN hu2
    have hg : Nat.gcd N 2 = 1 := Nat.coprime_two_right.mpr hodd
    have hd : orderOf u ∣ 1 :=
      hg ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one huN) (orderOf_dvd_of_pow_eq_one hu2)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨⟨1, one_pow N, one_pow 2⟩⟩⟩
  exact Subtype.ext ((hforce x.1 x.2.1 x.2.2).trans (hforce y.1 y.2.1 y.2.2).symm)

/-- For a nonzero even exponent, exactly two complex units have both the given power and their square equal to one. -/
theorem card_complexUnits_pow_eq_one_and_sq_eq_one_of_even (heven : Even N) : Nat.card {u : ℂˣ // u ^ N = 1 ∧ u ^ 2 = 1} = 2 := by
  have hiff : ∀ u : ℂˣ, (u ^ N = 1 ∧ u ^ 2 = 1) ↔ u ^ 2 = 1 := by
    intro u
    refine ⟨fun h => h.2, fun h2 => ⟨?_, h2⟩⟩
    obtain ⟨m, rfl⟩ := heven
    rw [show m + m = 2 * m from by ring, pow_mul, h2, one_pow]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), card_complexUnits_sq_eq_one]

/-- A dihedral group of nonzero odd rotation order has two complex-unit-valued linear characters. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem card_linearCharacters_of_odd (hodd : Odd N) : Nat.card (DihedralGroup N →* ℂˣ) = 2 := by
  rw [Nat.card_congr (linearCharactersEquivUnitPairs N),
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun u : ℂˣ => u ^ N = 1 ∧ u ^ 2 = 1)
      (q := fun w : ℂˣ => w ^ 2 = 1)),
    Nat.card_prod, card_complexUnits_pow_eq_one_and_sq_eq_one_of_odd hodd, card_complexUnits_sq_eq_one]

/-- A dihedral group of nonzero even rotation order has four complex-unit-valued linear characters. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem card_linearCharacters_of_even (heven : Even N) : Nat.card (DihedralGroup N →* ℂˣ) = 4 := by
  rw [Nat.card_congr (linearCharactersEquivUnitPairs N),
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun u : ℂˣ => u ^ N = 1 ∧ u ^ 2 = 1)
      (q := fun w : ℂˣ => w ^ 2 = 1)),
    Nat.card_prod, card_complexUnits_pow_eq_one_and_sq_eq_one_of_even heven, card_complexUnits_sq_eq_one]

end OneDim

/-!
## Part (a): exhaustiveness and the odd/even irreducible counts

We now assemble the full classification. The one-dimensional characters
`χ : DihedralGroup N →* ℂˣ` (counted by `card_linearCharacters_of_odd`/`_even`) together with the
two-dimensional `twoDimensionalRepresentation N j` (`2·j ≠ 0`, indexed up to `j ~ -j`) form a complete family of
pairwise non-isomorphic irreducibles whose squared dimensions sum to `|G| = 2N`. By the
Artin-Wedderburn count
(`RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card`)
and a pigeonhole argument,
this family is exactly the set of simples up to isomorphism.
-/

section Classification

open _root_.CategoryTheory

variable [NeZero N]

omit [NeZero N] in
/-- At residue one, the cyclic phase is the corresponding power of the auxiliary complex root. -/
theorem cyclicPhase_one (j : ZMod N) : cyclicPhase N j 1 = auxiliaryRootOfUnity N ^ j.val := by
  rw [cyclicPhase, mul_one]

/-- An auxiliary type depending on a nonzero natural number. -/
abbrev AuxiliaryParameter (N : ℕ) [NeZero N] : Type := {j : ZMod N // 0 < j.val ∧ 2 * j.val < N}

/-- Twice the underlying residue of an auxiliary parameter is nonzero. -/
theorem AuxiliaryParameter.two_mul_val_ne_zero (j : AuxiliaryParameter N) : (2 : ZMod N) * j.1 ≠ 0 := by
  obtain ⟨hpos, hlt⟩ := j.2
  intro hz
  rw [two_mul] at hz
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_add, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hval
  omega

/-- The auxiliary parameter type has cardinality the natural quotient of one less than the rotation order by two. -/
theorem card_auxiliaryParameter : Fintype.card (AuxiliaryParameter N) = (N - 1) / 2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  let e : AuxiliaryParameter N ≃ Fin ((N - 1) / 2) :=
    { toFun := fun j => ⟨j.1.val - 1, by
        obtain ⟨hpos, hlt⟩ := j.2
        have : j.1.val ≤ (N - 1) / 2 := by omega
        omega⟩
      invFun := fun i => ⟨((i.1 + 1 : ℕ) : ZMod N), by
        have hi : i.1 + 1 < N := by have := i.2; omega
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
        have := i.2; omega⟩
      left_inv := fun j => by
        obtain ⟨hpos, hlt⟩ := j.2
        apply Subtype.ext
        change ((j.1.val - 1 + 1 : ℕ) : ZMod N) = j.1
        rw [Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]
      right_inv := fun i => by
        apply Fin.ext
        change ((i.1 + 1 : ℕ) : ZMod N).val - 1 = i.1
        have hi : i.1 + 1 < N := by have := i.2; omega
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
        omega }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- An injective map into a finite index type is surjective when it preserves the total sum of a strictly positive weight function. -/
theorem surjective_of_injective_and_sum_eq {n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin n → ℕ) (hf : ∀ j, 0 < f j) (c : ι → Fin n) (hcinj : Function.Injective c)
    (hsum : ∑ i, f (c i) = ∑ j, f j) : Function.Surjective c := by
  classical
  have himg : ∑ j ∈ Finset.image c Finset.univ, f j = ∑ i, f (c i) :=
    Finset.sum_image (fun a _ b _ hab => hcinj hab)
  have hsplit := Finset.sum_sdiff (f := f) (Finset.subset_univ (Finset.image c Finset.univ))
  rw [himg, hsum] at hsplit
  have hzero : ∑ j ∈ Finset.univ \ Finset.image c Finset.univ, f j = 0 := by omega
  intro j
  have hjmem : j ∈ Finset.image c Finset.univ := by
    by_contra hj
    exact absurd ((Finset.sum_eq_zero_iff.mp hzero) j
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)) (hf j).ne'
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hjmem
  exact ⟨i, hi⟩

/-- The two-dimensional representation is simple when twice its residue index is nonzero. -/
theorem twoDimensionalRepresentation_simple (j : ZMod N) (hj : (2 : ZMod N) * j ≠ 0) :
    Simple (FDRep.of (twoDimensionalRepresentation N j)) := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) (twoDimensionalRepresentation N j).asModule :=
    twoDimensionalRepresentation_isSimpleModule j hj
  exact RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule (twoDimensionalRepresentation N j)

/-- The underlying complex vector space of the indexed representation has dimension two. -/
theorem twoDimensionalRepresentation_finrank (j : ZMod N) : Module.finrank ℂ (FDRep.of (twoDimensionalRepresentation N j)) = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- On a rotation, the character of the two-dimensional representation is the sum of a phase and its inverse. -/
theorem twoDimensionalRepresentation_character_rotation (j k : ZMod N) :
    (FDRep.of (twoDimensionalRepresentation N j)).character (DihedralGroup.r k) = cyclicPhase N j k + (cyclicPhase N j k)⁻¹ := by
  have hc : (FDRep.of (twoDimensionalRepresentation N j)).character (DihedralGroup.r k)
      = LinearMap.trace ℂ _ (twoDimensionalRepresentation N j (DihedralGroup.r k)) := rfl
  rw [hc, trace_twoDimensionalRepresentation_rotation]

/-- Two auxiliary parameters are equal when the displayed sums of their associated phase and its inverse agree. -/
theorem AuxiliaryParameter.ext (j j' : AuxiliaryParameter N)
    (h : cyclicPhase N j.1 1 + (cyclicPhase N j.1 1)⁻¹ = cyclicPhase N j'.1 1 + (cyclicPhase N j'.1 1)⁻¹) :
    j = j' := by
  set a := cyclicPhase N j.1 1 with ha_def
  set b := cyclicPhase N j'.1 1 with hb_def
  have ha : a ≠ 0 := cyclicPhase_ne_zero N j.1 1
  have hb : b ≠ 0 := cyclicPhase_ne_zero N j'.1 1
  have hkey : (a - b) * (a * b - 1) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp hkey with hab0 | hab1
  · -- a = b : same eigenvalue, so equal `val`
    have hEq : a = b := sub_eq_zero.mp hab0
    rw [ha_def, hb_def, cyclicPhase_one, cyclicPhase_one] at hEq
    have hval : (j.1).val = (j'.1).val :=
      auxiliaryRootOfUnity_isPrimitiveRoot.pow_inj (ZMod.val_lt j.1) (ZMod.val_lt j'.1) hEq
    exact Subtype.ext (ZMod.val_injective N hval)
  · -- a·b = 1 : forces `j' = -j`, impossible under the normalization
    exfalso
    have hab1' : a * b = 1 := by linear_combination hab1
    rw [ha_def, hb_def, cyclicPhase_one, cyclicPhase_one, ← pow_add] at hab1'
    have hdvd : N ∣ (j.1).val + (j'.1).val :=
      (auxiliaryRootOfUnity_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp hab1'
    obtain ⟨hpos, hlt⟩ := j.2
    obtain ⟨hpos', hlt'⟩ := j'.2
    have hsum_pos : 0 < (j.1).val + (j'.1).val := by omega
    have hsum_lt : (j.1).val + (j'.1).val < N := by omega
    exact absurd (Nat.le_of_dvd hsum_pos hdvd) (by omega)

/-- Every simple finite-dimensional complex representation of a dihedral group is isomorphic either to a one-dimensional representation from a linear character or to an indexed two-dimensional representation with nonzero doubled index. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem simpleRepresentation_iso_linear_or_twoDimensional
    (U : FDRep ℂ (DihedralGroup N)) [hUsimple : Simple U] :
    (∃ χ : DihedralGroup N →* ℂˣ,
        Nonempty (U ≅ FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ))) ∨
    (∃ j : ZMod N, (2 : ZMod N) * j ≠ 0 ∧
        Nonempty (U ≅ FDRep.of (twoDimensionalRepresentation N j))) := by
  classical
  -- `|G| = 2N` is invertible in `ℂ`, so the Wedderburn enumeration applies.
  haveI hNe : NeZero (Nat.card (DihedralGroup N) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    push_cast
    simpa using mul_ne_zero two_ne_zero hN
  -- The complete family of simples with `∑ dim² = |G| = 2N`.
  obtain ⟨n, V, hVsimple, _hVinj, hVsurj, hVsum⟩ :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ (DihedralGroup N)
  -- Finiteness (and a `Fintype`) of the character group.
  haveI : Finite (DihedralGroup N →* ℂˣ) := by
    rcases Nat.even_or_odd N with h | h
    · exact Nat.finite_of_card_ne_zero (by rw [card_linearCharacters_of_even h]; norm_num)
    · exact Nat.finite_of_card_ne_zero (by rw [card_linearCharacters_of_odd h]; norm_num)
  haveI : Fintype (DihedralGroup N →* ℂˣ) := Fintype.ofFinite _
  -- The exhibited family: the characters, and the `2`-dim reps at canonical indices.
  let E : (DihedralGroup N →* ℂˣ) ⊕ AuxiliaryParameter N → FDRep ℂ (DihedralGroup N) :=
    Sum.elim (fun χ => FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ))
      (fun j => FDRep.of (twoDimensionalRepresentation N j.1))
  have hEfinL : ∀ χ : DihedralGroup N →* ℂˣ, Module.finrank ℂ (E (Sum.inl χ)) = 1 :=
    fun _ => Module.finrank_self ℂ
  have hEfinR : ∀ j : AuxiliaryParameter N, Module.finrank ℂ (E (Sum.inr j)) = 2 :=
    fun j => twoDimensionalRepresentation_finrank j.1
  have hEsimple : ∀ i, Simple (E i) := by
    rintro (χ | j)
    · exact RepresentationTheory.PermutationDegreeThree.simple_representationOfUnitCharacter χ
    · exact twoDimensionalRepresentation_simple j.1 (AuxiliaryParameter.two_mul_val_ne_zero j)
  -- The members are pairwise non-isomorphic.
  have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
    rintro (χ | j) (χ' | j') ⟨α⟩
    · -- two characters: equal character forces `χ = χ'`
      have hχ : χ = χ' := by
        ext g
        have hg := congrFun (FDRep.char_iso α) g
        rw [show E (Sum.inl χ) = FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) from rfl,
            show E (Sum.inl χ') = FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ') from rfl,
            RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter,
            RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter] at hg
        exact_mod_cast hg
      rw [hχ]
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinL χ, hEfinR j'] at hfr; omega
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinR j, hEfinL χ'] at hfr; omega
    · -- two `2`-dim reps: character at `r 1` separates them
      have hg := congrFun (FDRep.char_iso α) (DihedralGroup.r 1)
      rw [show E (Sum.inr j) = FDRep.of (twoDimensionalRepresentation N j.1) from rfl,
          show E (Sum.inr j') = FDRep.of (twoDimensionalRepresentation N j'.1) from rfl,
          twoDimensionalRepresentation_character_rotation, twoDimensionalRepresentation_character_rotation] at hg
      exact congrArg Sum.inr (AuxiliaryParameter.ext j j' hg)
  -- Inject the family into the enumeration.
  choose c hc using fun i => hVsurj (E i) (hEsimple i)
  have hc_inj : Function.Injective c := by
    intro i j hij
    obtain ⟨αi⟩ := hc i; obtain ⟨αj⟩ := hc j
    exact hEinj i j ⟨αi ≪≫ eqToIso (congrArg V hij) ≪≫ αj.symm⟩
  have hfinrankc : ∀ i, Module.finrank ℂ (E i) = Module.finrank ℂ (V (c i)) := fun i =>
    LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hc i).some)
  -- Squared dimensions of the family sum to `2N`.
  have hEsum : ∑ i, (Module.finrank ℂ (E i)) ^ 2 = 2 * N := by
    rw [Fintype.sum_sum_type]
    have hL : ∑ χ : DihedralGroup N →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2
        = Fintype.card (DihedralGroup N →* ℂˣ) := by
      have hone : ∀ χ : DihedralGroup N →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = 1 := by
        intro χ; rw [hEfinL χ, one_pow]
      rw [Finset.sum_congr rfl (fun χ _ => hone χ), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_one]
    have hR : ∑ j : AuxiliaryParameter N, (Module.finrank ℂ (E (Sum.inr j))) ^ 2
        = 4 * Fintype.card (AuxiliaryParameter N) := by
      have hfour : ∀ j : AuxiliaryParameter N, (Module.finrank ℂ (E (Sum.inr j))) ^ 2 = 4 := by
        intro j; rw [hEfinR j]; norm_num
      rw [Finset.sum_congr rfl (fun j _ => hfour j), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]
    rw [hL, hR]
    -- `#chars + 4·#idx = 2N`, by parity.
    rcases Nat.even_or_odd N with h | h
    · rw [← Nat.card_eq_fintype_card, card_linearCharacters_of_even h, card_auxiliaryParameter]
      obtain ⟨m, rfl⟩ := h
      have hm : m ≠ 0 := by have := (NeZero.ne (m + m)); omega
      omega
    · rw [← Nat.card_eq_fintype_card, card_linearCharacters_of_odd h, card_auxiliaryParameter]
      obtain ⟨m, rfl⟩ := h
      omega
  -- The full sum of squared dimensions is also `2N`.
  have hVsum2 : ∑ j, (Module.finrank ℂ (V j)) ^ 2 = 2 * N := by
    rw [hVsum, DihedralGroup.card]
  have hmatch : ∑ i, (Module.finrank ℂ (V (c i))) ^ 2 = ∑ j, (Module.finrank ℂ (V j)) ^ 2 := by
    rw [hVsum2, ← hEsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hfinrankc i])
  -- Every simple has positive dimension, so the injection `c` is surjective.
  have hVpos : ∀ j, 0 < (Module.finrank ℂ (V j)) ^ 2 := by
    intro j
    haveI : Simple (V j) := hVsimple j
    haveI : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) (Representation.asModule (V j).ρ) :=
      RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep (V j)
    haveI : Nontrivial (Representation.asModule (V j).ρ) :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (DihedralGroup N)) _
    haveI : Nontrivial ↥(V j) := (Representation.asModuleEquiv (V j).ρ).symm.toEquiv.nontrivial
    exact pow_pos Module.finrank_pos 2
  have hcsurj : Function.Surjective c :=
    surjective_of_injective_and_sum_eq _ hVpos c hc_inj hmatch
  -- Read off the branch of the index matching `U`.
  obtain ⟨j0, hj0U⟩ := hVsurj U hUsimple
  obtain ⟨i, hci⟩ := hcsurj j0
  have hUEi : Nonempty (U ≅ E i) :=
    ⟨hj0U.some ≪≫ eqToIso (congrArg V hci).symm ≪≫ (hc i).some.symm⟩
  rcases i with χ | j
  · exact Or.inl ⟨χ, hUEi⟩
  · exact Or.inr ⟨j.1, AuxiliaryParameter.two_mul_val_ne_zero j, hUEi⟩

/-- For nonzero odd rotation order, the auxiliary parameter type has cardinality half of one less than the order. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem card_auxiliaryParameter_of_odd (_hodd : Odd N) :
    Fintype.card (AuxiliaryParameter N) = (N - 1) / 2 := card_auxiliaryParameter

/-- For nonzero even rotation order, the auxiliary parameter type has cardinality half of two less than the order. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem card_auxiliaryParameter_of_even (heven : Even N) :
    Fintype.card (AuxiliaryParameter N) = (N - 2) / 2 := by
  rw [card_auxiliaryParameter]; obtain ⟨m, rfl⟩ := heven; omega

/-- The number of linear characters plus four times the number of auxiliary parameters equals twice the rotation order. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem card_linearCharacters_add_four_mul_card_auxiliaryParameter :
    Nat.card (DihedralGroup N →* ℂˣ) * 1 + Fintype.card (AuxiliaryParameter N) * 4 = 2 * N := by
  rw [card_auxiliaryParameter]
  rcases Nat.even_or_odd N with h | h
  · rw [card_linearCharacters_of_even h]; obtain ⟨m, rfl⟩ := h
    have hm : m ≠ 0 := by have := (NeZero.ne (m + m)); omega
    omega
  · rw [card_linearCharacters_of_odd h]; obtain ⟨m, rfl⟩ := h; omega

/-- For nonzero odd rotation order, the number of linear characters plus auxiliary parameters equals two plus half of one less than the order. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem card_linearCharacters_add_card_auxiliaryParameter_of_odd (hodd : Odd N) :
    Nat.card (DihedralGroup N →* ℂˣ) + Fintype.card (AuxiliaryParameter N) = 2 + (N - 1) / 2 := by
  rw [card_linearCharacters_of_odd hodd, card_auxiliaryParameter]

/-- For nonzero even rotation order, the number of linear characters plus auxiliary parameters equals four plus half of two less than the order. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem card_linearCharacters_add_card_auxiliaryParameter_of_even (heven : Even N) :
    Nat.card (DihedralGroup N →* ℂˣ) + Fintype.card (AuxiliaryParameter N) = 4 + (N - 2) / 2 := by
  rw [card_linearCharacters_of_even heven, card_auxiliaryParameter_of_even heven]

end Classification

section Decomposition

open _root_.CategoryTheory MonoidalCategory

variable {N : ℕ}

/-- The trace of a reflection action in the two-dimensional representation is zero. -/
theorem trace_twoDimensionalRepresentation_reflection [NeZero N] (j k : ZMod N) :
    LinearMap.trace ℂ (Fin 2 → ℂ) (twoDimensionalRepresentation N j (DihedralGroup.sr k)) = 0 := by
  have hrfl : twoDimensionalRepresentation N j (DihedralGroup.sr k)
      = Matrix.toLin' (twoDimensionalRepresentationMatrix N j (DihedralGroup.sr k)) := rfl
  rw [hrfl, Matrix.trace_toLin'_eq]
  simp [twoDimensionalRepresentationMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- On a reflection, the character of the two-dimensional representation is zero. -/
theorem twoDimensionalRepresentation_character_reflection [NeZero N] (j k : ZMod N) :
    (FDRep.of (twoDimensionalRepresentation N j)).character (DihedralGroup.sr k) = 0 := by
  have hc : (FDRep.of (twoDimensionalRepresentation N j)).character (DihedralGroup.sr k)
      = LinearMap.trace ℂ _ (twoDimensionalRepresentation N j (DihedralGroup.sr k)) := rfl
  rw [hc, trace_twoDimensionalRepresentation_reflection]

/-- The character of the representation indexed by one agrees with the third auxiliary class function. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem twoDimensionalRepresentation_one_character [NeZero N] (g : DihedralGroup N) :
    (FDRep.of (twoDimensionalRepresentation N 1)).character g = auxiliaryClassFunctionC N g := by
  cases g with
  | r k => rw [twoDimensionalRepresentation_character_rotation]; simp only [auxiliaryClassFunctionC, cyclicPhase, one_mul, inv_pow]
  | sr k => rw [twoDimensionalRepresentation_character_reflection]; rfl

/-- The character of the representation indexed by two agrees with the first auxiliary class function. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem twoDimensionalRepresentation_two_character [NeZero N] (g : DihedralGroup N) :
    (FDRep.of (twoDimensionalRepresentation N 2)).character g = auxiliaryClassFunctionA N g := by
  cases g with
  | r k =>
    have hval : ((2 : ZMod N) * k).val = (2 * k.val) % N := by
      have h : (2 : ZMod N) * k = ((2 * k.val : ℕ) : ZMod N) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [h, ZMod.val_natCast]
    have h2 : cyclicPhase N 2 k = auxiliaryRootOfUnity N ^ (2 * k.val) := by
      unfold cyclicPhase; rw [hval, auxiliaryRootOfUnity_pow_mod]
    rw [twoDimensionalRepresentation_character_rotation, h2]; simp only [auxiliaryClassFunctionA, inv_pow]
  | sr k => rw [twoDimensionalRepresentation_character_reflection]; rfl

/-- The one-dimensional complex representation associated with a complex-unit-valued dihedral group homomorphism. -/
def representationOfLinearCharacter (χ : DihedralGroup N →* ℂˣ) : Representation ℂ (DihedralGroup N) ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The character of the one-dimensional representation associated with a homomorphism is the complex value of that homomorphism. -/
theorem representationOfLinearCharacter_character (χ : DihedralGroup N →* ℂˣ) (g : DihedralGroup N) :
    (FDRep.of (representationOfLinearCharacter χ)).character g = (χ g : ℂ) := by
  have hg : representationOfLinearCharacter χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (representationOfLinearCharacter χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- An auxiliary complex-unit-valued homomorphism on each dihedral group. -/
def auxiliaryLinearCharacter (N : ℕ) : DihedralGroup N →* ℂˣ where
  toFun g := match g with
    | .r _ => 1
    | .sr _ => -1
  map_one' := by rw [DihedralGroup.one_def]
  map_mul' a b := by
    cases a <;> cases b <;>
      simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr]

/-- The complex value of the auxiliary linear character equals the second auxiliary class function. -/
theorem auxiliaryLinearCharacter_val (g : DihedralGroup N) :
    ((auxiliaryLinearCharacter N g : ℂˣ) : ℂ) = auxiliaryClassFunctionB N g := by
  cases g with
  | r k => rfl
  | sr k => rfl

/-- The character of the product of two finite-dimensional dihedral representations is the sum of their characters. -/
theorem character_prod {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (DihedralGroup N) V) (σ : Representation ℂ (DihedralGroup N) W)
    (g : DihedralGroup N) :
    (FDRep.of (ρ.prod σ)).character g
      = (FDRep.of ρ).character g + (FDRep.of σ).character g := by
  change LinearMap.trace ℂ (V × W) ((ρ.prod σ) g)
    = LinearMap.trace ℂ V (ρ g) + LinearMap.trace ℂ W (σ g)
  have h : (ρ.prod σ) g = (ρ g).prodMap (σ g) := rfl
  rw [h]; exact LinearMap.trace_prodMap' (ρ g) (σ g)

/-- An auxiliary complex representation on a product of two scalar components and a two-dimensional component. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
noncomputable def auxiliaryDirectSumRepresentation (N : ℕ) [NeZero N] :
    Representation ℂ (DihedralGroup N) (ℂ × ℂ × (Fin 2 → ℂ)) :=
  (representationOfLinearCharacter (1 : DihedralGroup N →* ℂˣ)).prod ((representationOfLinearCharacter (auxiliaryLinearCharacter N)).prod (twoDimensionalRepresentation N 2))

/-- The character of the auxiliary product-space representation is one plus the second and first auxiliary class functions. -/
theorem auxiliaryDirectSumRepresentation_character [NeZero N] (g : DihedralGroup N) :
    (FDRep.of (auxiliaryDirectSumRepresentation N)).character g = 1 + auxiliaryClassFunctionB N g + auxiliaryClassFunctionA N g := by
  rw [auxiliaryDirectSumRepresentation, character_prod, character_prod, representationOfLinearCharacter_character, representationOfLinearCharacter_character,
    twoDimensionalRepresentation_two_character, auxiliaryLinearCharacter_val]
  simp only [MonoidHom.one_apply, Units.val_one]
  ring

/-- The tensor square of the representation indexed by one is isomorphic to the auxiliary product-space representation. -/
@[source_ref "Chapter4/Problem4.12.1" (role := supporting)]
theorem tensorSquare_twoDimensionalRepresentation_one_iso_auxiliaryDirectSum [NeZero N] :
    Nonempty ((FDRep.of (twoDimensionalRepresentation N 1) ⊗ FDRep.of (twoDimensionalRepresentation N 1)) ≅ FDRep.of (auxiliaryDirectSumRepresentation N)) := by
  apply RepresentationTheory.Group.CharacterAuxiliary.iso_of_character_eq (DihedralGroup N)
  funext g
  rw [FDRep.char_tensor, Pi.mul_apply, twoDimensionalRepresentation_one_character, auxiliaryDirectSumRepresentation_character,
    ← sq, auxiliaryClassFunctionC_sq]

end Decomposition

end RepresentationTheory.DihedralGroupComplexRepresentations
