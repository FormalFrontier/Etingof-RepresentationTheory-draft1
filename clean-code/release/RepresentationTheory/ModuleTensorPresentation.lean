/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorCoordinateMaps
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-- Scalar multiplication by a field element agrees with scalar multiplication by the corresponding constant function. -/
theorem smul_eq_const_smul (r : k) (a : PathAlgebra k Q) :
    r • a = (Function.const Q r : Q → k) • a := by
  rw [smul_eq_mul_image]
  have h1 : functionRingHom k Q (Function.const Q r) = r • (1 : PathAlgebra k Q) := by
    have hone : (1 : PathAlgebra k Q)
        = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) (1 : k) := by
      have := (functionRingHom k Q).map_one
      rw [functionRingHom_apply] at this
      simp only [Pi.one_apply] at this
      exact this.symm
    rw [functionRingHom_apply, hone, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.const_apply, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, mul_smul_comm, mul_one]

/-- An auxiliary operation taking an index, a field scalar, and an element of the displayed source carrier to the target carrier. -/
noncomputable def auxiliaryTerm (x : Quiver.BundledPath Q) (c : k) (m : secondaryFunctionModuleObject M) :
    secondaryAuxiliaryModuleObject M :=
  match x with
  | ⟨_, _, .nil⟩ => 0
  | ⟨a, d, .cons (b := b) p e⟩ =>
      ((c • ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, d, e⟩ : Edge Q) (1 : k) : FieldQuiverAuxiliary k Q) ⊗ₜ[Q → k] m
          : functionModuleObject M) : secondaryAuxiliaryModuleObject M)

/-- The auxiliary operation at a nil path is zero. -/
@[simp] theorem auxiliaryTerm_nil (a : Q) (c : k) (m : secondaryFunctionModuleObject M) :
    auxiliaryTerm M (⟨a, a, Quiver.Path.nil⟩ : Quiver.BundledPath Q) c m = 0 := rfl

/-- At a path formed by appending a quiver homomorphism, the auxiliary operation equals the displayed iterated pure tensor. -/
@[simp] theorem auxiliaryTerm_cons {a b d : Q} (p : Quiver.Path a b) (e : b ⟶ d) (c : k)
    (m : secondaryFunctionModuleObject M) :
    auxiliaryTerm M (⟨a, d, Quiver.Path.cons p e⟩ : Quiver.BundledPath Q) c m
      = ((c • ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, d, e⟩ : Edge Q) (1 : k) : FieldQuiverAuxiliary k Q) ⊗ₜ[Q → k] m
          : functionModuleObject M) : secondaryAuxiliaryModuleObject M) := rfl

/-- The auxiliary indexed operation is additive in its field-scalar argument. -/
theorem auxiliaryTerm_add_scalar (x : Quiver.BundledPath Q) (c c' : k) (m : secondaryFunctionModuleObject M) :
    auxiliaryTerm M x (c + c') m = auxiliaryTerm M x c m + auxiliaryTerm M x c' m := by
  obtain ⟨a, d, q⟩ := x
  cases q with
  | nil => simp
  | cons p e => rw [auxiliaryTerm_cons, auxiliaryTerm_cons, auxiliaryTerm_cons, add_smul,
      TensorProduct.add_tmul]

/-- The auxiliary indexed operation is additive in its source argument. -/
theorem auxiliaryTerm_add (x : Quiver.BundledPath Q) (c : k) (m m' : secondaryFunctionModuleObject M) :
    auxiliaryTerm M x c (m + m') = auxiliaryTerm M x c m + auxiliaryTerm M x c m' := by
  obtain ⟨a, d, q⟩ := x
  cases q with
  | nil => simp
  | cons p e => rw [auxiliaryTerm_cons, auxiliaryTerm_cons, auxiliaryTerm_cons, TensorProduct.tmul_add,
      TensorProduct.tmul_add]

/-- The auxiliary indexed operation packaged as an additive homomorphism in its scalar and source arguments. -/
noncomputable def auxiliaryTermAddHom (x : Quiver.BundledPath Q) :
    k →+ (secondaryFunctionModuleObject M →+ secondaryAuxiliaryModuleObject M) :=
  AddMonoidHom.mk'
    (fun c => AddMonoidHom.mk' (fun m => auxiliaryTerm M x c m) (auxiliaryTerm_add M x c))
    (fun c c' => by ext m; exact auxiliaryTerm_add_scalar M x c c' m)

/-- An auxiliary additive homomorphism from the displayed algebra to additive maps between the displayed module carriers. -/
noncomputable def auxiliaryAction : PathAlgebra k Q →+ (secondaryFunctionModuleObject M →+ secondaryAuxiliaryModuleObject M) :=
  Finsupp.liftAddHom (auxiliaryTermAddHom M)

/-- Applying the auxiliary homomorphism to a finitely supported singleton agrees with the auxiliary indexed operation. -/
@[simp] theorem auxiliaryAction_single_apply (x : Quiver.BundledPath Q) (c : k) (m : secondaryFunctionModuleObject M) :
    auxiliaryAction M (Finsupp.single x c) m = auxiliaryTerm M x c m := by
  have h : auxiliaryAction M (Finsupp.single x c) = auxiliaryTermAddHom M x c := by
    rw [auxiliaryAction]; exact Finsupp.liftAddHom_apply_single (auxiliaryTermAddHom M) x c
  rw [h]; rfl

/-- Scaling the scalar argument by the value of a vertex function at the displayed endpoint agrees with acting by that function on the source argument. -/
theorem auxiliaryTerm_smul (s : Q → k) (x : Quiver.BundledPath Q) (c : k) (m : secondaryFunctionModuleObject M) :
    auxiliaryTerm M x (s x.2.1 * c) m = auxiliaryTerm M x c (s • m) := by
  obtain ⟨a, d, q⟩ := x
  cases q with
  | nil => simp
  | cons p e =>

      have hR : ((Finsupp.single (⟨_, d, e⟩ : Edge Q) (1 : k) : FieldQuiverAuxiliary k Q)
            ⊗ₜ[Q → k] (s • m : secondaryFunctionModuleObject M) : functionModuleObject M)
          = ((Finsupp.single (⟨_, d, e⟩ : Edge Q) (s d) : FieldQuiverAuxiliary k Q) ⊗ₜ[Q → k] m
            : functionModuleObject M) := by
        rw [← TensorProduct.smul_tmul]
        congr 1
        change weightedScale k Q Edge.target s _ = _
        rw [auxiliaryAction_single]; simp
      rw [auxiliaryTerm_cons, auxiliaryTerm_cons, hR]

      rw [show ((s d * c) • ofPath (⟨a, _, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q)
            = (Function.const Q (s d) : Q → k) • (c • ofPath (⟨a, _, p⟩ : Quiver.BundledPath Q))
            from by rw [SemigroupAction.mul_smul, ← smul_eq_const_smul]]

      rw [TensorProduct.smul_tmul]
      congr 1
      change (Function.const Q (s d) : Q → k) • (_ : functionModuleObject M) = _
      rw [moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul, functionAction_apply]
      congr 1
      change weightedScale k Q Edge.source _ _ = _
      rw [auxiliaryAction_single]; simp

/-- The auxiliary homomorphism intertwines the function-valued scalar actions on its scalar and source arguments. -/
theorem auxiliaryAction_smul (s : Q → k) (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M) :
    auxiliaryAction M (s • a) m = auxiliaryAction M a (s • m) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [smul_add, map_add, AddMonoidHom.add_apply, hf, hg, map_add, AddMonoidHom.add_apply]
  | single x c =>
      rw [smul_eq_mul_image, single_mul_vertexFunction, Finsupp.smul_single, smul_eq_mul,
        auxiliaryAction_single_apply, auxiliaryAction_single_apply, auxiliaryTerm_smul]

/-- An auxiliary additive homomorphism between the two displayed module carriers. -/
noncomputable def auxiliaryAddHom : (auxiliaryModuleObject M : Type (u + 1)) →+ secondaryAuxiliaryModuleObject M :=
  TensorProduct.liftAddHom (auxiliaryAction M) (auxiliaryAction_smul M)

/-- On a pure tensor, the auxiliary additive homomorphism agrees with the auxiliary action. -/
@[simp] theorem auxiliaryAddHom_tmul (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M) :
    auxiliaryAddHom M (a ⊗ₜ[Q → k] m) = auxiliaryAction M a m := rfl

/-- Applying the auxiliary homomorphism to the displayed product agrees with the corresponding iterated pure tensor. -/
theorem auxiliaryAction_mul_apply (a : PathAlgebra k Q) (v : FieldQuiverAuxiliary k Q) (m : secondaryFunctionModuleObject M) :
    auxiliaryAction M (a * edgeLinearMap v) m
      = (a ⊗ₜ[Q → k] ((v ⊗ₜ[Q → k] m : functionModuleObject M)) : secondaryAuxiliaryModuleObject M) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [add_mul, map_add, AddMonoidHom.add_apply, hf, hg, TensorProduct.add_tmul]
  | single x c =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw =>
          rw [map_add, mul_add, map_add, AddMonoidHom.add_apply, hv, hw,
            TensorProduct.add_tmul, TensorProduct.tmul_add]
      | single y d =>
          rw [edgeLinearMap_single]
          rw [show (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x from by
                rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]]
          rw [show (c • ofPath x : PathAlgebra k Q) * (d • ofEdge y)
                = (c * d) • (ofPath x * ofEdge y) from by rw [smul_mul_smul_comm]]
          obtain ⟨a₀, b₀, p⟩ := x
          obtain ⟨c₀, d₀, e⟩ := y
          by_cases hbc : b₀ = c₀
          · subst hbc

            rw [path_mul_arrow_eq_comp, Quiver.Path.comp_toPath_eq_cons,
              show ((c * d) • ofPath (⟨a₀, d₀, Quiver.Path.cons p e⟩ : Quiver.BundledPath Q)
                    : PathAlgebra k Q)
                  = Finsupp.single (⟨a₀, d₀, Quiver.Path.cons p e⟩ : Quiver.BundledPath Q) (c * d)
                  from by rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one],
              auxiliaryAction_single_apply, auxiliaryTerm_cons]

            rw [show ((c * d) • ofPath (⟨a₀, b₀, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q)
                  = (Function.const Q d : Q → k) • (c • ofPath (⟨a₀, b₀, p⟩ : Quiver.BundledPath Q))
                  from by rw [mul_comm, SemigroupAction.mul_smul, ← smul_eq_const_smul]]
            rw [TensorProduct.smul_tmul]
            congr 1
            change (Function.const Q d : Q → k) • (_ : functionModuleObject M) = _
            rw [moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul, functionAction_apply]
            congr 1
            change weightedScale k Q Edge.source _ _ = _
            rw [auxiliaryAction_single]; simp
          ·
            have hz : weightedScale k Q Edge.source (Pi.single b₀ 1)
                (Finsupp.single (⟨c₀, d₀, e⟩ : Edge Q) d) = 0 := by
              rw [auxiliaryAction_single]
              simp only [Edge.source_mk, Pi.single_eq_of_ne (Ne.symm hbc), zero_mul,
                Finsupp.single_zero]
            rw [ofEdge, Edge.toPath, pathElement_mul_pathElement, mulPath_of_not_composable _ _ hbc,
              smul_zero, map_zero, AddMonoidHom.zero_apply]
            symm
            rw [show (c • ofPath (⟨a₀, b₀, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q)
                  = (Pi.single b₀ 1 : Q → k) • (c • ofPath (⟨a₀, b₀, p⟩ : Quiver.BundledPath Q))
                  from by rw [smul_eq_mul_image, smul_mul_assoc, indexedElement_mul_vertexFunction]; simp]
            rw [TensorProduct.smul_tmul, moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul, functionAction_apply, hz,
              TensorProduct.zero_tmul, TensorProduct.tmul_zero]

/-- The auxiliary additive homomorphism sends the image under the displayed morphism back to the original element. -/
theorem auxiliaryAddHom_apply_image (x : secondaryAuxiliaryModuleObject M) :
    auxiliaryAddHom M ((multiplicationHom M).hom x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m => rw [multiplicationHom_tmul, auxiliaryAddHom_tmul, auxiliaryAction_mul_apply]
      | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
  | add x z hx hz => rw [map_add, map_add, hx, hz]

/-- The displayed module homomorphism from the target carrier to the source carrier is injective. -/
theorem moduleHom_injective : Function.Injective (multiplicationHom M).hom :=
  Function.LeftInverse.injective (auxiliaryAddHom_apply_image M)

/-- The displayed module morphism is injective on underlying elements. -/
theorem auxiliary_morphism_injective : Function.Injective (auxiliaryDifferential M).hom := by
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  set g : secondaryAuxiliaryModuleObject M → secondaryAuxiliaryModuleObject M :=
    fun y => auxiliaryAddHom M ((actionHom M).hom y) with hg
  have hF : tensorToFinsupp (functionModuleObject M) ξ = 0 := by
    refine _root_.RepresentationTheory.PolynomialModule.Finsupp.finsupp_eq_zero_of_apply_eq_map_succ g (by rw [hg]; simp) _ (fun n => ?_)
    have key := difference_succ_apply M ξ n
    rw [hξ] at key
    simp only [map_zero, Finsupp.zero_apply] at key
    have hΦΨ : (multiplicationHom M).hom (tensorToFinsupp (functionModuleObject M) ξ n)
        = (actionHom M).hom (tensorToFinsupp (functionModuleObject M) ξ (n + 1)) := by
      rw [← sub_eq_zero]; exact key.symm
    rw [hg]
    calc tensorToFinsupp (functionModuleObject M) ξ n
        = auxiliaryAddHom M ((multiplicationHom M).hom (tensorToFinsupp (functionModuleObject M) ξ n)) :=
          (auxiliaryAddHom_apply_image M _).symm
      _ = auxiliaryAddHom M ((actionHom M).hom (tensorToFinsupp (functionModuleObject M) ξ (n + 1))) := by rw [hΦΨ]
  have := tensorToFinsupp_injective (functionModuleObject M)
  apply this
  rw [hF, map_zero]

/-- The displayed module morphism is a monomorphism. -/
theorem auxiliary_morphism_mono : Mono (auxiliaryDifferential M) := by
  rw [ModuleCat.mono_iff_injective]
  exact auxiliary_morphism_injective M

/-- The pure tensor with the value of the displayed map at zero equals the pure tensor of one with that value acting on the second factor. -/
theorem auxiliary_tmul_eq_tmul_smul (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M) :
    ((degreeProjection k Q 0 a) ⊗ₜ[Q → k] (m : M) : componentType M)
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k]
          ((degreeProjection k Q 0 a) • (m : M) : secondaryFunctionModuleObject M) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, TensorProduct.add_tmul, hf, hg, add_smul, TensorProduct.tmul_add]
  | single x c =>
      obtain ⟨a, b, p⟩ := x
      rw [degreeProjection_single, pathDegree_eq_length]
      cases p with
      | nil =>
          rw [if_pos Quiver.Path.length_nil]
          have hv : (Finsupp.single (⟨a, a, Quiver.Path.nil⟩ : Quiver.BundledPath Q) c
                : PathAlgebra k Q)
              = functionRingHom k Q (Pi.single a c) := by
            rw [functionRingHom_apply, Finset.sum_eq_single a]
            · rw [Pi.single_eq_same]
            · intro j _ hj; rw [Pi.single_eq_of_ne hj, Finsupp.single_zero]
            · intro h; exact absurd (Finset.mem_univ a) h
          rw [hv, ← one_tmul_smul_eq_tmul]
      | cons q e =>
          rw [if_neg (by rw [Quiver.Path.length_cons]; exact Nat.succ_ne_zero _)]
          rw [TensorProduct.zero_tmul, zero_smul, TensorProduct.tmul_zero]

/-- The degree-zero value of the displayed auxiliary map is a pure tensor of one with the image under the displayed morphism. -/
theorem auxiliary_zero_eq_tmul (ξ : auxiliaryModuleObject M) :
    componentData M ξ 0
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k]
          (show secondaryFunctionModuleObject M from (auxiliaryModuleToObject M).hom (componentData M ξ 0)) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [componentData_tmul_apply, auxiliaryModuleToObject_tmul]
      exact auxiliary_tmul_eq_tmul_smul M a m
  | add x y hx hy =>
      have hsum : componentData M (x + y) 0
          = componentData M x 0 + componentData M y 0 := by
        rw [map_add, Finsupp.add_apply]
      rw [hsum, map_add, TensorProduct.tmul_add, ← hx, ← hy]

/-- Applying the displayed auxiliary map to its degree-zero value produces the singleton supported at zero. -/
theorem auxiliary_apply_zero_eq_single (ξ : auxiliaryModuleObject M) :
    componentData M (componentData M ξ 0) = Finsupp.single 0 (componentData M ξ 0) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      ext n
      rw [componentData_tmul_apply, componentData_tmul_apply, degreeProjection_comp, Finsupp.single_apply]
      by_cases h : n = 0
      · subst h; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg (fun he : (0 : ℕ) = n => h he.symm), TensorProduct.zero_tmul]
  | add x y hx hy =>
      have hsum : componentData M (x + y) 0
          = componentData M x 0 + componentData M y 0 := by
        rw [map_add, Finsupp.add_apply]
      rw [hsum, map_add, Finsupp.single_add, hx, hy]

/-- An element is zero when every positive-degree component and its image under the displayed morphism are zero. -/
theorem eq_zero_of_auxiliary_succ_eq_zero (ξ : auxiliaryModuleObject M)
    (h : ∀ n, componentData M ξ (n + 1) = 0) (hε : (auxiliaryModuleToObject M).hom ξ = 0) :
    ξ = 0 := by
  have hξ : ξ = componentData M ξ 0 := by
    apply componentData_injective
    rw [auxiliary_apply_zero_eq_single]
    ext n
    cases n with
    | zero => rw [Finsupp.single_apply, if_pos rfl]
    | succ m => rw [h m, Finsupp.single_apply, if_neg (by omega : ¬ (0 = m + 1))]
  have key := auxiliary_zero_eq_tmul M ξ
  rw [← hξ, hε, TensorProduct.tmul_zero] at key
  exact key

/-- An element whose components vanish above a bound and whose image under the displayed morphism is zero has a preimage under the preceding morphism. -/
theorem auxiliary_exists_preimage :
    ∀ (N : ℕ) (ξ : auxiliaryModuleObject M),
      (∀ n, N < n → componentData M ξ n = 0) → (auxiliaryModuleToObject M).hom ξ = 0 →
        ∃ ζ : secondaryAuxiliaryModuleObject M, (auxiliaryDifferential M).hom ζ = ξ := by
  intro N
  induction N with
  | zero =>
      intro ξ h hε
      refine ⟨0, ?_⟩
      rw [map_zero]
      symm
      refine eq_zero_of_auxiliary_succ_eq_zero M ξ (fun n => h (n + 1) (Nat.succ_pos n)) hε
  | succ N ih =>
      intro ξ h hε
      obtain ⟨η, hηN, hηj, hηΦ⟩ := exists_supported_preimage_succ M ξ N
      have hdε : (auxiliaryModuleToObject M).hom ((auxiliaryDifferential M).hom η) = 0 := by
        have e := congrArg (fun f : secondaryAuxiliaryModuleObject M ⟶ M => f.hom η) (auxiliaryDifferential_comp_toObject M)
        simpa using e
      set ξ' : auxiliaryModuleObject M := ξ - (auxiliaryDifferential M).hom η with hξ'
      have hε' : (auxiliaryModuleToObject M).hom ξ' = 0 := by
        rw [hξ', map_sub, hε, hdε, sub_zero]
      have hcoord : ∀ n, N < n → componentData M ξ' n = 0 := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hξ', map_sub, Finsupp.sub_apply, difference_succ_apply M η m]
        by_cases hmN : m = N
        · subst hmN
          rw [hηN, hηj (m + 1) (by omega), map_zero, sub_zero, hηΦ, sub_self]
        · rw [hηj m hmN, hηj (m + 1) (by omega), map_zero, map_zero, sub_zero,
            h (m + 1) (by omega), zero_sub, neg_zero]
      obtain ⟨ζ', hζ'⟩ := ih ξ' hcoord hε'
      exact ⟨ζ' + η, by rw [map_add, hζ', hξ']; abel⟩

/-- The displayed short complex is exact. -/
theorem auxiliaryShortComplex_exact : (auxiliaryShortComplex M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro ξ hξ
  set F := componentData M ξ with hF
  by_cases hne : F.support.Nonempty
  · have hhigh : ∀ n, F.support.max' hne < n → componentData M ξ n = 0 := by
      intro n hn
      have hnm : n ∉ F.support := fun hmem => by
        have := Finset.le_max' _ _ hmem; omega
      simpa [hF] using Finsupp.notMem_support_iff.mp hnm
    exact auxiliary_exists_preimage M (F.support.max' hne) ξ hhigh hξ
  · have hF0 : F = 0 := by
      rw [← Finsupp.support_eq_empty, Finset.not_nonempty_iff_eq_empty.mp hne]
    have hhigh : ∀ n, 0 < n → componentData M ξ n = 0 := by
      intro n _; rw [← hF, hF0, Finsupp.zero_apply]
    exact auxiliary_exists_preimage M 0 ξ hhigh hξ

/-- The displayed short complex is short exact. -/
theorem auxiliaryShortComplex_shortExact : (auxiliaryShortComplex M).ShortExact where
  exact := auxiliaryShortComplex_exact M
  mono_f := auxiliary_morphism_mono M
  epi_g := auxiliaryModuleToObject_epi M

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
