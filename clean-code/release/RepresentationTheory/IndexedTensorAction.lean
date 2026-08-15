/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorCoordinateMaps

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-- A single-support function is the scalar multiple of its canonical indexed element. -/
theorem single_eq_smul_index (q : Quiver.BundledPath Q) (c : k) :
    (Finsupp.single q c : PathAlgebra k Q) = c • ofPath q := by
  rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Moves a scalar from the first factor of an iterated pure tensor into the coefficient of a single-support function. -/
theorem smul_tmul_single_eq_tmul_single_mul {a d c : Q} (p : Quiver.Path a d) (e : d ⟶ c) (ca cv : k)
    (m : secondaryFunctionModuleObject M) :
    ((ca • ofPath (⟨a, d, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨d, c, e⟩ : Edge Q) cv : FieldQuiverAuxiliary k Q)
          ⊗ₜ[Q → k] m : functionModuleObject M) : secondaryAuxiliaryModuleObject M)
      = ((ofPath (⟨a, d, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
          ((Finsupp.single (⟨d, c, e⟩ : Edge Q) (ca * cv) : FieldQuiverAuxiliary k Q)
            ⊗ₜ[Q → k] m : functionModuleObject M) : secondaryAuxiliaryModuleObject M) := by
  have hpath : (ca • ofPath (⟨a, d, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q)
      = (Pi.single d ca : Q → k) • (ofPath (⟨a, d, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) := by
    rw [smul_eq_mul_image, indexedElement_mul_vertexFunction]
    simp only [Pi.single_eq_same]
  rw [hpath, TensorProduct.smul_tmul]
  congr 1
  rw [moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul, functionAction_apply, auxiliaryAction_single]
  simp only [Edge.source, Pi.single_eq_same]

/-- An iterated pure tensor with incompatible intermediate vertices is zero. -/
theorem smul_tmul_single_eq_zero_of_ne {a d b c : Q} (p : Quiver.Path a d) (e : b ⟶ c) (ca cv : k)
    (hbd : b ≠ d) (m : secondaryFunctionModuleObject M) :
    ((ca • ofPath (⟨a, d, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, c, e⟩ : Edge Q) cv : FieldQuiverAuxiliary k Q)
          ⊗ₜ[Q → k] m : functionModuleObject M) : secondaryAuxiliaryModuleObject M) = 0 := by
  have hpath : (ca • ofPath (⟨a, d, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q)
      = (Pi.single d (1 : k) : Q → k)
          • (ca • ofPath (⟨a, d, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) := by
    rw [smul_eq_mul_image, smul_mul_assoc, indexedElement_mul_vertexFunction]
    simp only [Pi.single_eq_same, one_smul]
  rw [hpath, TensorProduct.smul_tmul, moduleAuxiliary_smul_eq_tensorMap, tensorMap_functionAction_tmul, functionAction_apply, auxiliaryAction_single]
  simp only [Edge.source, Pi.single_eq_of_ne hbd, zero_mul, Finsupp.single_zero,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero]

/-- Combines an index, a scalar, and an auxiliary carrier element in the target carrier. -/
noncomputable def indexedTerm (q : Quiver.BundledPath Q) (c : k) (m : secondaryFunctionModuleObject M) :
    secondaryAuxiliaryModuleObject M :=
  match q with
  | ⟨_, _, Quiver.Path.nil⟩ => 0
  | ⟨a, c', Quiver.Path.cons (b := b) p e⟩ =>
      (ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        (((Finsupp.single (⟨b, c', e⟩ : Edge Q) c : FieldQuiverAuxiliary k Q)
          ⊗ₜ[Q → k] m : functionModuleObject M))

/-- The indexed term associated with an empty path vanishes. -/
@[simp] theorem indexedTerm_nil (a : Q) (c : k) (m : secondaryFunctionModuleObject M) :
    indexedTerm M (⟨a, a, Quiver.Path.nil⟩ : Quiver.BundledPath Q) c m = 0 := rfl

/-- Expands an indexed term for a path extended by one arrow as an iterated pure tensor. -/
@[simp] theorem indexedTerm_cons {a b c' : Q} (p : Quiver.Path a b) (e : b ⟶ c') (c : k)
    (m : secondaryFunctionModuleObject M) :
    indexedTerm M (⟨a, c', Quiver.Path.cons p e⟩ : Quiver.BundledPath Q) c m
      = ((ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
          ((Finsupp.single (⟨b, c', e⟩ : Edge Q) c : FieldQuiverAuxiliary k Q)
            ⊗ₜ[Q → k] m : functionModuleObject M) : secondaryAuxiliaryModuleObject M) := rfl

/-- An indexed term with zero scalar is zero. -/
theorem indexedTerm_zero_scalar (q : Quiver.BundledPath Q) (m : secondaryFunctionModuleObject M) :
    indexedTerm M q (0 : k) m = 0 := by
  obtain ⟨a, c', p⟩ := q
  cases p with
  | nil => rfl
  | cons p e => rw [indexedTerm_cons]; simp only [Finsupp.single_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]

/-- An indexed term is additive in its scalar argument. -/
theorem indexedTerm_add_scalar (q : Quiver.BundledPath Q) (c c' : k) (m : secondaryFunctionModuleObject M) :
    indexedTerm M q (c + c') m = indexedTerm M q c m + indexedTerm M q c' m := by
  obtain ⟨a, cc, p⟩ := q
  cases p with
  | nil => simp only [indexedTerm_nil, add_zero]
  | cons p e =>
      simp only [indexedTerm_cons, Finsupp.single_add, TensorProduct.add_tmul,
        TensorProduct.tmul_add]

/-- An indexed term applied to zero in the auxiliary carrier is zero. -/
theorem indexedTerm_zero_input (q : Quiver.BundledPath Q) (c : k) :
    indexedTerm M q c (0 : secondaryFunctionModuleObject M) = 0 := by
  obtain ⟨a, cc, p⟩ := q
  cases p with
  | nil => rfl
  | cons p e => rw [indexedTerm_cons]; simp only [TensorProduct.tmul_zero]

/-- An indexed term is additive in its auxiliary carrier argument. -/
theorem indexedTerm_add_input (q : Quiver.BundledPath Q) (c : k) (m m' : secondaryFunctionModuleObject M) :
    indexedTerm M q c (m + m') = indexedTerm M q c m + indexedTerm M q c m' := by
  obtain ⟨a, cc, p⟩ := q
  cases p with
  | nil => simp only [indexedTerm_nil, add_zero]
  | cons p e => simp only [indexedTerm_cons, TensorProduct.tmul_add]

/-- The scalar dependence of an indexed term, packaged as an additive homomorphism. -/
noncomputable def indexedTermHom (q : Quiver.BundledPath Q) (m : secondaryFunctionModuleObject M) :
    k →+ secondaryAuxiliaryModuleObject M where
  toFun c := indexedTerm M q c m
  map_zero' := indexedTerm_zero_scalar M q m
  map_add' c c' := indexedTerm_add_scalar M q c c' m

/-- The action with a fixed auxiliary carrier element, packaged as an additive homomorphism. -/
noncomputable def flipActionAddHom (m : secondaryFunctionModuleObject M) :
    PathAlgebra k Q →+ secondaryAuxiliaryModuleObject M :=
  Finsupp.liftAddHom (fun q => indexedTermHom M q m)

/-- The flipped action on a single-support element is the corresponding indexed term. -/
@[simp] theorem flipActionAddHom_single (m : secondaryFunctionModuleObject M) (q : Quiver.BundledPath Q) (c : k) :
    flipActionAddHom M m (Finsupp.single q c) = indexedTerm M q c m := by
  change Finsupp.liftAddHom (fun q => indexedTermHom M q m) (Finsupp.single q c) = _
  rw [Finsupp.liftAddHom_apply_single]
  rfl

/-- The flipped action associated with the zero auxiliary carrier element vanishes. -/
theorem flipActionAddHom_zero (a : PathAlgebra k Q) :
    flipActionAddHom M (0 : secondaryFunctionModuleObject M) a = 0 := by
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add f g hf hg => rw [map_add, hf, hg, add_zero]
  | single q c => rw [flipActionAddHom_single, indexedTerm_zero_input]

/-- The flipped action homomorphism is additive in its fixed auxiliary carrier argument. -/
theorem flipActionAddHom_add (a : PathAlgebra k Q) (m m' : secondaryFunctionModuleObject M) :
    flipActionAddHom M (m + m') a = flipActionAddHom M m a + flipActionAddHom M m' a := by
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]; abel
  | single q c =>
      rw [flipActionAddHom_single, flipActionAddHom_single, flipActionAddHom_single, indexedTerm_add_input]

/-- The additive map assigning to each owner element its additive action on the auxiliary carrier. -/
noncomputable def actionAddHom :
    PathAlgebra k Q →+ secondaryFunctionModuleObject M →+
      secondaryAuxiliaryModuleObject M where
  toFun a :=
    { toFun := fun m => flipActionAddHom M m a
      map_zero' := flipActionAddHom_zero M a
      map_add' := fun m m' => flipActionAddHom_add M a m m' }
  map_zero' := by ext m; exact (flipActionAddHom M m).map_zero
  map_add' a a' := by ext m; exact (flipActionAddHom M m).map_add a a'

/-- Evaluating the action map agrees with evaluating its argument-flipped form. -/
@[simp] theorem actionAddHom_apply_eq_flip (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M) :
    actionAddHom M a m = flipActionAddHom M m a := rfl

/-- Scalar multiplication in the acting argument may be transferred to the auxiliary carrier argument. -/
theorem actionAddHom_smul (s : Q → k) (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M) :
    actionAddHom M ((s : Q → k) • a) m = actionAddHom M a ((s : Q → k) • m) := by
  simp only [actionAddHom_apply_eq_flip]
  induction a using Finsupp.induction_linear with
  | zero => rw [smul_eq_mul_image, zero_mul, map_zero, map_zero]
  | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg]
  | single q c =>
      obtain ⟨a, c', p⟩ := q
      rw [smul_eq_mul_image, single_mul_vertexFunction, Finsupp.smul_single, smul_eq_mul,
        flipActionAddHom_single, flipActionAddHom_single]

      cases p with
      | nil => rw [indexedTerm_nil, indexedTerm_nil]
      | cons p e =>
          rw [indexedTerm_cons, indexedTerm_cons]

          congr 1
          rw [← TensorProduct.smul_tmul]
          congr 1
          change (Finsupp.single (⟨_, c', e⟩ : Edge Q) (s c' * c) : FieldQuiverAuxiliary k Q)
            = weightedScale k Q Edge.target s (Finsupp.single (⟨_, c', e⟩ : Edge Q) c)
          rw [auxiliaryAction_single]
          simp only [Edge.target]

/-- An additive retraction from the source carrier to the target carrier. -/
noncomputable def retractionAddHom :
    auxiliaryModuleObject M →+
      secondaryAuxiliaryModuleObject M :=
  TensorProduct.liftAddHom (actionAddHom M) (actionAddHom_smul M)

/-- The retraction of a pure tensor agrees with the flipped action evaluation. -/
@[simp] theorem retractionAddHom_tmul (a : PathAlgebra k Q) (m : secondaryFunctionModuleObject M) :
    retractionAddHom M (a ⊗ₜ[Q → k] m) = flipActionAddHom M m a := by
  change TensorProduct.liftAddHom (actionAddHom M) (actionAddHom_smul M) (a ⊗ₜ[Q → k] m) = _
  rw [TensorProduct.liftAddHom_tmul, actionAddHom_apply_eq_flip]

/-- The additive retraction is a left inverse to the displayed module homomorphism. -/
theorem retractionAddHom_leftInverse : Function.LeftInverse (retractionAddHom M) (multiplicationHom M).hom := by
  intro η
  induction η using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul v m =>
          induction a using Finsupp.induction_linear with
          | zero => simp only [TensorProduct.zero_tmul, map_zero]
          | add f g hf hg => rw [TensorProduct.add_tmul, map_add, map_add, hf, hg]
          | single q ca =>
              induction v using Finsupp.induction_linear with
              | zero => simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, map_zero]
              | add v w hv hw =>
                  rw [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, map_add, hv, hw]
              | single arr cv =>
                  obtain ⟨a₀, d, path⟩ := q
                  obtain ⟨b', c', e⟩ := arr
                  rw [multiplicationHom_tmul]
                  simp only [single_eq_smul_index]
                  rw [edgeLinearMap_single, ofEdge, Edge.toPath, smul_mul_assoc,
                    mul_smul_comm, smul_smul, pathElement_mul_pathElement]
                  by_cases hdb : d = b'
                  · subst hdb
                    rw [mulPath_of_composable, Finsupp.smul_single, smul_eq_mul, mul_one, retractionAddHom_tmul,
                      flipActionAddHom_single,
                      show (⟨a₀, c', path.comp e.toPath⟩ : Quiver.BundledPath Q)
                        = ⟨a₀, c', Quiver.Path.cons path e⟩ from by
                          rw [Quiver.Path.comp_toPath_eq_cons], indexedTerm_cons,
                      smul_tmul_single_eq_tmul_single_mul]
                  · rw [mulPath_of_not_composable _ _ hdb, smul_zero, TensorProduct.zero_tmul, map_zero]
                    exact (smul_tmul_single_eq_zero_of_ne M path e ca cv (fun h => hdb h.symm) m).symm
      | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
  | add η ζ hη hζ => rw [map_add, map_add, hη, hζ]

/-- The displayed module homomorphism from the target carrier to the source carrier is injective. -/
theorem moduleHom_injective : Function.Injective (multiplicationHom M).hom :=
  (retractionAddHom_leftInverse M).injective

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
