/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib

/-! # Module base change -/

open scoped TensorProduct

namespace RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange

variable {K A V W S T : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]

section OneAlgebra

variable [CommRing S] [Algebra K S]

/-- The algebra homomorphism from the original algebra to scalar-linear endomorphisms of the
scalar-extended module. -/
noncomputable def baseAlgebraAction : A →ₐ[K] Module.End S (S ⊗[K] V) :=
  (Module.End.baseChangeHom K S V).comp (Algebra.lsmul K K V)

/-- The algebra homomorphism from the scalar-extended algebra to scalar-linear endomorphisms of
the scalar-extended module. -/
noncomputable def scalarExtensionAction : (S ⊗[K] A) →ₐ[S] Module.End S (S ⊗[K] V) :=
  AlgHom.liftEquiv K S A (Module.End S (S ⊗[K] V))
    (baseAlgebraAction (A := A) (V := V) (S := S))

/-- The module structure on the scalar extension of a module over the scalar-extended algebra. -/
noncomputable instance instModuleTensorProduct : Module (S ⊗[K] A) (S ⊗[K] V) :=
  Module.compHom (S ⊗[K] V) (R := Module.End S (S ⊗[K] V))
    (scalarExtensionAction (A := A) (V := V) (S := S)).toRingHom

/-- Scalar multiplication by the extended algebra agrees with evaluation of its action
homomorphism on the extended module. -/
theorem smul_eq_scalarExtensionAction (y : S ⊗[K] A) (x : S ⊗[K] V) :
    (y • x : S ⊗[K] V) = scalarExtensionAction (A := A) (V := V) (S := S) y x :=
  rfl

/-- The scalar-extension action of a tensor with scalar component one on a pure module tensor
applies the original algebra action to its module component. -/
theorem scalarExtensionAction_tmul_one_tmul (a : A) (s : S) (v : V) :
    scalarExtensionAction (A := A) (V := V) (S := S) (1 ⊗ₜ[K] a) (s ⊗ₜ[K] v) =
      s ⊗ₜ[K] (a • v) := by
  rw [scalarExtensionAction, AlgHom.liftEquiv_tmul, one_smul]
  simp [baseAlgebraAction, Module.End.baseChangeHom, LinearMap.baseChange_tmul, Algebra.lsmul_apply]

/-- An extended-algebra tensor with scalar component one acts on a pure module tensor through the
original module action. -/
theorem tmul_one_smul_tmul (a : A) (s : S) (v : V) :
    ((1 ⊗ₜ[K] a : S ⊗[K] A) • (s ⊗ₜ[K] v) : S ⊗[K] V) = s ⊗ₜ[K] (a • v) := by
  rw [smul_eq_scalarExtensionAction, scalarExtensionAction_tmul_one_tmul]

/-- An extended-algebra tensor formed from a scalar and the algebra unit acts by scalar
multiplication on the extended module. -/
theorem tmul_one_smul_eq_smul (s : S) (x : S ⊗[K] V) :
    ((s ⊗ₜ[K] (1 : A) : S ⊗[K] A) • x : S ⊗[K] V) = s • x := by
  rw [smul_eq_scalarExtensionAction, scalarExtensionAction, AlgHom.liftEquiv_tmul, map_one]
  rfl

end OneAlgebra

section Pushforward

variable [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]

/-- Transport a linear equivalence between scalar-extended modules along a homomorphism of
commutative scalar algebras. -/
noncomputable def baseChangeLinearEquiv (f : S →ₐ[K] T)
    (φ : (S ⊗[K] V) ≃ₗ[S ⊗[K] A] (S ⊗[K] W)) :
    (T ⊗[K] V) ≃ₗ[T ⊗[K] A] (T ⊗[K] W) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm

  let φS : (S ⊗[K] V) ≃ₗ[S] (S ⊗[K] W) :=
    { toFun := φ
      invFun := φ.symm
      left_inv := φ.left_inv
      right_inv := φ.right_inv
      map_add' := φ.map_add
      map_smul' := fun s x => by
        simp only [RingHom.id_apply]
        rw [← tmul_one_smul_eq_smul (A := A) s x, LinearEquiv.map_smul,
          tmul_one_smul_eq_smul] }

  let cV := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T V
  let cW := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W

  let ΦT : (T ⊗[K] V) ≃ₗ[T] (T ⊗[K] W) :=
    cV.symm ≪≫ₗ φS.baseChange S T _ _ ≪≫ₗ cW
  have ΦT_tmul : ∀ (t : T) (v : V), ΦT (t ⊗ₜ[K] v) = cW (t ⊗ₜ[S] φ (1 ⊗ₜ[K] v)) := by
    intro t v
    simp only [ΦT, LinearEquiv.trans_apply, cV,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul]
    rfl

  have key : ∀ (a : A) (t : T) (w : S ⊗[K] W),
      cW (t ⊗ₜ[S] ((1 ⊗ₜ[K] a : S ⊗[K] A) • w)) =
        (1 ⊗ₜ[K] a : T ⊗[K] A) • cW (t ⊗ₜ[S] w) := by
    intro a t w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s w0 =>
      simp only [tmul_one_smul_tmul, cW,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add x y hx hy =>
      simp only [smul_add, TensorProduct.tmul_add, map_add, hx, hy]

  have hcomm : ∀ (a : A) (x : T ⊗[K] V),
      ΦT ((1 ⊗ₜ[K] a : T ⊗[K] A) • x) = (1 ⊗ₜ[K] a : T ⊗[K] A) • ΦT x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t v =>
      rw [tmul_one_smul_tmul, ΦT_tmul, ΦT_tmul,
        show φ (1 ⊗ₜ[K] (a • v)) = (1 ⊗ₜ[K] a : S ⊗[K] A) • φ (1 ⊗ₜ[K] v) by
          rw [← tmul_one_smul_tmul a (1 : S) v, LinearEquiv.map_smul],
        key]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

  exact
    { toFun := ΦT
      invFun := ΦT.symm
      left_inv := ΦT.left_inv
      right_inv := ΦT.right_inv
      map_add' := ΦT.map_add
      map_smul' := by
        intro y x
        simp only [RingHom.id_apply]
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul t a =>
          have hmul : (t ⊗ₜ[K] a : T ⊗[K] A) = (t ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] a) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [hmul, mul_smul, mul_smul, tmul_one_smul_eq_smul, tmul_one_smul_eq_smul,
            LinearEquiv.map_smul, hcomm]
        | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq] }

/-- A linear equivalence between two scalar-extended modules induces one after further base change
along an algebra homomorphism. -/
theorem nonempty_linearEquiv_of_baseChange (f : S →ₐ[K] T)
    (h : Nonempty ((S ⊗[K] V) ≃ₗ[S ⊗[K] A] (S ⊗[K] W))) :
    Nonempty ((T ⊗[K] V) ≃ₗ[T ⊗[K] A] (T ⊗[K] W)) :=
  h.elim fun φ => ⟨baseChangeLinearEquiv f φ⟩

/-- Transport a linear map between scalar-extended modules along a homomorphism of commutative
scalar algebras. -/
noncomputable def baseChangeLinearMap (f : S →ₐ[K] T)
    (g : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) :
    (T ⊗[K] V) →ₗ[T ⊗[K] A] (T ⊗[K] W) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm

  let gS : (S ⊗[K] V) →ₗ[S] (S ⊗[K] W) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun s x => by
        simp only [RingHom.id_apply]
        rw [← tmul_one_smul_eq_smul (A := A) s x, LinearMap.map_smul,
          tmul_one_smul_eq_smul] }
  let cV := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T V
  let cW := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W

  let ΦT : (T ⊗[K] V) →ₗ[T] (T ⊗[K] W) :=
    cW.toLinearMap ∘ₗ LinearMap.baseChange T gS ∘ₗ cV.symm.toLinearMap
  have ΦT_tmul : ∀ (t : T) (v : V), ΦT (t ⊗ₜ[K] v) = cW (t ⊗ₜ[S] g (1 ⊗ₜ[K] v)) := by
    intro t v
    simp only [ΦT, LinearMap.comp_apply, LinearEquiv.coe_coe, cV,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul]
    rfl

  have key : ∀ (a : A) (t : T) (w : S ⊗[K] W),
      cW (t ⊗ₜ[S] ((1 ⊗ₜ[K] a : S ⊗[K] A) • w)) =
        (1 ⊗ₜ[K] a : T ⊗[K] A) • cW (t ⊗ₜ[S] w) := by
    intro a t w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s w0 =>
      simp only [tmul_one_smul_tmul, cW,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add x y hx hy =>
      simp only [smul_add, TensorProduct.tmul_add, map_add, hx, hy]

  have hcomm : ∀ (a : A) (x : T ⊗[K] V),
      ΦT ((1 ⊗ₜ[K] a : T ⊗[K] A) • x) = (1 ⊗ₜ[K] a : T ⊗[K] A) • ΦT x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t v =>
      rw [tmul_one_smul_tmul, ΦT_tmul, ΦT_tmul,
        show g (1 ⊗ₜ[K] (a • v)) = (1 ⊗ₜ[K] a : S ⊗[K] A) • g (1 ⊗ₜ[K] v) by
          rw [← tmul_one_smul_tmul a (1 : S) v, LinearMap.map_smul],
        key]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

  exact
    { toFun := ΦT
      map_add' := ΦT.map_add
      map_smul' := by
        intro y x
        simp only [RingHom.id_apply]
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul t a =>
          have hmul : (t ⊗ₜ[K] a : T ⊗[K] A) = (t ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] a) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [hmul, mul_smul, mul_smul, tmul_one_smul_eq_smul, tmul_one_smul_eq_smul,
            LinearMap.map_smul, hcomm]
        | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq] }

/-- On a pure tensor over the target scalar algebra, the transported map is obtained by applying
the original map to the unit tensor and then cancelling the intermediate base change. -/
theorem baseChangeLinearMap_tmul (f : S →ₐ[K] T)
    (g : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) (t : T) (v : V) :
    letI : Algebra S T := f.toRingHom.toAlgebra
    baseChangeLinearMap f g (t ⊗ₜ[K] v) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W
        (t ⊗ₜ[S] g (1 ⊗ₜ[K] v)) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  simp only [baseChangeLinearMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul]

end Pushforward

section PushforwardFunctorial

variable {U : Type*} [AddCommGroup U] [Module K U] [Module A U] [IsScalarTower K A U]
variable [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]

/-- The transported linear map sends a tensor introduced through cancellation of base change to
the corresponding tensor of the original map value. -/
theorem baseChangeLinearMap_cancelBaseChange_tmul (f : S →ₐ[K] T)
    (g : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) (t : T) (x : S ⊗[K] V) :
    letI : Algebra S T := f.toRingHom.toAlgebra
    baseChangeLinearMap f g
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T V (t ⊗ₜ[S] x)) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W (t ⊗ₜ[S] g x) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun y => (f.commutes y).symm
  simp only [baseChangeLinearMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

/-- Transporting a composite linear map along base change equals the composite of the transported
maps. -/
theorem baseChangeLinearMap_comp (f : S →ₐ[K] T)
    (g : (S ⊗[K] W) →ₗ[S ⊗[K] A] (S ⊗[K] U))
    (h : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) :
    baseChangeLinearMap f (g.comp h) =
      (baseChangeLinearMap f g).comp (baseChangeLinearMap f h) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t v =>
    simp only [LinearMap.comp_apply, baseChangeLinearMap_tmul,
      baseChangeLinearMap_cancelBaseChange_tmul]
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]

/-- Transporting the identity linear map along base change yields the identity. -/
theorem baseChangeLinearMap_id (f : S →ₐ[K] T) :
    baseChangeLinearMap f (LinearMap.id : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] V)) =
      LinearMap.id := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t v =>
    simp only [baseChangeLinearMap_tmul, LinearMap.id_coe, id_eq,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/-- A splitting by linear maps after scalar extension to one algebra induces a splitting after
further base change along an algebra homomorphism. -/
theorem exists_retraction_of_baseChange (f : S →ₐ[K] T)
    (h : ∃ (i : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W))
           (p : (S ⊗[K] W) →ₗ[S ⊗[K] A] (S ⊗[K] V)), p.comp i = LinearMap.id) :
    ∃ (i : (T ⊗[K] V) →ₗ[T ⊗[K] A] (T ⊗[K] W))
      (p : (T ⊗[K] W) →ₗ[T ⊗[K] A] (T ⊗[K] V)), p.comp i = LinearMap.id := by
  obtain ⟨i, p, hpi⟩ := h
  refine ⟨baseChangeLinearMap f i, baseChangeLinearMap f p, ?_⟩
  rw [← baseChangeLinearMap_comp f p i, hpi, baseChangeLinearMap_id]

end PushforwardFunctorial

end RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange
