/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Algebra.Module.TensorProductSimplicity
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary tensor-product representations -/

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open MonoidAlgebra

namespace RepresentationTheory.AuxiliaryTensorProductRepresentations

variable {k : Type*} [CommSemiring k]

/-- An auxiliary property of a representation. -/
def IsAuxiliary {Γ M : Type*} [Monoid Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) : Prop :=
  Nontrivial M ∧ ∀ N : Submodule k M, (∀ γ : Γ, ∀ x ∈ N, ρ γ x ∈ N) → N = ⊥ ∨ N = ⊤

section ExtTprod

variable {G H V W : Type*} [Monoid G] [Monoid H]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- The representation of a product monoid on the tensor product of two representation spaces. -/
noncomputable def tensorProductRepresentation
    (ρ : Representation k G V) (σ : Representation k H W) :
    Representation k (G × H) (V ⊗[k] W) where
  toFun gh := TensorProduct.map (ρ gh.1) (σ gh.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one, TensorProduct.map_one]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, TensorProduct.map_mul]

/-- The tensor-product representation acts through the two components of a product element. -/
@[simp]
theorem tensorProductRepresentation_apply
    (ρ : Representation k G V) (σ : Representation k H W) (gh : G × H) :
    tensorProductRepresentation ρ σ gh = TensorProduct.map (ρ gh.1) (σ gh.2) :=
  rfl

end ExtTprod

/-- A representation with the auxiliary property gives a simple module. -/
theorem isSimpleModule_of_isAuxiliary
    {k Γ M : Type*} [Field k] [Monoid Γ] [AddCommGroup M] [Module k M]
    {ρ : Representation k Γ M} (h : IsAuxiliary ρ) :
    IsSimpleModule (MonoidAlgebra k Γ) ρ.asModule := by
  obtain ⟨hnt, hsub⟩ := h
  haveI : Nontrivial M := hnt
  haveI : Nontrivial ρ.asModule := hnt
  refine { toIsSimpleOrder := { eq_bot_or_eq_top := fun N => ?_ } }
  set τ := Subrepresentation.ofSubmodule' N with hτ
  rcases hsub τ.toSubmodule (fun γ x hx => τ.apply_mem_toSubmodule γ hx) with hbot | htop
  · left
    refine eq_bot_iff.mpr fun w hw => ?_
    have hmem : w ∈ τ.toSubmodule := (Subrepresentation.mem_ofSubmodule'_iff).mpr hw
    rw [hbot, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact hmem
  · right
    refine eq_top_iff.mpr fun w _ => ?_
    have hmem : w ∈ τ.toSubmodule := by rw [htop]; trivial
    exact (Subrepresentation.mem_ofSubmodule'_iff).mp hmem

section PartI

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
variable {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [IsAlgClosed k] [Fintype G] [Fintype H]
    [FiniteDimensional k V] [FiniteDimensional k W] in
private theorem map_lsmul_mem_of_extTprod_stable
    (ρ : Representation k G V) (σ : Representation k H W)
    (N : Submodule k (V ⊗[k] W))
    (hN : ∀ gh : G × H, ∀ x ∈ N, tensorProductRepresentation ρ σ gh x ∈ N)
    (a : MonoidAlgebra k G) (b : MonoidAlgebra k H) (x : V ⊗[k] W) (hx : x ∈ N) :
    TensorProduct.map
      ((Algebra.lsmul k k ρ.asModule : MonoidAlgebra k G →ₐ[k] Module.End k ρ.asModule) a)
      ((Algebra.lsmul k k σ.asModule : MonoidAlgebra k H →ₐ[k] Module.End k σ.asModule) b)
      x ∈ N := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
    simp only [map_zero, TensorProduct.map_zero_left, LinearMap.zero_apply]
    exact N.zero_mem
  | add a₁ a₂ h₁ h₂ =>
    rw [map_add, TensorProduct.map_add_left]
    exact N.add_mem h₁ h₂
  | single g c =>
    have hL : (Algebra.lsmul k k ρ.asModule (MonoidAlgebra.single g c)) = c • ρ g := by
      ext v
      change (MonoidAlgebra.single g c) • v = (c • ρ g) v
      rw [Representation.single_smul]
      rfl
    induction b using MonoidAlgebra.induction_linear with
    | zero =>
      simp only [map_zero, TensorProduct.map_zero_right, LinearMap.zero_apply]
      exact N.zero_mem
    | add b₁ b₂ hb₁ hb₂ =>
      rw [map_add, TensorProduct.map_add_right]
      exact N.add_mem hb₁ hb₂
    | single h d =>
      have hR : (Algebra.lsmul k k σ.asModule (MonoidAlgebra.single h d)) = d • σ h := by
        ext w
        change (MonoidAlgebra.single h d) • w = (d • σ h) w
        rw [Representation.single_smul]
        rfl
      rw [hL, hR, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
        LinearMap.smul_apply, LinearMap.smul_apply]
      refine N.smul_mem c (N.smul_mem d ?_)
      exact hN (g, h) x hx

omit [Fintype G] [Fintype H] in
/-- The tensor-product representation has the auxiliary property when both factors do. -/
@[source_ref "Chapter5/Theorem5.6.1" (role := primary)]
theorem isAuxiliary_tensorProductRepresentation
    {ρ : Representation k G V} {σ : Representation k H W}
    (hρ : IsAuxiliary ρ) (hσ : IsAuxiliary σ) :
    IsAuxiliary (tensorProductRepresentation ρ σ) := by
  haveI hsG : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    isSimpleModule_of_isAuxiliary hρ
  haveI hsH : IsSimpleModule (MonoidAlgebra k H) σ.asModule :=
    isSimpleModule_of_isAuxiliary hσ
  haveI : Nontrivial V := hρ.1
  haveI : Nontrivial W := hσ.1
  refine ⟨?_, ?_⟩
  · have hpos : 0 < Module.finrank k (V ⊗[k] W) := by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
    exact Module.nontrivial_of_finrank_pos hpos
  · intro N hN
    exact RepresentationTheory.Algebra.Module.TensorProductSimplicity.submodule_eq_bot_or_top_of_tensorActions
      k (MonoidAlgebra k G) (MonoidAlgebra k H) ρ.asModule σ.asModule N
      (map_lsmul_mem_of_extTprod_stable ρ σ N hN)

end PartI

section OfModule

variable {k G V : Type*} [CommSemiring k] [Monoid G]
  [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]

/-- The representation induced by a module over a monoid algebra. -/
noncomputable def representationOfMonoidAlgebra : Representation k G V where
  toFun g :=
    { toFun := fun v => (MonoidAlgebra.single g (1 : k)) • v
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [smul_comm] }
  map_one' := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
    rw [show (MonoidAlgebra.single (1 : G) (1 : k)) = 1 from (MonoidAlgebra.one_def).symm, one_smul]
  map_mul' g h := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    rw [show (MonoidAlgebra.single (g * h) (1 : k))
          = MonoidAlgebra.single g 1 * MonoidAlgebra.single h 1 from by
        rw [MonoidAlgebra.single_mul_single, one_mul], mul_smul]

/-- The monoid-algebra-induced representation acts by the corresponding singleton element. -/
@[simp]
theorem representationOfMonoidAlgebra_apply (g : G) (v : V) :
    representationOfMonoidAlgebra (k := k) (G := G) (V := V) g v =
      (MonoidAlgebra.single g (1 : k)) • v :=
  rfl

/-- The representation induced by a monoid-algebra module sends a monoid element to the action of its singleton. -/
theorem representationOfMonoidAlgebra_toLinearMap (g : G) :
    (Algebra.lsmul k k V (MonoidAlgebra.single g (1 : k)) : Module.End k V)
      = representationOfMonoidAlgebra (k := k) (G := G) (V := V) g := by
  ext v
  simp only [Algebra.lsmul_coe, representationOfMonoidAlgebra_apply]

end OfModule

/-- The representation associated with a simple module has the auxiliary property. -/
theorem isAuxiliary_of_isSimpleModule
    {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
    [IsScalarTower k (MonoidAlgebra k G) V] [IsSimpleModule (MonoidAlgebra k G) V] :
    IsAuxiliary (representationOfMonoidAlgebra (k := k) (G := G) (V := V)) := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra k G) V
  refine ⟨inferInstance, fun N hN => ?_⟩
  let N' : Submodule (MonoidAlgebra k G) V :=
    { carrier := N
      add_mem' := fun hx hy => N.add_mem hx hy
      zero_mem' := N.zero_mem
      smul_mem' := fun a v hv => by
        induction a using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a₁ a₂ h₁ h₂ => rw [add_smul]; exact N.add_mem h₁ h₂
        | single g c =>
          have hsm : (MonoidAlgebra.single g c) • v = c • ((MonoidAlgebra.single g (1 : k)) • v) := by
            rw [← smul_assoc]
            congr 1
            rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
          rw [hsm]
          exact N.smul_mem c (hN g v hv) }
  have hNN' : ∀ x, x ∈ N' ↔ x ∈ N := fun _ => Iff.rfl
  rcases eq_bot_or_eq_top N' with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ N' := (hNN' x).mpr hx
    rw [h, Submodule.mem_bot] at this
    simp [this]
  · right
    refine eq_top_iff.mpr fun x _ => ?_
    have : x ∈ N' := by rw [h]; trivial
    exact (hNN' x).mp this

section PartII

universe u

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
variable {M : Type u} [AddCommGroup M] [Module k M] [FiniteDimensional k M]

omit [Fintype G] [Fintype H] in
/-- An auxiliary representation of a product group admits the displayed tensor-product description. -/
@[source_ref "Chapter5/Theorem5.6.1" (role := supporting)]
theorem auxiliary_exists_tensorProduct
    (τ : Representation k (G × H) M) (hτ : IsAuxiliary τ) :
    ∃ (V W : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
      (ρ : Representation k G V) (σ : Representation k H W),
      IsAuxiliary ρ ∧ IsAuxiliary σ ∧
      ∃ e : M ≃ₗ[k] V ⊗[k] W, ∀ gh : G × H, ∀ m : M,
        e (τ gh m) = tensorProductRepresentation ρ σ gh (e m) := by
  obtain ⟨hM_nt, hM_irr⟩ := hτ
  haveI : Nontrivial M := hM_nt
  set ρM : Representation k G M := τ.comp (MonoidHom.inl G H) with hρM
  set σM : Representation k H M := τ.comp (MonoidHom.inr G H) with hσM
  letI iAG : Module (MonoidAlgebra k G) M :=
    inferInstanceAs (Module (MonoidAlgebra k G) ρM.asModule)
  letI iAH : Module (MonoidAlgebra k H) M :=
    inferInstanceAs (Module (MonoidAlgebra k H) σM.asModule)
  letI iTG : IsScalarTower k (MonoidAlgebra k G) M :=
    inferInstanceAs (IsScalarTower k (MonoidAlgebra k G) ρM.asModule)
  letI iTH : IsScalarTower k (MonoidAlgebra k H) M :=
    inferInstanceAs (IsScalarTower k (MonoidAlgebra k H) σM.asModule)
  have hGsmul : ∀ (c : k) (g : G) (x : M),
      (MonoidAlgebra.single g c) • x = c • τ (g, 1) x := by
    intro c g x
    rw [Representation.single_smul]
    rfl
  have hHsmul : ∀ (d : k) (h : H) (x : M),
      (MonoidAlgebra.single h d) • x = d • τ (1, h) x := by
    intro d h x
    rw [Representation.single_smul]
    rfl
  have hcompute : ∀ (g : G) (h : H) (x : M),
      (MonoidAlgebra.single g (1 : k)) • ((MonoidAlgebra.single h (1 : k)) • x) = τ (g, h) x := by
    intro g h x
    rw [hHsmul, one_smul, hGsmul, one_smul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp
  haveI iComm : SMulCommClass (MonoidAlgebra k G) (MonoidAlgebra k H) M := by
    refine ⟨fun a b m => ?_⟩
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a₁ a₂ h₁ h₂ => rw [add_smul, add_smul, smul_add, h₁, h₂]
    | single g c =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp
      | add b₁ b₂ hb₁ hb₂ => rw [add_smul, smul_add, add_smul, hb₁, hb₂]
      | single h d =>
        have hcomm : τ (g, 1) (τ (1, h) m) = τ (1, h) (τ (g, 1) m) := by
          have hprod : ((g, 1) : G × H) * (1, h) = (1, h) * (g, 1) := by simp
          rw [← Module.End.mul_apply, ← map_mul, hprod, map_mul, Module.End.mul_apply]
        simp only [hGsmul, hHsmul, map_smul]
        rw [hcomm, smul_comm (c : k) (d : k)]
  have hMirr' : ∀ (U : Submodule k M),
      (∀ (a : MonoidAlgebra k G) (x : M), x ∈ U → a • x ∈ U) →
      (∀ (b : MonoidAlgebra k H) (x : M), x ∈ U → b • x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hUA hUB
    refine hM_irr U fun gh x hx => ?_
    obtain ⟨g, h⟩ := gh
    have hx1 : (MonoidAlgebra.single h (1 : k)) • x ∈ U := hUB _ x hx
    have hx2 : (MonoidAlgebra.single g (1 : k)) •
        ((MonoidAlgebra.single h (1 : k)) • x) ∈ U := hUA _ _ hx1
    rw [← hcompute]; exact hx2
  obtain ⟨V, W, instV, instkV, instAV, instTV, instFV, hVsimple,
      instW, instkW, instBW, instTW, instFW, hWsimple, e, hAe, hBe⟩ :=
    RepresentationTheory.Algebra.Module.TensorProductSimplicity.exists_tensorFactorization_of_simpleBimodule
      k (MonoidAlgebra k G) (MonoidAlgebra k H) M hMirr'
  refine ⟨V, W, instV, instkV, instFV, instW, instkW, instFW,
    representationOfMonoidAlgebra (k := k) (G := G) (V := V),
    representationOfMonoidAlgebra (k := k) (G := H) (V := W),
    isAuxiliary_of_isSimpleModule, isAuxiliary_of_isSimpleModule, e, ?_⟩
  intro gh m
  obtain ⟨g, h⟩ := gh
  rw [← hcompute, hAe, hBe]
  rw [representationOfMonoidAlgebra_toLinearMap, representationOfMonoidAlgebra_toLinearMap,
    ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  rfl

end PartII

section Combined

universe u

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]

omit [Fintype G] [Fintype H] in
/-- Over an algebraically closed field, the auxiliary representation property is characterized by the displayed tensor-product construction and decomposition. -/
@[source_ref "Chapter5/Introduction_5.6" (role := primary),
  source_ref "Chapter5/Theorem5.6.1" (role := primary)]
theorem auxiliary_tensorProduct_characterization :
    (∀ {V W : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
        [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (ρ : Representation k G V) (σ : Representation k H W),
        IsAuxiliary ρ → IsAuxiliary σ → IsAuxiliary (tensorProductRepresentation ρ σ)) ∧
    (∀ {M : Type u} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
        (τ : Representation k (G × H) M), IsAuxiliary τ →
        ∃ (V W : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
          (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
          (ρ : Representation k G V) (σ : Representation k H W),
          IsAuxiliary ρ ∧ IsAuxiliary σ ∧
          ∃ e : M ≃ₗ[k] V ⊗[k] W, ∀ gh : G × H, ∀ m : M,
            e (τ gh m) = tensorProductRepresentation ρ σ gh (e m)) :=
  ⟨fun _ _ hρ hσ => isAuxiliary_tensorProductRepresentation hρ hσ,
   fun τ hτ => auxiliary_exists_tensorProduct τ hτ⟩

end Combined

end RepresentationTheory.AuxiliaryTensorProductRepresentations
