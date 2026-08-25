/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroupRepresentations.Auxiliary
import RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar
import RepresentationTheory.Alignment.Attribute


open scoped MonoidAlgebra

namespace RepresentationTheory.Representation.Character.InversionAndInvariantForms

variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A nonzero invariant bilinear form on an irreducible complex representation is left nondegenerate. -/
theorem invariant_bilinear_form_left_nondegenerate
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hBne : B ≠ 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    ∀ v, (∀ w, B v w = 0) → v = 0 := by
  -- The radical `ker B` is `ρ`-invariant.
  have hRinv : LinearMap.ker B ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext w
    simp only [LinearMap.zero_apply]
    have hgg : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h1 : B (ρ g x) w = B (ρ g x) (ρ g (ρ g⁻¹ w)) := by rw [hgg]
    rw [h1, hinv g x (ρ g⁻¹ w)]
    rw [hx]
    simp
  -- Simplicity transports to the lattice of `ρ`-invariant submodules.
  haveI := hρ
  haveI hSO : IsSimpleOrder ρ.invtSubmodule :=
    (Representation.mapSubmodule ρ).isSimpleOrder_iff.mpr hρ.toIsSimpleOrder
  -- The radical is `⊥` or `⊤`; `B ≠ 0` rules out `⊤`.
  have hker : LinearMap.ker B = ⊥ := by
    rcases hSO.eq_bot_or_eq_top ⟨LinearMap.ker B, hRinv⟩ with h | h
    · simpa using congrArg Subtype.val h
    · exact absurd (LinearMap.ker_eq_top.mp (by simpa using congrArg Subtype.val h)) hBne
  -- `ker B = ⊥` is exactly nondegeneracy.
  intro v hv
  have hv' : v ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker]; ext w; exact hv w
  rw [hker, Submodule.mem_bot] at hv'
  exact hv'

open scoped TensorProduct

private lemma trace_eq_sum_repr_diag
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ M f = ∑ i, b.repr (f (b i)) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b f]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]

private lemma trace_comm_comp_map
    {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (A B : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W ⊗[ℂ] W)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B)
      = LinearMap.trace ℂ W (A ∘ₗ B) := by
  classical
  set b := Module.finBasis ℂ W with hb
  -- LHS via the tensor basis
  rw [trace_eq_sum_repr_diag (b.tensorProduct b)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B),
      Fintype.sum_prod_type]
  -- simplify the diagonal tensor entries
  have hLHS : ∀ i j, (b.tensorProduct b).repr
        ((((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B))
          ((b.tensorProduct b) (i, j))) (i, j)
        = b.repr (A (b i)) j * b.repr (B (b j)) i := by
    intro i j
    rw [Module.Basis.tensorProduct_apply]
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.comm_tmul, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  simp_rw [hLHS]
  -- RHS via matrix product
  rw [trace_eq_sum_repr_diag b (A ∘ₗ B)]
  have hRHS : ∀ i, b.repr ((A ∘ₗ B) (b i)) i
      = ∑ j, b.repr (A (b j)) i * b.repr (B (b i)) j := by
    intro i
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← Module.Basis.sum_repr b (B (b i))]
    rw [map_sum, map_sum, Finset.sum_apply']
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hRHS]
  rw [Finset.sum_comm]

variable [Fintype G] [DecidableEq G] [Module.Finite ℂ V]

/-- An irreducible complex representation for which an auxiliary value equals one admits a symmetric nonzero invariant bilinear form. -/
theorem exists_symmetric_ne_zero_invariant_bilinear_form_of_auxiliary_eq_one
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hFS : RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1) :
    ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ v w, B v w = B w v) ∧ B ≠ 0 ∧ (∀ g v w, B (ρ g v) (ρ g w) = B v w) := by
  classical
  haveI : Nonempty G := ⟨1⟩
  haveI hcard : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Fintype.card_pos).ne')
  -- the space of bilinear forms is the representation space of `linHom ρ ρ.dual`
  set Bil := V →ₗ[ℂ] Module.Dual ℂ V with hBildef
  set Λ := Representation.linHom ρ ρ.dual with hΛdef
  haveI : Module.Finite ℂ Bil :=
    inferInstanceAs (Module.Finite ℂ (V →ₗ[ℂ] Module.Dual ℂ V))
  have hΛapp : ∀ (g : G) (C : Bil) (v w : V), (Λ g C) v w = C (ρ g⁻¹ v) (ρ g⁻¹ w) := by
    intro g C v w
    rw [hΛdef, Representation.linHom_apply]
    simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply]
  -- the swap (flip) operator, a `ℂ`-linear involution on `Bil`
  set τ : Bil →ₗ[ℂ] Bil := (LinearMap.lflip : Bil ≃ₗ[ℂ] Bil).toLinearMap with hτdef
  have hτ_apply : ∀ (C : Bil) (v w : V), τ C v w = C w v := fun C v w => rfl
  have hτinvol : ∀ C : Bil, τ (τ C) = C := by
    intro C; ext v w; rw [hτ_apply, hτ_apply]
  -- `τ` commutes with each `Λ g`
  have hτΛ : ∀ (g : G) (C : Bil), τ (Λ g C) = Λ g (τ C) := by
    intro g C; ext v w
    simp only [hτ_apply, hΛapp]
  have hτinv : ∀ C ∈ Λ.invariants, τ C ∈ Λ.invariants := by
    intro C hC
    rw [Representation.mem_invariants] at hC ⊢
    intro g; rw [← hτΛ g C, hC g]
  -- the iso `Dual V ⊗ Dual V ≃ Bil`
  set T := Module.Dual ℂ V ⊗[ℂ] Module.Dual ℂ V with hTdef
  set E : T ≃ₗ[ℂ] Bil := dualTensorHomEquiv ℂ V (Module.Dual ℂ V) with hEdef
  have hEapp : ∀ (φ ψ : Module.Dual ℂ V) (v : V), (E (φ ⊗ₜ[ℂ] ψ)) v = φ v • ψ := by
    intro φ ψ v
    have hE : E (φ ⊗ₜ[ℂ] ψ) = dualTensorHom ℂ V (Module.Dual ℂ V) (φ ⊗ₜ[ℂ] ψ) := by
      rw [hEdef]; exact dualTensorHomEquivOfBasis_apply (Module.Free.chooseBasis ℂ V) _
    rw [hE, dualTensorHom_apply]
  have hEsymm : (E : T →ₗ[ℂ] Bil) ∘ₗ (E.symm : Bil →ₗ[ℂ] T) = LinearMap.id := by
    ext x; simp
  have hEsymm' : (E.symm : Bil →ₗ[ℂ] T) ∘ₗ (E : T →ₗ[ℂ] Bil) = LinearMap.id := by
    ext x; simp
  -- the per-`g` trace identity `trace (τ ∘ Λ g) = χ(g⁻¹ g⁻¹)`
  have hg : ∀ g : G, LinearMap.trace ℂ Bil (τ ∘ₗ Λ g) = ρ.character (g⁻¹ * g⁻¹) := by
    intro g
    set Fg := (TensorProduct.comm ℂ (Module.Dual ℂ V) (Module.Dual ℂ V)).toLinearMap
        ∘ₗ TensorProduct.map (ρ.dual g) (ρ.dual g) with hFg
    have hINT : (τ ∘ₗ Λ g) ∘ₗ (E : T →ₗ[ℂ] Bil) = (E : T →ₗ[ℂ] Bil) ∘ₗ Fg := by
      apply TensorProduct.ext'
      intro φ ψ
      refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
      have hL : ((τ ∘ₗ Λ g) ∘ₗ (E : T →ₗ[ℂ] Bil)) (φ ⊗ₜ[ℂ] ψ) v w
          = φ (ρ g⁻¹ w) * ψ (ρ g⁻¹ v) := by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hτ_apply, hΛapp,
          LinearEquiv.coe_coe, hEapp, LinearMap.smul_apply, smul_eq_mul]
      have hR : ((E : T →ₗ[ℂ] Bil) ∘ₗ Fg) (φ ⊗ₜ[ℂ] ψ) v w
          = ψ (ρ g⁻¹ v) * φ (ρ g⁻¹ w) := by
        rw [LinearMap.comp_apply, hFg, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.coe_coe, TensorProduct.map_tmul, TensorProduct.comm_tmul, hEapp,
          LinearMap.smul_apply]
        simp only [Representation.dual_apply, Module.Dual.transpose_apply,
          LinearMap.comp_apply, smul_eq_mul]
      rw [hL, hR, mul_comm]
    have e1 : (E : T →ₗ[ℂ] Bil) ∘ₗ (Fg ∘ₗ (E.symm : Bil →ₗ[ℂ] T)) = τ ∘ₗ Λ g := by
      rw [← LinearMap.comp_assoc, ← hINT, LinearMap.comp_assoc, hEsymm, LinearMap.comp_id]
    rw [← e1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hEsymm',
      LinearMap.comp_id, hFg, trace_comm_comp_map]
    rw [show ρ.dual g ∘ₗ ρ.dual g = ρ.dual (g * g) from by rw [map_mul]; rfl]
    change ρ.dual.character (g * g) = ρ.character (g⁻¹ * g⁻¹)
    rw [Representation.char_dual, mul_inv_rev]
  -- the averaging projector onto invariants
  set P := Representation.averageMap Λ with hPdef
  have hPsum : P = (⅟(Fintype.card G : ℂ)) • ∑ g : G, Λ g := by
    rw [hPdef]
    simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
      Representation.asAlgebraHom_of]
  have hPmem : ∀ C, P C ∈ Λ.invariants := fun C => Λ.averageMap_invariant C
  have hPfix : ∀ C ∈ Λ.invariants, P C = C := fun C hC => Λ.averageMap_id C hC
  have hPidem : ∀ C, P (P C) = P C := fun C => Λ.averageMap_id (P C) (Λ.averageMap_invariant C)
  -- **the trace identity**: `trace (τ ∘ P) = FS = 1`
  have htrace : LinearMap.trace ℂ Bil (τ ∘ₗ P) = 1 := by
    have hcomp : τ ∘ₗ P = (⅟(Fintype.card G : ℂ)) • ∑ g : G, (τ ∘ₗ Λ g) := by
      rw [hPsum, ← Module.End.mul_eq_comp, mul_smul_comm, Finset.mul_sum]
      rfl
    rw [hcomp, map_smul, map_sum]
    simp_rw [hg]
    rw [show (∑ g : G, ρ.character (g⁻¹ * g⁻¹)) = ∑ g : G, ρ.character (g * g) from
          Equiv.sum_comp (Equiv.inv G) (fun g => ρ.character (g * g))]
    rw [invOf_eq_inv, smul_eq_mul]
    exact hFS
  -- `IsProj.trace` needs freeness of the range/kernel; over the field `ℂ` these hold, but
  -- type-class search does not fire `Module.Free.of_divisionRing` here, so supply it explicitly.
  haveI : Module.Free ℂ ↥Λ.invariants := Module.Free.of_divisionRing ℂ ↥Λ.invariants
  haveI : Module.Free ℂ ↥(LinearMap.ker (Representation.averageMap Λ)) :=
    Module.Free.of_divisionRing ℂ ↥(LinearMap.ker (Representation.averageMap Λ))
  have hP_trace : LinearMap.trace ℂ Bil P = (Module.finrank ℂ Λ.invariants : ℂ) := by
    rw [hPdef]; exact (Λ.isProj_averageMap).trace
  -- the symmetric-part projector `Psym = ½(P + τ P)`, projecting onto symmetric invariants
  set Psym : Bil →ₗ[ℂ] Bil := (2⁻¹ : ℂ) • (P + τ ∘ₗ P) with hPsymdef
  have hPsymapp : ∀ C, Psym C = (2⁻¹ : ℂ) • (P C + τ (P C)) := by
    intro C
    change ((2⁻¹ : ℂ) • (P + τ ∘ₗ P)) C = _
    rw [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
  have hτfixPsym : ∀ C, τ (Psym C) = Psym C := by
    intro C
    conv_rhs => rw [hPsymapp C]
    rw [hPsymapp C, map_smul, map_add, hτinvol, add_comm]
  have hPfixPsym : ∀ C, P (Psym C) = Psym C := by
    intro C
    conv_rhs => rw [hPsymapp C]
    rw [hPsymapp C, map_smul, map_add, hPidem,
      hPfix (τ (P C)) (hτinv (P C) (hPmem C))]
  have hPsymInv : ∀ C, Psym C ∈ Λ.invariants := by
    intro C; rw [hPsymapp]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hPmem C) (hτinv (P C) (hPmem C)))
  have hPsymidem : IsIdempotentElem Psym := by
    apply LinearMap.ext; intro C
    rw [Module.End.mul_apply, hPsymapp (Psym C), hPfixPsym C, hτfixPsym C,
      ← two_smul ℂ (Psym C), smul_smul, show (2⁻¹ * 2 : ℂ) = 1 by norm_num, one_smul]
  -- the rank counting: `2 · dim(symmetric invariants) = dim(invariants) + 1`
  have hisproj := (LinearMap.isProj_range_iff_isIdempotentElem Psym).mpr hPsymidem
  haveI : Module.Free ℂ ↥(LinearMap.range Psym) :=
    Module.Free.of_divisionRing ℂ ↥(LinearMap.range Psym)
  haveI : Module.Free ℂ ↥(LinearMap.ker Psym) :=
    Module.Free.of_divisionRing ℂ ↥(LinearMap.ker Psym)
  have hPsym_trace_eq : LinearMap.trace ℂ Bil Psym
      = (Module.finrank ℂ (LinearMap.range Psym) : ℂ) := hisproj.trace
  have hPsym_trace2 : LinearMap.trace ℂ Bil Psym
      = (2⁻¹ : ℂ) * (LinearMap.trace ℂ Bil P + LinearMap.trace ℂ Bil (τ ∘ₗ P)) := by
    rw [hPsymdef, map_smul, map_add, smul_eq_mul]
  set d := Module.finrank ℂ Λ.invariants with hd
  set s := Module.finrank ℂ (LinearMap.range Psym) with hs
  have h2s : (2 : ℂ) * (s : ℂ) = (d : ℂ) + 1 := by
    have : (s : ℂ) = (2⁻¹ : ℂ) * ((d : ℂ) + 1) := by
      rw [← hPsym_trace_eq, hPsym_trace2, hP_trace, htrace]
    rw [this]; ring
  have hnat : 2 * s = d + 1 := by exact_mod_cast h2s
  have hspos : 0 < s := by omega
  -- extract a nonzero symmetric invariant form
  haveI : Nontrivial (LinearMap.range Psym) := Module.nontrivial_of_finrank_pos hspos
  obtain ⟨⟨B, hBmem⟩, hBne0⟩ := exists_ne (0 : (LinearMap.range Psym))
  obtain ⟨C, hC⟩ := hBmem
  have hBne : B ≠ 0 := fun h => hBne0 (Subtype.ext (by simpa using h))
  have hBinv_mem : B ∈ Λ.invariants := hC ▸ hPsymInv C
  refine ⟨B, ?_, hBne, ?_⟩
  · -- symmetric: `τ B = B`
    intro v w
    have hsymB : τ B = B := by rw [← hC]; exact hτfixPsym C
    have h := hτ_apply B w v
    rw [hsymB] at h
    exact h.symm
  · -- invariant
    intro g v w
    have hinv : Λ g⁻¹ B = B := (Representation.mem_invariants _ _).mp hBinv_mem g⁻¹
    have h := hΛapp g⁻¹ B v w
    rw [hinv, inv_inv] at h
    exact h.symm

/-- For an irreducible complex representation, an auxiliary value equal to one gives an auxiliary property. -/
theorem auxiliary_property_of_auxiliary_eq_one
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hFS : RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  obtain ⟨B, hsym, hBne, hinv⟩ :=
    exists_symmetric_ne_zero_invariant_bilinear_form_of_auxiliary_eq_one ρ hρ hFS
  exact ⟨B, hsym, invariant_bilinear_form_left_nondegenerate ρ hρ B hBne hinv, hinv⟩

/-- For an irreducible complex representation, an auxiliary property forces an auxiliary value to equal one. -/
theorem auxiliary_eq_one_of_auxiliary_property
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hreal : RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1 := by
  classical
  haveI : Nonempty G := ⟨1⟩
  haveI hcard : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Fintype.card_pos).ne')
  haveI : Invertible (Nat.card G : ℂ) := by rw [Nat.card_eq_fintype_card]; infer_instance
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  haveI hNT : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  -- the space of bilinear forms is the representation space of `linHom ρ ρ.dual`
  set Bil := V →ₗ[ℂ] Module.Dual ℂ V with hBildef
  set Λ := Representation.linHom ρ ρ.dual with hΛdef
  haveI : Module.Finite ℂ Bil :=
    inferInstanceAs (Module.Finite ℂ (V →ₗ[ℂ] Module.Dual ℂ V))
  have hΛapp : ∀ (g : G) (C : Bil) (v w : V), (Λ g C) v w = C (ρ g⁻¹ v) (ρ g⁻¹ w) := by
    intro g C v w
    rw [hΛdef, Representation.linHom_apply]
    simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply]
  -- the swap (flip) operator, a `ℂ`-linear involution on `Bil`
  set τ : Bil →ₗ[ℂ] Bil := (LinearMap.lflip : Bil ≃ₗ[ℂ] Bil).toLinearMap with hτdef
  have hτ_apply : ∀ (C : Bil) (v w : V), τ C v w = C w v := fun C v w => rfl
  have hτinvol : ∀ C : Bil, τ (τ C) = C := by
    intro C; ext v w; rw [hτ_apply, hτ_apply]
  have hτΛ : ∀ (g : G) (C : Bil), τ (Λ g C) = Λ g (τ C) := by
    intro g C; ext v w
    simp only [hτ_apply, hΛapp]
  have hτinv : ∀ C ∈ Λ.invariants, τ C ∈ Λ.invariants := by
    intro C hC
    rw [Representation.mem_invariants] at hC ⊢
    intro g; rw [← hτΛ g C, hC g]
  -- the iso `Dual V ⊗ Dual V ≃ Bil`
  set T := Module.Dual ℂ V ⊗[ℂ] Module.Dual ℂ V with hTdef
  set E : T ≃ₗ[ℂ] Bil := dualTensorHomEquiv ℂ V (Module.Dual ℂ V) with hEdef
  have hEapp : ∀ (φ ψ : Module.Dual ℂ V) (v : V), (E (φ ⊗ₜ[ℂ] ψ)) v = φ v • ψ := by
    intro φ ψ v
    have hE : E (φ ⊗ₜ[ℂ] ψ) = dualTensorHom ℂ V (Module.Dual ℂ V) (φ ⊗ₜ[ℂ] ψ) := by
      rw [hEdef]; exact dualTensorHomEquivOfBasis_apply (Module.Free.chooseBasis ℂ V) _
    rw [hE, dualTensorHom_apply]
  have hEsymm : (E : T →ₗ[ℂ] Bil) ∘ₗ (E.symm : Bil →ₗ[ℂ] T) = LinearMap.id := by
    ext x; simp
  have hEsymm' : (E.symm : Bil →ₗ[ℂ] T) ∘ₗ (E : T →ₗ[ℂ] Bil) = LinearMap.id := by
    ext x; simp
  -- the per-`g` trace identity `trace (τ ∘ Λ g) = χ(g⁻¹ g⁻¹)`
  have hg : ∀ g : G, LinearMap.trace ℂ Bil (τ ∘ₗ Λ g) = ρ.character (g⁻¹ * g⁻¹) := by
    intro g
    set Fg := (TensorProduct.comm ℂ (Module.Dual ℂ V) (Module.Dual ℂ V)).toLinearMap
        ∘ₗ TensorProduct.map (ρ.dual g) (ρ.dual g) with hFg
    have hINT : (τ ∘ₗ Λ g) ∘ₗ (E : T →ₗ[ℂ] Bil) = (E : T →ₗ[ℂ] Bil) ∘ₗ Fg := by
      apply TensorProduct.ext'
      intro φ ψ
      refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
      have hL : ((τ ∘ₗ Λ g) ∘ₗ (E : T →ₗ[ℂ] Bil)) (φ ⊗ₜ[ℂ] ψ) v w
          = φ (ρ g⁻¹ w) * ψ (ρ g⁻¹ v) := by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hτ_apply, hΛapp,
          LinearEquiv.coe_coe, hEapp, LinearMap.smul_apply, smul_eq_mul]
      have hR : ((E : T →ₗ[ℂ] Bil) ∘ₗ Fg) (φ ⊗ₜ[ℂ] ψ) v w
          = ψ (ρ g⁻¹ v) * φ (ρ g⁻¹ w) := by
        rw [LinearMap.comp_apply, hFg, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.coe_coe, TensorProduct.map_tmul, TensorProduct.comm_tmul, hEapp,
          LinearMap.smul_apply]
        simp only [Representation.dual_apply, Module.Dual.transpose_apply,
          LinearMap.comp_apply, smul_eq_mul]
      rw [hL, hR, mul_comm]
    have e1 : (E : T →ₗ[ℂ] Bil) ∘ₗ (Fg ∘ₗ (E.symm : Bil →ₗ[ℂ] T)) = τ ∘ₗ Λ g := by
      rw [← LinearMap.comp_assoc, ← hINT, LinearMap.comp_assoc, hEsymm, LinearMap.comp_id]
    rw [← e1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hEsymm',
      LinearMap.comp_id, hFg, trace_comm_comp_map]
    rw [show ρ.dual g ∘ₗ ρ.dual g = ρ.dual (g * g) from by rw [map_mul]; rfl]
    change ρ.dual.character (g * g) = ρ.character (g⁻¹ * g⁻¹)
    rw [Representation.char_dual, mul_inv_rev]
  -- the averaging projector onto invariants
  set P := Representation.averageMap Λ with hPdef
  have hPsum : P = (⅟(Fintype.card G : ℂ)) • ∑ g : G, Λ g := by
    rw [hPdef]
    simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
      Representation.asAlgebraHom_of]
  have hPmem : ∀ C, P C ∈ Λ.invariants := fun C => Λ.averageMap_invariant C
  have hPfix : ∀ C ∈ Λ.invariants, P C = C := fun C hC => Λ.averageMap_id C hC
  have hPidem : ∀ C, P (P C) = P C := fun C => Λ.averageMap_id (P C) (Λ.averageMap_invariant C)
  -- **the trace identity** in general form: `trace (τ ∘ P) = FS(ρ)`
  have htrace : LinearMap.trace ℂ Bil (τ ∘ₗ P) = RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ := by
    have hcomp : τ ∘ₗ P = (⅟(Fintype.card G : ℂ)) • ∑ g : G, (τ ∘ₗ Λ g) := by
      rw [hPsum, ← Module.End.mul_eq_comp, mul_smul_comm, Finset.mul_sum]
      rfl
    rw [hcomp, map_smul, map_sum]
    simp_rw [hg]
    rw [show (∑ g : G, ρ.character (g⁻¹ * g⁻¹)) = ∑ g : G, ρ.character (g * g) from
          Equiv.sum_comp (Equiv.inv G) (fun g => ρ.character (g * g))]
    rw [invOf_eq_inv, smul_eq_mul, RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar]
    simp only [Representation.character]
  -- `IsProj.trace` needs freeness of the range/kernel; over the field `ℂ` these hold, but
  -- type-class search does not fire `Module.Free.of_divisionRing` here, so supply it explicitly.
  haveI : Module.Free ℂ ↥Λ.invariants := Module.Free.of_divisionRing ℂ ↥Λ.invariants
  haveI : Module.Free ℂ ↥(LinearMap.ker (Representation.averageMap Λ)) :=
    Module.Free.of_divisionRing ℂ ↥(LinearMap.ker (Representation.averageMap Λ))
  have hP_trace : LinearMap.trace ℂ Bil P = (Module.finrank ℂ Λ.invariants : ℂ) := by
    rw [hPdef]; exact (Λ.isProj_averageMap).trace
  -- the symmetric-part projector `Psym = ½(P + τ P)`
  set Psym : Bil →ₗ[ℂ] Bil := (2⁻¹ : ℂ) • (P + τ ∘ₗ P) with hPsymdef
  have hPsymapp : ∀ C, Psym C = (2⁻¹ : ℂ) • (P C + τ (P C)) := by
    intro C
    change ((2⁻¹ : ℂ) • (P + τ ∘ₗ P)) C = _
    rw [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
  have hτfixPsym : ∀ C, τ (Psym C) = Psym C := by
    intro C
    conv_rhs => rw [hPsymapp C]
    rw [hPsymapp C, map_smul, map_add, hτinvol, add_comm]
  have hPfixPsym : ∀ C, P (Psym C) = Psym C := by
    intro C
    conv_rhs => rw [hPsymapp C]
    rw [hPsymapp C, map_smul, map_add, hPidem,
      hPfix (τ (P C)) (hτinv (P C) (hPmem C))]
  have hPsymInv : ∀ C, Psym C ∈ Λ.invariants := by
    intro C; rw [hPsymapp]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hPmem C) (hτinv (P C) (hPmem C)))
  have hPsymidem : IsIdempotentElem Psym := by
    apply LinearMap.ext; intro C
    rw [Module.End.mul_apply, hPsymapp (Psym C), hPfixPsym C, hτfixPsym C,
      ← two_smul ℂ (Psym C), smul_smul, show (2⁻¹ * 2 : ℂ) = 1 by norm_num, one_smul]
  have hisproj := (LinearMap.isProj_range_iff_isIdempotentElem Psym).mpr hPsymidem
  haveI : Module.Free ℂ ↥(LinearMap.range Psym) :=
    Module.Free.of_divisionRing ℂ ↥(LinearMap.range Psym)
  haveI : Module.Free ℂ ↥(LinearMap.ker Psym) :=
    Module.Free.of_divisionRing ℂ ↥(LinearMap.ker Psym)
  have hPsym_trace_eq : LinearMap.trace ℂ Bil Psym
      = (Module.finrank ℂ (LinearMap.range Psym) : ℂ) := hisproj.trace
  have hPsym_trace2 : LinearMap.trace ℂ Bil Psym
      = (2⁻¹ : ℂ) * (LinearMap.trace ℂ Bil P + LinearMap.trace ℂ Bil (τ ∘ₗ P)) := by
    rw [hPsymdef, map_smul, map_add, smul_eq_mul]
  set d := Module.finrank ℂ Λ.invariants with hd
  set s := Module.finrank ℂ (LinearMap.range Psym) with hs
  -- **the general trace identity**: `2·s = d + FS(ρ)`
  have h2s : (2 : ℂ) * (s : ℂ) = (d : ℂ) + RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ := by
    have : (s : ℂ) = (2⁻¹ : ℂ) * ((d : ℂ) + RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ) := by
      rw [← hPsym_trace_eq, hPsym_trace2, hP_trace, htrace]
    rw [this]; ring
  -- unpack the real-type structure
  obtain ⟨Bs, hBs_sym, hBs_nd, hBs_inv⟩ := hreal
  -- `Bs`, seen as an element of `Bil`, is a `Λ`-invariant, symmetric, nonzero form
  have hBsInvMem : (Bs : Bil) ∈ Λ.invariants := by
    rw [Representation.mem_invariants]
    intro g; ext v w
    rw [hΛapp g Bs v w]; exact hBs_inv g⁻¹ v w
  have hτBs : τ (Bs : Bil) = Bs := by
    ext v w; rw [hτ_apply]; exact hBs_sym w v
  have hBsne : (Bs : Bil) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h0; exact hv (hBs_nd v fun w => by rw [h0]; rfl)
  -- `Bs` is fixed by `Psym`, so it lies in `range Psym`; hence `s ≥ 1`
  have hPsymBs : Psym (Bs : Bil) = Bs := by
    rw [hPsymapp Bs, hPfix Bs hBsInvMem, hτBs, ← two_smul ℂ (Bs : Bil), smul_smul,
      show (2⁻¹ * 2 : ℂ) = 1 by norm_num, one_smul]
  have hBsmem : (Bs : Bil) ∈ LinearMap.range Psym := ⟨Bs, hPsymBs⟩
  haveI : Nontrivial (LinearMap.range Psym) := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro hbot
    exact hBsne (by simpa using (hbot ▸ hBsmem : (Bs : Bil) ∈ (⊥ : Submodule ℂ Bil)))
  have hspos : 0 < s := by
    rw [hs]; exact Module.finrank_pos (R := ℂ) (M := ↥(LinearMap.range Psym))
  -- symmetric invariants sit inside all invariants, so `s ≤ d`
  have hsd_le : s ≤ d := by
    rw [hs, hd]
    exact Submodule.finrank_mono (fun x ⟨C, hC⟩ => hC ▸ hPsymInv C)
  -- self-duality of the character (from the nondegenerate invariant form) forces `d = 1`
  have hchar_sd : ∀ g, ρ.character g⁻¹ = ρ.character g := by
    obtain ⟨e, he⟩ :=
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.exists_intertwiner_to_dual_of_nondegenerate_invariant_form ρ Bs hBs_nd hBs_inv
    intro g
    have hconj : ρ.dual g = e.conj (ρ g) := by
      ext w
      rw [LinearEquiv.conj_apply_apply, he g (e.symm w), LinearEquiv.apply_symm_apply]
    calc ρ.character g⁻¹
        = ρ.dual.character g := (ρ.char_dual g).symm
      _ = LinearMap.trace ℂ (Module.Dual ℂ V) (e.conj (ρ g)) := by
            rw [Representation.character, hconj]
      _ = LinearMap.trace ℂ V (ρ g) := LinearMap.trace_conj' (ρ g) e
      _ = ρ.character g := rfl
  have hd1 : d = 1 := by
    have hkey := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom ρ ρ.dual)
    have hortho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
    have hchar : ∀ g, (Representation.linHom ρ ρ.dual).character g
        = ρ.character g * ρ.character g⁻¹ := fun g => by
      rw [Representation.char_linHom, Representation.char_dual, hchar_sd g]
    rw [Finset.sum_congr rfl (fun g _ => hchar g), hortho] at hkey
    rw [hd, hΛdef]
    exact_mod_cast hkey.symm
  -- conclude: `s = 1`, hence `FS(ρ) = 2·1 − 1 = 1`
  have hsval : s = 1 := by omega
  rw [hsval, hd1] at h2s
  push_cast at h2s
  linear_combination -h2s


section RealForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def avgCoordForm
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V) : V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  ∑ g : G, (∑ i : ι,
    (LinearMap.mul ℂ ℂ).compl₁₂ (b.coord i) (b.coord i)).compl₁₂ (ρ g) (ρ g)

private theorem avgCoordForm_apply
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V) (v w : V) :
    avgCoordForm ρ b v w
      = ∑ g : G, ∑ i : ι, (b.coord i (ρ g v)) * (b.coord i (ρ g w)) := by
  simp only [avgCoordForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply']

/-- An irreducible complex representation with real matrix entries in a finite basis has an auxiliary property. -/
theorem auxiliary_property_of_real_matrix_entries
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (b : Module.Basis ι ℂ V)
    (hreal : ∀ (g : G) (i j : ι), (LinearMap.toMatrix b b (ρ g) i j).im = 0) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  haveI := hρ
  haveI hNT : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨i₀⟩ := b.index_nonempty
  -- Symmetry: each summand is symmetric because multiplication on `ℂ` is.
  have hsym : ∀ v w, avgCoordForm ρ b v w = avgCoordForm ρ b w v := by
    intro v w
    rw [avgCoordForm_apply, avgCoordForm_apply]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- `G`-invariance: reindex the average by `h ↦ h * g`.
  have hmul : ∀ (g h : G) (x : V), ρ h (ρ g x) = ρ (h * g) x := by
    intro g h x; rw [map_mul]; rfl
  have hinv : ∀ g v w, avgCoordForm ρ b (ρ g v) (ρ g w) = avgCoordForm ρ b v w := by
    intro g v w
    rw [avgCoordForm_apply, avgCoordForm_apply,
      ← Equiv.sum_comp (Equiv.mulRight g)
        (fun h => ∑ i : ι, (b.coord i (ρ h v)) * (b.coord i (ρ h w)))]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hmul g h v, hmul g h w]
  -- Reading a coordinate of `ρ g` as a matrix entry, hence real.
  have hcoord : ∀ (g : G) (i : ι),
      b.coord i (ρ g (b i₀)) = LinearMap.toMatrix b b (ρ g) i i₀ := by
    intro g i; rw [LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  -- Non-vanishing: the real part of `B (b i₀) (b i₀)` is `≥ 1`.
  have hre : (avgCoordForm ρ b (b i₀) (b i₀)).re
      = ∑ g : G, ∑ i : ι, ((b.coord i (ρ g (b i₀))).re) ^ 2 := by
    rw [avgCoordForm_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have him : (b.coord i (ρ g (b i₀))).im = 0 := by rw [hcoord]; exact hreal g i i₀
    rw [Complex.mul_re, him, sq]; ring
  have hnonneg : ∀ g : G, (0 : ℝ) ≤ ∑ i : ι, ((b.coord i (ρ g (b i₀))).re) ^ 2 :=
    fun g => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hone : (∑ i : ι, ((b.coord i (ρ (1 : G) (b i₀))).re) ^ 2) = 1 := by
    have : ∀ i : ι, b.coord i (ρ (1 : G) (b i₀)) = (if i = i₀ then (1 : ℂ) else 0) := by
      intro i
      rw [map_one, Module.End.one_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      simp [eq_comm]
    simp only [this]
    rw [Finset.sum_congr rfl (fun i _ => by split <;> simp : ∀ i ∈ Finset.univ,
      ((if i = i₀ then (1 : ℂ) else 0).re) ^ 2 = (if i = i₀ then (1 : ℝ) else 0))]
    simp
  have hge : (1 : ℝ) ≤ (avgCoordForm ρ b (b i₀) (b i₀)).re := by
    rw [hre, ← hone]
    exact Finset.single_le_sum (fun g _ => hnonneg g) (Finset.mem_univ (1 : G))
  have hval_ne : avgCoordForm ρ b (b i₀) (b i₀) ≠ 0 := by
    intro h0
    rw [h0] at hge
    simp only [Complex.zero_re] at hge
    linarith
  have hBne : avgCoordForm ρ b ≠ 0 := by
    intro h0
    exact hval_ne (by rw [h0]; simp)
  exact ⟨avgCoordForm ρ b, hsym,
    invariant_bilinear_form_left_nondegenerate ρ hρ _ hBne hinv, hinv⟩

/-- An irreducible complex representation with rational matrix entries in a finite basis has an auxiliary property. -/
theorem auxiliary_property_of_rational_matrix_entries
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (b : Module.Basis ι ℂ V)
    (hrat : ∀ (g : G) (i j : ι), ∃ q : ℚ, LinearMap.toMatrix b b (ρ g) i j = (q : ℂ)) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ :=
  auxiliary_property_of_real_matrix_entries ρ hρ b fun g i j => by
    obtain ⟨q, hq⟩ := hrat g i j; rw [hq]; simp

end RealForm


open Polynomial in
private lemma reverse_multiset_prod {R : Type*} [CommRing R] [NoZeroDivisors R]
    (s : Multiset R[X]) : s.prod.reverse = (s.map Polynomial.reverse).prod := by
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.prod_zero, Multiset.map_zero]
    rw [show (1 : R[X]) = C 1 from (map_one C).symm, Polynomial.reverse_C]
  | cons a s ih =>
    rw [Multiset.prod_cons, Polynomial.reverse_mul_of_domain, ih, Multiset.map_cons,
      Multiset.prod_cons]

open Polynomial in
private lemma roots_reverse_X_sub_C {a : ℂ} (ha : a ≠ 0) :
    ((X - C a).reverse).roots = {a⁻¹} := by
  have hu : (-a) ≠ 0 := neg_ne_zero.mpr ha
  have hrev : (X - C a).reverse = C ((Units.mk0 (-a) hu : ℂˣ) : ℂ) * X + C 1 := by
    rw [Polynomial.reverse, natDegree_X_sub_C, sub_eq_add_neg, ← C_neg, reflect_add,
      reflect_one_X, reflect_C, pow_one, Units.val_mk0, C_1]
    ring
  rw [hrev, roots_C_mul_X_add_C_of_IsUnit, Multiset.singleton_inj, mul_one,
    Units.val_inv_eq_inv_val, Units.val_mk0, inv_neg, neg_neg]

open Polynomial in
private lemma roots_reverse_eq_map_inv {p : ℂ[X]} (hsp : p.Splits)
    (hm : p.Monic) (h0 : (0 : ℂ) ∉ p.roots) :
    p.reverse.roots = p.roots.map (·⁻¹) := by
  set R := p.roots with hR
  have key : ∀ a ∈ R, ((X - C a).reverse).roots = ({a⁻¹} : Multiset ℂ) :=
    fun a ha => roots_reverse_X_sub_C (fun h => h0 (h ▸ ha))
  have hfact : p = (R.map (fun a => X - C a)).prod := hsp.eq_prod_roots_of_monic hm
  rw [hfact, reverse_multiset_prod, Multiset.map_map, roots_multiset_prod,
    Multiset.bind_map]
  · simp only [Function.comp_apply]
    rw [Multiset.bind_congr (g := fun a => ({a⁻¹} : Multiset ℂ)) (fun a ha => key a ha),
      Multiset.bind_singleton]
  · simp only [Multiset.mem_map, Function.comp_apply, not_exists, not_and]
    exact fun a _ hcontra => X_sub_C_ne_zero a (Polynomial.reverse_eq_zero.mp hcontra)

open Polynomial Matrix in
private lemma matrix_trace_inv_eq_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {n : ℕ} (hn : 0 < n) (hpow : A ^ n = 1) :
    A⁻¹.trace = starRingEnd ℂ A.trace := by
  -- `A` is invertible since `A * A^(n-1) = 1` and `A^(n-1) * A = 1`.
  have hr : A * A ^ (n - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hn]; exact hpow
  have hl : A ^ (n - 1) * A = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn]; exact hpow
  have hunit : IsUnit A := ⟨⟨A, A ^ (n - 1), hr, hl⟩, rfl⟩
  -- `A.charpoly` is monic and splits over `ℂ`.
  have hmon : A.charpoly.Monic := A.charpoly_monic
  have hsplit : A.charpoly.Splits := IsAlgClosed.splits _
  -- No zero root: the product of the roots is `det A ≠ 0`.
  have hdet : A.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  have h0 : (0 : ℂ) ∉ A.charpoly.roots := by
    intro hmem
    have hprod : A.charpoly.roots.prod = 0 := Multiset.prod_eq_zero hmem
    rw [← Matrix.det_eq_prod_roots_charpoly A] at hprod
    exact hdet hprod
  -- Each root `λ` of the characteristic polynomial is a root of unity.
  have hroot : ∀ μ ∈ A.charpoly.roots, μ ^ n = 1 := by
    intro μ hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact (Polynomial.mem_roots'.mp hμ).2
    obtain ⟨v, hv_mem, hv0⟩ := hev.exists_hasEigenvector
    have hveq : Matrix.toLin' A v = μ • v := Module.End.mem_eigenspace_iff.mp hv_mem
    have key : ∀ k, (Matrix.toLin' A ^ k) v = μ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, Module.End.mul_apply, hveq, map_smul, ih, smul_smul, ← pow_succ']
    have hkey := key n
    rw [← Matrix.toLin'_pow, hpow, Matrix.toLin'_one, LinearMap.id_apply] at hkey
    have hsmul : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← hkey, sub_self]
    rcases smul_eq_zero.mp hsmul with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  -- Star of a root of unity is its inverse.
  have hstar : ∀ μ ∈ A.charpoly.roots, starRingEnd ℂ μ = μ⁻¹ := by
    intro μ hμ
    have hnorm : ‖μ‖ = 1 := by
      have h1 : ‖μ‖ ^ n = 1 := by rw [← norm_pow, hroot μ hμ, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1
    exact (Complex.inv_eq_conj hnorm).symm
  -- `tr(A⁻¹) = ∑ (roots A).map inv`.
  have hinvtr : A⁻¹.trace = (A.charpoly.roots.map (·⁻¹)).sum := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    have hcp : A⁻¹.charpoly =
        C ((-1) ^ Fintype.card ι * Ring.inverse A.det) * A.charpoly.reverse := by
      rw [Matrix.charpoly_inv A hunit, ← Matrix.reverse_charpoly,
        show ((-1 : ℂ[X]) ^ Fintype.card ι) = C ((-1 : ℂ) ^ Fintype.card ι) by
          rw [map_pow, map_neg, map_one], ← C_mul]
    have hc : (-1 : ℂ) ^ Fintype.card ι * Ring.inverse A.det ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero _ (by norm_num))
      rw [Ring.inverse_eq_inv]
      exact inv_ne_zero hdet
    rw [hcp, roots_C_mul _ hc, roots_reverse_eq_map_inv hsplit hmon h0]
  -- `conj(tr A) = ∑ conj(roots A) = ∑ (roots A).map inv`.
  rw [hinvtr, Matrix.trace_eq_sum_roots_charpoly, map_multiset_sum]
  exact congrArg Multiset.sum (Multiset.map_congr rfl (fun μ hμ => (hstar μ hμ).symm))

/-- The character of a complex representation at an inverse is the complex conjugate of its value. -/
theorem character_inv_eq_conj (ρ : Representation ℂ G V) (g : G) :
    Representation.character ρ g⁻¹ = starRingEnd ℂ (Representation.character ρ g) := by
  classical
  -- Pass to a matrix `A := [ρ g]` in a basis; then `[ρ g⁻¹] = A⁻¹` and `A` has finite order.
  let b := Module.finBasis ℂ V
  let E := LinearMap.toMatrixAlgEquiv b
  have hcg : Representation.character ρ g = (E (ρ g)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ b (ρ g)
  have hcgi : Representation.character ρ g⁻¹ = (E (ρ g⁻¹)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ b (ρ g⁻¹)
  have hpow : (E (ρ g)) ^ orderOf g = 1 := by
    rw [← map_pow, ← map_pow ρ, pow_orderOf_eq_one, map_one, map_one]
  have hinv : (E (ρ g))⁻¹ = E (ρ g⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, ← map_mul ρ, inv_mul_cancel, map_one, map_one]
  rw [hcg, hcgi, ← hinv]
  exact matrix_trace_inv_eq_conj (E (ρ g)) (orderOf_pos g) hpow

/-- The character of a complex representation is real-valued when every group element is conjugate to its inverse. -/
theorem character_im_eq_zero_of_isConj_inv
    (h : ∀ g : G, IsConj g g⁻¹) (ρ : Representation ℂ G V) (g : G) :
    (Representation.character ρ g).im = 0 := by
  -- Ambivalence: `χ(g⁻¹) = χ(g)` via conjugacy-invariance of the character.
  obtain ⟨c, hc⟩ := isConj_iff.mp (h g)
  have hconj : Representation.character ρ g⁻¹ = Representation.character ρ g := by
    rw [← hc]; exact Representation.char_conj ρ g c
  -- Combined with `χ(g⁻¹) = conj(χ(g))`: `χ(g)` is fixed by conjugation.
  rw [character_inv_eq_conj] at hconj
  exact Complex.conj_eq_iff_im.mp hconj


private theorem even_finrank_of_nondegenerate_alternating
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (halt : ∀ v, B v v = 0)
    (hnondeg : ∀ v, (∀ w, B v w = 0) → v = 0) :
    Even (Module.finrank ℂ V) := by
  -- Alternating ⟹ skew-symmetric: expand `B (v + w) (v + w) = 0`.
  have hskew : ∀ v w, B v w = - B w v := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt] at h
    linear_combination h
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  -- Work with the Gram matrix `M` of `B` in the canonical finite basis.
  set b := Module.finBasis ℂ V with hb
  set M := LinearMap.BilinForm.toMatrix b B with hM
  -- Nondegeneracy is literally the hypothesis, so `det M ≠ 0`.
  have hnd : LinearMap.BilinForm.Nondegenerate B := by
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    exact hnondeg m (fun w => by rw [hm]; simp)
  have hdet_ne : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  -- Skew-symmetry of `B` makes `M` skew-symmetric.
  have htrans : M.transpose = -M := by
    ext i j
    simp only [hM, Matrix.transpose_apply, Matrix.neg_apply, LinearMap.BilinForm.toMatrix_apply]
    exact hskew (b j) (b i)
  -- `det M = (-1)ⁿ det M`, and `n` odd forces `det M = 0`.
  have h1 : M.det = (-1) ^ Module.finrank ℂ V * M.det := by
    conv_lhs => rw [← Matrix.det_transpose M, htrans, Matrix.det_neg]
    simp [Fintype.card_fin]
  rw [hne.neg_one_pow] at h1
  exact hdet_ne (by linear_combination (1 / 2 : ℂ) * h1)

/-- Under an auxiliary condition on a complex representation, its dimension is even. -/
@[source_ref "Chapter5/Discussion_after_Definition5.1.1" (role := primary)]
theorem even_finrank_of_auxiliary
    (ρ : Representation ℂ G V) (h : RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ) :
    Even (Module.finrank ℂ V) := by
  obtain ⟨B, hskew, hnondeg, _⟩ := h
  refine even_finrank_of_nondegenerate_alternating B (fun v => ?_) hnondeg
  -- `B v v = -(B v v)` in characteristic `0` forces `B v v = 0`.
  have e : B v v = -(B v v) := hskew v v
  have h2 : (2 : ℂ) * B v v = 0 := by linear_combination e
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)


/-- An irreducible complex representation whose character agrees at inverses admits a nonzero invariant bilinear form. -/
theorem exists_ne_zero_invariant_bilinear_form_of_character_inv_eq
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hsd : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g) :
    ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, B ≠ 0 ∧ (∀ g v w, B (ρ g v) (ρ g w) = B v w) := by
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  haveI : Nonempty G := ⟨1⟩
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.card_pos.ne')
  -- `finrank` of the invariant bilinear forms, cast to `ℂ`, equals `1`.
  have hkey := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom ρ ρ.dual)
  have hortho := Representation.char_orthonormal ρ ρ
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
  have hchar : ∀ g, (Representation.linHom ρ ρ.dual).character g
      = ρ.character g * ρ.character g⁻¹ := fun g => by
    rw [Representation.char_linHom, Representation.char_dual, hsd g]
  rw [Finset.sum_congr rfl (fun g _ => hchar g), hortho] at hkey
  have hfr : (Module.finrank ℂ ((Representation.linHom ρ ρ.dual).invariants) : ℂ) = 1 :=
    hkey.symm
  have hpos : 0 < Module.finrank ℂ ((Representation.linHom ρ ρ.dual).invariants) := by
    rw [Nat.pos_iff_ne_zero]; intro h0; rw [h0] at hfr; norm_num at hfr
  -- positive `finrank` ⟹ a nonzero invariant element ⟹ a nonzero invariant bilinear form.
  haveI : Nontrivial ((Representation.linHom ρ ρ.dual).invariants) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx0⟩ := exists_ne (0 : (Representation.linHom ρ ρ.dual).invariants)
  refine ⟨x.1, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  intro g v w
  have hmem : (Representation.linHom ρ ρ.dual) g⁻¹ x.1 = x.1 := x.2 g⁻¹
  have h1 := LinearMap.congr_fun (LinearMap.congr_fun hmem v) w
  simpa [Representation.linHom_apply, Representation.dual_apply,
    Module.Dual.transpose_apply] using h1

/-- For an irreducible complex representation whose character agrees at inverses, one of two auxiliary alternatives holds. -/
theorem auxiliary_property_or_auxiliary_condition_of_character_inv_eq
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hsd : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ ∨ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ := by
  obtain ⟨B, hBne, hBinv⟩ := exists_ne_zero_invariant_bilinear_form_of_character_inv_eq ρ hρ hsd
  have hflipinv : ∀ g v w, B.flip (ρ g v) (ρ g w) = B.flip v w := fun g v w => by
    simp only [LinearMap.flip_apply]; exact hBinv g w v
  by_cases hS : B + B.flip = 0
  · -- `B` itself is skew-symmetric, nonzero, invariant ⟹ quaternionic type.
    refine Or.inr ⟨B, ?_, invariant_bilinear_form_left_nondegenerate ρ hρ B hBne hBinv, hBinv⟩
    intro v w
    have h := LinearMap.congr_fun (LinearMap.congr_fun hS v) w
    simp only [LinearMap.add_apply, LinearMap.zero_apply, LinearMap.flip_apply] at h
    linear_combination h
  · -- the symmetric part `B + Bᵀ` is nonzero, invariant ⟹ real type.
    refine Or.inl ⟨B + B.flip, fun v w => ?_,
      invariant_bilinear_form_left_nondegenerate ρ hρ _ hS (fun g v w => ?_), fun g v w => ?_⟩
    · simp only [LinearMap.add_apply, LinearMap.flip_apply]; ring
    · simp only [LinearMap.add_apply]; rw [hBinv, hflipinv]
    · simp only [LinearMap.add_apply]; rw [hBinv, hflipinv]

/-- An odd-dimensional irreducible complex representation whose character agrees at inverses has an auxiliary property. -/
theorem auxiliary_property_of_odd_finrank_and_character_inv_eq
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hsd : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g)
    (hodd : Odd (Module.finrank ℂ V)) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  rcases auxiliary_property_or_auxiliary_condition_of_character_inv_eq ρ hρ hsd with h | h
  · exact h
  · exact absurd (even_finrank_of_auxiliary ρ h)
      (by rw [Nat.not_even_iff_odd]; exact hodd)

end RepresentationTheory.Representation.Character.InversionAndInvariantForms
