/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity
import RepresentationTheory.Alignment.Attribute

/-! # Tensor-product simplicity and factorization -/

namespace RepresentationTheory.Algebra.Module.TensorProductSimplicity

section Part1

open scoped TensorProduct

variable {k : Type*} {V W : Type*}
  [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [FiniteDimensional k V] [FiniteDimensional k W] in

private theorem map_smulRight_smulRight_eq
    (φ : V →ₗ[k] k) (ψ : W →ₗ[k] k) (v₀ : V) (w₀ : W) (t : V ⊗[k] W) :
    TensorProduct.map (φ.smulRight v₀) (ψ.smulRight w₀) t =
      TensorProduct.lid k k (TensorProduct.map φ ψ t) • (v₀ ⊗ₜ[k] w₀) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.smulRight_apply, TensorProduct.lid_tmul,
      smul_eq_mul, TensorProduct.smul_tmul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_smul]

private theorem pure_tensors_mem_of_stable
    (U : Submodule k (V ⊗[k] W))
    (hU_end : ∀ (f : Module.End k V) (g : Module.End k W) (x : V ⊗[k] W),
        x ∈ U → TensorProduct.map f g x ∈ U)
    {u : V ⊗[k] W} (hu : u ∈ U) (hu_ne : u ≠ 0)
    (v : V) (w : W) : v ⊗ₜ[k] w ∈ U := by
  classical

  let bV := Module.finBasis k V
  let coeffs := TensorProduct.equivFinsuppOfBasisLeft bV u

  have hcoeffs_ne : coeffs ≠ 0 := by
    intro h
    apply hu_ne
    have : u = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply u).symm
    rw [this, h, map_zero]
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hcoeffs_ne
  simp only [Finsupp.zero_apply] at hi₀

  set w₀ := coeffs i₀ with hw₀_def

  let bW := Module.finBasis k W
  have hw₀_ne : w₀ ≠ 0 := hi₀
  have hrepr_ne : bW.repr w₀ ≠ 0 :=
    fun h => hw₀_ne (bW.repr.injective (show _ = _ by simp [h]))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp hrepr_ne
  simp only [Finsupp.zero_apply] at hj₀

  have h_mem : TensorProduct.map ((bV.coord i₀).smulRight v) ((bW.coord j₀).smulRight w) u ∈ U :=
    hU_end _ _ u hu
  rw [map_smulRight_smulRight_eq] at h_mem

  set c := TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u)

  have hc_ne : c ≠ 0 := by

    suffices hc_eq : c = (bW.repr w₀) j₀ by rw [hc_eq]; exact hj₀

    have hu_decomp : u = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply u).symm

    change TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u) = _
    rw [hu_decomp, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]

    rw [Finsupp.sum]
    simp only [map_sum, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

    rw [Finset.sum_eq_single i₀]
    · simp [hw₀_def]
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finsupp.mem_support_iff.mpr hi₀) h

  have := U.smul_mem c⁻¹ h_mem
  rwa [inv_smul_smul₀ hc_ne] at this

end Part1

open TensorProduct in

/-- A submodule stable under the displayed tensor-factor actions is bottom or top. -/
@[source_ref "Chapter3/Theorem3.10.2" (role := primary),
  source_ref "Chapter3/Discussion_proof_of_Theorem3.10.2" (role := supporting),
  source_ref "Chapter5/Theorem5.6.1" (role := supporting)]
theorem submodule_eq_bot_or_top_of_tensorActions (k : Type*) (A B V W : Type*)
    [Field k] [IsAlgClosed k]
    [Ring A] [Algebra k A]
    [Ring B] [Algebra k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule B W] :
    ∀ (U : Submodule k (V ⊗[k] W)),
      (∀ (a : A) (b : B) (x : V ⊗[k] W), x ∈ U →
        TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a)
          ((Algebra.lsmul k k W : B →ₐ[k] Module.End k W) b) x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨u, hu, hu_ne⟩ := U.ne_bot_iff.mp hbot

    have hdens_A := RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.algebra_smul_surjective k A V
    have hdens_B := RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.algebra_smul_surjective k B W

    have hU_end : ∀ (f : Module.End k V) (g : Module.End k W) (x : V ⊗[k] W),
        x ∈ U → TensorProduct.map f g x ∈ U := by
      intro f g x hx
      obtain ⟨a, ha⟩ := hdens_A f
      obtain ⟨b, hb⟩ := hdens_B g
      rw [← ha, ← hb]
      exact hU a b x hx

    rw [eq_top_iff]
    intro x _

    have := span_tmul_eq_top k V W
    rw [eq_top_iff] at this
    have hx := this (Submodule.mem_top : x ∈ ⊤)

    refine Submodule.span_le.mpr ?_ hx
    intro t ht
    obtain ⟨v, w, rfl⟩ := ht
    exact pure_tensors_mem_of_stable U hU_end hu hu_ne v w

section Part2Helpers

open scoped TensorProduct

variable {k : Type*} {A B : Type*} [Field k] [IsAlgClosed k]
  [Ring A] [Algebra k A]
  [Ring B] [Algebra k B]

variable {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [Module A M] [IsScalarTower k A M]
  [Module B M] [IsScalarTower k B M]
  [SMulCommClass A B M]

variable (V₀ : Submodule A M)

/-- A linear map evaluating a pure tensor of a submodule element and a linear map at that element. -/
noncomputable def evaluationTensorLinearMap : V₀ ⊗[k] (V₀ →ₗ[A] M) →ₗ[k] M :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun f => f v
          map_add' := fun _ _ => rfl
          map_smul' := fun c f => by
            change (c • f) v = c • f v
            rfl }
      map_add' := fun v₁ v₂ => by ext f; exact f.map_add v₁ v₂
      map_smul' := fun c v => by
        ext f; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        change f (c • v) = c • f v

        have h1 : f ((algebraMap k A c) • v) = (algebraMap k A c) • f v := f.map_smul _ _
        rwa [algebraMap_smul, algebraMap_smul] at h1 }

omit [IsAlgClosed k] [FiniteDimensional k M] in
/-- The evaluation tensor map sends a pure tensor to the displayed evaluation. -/
@[simp]
theorem evaluationTensorLinearMap_tmul (v : V₀) (f : V₀ →ₗ[A] M) :
    evaluationTensorLinearMap V₀ (v ⊗ₜ[k] f) = f v := by
  simp [evaluationTensorLinearMap]

end Part2Helpers

open TensorProduct in

/-- Under the displayed simplicity hypothesis, the formal signature provides the stated factorization data. -/
@[source_ref "Chapter3/Theorem3.10.2" (role := supporting),
  source_ref "Chapter3/Discussion_proof_of_Theorem3.10.2" (role := primary),
  source_ref "Chapter5/Theorem5.6.1" (role := supporting)]
theorem exists_tensorFactorization_of_simpleBimodule.{u}
    (k : Type*) (A B : Type*)
    (M : Type u)
    [Field k] [IsAlgClosed k]
    [Ring A] [Algebra k A]
    [Ring B] [Algebra k B]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module A M] [IsScalarTower k A M]
    [Module B M] [IsScalarTower k B M]
    [SMulCommClass A B M]
    [Nontrivial M]
    (hM : ∀ (U : Submodule k M),
      (∀ (a : A) (x : M), x ∈ U → a • x ∈ U) →
      (∀ (b : B) (x : M), x ∈ U → b • x ∈ U) →
      U = ⊥ ∨ U = ⊤) :
    ∃ (V : Type u) (W : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module A V)
      (_ : IsScalarTower k A V) (_ : FiniteDimensional k V) (_ : IsSimpleModule A V)
      (_ : AddCommGroup W) (_ : Module k W) (_ : Module B W)
      (_ : IsScalarTower k B W) (_ : FiniteDimensional k W) (_ : IsSimpleModule B W)
      (e : M ≃ₗ[k] V ⊗[k] W),
      (∀ (a : A) (m : M),
        e (a • m) = TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id (e m)) ∧
      (∀ (b : B) (m : M),
        e (b • m) = TensorProduct.map LinearMap.id ((Algebra.lsmul k k W : B →ₐ[k] _) b) (e m)) := by

  haveI : IsArtinian A M := isArtinian_of_tower k (inferInstance : IsArtinian k M)
  have hM_ne : (⊤ : Submodule A M) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx (congr_arg (x ∈ ·) h |>.mp Submodule.mem_top)
  haveI hatomic : IsAtomic (Submodule A M) :=
    isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨V₀, hV₀_atom, _⟩ :=
    (hatomic.eq_bot_or_exists_atom_le (⊤ : Submodule A M)).resolve_left hM_ne
  haveI : IsSimpleModule A V₀ := isSimpleModule_iff_isAtom.mpr hV₀_atom
  haveI : FiniteDimensional k V₀ := by
    have : Module.Finite k (V₀.restrictScalars k) := inferInstance
    exact this

  have hι_ne : (V₀.subtype.restrictScalars A : (V₀ →ₗ[A] M)) ≠ 0 := by
    intro h
    have hzero : ∀ v : V₀, (v : M) = 0 := fun v => LinearMap.congr_fun h v
    exact hV₀_atom.1 (eq_bot_iff.mpr fun x hx => hzero ⟨x, hx⟩)

  have hev_surj : Function.Surjective (evaluationTensorLinearMap V₀ : V₀ ⊗[k] (V₀ →ₗ[A] M) →ₗ[k] M) := by
    rw [← LinearMap.range_eq_top]
    set evR := LinearMap.range (evaluationTensorLinearMap V₀ : V₀ ⊗[k] (V₀ →ₗ[A] M) →ₗ[k] M)
    have hA_inv : ∀ (a : A) (x : M), x ∈ evR → a • x ∈ evR := by
      rintro a _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul v f =>
        exact ⟨(a • v) ⊗ₜ[k] f, by simp [evaluationTensorLinearMap_tmul, f.map_smul]⟩
      | add _ _ hx hy =>
        rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
    have hB_inv : ∀ (b : B) (x : M), x ∈ evR → b • x ∈ evR := by
      rintro b _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul v f => exact ⟨v ⊗ₜ[k] (b • f), by simp [evaluationTensorLinearMap_tmul, LinearMap.smul_apply]⟩
      | add _ _ hx hy =>
        rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
    have hne : evR ≠ ⊥ := by
      intro h
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₀_atom.1
      have : (v : M) ∈ evR :=
        ⟨⟨v, hv_mem⟩ ⊗ₜ[k] V₀.subtype.restrictScalars A, by simp [evaluationTensorLinearMap_tmul]⟩
      rw [h, Submodule.mem_bot] at this; exact hv_ne this
    exact (hM evR hA_inv hB_inv).resolve_left hne

  have hev_inj : Function.Injective (evaluationTensorLinearMap V₀ : V₀ ⊗[k] (V₀ →ₗ[A] M) →ₗ[k] M) := by

    have hequi : ∀ (a : A) (s : V₀ ⊗[k] (V₀ →ₗ[A] M)),
        evaluationTensorLinearMap V₀ (TensorProduct.map ((Algebra.lsmul k k V₀ : A →ₐ[k] _) a)
          LinearMap.id s) = a • evaluationTensorLinearMap V₀ s := by
      intro a s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul v f =>
        rw [TensorProduct.map_tmul, LinearMap.id_apply, evaluationTensorLinearMap_tmul, evaluationTensorLinearMap_tmul]
        simp only [Algebra.lsmul_coe]
        exact f.map_smul a v
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]

    have hstable : ∀ (φ : Module.End k V₀) (s : V₀ ⊗[k] (V₀ →ₗ[A] M)),
        evaluationTensorLinearMap V₀ s = 0 → evaluationTensorLinearMap V₀ (TensorProduct.map φ LinearMap.id s) = 0 := by
      intro φ s hs
      obtain ⟨a, ha⟩ := RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.algebra_smul_surjective k A V₀ φ
      rw [← ha, hequi, hs, smul_zero]

    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    obtain ⟨t, ht_mem, ht_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker] at ht_mem

    let bV := Module.finBasis k V₀
    have ht_ne' : TensorProduct.equivFinsuppOfBasisLeft bV t ≠ 0 := by
      intro h; exact ht_ne ((TensorProduct.equivFinsuppOfBasisLeft bV).injective
        (show _ = _ by rw [h, map_zero]))
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp ht_ne'
    simp only [Finsupp.zero_apply] at hj

    obtain ⟨v, hv⟩ : ∃ v, (TensorProduct.equivFinsuppOfBasisLeft bV t) j v ≠ 0 := by
      by_contra h; push Not at h
      exact hj (LinearMap.ext fun v => by simpa using h v)

    let φ : Module.End k V₀ := bV.constr k (fun i => if i = j then v else 0)
    have hφ : ∀ i, φ (bV i) = if i = j then v else 0 :=
      fun i => bV.constr_basis k _ i

    have hzero := hstable φ t ht_mem

    have ht_eq : t = Finsupp.sum (TensorProduct.equivFinsuppOfBasisLeft bV t)
        (fun i w => bV i ⊗ₜ[k] w) := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
          LinearEquiv.symm_apply_apply]
    rw [ht_eq] at hzero
    simp only [Finsupp.sum, map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      evaluationTensorLinearMap_tmul] at hzero

    simp only [hφ] at hzero
    rw [Finset.sum_eq_single j] at hzero
    · simp at hzero; exact hv hzero
    · intro i _ hi; simp [hi]
    · intro hj_mem
      exfalso; exact hj_mem (Finsupp.mem_support_iff.mpr (by intro h; exact hj h))
  set ev_equiv : V₀ ⊗[k] (V₀ →ₗ[A] M) ≃ₗ[k] M :=
    LinearEquiv.ofBijective (evaluationTensorLinearMap V₀) ⟨hev_inj, hev_surj⟩ with hev_def
  have ev_apply : ∀ x, ev_equiv x = evaluationTensorLinearMap V₀ x := by
    intro x; rw [hev_def, LinearEquiv.ofBijective_apply]

  have hAeq : ∀ (a : A) (s : V₀ ⊗[k] (V₀ →ₗ[A] M)),
      evaluationTensorLinearMap V₀ (TensorProduct.map ((Algebra.lsmul k k V₀ : A →ₐ[k] _) a) LinearMap.id s)
        = a • evaluationTensorLinearMap V₀ s := by
    intro a s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, evaluationTensorLinearMap_tmul, evaluationTensorLinearMap_tmul]
      simp only [Algebra.lsmul_coe]
      exact f.map_smul a v
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  have hBeq : ∀ (b : B) (s : V₀ ⊗[k] (V₀ →ₗ[A] M)),
      evaluationTensorLinearMap V₀ (TensorProduct.map LinearMap.id ((Algebra.lsmul k k (V₀ →ₗ[A] M) : B →ₐ[k] _) b) s)
        = b • evaluationTensorLinearMap V₀ s := by
    intro b s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, evaluationTensorLinearMap_tmul, evaluationTensorLinearMap_tmul]
      simp only [Algebra.lsmul_coe]
      rfl
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]

  haveI : FiniteDimensional k (V₀ →ₗ[A] M) := by

    let ι : (V₀ →ₗ[A] M) →ₗ[k] (V₀ →ₗ[k] M) :=
      { toFun := fun f => f.restrictScalars k
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => by
          ext v; change (c • f) v = c • f v; rfl }
    exact Module.Finite.of_injective ι (fun f g h => by
      ext v; exact LinearMap.congr_fun h v)

  haveI : IsSimpleModule B (V₀ →ₗ[A] M) := by
    haveI : Nontrivial (V₀ →ₗ[A] M) :=
      ⟨⟨0, V₀.subtype.restrictScalars A, hι_ne.symm⟩⟩
    have hsimple : ∀ S : Submodule B (V₀ →ₗ[A] M), S = ⊥ ∨ S = ⊤ := by
      intro S
      by_contra hS
      push Not at hS
      obtain ⟨hS_ne_bot, hS_ne_top⟩ := hS

      obtain ⟨f, hf_mem, hf_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS_ne_bot

      obtain ⟨v, hv⟩ : ∃ v, (f : (V₀ →ₗ[A] M)) v ≠ 0 := by
        by_contra h; push Not at h
        exact hf_ne (LinearMap.ext fun v => by simpa using h v)

      let incl : S →ₗ[k] (V₀ →ₗ[A] M) := S.subtype.restrictScalars k
      set evS : V₀ ⊗[k] S →ₗ[k] M :=
        (evaluationTensorLinearMap V₀).comp (TensorProduct.map LinearMap.id incl) with hevS_def
      have hevS_tmul : ∀ (v' : V₀) (g : S), evS (v' ⊗ₜ[k] g) = (g : (V₀ →ₗ[A] M)) v' := by
        intro v' g; simp only [hevS_def, LinearMap.comp_apply, TensorProduct.map_tmul,
          LinearMap.id_apply, evaluationTensorLinearMap_tmul]; rfl
      have hevS_surj : Function.Surjective evS := by
        rw [← LinearMap.range_eq_top]
        set R := LinearMap.range evS
        have hR_A : ∀ (a : A) (x : M), x ∈ R → a • x ∈ R := by
          rintro a _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul v' g =>
            rw [hevS_tmul]; exact ⟨(a • v') ⊗ₜ[k] g, by rw [hevS_tmul, (g : (V₀ →ₗ[A] M)).map_smul]⟩
          | add _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
        have hR_B : ∀ (b : B) (x : M), x ∈ R → b • x ∈ R := by
          rintro b _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul v' g =>
            rw [hevS_tmul]
            refine ⟨v' ⊗ₜ[k] ⟨b • (g : (V₀ →ₗ[A] M)), S.smul_mem b g.2⟩, ?_⟩
            rw [hevS_tmul]; rfl
          | add _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
        have hR_ne : R ≠ ⊥ := by
          intro h
          have : evS (v ⊗ₜ[k] ⟨f, hf_mem⟩) ∈ R := LinearMap.mem_range_self evS _
          rw [h, Submodule.mem_bot] at this
          rw [hevS_tmul] at this
          exact hv this
        exact (hM R hR_A hR_B).resolve_left hR_ne

      haveI : FiniteDimensional k S :=
        Module.Finite.of_injective incl Subtype.val_injective

      have h1 : Module.finrank k M ≤ Module.finrank k V₀ * Module.finrank k S := by
        rw [← Module.finrank_tensorProduct]
        calc Module.finrank k M
            = Module.finrank k (LinearMap.range evS) + 0 := by
              rw [LinearMap.range_eq_top.mpr hevS_surj]; simp
          _ ≤ Module.finrank k (LinearMap.range evS) +
              Module.finrank k (LinearMap.ker evS) := by omega
          _ = _ := evS.finrank_range_add_finrank_ker
      have h2 : Module.finrank k M = Module.finrank k V₀ * Module.finrank k (V₀ →ₗ[A] M) := by
        rw [← Module.finrank_tensorProduct, ev_equiv.finrank_eq]
      haveI : Nontrivial V₀ := by
        obtain ⟨x, hx, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₀_atom.1
        exact ⟨⟨⟨x, hx⟩, 0, fun h => hx_ne (congr_arg Subtype.val h)⟩⟩
      have hV₀_pos : 0 < Module.finrank k V₀ := Module.finrank_pos
      have h3 : Module.finrank k (V₀ →ₗ[A] M) ≤ Module.finrank k S := by
        exact Nat.le_of_mul_le_mul_left (h2 ▸ h1) hV₀_pos
      have h4 : Module.finrank k S ≤ Module.finrank k (V₀ →ₗ[A] M) :=
        Submodule.finrank_le (S.restrictScalars k)
      have hS_k_top : S.restrictScalars k = ⊤ :=
        Submodule.eq_top_of_finrank_eq
          (show Module.finrank k (S.restrictScalars k) = _ from le_antisymm h4 h3)
      exact hS_ne_top (eq_top_iff.mpr fun x _ => by
        have : x ∈ (S.restrictScalars k : Set (V₀ →ₗ[A] M)) := by rw [hS_k_top]; trivial
        exact this)
    exact { toIsSimpleOrder := { eq_bot_or_eq_top := hsimple } }
  refine ⟨↥V₀, (V₀ →ₗ[A] M), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ev_equiv.symm, ?_, ?_⟩
  ·
    intro a m
    apply ev_equiv.injective
    rw [LinearEquiv.apply_symm_apply, ev_apply, hAeq]
    have hsm : evaluationTensorLinearMap V₀ (ev_equiv.symm m) = m := by
      rw [← ev_apply]; exact ev_equiv.apply_symm_apply m
    rw [hsm]
  ·
    intro b m
    apply ev_equiv.injective
    rw [LinearEquiv.apply_symm_apply, ev_apply, hBeq]
    have hsm : evaluationTensorLinearMap V₀ (ev_equiv.symm m) = m := by
      rw [← ev_apply]; exact ev_equiv.apply_symm_apply m
    rw [hsm]

section Part3Helpers

open scoped TensorProduct

private theorem exists_functional_ne_zero {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {v : V} (hv : v ≠ 0) :
    ∃ φ : V →ₗ[k] k, φ v ≠ 0 := by
  classical
  let bV := Module.finBasis k V
  have hrepr : bV.repr v ≠ 0 := fun h => hv (bV.repr.injective (by simp [h]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr
  simp only [Finsupp.zero_apply] at hi
  exact ⟨bV.coord i, by simpa [Module.Basis.coord_apply] using hi⟩

private theorem tmul_ne_zero {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[k] w ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_functional_ne_zero (k := k) hv
  obtain ⟨ψ, hψ⟩ := exists_functional_ne_zero (k := k) hw
  intro h
  apply mul_ne_zero hφ hψ
  have := congrArg (fun z => TensorProduct.lid k k (TensorProduct.map φ ψ z)) h
  simpa [TensorProduct.map_tmul, TensorProduct.lid_tmul] using this

private theorem exists_contraction_ne_zero {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {t : V ⊗[k] W} (ht : t ≠ 0) :
    ∃ (φ : V →ₗ[k] k) (ψ : W →ₗ[k] k),
      TensorProduct.lid k k (TensorProduct.map φ ψ t) ≠ 0 := by
  classical
  let bV := Module.finBasis k V
  let coeffs := TensorProduct.equivFinsuppOfBasisLeft bV t
  have hcoeffs_ne : coeffs ≠ 0 := by
    intro h
    apply ht
    have : t = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply t).symm
    rw [this, h, map_zero]
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hcoeffs_ne
  simp only [Finsupp.zero_apply] at hi₀
  set w₀ := coeffs i₀ with hw₀_def
  let bW := Module.finBasis k W
  have hrepr_ne : bW.repr w₀ ≠ 0 :=
    fun h => hi₀ (bW.repr.injective (by simp [h]))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp hrepr_ne
  simp only [Finsupp.zero_apply] at hj₀
  refine ⟨bV.coord i₀, bW.coord j₀, ?_⟩
  suffices hc : TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) t)
      = (bW.repr w₀) j₀ by rw [hc]; exact hj₀
  have hu_decomp : t = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
    ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply t).symm
  conv_lhs => rw [hu_decomp]
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum]
  simp only [map_sum, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i₀]
  · simp [hw₀_def]
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finsupp.mem_support_iff.mpr hi₀) h

private theorem lid_map_eq_apply_rid {k V' W' : Type*} [Field k]
    [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    (φ : V' →ₗ[k] k) (ψ : W' →ₗ[k] k) (z : V' ⊗[k] W') :
    φ ((TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ z))
      = TensorProduct.lid k k (TensorProduct.map φ ψ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v' w' =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul,
      map_smul, smul_eq_mul, TensorProduct.lid_tmul]
    ring
  | add x y hx hy => simp [map_add, hx, hy]

private theorem rid_mapψ_lsmul {k A V' W' : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V'] [Module k V'] [Module A V'] [IsScalarTower k A V']
    [AddCommGroup W'] [Module k W']
    (ψ : W' →ₗ[k] k) (a : A) (z : V' ⊗[k] W') :
    (TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ
        (TensorProduct.map ((Algebra.lsmul k k V' : A →ₐ[k] _) a) LinearMap.id z))
      = a • (TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v' w' =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, Algebra.lsmul_coe,
      TensorProduct.rid_tmul]
    exact smul_comm (ψ w') a v'
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

end Part3Helpers

open scoped TensorProduct in

/-- A tensor-product equivalence respecting the displayed left action induces an equivalence of the left module factors. -/
theorem nonempty_linearEquiv_of_tensorEquiv_left
    {k A V W V' W' : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]
    [AddCommGroup V'] [Module k V'] [Module A V'] [IsScalarTower k A V'] [FiniteDimensional k V']
    [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    [IsSimpleModule A V] [IsSimpleModule A V']
    (e : V ⊗[k] W ≃ₗ[k] V' ⊗[k] W')
    (hA : ∀ (a : A) (x : V ⊗[k] W),
        e (TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id x)
          = TensorProduct.map ((Algebra.lsmul k k V' : A →ₐ[k] _) a) LinearMap.id (e x)) :
    Nonempty (V ≃ₗ[A] V') := by
  classical
  haveI := IsSimpleModule.nontrivial A V
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)

  let T : (W' →ₗ[k] k) → (V →ₗ[A] V') := fun ψ =>
    { toFun := fun v =>
        (TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ (e (v ⊗ₜ[k] w₀)))
      map_add' := fun x y => by simp only [TensorProduct.add_tmul, map_add]
      map_smul' := fun a v => by
        simp only [RingHom.id_apply]
        have hsmul : (a • v) ⊗ₜ[k] w₀
            = TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id (v ⊗ₜ[k] w₀) := by
          rw [TensorProduct.map_tmul]; simp [Algebra.lsmul_coe]
        rw [hsmul, hA, rid_mapψ_lsmul] }

  have hex : ∃ ψ : W' →ₗ[k] k, T ψ ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)
    have ht : e (v₁ ⊗ₜ[k] w₀) ≠ 0 :=
      fun hz => tmul_ne_zero hv₁ hw₀ (e.injective (hz.trans (map_zero e).symm))
    obtain ⟨φ, ψ, hφψ⟩ := exists_contraction_ne_zero ht
    apply hφψ
    have hTψ : (TensorProduct.rid k V')
        (TensorProduct.map LinearMap.id ψ (e (v₁ ⊗ₜ[k] w₀))) = 0 := by
      calc (TensorProduct.rid k V')
              (TensorProduct.map LinearMap.id ψ (e (v₁ ⊗ₜ[k] w₀)))
          = T ψ v₁ := rfl
        _ = (0 : V →ₗ[A] V') v₁ := by rw [h ψ]
        _ = 0 := rfl
    calc TensorProduct.lid k k (TensorProduct.map φ ψ (e (v₁ ⊗ₜ[k] w₀)))
        = φ ((TensorProduct.rid k V')
            (TensorProduct.map LinearMap.id ψ (e (v₁ ⊗ₜ[k] w₀)))) :=
          (lid_map_eq_apply_rid φ ψ _).symm
      _ = φ 0 := by rw [hTψ]
      _ = 0 := map_zero φ
  obtain ⟨ψ, hψ⟩ := hex
  exact ⟨LinearEquiv.ofBijective (T ψ) (LinearMap.bijective_of_ne_zero hψ)⟩

open scoped TensorProduct in

private theorem comm_map_apply {k M N M' N' : Type*} [CommSemiring k]
    [AddCommMonoid M] [Module k M] [AddCommMonoid N] [Module k N]
    [AddCommMonoid M'] [Module k M'] [AddCommMonoid N'] [Module k N']
    (f : M →ₗ[k] M') (g : N →ₗ[k] N') (x : M ⊗[k] N) :
    (TensorProduct.comm k M' N') (TensorProduct.map f g x)
      = TensorProduct.map g f ((TensorProduct.comm k M N) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.map_tmul, TensorProduct.comm_tmul]
  | add p q hp hq => simp [map_add, hp, hq]

open scoped TensorProduct in

/-- A tensor-product equivalence respecting both displayed factor actions induces equivalences of both factors. -/
@[source_ref "Chapter3/Theorem3.10.2" (role := primary),
  source_ref "Chapter3/Discussion_proof_of_Theorem3.10.2" (role := primary)]
theorem nonempty_linearEquiv_factors_of_tensorEquiv
    {k A B V W V' W' : Type*} [Field k]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W] [FiniteDimensional k W]
    [AddCommGroup V'] [Module k V'] [Module A V'] [IsScalarTower k A V'] [FiniteDimensional k V']
    [AddCommGroup W'] [Module k W'] [Module B W'] [IsScalarTower k B W'] [FiniteDimensional k W']
    [IsSimpleModule A V] [IsSimpleModule A V'] [IsSimpleModule B W] [IsSimpleModule B W']
    (e : V ⊗[k] W ≃ₗ[k] V' ⊗[k] W')
    (hA : ∀ (a : A) (x : V ⊗[k] W),
        e (TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id x)
          = TensorProduct.map ((Algebra.lsmul k k V' : A →ₐ[k] _) a) LinearMap.id (e x))
    (hB : ∀ (b : B) (x : V ⊗[k] W),
        e (TensorProduct.map LinearMap.id ((Algebra.lsmul k k W : B →ₐ[k] _) b) x)
          = TensorProduct.map LinearMap.id ((Algebra.lsmul k k W' : B →ₐ[k] _) b) (e x)) :
    Nonempty (V ≃ₗ[A] V') ∧ Nonempty (W ≃ₗ[B] W') := by
  haveI := IsSimpleModule.nontrivial A V
  haveI := IsSimpleModule.nontrivial B W
  refine ⟨nonempty_linearEquiv_of_tensorEquiv_left e hA, ?_⟩

  let ê : W ⊗[k] V ≃ₗ[k] W' ⊗[k] V' :=
    (TensorProduct.comm k W V).trans (e.trans (TensorProduct.comm k V' W'))
  refine nonempty_linearEquiv_of_tensorEquiv_left (A := B) (V := W) (W := V) (V' := W') (W' := V') ê ?_
  intro b x
  change (TensorProduct.comm k V' W') (e ((TensorProduct.comm k W V)
        (TensorProduct.map ((Algebra.lsmul k k W : B →ₐ[k] _) b) LinearMap.id x)))
      = TensorProduct.map ((Algebra.lsmul k k W' : B →ₐ[k] _) b) LinearMap.id
          ((TensorProduct.comm k V' W') (e ((TensorProduct.comm k W V) x)))
  rw [comm_map_apply, hB, comm_map_apply]

section InfiniteDimensionalRegression

open Polynomial

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- A module structure of a polynomial algebra on its base field. -/
noncomputable local instance polynomialModule : Module k[X] k :=
  Module.compHom k ((aeval (0 : k)).toRingHom)

/-- The displayed action of a polynomial algebra on its base field forms a scalar tower. -/
local instance polynomial_scalarTower : IsScalarTower k k[X] k where
  smul_assoc c p x := by
    change aeval (0 : k) (c • p) * x = c • (aeval (0 : k) p * x)
    rw [map_smul]
    exact smul_mul_assoc c (aeval (0 : k) p) x

/-- The displayed polynomial algebra actions on the base field commute. -/
local instance polynomial_smulCommClass : SMulCommClass k[X] k[X] k where
  smul_comm p q x := by
    change aeval (0 : k) p * (aeval (0 : k) q * x) = aeval (0 : k) q * (aeval (0 : k) p * x)
    ring

/-- The base field is a simple module over the displayed polynomial algebra. -/
local instance polynomial_isSimpleModule : IsSimpleModule k[X] k :=
  { toIsSimpleOrder :=
    { eq_bot_or_eq_top := fun N => by
        rcases eq_bot_or_eq_top (N.restrictScalars k) with h | h
        · refine Or.inl (Submodule.restrictScalars_injective k k[X] k ?_)
          rw [Submodule.restrictScalars_bot]; exact h
        · refine Or.inr (Submodule.restrictScalars_injective k k[X] k ?_)
          rw [Submodule.restrictScalars_top]; exact h } }

example : True := by
  have := submodule_eq_bot_or_top_of_tensorActions k k[X] k[X] k k
  trivial

example : True := by
  have := exists_tensorFactorization_of_simpleBimodule k k[X] k[X] k
  trivial

end InfiniteDimensionalRegression

end RepresentationTheory.Algebra.Module.TensorProductSimplicity
