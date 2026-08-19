/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.SimpleModule.Endomorphisms
import RepresentationTheory.Alignment.Attribute


namespace RepresentationTheory.Algebra.Module.ExtensionCocycles

variable (k : Type*) (A : Type*) (V : Type*) (W : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

/-- A family of base-field-linear endomorphisms of a module indexed by elements of the algebra. -/
noncomputable abbrev algebraEndomorphismFamily (M : Type*) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] (a : A) : M →ₗ[k] M :=
  Algebra.lsmul k k M a

/-- The predicate on a linear map that makes its associated action on the product multiplicative. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
def IsExtensionCocycle (f : A →ₗ[k] (W →ₗ[k] V)) : Prop :=
  ∀ a b : A, f (a * b) = (algebraEndomorphismFamily k A V a).comp (f b) + (f a).comp (algebraEndomorphismFamily k A W b)

/-- The linear endomorphism of a product determined by an algebra element and an extension map. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
noncomputable def extensionAction (f : A →ₗ[k] (W →ₗ[k] V)) (a : A) : (V × W) →ₗ[k] (V × W) :=
  LinearMap.prod
    (LinearMap.coprod (algebraEndomorphismFamily k A V a) (f a))
    ((algebraEndomorphismFamily k A W a).comp (LinearMap.snd k V W))

/-- The extension action on a pair is the diagonal module action together with the extension contribution in the first component. -/
theorem extensionAction_apply_mk (f : A →ₗ[k] (W →ₗ[k] V)) (a : A) (v : V) (w : W) :
    extensionAction k A V W f a (v, w) = (a • v + f a w, a • w) := by
  simp [extensionAction, Algebra.lsmul_coe]

/-- The extension action preserves multiplication exactly when the defining linear map is an extension cocycle. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
theorem extensionAction_mul_iff (f : A →ₗ[k] (W →ₗ[k] V)) :
    (∀ a b : A, extensionAction k A V W f (a * b)
        = (extensionAction k A V W f a).comp (extensionAction k A V W f b))
      ↔ IsExtensionCocycle k A V W f := by
  constructor
  · intro h a b
    ext w
    have h2 := LinearMap.congr_fun (h a b) (0, w)
    rw [LinearMap.comp_apply, extensionAction_apply_mk, extensionAction_apply_mk, extensionAction_apply_mk] at h2
    simp only [smul_zero, zero_add, Prod.mk.injEq] at h2
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe]
    exact h2.1
  · intro h a b
    apply LinearMap.ext
    rintro ⟨v, w⟩
    have hc := LinearMap.congr_fun (h a b) w
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe] at hc
    rw [LinearMap.comp_apply, extensionAction_apply_mk, extensionAction_apply_mk, extensionAction_apply_mk, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hc]; simp only [mul_smul, smul_add]; abel
    · rw [mul_smul]

/-- An auxiliary submodule of linear maps from the algebra to linear maps between the two modules. -/
@[source_ref "Chapter3/Problem3.9.1" (role := primary)]
def auxiliaryMapSubmodule : Submodule k (A →ₗ[k] (W →ₗ[k] V)) where
  carrier := {f | IsExtensionCocycle k A V W f}
  add_mem' {f g} hf hg := by
    intro a b
    simp only [LinearMap.add_apply, hf a b, hg a b, LinearMap.comp_add, LinearMap.add_comp]
    abel
  zero_mem' := by intro a b; simp
  smul_mem' c f hf := by
    intro a b
    simp only [LinearMap.smul_apply, hf a b, LinearMap.comp_smul, LinearMap.smul_comp, smul_add]

/-- The extension map measuring the difference between applying an algebra element before and after a linear map of modules. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
noncomputable def coboundary (X : W →ₗ[k] V) : A →ₗ[k] (W →ₗ[k] V) :=
  ((LinearMap.llcomp k W V V).flip X).comp (Algebra.lsmul k k V).toLinearMap
    - (LinearMap.llcomp k W W V X).comp (Algebra.lsmul k k W).toLinearMap

/-- Evaluating a coboundary gives the algebra action after the linear map minus the linear map after the algebra action. -/
theorem coboundary_apply_apply (X : W →ₗ[k] V) (a : A) (w : W) :
    coboundary k A V W X a w = a • X w - X (a • w) := by
  simp only [coboundary, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
    LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe]

/-- Every coboundary satisfies the extension cocycle condition. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
theorem isExtensionCocycle_coboundary (X : W →ₗ[k] V) : IsExtensionCocycle k A V W (coboundary k A V W X) := by
  intro a b
  ext w
  simp only [coboundary, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.llcomp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe,
    mul_smul, map_sub]
  abel

/-- A coboundary vanishes exactly when the underlying linear map commutes with the algebra action. -/
@[source_ref "Chapter3/Problem3.9.1" (role := primary),
  source_ref "Chapter3/Problem3.9.1/Derived7" (role := supporting)]
theorem coboundary_eq_zero_iff (X : W →ₗ[k] V) :
    coboundary k A V W X = 0 ↔ ∀ (a : A) (w : W), X (a • w) = a • X w := by
  constructor
  · intro h a w
    have := LinearMap.congr_fun (LinearMap.congr_fun h a) w
    simp only [coboundary, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
      LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe, LinearMap.zero_apply,
      sub_eq_zero] at this
    exact this.symm
  · intro h
    ext a w
    simp only [coboundary, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
      LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe, LinearMap.zero_apply,
      sub_eq_zero, h a w]

/-- The submodule of extension maps arising as coboundaries of linear maps between the two modules. -/
def coboundaries : Submodule k (A →ₗ[k] (W →ₗ[k] V)) :=
  Submodule.span k (Set.range (coboundary k A V W))

/-- The linear map sending a linear map between modules to its associated coboundary. -/
@[source_ref "Chapter3/Problem3.9.1/Derived7" (role := supporting)]
noncomputable def coboundaryLinearMap : (W →ₗ[k] V) →ₗ[k] (A →ₗ[k] (W →ₗ[k] V)) where
  toFun := coboundary k A V W
  map_add' X Y := by
    ext a w
    simp only [coboundary_apply_apply, LinearMap.add_apply, smul_add]
    abel
  map_smul' c X := by
    ext a w
    simp only [coboundary_apply_apply, LinearMap.smul_apply, RingHom.id_apply, smul_sub,
      smul_comm a c]

/-- The coboundary linear map evaluates to the corresponding coboundary. -/
@[simp] theorem coboundaryLinearMap_apply (X : W →ₗ[k] V) :
    coboundaryLinearMap k A V W X = coboundary k A V W X := rfl

/-- The submodule of coboundaries is the range of the coboundary linear map. -/
@[source_ref "Chapter3/Problem3.9.1/Derived7" (role := supporting)]
theorem coboundaries_eq_range :
    coboundaries k A V W = LinearMap.range (coboundaryLinearMap k A V W) := by
  apply le_antisymm
  · rw [coboundaries, Submodule.span_le]
    rintro _ ⟨X, rfl⟩
    exact ⟨X, rfl⟩
  · rintro _ ⟨X, rfl⟩
    exact Submodule.subset_span ⟨X, rfl⟩

/-- An extension map belongs to the coboundary submodule exactly when it is the coboundary of some linear map. -/
theorem mem_coboundaries_iff (g : A →ₗ[k] (W →ₗ[k] V)) :
    g ∈ coboundaries k A V W ↔ ∃ X : W →ₗ[k] V, coboundary k A V W X = g := by
  rw [coboundaries_eq_range, LinearMap.mem_range]
  simp only [coboundaryLinearMap_apply]

/-- Every coboundary belongs to the auxiliary submodule of linear maps. -/
theorem coboundaries_le_auxiliaryMapSubmodule :
    coboundaries k A V W ≤ auxiliaryMapSubmodule k A V W := by
  rw [coboundaries, Submodule.span_le, Set.range_subset_iff]
  intro X
  exact isExtensionCocycle_coboundary k A V W X

/-- An auxiliary type parameterized by two modules over an algebra. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
abbrev AuxiliaryData : Type _ :=
  (auxiliaryMapSubmodule k A V W) ⧸
    (coboundaries k A V W).submoduleOf (auxiliaryMapSubmodule k A V W)


/-- A compatibility predicate for a linear equivalence of products relative to two extension maps. -/
def IsExtensionEquiv (f f' : A →ₗ[k] (W →ₗ[k] V)) (φ : (V × W) ≃ₗ[k] (V × W)) : Prop :=
  ∀ a : A, (φ.toLinearMap).comp (extensionAction k A V W f a)
    = (extensionAction k A V W f' a).comp φ.toLinearMap

/-- A coboundary difference between two extension cocycles yields a compatible equivalence of their products. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
theorem exists_isExtensionEquiv_of_sub_mem_coboundaries (f f' : A →ₗ[k] (W →ₗ[k] V))
    (hf : IsExtensionCocycle k A V W f) (hf' : IsExtensionCocycle k A V W f')
    (hsub : f - f' ∈ coboundaries k A V W) :
    ∃ φ : (V × W) ≃ₗ[k] (V × W), IsExtensionEquiv k A V W f f' φ := by
  obtain ⟨X, hX⟩ := (mem_coboundaries_iff k A V W (f - f')).1 hsub
  -- `φ = [[1, X], [0, 1]]`, i.e. `(v, w) ↦ (v + X w, w)`, with inverse `(v, w) ↦ (v - X w, w)`.
  set L : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W + X ∘ₗ LinearMap.snd k V W) (LinearMap.snd k V W)
    with hL
  set Linv : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W - X ∘ₗ LinearMap.snd k V W) (LinearMap.snd k V W)
    with hLinv
  have Lapp : ∀ p : V × W, L p = (p.1 + X p.2, p.2) := fun p => by
    simp [hL, Function.prod_apply]
  have Linvapp : ∀ p : V × W, Linv p = (p.1 - X p.2, p.2) := fun p => by
    simp [hLinv, Function.prod_apply]
  refine ⟨LinearEquiv.ofLinear L Linv ?_ ?_, ?_⟩
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp [Lapp, Linvapp]
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp [Lapp, Linvapp]
  intro a
  apply LinearMap.ext
  rintro ⟨v, w⟩
  -- The off-diagonal identity: `(f - f') a w = a • X w - X (a • w)`.
  have key : a • X w + f' a w = f a w + X (a • w) := by
    have h := LinearMap.congr_fun (LinearMap.congr_fun hX a) w
    rw [coboundary_apply_apply, LinearMap.sub_apply] at h
    exact sub_eq_sub_iff_add_eq_add.1 h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, extensionAction_apply_mk,
    Lapp, smul_add]
  rw [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  simp only [add_assoc, ← key]

/-- A compatible product equivalence given by a linear shear forces the difference of its extension maps to be a coboundary. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
theorem sub_mem_coboundaries_of_shear_isExtensionEquiv
    (f f' : A →ₗ[k] (W →ₗ[k] V)) (_hf : IsExtensionCocycle k A V W f) (_hf' : IsExtensionCocycle k A V W f')
    (φ : (V × W) ≃ₗ[k] (V × W)) (X : W →ₗ[k] V)
    (hφX : ∀ p : V × W, (φ p : V × W) = (p.1 + X p.2, p.2))
    (hφ : IsExtensionEquiv k A V W f f' φ) :
    f - f' ∈ coboundaries k A V W := by
  rw [mem_coboundaries_iff]
  refine ⟨X, ?_⟩
  ext a w
  -- Off-diagonal `(1,2)`-block of `φ ∘ ρ_{U_f}(a) = ρ_{U_{f'}}(a) ∘ φ`, evaluated at `(0, w)`.
  have h := LinearMap.congr_fun (hφ a) (0, w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, extensionAction_apply_mk, hφX, smul_zero,
    zero_add] at h
  -- `h : (f a w + X (a • w), a • w) = (a • X w + f' a w, a • w)`.
  rw [Prod.ext_iff] at h
  obtain ⟨h1, -⟩ := h
  rw [coboundary_apply_apply]
  simp only [LinearMap.sub_apply]
  -- goal: `a • X w - X (a • w) = f a w - f' a w`
  exact sub_eq_sub_iff_add_eq_add.mpr h1.symm

/-- If the first extension map minus a nonzero scalar multiple of the second is a coboundary, then a compatible product equivalence exists. -/
theorem exists_isExtensionEquiv_of_sub_smul_mem_coboundaries (f f' : A →ₗ[k] (W →ₗ[k] V))
    (c : k) (hc : c ≠ 0) (hsub : f - c • f' ∈ coboundaries k A V W) :
    ∃ φ : (V × W) ≃ₗ[k] (V × W), IsExtensionEquiv k A V W f f' φ := by
  obtain ⟨X, hX⟩ := (mem_coboundaries_iff k A V W (f - c • f')).1 hsub
  -- `φ = [[1, X], [0, c]]`, i.e. `(v, w) ↦ (v + X w, c • w)`.
  set L : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W + X ∘ₗ LinearMap.snd k V W) (c • LinearMap.snd k V W)
    with hL
  set Linv : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W - c⁻¹ • (X ∘ₗ LinearMap.snd k V W))
      (c⁻¹ • LinearMap.snd k V W) with hLinv
  have Lapp : ∀ p : V × W, L p = (p.1 + X p.2, c • p.2) := fun p => by
    simp [hL, Function.prod_apply]
  have Linvapp : ∀ p : V × W, Linv p = (p.1 - c⁻¹ • X p.2, c⁻¹ • p.2) := fun p => by
    simp [hLinv, Function.prod_apply]
  refine ⟨LinearEquiv.ofLinear L Linv ?_ ?_, ?_⟩
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp only [LinearMap.comp_apply, Lapp, Linvapp, LinearMap.id_coe, id_eq, map_smul,
      smul_inv_smul₀ hc, sub_add_cancel]
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp only [LinearMap.comp_apply, Lapp, Linvapp, LinearMap.id_coe, id_eq, map_smul,
      inv_smul_smul₀ hc, add_sub_cancel_right]
  intro a
  apply LinearMap.ext
  rintro ⟨v, w⟩
  -- Off-diagonal identity: `(f - c • f') a w = a • X w - X (a • w)`.
  have key : a • X w + c • f' a w = f a w + X (a • w) := by
    have h := LinearMap.congr_fun (LinearMap.congr_fun hX a) w
    simp only [coboundary_apply_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h
    exact sub_eq_sub_iff_add_eq_add.1 h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, extensionAction_apply_mk,
    Lapp, smul_add, map_smul]
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [add_assoc, ← key]
  · rw [smul_comm]

/-- Over an algebraically closed field, under the stated simplicity and finite-dimensionality hypotheses, a compatible product equivalence exists exactly when the first extension map minus a nonzero scalar multiple of the second is a coboundary. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
theorem exists_isExtensionEquiv_iff_exists_sub_smul_mem_coboundaries [IsAlgClosed k]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule A W]
    (f f' : A →ₗ[k] (W →ₗ[k] V)) (_hf : IsExtensionCocycle k A V W f) (_hf' : IsExtensionCocycle k A V W f') :
    (∃ φ : (V × W) ≃ₗ[k] (V × W), IsExtensionEquiv k A V W f f' φ)
      ↔ ∃ c : k, c ≠ 0 ∧ f - c • f' ∈ coboundaries k A V W := by
  constructor
  · rintro ⟨φ, hφ⟩
    -- Block components of `φ` in the `V × W` basis.
    set P : (V × W) →ₗ[k] V := (LinearMap.fst k V W).comp φ.toLinearMap with hP
    set Q : (V × W) →ₗ[k] W := (LinearMap.snd k V W).comp φ.toLinearMap with hQ
    set α : V →ₗ[k] V := P.comp (LinearMap.inl k V W) with hαdef
    set β : W →ₗ[k] V := P.comp (LinearMap.inr k V W) with hβdef
    set γ : V →ₗ[k] W := Q.comp (LinearMap.inl k V W) with hγdef
    set δ : W →ₗ[k] W := Q.comp (LinearMap.inr k V W) with hδdef
    have hPvw : ∀ v w, P (v, w) = α v + β w := by
      intro v w
      have h : (v, w) = LinearMap.inl k V W v + LinearMap.inr k V W w := by
        simp
      rw [h, map_add]; rfl
    have hQvw : ∀ v w, Q (v, w) = γ v + δ w := by
      intro v w
      have h : (v, w) = LinearMap.inl k V W v + LinearMap.inr k V W w := by
        simp
      rw [h, map_add]; rfl
    have hP1 : ∀ p : V × W, (φ p : V × W).1 = P p := fun p => by simp [hP]
    have hQ2 : ∀ p : V × W, (φ p : V × W).2 = Q p := fun p => by simp [hQ]
    have hφsplit : ∀ v w, (φ (v, w) : V × W) = (P (v, w), Q (v, w)) := by
      intro v w
      exact Prod.ext (hP1 (v, w)) (hQ2 (v, w))
    -- Master intertwining identity, evaluated pointwise.
    have hmain : ∀ a v w,
        (φ (a • v + f a w, a • w) : V × W)
          = (a • P (v, w) + f' a (Q (v, w)), a • Q (v, w)) := by
      intro a v w
      have h := LinearMap.congr_fun (hφ a) (v, w)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, extensionAction_apply_mk] at h
      rw [h, hφsplit v w, extensionAction_apply_mk]
    have EfstP : ∀ a v w, P (a • v + f a w, a • w) = a • P (v, w) + f' a (Q (v, w)) := by
      intro a v w
      have h := congrArg Prod.fst (hmain a v w)
      rwa [hP1] at h
    have EsndQ : ∀ a v w, Q (a • v + f a w, a • w) = a • Q (v, w) := by
      intro a v w
      have h := congrArg Prod.snd (hmain a v w)
      rwa [hQ2] at h
    -- The four block equations.
    have hγA : ∀ (a : A) (v : V), γ (a • v) = a • γ v := by
      intro a v
      have h := EsndQ a v 0
      simpa only [map_zero, smul_zero, add_zero, hQvw] using h
    have Eq11 : ∀ (a : A) (v : V), α (a • v) = a • α v + f' a (γ v) := by
      intro a v
      have h := EfstP a v 0
      simpa only [map_zero, smul_zero, add_zero, hPvw, hQvw] using h
    have Eq12 : ∀ (a : A) (w : W), α (f a w) + β (a • w) = a • β w + f' a (δ w) := by
      intro a w
      have h := EfstP a 0 w
      simpa only [smul_zero, zero_add, hPvw, hQvw, map_zero, add_zero] using h
    have Eq22 : ∀ (a : A) (w : W), γ (f a w) + δ (a • w) = a • δ w := by
      intro a w
      have h := EsndQ a 0 w
      simpa only [smul_zero, zero_add, hQvw, map_zero, add_zero] using h
    -- Package `γ` as an `A`-linear map and apply Schur.
    let γA : V →ₗ[A] W :=
      { toFun := γ, map_add' := fun x y => γ.map_add x y, map_smul' := fun a v => hγA a v }
    rcases γA.bijective_or_eq_zero with hbij | hzero
    · -- `γ` is an isomorphism: both `f` and `f'` are coboundaries.
      let eγ : V ≃ₗ[A] W := LinearEquiv.ofBijective γA hbij
      have heγ : ∀ x, eγ x = γ x := fun x => rfl
      let gk : W →ₗ[k] V := (eγ.symm.toLinearMap).restrictScalars k
      have hgk : ∀ w, gk w = eγ.symm w := fun w => rfl
      have hγsym : ∀ w, γ (eγ.symm w) = w := by
        intro w
        have h := eγ.apply_symm_apply w
        rwa [heγ] at h
      have hfcob : f ∈ coboundaries k A V W := by
        rw [mem_coboundaries_iff]
        refine ⟨gk.comp δ, ?_⟩
        ext a w
        have hgw : γ (f a w) = a • δ w - δ (a • w) := by
          rw [eq_sub_iff_add_eq]; exact Eq22 a w
        simp only [coboundary_apply_apply, LinearMap.comp_apply, hgk]
        rw [← map_smul (eγ.symm) a (δ w), ← map_sub, ← hgw, ← heγ (f a w),
          eγ.symm_apply_apply]
      have hf'cob : f' ∈ coboundaries k A V W := by
        rw [mem_coboundaries_iff]
        refine ⟨-(α.comp gk), ?_⟩
        ext a w
        have hEq := Eq11 a (eγ.symm w)
        rw [hγsym w] at hEq
        rw [← map_smul (eγ.symm) a w] at hEq
        simp only [coboundary_apply_apply, LinearMap.neg_apply, LinearMap.comp_apply, hgk, smul_neg]
        rw [hEq]
        abel
      exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.sub_mem _ hfcob hf'cob⟩
    · -- `γ = 0`: `α`, `δ` are nonzero scalars; the `(1,2)` block gives proportionality.
      have hγ0 : ∀ v, γ v = 0 := fun v => LinearMap.congr_fun hzero v
      have hαA : ∀ (a : A) (v : V), α (a • v) = a • α v := by
        intro a v; rw [Eq11 a v, hγ0 v, map_zero, add_zero]
      have hδA : ∀ (a : A) (w : W), δ (a • w) = a • δ w := by
        intro a w
        have h := Eq22 a w
        rwa [hγ0 (f a w), zero_add] at h
      let αA : V →ₗ[A] V :=
        { toFun := α, map_add' := fun x y => α.map_add x y, map_smul' := fun a v => hαA a v }
      let δA : W →ₗ[A] W :=
        { toFun := δ, map_add' := fun x y => δ.map_add x y, map_smul' := fun a w => hδA a w }
      obtain ⟨s, hs⟩ := RepresentationTheory.Algebra.SimpleModule.Endomorphisms.endomorphism_eq_smul (k := k) (A := A) (V := V) αA
      obtain ⟨t, ht⟩ := RepresentationTheory.Algebra.SimpleModule.Endomorphisms.endomorphism_eq_smul (k := k) (A := A) (V := W) δA
      have hsα : ∀ v, α v = s • v := hs
      have htδ : ∀ w, δ w = t • w := ht
      have hs0 : s ≠ 0 := by
        intro hs_eq
        haveI : Nontrivial V := IsSimpleModule.nontrivial (R := A) (M := V)
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine hv ?_
        have hz : (φ (v, 0) : V × W) = 0 := by
          rw [hφsplit v 0, hPvw, hQvw]
          simp [hsα v, hs_eq, hγ0 v]
        have h0 := φ.map_eq_zero_iff.mp hz
        simpa using congrArg Prod.fst h0
      have ht0 : t ≠ 0 := by
        intro ht_eq
        haveI : Nontrivial W := IsSimpleModule.nontrivial (R := A) (M := W)
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        refine hw ?_
        have hQzero : ∀ q : V × W, Q q = 0 := by
          intro q
          obtain ⟨qv, qw⟩ := q
          rw [hQvw]
          simp [hγ0 qv, htδ qw, ht_eq]
        have hval : (φ (φ.symm (0, w)) : V × W).2 = w := by rw [φ.apply_symm_apply]
        rw [hQ2, hQzero] at hval
        exact hval.symm
      have hcob : s • f - t • f' ∈ coboundaries k A V W := by
        rw [mem_coboundaries_iff]
        refine ⟨β, ?_⟩
        ext a w
        have h := Eq12 a w
        rw [hsα (f a w), htδ w, map_smul (f' a) t w] at h
        simp only [coboundary_apply_apply, LinearMap.sub_apply, LinearMap.smul_apply]
        exact sub_eq_sub_iff_add_eq_add.mpr h.symm
      refine ⟨s⁻¹ * t, mul_ne_zero (inv_ne_zero hs0) ht0, ?_⟩
      have hrw : f - (s⁻¹ * t) • f' = s⁻¹ • (s • f - t • f') := by
        rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [hrw]
      exact Submodule.smul_mem _ _ hcob
  · rintro ⟨c, hc, hsub⟩
    exact exists_isExtensionEquiv_of_sub_smul_mem_coboundaries k A V W f f' c hc hsub


/-- Describes the extension action on an arbitrary element of the product. -/
theorem extensionAction_apply (f : A →ₗ[k] (W →ₗ[k] V)) (a : A) (p : V × W) :
    extensionAction k A V W f a p = (a • p.1 + f a p.2, a • p.2) :=
  extensionAction_apply_mk k A V W f a p.1 p.2

/-- An extension cocycle vanishes at one. -/
theorem IsExtensionCocycle.map_one_eq_zero {f : A →ₗ[k] (W →ₗ[k] V)} (hf : IsExtensionCocycle k A V W f) : f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one] at h
  have h2 : f 1 = f 1 + f 1 := by
    refine h.trans ?_
    ext w
    simp
  simpa using h2

/-- The zero extension map satisfies the extension cocycle condition. -/
theorem isExtensionCocycle_zero : IsExtensionCocycle k A V W (0 : A →ₗ[k] (W →ₗ[k] V)) := by
  intro a b; simp

/-- The module type on a product determined by an extension cocycle valued in linear maps between two modules. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
def ExtensionModule (f : A →ₗ[k] (W →ₗ[k] V)) (_hf : IsExtensionCocycle k A V W f) : Type _ := V × W

namespace ExtensionModule

variable {k A V W}
variable {f f' : A →ₗ[k] (W →ₗ[k] V)}
variable {hf : IsExtensionCocycle k A V W f} {hf' : IsExtensionCocycle k A V W f'}

/-- The additive commutative group structure on an extension module. -/
instance instAddCommGroup : AddCommGroup (ExtensionModule k A V W f hf) :=
  inferInstanceAs (AddCommGroup (V × W))

/-- The field-module structure on an extension module. -/
instance instModuleField : Module k (ExtensionModule k A V W f hf) :=
  inferInstanceAs (Module k (V × W))

/-- Returns the underlying pair of an element of an extension module. -/
def toProd (u : ExtensionModule k A V W f hf) : V × W := u

/-- Regards an element of the underlying product as an element of an extension module. -/
def ofProd (g : A →ₗ[k] (W →ₗ[k] V)) (hg : IsExtensionCocycle k A V W g) (p : V × W) :
    ExtensionModule k A V W g hg := p

/-- Constructs an element of an extension module from its two components. -/
def mk (g : A →ₗ[k] (W →ₗ[k] V)) (hg : IsExtensionCocycle k A V W g) (v : V) (w : W) :
    ExtensionModule k A V W g hg := ofProd g hg (v, w)

/-- The map from an extension module to its underlying product is injective. -/
theorem toProd_injective {u u' : ExtensionModule k A V W f hf} (h : u.toProd = u'.toProd) : u = u' := h

/-- Passing from a product element to the extension and back returns the original product. -/
@[simp] theorem toProd_ofProd (p : V × W) : (ofProd f hf p).toProd = p := rfl

/-- Converting an extension element to the product and back leaves it unchanged. -/
@[simp] theorem ofProd_toProd (u : ExtensionModule k A V W f hf) : ofProd f hf u.toProd = u := rfl

/-- The underlying pair of an extension element constructed from two components is that pair. -/
@[simp] theorem toProd_mk (v : V) (w : W) : (mk f hf v w).toProd = (v, w) := rfl

/-- The underlying pair of zero is zero. -/
@[simp] theorem toProd_zero : (0 : ExtensionModule k A V W f hf).toProd = 0 := rfl

/-- The underlying pair of a sum is the sum of the underlying pairs. -/
@[simp] theorem toProd_add (u u' : ExtensionModule k A V W f hf) : (u + u').toProd = u.toProd + u'.toProd := rfl

/-- The underlying-pair map commutes with scalar multiplication by the base field. -/
@[simp] theorem toProd_smul_field (c : k) (u : ExtensionModule k A V W f hf) : (c • u).toProd = c • u.toProd := rfl

/-- The scalar action of the algebra on an extension module. -/
noncomputable instance instSMul : SMul A (ExtensionModule k A V W f hf) :=
  ⟨fun a u => ofProd f hf (a • u.toProd.1 + f a u.toProd.2, a • u.toProd.2)⟩

/-- Describes the underlying pair after scalar multiplication by an algebra element. -/
@[simp] theorem toProd_smul_algebra (a : A) (u : ExtensionModule k A V W f hf) :
    (a • u).toProd = (a • u.toProd.1 + f a u.toProd.2, a • u.toProd.2) := rfl

/-- The underlying pair of an algebra multiple is obtained by applying the extension action to the underlying pair. -/
theorem toProd_smul_eq_extensionAction (a : A) (u : ExtensionModule k A V W f hf) :
    (a • u).toProd = extensionAction k A V W f a u.toProd := by
  rw [toProd_smul_algebra, extensionAction_apply]

/-- Algebra scalar multiplication on an extension element acts diagonally with the cocycle contribution in the first component. -/
@[simp] theorem smul_mk (a : A) (v : V) (w : W) :
    a • mk f hf v w = mk f hf (a • v + f a w) (a • w) := rfl

/-- The multiplicative action of the algebra on an extension module. -/
noncomputable instance instMulAction : MulAction A (ExtensionModule k A V W f hf) :=
  { instSMul with
    one_smul := fun u => by
      apply ExtensionModule.toProd_injective
      simp [hf.map_one_eq_zero]
    mul_smul := fun a b u => by
      apply ExtensionModule.toProd_injective
      have hc := LinearMap.congr_fun (hf a b) u.toProd.2
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe] at hc
      simp only [toProd_smul_algebra, hc, mul_smul, smul_add, Prod.mk.injEq]
      exact ⟨by abel, trivial⟩ }

/-- The distributive multiplicative action of the algebra on an extension module. -/
noncomputable instance instDistribMulAction : DistribMulAction A (ExtensionModule k A V W f hf) :=
  { instMulAction with
    smul_zero := fun a => by
      apply ExtensionModule.toProd_injective
      simp
    smul_add := fun a u u' => by
      apply ExtensionModule.toProd_injective
      simp only [toProd_smul_algebra, toProd_add, Prod.fst_add, Prod.snd_add, smul_add, map_add,
        Prod.mk_add_mk, Prod.mk.injEq]
      exact ⟨by abel, trivial⟩ }

/-- The algebra-module structure on an extension module. -/
noncomputable instance instModuleAlgebra : Module A (ExtensionModule k A V W f hf) :=
  { instDistribMulAction with
    add_smul := fun a b u => by
      apply ExtensionModule.toProd_injective
      simp only [toProd_smul_algebra, toProd_add, add_smul, map_add, LinearMap.add_apply, Prod.mk_add_mk,
        Prod.mk.injEq]
      exact ⟨by abel, trivial⟩
    zero_smul := fun u => by
      apply ExtensionModule.toProd_injective
      simp }

/-- The scalar actions of the field and algebra on an extension module form a scalar tower. -/
instance instIsScalarTower : IsScalarTower k A (ExtensionModule k A V W f hf) where
  smul_assoc c a u := by
    apply ExtensionModule.toProd_injective
    simp only [toProd_smul_algebra, toProd_smul_field, smul_assoc, map_smul, LinearMap.smul_apply, Prod.smul_mk,
      smul_add]

/-- The extension module is linearly equivalent over the base field to its underlying product. -/
def linearEquivProd (g : A →ₗ[k] (W →ₗ[k] V)) (hg : IsExtensionCocycle k A V W g) :
    ExtensionModule k A V W g hg ≃ₗ[k] V × W where
  toFun := toProd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := ofProd g hg
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical equivalence with the product evaluates to the underlying-pair map. -/
@[simp] theorem linearEquivProd_apply (u : ExtensionModule k A V W f hf) : linearEquivProd f hf u = u.toProd := rfl

/-- The inverse of the canonical equivalence with the product evaluates by the product constructor. -/
@[simp] theorem linearEquivProd_symm_apply (p : V × W) : (linearEquivProd f hf).symm p = ofProd f hf p := rfl


/-- The linear inclusion of the first module into an extension module. -/
def inclusion (g : A →ₗ[k] (W →ₗ[k] V)) (hg : IsExtensionCocycle k A V W g) :
    V →ₗ[A] ExtensionModule k A V W g hg where
  toFun v := mk g hg v 0
  map_add' v v' := by apply ExtensionModule.toProd_injective; simp
  map_smul' a v := by apply ExtensionModule.toProd_injective; simp

/-- The canonical inclusion sends an element to the extension element with zero second component. -/
@[simp] theorem inclusion_apply (v : V) : inclusion f hf v = mk f hf v 0 := rfl

/-- The linear projection from an extension module to its second module. -/
def projection (g : A →ₗ[k] (W →ₗ[k] V)) (hg : IsExtensionCocycle k A V W g) :
    ExtensionModule k A V W g hg →ₗ[A] W where
  toFun u := u.toProd.2
  map_add' u u' := by simp
  map_smul' a u := by simp

/-- The canonical projection is the second component of the underlying product. -/
@[simp] theorem projection_apply (u : ExtensionModule k A V W f hf) : projection f hf u = u.toProd.2 := rfl

/-- The canonical inclusion into an extension module is injective. -/
theorem inclusion_injective : Function.Injective (inclusion f hf) := by
  intro v v' h
  have := congrArg ExtensionModule.toProd h
  simpa using congrArg Prod.fst this

/-- The canonical projection from an extension module is surjective. -/
theorem projection_surjective : Function.Surjective (projection f hf) :=
  fun w => ⟨mk f hf 0 w, by simp⟩

/-- The composite of the canonical projection with the canonical inclusion is zero. -/
theorem projection_comp_inclusion :
    (projection f hf).comp (inclusion f hf) = 0 := by
  ext v
  simp

/-- The range of the canonical inclusion equals the kernel of the canonical projection. -/
theorem range_inclusion_eq_ker_projection :
    LinearMap.range (inclusion f hf) = LinearMap.ker (projection f hf) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    simp [LinearMap.mem_ker]
  · intro u hu
    rw [LinearMap.mem_ker, projection_apply] at hu
    exact ⟨u.toProd.1, ExtensionModule.toProd_injective (by simp [Prod.ext_iff, hu])⟩

/-- The canonical inclusion and projection of an extension module form an exact pair. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
theorem exact_inclusion_projection :
    Function.Exact (inclusion f hf) (projection f hf) :=
  LinearMap.exact_iff.mpr range_inclusion_eq_ker_projection.symm

/-- The quotient of an extension module by the range of its canonical inclusion is linearly equivalent to the second module. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
noncomputable def quotientRangeInclusionEquiv (g : A →ₗ[k] (W →ₗ[k] V)) (hg : IsExtensionCocycle k A V W g) :
    (ExtensionModule k A V W g hg ⧸ LinearMap.range (inclusion g hg)) ≃ₗ[A] W :=
  (Submodule.quotEquivOfEq _ _ range_inclusion_eq_ker_projection).trans
    ((projection g hg).quotKerEquivOfSurjective projection_surjective)

/-- The extension module associated with the zero cocycle is linearly equivalent over the algebra to the product module. -/
@[source_ref "Chapter3/Problem3.9.1" (role := primary)]
noncomputable def zeroLinearEquivProd : ExtensionModule k A V W (0 : A →ₗ[k] (W →ₗ[k] V)) (isExtensionCocycle_zero k A V W)
    ≃ₗ[A] V × W where
  toFun := toProd
  map_add' _ _ := rfl
  map_smul' a u := by simp [Prod.ext_iff]
  invFun := ofProd _ _
  left_inv _ := rfl
  right_inv _ := rfl


/-- Constructs a linear equivalence of extension modules from a compatible equivalence of their underlying products. -/
noncomputable def linearEquivOfIsExtensionEquiv (hf : IsExtensionCocycle k A V W f) (hf' : IsExtensionCocycle k A V W f')
    (φ : (V × W) ≃ₗ[k] (V × W)) (hφ : IsExtensionEquiv k A V W f f' φ) :
    ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf' where
  toFun u := ofProd f' hf' (φ u.toProd)
  map_add' u u' := by apply ExtensionModule.toProd_injective; simp
  map_smul' a u := by
    apply ExtensionModule.toProd_injective
    have h := LinearMap.congr_fun (hφ a) u.toProd
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    simpa [toProd_smul_eq_extensionAction, extensionAction_apply] using h
  invFun u := ofProd f hf (φ.symm u.toProd)
  left_inv u := by apply ExtensionModule.toProd_injective; simp
  right_inv u := by apply ExtensionModule.toProd_injective; simp

/-- The equivalence induced by compatible product data agrees with that data after passage to the underlying products. -/
@[simp] theorem toProd_linearEquivOfIsExtensionEquiv (hf : IsExtensionCocycle k A V W f) (hf' : IsExtensionCocycle k A V W f')
    (φ : (V × W) ≃ₗ[k] (V × W)) (hφ : IsExtensionEquiv k A V W f f' φ)
    (u : ExtensionModule k A V W f hf) :
    (linearEquivOfIsExtensionEquiv hf hf' φ hφ u).toProd = φ u.toProd := rfl

/-- The linear equivalence of underlying products induced by a linear equivalence of extension modules. -/
noncomputable def underlyingLinearEquiv (ψ : ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf') :
    (V × W) ≃ₗ[k] (V × W) :=
  ((linearEquivProd f hf).symm.trans (ψ.restrictScalars k)).trans (linearEquivProd f' hf')

/-- Evaluating the induced equivalence of products amounts to entering the source extension, applying the given equivalence, and returning to the product. -/
@[simp] theorem underlyingLinearEquiv_apply
    (ψ : ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf') (p : V × W) :
    underlyingLinearEquiv ψ p = (ψ (ofProd f hf p)).toProd := rfl

/-- The equivalence of products induced by a linear equivalence of extension modules is compatible with their extension data. -/
theorem isExtensionEquiv_underlyingLinearEquiv
    (ψ : ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf') :
    IsExtensionEquiv k A V W f f' (underlyingLinearEquiv ψ) := by
  intro a
  apply LinearMap.ext
  intro p
  have hkey : ofProd f hf (extensionAction k A V W f a p) = a • ofProd f hf p :=
    ExtensionModule.toProd_injective (by rw [toProd_ofProd, toProd_smul_eq_extensionAction, toProd_ofProd])
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, underlyingLinearEquiv_apply, hkey,
    map_smul, toProd_smul_eq_extensionAction]

/-- Two extension modules are linearly equivalent exactly when their underlying products admit a compatible linear equivalence. -/
theorem nonempty_linearEquiv_iff_exists_isExtensionEquiv (hf : IsExtensionCocycle k A V W f) (hf' : IsExtensionCocycle k A V W f') :
    Nonempty (ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf')
      ↔ ∃ φ : (V × W) ≃ₗ[k] (V × W), IsExtensionEquiv k A V W f f' φ :=
  ⟨fun ⟨ψ⟩ => ⟨underlyingLinearEquiv ψ, isExtensionEquiv_underlyingLinearEquiv ψ⟩,
   fun ⟨φ, hφ⟩ => ⟨linearEquivOfIsExtensionEquiv hf hf' φ hφ⟩⟩

/-- A coboundary difference between two cocycles yields a linear equivalence of their extension modules. -/
@[source_ref "Chapter3/Problem3.9.1" (role := primary)]
theorem nonempty_linearEquiv_of_sub_mem_coboundaries (hf : IsExtensionCocycle k A V W f)
    (hf' : IsExtensionCocycle k A V W f') (hsub : f - f' ∈ coboundaries k A V W) :
    Nonempty (ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf') :=
  (nonempty_linearEquiv_iff_exists_isExtensionEquiv hf hf').mpr
    (exists_isExtensionEquiv_of_sub_mem_coboundaries k A V W f f' hf hf' hsub)

/-- If an equivalence of extension modules acts on the underlying product by a linear shear, then the difference of the cocycles is a coboundary. -/
@[source_ref "Chapter3/Problem3.9.1" (role := primary)]
theorem sub_mem_coboundaries_of_shear_linearEquiv (hf : IsExtensionCocycle k A V W f)
    (hf' : IsExtensionCocycle k A V W f') (ψ : ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf')
    (X : W →ₗ[k] V) (hψX : ∀ p : V × W, (ψ (ofProd f hf p)).toProd = (p.1 + X p.2, p.2)) :
    f - f' ∈ coboundaries k A V W :=
  sub_mem_coboundaries_of_shear_isExtensionEquiv k A V W f f' hf hf'
    (underlyingLinearEquiv ψ) X hψX (isExtensionEquiv_underlyingLinearEquiv ψ)

/-- For finite-dimensional simple modules over an algebraically closed field, two extension modules are equivalent exactly when the first cocycle minus a nonzero scalar multiple of the second is a coboundary. -/
@[source_ref "Chapter3/Problem3.9.1" (role := primary)]
theorem nonempty_linearEquiv_iff_exists_sub_smul_mem_coboundaries [IsAlgClosed k]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule A W]
    (hf : IsExtensionCocycle k A V W f) (hf' : IsExtensionCocycle k A V W f') :
    Nonempty (ExtensionModule k A V W f hf ≃ₗ[A] ExtensionModule k A V W f' hf')
      ↔ ∃ c : k, c ≠ 0 ∧ f - c • f' ∈ coboundaries k A V W :=
  (nonempty_linearEquiv_iff_exists_isExtensionEquiv hf hf').trans
    (exists_isExtensionEquiv_iff_exists_sub_smul_mem_coboundaries k A V W f f' hf hf')

/-- Under the stated simplicity and finite-dimensionality hypotheses, an extension module is equivalent to the product module exactly when its cocycle is a coboundary. -/
@[source_ref "Chapter3/Problem3.9.1" (role := supporting)]
theorem nonempty_linearEquiv_prod_iff_mem_coboundaries [IsAlgClosed k]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule A W] (hf : IsExtensionCocycle k A V W f) :
    Nonempty (ExtensionModule k A V W f hf ≃ₗ[A] (V × W)) ↔ f ∈ coboundaries k A V W := by
  constructor
  · rintro ⟨ψ⟩
    have h : Nonempty (ExtensionModule k A V W f hf
        ≃ₗ[A] ExtensionModule k A V W (0 : A →ₗ[k] (W →ₗ[k] V)) (isExtensionCocycle_zero k A V W)) :=
      ⟨ψ.trans zeroLinearEquivProd.symm⟩
    obtain ⟨c, -, hc⟩ := (nonempty_linearEquiv_iff_exists_sub_smul_mem_coboundaries hf (isExtensionCocycle_zero k A V W)).1 h
    simpa using hc
  · intro hmem
    obtain ⟨ψ⟩ := nonempty_linearEquiv_of_sub_mem_coboundaries hf (isExtensionCocycle_zero k A V W)
      (by simpa using hmem)
    exact ⟨ψ.trans zeroLinearEquivProd⟩

end ExtensionModule

end RepresentationTheory.Algebra.Module.ExtensionCocycles
