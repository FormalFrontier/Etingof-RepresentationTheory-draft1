/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CentralizerDecomposition

open scoped TensorProduct

universe u v

namespace RepresentationTheory.Centralizer.LinearMaps

open RepresentationTheory.CentralizerDecomposition

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

noncomputable local instance (priority := high) centralizerModuleSubmoduleHom
    (A : Subalgebra k (Module.End k E)) (V : Submodule A E) :
    Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥V →ₗ[A] E) :=
  centralizerModuleHom k E (A := A) (V := ↥V)

/-- Precomposition with an `R`-linear equivalence gives a `k`-linear equivalence between the
corresponding spaces of `R`-linear maps into `E`. -/
noncomputable def LinearEquiv.linearMapPrecomp
    (k : Type*) [CommSemiring k]
    (R : Type*) [Ring R] [Algebra k R]
    (E : Type*) [AddCommGroup E] [Module k E] [Module R E] [IsScalarTower k R E]
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
    (e : M ≃ₗ[R] N) :
    (N →ₗ[R] E) ≃ₗ[k] (M →ₗ[R] E) where
  toFun f := f.comp e.toLinearMap
  invFun f := f.comp e.symm.toLinearMap
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp [LinearMap.smul_apply, LinearMap.comp_apply]

/-- A compatible scalar action through a surjective ring homomorphism transfers simplicity from
the target ring to the source ring. -/
theorem IsSimpleModule.restrictScalars_of_surjective
    {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) [RingHomSurjective σ]
    {X : Type*} [AddCommGroup X] [Module R X] [Module S X]
    (hcompat : ∀ (r : R) (x : X), r • x = σ r • x)
    [IsSimpleModule S X] : IsSimpleModule R X :=
  (LinearMap.isSimpleModule_iff_of_bijective
    ({ toFun := id, map_add' := fun _ _ => rfl,
        map_smul' := fun r x => (hcompat r x) } : X →ₛₗ[σ] X)
    Function.bijective_id).mpr ‹_›

set_option maxHeartbeats 800000 in
-- The outer budget covers scalar-tower elaboration and proof checking.
set_option synthInstance.maxHeartbeats 800000 in
-- The centralizer scalar-tower instance requires costly action synthesis.
/-- The centralizer action on maps from an `A`-module to `E` is compatible with the scalar action
of the base field. -/
instance Subalgebra.centralizer.isScalarTower_linearMap
    {A : Subalgebra k (Module.End k E)}
    {V : Type*} [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    IsScalarTower k (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) where
  smul_assoc r b f := by
    refine LinearMap.ext fun v => ?_
    change (r • b).val (f v) = r • (b.val (f v))
    rw [Subalgebra.coe_smul, LinearMap.smul_apply]

set_option synthInstance.maxHeartbeats 800000 in
-- Specializing the scalar tower to submodules requires deeper instance search.
noncomputable local instance (priority := high) centralizerIsScalarTowerSubmoduleHom
    (A : Subalgebra k (Module.End k E)) (V : Submodule A E) :
    IsScalarTower k (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥V →ₗ[A] E) :=
  Subalgebra.centralizer.isScalarTower_linearMap (A := A) (V := ↥V) k E

set_option synthInstance.maxHeartbeats 800000 in
-- The iterated centralizer action requires costly double-hom module synthesis.
noncomputable local instance (priority := high) doubleCentralizerModuleSubmoduleHom
    (A : Subalgebra k (Module.End k E)) (V : Submodule A E) :
    Module (↥(Subalgebra.centralizer k
      ((Subalgebra.centralizer k (A : Set (Module.End k E))) : Set (Module.End k E))))
      ((↥V →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
  centralizerModuleHom k E
    (A := Subalgebra.centralizer k (A : Set (Module.End k E)))
    (V := (↥V →ₗ[A] E))

set_option maxHeartbeats 6400000 in
-- The outer budget covers the double-centralizer dimension proof.
set_option synthInstance.maxHeartbeats 3200000 in
-- The double-centralizer dimension argument needs extended algebraic instance synthesis.
/-- A simple submodule and its centralizer-linear map space into `E` have equal dimension over the
base field. -/
theorem Subalgebra.centralizer.finrank_linearMap_eq
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    (S : Submodule A E) [IsSimpleModule A S] :
    Module.finrank k ↥S =
      Module.finrank k ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) := by
  classical
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI hCss : IsSemisimpleRing
      (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
    isSemisimpleRing_centralizer k E A
  haveI : IsSemisimpleModule
      (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  haveI hMS : IsSimpleModule
      (Subalgebra.centralizer k (A : Set (Module.End k E))) (↥S →ₗ[A] E) :=
    isSimpleModule_linearMap k E A S
  haveI : Nontrivial ↥S := IsSimpleModule.nontrivial A ↥S
  obtain ⟨s0, hs0⟩ := exists_ne (0 : ↥S)
  let evs0 : (↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E :=
    { toFun := fun l => l s0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hevs0_ne : evs0 ≠ 0 := by
    intro h
    apply hs0
    have h1 : (s0 : E) = 0 := by
      have := LinearMap.congr_fun h S.subtype
      simpa [evs0] using this
    exact Subtype.ext (by simpa using h1)
  have hinjE : Function.Injective evs0 := LinearMap.injective_of_ne_zero hevs0_ne
  let W : Submodule (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    LinearMap.range evs0
  let eMW : (↥S →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] ↥W :=
    LinearEquiv.ofInjective evs0 hinjE
  haveI hWsimple : IsSimpleModule
      (Subalgebra.centralizer k (A : Set (Module.End k E))) ↥W :=
    IsSimpleModule.congr eMW.symm
  haveI hWE : IsSimpleModule
      (Subalgebra.centralizer k
        ((Subalgebra.centralizer k (A : Set (Module.End k E))) :
          Set (Module.End k E)))
      (↥W →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    isSimpleModule_linearMap k E
      (Subalgebra.centralizer k (A : Set (Module.End k E))) W
  let preD : (↥W →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E)
      ≃ₗ[Subalgebra.centralizer k
        ((Subalgebra.centralizer k (A : Set (Module.End k E))) :
          Set (Module.End k E))]
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    { toFun := fun f => f.comp eMW.toLinearMap
      invFun := fun f => f.comp eMW.symm.toLinearMap
      left_inv := fun f => by ext m; simp
      right_inv := fun f => by ext m; simp
      map_add' := fun f g => by ext m; simp
      map_smul' := fun b f => by ext m; rfl }
  haveI hsimpD : IsSimpleModule
      (Subalgebra.centralizer k
        ((Subalgebra.centralizer k (A : Set (Module.End k E))) :
          Set (Module.End k E)))
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    IsSimpleModule.congr preD.symm
  have hCC : Subalgebra.centralizer k
      ((Subalgebra.centralizer k (A : Set (Module.End k E))) :
        Set (Module.End k E)) = A :=
    centralizer_centralizer_eq k E A
  have hAle : A ≤ Subalgebra.centralizer k
      ((Subalgebra.centralizer k (A : Set (Module.End k E))) :
        Set (Module.End k E)) :=
    le_of_eq hCC.symm
  let σ : (↥A) →+* ↥(Subalgebra.centralizer k
      ((Subalgebra.centralizer k (A : Set (Module.End k E))) :
        Set (Module.End k E))) :=
    (Subalgebra.inclusion hAle).toRingHom
  haveI hσsurj : RingHomSurjective σ :=
    ⟨fun y => ⟨⟨y.val, hCC.le y.2⟩, Subtype.ext rfl⟩⟩
  letI instA : Module (↥A)
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    Module.compHom _ σ
  haveI hsimpA : IsSimpleModule (↥A)
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    IsSimpleModule.restrictScalars_of_surjective σ (fun _ _ => rfl)
  let ev : ↥S → ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E) :=
    fun v =>
    { toFun := fun l => l v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let biSk : ↥S →ₗ[k]
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    { toFun := ev
      map_add' := fun v w => by ext l; exact l.map_add v w
      map_smul' := fun c v => by ext l; exact l.map_smul_of_tower c v }
  let biSA : ↥S →ₗ[A]
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    { toFun := ev
      map_add' := fun v w => by ext l; exact l.map_add v w
      map_smul' := fun a v => by
        ext l
        change l (a • v) = (σ a).val (l v)
        rw [l.map_smul a v]; rfl }
  have hinj : Function.Injective biSk := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : (v : E) = 0 := by
      have := LinearMap.congr_fun hv S.subtype
      simpa [biSk, ev] using this
    exact Subtype.ext (by simpa using h1)
  have hbiSA_ne : biSA ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : ↥S)
    intro h
    apply hv
    have hv0 : biSk v = 0 := by
      have : biSA v = 0 := by rw [h]; rfl
      exact this
    apply hinj
    simpa using hv0
  have hrangeA_ne : LinearMap.range biSA ≠ ⊥ := by
    intro hbot
    apply hbiSA_ne
    apply LinearMap.ext
    intro v
    have hv : biSA v ∈ LinearMap.range biSA := ⟨v, rfl⟩
    rw [hbot] at hv
    simpa only [Submodule.mem_bot, LinearMap.zero_apply] using hv
  have hrangeA_top : LinearMap.range biSA = ⊤ :=
    (eq_bot_or_eq_top (LinearMap.range biSA)).resolve_left hrangeA_ne
  have hsurjA : Function.Surjective biSA :=
    LinearMap.range_eq_top.mp hrangeA_top
  have hsurj : Function.Surjective biSk := hsurjA
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective biSk ⟨hinj, hsurj⟩)

set_option maxHeartbeats 6400000 in
-- The outer budget covers the full biduality construction.
set_option synthInstance.maxHeartbeats 3200000 in
-- The biduality construction combines finite-map and scalar-tower inference.
/-- An equivalence between the centralizer-linear map spaces associated with two simple
submodules yields a linear equivalence of those submodules. -/
theorem Subalgebra.centralizer.linearMapEquiv_implies_linearEquiv
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    (S T : Submodule A E) [IsSimpleModule A S] [IsSimpleModule A T]
    (h : Nonempty ((↥S →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] (↥T →ₗ[A] E))) :
    Nonempty (↥S ≃ₗ[A] ↥T) := by
  classical
  letI : Module.Free k E := Module.Free.of_divisionRing k E
  letI : Module.Free k ↥S := Module.Free.of_divisionRing k ↥S
  letI : Module.Free k ↥T := Module.Free.of_divisionRing k ↥T
  obtain ⟨ψ⟩ := h
  haveI hSfin : Module.Finite k ↥S :=
    Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  haveI hTfin : Module.Finite k ↥T :=
    Module.Finite.of_injective (T.subtype.restrictScalars k) Subtype.val_injective
  haveI : Module.Finite k (↥S →ₗ[k] E) :=
    Module.Finite.linearMap k k ↥S E
  haveI hMSfin : Module.Finite k ((↥S →ₗ[A] E)) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (↥S) E k)
      (LinearMap.restrictScalars_injective _)
  haveI : Module.Finite k (↥T →ₗ[k] E) :=
    Module.Finite.linearMap k k ↥T E
  haveI hMTfin : Module.Finite k ((↥T →ₗ[A] E)) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (↥T) E k)
      (LinearMap.restrictScalars_injective _)
  haveI hDSfin : Module.Finite k
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k
        (Subalgebra.centralizer k (A : Set (Module.End k E)))
        (↥S →ₗ[A] E) E k)
      (LinearMap.restrictScalars_injective _)
  haveI hDTfin : Module.Finite k
      ((↥T →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k
        (Subalgebra.centralizer k (A : Set (Module.End k E)))
        (↥T →ₗ[A] E) E k)
      (LinearMap.restrictScalars_injective _)
  let evS_lin : ↥S →ₗ[k] ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E) :=
    { toFun := fun v =>
        { toFun := fun l => l v
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := fun _ _ => by ext l; simp
      map_smul' := fun r v => by ext l; exact l.map_smul_of_tower r v }
  let evT_lin : ↥T →ₗ[k] ((↥T →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E) :=
    { toFun := fun v =>
        { toFun := fun l => l v
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := fun _ _ => by ext l; simp
      map_smul' := fun r v => by ext l; exact l.map_smul_of_tower r v }
  have hinjS : Function.Injective ⇑evS_lin := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hval : (↑v : E) = 0 := LinearMap.congr_fun hv S.subtype
    exact Subtype.ext (by simpa using hval)
  have hinjT : Function.Injective ⇑evT_lin := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hval : (↑v : E) = 0 := LinearMap.congr_fun hv T.subtype
    exact Subtype.ext (by simpa using hval)
  let semiringK : Semiring k := inferInstance
  let fieldK : Field k := inferInstance
  let ringK : Ring k :=
    { fieldK.toCommRing.toRing with
      toSemiring := semiringK }
  letI : Ring k := ringK
  letI : IsArtinianRing k := DivisionSemiring.instIsArtinianRing
  haveI : IsArtinian k ↥S :=
    isArtinian_of_fg_of_artinian' (R := k) (M := ↥S)
  haveI : IsArtinian k ↥T :=
    isArtinian_of_fg_of_artinian' (R := k) (M := ↥T)
  let auxS := Classical.choice
    (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (Subalgebra.centralizer.finrank_linearMap_eq k E A S).symm)
  let auxT := Classical.choice
    (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (Subalgebra.centralizer.finrank_linearMap_eq k E A T).symm)
  let gS : ↥S →ₗ[k] ↥S := auxS.toLinearMap.comp evS_lin
  let gT : ↥T →ₗ[k] ↥T := auxT.toLinearMap.comp evT_lin
  have hgS_inj : Function.Injective gS := by
    intro x y hxy
    apply hinjS
    apply auxS.injective
    simpa [gS, LinearMap.comp_apply] using hxy
  have hgT_inj : Function.Injective gT := by
    intro x y hxy
    apply hinjT
    apply auxT.injective
    simpa [gT, LinearMap.comp_apply] using hxy
  have hgS_surj : Function.Surjective gS :=
    IsArtinian.surjective_of_injective_endomorphism gS hgS_inj
  have hgT_surj : Function.Surjective gT :=
    IsArtinian.surjective_of_injective_endomorphism gT hgT_inj
  have hsurjS : Function.Surjective evS_lin := by
    intro y
    obtain ⟨x, hx⟩ := hgS_surj (auxS y)
    refine ⟨x, auxS.injective ?_⟩
    simpa [gS, LinearMap.comp_apply] using hx
  have hsurjT : Function.Surjective evT_lin := by
    intro y
    obtain ⟨x, hx⟩ := hgT_surj (auxT y)
    refine ⟨x, auxT.injective ?_⟩
    simpa [gT, LinearMap.comp_apply] using hx
  let evS_k := LinearEquiv.ofBijective evS_lin ⟨hinjS, hsurjS⟩
  let evT_k := LinearEquiv.ofBijective evT_lin ⟨hinjT, hsurjT⟩
  let pre_k := LinearEquiv.linearMapPrecomp k
    (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E ψ.symm
  let Φ : ↥S ≃ₗ[k] ↥T := evS_k.trans (pre_k.trans evT_k.symm)
  have eS : ∀ (w : ↥S) (l : ↥S →ₗ[A] E), evS_k w l = l w := fun _ _ => rfl
  have eT : ∀ (w : ↥T) (m : ↥T →ₗ[A] E), evT_k w m = m w := fun _ _ => rfl
  have eP : ∀ (F : (↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E) (m : ↥T →ₗ[A] E),
      pre_k F m = F (ψ.symm m) :=
    fun _ _ => rfl
  have hΦ : ∀ w : ↥S, evT_k (Φ w) = pre_k (evS_k w) := fun w =>
    evT_k.apply_symm_apply _
  refine ⟨{ toFun := Φ, map_add' := Φ.map_add,
            invFun := Φ.symm, left_inv := Φ.left_inv, right_inv := Φ.right_inv,
            map_smul' := fun a v => ?_ }⟩
  simp only [RingHom.id_apply]
  apply evT_k.injective
  rw [hΦ (a • v)]
  ext m
  have hmv : m (Φ v) = (ψ.symm m) v := by
    have hc := LinearMap.congr_fun (hΦ v) m
    rw [eT (Φ v) m, eP (evS_k v) m, eS v (ψ.symm m)] at hc
    exact hc
  rw [eP (evS_k (a • v)) m, eS (a • v) (ψ.symm m), eT (a • Φ v) m,
    (ψ.symm m).map_smul a v, m.map_smul a (Φ v), hmv]

set_option maxHeartbeats 6400000 in
-- The outer budget covers the biduality reduction at arbitrary indices.
set_option synthInstance.maxHeartbeats 3200000 in
-- Reducing multiplicity-space equivalence to biduality replays the costly inference chain.
/-- For a family of simple submodules with distinct equivalence classes, equivalence of the
associated centralizer-linear map spaces forces the indices to agree. -/
theorem Subalgebra.centralizer.linearMapEquiv_index_eq
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    {ι : Type*} (S' : ι → Submodule A E) [∀ i, IsSimpleModule A (S' i)]
    (hS'_dist : ∀ i j, Nonempty (↥(S' i) ≃ₗ[A] ↥(S' j)) → i = j)
    (i j : ι)
    (h : Nonempty ((↥(S' i) →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] (↥(S' j) →ₗ[A] E))) :
    i = j :=
  hS'_dist i j
    (Subalgebra.centralizer.linearMapEquiv_implies_linearEquiv
      k E A (S' i) (S' j) h)

end RepresentationTheory.Centralizer.LinearMaps
