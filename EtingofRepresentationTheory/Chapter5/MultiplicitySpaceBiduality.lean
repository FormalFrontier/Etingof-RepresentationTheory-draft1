import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_1

/-!
# Multiplicity-space biduality and `C`-distinctness (Schur-Weyl, Part 2)

For a semisimple subalgebra `A ⊆ End_k(E)` acting faithfully on a
finite-dimensional `k`-vector space `E` (`k` algebraically closed), let
`C = centralizer(A)` be the commutant. Each simple `A`-submodule `S ≤ E`
has a **multiplicity space** `M_S := ↥S →ₗ[A] E`, which is a simple
`C`-module (post-composition action, `Theorem5_18_1.isSimpleModule_homA_centralizer`).

This file proves **Part 2** of the Schur-Weyl GL-side distinctness output
(parent #4849, reducing #4731's `glTensorRep_equivariant_schurWeyl_decomposition`):
a `C`-linear iso of multiplicity spaces forces the underlying simple
`A`-modules to coincide,

  `M_{S_i} ≃ₗ[C] M_{S_j}  ⟹  i = j`,

given the `A`-side distinctness `hS'_dist : S_i ≃ₗ[A] S_j → i = j` produced by
`Theorem5_18_4_bimodule_decomposition_explicit`.

## Strategy — biduality (double-centralizer reflexivity)

The crux is the natural `A`-linear iso (symmetric double centralizer / biduality)

  `bidualityMap_S : ↥S ≃ₗ[A] (M_S →ₗ[C] E)`,

the curried evaluation `v ↦ (l ↦ l v)`. Given a `C`-iso `ψ : M_{S_i} ≃ₗ[C] M_{S_j}`,
precomposition `(- ∘ ψ.symm)` is an `A`-linear iso
`(M_{S_i} →ₗ[C] E) ≃ₗ[A] (M_{S_j} →ₗ[C] E)`; threading the two biduality maps
gives `S_i ≃ₗ[A] S_j`, whence `i = j` by `hS'_dist`.

The reusable `k`-linear precomposition congruence `homCongrLeftOverSubring`
(mirror of `Theorem5_18_1.homCongrRightOverSubring`) is proved here. The
biduality iso itself is the research core, isolated as
`multiplicitySpace_biduality_Aiso`.
-/

open scoped TensorProduct

universe u v

namespace Etingof

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- Pre-composition equivalence: an `R`-linear equivalence of the **domain**
induces a `k`-linear equivalence of hom-spaces (contravariantly). This is the
domain-side mirror of `homCongrRightOverSubring`, and like it works for
non-commutative `R` (where `LinearEquiv.congrLeft` does not apply directly). -/
noncomputable def homCongrLeftOverSubring
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

/-- Restricting a simple `S`-module along a **surjective** ring homomorphism
`σ : R →+* S` (with the `R`-action obtained by `σ`-restriction, `r • x = σ r • x`)
keeps it simple: the `R`- and `S`-submodules coincide because every `S`-scalar is
a `σ`-image. This is the transport tool for the double-centralizer identification
`centralizer(centralizer A) = A`, where the inclusion `↥A → ↥(centralizer C)` is a
bijective (hence surjective) ring hom. -/
theorem isSimpleModule_of_surjective_ringHom
    {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) [RingHomSurjective σ]
    {X : Type*} [AddCommGroup X] [Module R X] [Module S X]
    (hcompat : ∀ (r : R) (x : X), r • x = σ r • x)
    [IsSimpleModule S X] : IsSimpleModule R X :=
  (LinearMap.isSimpleModule_iff_of_bijective
    ({ toFun := id, map_add' := fun _ _ => rfl,
        map_smul' := fun r x => (hcompat r x) } : X →ₛₗ[σ] X)
    Function.bijective_id).mpr ‹_›

-- Heartbeats bumped: even synthesizing the `SMul (↥centralizer A) (V →ₗ[A] E)`
-- in this instance's statement runs the deep `centralizerModuleHom`
-- `Subalgebra → Module.End` chain, overrunning the default 20000 synth budget
-- (same root cause as `centralizerModuleHom` / `_smulCommClass`).
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The centralizer post-composition action on `V →ₗ[A] E` forms a scalar tower
with the pointwise `k`-action: `(r • b) • f = r • (b • f)`. This is the
`IsScalarTower` companion of `centralizerModuleHom_smulCommClass`, needed so
that `centralizerModuleHom` can fire a *second* time (with `C` in the `A`-slot)
on the double hom-space `(↥S →ₗ[A] E) →ₗ[C] E`. -/
instance centralizerModuleHom_isScalarTower
    {A : Subalgebra k (Module.End k E)}
    {V : Type*} [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    IsScalarTower k (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) where
  smul_assoc r b f := by
    refine LinearMap.ext fun v => ?_
    change (r • b).val (f v) = r • (b.val (f v))
    rw [Subalgebra.coe_smul, LinearMap.smul_apply]

-- Heartbeats bumped: the `Module ↥(centralizer A) (↥S →ₗ[A] E)` instance
-- (`Theorem5_18_1.centralizerModuleHom`, a `Subalgebra → Module.End` chain)
-- needed to even state the `≃ₗ[C]` overruns the default 20000 synth /
-- 200000 elaboration budgets, exactly as in `SchurWeylLDistinct` / `Theorem5_18_1`.
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Multiplicity-matching dimension count (isolated research core).**
For a simple `A`-submodule `S ≤ E` of a faithful semisimple `A`-module over an
algebraically closed field, the `k`-dimension of `S` equals that of the double
hom-space `(M_S →ₗ[C] E)`, where `M_S := ↥S →ₗ[A] E` and `C = centralizer(A)`.

This is the only genuinely-deep ingredient of biduality: matching the `A`-side
bimodule decomposition `E ≅ ⨁ V_i ⊗ (V_i →ₗ[A] E)` against the symmetric
`C`-side decomposition (`Theorem5_18_1_bimodule_decomposition_explicit` with `C`
in the `A`-slot). Concretely `dim_k M_S = mult_C(M_S in E)` (Schur over `C`,
alg-closed) and `mult_C(M_S in E) = dim_k S` (the `A`-side multiplicity equals
`dim V_{i0}` since the `M_{V_i}` are pairwise non-isomorphic simple `C`-modules).

Once this holds, the curried-evaluation biduality map `↥S → (M_S →ₗ[C] E)`
(`v ↦ (l ↦ l v)`), which is injective by construction, becomes an isomorphism
by equal finite dimension — see `multiplicitySpace_biduality_Aiso`. -/
theorem multiplicitySpace_double_hom_finrank
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    (S : Submodule A E) [IsSimpleModule A S] :
    Module.finrank k ↥S =
      Module.finrank k ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
        (A : Set (Module.End k E))] E) := by
  classical
  -- Semisimplicity facts on both sides.
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI hCss : IsSemisimpleRing (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
    Theorem5_18_1_commutant_semisimple k E A
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  -- `M_S := ↥S →ₗ[A] E` is a simple `C`-module (`C = centralizer A`).
  haveI hMS : IsSimpleModule (Subalgebra.centralizer k (A : Set (Module.End k E)))
      (↥S →ₗ[A] E) := isSimpleModule_homA_centralizer k E A S
  -- Pick a nonzero `s0 ∈ S`.
  haveI : Nontrivial ↥S := IsSimpleModule.nontrivial A ↥S
  obtain ⟨s0, hs0⟩ := exists_ne (0 : ↥S)
  -- Evaluation at `s0`: a nonzero `C`-linear map `M_S → E`, hence injective.
  let evs0 : (↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E :=
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
  -- Its range `W` is a simple `C`-submodule of `E`, `C`-iso to `M_S`.
  let W : Submodule (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    LinearMap.range evs0
  let eMW : (↥S →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] ↥W :=
    LinearEquiv.ofInjective evs0 hinjE
  haveI hWsimple : IsSimpleModule (Subalgebra.centralizer k (A : Set (Module.End k E))) ↥W :=
    IsSimpleModule.congr eMW.symm
  -- `W →ₗ[C] E` is simple over `centralizer C` (`= A`).
  haveI hWE : IsSimpleModule
      (Subalgebra.centralizer k
        ((Subalgebra.centralizer k (A : Set (Module.End k E))) : Set (Module.End k E)))
      (↥W →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    isSimpleModule_homA_centralizer k E (Subalgebra.centralizer k (A : Set (Module.End k E))) W
  -- Transport simplicity to the double-hom space along precomposition with `eMW`.
  let preD : (↥W →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E)
      ≃ₗ[Subalgebra.centralizer k
        ((Subalgebra.centralizer k (A : Set (Module.End k E))) : Set (Module.End k E))]
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    { toFun := fun f => f.comp eMW.toLinearMap
      invFun := fun f => f.comp eMW.symm.toLinearMap
      left_inv := fun f => by ext m; simp
      right_inv := fun f => by ext m; simp
      map_add' := fun f g => by ext m; simp
      map_smul' := fun b f => by ext m; rfl }
  haveI hsimpD : IsSimpleModule
      (Subalgebra.centralizer k
        ((Subalgebra.centralizer k (A : Set (Module.End k E))) : Set (Module.End k E)))
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    IsSimpleModule.congr preD.symm
  -- Double centralizer: `centralizer C = A`. Build the (bijective) inclusion ring hom
  -- `↥A → ↥(centralizer C)` and transport simplicity down to `A`.
  have hCC : Subalgebra.centralizer k
      ((Subalgebra.centralizer k (A : Set (Module.End k E))) : Set (Module.End k E)) = A :=
    Theorem5_18_1_double_centralizer k E A
  have hAle : A ≤ Subalgebra.centralizer k
      ((Subalgebra.centralizer k (A : Set (Module.End k E))) : Set (Module.End k E)) :=
    le_of_eq hCC.symm
  let σ : (↥A) →+* ↥(Subalgebra.centralizer k
      ((Subalgebra.centralizer k (A : Set (Module.End k E))) : Set (Module.End k E))) :=
    (Subalgebra.inclusion hAle).toRingHom
  haveI hσsurj : RingHomSurjective σ :=
    ⟨fun y => ⟨⟨y.val, hCC.le y.2⟩, Subtype.ext rfl⟩⟩
  letI instA : Module (↥A)
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    Module.compHom _ σ
  haveI hsimpA : IsSimpleModule (↥A)
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    isSimpleModule_of_surjective_ringHom σ (fun _ _ => rfl)
  -- The curried-evaluation map `v ↦ (l ↦ l v)`, both as a `k`-map and an `A`-map.
  let ev : ↥S → ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    fun v =>
    { toFun := fun l => l v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let biSk : ↥S →ₗ[k]
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    { toFun := ev
      map_add' := fun v w => by ext l; exact l.map_add v w
      map_smul' := fun c v => by ext l; exact l.map_smul_of_tower c v }
  let biSA : ↥S →ₗ[A]
      ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))] E) :=
    { toFun := ev
      map_add' := fun v w => by ext l; exact l.map_add v w
      map_smul' := fun a v => by
        ext l
        show l (a • v) = (σ a).val (l v)
        rw [l.map_smul a v]; rfl }
  -- `biSk` is injective (evaluating at `S.subtype` recovers `↑v`).
  have hinj : Function.Injective biSk := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : (v : E) = 0 := by
      have := LinearMap.congr_fun hv S.subtype
      simpa [biSk, ev] using this
    exact Subtype.ext (by simpa using h1)
  -- `biSA` is nonzero, hence surjective by Schur (target simple over `A`).
  have hbiSA_ne : biSA ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : ↥S)
    intro h
    apply hv
    have hv0 : biSk v = 0 := by
      have : biSA v = 0 := by rw [h]; rfl
      exact this
    exact (injective_iff_map_eq_zero biSk).mp hinj v hv0
  have hsurjA : Function.Surjective biSA :=
    LinearMap.surjective_of_ne_zero hbiSA_ne
  have hsurj : Function.Surjective biSk := hsurjA
  -- Equal `k`-dimension via the resulting `k`-linear equivalence.
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective biSk ⟨hinj, hsurj⟩)

-- Heartbeats bumped: stating and proving over the double hom-space
-- `(↥S →ₗ[A] E) →ₗ[C] E` runs the deep `centralizerModuleHom`
-- `Subalgebra → Module.End` instance chain (twice), overrunning the default
-- 20000 synth / 200000 elaboration budgets, as in `Theorem5_18_1`.
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Biduality (research core).** For a simple `A`-submodule `S ≤ E` of a
faithful semisimple `A`-module, the curried evaluation
`↥S → (M_S →ₗ[C] E)`, `v ↦ (l ↦ l v)`, is an `A`-linear isomorphism, where
`M_S := ↥S →ₗ[A] E` and `C = centralizer(A)`. Consequently a `C`-iso of
multiplicity spaces yields an `A`-iso of the underlying simple modules.

This is the symmetric double-centralizer / biduality statement. The proof builds
the `k`-linear curried-evaluation equivalences `↥S ≃ₗ[k] (M_S →ₗ[C] E)` and
`↥T ≃ₗ[k] (M_T →ₗ[C] E)` (injective by construction, bijective by the
dimension count `multiplicitySpace_double_hom_finrank`), threads the given
`C`-iso `M_S ≃ₗ[C] M_T` through the precomposition congruence
`homCongrLeftOverSubring`, and verifies that the resulting `k`-linear bijection
`↥S ≃ₗ[k] ↥T` is in fact `A`-linear (post-composition by `a ∈ A` commutes with
both the evaluation and the `C`-linear precomposition). -/
theorem multiplicitySpace_biduality_Aiso
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    (S T : Submodule A E) [IsSimpleModule A S] [IsSimpleModule A T]
    (h : Nonempty ((↥S →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))]
      (↥T →ₗ[A] E))) :
    Nonempty (↥S ≃ₗ[A] ↥T) := by
  classical
  obtain ⟨ψ⟩ := h
  -- `k`-finiteness of all the hom-spaces involved (sub-objects of finite
  -- `k`-vector spaces).
  haveI hSfin : Module.Finite k ↥S :=
    Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  haveI hTfin : Module.Finite k ↥T :=
    Module.Finite.of_injective (T.subtype.restrictScalars k) Subtype.val_injective
  haveI hMSfin : Module.Finite k ((↥S →ₗ[A] E)) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (↥S) E k)
      (LinearMap.restrictScalars_injective _)
  haveI hMTfin : Module.Finite k ((↥T →ₗ[A] E)) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (↥T) E k)
      (LinearMap.restrictScalars_injective _)
  haveI hDSfin : Module.Finite k ((↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k (Subalgebra.centralizer k (A : Set (Module.End k E)))
        (↥S →ₗ[A] E) E k)
      (LinearMap.restrictScalars_injective _)
  haveI hDTfin : Module.Finite k ((↥T →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k (Subalgebra.centralizer k (A : Set (Module.End k E)))
        (↥T →ₗ[A] E) E k)
      (LinearMap.restrictScalars_injective _)
  -- The `k`-linear curried-evaluation maps `v ↦ (l ↦ l v)` into the double
  -- hom-space.  The inner map is `C`-linear; the outer is `k`-linear.
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
  -- Both evaluation maps are injective: evaluating at `S.subtype` recovers `↑v`.
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
  -- Equal finite `k`-dimension upgrades the injections to `k`-linear equivs.
  let evS_k := LinearEquiv.ofInjectiveOfFinrankEq evS_lin hinjS
    (multiplicitySpace_double_hom_finrank k E A S)
  let evT_k := LinearEquiv.ofInjectiveOfFinrankEq evT_lin hinjT
    (multiplicitySpace_double_hom_finrank k E A T)
  -- Precomposition by the given `C`-iso `ψ : M_S ≃ₗ[C] M_T` (use `ψ.symm` so the
  -- direction is `D_S → D_T`).
  let pre_k := homCongrLeftOverSubring k
    (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E ψ.symm
  -- The threaded `k`-linear bijection.
  let Φ : ↥S ≃ₗ[k] ↥T := evS_k.trans (pre_k.trans evT_k.symm)
  -- Application formulas (all definitional).
  have eS : ∀ (w : ↥S) (l : ↥S →ₗ[A] E), evS_k w l = l w := fun _ _ => rfl
  have eT : ∀ (w : ↥T) (m : ↥T →ₗ[A] E), evT_k w m = m w := fun _ _ => rfl
  have eP : ∀ (F : (↥S →ₗ[A] E) →ₗ[Subalgebra.centralizer k
      (A : Set (Module.End k E))] E) (m : ↥T →ₗ[A] E), pre_k F m = F (ψ.symm m) :=
    fun _ _ => rfl
  -- `evT_k ∘ Φ = pre_k ∘ evS_k`.
  have hΦ : ∀ w : ↥S, evT_k (Φ w) = pre_k (evS_k w) := fun w =>
    evT_k.apply_symm_apply _
  -- `Φ` is `A`-linear: package as a `↥A`-linear equivalence.
  refine ⟨{ toFun := Φ, map_add' := Φ.map_add,
            invFun := Φ.symm, left_inv := Φ.left_inv, right_inv := Φ.right_inv,
            map_smul' := fun a v => ?_ }⟩
  simp only [RingHom.id_apply]
  apply evT_k.injective
  rw [hΦ (a • v)]
  ext m
  -- Key compatibility: `m (Φ v) = (ψ.symm m) v`.
  have hmv : m (Φ v) = (ψ.symm m) v := by
    have hc := LinearMap.congr_fun (hΦ v) m
    rw [eT (Φ v) m, eP (evS_k v) m, eS v (ψ.symm m)] at hc
    exact hc
  rw [eP (evS_k (a • v)) m, eS (a • v) (ψ.symm m), eT (a • Φ v) m,
    (ψ.symm m).map_smul a v, m.map_smul a (Φ v), hmv]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Part 2: multiplicity-space `C`-distinctness.** Given a family `S'` of
simple `A`-submodules of `E` that are pairwise `A`-distinct (`hS'_dist`), a
`C`-linear isomorphism of multiplicity spaces `M_{S'_i} ≃ₗ[C] M_{S'_j}` forces
`i = j`. Here `A` is a semisimple subalgebra of `End_k(E)` acting faithfully,
`k` is algebraically closed, and `C = centralizer(A)`.

This is the B-side distinctness consumed by parent #4849: it upgrades the
multiplicity-space iso produced by Part 1 to the index identity needed to
complete the GL-equivariant Schur-Weyl decomposition. -/
theorem multiplicitySpace_Cdistinct
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] [FaithfulSMul A E] [IsAlgClosed k]
    {ι : Type*} (S' : ι → Submodule A E) [∀ i, IsSimpleModule A (S' i)]
    (hS'_dist : ∀ i j, Nonempty (↥(S' i) ≃ₗ[A] ↥(S' j)) → i = j)
    (i j : ι)
    (h : Nonempty ((↥(S' i) →ₗ[A] E) ≃ₗ[Subalgebra.centralizer k (A : Set (Module.End k E))]
      (↥(S' j) →ₗ[A] E))) :
    i = j :=
  hS'_dist i j (multiplicitySpace_biduality_Aiso k E A (S' i) (S' j) h)

end Etingof
