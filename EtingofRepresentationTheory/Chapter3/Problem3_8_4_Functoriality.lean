import Mathlib

/-!
# Problem 3.8.4: base-change functoriality of the `S ⊗[K] A`-module `S ⊗[K] V`

`Chapter3/Problem3_8_4.lean` builds, for a field extension `L / K`, the `L ⊗[K] A`-module
structure on the base change `L ⊗[K] V`. That construction only ever uses `L` as a commutative
`K`-algebra, so here we redevelop it for an arbitrary commutative `K`-algebra `S` (in the
sub-namespace `Etingof.Problem3_8_4.Functoriality`, to avoid clashing with the field version)
and prove the **pushforward functoriality** that the general-`L` descent proofs of Problem 3.8.4
need:

Given a `K`-algebra homomorphism `f : S →ₐ[K] T` of commutative `K`-algebras, an
`S ⊗[K] A`-linear isomorphism `S ⊗[K] V ≃ S ⊗[K] W` is pushed forward to a `T ⊗[K] A`-linear
isomorphism `T ⊗[K] V ≃ T ⊗[K] W`. The map base-changes the given iso along `f` (viewing `T`
as an `S`-algebra through `f`) and transports it across the canonical comparison
`T ⊗[S] (S ⊗[K] V) ≅ T ⊗[K] V` (`Algebra.TensorProduct.cancelBaseChange`).

The `S ⊗[K] A`-action is `Module.compHom` through the non-canonical `repTensor`, so all
comparisons are checked on pure tensors by unfolding `repTensor` (`smul_one_tmul`,
`smul_tmul_one`), exactly as in `Problem3_8_4_Power.lean`.
-/

open scoped TensorProduct

namespace Etingof.Problem3_8_4.Functoriality

variable {K A V W S T : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]

section OneAlgebra

variable [CommRing S] [Algebra K S]

/-- The representation of `A` on the base change `S ⊗[K] V`, acting `S`-linearly on the right
factor. Generalizes `Etingof.Problem3_8_4.rep` from a field to a commutative `K`-algebra `S`. -/
noncomputable def rep : A →ₐ[K] Module.End S (S ⊗[K] V) :=
  (Module.End.baseChangeHom K S V).comp (Algebra.lsmul K K V)

/-- The `S ⊗[K] A`-representation on `S ⊗[K] V`, from the universal property of base change. -/
noncomputable def repTensor : (S ⊗[K] A) →ₐ[S] Module.End S (S ⊗[K] V) :=
  AlgHom.liftEquiv K S A (Module.End S (S ⊗[K] V)) (rep (A := A) (V := V) (S := S))

/-- The base change `S ⊗[K] V` as a module over `S ⊗[K] A`. Mathlib deliberately does not
register this instance globally (to avoid a scalar-action diamond on `A ⊗[K] A`), so we build
it here for the arbitrary commutative `K`-algebra `S`. -/
noncomputable instance bcMod : Module (S ⊗[K] A) (S ⊗[K] V) :=
  Module.compHom (S ⊗[K] V) (R := Module.End S (S ⊗[K] V))
    (repTensor (A := A) (V := V) (S := S)).toRingHom

/-- The `S ⊗[K] A`-action is application of the representation `repTensor`. -/
theorem bcMod_smul (y : S ⊗[K] A) (x : S ⊗[K] V) :
    (y • x : S ⊗[K] V) = repTensor (A := A) (V := V) (S := S) y x :=
  rfl

/-- `repTensor` sends `1 ⊗ a` to the operator `s ⊗ v ↦ s ⊗ (a • v)`. -/
theorem repTensor_one_tmul_apply (a : A) (s : S) (v : V) :
    repTensor (A := A) (V := V) (S := S) (1 ⊗ₜ[K] a) (s ⊗ₜ[K] v) = s ⊗ₜ[K] (a • v) := by
  rw [repTensor, AlgHom.liftEquiv_tmul, one_smul]
  simp [rep, Module.End.baseChangeHom, LinearMap.baseChange_tmul, Algebra.lsmul_apply]

/-- `A` acts on the base change through the right factor: `(1 ⊗ a) • (s ⊗ v) = s ⊗ (a • v)`. -/
theorem smul_one_tmul (a : A) (s : S) (v : V) :
    ((1 ⊗ₜ[K] a : S ⊗[K] A) • (s ⊗ₜ[K] v) : S ⊗[K] V) = s ⊗ₜ[K] (a • v) := by
  rw [bcMod_smul, repTensor_one_tmul_apply]

/-- Restricting the `S ⊗[K] A`-action along `s ↦ s ⊗ 1` recovers the natural `S`-action:
`(s ⊗ 1) • x = s • x`. -/
theorem smul_tmul_one (s : S) (x : S ⊗[K] V) :
    ((s ⊗ₜ[K] (1 : A) : S ⊗[K] A) • x : S ⊗[K] V) = s • x := by
  rw [bcMod_smul, repTensor, AlgHom.liftEquiv_tmul, map_one]
  rfl

end OneAlgebra

section Pushforward

variable [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]

/-- **Pushforward functoriality.** A `K`-algebra homomorphism `f : S →ₐ[K] T` of commutative
`K`-algebras pushes an `S ⊗[K] A`-linear isomorphism `S ⊗[K] V ≃ S ⊗[K] W` forward to a
`T ⊗[K] A`-linear isomorphism `T ⊗[K] V ≃ T ⊗[K] W`, by base-changing along `f` and transporting
through the comparison `T ⊗[S] (S ⊗[K] V) ≅ T ⊗[K] V`. -/
noncomputable def pushEquiv (f : S →ₐ[K] T)
    (φ : (S ⊗[K] V) ≃ₗ[S ⊗[K] A] (S ⊗[K] W)) :
    (T ⊗[K] V) ≃ₗ[T ⊗[K] A] (T ⊗[K] W) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  -- Reinterpret `φ` as an `S`-linear equivalence for the natural `S`-actions.
  let φS : (S ⊗[K] V) ≃ₗ[S] (S ⊗[K] W) :=
    { toFun := φ
      invFun := φ.symm
      left_inv := φ.left_inv
      right_inv := φ.right_inv
      map_add' := φ.map_add
      map_smul' := fun s x => by
        simp only [RingHom.id_apply]
        rw [← smul_tmul_one (A := A) s x, LinearEquiv.map_smul, smul_tmul_one] }
  -- Comparison isomorphisms `T ⊗[S] (S ⊗[K] ·) ≅ T ⊗[K] ·`.
  let cV := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T V
  let cW := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W
  -- The underlying `T`-linear pushforward.
  let ΦT : (T ⊗[K] V) ≃ₗ[T] (T ⊗[K] W) :=
    cV.symm ≪≫ₗ φS.baseChange S T _ _ ≪≫ₗ cW
  have ΦT_tmul : ∀ (t : T) (v : V), ΦT (t ⊗ₜ[K] v) = cW (t ⊗ₜ[S] φ (1 ⊗ₜ[K] v)) := by
    intro t v
    simp only [ΦT, LinearEquiv.trans_apply, cV,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul]
    rfl
  -- `cW` intertwines the `A`-action on the middle factor with the `A`-action on `T ⊗[K] W`.
  have key : ∀ (a : A) (t : T) (w : S ⊗[K] W),
      cW (t ⊗ₜ[S] ((1 ⊗ₜ[K] a : S ⊗[K] A) • w)) =
        (1 ⊗ₜ[K] a : T ⊗[K] A) • cW (t ⊗ₜ[S] w) := by
    intro a t w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s w0 =>
      simp only [smul_one_tmul, cW,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add x y hx hy =>
      simp only [smul_add, TensorProduct.tmul_add, map_add, hx, hy]
  -- The `A`-action commutes with `ΦT`.
  have hcomm : ∀ (a : A) (x : T ⊗[K] V),
      ΦT ((1 ⊗ₜ[K] a : T ⊗[K] A) • x) = (1 ⊗ₜ[K] a : T ⊗[K] A) • ΦT x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t v =>
      rw [smul_one_tmul, ΦT_tmul, ΦT_tmul,
        show φ (1 ⊗ₜ[K] (a • v)) = (1 ⊗ₜ[K] a : S ⊗[K] A) • φ (1 ⊗ₜ[K] v) by
          rw [← smul_one_tmul a (1 : S) v, LinearEquiv.map_smul],
        key]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  -- Upgrade `ΦT` to a `T ⊗[K] A`-linear equivalence.
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
          rw [hmul, mul_smul, mul_smul, smul_tmul_one, smul_tmul_one,
            LinearEquiv.map_smul, hcomm]
        | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq] }

/-- Existential form of `pushEquiv`: a `K`-algebra hom `f : S →ₐ[K] T` sends the existence of an
`S ⊗[K] A`-iso `S ⊗[K] V ≃ S ⊗[K] W` to the existence of a `T ⊗[K] A`-iso
`T ⊗[K] V ≃ T ⊗[K] W`. -/
theorem nonempty_baseChange_iso (f : S →ₐ[K] T)
    (h : Nonempty ((S ⊗[K] V) ≃ₗ[S ⊗[K] A] (S ⊗[K] W))) :
    Nonempty ((T ⊗[K] V) ≃ₗ[T ⊗[K] A] (T ⊗[K] W)) :=
  h.elim fun φ => ⟨pushEquiv f φ⟩

end Pushforward

section PushMap

variable [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
variable {M N P : Type*}
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
  [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
  [AddCommGroup P] [Module K P] [Module A P] [IsScalarTower K A P]

/-- An `S ⊗[K] A`-linear map between base changes is in particular `S`-linear (restrict the
`S ⊗[K] A`-action along `s ↦ s ⊗ 1`, which recovers the natural `S`-action by `smul_tmul_one`).
The map analog of `pushEquiv`'s internal `φS`. -/
noncomputable def restrictScalarsS (φ : (S ⊗[K] M) →ₗ[S ⊗[K] A] (S ⊗[K] N)) :
    (S ⊗[K] M) →ₗ[S] (S ⊗[K] N) where
  toFun := φ
  map_add' := φ.map_add
  map_smul' s x := by
    simp only [RingHom.id_apply]
    rw [← smul_tmul_one (A := A) s x, φ.map_smul, smul_tmul_one]

@[simp]
theorem restrictScalarsS_apply (φ : (S ⊗[K] M) →ₗ[S ⊗[K] A] (S ⊗[K] N)) (x : S ⊗[K] M) :
    restrictScalarsS φ x = φ x := rfl

/-- **Pushforward of an `S ⊗[K] A`-linear map.** A `K`-algebra homomorphism `f : S →ₐ[K] T`
of commutative `K`-algebras pushes an `S ⊗[K] A`-linear map `S ⊗[K] M → S ⊗[K] N` forward to a
`T ⊗[K] A`-linear map `T ⊗[K] M → T ⊗[K] N`, by base-changing along `f` and transporting through
the comparison `T ⊗[S] (S ⊗[K] ·) ≅ T ⊗[K] ·`. The map analog of `pushEquiv`. -/
noncomputable def pushMap (f : S →ₐ[K] T) (φ : (S ⊗[K] M) →ₗ[S ⊗[K] A] (S ⊗[K] N)) :
    (T ⊗[K] M) →ₗ[T ⊗[K] A] (T ⊗[K] N) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  let cM := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T M
  let cN := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T N
  let ΦT : (T ⊗[K] M) →ₗ[T] (T ⊗[K] N) :=
    cN.toLinearMap ∘ₗ (LinearMap.baseChange T (restrictScalarsS φ)) ∘ₗ cM.symm.toLinearMap
  have ΦT_tmul : ∀ (t : T) (m : M), ΦT (t ⊗ₜ[K] m) = cN (t ⊗ₜ[S] φ (1 ⊗ₜ[K] m)) :=
    fun _ _ => rfl
  -- `cN` intertwines the `A`-action on the middle factor with the `A`-action on `T ⊗[K] N`.
  have key : ∀ (a : A) (t : T) (w : S ⊗[K] N),
      cN (t ⊗ₜ[S] ((1 ⊗ₜ[K] a : S ⊗[K] A) • w)) =
        (1 ⊗ₜ[K] a : T ⊗[K] A) • cN (t ⊗ₜ[S] w) := by
    intro a t w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s w0 =>
      simp only [smul_one_tmul, cN,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add x y hx hy =>
      simp only [smul_add, TensorProduct.tmul_add, map_add, hx, hy]
  have hcomm : ∀ (a : A) (x : T ⊗[K] M),
      ΦT ((1 ⊗ₜ[K] a : T ⊗[K] A) • x) = (1 ⊗ₜ[K] a : T ⊗[K] A) • ΦT x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      rw [smul_one_tmul, ΦT_tmul, ΦT_tmul,
        show φ (1 ⊗ₜ[K] (a • m)) = (1 ⊗ₜ[K] a : S ⊗[K] A) • φ (1 ⊗ₜ[K] m) by
          rw [← smul_one_tmul a (1 : S) m, φ.map_smul],
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
          rw [hmul, mul_smul, mul_smul, smul_tmul_one, smul_tmul_one,
            LinearMap.map_smul, hcomm]
        | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq] }

/-- `pushMap` sends the identity to the identity. -/
theorem pushMap_id (f : S →ₐ[K] T) :
    pushMap f (LinearMap.id : (S ⊗[K] M) →ₗ[S ⊗[K] A] (S ⊗[K] M)) = LinearMap.id := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t m =>
    change TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T M
        (t ⊗ₜ[S] (1 ⊗ₜ[K] m)) = LinearMap.id (t ⊗ₜ[K] m)
    simp only [LinearMap.id_coe, id_eq,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `pushMap` is functorial: it sends a composite to the composite of pushforwards. -/
theorem pushMap_comp (f : S →ₐ[K] T) (φ : (S ⊗[K] M) →ₗ[S ⊗[K] A] (S ⊗[K] N))
    (ψ : (S ⊗[K] N) →ₗ[S ⊗[K] A] (S ⊗[K] P)) :
    pushMap f (ψ.comp φ) = (pushMap f ψ).comp (pushMap f φ) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  -- The pushforward of `ψ` on an element of the form `cN (t ⊗ₜ[S] y)` reads off `ψ y`.
  have hcN : ∀ (t : T) (y : S ⊗[K] N),
      pushMap f ψ (TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T N (t ⊗ₜ[S] y)) =
        TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T P (t ⊗ₜ[S] ψ y) := by
    intro t y
    show TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T P
        ((LinearMap.baseChange T (restrictScalarsS ψ))
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T N).symm
            (TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T N (t ⊗ₜ[S] y)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, restrictScalarsS_apply]
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t m =>
    -- Both `pushMap`s evaluate on pure tensors by `rfl` through `cancelBaseChange`.
    change TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T P
        (t ⊗ₜ[S] ψ (φ (1 ⊗ₜ[K] m))) =
      pushMap f ψ (TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T N
        (t ⊗ₜ[S] φ (1 ⊗ₜ[K] m)))
    rw [hcN]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

/-- Existential pushforward of a **split injection** (direct-summand witness): a `K`-algebra hom
`f : S →ₐ[K] T` sends a `S ⊗[K] A`-split injection `S ⊗[K] V → S ⊗[K] W` (a pair `(i, p)` with
`p ∘ i = id`) to a `T ⊗[K] A`-split injection `T ⊗[K] V → T ⊗[K] W`. -/
theorem exists_baseChange_directSummand (f : S →ₐ[K] T)
    (h : ∃ (i : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W))
           (p : (S ⊗[K] W) →ₗ[S ⊗[K] A] (S ⊗[K] V)), p.comp i = LinearMap.id) :
    ∃ (i : (T ⊗[K] V) →ₗ[T ⊗[K] A] (T ⊗[K] W))
      (p : (T ⊗[K] W) →ₗ[T ⊗[K] A] (T ⊗[K] V)), p.comp i = LinearMap.id := by
  obtain ⟨i, p, hpi⟩ := h
  refine ⟨pushMap f i, pushMap f p, ?_⟩
  rw [← pushMap_comp, hpi, pushMap_id]

end PushMap

end Etingof.Problem3_8_4.Functoriality
