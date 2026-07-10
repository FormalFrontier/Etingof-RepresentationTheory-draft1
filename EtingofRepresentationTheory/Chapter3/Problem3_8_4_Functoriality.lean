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

/-- The **pushforward of an `S ⊗[K] A`-linear map** along `f : S →ₐ[K] T`, the split-injection
(single-map) analog of `pushEquiv`. Same underlying `T`-linear map `cW ∘ baseChange T gS ∘ cV.symm`
and the same `1 ⊗ a`-commutation argument, but built from a bare linear map so that it can be
applied to a split injection `⟨i, p⟩` and its two functoriality equations (`pushHom_comp`,
`pushHom_id`) transport the splitting relation `p ∘ i = id`. -/
noncomputable def pushHom (f : S →ₐ[K] T)
    (g : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) :
    (T ⊗[K] V) →ₗ[T ⊗[K] A] (T ⊗[K] W) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  -- Reinterpret `g` as an `S`-linear map for the natural `S`-actions.
  let gS : (S ⊗[K] V) →ₗ[S] (S ⊗[K] W) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun s x => by
        simp only [RingHom.id_apply]
        rw [← smul_tmul_one (A := A) s x, LinearMap.map_smul, smul_tmul_one] }
  let cV := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T V
  let cW := TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W
  -- The underlying `T`-linear pushforward.
  let ΦT : (T ⊗[K] V) →ₗ[T] (T ⊗[K] W) :=
    cW.toLinearMap ∘ₗ LinearMap.baseChange T gS ∘ₗ cV.symm.toLinearMap
  have ΦT_tmul : ∀ (t : T) (v : V), ΦT (t ⊗ₜ[K] v) = cW (t ⊗ₜ[S] g (1 ⊗ₜ[K] v)) := by
    intro t v
    simp only [ΦT, LinearMap.comp_apply, LinearEquiv.coe_coe, cV,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul]
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
        show g (1 ⊗ₜ[K] (a • v)) = (1 ⊗ₜ[K] a : S ⊗[K] A) • g (1 ⊗ₜ[K] v) by
          rw [← smul_one_tmul a (1 : S) v, LinearMap.map_smul],
        key]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  -- Upgrade `ΦT` to a `T ⊗[K] A`-linear map.
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

/-- On a pure tensor, `pushHom f g (t ⊗ v) = cW (t ⊗ₛ g (1 ⊗ v))`, where `cW` is the base-change
comparison. This is the defining behaviour, extracted for the functoriality proofs. -/
theorem pushHom_tmul (f : S →ₐ[K] T) (g : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) (t : T) (v : V) :
    letI : Algebra S T := f.toRingHom.toAlgebra
    pushHom f g (t ⊗ₜ[K] v) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W (t ⊗ₜ[S] g (1 ⊗ₜ[K] v)) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  simp only [pushHom, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul]

end Pushforward

section PushforwardFunctorial

variable {U : Type*} [AddCommGroup U] [Module K U] [Module A U] [IsScalarTower K A U]
variable [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]

/-- Behaviour of `pushHom` on the image of the base-change comparison `cV` (source side): it
transports `cV (t ⊗ₛ w)` to `cW (t ⊗ₛ g w)`. This is what makes `pushHom` compose, since
`pushHom f h` lands in such comparison images. -/
theorem pushHom_cancelBaseChange (f : S →ₐ[K] T)
    (g : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) (t : T) (x : S ⊗[K] V) :
    letI : Algebra S T := f.toRingHom.toAlgebra
    pushHom f g (TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T V (t ⊗ₜ[S] x)) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T W (t ⊗ₜ[S] g x) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun y => (f.commutes y).symm
  simp only [pushHom, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

/-- `pushHom` preserves composition. -/
theorem pushHom_comp (f : S →ₐ[K] T)
    (g : (S ⊗[K] W) →ₗ[S ⊗[K] A] (S ⊗[K] U)) (h : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W)) :
    pushHom f (g.comp h) = (pushHom f g).comp (pushHom f h) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t v =>
    simp only [LinearMap.comp_apply, pushHom_tmul, pushHom_cancelBaseChange]
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]

/-- `pushHom` preserves the identity. -/
theorem pushHom_id (f : S →ₐ[K] T) :
    pushHom f (LinearMap.id : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] V)) = LinearMap.id := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  haveI hst : IsScalarTower K S T := .of_algebraMap_eq fun x => (f.commutes x).symm
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t v =>
    simp only [pushHom_tmul, LinearMap.id_coe, id_eq,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/-- **Split-injection pushforward functoriality.** A `K`-algebra hom `f : S →ₐ[K] T` of
commutative `K`-algebras pushes a split injection `⟨i, p⟩` (with `p ∘ i = id`) of base changes
over `S ⊗[K] A` forward to one over `T ⊗[K] A`. -/
theorem nonempty_baseChange_directSummand (f : S →ₐ[K] T)
    (h : ∃ (i : (S ⊗[K] V) →ₗ[S ⊗[K] A] (S ⊗[K] W))
           (p : (S ⊗[K] W) →ₗ[S ⊗[K] A] (S ⊗[K] V)), p.comp i = LinearMap.id) :
    ∃ (i : (T ⊗[K] V) →ₗ[T ⊗[K] A] (T ⊗[K] W))
      (p : (T ⊗[K] W) →ₗ[T ⊗[K] A] (T ⊗[K] V)), p.comp i = LinearMap.id := by
  obtain ⟨i, p, hpi⟩ := h
  refine ⟨pushHom f i, pushHom f p, ?_⟩
  rw [← pushHom_comp f p i, hpi, pushHom_id]

end PushforwardFunctorial

end Etingof.Problem3_8_4.Functoriality
