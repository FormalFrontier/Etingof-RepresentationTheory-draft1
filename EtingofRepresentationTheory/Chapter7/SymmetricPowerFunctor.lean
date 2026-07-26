import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Functoriality of the symmetric tensor power

Mathlib's `SymmetricPower` (`Sym[R] ι M`) is defined as a quotient of the tensor power
`⨂[R] (_ : ι), M`, but it carries no action on linear maps: the file
`Mathlib/LinearAlgebra/TensorPower/Symmetric.lean` lists the universal property as future
work, and there is no `SymmetricPower.map`. Example 7.2.2(8) of Etingof asserts that
`V ↦ SⁿV` is a functor `Vect_k → Vect_k`, so the missing action is exactly what has to be
supplied.

This file supplies it, for an arbitrary index type `ι` rather than just `Fin n`:

* `SymmetricPower.map f : Sym[R] ι M →ₗ[R] Sym[R] ι N` for `f : M →ₗ[R] N`, descending
  `PiTensorProduct.map (fun _ => f)` through the symmetrising quotient;
* `SymmetricPower.map_id` and `SymmetricPower.map_comp`, the functor laws;
* `SymmetricPower.functor R ι : ModuleCat R ⥤ ModuleCat R`, the packaged functor, and
  `ModuleCat.symmetricPower.functor R n` for the `n`-th symmetric power.

The project's `Etingof.symmetricPowerMap` (`Chapter5/Example5_19_3.lean`) is the special
case of `SymmetricPower.map` for an endomorphism of a finite-dimensional space over a
field; it predates this file and is left in place, since a large amount of Chapter 5
depends on it definitionally.
-/

open scoped TensorProduct

namespace SymmetricPower

universe u v w x

variable {R ι : Type u} [CommSemiring R]
  {M : Type v} [AddCommMonoid M] [Module R M]
  {N : Type w} [AddCommMonoid N] [Module R N]
  {P : Type x} [AddCommMonoid P] [Module R P]

/-- Two linear maps out of a symmetric power agree as soon as they agree on the image of
the quotient map `mk`, which is surjective. -/
theorem linearMap_ext {Q : Type*} [AddCommMonoid Q] [Module R Q]
    {f g : Sym[R] ι M →ₗ[R] Q}
    (h : ∀ x : ⨂[R] (_ : ι), M, f (mk R ι M x) = g (mk R ι M x)) : f = g := by
  ext x
  exact AddCon.induction_on x h

/-- The functorial action of a linear map `f : M →ₗ[R] N` on symmetric powers.

It is the descent of the diagonal tensor-power map `f ⊗ ⋯ ⊗ f` through the symmetrising
quotient: this is legitimate because permuting the factors of a pure tensor commutes with
applying `f` in every slot. -/
noncomputable def map (f : M →ₗ[R] N) : Sym[R] ι M →ₗ[R] Sym[R] ι N :=
  let F : (⨂[R] (_ : ι), M) →+ Sym[R] ι N :=
    (AddCon.mk' _).comp (PiTensorProduct.map (fun _ : ι => f)).toAddMonoidHom
  { toFun := AddCon.lift _ F (fun x y h => Quotient.sound (by
      induction h with
      | of x y h => cases h with
        | perm e g =>
          simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.map_tprod]
          exact AddConGen.Rel.of _ _ (SymmetricPower.Rel.perm e (fun i => f (g i)))
      | refl => exact AddCon.refl _ _
      | symm _ ih => exact AddCon.symm _ ih
      | trans _ _ ih₁ ih₂ => exact AddCon.trans _ ih₁ ih₂
      | add _ _ ih₁ ih₂ => simp only [map_add]; exact AddCon.add _ ih₁ ih₂))
    map_add' := fun x y => by
      refine AddCon.induction_on₂ x y (fun a b => ?_)
      change mk R ι N (PiTensorProduct.map (fun _ : ι => f) (a + b))
        = mk R ι N (PiTensorProduct.map (fun _ : ι => f) a)
          + mk R ι N (PiTensorProduct.map (fun _ : ι => f) b)
      rw [map_add, map_add]
    map_smul' := fun r x => by
      refine AddCon.induction_on x (fun a => ?_)
      change mk R ι N (PiTensorProduct.map (fun _ : ι => f) (r • a))
        = r • mk R ι N (PiTensorProduct.map (fun _ : ι => f) a)
      rw [map_smul, map_smul] }

@[simp] theorem map_mk (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
    map (ι := ι) f (mk R ι M x) = mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) :=
  rfl

@[simp] theorem map_tprod (f : M →ₗ[R] N) (g : ι → M) :
    map (ι := ι) f (⨂ₛ[R] i, g i) = ⨂ₛ[R] i, f (g i) := by
  change map (ι := ι) f (mk R ι M (PiTensorProduct.tprod R g)) = _
  rw [map_mk, PiTensorProduct.map_tprod]
  rfl

@[simp] theorem map_id : map (ι := ι) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  refine linearMap_ext fun x => ?_
  rw [map_mk, PiTensorProduct.map_id]
  rfl

theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map (ι := ι) (g ∘ₗ f) = map (ι := ι) g ∘ₗ map (ι := ι) f := by
  refine linearMap_ext fun x => ?_
  rw [map_mk, LinearMap.comp_apply, map_mk, map_mk,
    show (fun _ : ι => g ∘ₗ f) = fun i : ι => (fun _ : ι => g) i ∘ₗ (fun _ : ι => f) i from rfl,
    PiTensorProduct.map_comp]
  rfl

@[simp] theorem map_comp_apply (g : N →ₗ[R] P) (f : M →ₗ[R] N) (x : Sym[R] ι M) :
    map (ι := ι) (g ∘ₗ f) x = map (ι := ι) g (map (ι := ι) f x) := by
  rw [map_comp]; rfl

end SymmetricPower

namespace ModuleCat

open CategoryTheory

universe u v

/-- The `ι`-indexed symmetric-power functor `M ↦ Sym[R] ι M` on `ModuleCat R`.

The index type `ι` must live in the same universe as `R`, because that is how
`SymmetricPower` is set up in Mathlib; the carriers may live anywhere above it. -/
noncomputable def symmetricPowerFunctor (R : Type u) [CommRing R] (ι : Type u) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R (Sym[R] ι M)
  map f := ModuleCat.ofHom (SymmetricPower.map (ι := ι) f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact SymmetricPower.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact SymmetricPower.map_comp _ _

/-- The `n`-th symmetric-power functor `V ↦ SⁿV` on `ModuleCat R`: Etingof's
Example 7.2.2(8), the companion of `ModuleCat.exteriorPower.functor`. -/
noncomputable abbrev symmetricPower (R : Type) [CommRing R] (n : ℕ) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  symmetricPowerFunctor R (Fin n)

end ModuleCat
