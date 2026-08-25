import Mathlib

/-!
# Definition 5.8.1: Induced Representation

Let `H` be a subgroup of `G` and `V` a representation of `H`. The **induced representation**
`Ind_H^G V` is the representation of `G` that Etingof describes by the function-space model

  `Ind_H^G V = {f : G → V | f(h x) = ρ_V(h) f(x) for all h ∈ H, x ∈ G}`

with the `G`-action `(g · f)(x) = f(x g)`.

## Mathlib correspondence

Mathlib's `Representation.coind H.subtype ρ` is literally the book's function-space model.
It also ships the tensor model `Representation.ind H.subtype ρ`, the `H`-coinvariants of
`ℂ[G] ⊗_ℂ V` and the left adjoint of restriction.

For a finite-index subgroup the two models agree naturally (`Rep.indCoindIso`).  The book's
literal object is exposed below as `Definition5_8_1_functionSpace`; the traditional Chapter 5
name `Definition5_8_1` retains the tensor model only under the finite-index hypothesis, and
`Definition5_8_1_iso_functionSpace` records the canonical identification.

Properties (proved downstream): `dim(Ind_H^G V) = [G : H] · dim(V)`.
-/

open Representation

/-- Mathlib's unrestricted tensor/coinvariant induction.  This is the left adjoint of restriction
for arbitrary subgroups; it is kept as a companion for results, such as induction in stages, that
belong to the tensor model without any finite-index assumption. -/
noncomputable def Etingof.inducedTensorModel
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.IndV H.subtype ρ) :=
  Representation.ind H.subtype ρ

/-- The tensor realization of the induced representation `Ind_H^G V`, available under the
finite-index hypothesis where it agrees with Etingof's function-space definition.  Concretely the
underlying module is
`Representation.IndV H.subtype ρ`, the `H`-coinvariants of `ℂ[G] ⊗_ℂ V`, with `G` acting on the
`ℂ[G]` factor.
(Etingof Definition 5.8.1) -/
noncomputable def Etingof.Definition5_8_1
    {G : Type*} [Group G]
    (H : Subgroup G) [H.FiniteIndex]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.IndV H.subtype ρ) :=
  Etingof.inducedTensorModel H ρ

/-- **Definition 5.8.1, literally.** The function-space representation
`{f : G → V | f (h * x) = ρ(h) (f x)}`, with action `(g • f)(x) = f(x * g)`.
It agrees with the tensor model under finite index, but is the book's definition for arbitrary
subgroups. -/
noncomputable def Etingof.Definition5_8_1_functionSpace
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.coindV H.subtype ρ) :=
  Representation.coind H.subtype ρ

/-- A function belongs to the carrier of Definition 5.8.1 exactly when it satisfies the book's
covariance equation. -/
theorem Etingof.mem_Definition5_8_1_functionSpace
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G → V) :
    f ∈ Representation.coindV H.subtype ρ ↔
      ∀ (h : H) (x : G), f (h * x) = ρ h (f x) :=
  Representation.mem_coindV H.subtype ρ f

/-- Membership in the function-space model is exactly the covariance equation from the book. -/
theorem Etingof.Definition5_8_1_functionSpace_condition
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V)
    (f : Representation.coindV H.subtype ρ) (h : H) (x : G) :
    f.val (h * x) = ρ h (f.val x) :=
  f.prop h x

/-- The `G`-action in the function-space model is right translation: `(g • f)(x) = f(xg)`. -/
@[simp]
theorem Etingof.Definition5_8_1_functionSpace_apply
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V)
    (g : G) (f : Representation.coindV H.subtype ρ) (x : G) :
    (Etingof.Definition5_8_1_functionSpace H ρ g f).val x = f.val (x * g) :=
  rfl

/-- The identity element acts trivially in the function-space model. -/
@[simp]
theorem Etingof.Definition5_8_1_functionSpace_one
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : Representation.coindV H.subtype ρ) :
    Etingof.Definition5_8_1_functionSpace H ρ 1 f = f := by
  rw [map_one]
  rfl

/-- Successive right translations give the action of the product. -/
theorem Etingof.Definition5_8_1_functionSpace_mul
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (g g' : G)
    (f : Representation.coindV H.subtype ρ) :
    Etingof.Definition5_8_1_functionSpace H ρ (g * g') f =
      Etingof.Definition5_8_1_functionSpace H ρ g
        (Etingof.Definition5_8_1_functionSpace H ρ g' f) := by
  rw [map_mul]
  rfl

/-- For finite-index `H`, the tensor realization used in the rest of finite-group Chapter 5 is
canonically isomorphic to the book's literal function-space realization. -/
noncomputable def Etingof.Definition5_8_1_iso_functionSpace
    {G : Type*} [Group G]
    (H : Subgroup G) [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Rep.of (Etingof.Definition5_8_1 H ρ) ≅
      Rep.of (Etingof.Definition5_8_1_functionSpace H ρ) :=
  Rep.indCoindIso (Rep.of ρ)
