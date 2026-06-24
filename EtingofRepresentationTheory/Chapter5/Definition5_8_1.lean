import Mathlib

/-!
# Definition 5.8.1: Induced Representation

Let `H` be a subgroup of `G` and `V` a representation of `H`. The **induced representation**
`Ind_H^G V` is the representation of `G` that Etingof describes by the function-space model

  `Ind_H^G V = {f : G → V | f(h x) = ρ_V(h) f(x) for all h ∈ H, x ∈ G}`

with the `G`-action `(g · f)(x) = f(x g)`.

## Mathlib correspondence

Mathlib ships a general induced representation `Representation.ind` (and its packaged form
`Rep.ind`) built as the tensor model `(k[G] ⊗_k V)_H`, the `H`-coinvariants of `k[G] ⊗_k V`,
with the `G`-action defined by sending `h : G` and `⟦h₁ ⊗ₜ v⟧` to `⟦h₁ h⁻¹ ⊗ₜ v⟧`. We realize
`Ind_H^G V` as `Representation.ind H.subtype ρ`, induction along the subgroup inclusion
`H.subtype : H →* G`.

The tensor model used here is the *left* adjoint of restriction; Etingof's function-space model
`{f : G → V | f(h x) = ρ(h) f(x)}` is literally the *coinduced* representation `Rep.coind`. For
finite groups the two agree (`Rep.indCoindIso`), so this is the same `Ind_H^G V`.

Properties (proved downstream): `dim(Ind_H^G V) = [G : H] · dim(V)`.
-/

open Representation

/-- The induced representation `Ind_H^G V` of a representation `ρ : Representation ℂ H V` of a
subgroup `H ≤ G`, realized via Mathlib's general induction `Representation.ind` along the subgroup
inclusion `H.subtype : H →* G`. Concretely the underlying module is
`Representation.IndV H.subtype ρ`, the `H`-coinvariants of `ℂ[G] ⊗_ℂ V`, with `G` acting on the
`ℂ[G]` factor.
(Etingof Definition 5.8.1) -/
noncomputable def Etingof.Definition5_8_1
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.IndV H.subtype ρ) :=
  Representation.ind H.subtype ρ
