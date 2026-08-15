/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! Character duality for finite commutative groups. -/

/-- A finite simple representation of a finite commutative group over an algebraically closed field has dimension one. -/
@[source_ref "Chapter4/Example4.3_FiniteAbelianGroups" (role := primary)]
theorem RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [CommGroup G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V)
    [hirr : IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Module.finrank k V = 1 := by
  
  have : IsMulCommutative (MonoidAlgebra k G) := ⟨⟨mul_comm⟩⟩
  
  
  
  have h : Module.finrank k ρ.asModule = 1 :=
    IsSimpleModule.finrank_eq_one_of_isMulCommutative
      (k := k) (A := MonoidAlgebra k G) (V := ρ.asModule)
  rwa [ρ.asModuleEquiv.finrank_eq] at h

namespace RepresentationTheory.Group.CharacterDuality

/-- The character group of a commutative group. -/
@[source_ref "Chapter4/Example4.3_FiniteAbelianGroups" (role := supporting)]
abbrev characterGroup (G : Type*) [CommGroup G] : Type _ := G →* ℂˣ

example (G : Type*) [CommGroup G] : CommGroup (characterGroup G) := inferInstance

/-- The complex numbers have enough roots of unity for the exponent of a finite group. -/
instance hasEnoughRootsOfUnity_exponent (G : Type*) [Group G] [Finite G] :
    HasEnoughRootsOfUnity ℂ (Monoid.exponent G) :=
  have : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := G)⟩
  inferInstance

/-- The character group of a product is multiplicatively equivalent to the product of character groups. -/
@[source_ref "Chapter4/Example4.3_FiniteAbelianGroups" (role := primary)]
def characterGroupProdEquiv (G₁ G₂ : Type*) [CommGroup G₁] [CommGroup G₂] :
    characterGroup (G₁ × G₂) ≃* characterGroup G₁ × characterGroup G₂ where
  toFun φ := (φ.comp (.inl G₁ G₂), φ.comp (.inr G₁ G₂))
  invFun p := p.1.comp (.fst G₁ G₂) * p.2.comp (.snd G₁ G₂)
  left_inv φ := by
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, b⟩ := x
    change φ (a, 1) * φ (1, b) = φ (a, b)
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  right_inv p := by
    refine Prod.ext (DFunLike.ext _ _ fun a => ?_) (DFunLike.ext _ _ fun a => ?_)
    · change p.1 a * p.2 1 = p.1 a
      rw [map_one, mul_one]
    · change p.1 1 * p.2 a = p.2 a
      rw [map_one, one_mul]
  map_mul' φ ψ := Prod.ext rfl rfl

/-- The character group of a finite product is multiplicatively equivalent to the displayed product of character groups. -/
@[source_ref "Chapter4/Example4.3_FiniteAbelianGroups" (role := primary)]
def characterGroupPiEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)] :
    characterGroup (∀ i, G i) ≃* ∀ i, characterGroup (G i) :=
  Pi.monoidHomMulEquiv G ℂˣ

/-- A finite commutative group is multiplicatively equivalent to its character group. -/
@[source_ref "Chapter4/Example4.3_FiniteAbelianGroups" (role := primary)]
theorem nonempty_characterGroupEquiv (G : Type*) [CommGroup G] [Finite G] :
    Nonempty (G ≃* characterGroup G) :=
  (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).map MulEquiv.symm

/-- A finite commutative group is multiplicatively equivalent to the character group of its character group. -/
@[source_ref "Chapter4/Example4.3_FiniteAbelianGroups" (role := primary)]
noncomputable def characterGroupDualEquiv (G : Type*) [CommGroup G] [Finite G] :
    G ≃* characterGroup (characterGroup G) :=
  (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm

/-- The double-character equivalence has the displayed value at a group element and character. -/
@[simp, source_ref "Chapter4/Example4.3_FiniteAbelianGroups" (role := primary)]
theorem characterGroupDualEquiv_apply (G : Type*) [CommGroup G] [Finite G]
    (g : G) (χ : characterGroup G) :
    characterGroupDualEquiv G g χ = χ g :=
  CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply G ℂ g χ

end RepresentationTheory.Group.CharacterDuality
