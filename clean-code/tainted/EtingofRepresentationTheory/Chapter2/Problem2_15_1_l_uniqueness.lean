import EtingofRepresentationTheory.Chapter2.Sl2JordanTypeIso

/-!
# Jacobson–Morozov for `sl(2)`: uniqueness and the full part-(l) statement (Problem 2.15.1(l))

Etingof Problem 2.15.1(l) is the `sl(2)` special case of the Jacobson–Morozov lemma: for a
finite dimensional complex vector space `V` and a nilpotent operator `A : V → V` there is a
representation of `sl(2)` on `V` with `E = A`, **unique up to isomorphism**.

Existence (`exists_sl2Rep_of_nilpotent`) is established in `Problem2_15_1_l.lean`. This file
supplies the *uniqueness* half and bundles the two into the full statement, closing the
problem:

* `sl2Rep_unique_of_e_eq`: any two `sl(2)`-representations `ρ, ρ'` on `V` with the same
  raising operator `ρ e = ρ' e` are isomorphic as `sl(2)`-modules.
* `jacobsonMorozov_sl2`: existence and uniqueness for a nilpotent `A`.

An `sl(2)`-representation is a bundled Lie hom `ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V`, whereas the
key input `sl2Rep_iso_of_e_jordanType_eq` (from `Sl2JordanTypeIso.lean`, itself resting on
the classification of representations and the `sl₂` complete-reducibility results) is phrased
for the `LieRingModule`/`LieModule` typeclass structure. `RepOf ρ` relates the two: it is
the space `V` carrying the `sl(2)`-module structure pulled back along `ρ`
(`LieRingModule.compLieHom`, `⁅x, m⁆ = ρ x m`), so its raising operator is exactly `ρ e`
(`raising_repOf`). Two representations with the same `ρ e` then have literally equal raising
operators, hence the same nullity sequence `k ↦ dim ker (E^k)`, so the two modules are
`sl(2)`-isomorphic.
-/

open Etingof
open Etingof.Sl2Irrep

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Etingof.Sl2Irrep

section Uniqueness

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The space `V` equipped with the `sl(2)`-module structure defined by the representation
`ρ` (the pullback along `ρ` of the tautological `Module.End`-action, `⁅x, m⁆ = ρ x m`). -/
-- The index `ρ` intentionally distinguishes the module structures even though the carrier
-- reduces to `V`.
@[nolint unusedArguments]
def RepOf (_ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V) : Type _ := V

namespace RepOf

variable (ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V)

instance : AddCommGroup (RepOf ρ) := inferInstanceAs (AddCommGroup V)
instance : Module ℂ (RepOf ρ) := inferInstanceAs (Module ℂ V)
/-- Finite dimensionality is preserved when a representation is bundled as `RepOf`. -/
instance [FiniteDimensional ℂ V] : FiniteDimensional ℂ (RepOf ρ) :=
  inferInstanceAs (FiniteDimensional ℂ V)
noncomputable instance : LieRingModule sl2 (RepOf ρ) := LieRingModule.compLieHom V ρ
/-- The scalar-compatible Lie action on `RepOf ρ`. -/
instance : LieModule ℂ sl2 (RepOf ρ) := LieModule.compLieHom V ρ

/-- The raising operator of `RepOf ρ` is exactly `ρ e`. -/
theorem raising_repOf : raising (RepOf ρ) = ρ sl2_e := by
  ext m
  change LieModule.toEnd ℂ sl2 (RepOf ρ) sl2_e m = ρ sl2_e m
  rw [LieModule.toEnd_apply_apply]
  rfl

end RepOf

open RepOf in
/-- **Uniqueness (Problem 2.15.1(l)).** On a finite dimensional complex vector space `V`,
any two `sl(2)`-representations `ρ, ρ'` with the same raising operator `ρ e = ρ' e` are
isomorphic as `sl(2)`-modules. In particular this applies to two `sl(2)`-structures with
`E = A` for a fixed (nilpotent) operator `A`. -/
theorem sl2Rep_unique_of_e_eq [FiniteDimensional ℂ V]
    (ρ ρ' : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V) (h : ρ sl2_e = ρ' sl2_e) :
    Nonempty (RepOf ρ ≃ₗ⁅ℂ,sl2⁆ RepOf ρ') := by
  refine sl2Rep_iso_of_e_jordanType_eq (fun k => ?_)
  rw [raising_repOf, raising_repOf, h]
  rfl

/-- **Jacobson–Morozov for `sl(2)` (Etingof Problem 2.15.1(l)), full statement.** For a
finite dimensional complex vector space `V` and a nilpotent operator `A : V → V` there is an
`sl(2)`-representation with `E = A` (existence), and any two such representations are
isomorphic as `sl(2)`-modules (uniqueness up to isomorphism). -/
theorem jacobsonMorozov_sl2 [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (hA : IsNilpotent A) :
    (∃ ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V, ρ sl2_e = A) ∧
      (∀ ρ ρ' : sl2 →ₗ⁅ℂ⁆ Module.End ℂ V, ρ sl2_e = A → ρ' sl2_e = A →
        Nonempty (RepOf ρ ≃ₗ⁅ℂ,sl2⁆ RepOf ρ')) :=
  ⟨exists_sl2Rep_of_nilpotent A hA,
    fun ρ ρ' hρ hρ' => sl2Rep_unique_of_e_eq ρ ρ' (hρ.trans hρ'.symm)⟩

end Uniqueness

end Etingof.Sl2Irrep
