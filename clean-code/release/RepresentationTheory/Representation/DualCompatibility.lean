import Mathlib
import RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

set_option linter.style.longLine false

noncomputable section

namespace RepresentationTheory.Representation.DualCompatibility

open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

variable {k : Type*} [CommRing k] {G V : Type*} [Group G] [AddCommGroup V] [Module k V]

/-- Dualizing the displayed representation construction equals applying it to the inverse unit-valued character and the dual representation. -/
theorem dual_construction_eq_construction_inv_dual (c : G →* kˣ) (ρ : Representation k G V) :
    Representation.dual (twistByCharacter c ρ) = twistByCharacter c⁻¹ (Representation.dual ρ) := by
  ext g f v
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    twistByCharacter_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  congr 1
  rw [map_inv, MonoidHom.inv_apply]

end RepresentationTheory.Representation.DualCompatibility
