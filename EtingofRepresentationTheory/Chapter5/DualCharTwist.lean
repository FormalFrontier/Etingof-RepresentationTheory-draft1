import Mathlib
import EtingofRepresentationTheory.Chapter5.KernelLemmaKPrime

/-!
# The dual of a character twist

This file records the reusable representation-theoretic identity relating the linear dual
`Representation.dual` (Mathlib) to the character twist `charTwistRep`
(`Chapter5/KernelLemmaKPrime.lean`):

* `dual_charTwistRep` — for a character `c : G →* kˣ` and a representation `ρ`,
  `Representation.dual (charTwistRep c ρ) = charTwistRep c⁻¹ (Representation.dual ρ)`.

The dual negates the group element (`(dual σ) g = transpose (σ g⁻¹)`), so the twisting
scalar `c g` of `charTwistRep c ρ` is read at `g⁻¹`, i.e. as `c(g⁻¹) = c⁻¹(g)`. Combined
with `charTwistRep_charTwistRep` this collapses a stacked `det^s`-twist on a contragredient
into a single twist by the inverse-power determinant character — the form consumed by the
linear-dual half of the contragredient identity (#5544).
-/

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

variable {k : Type*} [CommRing k] {G V : Type*} [Group G] [AddCommGroup V] [Module k V]

/-- **The dual of a character twist is the dual twisted by the inverse character.** Since the
dual representation reads the group element at `g⁻¹`
(`(dual σ) g = transpose (σ g⁻¹)`), the twisting scalar of `charTwistRep c ρ` becomes
`c(g⁻¹) = c⁻¹(g)`, so `dual (charTwistRep c ρ) = charTwistRep c⁻¹ (dual ρ)`. -/
theorem dual_charTwistRep (c : G →* kˣ) (ρ : Representation k G V) :
    Representation.dual (charTwistRep c ρ) = charTwistRep c⁻¹ (Representation.dual ρ) := by
  ext g f v
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    charTwistRep_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  congr 1
  rw [map_inv, MonoidHom.inv_apply]

end Etingof
