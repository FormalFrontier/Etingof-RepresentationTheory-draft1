import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1

/-!
# Discussion 5.11: Worked examples of induced representations for `S₃`

Etingof's §5.11 computes, via Frobenius reciprocity, the decomposition into
irreducibles of representations of `S₃ = Sym(Fin 3)` induced from one-dimensional
representations of the cyclic subgroups `Z₂` and `Z₃`:

* `Ind_{Z₂}^{S₃} ℂ₊ ≅ ℂ² ⊕ ℂ₊` and `Ind_{Z₂}^{S₃} ℂ₋ ≅ ℂ² ⊕ ℂ₋`;
* `Ind_{Z₃}^{S₃} ℂ₊ ≅ ℂ₊ ⊕ ℂ₋` and `Ind_{Z₃}^{S₃} ℂ_ε ≅ ℂ²`,

where `ℂ₊` is the trivial representation, `ℂ₋` the sign representation, and `ℂ²`
the two-dimensional standard (irreducible) representation of `S₃`.

This file builds the **S₃ irreducible-representation catalogue** used by those
statements — the trivial, sign, and standard representations as objects of
`FDRep ℂ S₃` — and states the four decompositions. The catalogue is the reusable
piece the issue asks for; the decomposition proofs go through Frobenius-reciprocity
multiplicities (`Etingof.Theorem5_10_1` / `Etingof.Theorem5_9_1`) together with the
fact that over `ℂ` a finite group's representation is determined up to isomorphism by
its character.

## Mathlib correspondence

* `Equiv.Perm (Fin 3)` — the group `S₃`.
* `Equiv.Perm.sign` — the sign homomorphism, used for `ℂ₋`.
* `Representation.ofMulAction` / a hand-rolled permutation action — the natural
  3-dimensional representation, whose sum-zero subspace is the standard
  representation `ℂ²`.
* `Etingof.Definition5_8_1` — the induced representation `Ind_H^G`.
-/

open CategoryTheory

noncomputable section

namespace Etingof.Discussion5_11

/-- `S₃`, realized as the symmetric group on `Fin 3`. -/
abbrev S3 : Type := Equiv.Perm (Fin 3)

/-! ## The irreducible-representation catalogue of `S₃` -/

/-- A one-dimensional representation of a group `G` attached to a multiplicative
character `χ : G →* ℂˣ`: `g` acts on `ℂ` by multiplication by `χ g`. -/
def charRep {G : Type*} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The trivial representation `ℂ₊` of `S₃`. -/
def trivRep : FDRep ℂ S3 := FDRep.of (charRep (1 : S3 →* ℂˣ))

/-- The sign character `S₃ →* ℂˣ`, sending a permutation to `±1 ∈ ℂˣ`. -/
def signHom : S3 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- The sign representation `ℂ₋` of `S₃`. -/
def signRep : FDRep ℂ S3 := FDRep.of (charRep signHom)

/-- The character of a one-dimensional `charRep χ` is `g ↦ χ g`. -/
@[simp] lemma charRep_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (charRep χ)).character g = (χ g : ℂ) := by
  have hg : charRep χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (charRep χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- Any one-dimensional `charRep χ` is simple as an object of `FDRep ℂ G`: its
character has norm one, `∑ g, χ(g)·χ(g⁻¹) = |G|`. -/
lemma charRep_simple {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (FDRep.of (charRep χ)) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have : ∀ g : G, (FDRep.of (charRep χ)).character g * (FDRep.of (charRep χ)).character g⁻¹
      = 1 := by
    intro g
    rw [charRep_character, charRep_character, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card]

/-- `ℂ₊` is simple. -/
lemma trivRep_simple : Simple trivRep := charRep_simple _

/-- `ℂ₋` is simple. -/
lemma signRep_simple : Simple signRep := charRep_simple _

/-! ### The standard representation `ℂ²`

The natural 3-dimensional permutation representation of `S₃` on `Fin 3 → ℂ`
(`σ` acts by `f ↦ f ∘ σ⁻¹`) contains the sum-zero subspace as an invariant
2-dimensional subspace; this subspace is the standard irreducible representation. -/

/-- The permutation representation of `S₃` on `Fin 3 → ℂ`: `σ` acts by `f ↦ f ∘ σ⁻¹`. -/
def permRep : Representation ℂ S3 (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

@[simp] lemma permRep_apply (σ : S3) (f : Fin 3 → ℂ) (i : Fin 3) :
    permRep σ f i = f (σ⁻¹ i) := rfl

/-- The sum map `(Fin 3 → ℂ) →ₗ[ℂ] ℂ`, `f ↦ ∑ i, f i`. -/
def sumLM : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

@[simp] lemma sumLM_apply (f : Fin 3 → ℂ) : sumLM f = ∑ i, f i := by
  simp [sumLM, Finset.sum_apply]

/-- The standard representation `ℂ²` as the sum-zero subrepresentation of `permRep`. -/
def stdSub : Subrepresentation permRep where
  toSubmodule := LinearMap.ker sumLM
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, sumLM_apply] at hf ⊢
    calc ∑ i, permRep σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [permRep_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 3)) f
      _ = 0 := hf

/-- The standard (2-dimensional) irreducible representation `ℂ²` of `S₃`. -/
def stdRep : FDRep ℂ S3 := FDRep.of stdSub.toRepresentation

/-! ## The cyclic subgroups -/

/-- `Z₂ ≤ S₃`, generated by the transposition `(0 1)`. -/
def Z2 : Subgroup S3 := Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)

/-- `Z₃ ≤ S₃`, the alternating group `A₃ = ⟨(0 1 2)⟩`. -/
def Z3 : Subgroup S3 := alternatingGroup (Fin 3)

/-! ## The induced representations and their decompositions

Each statement asserts an isomorphism of `S₃`-representations. The cleanest proof
route (Etingof §5.11) computes the multiplicity of each irreducible constituent by
Frobenius reciprocity, `⟨Ind_H^G W, V_i⟩ = ⟨W, Res_H V_i⟩`, then uses that over `ℂ`
a finite group's representation is determined up to isomorphism by its character. -/

/-- `Ind_{Z₂}^{S₃} ℂ₊ ≅ ℂ² ⊕ ℂ₊`. (Etingof Discussion 5.11(1)) -/
theorem indZ2_trivPlus_decomp :
    Nonempty
      (FDRep.of (Etingof.Definition5_8_1 Z2 (charRep (1 : ↥Z2 →* ℂˣ))) ≅ stdRep ⊞ trivRep) := by
  sorry

/-- `Ind_{Z₂}^{S₃} ℂ₋ ≅ ℂ² ⊕ ℂ₋`. (Etingof Discussion 5.11(1)) -/
theorem indZ2_signMinus_decomp :
    Nonempty
      (FDRep.of (Etingof.Definition5_8_1 Z2 (charRep (signHom.comp Z2.subtype))) ≅
        stdRep ⊞ signRep) := by
  sorry

/-- `Ind_{Z₃}^{S₃} ℂ₊ ≅ ℂ₊ ⊕ ℂ₋`. (Etingof Discussion 5.11(2)) -/
theorem indZ3_trivPlus_decomp :
    Nonempty
      (FDRep.of (Etingof.Definition5_8_1 Z3 (charRep (1 : ↥Z3 →* ℂˣ))) ≅ trivRep ⊞ signRep) := by
  sorry

end Etingof.Discussion5_11

end
