import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1
import EtingofRepresentationTheory.Chapter5.DihedralCharacterCombinatorics
import EtingofRepresentationTheory.Chapter5.AbelianFDRep
import EtingofRepresentationTheory.Chapter5.Exercise5_27_2_Transport

/-!
# Exercise 5.27.2 (dihedral group): redo Problem 4.12.1(a) using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the **Problem 4.12.1(a)** part: describe all irreducible complex
representations of the dihedral group `D_N`, the symmetry group of a regular `N`-gon (order
`2N`), distinguishing the cases of odd and even `N`.

## The dihedral group as a semidirect product

`D_N = ⟨r, s | rᴺ = s² = 1, s r s⁻¹ = r⁻¹⟩` is the semidirect product of the cyclic rotation
group `A = ⟨r⟩ ≅ ℤ/N` (abelian, normal) by the order-two reflection group `G = ⟨s⟩ ≅ ℤ/2`,
where `s` acts on `A` by inversion `r ↦ r⁻¹`. So `Theorem 5.27.1` (the orbit method for
`A ⋊ G` with `A` abelian) applies with `A = Multiplicative (ZMod N)`, `G = Multiplicative
(ZMod 2)`, and `φ` sending the reflection to the inversion automorphism.

We state the classification for Mathlib's `DihedralGroup N` (the concrete group of `N`-gon
symmetries); the docstrings record how Theorem 5.27.1 produces it. The dual `G`-action on
`Â = A →* ℂˣ ≅ ℤ/N` is again inversion `χ ↦ χ⁻¹`, so the orbits are:

* the fixed characters (`χ = χ⁻¹`), whose stabilizer is all of `G`; each contributes two
  `1`-dimensional irreducibles (one per character of `G ≅ ℤ/2`);
* the free orbit-pairs `{χ, χ⁻¹}` with `χ ≠ χ⁻¹`, whose stabilizer is trivial; each
  contributes one `2`-dimensional irreducible `V(χ, U)` of dimension `[G : G_χ] = 2`.

The number of fixed characters is `gcd(2, N)`: for `N` odd only `χ = 1` is fixed (one
character, two `1`-dim irreps), and for `N` even both `χ = 1` and the order-two character
are fixed (two characters, four `1`-dim irreps). The remaining `N - gcd(2,N)` nontrivial
characters split into `(N - gcd(2,N))/2` free orbit-pairs, giving that many `2`-dimensional
irreducibles.

## The classification (Problem 4.12.1(a))

* `N` odd: `2` irreducibles of dimension `1` and `(N-1)/2` of dimension `2`
  (`∑ dim² = 2 + 4·(N-1)/2 = 2N`);
* `N` even: `4` irreducibles of dimension `1` and `(N-2)/2` of dimension `2`
  (`∑ dim² = 4 + 4·(N-2)/2 = 2N`).

Both `semidirect_classification` (the semidirect-product model) and `dihedral_classification`
(Mathlib's `DihedralGroup N`) follow from the orbit method of Theorem 5.27.1.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Module

namespace Etingof.Exercise5_27_2

variable (N : ℕ) [NeZero N]

/-! ## The dihedral group as a semidirect product `⟨r⟩ ⋊ ⟨s⟩`

We realize `DihedralGroup N` as `Multiplicative (ZMod N) ⋊[dihedralφ N] Multiplicative (ZMod 2)`,
with the reflection generator acting on the rotation group by inversion `a ↦ a⁻¹`. -/

/-- Inversion `a ↦ a⁻¹` as an automorphism of the abelian rotation group `Multiplicative (ZMod N)`. -/
def invAut : MulAut (Multiplicative (ZMod N)) := MulEquiv.inv (Multiplicative (ZMod N))

omit [NeZero N] in
@[simp] lemma invAut_apply (a : Multiplicative (ZMod N)) : invAut N a = a⁻¹ := rfl

omit [NeZero N] in
lemma invAut_mul_self : invAut N * invAut N = 1 := by
  ext a; simp

/-- The action of the reflection group `Multiplicative (ZMod 2)` on the rotation group
`Multiplicative (ZMod N)`: the nontrivial element acts by inversion `a ↦ a⁻¹`. -/
def dihedralφ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod N)) :=
  MonoidHom.mk' (fun g => if Multiplicative.toAdd g = 0 then 1 else invAut N) <| by
    intro a b
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    simp only [toAdd_mul]
    rcases h2 (Multiplicative.toAdd a) with ha | ha <;>
      rcases h2 (Multiplicative.toAdd b) with hb | hb <;> simp only [ha, hb]
    · simp
    · simp
    · simp
    · exact (invAut_mul_self N).symm

omit [NeZero N] in
@[simp] lemma dihedralφ_one_apply (a : Multiplicative (ZMod N)) :
    (dihedralφ N (1 : Multiplicative (ZMod 2))) a = a := by
  simp only [dihedralφ, MonoidHom.mk'_apply]
  rw [if_pos]; · rfl
  rfl

omit [NeZero N] in
@[simp] lemma dihedralφ_ofAdd_one_apply (a : Multiplicative (ZMod N)) :
    (dihedralφ N (Multiplicative.ofAdd (1 : ZMod 2))) a = a⁻¹ := by
  simp only [dihedralφ, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [if_neg (by decide)]; rfl

/-- The semidirect-product realization of the dihedral group `D_N`. -/
abbrev DihedralSemidirect : Type := Multiplicative (ZMod N) ⋊[dihedralφ N] Multiplicative (ZMod 2)

/-- The group isomorphism `D_N ≅ ⟨r⟩ ⋊ ⟨s⟩` realizing Mathlib's concrete
`DihedralGroup N` as the semidirect product of the rotation group `Multiplicative (ZMod N)` by
the reflection group `Multiplicative (ZMod 2)` acting by inversion. On generators
`r i ↦ ⟨ofAdd i, 1⟩` and `sr i ↦ ⟨ofAdd (-i), ofAdd 1⟩`. -/
def dihedralEquiv : DihedralGroup N ≃* DihedralSemidirect N where
  toFun x := match x with
    | .r i => ⟨Multiplicative.ofAdd i, 1⟩
    | .sr i => ⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd (1 : ZMod 2)⟩
  invFun p :=
    if Multiplicative.toAdd p.right = 0
    then DihedralGroup.r (Multiplicative.toAdd p.left)
    else DihedralGroup.sr (- Multiplicative.toAdd p.left)
  left_inv x := by
    cases x with
    | r i => simp
    | sr i => simp [(by decide : (1 : ZMod 2) ≠ 0)]
  right_inv p := by
    obtain ⟨a, g⟩ := p
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases h2 (Multiplicative.toAdd g) with hg | hg
    · have : g = 1 := by
        rw [← ofAdd_toAdd g, hg]; rfl
      subst this; simp
    · have : g = Multiplicative.ofAdd (1 : ZMod 2) := by
        rw [← ofAdd_toAdd g, hg]
      subst this
      simp only [toAdd_ofAdd, (by decide : (1 : ZMod 2) ≠ 0), if_false, neg_neg,
        ofAdd_toAdd]
  map_mul' x y := by
    cases x <;> cases y <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;>
      apply SemidirectProduct.ext <;>
      simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, ← ofAdd_neg, ← ofAdd_add,
        sub_eq_add_neg, add_comm, show (1 : ZMod 2) + 1 = 0 from by decide, ofAdd_zero]

/-! ## Transport of representation classifications along a group isomorphism

Restriction of scalars along `dihedralEquiv N` is an equivalence of representation categories
`FDRep ℂ (DihedralSemidirect N) ≌ FDRep ℂ (DihedralGroup N)`. The machinery for moving a
classification across such an equivalence — `repEquiv`, `transport_classification` and
`filter_finrank_congr` — lives in `Chapter5/Exercise5_27_2_Transport.lean`, shared with the
Heisenberg and affine arms of this exercise. -/

/-- Restriction of scalars along `dihedralEquiv N`: the equivalence of representation categories
`FDRep ℂ (⟨r⟩ ⋊ ⟨s⟩) ≌ FDRep ℂ (D_N)`. -/
def dihedralRepEquiv :
    FDRep ℂ (DihedralSemidirect N) ≌ FDRep ℂ (DihedralGroup N) :=
  repEquiv (dihedralEquiv N)

omit [NeZero N] in
/-- The transport functor keeps the underlying vector space, so it preserves dimension. -/
lemma finrank_dihedralRepEquiv_functor (V : FDRep ℂ (DihedralSemidirect N)) :
    finrank ℂ ((dihedralRepEquiv N).functor.obj V : Type) = finrank ℂ (V : Type) := rfl

open Classical in
/-- **Classification on the semidirect-product model.** The classification stated on the
semidirect-product model `⟨r⟩ ⋊ ⟨s⟩`, before transporting back to Mathlib's `DihedralGroup N`.
This is the orbit-method content of Theorem 5.27.1 applied to the inversion action, together with the
`gcd(2,N)` fixed-character / `(N-gcd(2,N))/2` free-orbit count. -/
theorem semidirect_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (DihedralSemidirect N)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (DihedralSemidirect N), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = 2) ∧
      (Odd N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 2 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 1) / 2) ∧
      (Even N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 4 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 2) / 2) := by
  classical
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport, hi, hii, hiii, hiv, hv, hvi,
      hvii, hviii, hix⟩ :=
    Etingof.Theorem5_27_1 (Multiplicative (ZMod 2)) (Multiplicative (ZMod N)) (dihedralφ N)
  -- The reflection generator is self-inverse in `ℤ/2`.
  have hgen_inv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
  -- **Dual action is inversion.** The generator acts on characters by `χ ↦ χ⁻¹`.
  have hdual_gen : ∀ χ : Multiplicative (ZMod N) →* ℂˣ,
      dualSmul (Multiplicative.ofAdd 1) χ = χ⁻¹ := by
    intro χ
    refine MonoidHom.ext (fun a => ?_)
    rw [hdual, hgen_inv, dihedralφ_ofAdd_one_apply, map_inv, MonoidHom.inv_apply]
  -- The identity fixes every character.
  have hdual_one : ∀ χ : Multiplicative (ZMod N) →* ℂˣ,
      dualSmul (1 : Multiplicative (ZMod 2)) χ = χ := by
    intro χ
    refine MonoidHom.ext (fun a => ?_)
    rw [hdual, inv_one, dihedralφ_one_apply]
  -- **Stabilizer.** `χ` is fixed by the generator iff it is self-inverse.
  have hstab_gen : ∀ χ : Multiplicative (ZMod N) →* ℂˣ,
      (Multiplicative.ofAdd 1 ∈ stab χ) ↔ χ⁻¹ = χ := by
    intro χ; rw [hstab χ (Multiplicative.ofAdd 1), hdual_gen]
  -- Every element of `Multiplicative (ZMod 2)` is the identity or the reflection generator.
  have hG2 : ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = Multiplicative.ofAdd 1 := by
    intro g
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (Multiplicative.toAdd g) with h | h
    · left; rw [← ofAdd_toAdd g, h]; rfl
    · right; rw [← ofAdd_toAdd g, h]
  -- **Stabilizer dichotomy.** `stab χ = ⊤` when `χ` is self-inverse, `⊥` otherwise.
  have hstab_top : ∀ χ : Multiplicative (ZMod N) →* ℂˣ, χ⁻¹ = χ → stab χ = ⊤ := by
    intro χ hχ
    rw [eq_top_iff]; intro g _
    rcases hG2 g with rfl | rfl
    · exact one_mem _
    · exact (hstab_gen χ).mpr hχ
  have hstab_bot : ∀ χ : Multiplicative (ZMod N) →* ℂˣ, χ⁻¹ ≠ χ → stab χ = ⊥ := by
    intro χ hχ
    rw [eq_bot_iff]; intro g hg
    rcases hG2 g with rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exact absurd ((hstab_gen χ).mp hg) hχ
  -- Fintype instances for the character groups.
  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype (Multiplicative (ZMod 2) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} := Fintype.ofFinite _
  -- `Multiplicative (ZMod 2)` has exactly two elements.
  have hcardG2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  -- **Dimension of the family members.**
  have hdim_self : ∀ (χ : Multiplicative (ZMod N) →* ℂˣ), χ⁻¹ = χ →
      ∀ ρ : Multiplicative (ZMod 2) →* ℂˣ,
      finrank ℂ (V χ (Etingof.AbelianFDRep.charFDRep (ρ.comp (stab χ).subtype)) : Type) = 1 := by
    intro χ hχ ρ
    rw [hv, hstab_top χ hχ, Subgroup.index_top, Etingof.AbelianFDRep.charFDRep_finrank, mul_one]
  have hdim_free : ∀ (χ : Multiplicative (ZMod N) →* ℂˣ), χ⁻¹ ≠ χ →
      finrank ℂ (V χ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ) →* ℂˣ)) : Type) = 2 := by
    intro χ hχ
    rw [hv, hstab_bot χ hχ, Subgroup.index_bot, Etingof.AbelianFDRep.charFDRep_finrank, mul_one,
      hcardG2]
  -- **A concrete injective key**, to choose orbit representatives for the inversion involution.
  let key : (Multiplicative (ZMod N) →* ℂˣ) → ℕ := fun χ => (Fintype.equivFin _ χ).val
  have key_inj : Function.Injective key := fun a b h =>
    (Fintype.equivFin (Multiplicative (ZMod N) →* ℂˣ)).injective (Fin.val_injective h)
  have hinv_inv (χ : Multiplicative (ZMod N) →* ℂˣ) : χ⁻¹⁻¹ = χ := by
    ext a
    simp
  -- **The free-orbit transversal**: one representative per pair `{χ, χ⁻¹}` with `χ ≠ χ⁻¹`.
  let T := {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹ ∧ key χ < key χ⁻¹}
  haveI : Fintype T := Fintype.ofFinite _
  -- The map `T ⊕ T → {χ // χ ≠ χ⁻¹}` sending the two copies to `t` and `t⁻¹`.
  let toFree : T ⊕ T → {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} :=
    Sum.elim (fun t => ⟨t.1, t.2.1⟩)
      (fun t => ⟨t.1⁻¹, by rw [hinv_inv]; exact t.2.1.symm⟩)
  have htoFree_inj : Function.Injective toFree := by
    rintro (⟨χ, hχ, hk⟩ | ⟨χ, hχ, hk⟩) (⟨χ', hχ', hk'⟩ | ⟨χ', hχ', hk'⟩) hxy <;>
      simp only [toFree, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at hxy
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · exfalso
      -- χ = χ'⁻¹ contradicts the key inequalities
      have e1 : key χ < key χ⁻¹ := hk
      have e2 : key χ' < key χ'⁻¹ := hk'
      rw [hxy] at e1
      rw [hinv_inv] at e1
      omega
    · exfalso
      have e1 : key χ < key χ⁻¹ := hk
      have e2 : key χ' < key χ'⁻¹ := hk'
      rw [← hxy] at e2
      rw [hinv_inv] at e2
      omega
    · refine congrArg Sum.inr (Subtype.ext ?_)
      exact inv_injective hxy
  have htoFree_surj : Function.Surjective toFree := by
    rintro ⟨χ, hχ⟩
    rcases lt_or_gt_of_ne (fun h => hχ (key_inj h)) with h | h
    · exact ⟨Sum.inl ⟨χ, hχ, h⟩, rfl⟩
    · refine ⟨Sum.inr ⟨χ⁻¹, ?_, ?_⟩, Subtype.ext (inv_inv χ)⟩
      · rw [hinv_inv]; exact hχ.symm
      · rw [hinv_inv]; exact h
  -- The transversal has `(N - gcd(2,N))/2` elements, one per free orbit pair.
  have hTfree : Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} = 2 * Nat.card T := by
    rw [← Nat.card_congr (Equiv.ofBijective toFree ⟨htoFree_inj, htoFree_surj⟩),
      Nat.card_sum, two_mul]
  have hcardT : Nat.card T = (N - Nat.gcd 2 N) / 2 := by
    have hfop := Etingof.DihedralCharacterCombinatorics.card_freeOrbitPairs N
    rw [hTfree, Nat.mul_div_cancel_left _ (by norm_num)] at hfop
    exact hfop
  -- Given a free character, produce its transversal representative.
  have rep : ∀ (χ : Multiplicative (ZMod N) →* ℂˣ), χ ≠ χ⁻¹ →
      ∃ t : T, t.1 = χ ∨ t.1 = χ⁻¹ := by
    intro χ hχ
    rcases lt_or_gt_of_ne (fun h => hχ (key_inj h)) with h | h
    · exact ⟨⟨χ, hχ, h⟩, Or.inl rfl⟩
    · exact ⟨⟨χ⁻¹, by rw [hinv_inv]; exact hχ.symm,
        by rw [hinv_inv]; exact h⟩, Or.inr rfl⟩
  -- **The index type and family.**
  let ι := ({χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} × (Multiplicative (ZMod 2) →* ℂˣ)) ⊕ T
  let F : ι → FDRep ℂ (DihedralSemidirect N) :=
    Sum.elim
      (fun x => V x.1.1 (Etingof.AbelianFDRep.charFDRep (x.2.comp (stab x.1.1).subtype)))
      (fun t => V t.1 (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab t.1) →* ℂˣ)))
  have hFsimple : ∀ a : ι, Simple (F a) := by
    rintro (⟨⟨χ, hχ⟩, ρ⟩ | t)
    · exact hi _ _ (Etingof.AbelianFDRep.charFDRep_simple _)
    · exact hi _ _ (Etingof.AbelianFDRep.charFDRep_simple _)
  have hFdim1 : ∀ (x : {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹}
        × (Multiplicative (ZMod 2) →* ℂˣ)),
      finrank ℂ (F (Sum.inl x) : Type) = 1 := by
    rintro ⟨⟨χ, hχ⟩, ρ⟩
    exact hdim_self χ hχ.symm ρ
  have hFdim2 : ∀ (t : T), finrank ℂ (F (Sum.inr t) : Type) = 2 := by
    rintro ⟨χ, hχ, _⟩
    exact hdim_free χ (fun h => hχ h.symm)
  have hFdim : ∀ a : ι, finrank ℂ (F a : Type) = 1 ∨ finrank ℂ (F a : Type) = 2 := by
    rintro (x | t)
    · exact Or.inl (hFdim1 x)
    · exact Or.inr (hFdim2 t)
  -- An iso of family members forces equal dimension (used to separate 1-dim from 2-dim reps).
  have hiso_finrank : ∀ {a b : ι}, Nonempty (F a ≅ F b) →
      finrank ℂ (F a : Type) = finrank ℂ (F b : Type) := by
    rintro a b ⟨α⟩
    have hc := congrFun (FDRep.char_iso α) 1
    rw [FDRep.char_one, FDRep.char_one] at hc
    exact_mod_cast hc
  -- **Pairwise non-isomorphism.**
  have hFinj : ∀ a b : ι, Nonempty (F a ≅ F b) → a = b := by
    rintro (⟨⟨χ, hχ⟩, ρ⟩ | ⟨χ, hχ, hk⟩) (⟨⟨χ', hχ'⟩, ρ'⟩ | ⟨χ', hχ', hk'⟩) ⟨α⟩
    · -- self vs self: `χ = χ'` (self-inverse orbit is a fixed point) and `ρ = ρ'`.
      obtain ⟨g, hg, ⟨β⟩⟩ := hii χ χ' _ _
        (Etingof.AbelianFDRep.charFDRep_simple _) (Etingof.AbelianFDRep.charFDRep_simple _) ⟨α⟩
      have hχχ' : χ = χ' := by
        rcases hG2 g with rfl | rfl
        · rw [← hg, hdual_one]
        · rw [← hg, hdual_gen]; exact hχ
      subst hχχ'
      have hcentral : ∀ x : Multiplicative (ZMod 2), g * x = x * g := fun x => mul_comm g x
      have hUiso : Nonempty (Etingof.AbelianFDRep.charFDRep (ρ'.comp (stab χ).subtype) ≅
          Etingof.AbelianFDRep.charFDRep (ρ.comp (stab χ).subtype)) :=
        ⟨β ≪≫ (hviii χ g hg _ hcentral).some⟩
      have hρρ' : ρ'.comp (stab χ).subtype = ρ.comp (stab χ).subtype :=
        Etingof.AbelianFDRep.charFDRep_iso_iff.mp hUiso
      have hρeq : ρ' = ρ := by
        refine MonoidHom.ext fun x => ?_
        have hx : x ∈ stab χ := by rw [hstab_top χ hχ.symm]; exact Subgroup.mem_top x
        have hval := DFunLike.congr_fun hρρ' (⟨x, hx⟩ : ↥(stab χ))
        simpa using hval
      rw [hρeq]
    · -- self vs free: dimensions differ.
      exfalso
      have h := hiso_finrank ⟨α⟩
      rw [hFdim1 (⟨χ, hχ⟩, ρ), hFdim2 ⟨χ', hχ', hk'⟩] at h
      exact absurd h (by norm_num)
    · -- free vs self: dimensions differ.
      exfalso
      have h := hiso_finrank ⟨α⟩
      rw [hFdim2 ⟨χ, hχ, hk⟩, hFdim1 (⟨χ', hχ'⟩, ρ')] at h
      exact absurd h (by norm_num)
    · -- free vs free: `χ = χ'` (both are transversal representatives of the same orbit).
      obtain ⟨g, hg, -⟩ := hii χ χ' _ _
        (Etingof.AbelianFDRep.charFDRep_simple _) (Etingof.AbelianFDRep.charFDRep_simple _) ⟨α⟩
      have hor : χ' = χ ∨ χ' = χ⁻¹ := by
        rcases hG2 g with rfl | rfl
        · left; rw [← hg, hdual_one]
        · right; rw [← hg, hdual_gen]
      have hχχ' : χ = χ' := by
        rcases hor with h | h
        · exact h.symm
        · exfalso
          have e1 : key χ < key χ⁻¹ := hk
          have e2 : key χ' < key χ'⁻¹ := hk'
          rw [h] at e2
          rw [hinv_inv] at e2
          omega
      subst hχχ'
      rfl
  -- **Completeness.**
  have hFcomplete : ∀ S : FDRep ℂ (DihedralSemidirect N), Simple S → ∃ a : ι, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    haveI : Simple U := hU
    by_cases hχ : χ = χ⁻¹
    · -- self-inverse: recover `ρ : G →* ℂˣ` from the stabilizer character.
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso U
      let eStab : ↥(stab χ) ≃* Multiplicative (ZMod 2) :=
        (MulEquiv.subgroupCongr (hstab_top χ hχ.symm)).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab χ).subtype s) := fun s => rfl
      refine ⟨Sum.inl (⟨χ, hχ⟩, ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp (stab χ).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab χ).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (⟨χ, hχ⟩, ξ.comp eStab.symm.toMonoidHom))
          = V χ (Etingof.AbelianFDRep.charFDRep ξ) := by
        change V χ (Etingof.AbelianFDRep.charFDRep
            ((ξ.comp eStab.symm.toMonoidHom).comp (stab χ).subtype))
          = V χ (Etingof.AbelianFDRep.charFDRep ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫ (hvi χ U (Etingof.AbelianFDRep.charFDRep ξ) hξ).some⟩
    · -- free: move the base point to the transversal representative.
      obtain ⟨t, htor⟩ := rep χ hχ
      obtain ⟨g, hg⟩ : ∃ g : Multiplicative (ZMod 2), dualSmul g χ = t.1 := by
        rcases htor with h | h
        · exact ⟨1, by rw [hdual_one]; exact h.symm⟩
        · exact ⟨Multiplicative.ofAdd 1, by rw [hdual_gen]; exact h.symm⟩
      haveI : Simple (transport g χ t.1 hg U) := hix χ t.1 U g hg hU
      haveI hsub : Subsingleton ↥(stab t.1) := by
        have hbot : stab t.1 = ⊥ := hstab_bot t.1 (fun e => t.2.1 e.symm)
        rw [hbot]
        exact ⟨fun a b => Subtype.ext (by
          rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso (transport g χ t.1 hg U)
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_
        rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ
      exact ⟨Sum.inr t, ⟨hSU.some ≪≫ (hvii χ t.1 U g hg).some
        ≪≫ (hvi t.1 (transport g χ t.1 hg U) _ hξ).some⟩⟩
  -- **Cardinalities for the counts.**
  have hcardGhat : Fintype.card (Multiplicative (ZMod 2) →* ℂˣ) = 2 := by
    rw [← Nat.card_eq_fintype_card, Etingof.AbelianFDRep.card_charFDRep_dual, hcardG2]
  have hcardSelf : Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹}
      = Nat.gcd 2 N := by
    rw [← Nat.card_eq_fintype_card, Etingof.DihedralCharacterCombinatorics.card_selfInverse]
  have hcardT' : Fintype.card T = (N - Nat.gcd 2 N) / 2 := by
    rw [← Nat.card_eq_fintype_card, hcardT]
  -- The dimension-1 (resp. dimension-2) members are exactly the `Sum.inl` (resp. `Sum.inr`) ones.
  have hsum1 : (∑ a : ι, if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0)
      = Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} * 2 := by
    rw [Fintype.sum_sum_type]
    have hL : ∀ x, (if finrank ℂ (F (Sum.inl x) : Type) = 1 then (1 : ℕ) else 0) = 1 := by
      intro x; rw [if_pos (hFdim1 x)]
    have hR : ∀ t, (if finrank ℂ (F (Sum.inr t) : Type) = 1 then (1 : ℕ) else 0) = 0 := by
      intro t; have : finrank ℂ (F (Sum.inr t) : Type) ≠ 1 := by rw [hFdim2 t]; norm_num
      rw [if_neg this]
    simp only [hL, hR, Finset.sum_const, mul_zero, smul_eq_mul, mul_one, add_zero,
      Finset.card_univ, Fintype.card_prod, hcardGhat]
  have hsum2 : (∑ a : ι, if finrank ℂ (F a : Type) = 2 then (1 : ℕ) else 0)
      = Fintype.card T := by
    rw [Fintype.sum_sum_type]
    have hL : ∀ x, (if finrank ℂ (F (Sum.inl x) : Type) = 2 then (1 : ℕ) else 0) = 0 := by
      intro x; have : finrank ℂ (F (Sum.inl x) : Type) ≠ 2 := by rw [hFdim1 x]; norm_num
      rw [if_neg this]
    have hR : ∀ t, (if finrank ℂ (F (Sum.inr t) : Type) = 2 then (1 : ℕ) else 0) = 1 := by
      intro t; rw [if_pos (hFdim2 t)]
    simp only [hL, hR, Finset.sum_const, mul_zero, smul_eq_mul, mul_one, zero_add,
      Finset.card_univ]
  -- Transport the family to `Fin (card ι)`.
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij
    exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · exact fun i => hFdim (e.symm i)
  · -- Odd `N`: `gcd(2,N) = 1`, so `2` one-dim reps and `(N-1)/2` two-dim reps.
    intro hpar
    have hg1 : Nat.gcd 2 N = 1 := by rw [Nat.gcd_rec, Nat.odd_iff.mp hpar]; simp
    refine ⟨?_, ?_⟩
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0), hsum1, hcardSelf, hg1]
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 2 then (1 : ℕ) else 0), hsum2, hcardT', hg1]
  · -- Even `N`: `gcd(2,N) = 2`, so `4` one-dim reps and `(N-2)/2` two-dim reps.
    intro hpar
    have hg2 : Nat.gcd 2 N = 2 := by rw [Nat.gcd_rec, Nat.even_iff.mp hpar]; simp
    refine ⟨?_, ?_⟩
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0), hsum1, hcardSelf, hg2]
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 2 then (1 : ℕ) else 0), hsum2, hcardT', hg2]

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.1(a).** The complete classification of the irreducible
complex representations of the dihedral group `D_N` (symmetries of a regular `N`-gon, order
`2N`), obtained from Theorem 5.27.1 via the semidirect-product structure `⟨r⟩ ⋊ ⟨s⟩` with `s`
acting by inversion. Every irreducible has dimension `1` or `2`, and the number of each kind
depends on the parity of `N`: for `N` odd there are `2` of dimension `1` and `(N-1)/2` of
dimension `2`; for `N` even there are `4` of dimension `1` and `(N-2)/2` of dimension `2`.
In both cases `∑ dim² = 2N = |D_N|`. -/
theorem dihedral_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (DihedralGroup N)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (DihedralGroup N), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = 2) ∧
      (Odd N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 2 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 1) / 2) ∧
      (Even N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 4 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 2) / 2) := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hDim, hOdd, hEven⟩ := semidirect_classification N
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    transport_classification (dihedralEquiv N) V hSimple hInj hComplete
  have hfilt : ∀ d : ℕ, (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = d)) =
      (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) :=
    fun d => filter_finrank_congr hWdim d
  refine ⟨n, W, hW1, hW2, hW3, ?_, ?_, ?_⟩
  · -- dimensions are unchanged
    intro i
    rw [hWdim i]; exact hDim i
  · -- odd-`N` counts: the dimension filters agree pointwise with the pre-transport ones
    intro hpar
    rw [hfilt, hfilt]; exact hOdd hpar
  · intro hpar
    rw [hfilt, hfilt]; exact hEven hpar

end Etingof.Exercise5_27_2
