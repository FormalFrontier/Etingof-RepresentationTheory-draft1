import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1
import EtingofRepresentationTheory.Chapter5.AbelianFDRep
import EtingofRepresentationTheory.Chapter5.Exercise5_27_2_Transport
import EtingofRepresentationTheory.Chapter4.Problem4_12_6

/-!
# Exercise 5.27.2 (affine group): redo Problem 4.12.6 using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the Problem 4.12.6 part: the group `G` of nonconstant inhomogeneous linear
transformations `x ↦ a x + b` over a finite field `K` (with `a ∈ Kˣ`, `b ∈ K`). Problem 4.12.6 asks
for all irreducible complex representations of `G` and their characters. Theorem 5.27.1 (the orbit
method for semidirect products `A ⋊ G` with `A` abelian) supplies them directly, because the affine
group is a semidirect product of the abelian translation group by the multiplicative group.

## The affine group as a semidirect product

Composition of `x ↦ a₁ x + b₁` after `x ↦ a₂ x + b₂` sends `x ↦ a₁ a₂ x + (a₁ b₂ + b₁)`. Writing the
additive translation group `(K, +)` multiplicatively as `Multiplicative K` and letting `Kˣ` act on
it by multiplication, this is exactly the semidirect-product multiplication
`⟨b₁, a₁⟩ * ⟨b₂, a₂⟩ = ⟨b₁ · φ(a₁)(b₂), a₁ a₂⟩`. So

`AffineGroup K := Multiplicative K ⋊[affineφ K] Kˣ`,

where `affineφ K : Kˣ →* MulAut (Multiplicative K)` is multiplication by a unit, obtained from the
distributive `Kˣ`-action on the ring `K` via `AddAut.mulLeft` and the identification
`MulAut (Multiplicative K) ≃* Multiplicative (AddAut K)`.

## The classification (orbit method, Theorem 5.27.1)

Here `A = Multiplicative K` (order `q = |K|`) and `G = Kˣ` (order `q - 1`), so `|AffineGroup K| =
q(q - 1)`. The dual `G`-action on `Â = A →* ℂˣ` has two orbits: the trivial character `{1}` (fixed,
stabilizer all of `Kˣ`) and the single free orbit of all `q - 1` nontrivial characters (stabilizer
trivial). Theorem 5.27.1 then yields:

* over the fixed character `1`, one irreducible `V(1, U)` for each irreducible `U` of `Kˣ`, i.e. the
  `q - 1` one-dimensional characters of `AffineGroup K` factoring through `Kˣ`;
* over the free orbit, a single irreducible `V(χ, U)` (with `U` the trivial rep of the trivial
  stabilizer) of dimension `[G : G_χ] = q - 1`.

Thus there are exactly `q` irreducibles: `q - 1` of dimension `1` and one of dimension `q - 1`
(consistent with `∑ dim² = (q - 1)·1 + (q - 1)² = q(q - 1) = |AffineGroup K|`).

The classification `affine_classification` is proved below by feeding the two orbit facts above
into Theorem 5.27.1 (for fields with `q > 2`; see the theorem docstring for the `q = 2` caveat).

## Landing on the group of Problem 4.12.6

Problem 4.12.6 studies the `structure Problem4_12_6.Affine K` of pairs `⟨a, b⟩`, a different type
from the semidirect-product model `AffineGroup K`. `affineEquiv` is the group isomorphism between
them, `affine_classification'` and `affine_classification_two'` are the two classifications
transported onto the textbook group along it (via `Exercise5_27_2_Transport`), and
`affine_classification_named` matches the transported family with the book's own named
representations: the `q - 1` characters `charRep χ` and the zero-sum representation
`V = Vsub` of dimension `q - 1` that the problem's hint singles out.
-/

noncomputable section

open CategoryTheory Module

namespace Etingof.Exercise5_27_2

variable (K : Type) [Field K] [Fintype K]

/-- The action of `Kˣ` on the translation group `(K, +) = Multiplicative K` by multiplication:
`affineφ K a` is `b ↦ a · b`. Built from the distributive `Kˣ`-action on the ring `K`. -/
def affineφ : Kˣ →* MulAut (Multiplicative K) :=
  (MulAutMultiplicative K).symm.toMonoidHom.comp (AddAut.mulLeft (R := K))

omit [Fintype K] in
@[simp] lemma affineφ_apply (a : Kˣ) (b : K) :
    Multiplicative.toAdd ((affineφ K a) (Multiplicative.ofAdd b)) = (a : K) * b := rfl

/-- The affine group `x ↦ a x + b` over `K`, realized as the semidirect product of the abelian
translation group `Multiplicative K` by the multiplicative group `Kˣ` acting by multiplication. -/
abbrev AffineGroup : Type := Multiplicative K ⋊[affineφ K] Kˣ

/-! ## The dual `Kˣ`-action on characters of `(K, +)`

The orbit-method engine (Theorem 5.27.1) equips the character group `Â = Multiplicative K →* ℂˣ`
with the dual action `(g · χ)(a) = χ(φ(g⁻¹)(a))`. For the affine action `φ(g)(a) = g · a`, this is
`(g · χ)(a) = χ(g⁻¹ a)`, i.e. multiplicative shift of the underlying additive character. We record
the two orbit facts the classification needs, both consequences of the fact that over a field
every nontrivial additive character is primitive (`AddChar.IsPrimitive.of_ne_one`):

* `affineDualSmul_eq_self_iff`: a nontrivial character has trivial stabilizer (only `g = 1`
  fixes it), while the trivial character is fixed by all of `Kˣ` (`affineDualSmul_trivial`);
* `affineDualSmul_transitive`: `Kˣ` acts transitively on the `q - 1` nontrivial characters
  (a single free orbit), because `r ↦ mulShift ψ r` is an injection `K ↪ Â` between sets of equal
  size `q`, hence a bijection.
-/

/-- The concrete dual `Kˣ`-action on characters: `affineDualSmul g χ = a ↦ χ(g⁻¹ · a)`. This is the
witness `dualSmul` of Theorem 5.27.1 specialized to `affineφ K` (matched via its `hdual` clause). -/
def affineDualSmul (g : Kˣ) (χ : Multiplicative K →* ℂˣ) : Multiplicative K →* ℂˣ :=
  χ.comp (affineφ K g⁻¹).toMonoidHom

omit [Fintype K] in
@[simp] lemma affineDualSmul_apply (g : Kˣ) (χ : Multiplicative K →* ℂˣ) (x : Multiplicative K) :
    affineDualSmul K g χ x = χ ((affineφ K g⁻¹) x) := rfl

omit [Fintype K] in
/-- The affine action on a general element of `Multiplicative K`. -/
@[simp] lemma affineφ_apply' (a : Kˣ) (x : Multiplicative K) :
    (affineφ K a) x = Multiplicative.ofAdd ((a : K) * Multiplicative.toAdd x) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  conv_lhs => rw [← ofAdd_toAdd x]
  rw [affineφ_apply]

omit [Fintype K] in
/-- The trivial character is fixed by every `g` (its stabilizer is all of `Kˣ`). -/
@[simp] lemma affineDualSmul_trivial (g : Kˣ) :
    affineDualSmul K g (1 : Multiplicative K →* ℂˣ) = 1 := by
  ext x; simp [affineDualSmul]

omit [Fintype K] in
/-- `AddChar.toMonoidHomEquiv` carries the trivial additive character to the trivial monoid hom. -/
private lemma toMonoidHomEquiv_one :
    AddChar.toMonoidHomEquiv (1 : AddChar K ℂˣ) = (1 : Multiplicative K →* ℂˣ) := by
  ext x; simp

omit [Fintype K] in
/-- A nontrivial multiplicative character corresponds to a nontrivial additive character. -/
private lemma toAddChar_ne_one {χ : Multiplicative K →* ℂˣ} (hχ : χ ≠ 1) :
    AddChar.toMonoidHomEquiv.symm χ ≠ (1 : AddChar K ℂˣ) := by
  intro h
  apply hχ
  have := congrArg AddChar.toMonoidHomEquiv h
  rw [Equiv.apply_symm_apply, toMonoidHomEquiv_one] at this
  exact this

omit [Fintype K] in
/-- The dual action is the multiplicative shift of the associated additive character by `g⁻¹`. -/
lemma affineDualSmul_eq_mulShift (g : Kˣ) (χ : Multiplicative K →* ℂˣ) :
    affineDualSmul K g χ =
      AddChar.toMonoidHomEquiv
        (AddChar.mulShift (AddChar.toMonoidHomEquiv.symm χ) ((g⁻¹ : Kˣ) : K)) := by
  refine MonoidHom.ext (fun x => ?_)
  rw [affineDualSmul_apply, affineφ_apply', AddChar.toMonoidHomEquiv_apply,
    AddChar.mulShift_apply, AddChar.toMonoidHomEquiv_symm_apply]

omit [Fintype K] in
/-- **Stabilizer dichotomy.** A nontrivial character is fixed by `g` only when `g = 1`, so its
stabilizer under the dual action is trivial. -/
lemma affineDualSmul_eq_self_iff (g : Kˣ) {χ : Multiplicative K →* ℂˣ} (hχ : χ ≠ 1) :
    affineDualSmul K g χ = χ ↔ g = 1 := by
  have hprim : (AddChar.toMonoidHomEquiv.symm χ).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (toAddChar_ne_one K hχ)
  rw [affineDualSmul_eq_mulShift]
  constructor
  · intro h
    have h2 : AddChar.mulShift (AddChar.toMonoidHomEquiv.symm χ) ((g⁻¹ : Kˣ) : K)
        = AddChar.toMonoidHomEquiv.symm χ := by
      apply AddChar.toMonoidHomEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    have h3 : ((g⁻¹ : Kˣ) : K) = 1 :=
      AddChar.to_mulShift_inj_of_isPrimitive hprim
        (by rw [AddChar.mulShift_one]; exact h2)
    rw [Units.val_eq_one] at h3
    exact inv_eq_one.mp h3
  · rintro rfl
    simp only [inv_one, Units.val_one, AddChar.mulShift_one, Equiv.apply_symm_apply]

/-- **Transitivity.** `Kˣ` acts transitively on the nontrivial characters: for any two nontrivial
`χ₁, χ₂` there is `g` with `g · χ₁ = χ₂`. Hence the nontrivial characters form a single orbit. -/
lemma affineDualSmul_transitive {χ₁ χ₂ : Multiplicative K →* ℂˣ}
    (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1) : ∃ g : Kˣ, affineDualSmul K g χ₁ = χ₂ := by
  classical
  set ψ₁ := AddChar.toMonoidHomEquiv.symm χ₁ with hψ₁
  have hprim : ψ₁.IsPrimitive := AddChar.IsPrimitive.of_ne_one (toAddChar_ne_one K h1)
  -- The injection `r ↦ E (mulShift ψ₁ r)` from `K` to characters.
  let F : K → (Multiplicative K →* ℂˣ) := fun r => AddChar.toMonoidHomEquiv (AddChar.mulShift ψ₁ r)
  have hFinj : Function.Injective F := fun a b hab =>
    AddChar.to_mulShift_inj_of_isPrimitive hprim (AddChar.toMonoidHomEquiv.injective hab)
  -- `K` and the character group have equal (finite) cardinality, so `F` is a bijection.
  haveI : Fintype (Multiplicative K →* ℂˣ) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (Multiplicative K →* ℂˣ) := by
    have := Etingof.AbelianFDRep.card_charFDRep_dual (G := Multiplicative K)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    simpa [Fintype.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)] using this.symm
  have hFsurj : Function.Surjective F :=
    ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hFinj, hcard⟩).surjective
  obtain ⟨c, hc⟩ := hFsurj χ₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h2
    rw [← hc]
    simp [F, AddChar.mulShift_zero, toMonoidHomEquiv_one]
  refine ⟨(Ne.isUnit hc0).unit⁻¹, ?_⟩
  rw [affineDualSmul_eq_mulShift, ← hψ₁]
  simp only [inv_inv, IsUnit.unit_spec]
  exact hc

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.6.** The complete classification of the irreducible complex
representations of the affine group `x ↦ a x + b` over a finite field `K` (`q = |K|` elements),
obtained from Theorem 5.27.1: there are exactly `q` pairwise non-isomorphic irreducibles forming a
complete set, of which `q - 1` have dimension `1` (the characters factoring through `Kˣ`) and one
has dimension `q - 1` (over the free orbit of nontrivial characters).

The hypothesis `2 < q` excludes the degenerate field `K = 𝔽₂`, where `AffineGroup K ≅ ℤ/2` has two
one-dimensional irreducibles: there the free-orbit rep also has dimension `q - 1 = 1`, so the two
dimension filters would overlap and the counts `q - 1` and `1` could not both hold. For `q ≥ 3` the
dimensions `1` and `q - 1 ≥ 2` are distinct, so the split is clean. -/
theorem affine_classification (hq : 2 < Fintype.card K) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (AffineGroup K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (AffineGroup K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 := by
  classical
  haveI : Nonempty Kˣ := ⟨1⟩
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport,
    hi, hii, hiii, hiv, hv, hvi, hvii, hviii, hix⟩ :=
    Etingof.Theorem5_27_1 Kˣ (Multiplicative K) (affineφ K)
  -- Match the abstract dual action supplied by Theorem 5.27.1 to the concrete `affineDualSmul`.
  have hds : ∀ (g : Kˣ) (χ : Multiplicative K →* ℂˣ), dualSmul g χ = affineDualSmul K g χ := by
    intro g χ
    refine MonoidHom.ext fun a => ?_
    rw [hdual g χ a, affineDualSmul_apply]
  -- The trivial character is fixed by all of `Kˣ`: its stabilizer is `⊤`.
  have hstab_triv : stab (1 : Multiplicative K →* ℂˣ) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact (hstab 1 g).mpr (by rw [hds]; exact affineDualSmul_trivial K g)
  -- A nontrivial character has trivial stabilizer `⊥`.
  have hstab_ntriv : ∀ {χ : Multiplicative K →* ℂˣ}, χ ≠ 1 → stab χ = ⊥ := by
    intro χ hχ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgχ : affineDualSmul K g χ = χ := by rw [← hds]; exact (hstab χ g).mp hg
    exact (affineDualSmul_eq_self_iff K g hχ).mp hgχ
  -- `Kˣ` is abelian, so conjugation is trivial.
  have hconj : ∀ h g : Kˣ, h * g * h⁻¹ = g := fun h g => by
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  haveI : Fintype (Multiplicative K →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype (Kˣ →* ℂˣ) := Fintype.ofFinite _
  -- Cardinality of the character group of `(K, +)` equals `q`.
  have hcardHom : Fintype.card (Multiplicative K →* ℂˣ) = Fintype.card K := by
    have h := Etingof.AbelianFDRep.card_charFDRep_dual (G := Multiplicative K)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rwa [Fintype.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)] at h
  -- Cardinality of the character group of `Kˣ` equals `q - 1`.
  have hcardDual : Fintype.card (Kˣ →* ℂˣ) = Fintype.card K - 1 := by
    rw [← Nat.card_eq_fintype_card, Etingof.AbelianFDRep.card_charFDRep_dual,
      Nat.card_eq_fintype_card, Fintype.card_units]
  -- Choose a nontrivial character to represent the single free orbit.
  haveI : Nontrivial (Multiplicative K →* ℂˣ) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcardHom]; omega
  obtain ⟨χ₀, hχ₀⟩ := exists_ne (1 : Multiplicative K →* ℂˣ)
  -- The classifying family: `Sum.inl ρ` gives the 1-dim rep over the fixed character (indexed by a
  -- character `ρ` of `Kˣ`); `Sum.inr ()` gives the single `(q-1)`-dim rep over the free orbit.
  set F : (Kˣ →* ℂˣ) ⊕ Unit → FDRep ℂ (AffineGroup K) := fun a =>
    a.elim
      (fun ρ => V (1 : Multiplicative K →* ℂˣ)
        (Etingof.AbelianFDRep.charFDRep (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)))
      (fun _ => V χ₀ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ))) with hF
  -- **Closed-form character of the fixed-orbit (1-dim) reps:** at `⟨a, g⟩` it is `ρ g`.
  have fixed_char : ∀ (ρ : Kˣ →* ℂˣ) (a : Multiplicative K) (g : Kˣ),
      (V (1 : Multiplicative K →* ℂˣ)
        (Etingof.AbelianFDRep.charFDRep
          (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))).character ⟨a, g⟩
      = (ρ g : ℂ) := by
    intro ρ a g
    have hSimpleU := Etingof.AbelianFDRep.charFDRep_simple
      (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)
    have hmemg : g ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      rw [hstab_triv]; exact Subgroup.mem_top g
    have hmemall : ∀ h : Kˣ, h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      intro h; rw [hstab_triv]; exact Subgroup.mem_top _
    have hcard : Fintype.card ↥(stab (1 : Multiplicative K →* ℂˣ)) = Fintype.card Kˣ := by
      rw [hstab_triv]; exact Fintype.card_congr Subgroup.topEquiv.toEquiv
    have hterm : ∀ h : Kˣ,
        (if hh : h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ)
          then ((1 : Multiplicative K →* ℂˣ)
                ((affineφ K h : MulAut (Multiplicative K)) a) : ℂ)
              * (Etingof.AbelianFDRep.charFDRep
                  (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)).character
                  ⟨h * g * h⁻¹, hh⟩
          else 0)
        = (ρ g : ℂ) := by
      intro h
      rw [dif_pos (hmemall h),
        show (⟨h * g * h⁻¹, hmemall h⟩ : ↥(stab (1 : Multiplicative K →* ℂˣ))) = ⟨g, hmemg⟩ from
          Subtype.ext (hconj h g),
        Etingof.AbelianFDRep.charFDRep_character, MonoidHom.one_apply, Units.val_one, one_mul]
      rfl
    rw [hiv 1 _ hSimpleU a g, Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
      inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  -- Dimensions of the two kinds of family members.
  have hdim_inl : ∀ ρ : Kˣ →* ℂˣ, finrank ℂ (F (Sum.inl ρ) : Type) = 1 := by
    intro ρ
    change finrank ℂ (V (1 : Multiplicative K →* ℂˣ)
      (Etingof.AbelianFDRep.charFDRep
        (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) : Type) = 1
    rw [hv, Etingof.AbelianFDRep.charFDRep_finrank, mul_one, hstab_triv, Subgroup.index_top]
  have hdim_inr : finrank ℂ (F (Sum.inr () : (Kˣ →* ℂˣ) ⊕ Unit) : Type) = Fintype.card K - 1 := by
    change finrank ℂ (V χ₀ (Etingof.AbelianFDRep.charFDRep
      (1 : ↥(stab χ₀) →* ℂˣ)) : Type) = Fintype.card K - 1
    rw [hv, Etingof.AbelianFDRep.charFDRep_finrank, mul_one, hstab_ntriv hχ₀,
      Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_units]
  -- Simplicity of every family member.
  have hFsimple : ∀ a, Simple (F a) := by
    rintro (ρ | _)
    · exact hi 1 _ (Etingof.AbelianFDRep.charFDRep_simple _)
    · exact hi χ₀ _ (Etingof.AbelianFDRep.charFDRep_simple _)
  -- Pairwise non-isomorphism: an isomorphism forces equal index.
  have hFinj : ∀ a b, Nonempty (F a ≅ F b) → a = b := by
    rintro (ρ₁ | _) (ρ₂ | _) ⟨α⟩
    · -- fixed vs fixed: characters recover `ρ`
      have hchar := FDRep.char_iso α
      have hρ : ρ₁ = ρ₂ := by
        refine MonoidHom.ext fun g => ?_
        have h := congrFun hchar ⟨(1 : Multiplicative K), g⟩
        rw [show F (Sum.inl ρ₁) = V (1 : Multiplicative K →* ℂˣ)
            (Etingof.AbelianFDRep.charFDRep
              (ρ₁.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          show F (Sum.inl ρ₂) = V (1 : Multiplicative K →* ℂˣ)
            (Etingof.AbelianFDRep.charFDRep
              (ρ₂.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          fixed_char ρ₁ 1 g, fixed_char ρ₂ 1 g] at h
        exact Units.ext h
      rw [hρ]
    · -- fixed vs free: dimensions `1` and `q - 1 ≥ 2` differ
      exfalso
      have h := congrFun (FDRep.char_iso α) 1
      rw [FDRep.char_one, FDRep.char_one, hdim_inl ρ₁, hdim_inr, Nat.cast_inj] at h
      omega
    · -- free vs fixed: symmetric
      exfalso
      have h := congrFun (FDRep.char_iso α) 1
      rw [FDRep.char_one, FDRep.char_one, hdim_inl ρ₂, hdim_inr, Nat.cast_inj] at h
      omega
    · -- free vs free: the free orbit is a single point
      exact congrArg Sum.inr (Subsingleton.elim _ _)
  -- Completeness: every simple rep is isomorphic to a family member.
  have hFcomplete : ∀ S : FDRep ℂ (AffineGroup K), Simple S → ∃ a, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    haveI : Simple U := hU
    by_cases hχ : χ = 1
    · -- fixed orbit: recover a character `ρ` of `Kˣ` from `U ≅ charFDRep ξ`
      subst hχ
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso U
      let eStab : ↥(stab (1 : Multiplicative K →* ℂˣ)) ≃* Kˣ :=
        (MulEquiv.subgroupCongr hstab_triv).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab (1 : Multiplicative K →* ℂˣ)).subtype s) := fun _ => rfl
      refine ⟨Sum.inl (ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp
          (stab (1 : Multiplicative K →* ℂˣ)).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab (1 : Multiplicative K →* ℂˣ)).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (ξ.comp eStab.symm.toMonoidHom))
          = V (1 : Multiplicative K →* ℂˣ) (Etingof.AbelianFDRep.charFDRep ξ) := by
        change V (1 : Multiplicative K →* ℂˣ) (Etingof.AbelianFDRep.charFDRep
            ((ξ.comp eStab.symm.toMonoidHom).comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))
          = V (1 : Multiplicative K →* ℂˣ) (Etingof.AbelianFDRep.charFDRep ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫ (hvi 1 U (Etingof.AbelianFDRep.charFDRep ξ) hξ).some⟩
    · -- free orbit: move the base point to `χ₀` along the orbit
      refine ⟨Sum.inr (), ?_⟩
      obtain ⟨g, hg⟩ := affineDualSmul_transitive K hχ₀ hχ
      have hg' : dualSmul g χ₀ = χ := by rw [hds]; exact hg
      haveI : Subsingleton ↥(stab χ) := by
        rw [hstab_ntriv hχ]
        exact ⟨fun a b => Subtype.ext
          (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      -- `U ≅ charFDRep 1`
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso U
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ
      -- transport of `charFDRep 1` is again `≅ charFDRep 1`
      haveI : Simple (transport g χ₀ χ hg' (Etingof.AbelianFDRep.charFDRep
          (1 : ↥(stab χ₀) →* ℂˣ))) :=
        hix χ₀ χ _ g hg' (Etingof.AbelianFDRep.charFDRep_simple _)
      obtain ⟨ζ, hζ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso
        (transport g χ₀ χ hg' (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))
      have hζ1 : ζ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hζ1] at hζ
      -- assemble: `V χ₀ (charFDRep 1) ≅ V χ (transport …) ≅ V χ (charFDRep 1) ≅ V χ U ≅ S`
      have step1 : Nonempty (V χ₀ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ))
          ≅ V χ (transport g χ₀ χ hg'
              (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))) :=
        hvii χ₀ χ (Etingof.AbelianFDRep.charFDRep 1) g hg'
      have step2 : Nonempty (V χ (transport g χ₀ χ hg'
            (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))
          ≅ V χ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ) →* ℂˣ))) :=
        hvi χ _ _ hζ
      have step3 : Nonempty (V χ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ) →* ℂˣ))
          ≅ V χ U) :=
        hvi χ _ _ ⟨hξ.some.symm⟩
      change Nonempty (S ≅ V χ₀ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))
      exact ⟨hSU.some ≪≫ step3.some.symm ≪≫ step2.some.symm ≪≫ step1.some.symm⟩
  -- Assemble into a `Fin n`-indexed family.
  set e := Fintype.equivFin ((Kˣ →* ℂˣ) ⊕ Unit) with he
  refine ⟨Fintype.card ((Kˣ →* ℂˣ) ⊕ Unit), fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij; exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · rw [Fintype.card_sum, Fintype.card_unit, hcardDual]; omega
  · -- count of dimension-1 reps
    have hL1 : ∀ ρ : Kˣ →* ℂˣ,
        (if finrank ℂ (F (Sum.inl ρ) : Type) = 1 then (1 : ℕ) else 0) = 1 :=
      fun ρ => if_pos (hdim_inl ρ)
    have hR1 : ∀ u : Unit,
        (if finrank ℂ (F (Sum.inr u) : Type) = 1 then (1 : ℕ) else 0) = 0 := by
      rintro ⟨⟩; exact if_neg (by rw [hdim_inr]; omega)
    rw [Finset.card_filter,
      Equiv.sum_comp e.symm (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0),
      Fintype.sum_sum_type]
    simp only [hL1, hR1, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      mul_zero, add_zero, hcardDual]
  · -- count of dimension-`(q-1)` reps
    have hLp : ∀ ρ : Kˣ →* ℂˣ,
        (if finrank ℂ (F (Sum.inl ρ) : Type) = Fintype.card K - 1 then (1 : ℕ) else 0) = 0 :=
      fun ρ => if_neg (by rw [hdim_inl ρ]; omega)
    have hRp : ∀ u : Unit,
        (if finrank ℂ (F (Sum.inr u) : Type) = Fintype.card K - 1 then (1 : ℕ) else 0) = 1 := by
      rintro ⟨⟩; exact if_pos hdim_inr
    rw [Finset.card_filter,
      Equiv.sum_comp e.symm
        (fun a => if finrank ℂ (F a : Type) = Fintype.card K - 1 then (1 : ℕ) else 0),
      Fintype.sum_sum_type]
    simp only [hLp, hRp, Finset.sum_const, Finset.card_univ, Fintype.card_unit, smul_eq_mul,
      mul_one, mul_zero, zero_add]

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.6, degenerate field `K = 𝔽₂`.** When `q = |K| = 2` the
affine group `x ↦ a x + b` collapses to `Multiplicative K ≅ ℤ/2` (the multiplicative group `Kˣ` is
trivial), so all of its irreducibles are one-dimensional. This is the `q = 2` companion to
`affine_classification`, whose `{1, q-1}` dimension partition degenerates here (`q - 1 = 1`): the
free-orbit rep has the same dimension `1` as the fixed-orbit reps, so the two dimension-count
clauses of `affine_classification` cannot both hold and the theorem is restated with the uniform
"every irreducible is one-dimensional" conclusion instead.

Like `affine_classification`, the family is produced by the orbit method (Theorem 5.27.1): the
`q - 1 = 1` fixed-orbit rep(s) over the trivial character and the single free-orbit rep over the
nontrivial characters, for a total of `q = 2` pairwise non-isomorphic irreducibles. The fixed and
free reps are told apart by their character at a nontrivial translation `⟨a, 1⟩`: the fixed rep is
constant (`= 1`) there while the free rep takes the value `χ₀ a ≠ 1`. -/
theorem affine_classification_two (hq : Fintype.card K = 2) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (AffineGroup K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (AffineGroup K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = 2 ∧
      (∀ i, finrank ℂ (W i : Type) = 1) := by
  classical
  haveI : Nonempty Kˣ := ⟨1⟩
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport,
    hi, hii, hiii, hiv, hv, hvi, hvii, hviii, hix⟩ :=
    Etingof.Theorem5_27_1 Kˣ (Multiplicative K) (affineφ K)
  -- Match the abstract dual action supplied by Theorem 5.27.1 to the concrete `affineDualSmul`.
  have hds : ∀ (g : Kˣ) (χ : Multiplicative K →* ℂˣ), dualSmul g χ = affineDualSmul K g χ := by
    intro g χ
    refine MonoidHom.ext fun a => ?_
    rw [hdual g χ a, affineDualSmul_apply]
  -- The trivial character is fixed by all of `Kˣ`: its stabilizer is `⊤`.
  have hstab_triv : stab (1 : Multiplicative K →* ℂˣ) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact (hstab 1 g).mpr (by rw [hds]; exact affineDualSmul_trivial K g)
  -- A nontrivial character has trivial stabilizer `⊥`.
  have hstab_ntriv : ∀ {χ : Multiplicative K →* ℂˣ}, χ ≠ 1 → stab χ = ⊥ := by
    intro χ hχ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgχ : affineDualSmul K g χ = χ := by rw [← hds]; exact (hstab χ g).mp hg
    exact (affineDualSmul_eq_self_iff K g hχ).mp hgχ
  -- `Kˣ` is abelian, so conjugation is trivial.
  have hconj : ∀ h g : Kˣ, h * g * h⁻¹ = g := fun h g => by
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  -- At `q = 2` the multiplicative group is trivial: `|Kˣ| = q - 1 = 1`.
  have hcardUnits : Fintype.card Kˣ = 1 := by rw [Fintype.card_units, hq]
  haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  haveI : Unique Kˣ := ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
  haveI : Fintype (Multiplicative K →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype (Kˣ →* ℂˣ) := Fintype.ofFinite _
  -- Cardinality of the character group of `(K, +)` equals `q = 2`.
  have hcardHom : Fintype.card (Multiplicative K →* ℂˣ) = Fintype.card K := by
    have h := Etingof.AbelianFDRep.card_charFDRep_dual (G := Multiplicative K)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rwa [Fintype.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)] at h
  -- Cardinality of the character group of `Kˣ` equals `q - 1 = 1`.
  have hcardDual : Fintype.card (Kˣ →* ℂˣ) = Fintype.card K - 1 := by
    rw [← Nat.card_eq_fintype_card, Etingof.AbelianFDRep.card_charFDRep_dual,
      Nat.card_eq_fintype_card, Fintype.card_units]
  -- Choose a nontrivial character to represent the single free orbit.
  haveI : Nontrivial (Multiplicative K →* ℂˣ) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcardHom]; omega
  obtain ⟨χ₀, hχ₀⟩ := exists_ne (1 : Multiplicative K →* ℂˣ)
  -- The classifying family: `Sum.inl ρ` gives the 1-dim rep over the fixed character; `Sum.inr ()`
  -- gives the free-orbit rep (also 1-dimensional here, since `q - 1 = 1`).
  set F : (Kˣ →* ℂˣ) ⊕ Unit → FDRep ℂ (AffineGroup K) := fun a =>
    a.elim
      (fun ρ => V (1 : Multiplicative K →* ℂˣ)
        (Etingof.AbelianFDRep.charFDRep (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)))
      (fun _ => V χ₀ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ))) with hF
  -- **Closed-form character of the fixed-orbit reps:** at `⟨a, g⟩` it is `ρ g` (independent of `a`).
  have fixed_char : ∀ (ρ : Kˣ →* ℂˣ) (a : Multiplicative K) (g : Kˣ),
      (V (1 : Multiplicative K →* ℂˣ)
        (Etingof.AbelianFDRep.charFDRep
          (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))).character ⟨a, g⟩
      = (ρ g : ℂ) := by
    intro ρ a g
    have hSimpleU := Etingof.AbelianFDRep.charFDRep_simple
      (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)
    have hmemg : g ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      rw [hstab_triv]; exact Subgroup.mem_top g
    have hmemall : ∀ h : Kˣ, h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      intro h; rw [hstab_triv]; exact Subgroup.mem_top _
    have hcard : Fintype.card ↥(stab (1 : Multiplicative K →* ℂˣ)) = Fintype.card Kˣ := by
      rw [hstab_triv]; exact Fintype.card_congr Subgroup.topEquiv.toEquiv
    have hterm : ∀ h : Kˣ,
        (if hh : h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ)
          then ((1 : Multiplicative K →* ℂˣ)
                ((affineφ K h : MulAut (Multiplicative K)) a) : ℂ)
              * (Etingof.AbelianFDRep.charFDRep
                  (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)).character
                  ⟨h * g * h⁻¹, hh⟩
          else 0)
        = (ρ g : ℂ) := by
      intro h
      rw [dif_pos (hmemall h),
        show (⟨h * g * h⁻¹, hmemall h⟩ : ↥(stab (1 : Multiplicative K →* ℂˣ))) = ⟨g, hmemg⟩ from
          Subtype.ext (hconj h g),
        Etingof.AbelianFDRep.charFDRep_character, MonoidHom.one_apply, Units.val_one, one_mul]
      rfl
    rw [hiv 1 _ hSimpleU a g, Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
      inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  -- **Closed-form character of the free-orbit rep at a translation `⟨a, 1⟩`:** it is `χ₀ a`. (`Kˣ`
  -- is trivial, so the orbit sum collapses to its single term.)
  have free_char : ∀ a : Multiplicative K,
      (V χ₀ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ))).character ⟨a, 1⟩
      = (χ₀ a : ℂ) := by
    intro a
    have hSimpleU := Etingof.AbelianFDRep.charFDRep_simple (1 : ↥(stab χ₀) →* ℂˣ)
    have hcardstab : Fintype.card ↥(stab χ₀) = 1 := by
      have hle : Fintype.card ↥(stab χ₀) ≤ Fintype.card Kˣ :=
        Fintype.card_le_of_injective _ Subtype.val_injective
      have hpos : 0 < Fintype.card ↥(stab χ₀) := Fintype.card_pos
      omega
    have hh1 : ∀ h : Kˣ, h * 1 * h⁻¹ = 1 := fun h => by rw [mul_one, mul_inv_cancel]
    -- Each summand collapses to `χ₀ a`: the character factor is `1`, and `h = 1` in the trivial
    -- `Kˣ` makes the twist `φ h` the identity.
    have hterm : ∀ h : Kˣ,
        (if hh : h * 1 * h⁻¹ ∈ stab χ₀
          then (χ₀ ((affineφ K h : MulAut (Multiplicative K)) a) : ℂ)
            * (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)).character ⟨h * 1 * h⁻¹, hh⟩
          else 0)
        = (χ₀ a : ℂ) := by
      intro h
      rw [dif_pos (by rw [hh1 h]; exact one_mem _),
        show (⟨h * 1 * h⁻¹, by rw [hh1 h]; exact one_mem _⟩ : ↥(stab χ₀)) = 1 from
          Subtype.ext (by simp ),
        Etingof.AbelianFDRep.charFDRep_character, MonoidHom.one_apply, Units.val_one, mul_one,
        Subsingleton.elim h 1, map_one]
      rfl
    rw [hiv χ₀ _ hSimpleU a 1, Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_const, Finset.card_univ, hcardUnits, one_smul,
      hcardstab, Nat.cast_one, inv_one, one_mul]
  -- Both kinds of family member are one-dimensional (`q - 1 = 1` for the free orbit).
  have hdim_inl : ∀ ρ : Kˣ →* ℂˣ, finrank ℂ (F (Sum.inl ρ) : Type) = 1 := by
    intro ρ
    change finrank ℂ (V (1 : Multiplicative K →* ℂˣ)
      (Etingof.AbelianFDRep.charFDRep
        (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) : Type) = 1
    rw [hv, Etingof.AbelianFDRep.charFDRep_finrank, mul_one, hstab_triv, Subgroup.index_top]
  have hdim_inr : finrank ℂ (F (Sum.inr () : (Kˣ →* ℂˣ) ⊕ Unit) : Type) = 1 := by
    change finrank ℂ (V χ₀ (Etingof.AbelianFDRep.charFDRep
      (1 : ↥(stab χ₀) →* ℂˣ)) : Type) = 1
    rw [hv, Etingof.AbelianFDRep.charFDRep_finrank, mul_one, hstab_ntriv hχ₀,
      Subgroup.index_bot, Nat.card_eq_fintype_card, hcardUnits]
  -- Simplicity of every family member.
  have hFsimple : ∀ a, Simple (F a) := by
    rintro (ρ | _)
    · exact hi 1 _ (Etingof.AbelianFDRep.charFDRep_simple _)
    · exact hi χ₀ _ (Etingof.AbelianFDRep.charFDRep_simple _)
  -- Pairwise non-isomorphism. The fixed reps are distinguished from each other by their character;
  -- the fixed and free reps by their character at a nontrivial translation (`1` vs `χ₀ a ≠ 1`).
  have hFinj : ∀ a b, Nonempty (F a ≅ F b) → a = b := by
    -- A nontrivial translation `a₀` on which `χ₀` is nontrivial: the fixed/free separator.
    obtain ⟨a₀, ha₀⟩ := DFunLike.ne_iff.mp hχ₀
    rw [MonoidHom.one_apply] at ha₀
    have ha₀' : (χ₀ a₀ : ℂ) ≠ 1 := fun h => ha₀ (Units.ext h)
    rintro (ρ₁ | _) (ρ₂ | _) ⟨α⟩
    · -- fixed vs fixed: characters recover `ρ`
      have hchar := FDRep.char_iso α
      have hρ : ρ₁ = ρ₂ := by
        refine MonoidHom.ext fun g => ?_
        have h := congrFun hchar ⟨(1 : Multiplicative K), g⟩
        rw [show F (Sum.inl ρ₁) = V (1 : Multiplicative K →* ℂˣ)
            (Etingof.AbelianFDRep.charFDRep
              (ρ₁.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          show F (Sum.inl ρ₂) = V (1 : Multiplicative K →* ℂˣ)
            (Etingof.AbelianFDRep.charFDRep
              (ρ₂.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          fixed_char ρ₁ 1 g, fixed_char ρ₂ 1 g] at h
        exact Units.ext h
      rw [hρ]
    · -- fixed vs free: character at `⟨a₀, 1⟩` is `ρ₁ 1 = 1` (fixed) vs `χ₀ a₀ ≠ 1` (free)
      exfalso
      have h := congrFun (FDRep.char_iso α) ⟨a₀, 1⟩
      rw [show F (Sum.inl ρ₁) = V (1 : Multiplicative K →* ℂˣ)
          (Etingof.AbelianFDRep.charFDRep
            (ρ₁.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
        show F (Sum.inr ()) = V χ₀ (Etingof.AbelianFDRep.charFDRep
            (1 : ↥(stab χ₀) →* ℂˣ)) from rfl,
        fixed_char ρ₁ a₀ 1, free_char a₀, map_one, Units.val_one] at h
      exact ha₀' h.symm
    · -- free vs fixed: symmetric
      exfalso
      have h := congrFun (FDRep.char_iso α) ⟨a₀, 1⟩
      rw [show F (Sum.inl ρ₂) = V (1 : Multiplicative K →* ℂˣ)
          (Etingof.AbelianFDRep.charFDRep
            (ρ₂.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
        show F (Sum.inr ()) = V χ₀ (Etingof.AbelianFDRep.charFDRep
            (1 : ↥(stab χ₀) →* ℂˣ)) from rfl,
        fixed_char ρ₂ a₀ 1, free_char a₀, map_one, Units.val_one] at h
      exact ha₀' h
    · -- free vs free: the free orbit is a single point
      exact congrArg Sum.inr (Subsingleton.elim _ _)
  -- Completeness: every simple rep is isomorphic to a family member.
  have hFcomplete : ∀ S : FDRep ℂ (AffineGroup K), Simple S → ∃ a, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    haveI : Simple U := hU
    by_cases hχ : χ = 1
    · -- fixed orbit: recover a character `ρ` of `Kˣ` from `U ≅ charFDRep ξ`
      subst hχ
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso U
      let eStab : ↥(stab (1 : Multiplicative K →* ℂˣ)) ≃* Kˣ :=
        (MulEquiv.subgroupCongr hstab_triv).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab (1 : Multiplicative K →* ℂˣ)).subtype s) := fun _ => rfl
      refine ⟨Sum.inl (ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp
          (stab (1 : Multiplicative K →* ℂˣ)).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab (1 : Multiplicative K →* ℂˣ)).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (ξ.comp eStab.symm.toMonoidHom))
          = V (1 : Multiplicative K →* ℂˣ) (Etingof.AbelianFDRep.charFDRep ξ) := by
        change V (1 : Multiplicative K →* ℂˣ) (Etingof.AbelianFDRep.charFDRep
            ((ξ.comp eStab.symm.toMonoidHom).comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))
          = V (1 : Multiplicative K →* ℂˣ) (Etingof.AbelianFDRep.charFDRep ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫ (hvi 1 U (Etingof.AbelianFDRep.charFDRep ξ) hξ).some⟩
    · -- free orbit: move the base point to `χ₀` along the orbit
      refine ⟨Sum.inr (), ?_⟩
      obtain ⟨g, hg⟩ := affineDualSmul_transitive K hχ₀ hχ
      have hg' : dualSmul g χ₀ = χ := by rw [hds]; exact hg
      haveI : Subsingleton ↥(stab χ) := by
        rw [hstab_ntriv hχ]
        exact ⟨fun a b => Subtype.ext
          (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso U
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ
      haveI : Simple (transport g χ₀ χ hg' (Etingof.AbelianFDRep.charFDRep
          (1 : ↥(stab χ₀) →* ℂˣ))) :=
        hix χ₀ χ _ g hg' (Etingof.AbelianFDRep.charFDRep_simple _)
      obtain ⟨ζ, hζ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso
        (transport g χ₀ χ hg' (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))
      have hζ1 : ζ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hζ1] at hζ
      have step1 : Nonempty (V χ₀ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ))
          ≅ V χ (transport g χ₀ χ hg'
              (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))) :=
        hvii χ₀ χ (Etingof.AbelianFDRep.charFDRep 1) g hg'
      have step2 : Nonempty (V χ (transport g χ₀ χ hg'
            (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))
          ≅ V χ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ) →* ℂˣ))) :=
        hvi χ _ _ hζ
      have step3 : Nonempty (V χ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ) →* ℂˣ))
          ≅ V χ U) :=
        hvi χ _ _ ⟨hξ.some.symm⟩
      change Nonempty (S ≅ V χ₀ (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab χ₀) →* ℂˣ)))
      exact ⟨hSU.some ≪≫ step3.some.symm ≪≫ step2.some.symm ≪≫ step1.some.symm⟩
  -- Assemble into a `Fin n`-indexed family.
  set e := Fintype.equivFin ((Kˣ →* ℂˣ) ⊕ Unit) with he
  refine ⟨Fintype.card ((Kˣ →* ℂˣ) ⊕ Unit), fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij; exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · rw [Fintype.card_sum, Fintype.card_unit, hcardDual, hq]
  · -- every irreducible is one-dimensional
    have hall : ∀ a, finrank ℂ (F a : Type) = 1 := by
      rintro (ρ | ⟨⟩)
      · exact hdim_inl ρ
      · exact hdim_inr
    exact fun i => hall (e.symm i)

/-! ## Landing the classification on the group of Problem 4.12.6

Problem 4.12.6 studies the affine group as the `structure Problem4_12_6.Affine K` with fields
`a : Kˣ` and `b : K`, multiplying by `⟨a₁, b₁⟩ * ⟨a₂, b₂⟩ = ⟨a₁ a₂, a₁ · b₂ + b₁⟩`. That is a
different type from the semidirect-product model `AffineGroup K` used above, so "redo Problem
4.12.6" is only finished once the orbit-method classification is transported onto it. The
identification sends `⟨a, b⟩` to the pair `⟨ofAdd b, a⟩`: the abelian normal subgroup is the
translation part `b` and the complement is the linear part `a`. -/

/-- **The affine group of Problem 4.12.6 is the semidirect-product model.** The transformation
`x ↦ a x + b`, encoded by `⟨a, b⟩`, corresponds to `⟨ofAdd b, a⟩`: no correction term is needed,
because `⟨a₁, b₁⟩ * ⟨a₂, b₂⟩ = ⟨a₁ a₂, a₁ · b₂ + b₁⟩` matches the semidirect product
`⟨b₁, a₁⟩ * ⟨b₂, a₂⟩ = ⟨b₁ + a₁ · b₂, a₁ a₂⟩` under `affineφ K a : b ↦ a · b`. -/
def affineEquiv : Problem4_12_6.Affine K ≃* AffineGroup K where
  toFun g := ⟨Multiplicative.ofAdd g.b, g.a⟩
  invFun y := ⟨y.right, Multiplicative.toAdd y.left⟩
  left_inv g := rfl
  right_inv y := rfl
  map_mul' g h := by
    refine SemidirectProduct.ext ?_ rfl
    change Multiplicative.ofAdd ((g.a : K) * h.b + g.b)
      = Multiplicative.ofAdd g.b * (affineφ K g.a) (Multiplicative.ofAdd h.b)
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, affineφ_apply]
    exact add_comm _ _

omit [Fintype K] in
@[simp] lemma affineEquiv_apply (g : Problem4_12_6.Affine K) :
    affineEquiv K g = ⟨Multiplicative.ofAdd g.b, g.a⟩ := rfl

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.6.** The classification of the irreducible complex
representations of the affine group *as Problem 4.12.6 poses it* — the group
`Problem4_12_6.Affine K` of pairs `⟨a, b⟩` acting by `x ↦ a x + b` — derived from the orbit
method of Theorem 5.27.1 by transporting `affine_classification` along `affineEquiv`. For
`q = |K| > 2` there are exactly `q` irreducibles: `q - 1` of dimension `1` and one of dimension
`q - 1`. -/
theorem affine_classification' (hq : 2 < Fintype.card K) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Problem4_12_6.Affine K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Problem4_12_6.Affine K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter
        (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hn, hcard1, hcardq⟩ := affine_classification K hq
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    transport_classification (affineEquiv K) V hSimple hInj hComplete
  have hfilt : ∀ d : ℕ, (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = d)) =
      (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) :=
    fun d => filter_finrank_congr hWdim d
  refine ⟨n, W, hW1, hW2, hW3, hn, ?_, ?_⟩
  · rw [hfilt]; exact hcard1
  · rw [hfilt]; exact hcardq

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.6, degenerate field `K = 𝔽₂`.** The `q = 2` companion to
`affine_classification'`, transported onto `Problem4_12_6.Affine K` along `affineEquiv`: the
affine group over `𝔽₂` is `ℤ/2`, with two one-dimensional irreducibles. -/
theorem affine_classification_two' (hq : Fintype.card K = 2) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Problem4_12_6.Affine K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Problem4_12_6.Affine K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = 2 ∧
      (∀ i, finrank ℂ (W i : Type) = 1) := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hn, hdim⟩ := affine_classification_two K hq
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    transport_classification (affineEquiv K) V hSimple hInj hComplete
  exact ⟨n, W, hW1, hW2, hW3, hn, fun i => by rw [hWdim i]; exact hdim i⟩

/-! ## The transported family is the book's family

Problem 4.12.6 names its irreducibles: the `q - 1` one-dimensional characters `charRep χ` and
the single `(q-1)`-dimensional zero-sum representation `V` — the hint's subrepresentation
`Vsub` of the permutation representation on `K → ℂ`. Matching the orbit-method family against
that list is what makes "redo Problem 4.12.6 using Theorem 5.27.1" land on the book's own
answer rather than on an abstract count. -/

/-- The zero-sum representation `V` of Problem 4.12.6 — the hint's `(q-1)`-dimensional
subrepresentation of the permutation representation on `K → ℂ` — as an object of
`FDRep ℂ (Problem4_12_6.Affine K)`. -/
def zeroSumFDRep : FDRep ℂ (Problem4_12_6.Affine K) :=
  FDRep.of (Problem4_12_6.Vsub (K := K)).toRepresentation

/-- `V` has dimension `q - 1`. -/
lemma finrank_zeroSumFDRep :
    finrank ℂ (zeroSumFDRep K : Type) = Fintype.card K - 1 :=
  Problem4_12_6.zeroSum_finrank (K := K)

/-- `V` is irreducible (Problem 4.12.6's hint, `zeroSum_irreducible`). -/
lemma zeroSumFDRep_simple : Simple (zeroSumFDRep K) :=
  haveI := Problem4_12_6.Vrep_isSimpleModule (K := K) Fintype.one_lt_card
  Etingof.simple_fdRepOf_of_isSimpleModule _

open Classical in
/-- **The orbit-method family is the book's family.** For `q = |K| > 2`, the family of
irreducibles that Theorem 5.27.1 produces for `Problem4_12_6.Affine K` consists of exactly the
representations Problem 4.12.6 names, matched by dimension: every one-dimensional member is a
character `charRep χ` and every character occurs, while the unique `(q-1)`-dimensional member is
the zero-sum representation `V = Vsub`. So redoing Problem 4.12.6 through the orbit method
recovers the book's own list. -/
theorem affine_classification_named (hq : 2 < Fintype.card K) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Problem4_12_6.Affine K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Problem4_12_6.Affine K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter
        (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 ∧
      (∀ i, finrank ℂ (W i : Type) = 1 → ∃ χ : Problem4_12_6.Affine K →* ℂˣ,
        Nonempty (W i ≅ FDRep.of (Problem4_12_6.charRep χ))) ∧
      (∀ i, finrank ℂ (W i : Type) = Fintype.card K - 1 →
        Nonempty (W i ≅ zeroSumFDRep K)) ∧
      (∀ χ : Problem4_12_6.Affine K →* ℂˣ,
        ∃ i, Nonempty (FDRep.of (Problem4_12_6.charRep χ) ≅ W i)) ∧
      (∃ i, Nonempty (zeroSumFDRep K ≅ W i)) := by
  classical
  obtain ⟨n, W, hSimple, hInj, hComplete, hn, hcard1, hcardq⟩ := affine_classification' K hq
  refine ⟨n, W, hSimple, hInj, hComplete, hn, hcard1, hcardq, ?_, ?_, ?_, ?_⟩
  · -- a one-dimensional member is the character representation of its own character
    intro i hi
    obtain ⟨ξ, hξ⟩ := exists_charRep_iso_of_finrank_eq_one (W i) hi
    exact ⟨ξ, hξ⟩
  · -- the `(q-1)`-dimensional member is unique, and `V` is one such, so they agree
    intro i hi
    haveI := zeroSumFDRep_simple K
    obtain ⟨j, hj⟩ := hComplete (zeroSumFDRep K) inferInstance
    have hjdim : finrank ℂ (W j : Type) = Fintype.card K - 1 := by
      rw [← LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hj.some)]
      exact finrank_zeroSumFDRep K
    -- both `i` and `j` lie in a filter of cardinality one
    have hij : i = j := by
      have hmem : ∀ l : Fin n, finrank ℂ (W l : Type) = Fintype.card K - 1 →
          l ∈ Finset.univ.filter (fun l => finrank ℂ (W l : Type) = Fintype.card K - 1) :=
        fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
      exact Finset.card_le_one.mp (le_of_eq hcardq) i (hmem i hi) j (hmem j hjdim)
    exact ⟨hij ▸ hj.some.symm⟩
  · -- every character occurs: it is simple, so completeness catches it
    intro χ
    haveI : Simple (FDRep.of (Problem4_12_6.charRep χ)) := Problem4_12_6.charRep_simple χ
    exact hComplete _ inferInstance
  · -- `V` occurs, for the same reason
    haveI := zeroSumFDRep_simple K
    exact hComplete _ inferInstance

end Etingof.Exercise5_27_2
