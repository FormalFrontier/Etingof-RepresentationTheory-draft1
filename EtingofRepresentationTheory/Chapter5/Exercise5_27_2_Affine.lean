import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1
import EtingofRepresentationTheory.Chapter5.AbelianFDRep

/-!
# Exercise 5.27.2 (affine group): redo Problem 4.12.6 using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the **Problem 4.12.6** part: the group `G` of nonconstant inhomogeneous linear
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

Statement pass: the classification is stated; the proof is left as `sorry`.
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
the two orbit facts the classification needs, both consequences of the fact that over a **field**
every nontrivial additive character is *primitive* (`AddChar.IsPrimitive.of_ne_one`):

* `affineDualSmul_eq_self_iff` — a nontrivial character has **trivial** stabilizer (only `g = 1`
  fixes it), while the trivial character is fixed by all of `Kˣ` (`affineDualSmul_trivial`);
* `affineDualSmul_transitive` — `Kˣ` acts **transitively** on the `q - 1` nontrivial characters
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
has dimension `q - 1` (over the free orbit of nontrivial characters). -/
theorem affine_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (AffineGroup K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (AffineGroup K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 := by
  sorry

end Etingof.Exercise5_27_2
