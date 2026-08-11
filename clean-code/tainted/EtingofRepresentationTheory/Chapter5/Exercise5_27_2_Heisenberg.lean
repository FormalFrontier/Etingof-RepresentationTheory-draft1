import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1
import EtingofRepresentationTheory.Chapter5.AbelianFDRep
import EtingofRepresentationTheory.Chapter5.Exercise5_27_2_Transport
import EtingofRepresentationTheory.Chapter4.Problem4_12_2

/-!
# Exercise 5.27.2 (Heisenberg group): redo Problem 4.12.2 using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the **Problem 4.12.2** part: classify all irreducible complex
representations of the Heisenberg group `H_p`, the group of `3 × 3` upper unitriangular
matrices over `𝔽_p` (order `p³`).

## The Heisenberg group as a semidirect product

Writing a unitriangular matrix by its strict-upper entries `(a, b, c)` (positions `(1,2)`,
`(2,3)`, `(1,3)`), the product is `(a,b,c)·(a',b',c') = (a+a', b+b', c+c'+a·b')`. The
subgroup `A = {(0, b, c)}` is abelian and normal (order `p²`), with complement
`G = {(a, 0, 0)}` (order `p`); conjugation by `(a,0,0)` sends `(0,b,c) ↦ (0, b, c + a·b)`.
Thus

`H_p = A ⋊[φ] G`, with `A = Multiplicative (ZMod p × ZMod p)`, `G = Multiplicative (ZMod p)`,

and `φ a` the shear automorphism `(b, c) ↦ (b, c + a·b)` of `A`. Because `A` is abelian,
**Theorem 5.27.1** (the orbit method) applies directly.

## The classification (orbit method, Theorem 5.27.1)

The dual `G`-action on `Â = A →* ℂˣ ≅ (ℤ/p)²` sends the character indexed by `(β, γ)` to
the one indexed by `(β - a·γ, γ)`. Hence:

* **Fixed characters** are those with `γ = 0` (there are `p` of them), each with stabilizer
  all of `G`; over each, Theorem 5.27.1 gives one irreducible `V(χ, U)` per irreducible `U`
  of `G ≅ ℤ/p`, i.e. `p` one-dimensional characters. This yields `p · p = p²`
  one-dimensional irreducibles, exactly the characters of `H_p`, which factor through the
  abelianization `H_p / Z(H_p) ≅ (ℤ/p)²`.
* **Free orbits** are indexed by `γ ≠ 0` (there are `p - 1`), each of size `p` with trivial
  stabilizer; over each, Theorem 5.27.1 gives a single irreducible `V(χ, U)` of dimension
  `[G : G_χ] = p`. These are the `p - 1` representations `R_z` (`z ≠ 1`) of Problem 4.12.2.

So there are exactly `p² + (p - 1)` irreducibles: `p²` of dimension `1` and `p - 1` of
dimension `p`, consistent with `∑ dim² = p²·1 + (p-1)·p² = p³ = |H_p|`.

The classification `heisenberg_classification` follows from the orbit method: the induced
representations `V(χ, U)` of Theorem 5.27.1 are computed via the explicit character formula (iv),
whose closed forms (`fixed_charρ`, `free_char`) give both the pairwise non-isomorphism and the
completeness.

## Landing on the group of Problem 4.12.2

Problem 4.12.2 studies the unitriangular-matrix group `Problem4_12_2.Heisenberg p`, a different
type from the semidirect-product model `HeisenbergGroup p`. `heisenbergEquiv` is the group
isomorphism between them, `heisenberg_classification'` is the classification transported onto
the textbook group along it (via `Exercise5_27_2_Transport`), and
`heisenberg_classification_named` matches the transported family with the book's own named
representations: the `p²` characters `charRep χ` and the `p - 1` representations
`R_z = rhoHom z` with `z ≠ 1`.
-/

noncomputable section

open CategoryTheory Module

namespace Etingof.Exercise5_27_2

variable (p : ℕ) [Fact p.Prime]

/-- The shear automorphism `(b, c) ↦ (b, c + a·b)` of the abelian translation group
`Multiplicative (ZMod p × ZMod p)`, realized directly as a multiplicative automorphism. -/
def heisenbergShear (a : ZMod p) : MulAut (Multiplicative (ZMod p × ZMod p)) where
  toFun x := Multiplicative.ofAdd
    ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1)
  invFun x := Multiplicative.ofAdd
    ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 - a * (Multiplicative.toAdd x).1)
  left_inv x := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · change (Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1
        - a * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
      ring
  right_inv x := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · change (Multiplicative.toAdd x).2 - a * (Multiplicative.toAdd x).1
        + a * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
      ring
  map_mul' x y := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · change ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2)
          + a * ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1)
        = ((Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1)
          + ((Multiplicative.toAdd y).2 + a * (Multiplicative.toAdd y).1)
      ring

@[simp] lemma heisenbergShear_zero : heisenbergShear p 0 = 1 := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  apply Multiplicative.toAdd.injective
  change ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + 0 * (Multiplicative.toAdd x).1)
      = Multiplicative.toAdd x
  apply Prod.ext
  · rfl
  · change (Multiplicative.toAdd x).2 + 0 * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
    ring

lemma heisenbergShear_add (a a' : ZMod p) :
    heisenbergShear p (a + a') = heisenbergShear p a * heisenbergShear p a' := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply]
  apply Multiplicative.toAdd.injective
  change ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + (a + a') * (Multiplicative.toAdd x).1)
      = ((Multiplicative.toAdd x).1,
          (Multiplicative.toAdd x).2 + a' * (Multiplicative.toAdd x).1 + a * (Multiplicative.toAdd x).1)
  apply Prod.ext
  · rfl
  · change (Multiplicative.toAdd x).2 + (a + a') * (Multiplicative.toAdd x).1
        = (Multiplicative.toAdd x).2 + a' * (Multiplicative.toAdd x).1
          + a * ((Multiplicative.toAdd x).1)
    ring

/-- The `G`-action on the abelian normal subgroup `A` of the Heisenberg group: the
multiplicative element `a ∈ G = Multiplicative (ZMod p)` acts by the shear `φ a`. -/
def heisenbergφ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod p × ZMod p)) where
  toFun a := heisenbergShear p (Multiplicative.toAdd a)
  map_one' := by
    change heisenbergShear p (0 : ZMod p) = 1
    exact heisenbergShear_zero p
  map_mul' a a' := by
    change heisenbergShear p (Multiplicative.toAdd a + Multiplicative.toAdd a')
      = heisenbergShear p (Multiplicative.toAdd a) * heisenbergShear p (Multiplicative.toAdd a')
    exact heisenbergShear_add p _ _

/-- The **Heisenberg group** `H_p` over `𝔽_p`, realized as the semidirect product of its
abelian normal subgroup `A = (ℤ/p)²` by `G = ℤ/p` acting by the shear `φ`. -/
abbrev HeisenbergGroup : Type := Multiplicative (ZMod p × ZMod p) ⋊[heisenbergφ p] Multiplicative (ZMod p)

/-!
## Character parametrization of `Â = (ℤ/p)²` and the dual-action orbit combinatorics

We concretely parametrize the character group `Â = A →* ℂˣ` of `A = (ℤ/p)²` by pairs
`(β, γ) ∈ ZMod p × ZMod p` using a fixed primitive `p`-th root of unity `ζ`:
`χ_{β,γ}(b, c) = ζ^(β·b + γ·c)`. The dual `G`-action `χ ↦ χ ∘ φ(g⁻¹)` acts by
`(β, γ) ↦ (β − a·γ, γ)` where `a = Multiplicative.toAdd g`, so `γ` is an orbit
invariant: `γ = 0` gives fixed characters (stabilizer all of `G`), and `γ ≠ 0` gives free
orbits of size `p` (trivial stabilizer). These lemmas feed `Etingof.Theorem5_27_1`.
-/

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- A fixed primitive `p`-th root of unity in `ℂˣ`, used to parametrize the characters of
`A = (ℤ/p)²`. -/
noncomputable def heisenbergZeta : ℂˣ :=
  ((Complex.isPrimitiveRoot_exp p (NeZero.ne p)).isUnit (NeZero.ne p)).unit

lemma heisenbergZeta_primitive : IsPrimitiveRoot (heisenbergZeta p) p :=
  IsPrimitiveRoot.isUnit_unit (NeZero.ne p) (Complex.isPrimitiveRoot_exp p (NeZero.ne p))

/-- The `ZMod p`-linear exponent `(b, c) ↦ β·b + γ·c` used in the character `χ_{β,γ}`. -/
def heisenbergExp (β γ : ZMod p) : ZMod p × ZMod p →+ ZMod p :=
  (AddMonoidHom.mulLeft β).comp (AddMonoidHom.fst (ZMod p) (ZMod p)) +
    (AddMonoidHom.mulLeft γ).comp (AddMonoidHom.snd (ZMod p) (ZMod p))

@[simp] lemma heisenbergExp_apply (β γ : ZMod p) (bc : ZMod p × ZMod p) :
    heisenbergExp p β γ bc = β * bc.1 + γ * bc.2 := rfl

/-- The additive character `(b, c) ↦ ζ^(β·b + γ·c)` of `A = (ℤ/p)²`, valued in `ℂˣ`. -/
noncomputable def heisenbergAddChar (β γ : ZMod p) : AddChar (ZMod p × ZMod p) ℂˣ :=
  (AddChar.zmodChar p (heisenbergZeta_primitive p).pow_eq_one).compAddMonoidHom
    (heisenbergExp p β γ)

/-- The character `χ_{β,γ} : A →* ℂˣ` of `A = (ℤ/p)²`, `(b, c) ↦ ζ^(β·b + γ·c)`. -/
noncomputable def heisenbergChar (β γ : ZMod p) : Multiplicative (ZMod p × ZMod p) →* ℂˣ :=
  AddChar.toMonoidHomEquiv (heisenbergAddChar p β γ)

lemma heisenbergChar_apply (β γ : ZMod p) (b c : ZMod p) :
    heisenbergChar p β γ (Multiplicative.ofAdd (b, c)) =
      heisenbergZeta p ^ (β * b + γ * c).val := by
  rfl

/-- The shear `φ a` acts on `A` by `(b, c) ↦ (b, c + a·b)`. -/
lemma heisenbergφ_apply_ofAdd (a : Multiplicative (ZMod p)) (b c : ZMod p) :
    (heisenbergφ p a : MulAut _) (Multiplicative.ofAdd (b, c))
      = Multiplicative.ofAdd (b, c + Multiplicative.toAdd a * b) := rfl

/-- **Dual-action formula.** Precomposing `χ_{β,γ}` with the shear `φ(g⁻¹)`, i.e. applying the
dual `G`-action of `g`, yields `χ_{β − a·γ, γ}` where `a = Multiplicative.toAdd g`. This is
exactly what `Etingof.Theorem5_27_1`'s `dualSmul` unfolds to. -/
lemma heisenbergChar_comp_heisenbergφ_inv (g : Multiplicative (ZMod p)) (β γ : ZMod p) :
    (heisenbergChar p β γ).comp (heisenbergφ p g⁻¹ : MulAut _).toMonoidHom
      = heisenbergChar p (β - Multiplicative.toAdd g * γ) γ := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨b, c, rfl⟩ : ∃ b c, x = Multiplicative.ofAdd (b, c) :=
    ⟨(Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2, rfl⟩
  have hexp : β * b + γ * (c + Multiplicative.toAdd g⁻¹ * b)
      = (β - Multiplicative.toAdd g * γ) * b + γ * c := by
    rw [toAdd_inv]; ring
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, heisenbergφ_apply_ofAdd,
    heisenbergChar_apply, hexp]

/-- **Injectivity of the parametrization (equation form).** Equal characters have equal
parameters. Stated on a bare equation so downstream lemmas can apply it without higher-order
unification against `heisenbergChar`. -/
lemma heisenbergChar_inj {β γ β' γ' : ZMod p}
    (h : heisenbergChar p β γ = heisenbergChar p β' γ') : β = β' ∧ γ = γ' := by
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (1, 0))
  have h2 := DFunLike.congr_fun h (Multiplicative.ofAdd (0, 1))
  rw [heisenbergChar_apply, heisenbergChar_apply] at h1 h2
  simp only [mul_one, mul_zero, add_zero, zero_add] at h1 h2
  exact ⟨ZMod.val_injective p
      ((heisenbergZeta_primitive p).pow_inj (ZMod.val_lt β) (ZMod.val_lt β') h1),
    ZMod.val_injective p
      ((heisenbergZeta_primitive p).pow_inj (ZMod.val_lt γ) (ZMod.val_lt γ') h2)⟩

/-- **Injectivity of the parametrization.** Distinct `(β, γ)` give distinct characters. -/
lemma heisenbergChar_injective :
    Function.Injective (fun bg : ZMod p × ZMod p => heisenbergChar p bg.1 bg.2) := by
  rintro ⟨β, γ⟩ ⟨β', γ'⟩ h
  obtain ⟨hβ, hγ⟩ := heisenbergChar_inj p h
  exact Prod.ext hβ hγ

/-- **Fixed-point characterization.** `χ_{β,γ}` is fixed by the whole dual `G`-action iff
`γ = 0`. These are the `p` characters whose stabilizer is all of `G`. -/
lemma heisenbergChar_fixed_iff (β γ : ZMod p) :
    (∀ g : Multiplicative (ZMod p),
      (heisenbergChar p β γ).comp (heisenbergφ p g⁻¹ : MulAut _).toMonoidHom
        = heisenbergChar p β γ) ↔ γ = 0 := by
  constructor
  · intro hfix
    have hg1 := hfix (Multiplicative.ofAdd 1)
    rw [heisenbergChar_comp_heisenbergφ_inv] at hg1
    obtain ⟨h, -⟩ := heisenbergChar_inj p hg1
    simp only [toAdd_ofAdd, one_mul, sub_eq_self] at h
    exact h
  · rintro rfl g
    rw [heisenbergChar_comp_heisenbergφ_inv]
    simp

/-- **Free-orbit stabilizer.** For `γ ≠ 0`, the only `g` fixing `χ_{β,γ}` is the identity, so the
stabilizer is trivial and the orbit is free (size `p`). -/
lemma heisenbergChar_stab_free (β γ : ZMod p) (hγ : γ ≠ 0)
    (g : Multiplicative (ZMod p))
    (hg : (heisenbergChar p β γ).comp (heisenbergφ p g⁻¹ : MulAut _).toMonoidHom
      = heisenbergChar p β γ) :
    g = 1 := by
  rw [heisenbergChar_comp_heisenbergφ_inv] at hg
  obtain ⟨h, -⟩ := heisenbergChar_inj p hg
  have hz : Multiplicative.toAdd g * γ = 0 := sub_eq_self.mp h
  have htg : Multiplicative.toAdd g = 0 := (mul_eq_zero.mp hz).resolve_right hγ
  apply Multiplicative.toAdd.injective
  rw [htg]; rfl

/-- **Coverage.** The parametrization is surjective: every character of `A = (ℤ/p)²` is `χ_{β,γ}`
for some `(β, γ)`. Combined with `heisenbergChar_injective`, this makes `(β, γ) ↦ χ_{β,γ}` a
bijection onto `Â`. -/
lemma heisenbergChar_surjective (χ : Multiplicative (ZMod p × ZMod p) →* ℂˣ) :
    ∃ β γ, heisenbergChar p β γ = χ := by
  classical
  haveI : Fintype (Multiplicative (ZMod p × ZMod p) →* ℂˣ) := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod p × ZMod p)
      = Fintype.card (Multiplicative (ZMod p × ZMod p) →* ℂˣ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Etingof.AbelianFDRep.card_charFDRep_dual]
    exact (Nat.card_congr Multiplicative.ofAdd)
  have hbij := (Fintype.bijective_iff_injective_and_card
    (fun bg : ZMod p × ZMod p => heisenbergChar p bg.1 bg.2)).mpr
    ⟨heisenbergChar_injective p, hcard⟩
  obtain ⟨bg, hbg⟩ := hbij.surjective χ
  exact ⟨bg.1, bg.2, hbg⟩

/-!
## The complex-valued additive character and the orthogonality sum

To compute the character of the induced representations `V(χ, U)` via Theorem 5.27.1's character
formula (iv), we package `ζ^(·)` as a complex-valued additive character `heisenbergPsi`
of `ZMod p`, whose primitivity yields the geometric-sum (orthogonality) identity
`∑_t ψ(t·m) = if m = 0 then p else 0`. This collapses the inner sum in the character formula.
-/

/-- `heisenbergZeta` as a complex number is a `p`-th root of unity. -/
lemma heisenbergZeta_coe_pow : ((heisenbergZeta p : ℂ)) ^ p = 1 := by
  have h := (heisenbergZeta_primitive p).pow_eq_one
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

/-- `heisenbergZeta` as a complex number is a primitive `p`-th root of unity. -/
lemma heisenbergZeta_coe_primitive : IsPrimitiveRoot ((heisenbergZeta p : ℂ)) p :=
  IsPrimitiveRoot.coe_units_iff.mpr (heisenbergZeta_primitive p)

/-- The complex-valued additive character `ψ : ZMod p → ℂ`, `x ↦ ζ^(x.val)`. Primitive, so its
orthogonality relations give the geometric sums appearing in the character formula. -/
noncomputable def heisenbergPsi : AddChar (ZMod p) ℂ :=
  AddChar.zmodChar p (heisenbergZeta_coe_pow p)

lemma heisenbergPsi_apply (x : ZMod p) : heisenbergPsi p x = (heisenbergZeta p : ℂ) ^ x.val :=
  AddChar.zmodChar_apply _ x

lemma heisenbergPsi_primitive : (heisenbergPsi p).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root p (heisenbergZeta_coe_primitive p)

/-- The coerced value of `χ_{β,γ}` is `ψ(β·b + γ·c)`. -/
lemma heisenbergChar_coe_eq_psi (β γ b c : ZMod p) :
    ((heisenbergChar p β γ (Multiplicative.ofAdd (b, c)) : ℂˣ) : ℂ)
      = heisenbergPsi p (β * b + γ * c) := by
  rw [heisenbergChar_apply, Units.val_pow_eq_pow_val, heisenbergPsi_apply]

/-- **Orthogonality collapse.** Summing `χ_{β,γ}` over the shear-translates of `(b, c)` gives
`(if γ·b = 0 then p else 0) · χ_{β,γ}(b, c)`. This is the inner sum of the character formula (iv)
after the (abelian) conjugation `h·g·h⁻¹ = g` has been carried out. -/
lemma heisenberg_shear_sum (β γ b c : ZMod p) :
    ∑ h : Multiplicative (ZMod p),
      ((heisenbergChar p β γ
        (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ)
    = (if γ * b = 0 then (p : ℂ) else 0) *
        ((heisenbergChar p β γ (Multiplicative.ofAdd (b, c)) : ℂˣ) : ℂ) := by
  have hterm : ∀ h : Multiplicative (ZMod p),
      ((heisenbergChar p β γ
        (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ)
        = heisenbergPsi p (β * b + γ * c) *
            heisenbergPsi p (γ * b * Multiplicative.toAdd h) := by
    intro h
    rw [heisenbergChar_coe_eq_psi,
      show β * b + γ * (c + Multiplicative.toAdd h * b)
        = (β * b + γ * c) + (γ * b * Multiplicative.toAdd h) from by ring,
      AddChar.map_add_eq_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hreindex : ∑ h : Multiplicative (ZMod p),
        heisenbergPsi p (γ * b * Multiplicative.toAdd h)
      = ∑ t : ZMod p, heisenbergPsi p (t * (γ * b)) :=
    Fintype.sum_equiv (Multiplicative.toAdd (α := ZMod p)) _ _ (fun h => by rw [mul_comm])
  rw [hreindex, AddChar.sum_mulShift (γ * b) (heisenbergPsi_primitive p), ZMod.card,
    heisenbergChar_coe_eq_psi]
  push_cast
  ring

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.2.** The complete classification of the irreducible
complex representations of the Heisenberg group `H_p` (order `p³`), obtained from Theorem
5.27.1 via the semidirect-product structure `(ℤ/p)² ⋊ ℤ/p`: there are exactly `p² + (p-1)`
pairwise non-isomorphic irreducibles forming a complete set, of which `p²` have dimension `1`
(the characters factoring through the abelianization `(ℤ/p)²`) and `p - 1` have dimension `p`
(the representations `R_z`, `z ≠ 1`, over the free orbits). Every irreducible has dimension
`1` or `p`, and `∑ dim² = p²·1 + (p-1)·p² = p³ = |H_p|`. -/
theorem heisenberg_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (HeisenbergGroup p)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (HeisenbergGroup p), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = p) ∧
      n = p ^ 2 + (p - 1) ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = p ^ 2 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = p)).card = p - 1 := by
  classical
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport, hi, hii, hiii, hiv, hv, hvi, _, _, _⟩ :=
    Etingof.Theorem5_27_1 (Multiplicative (ZMod p)) (Multiplicative (ZMod p × ZMod p))
      (heisenbergφ p)
  -- Dual action on the parametrized characters: `g · χ_{β,γ} = χ_{β − a·γ, γ}`.
  have hdualhb : ∀ (g : Multiplicative (ZMod p)) (β γ : ZMod p),
      dualSmul g (heisenbergChar p β γ)
        = heisenbergChar p (β - Multiplicative.toAdd g * γ) γ := by
    intro g β γ
    refine MonoidHom.ext fun a => ?_
    exact (hdual g (heisenbergChar p β γ) a).trans
      (DFunLike.congr_fun (heisenbergChar_comp_heisenbergφ_inv p g β γ) a)
  -- Fixed characters (γ = 0) have full stabilizer.
  have hstab_f : ∀ β : ZMod p, stab (heisenbergChar p β 0) = ⊤ := by
    intro β
    rw [eq_top_iff]
    intro g _
    rw [hstab (heisenbergChar p β 0) g, hdualhb]
    simp
  -- Free characters (γ ≠ 0) have trivial stabilizer.
  have hstab_r : ∀ (β γ : ZMod p), γ ≠ 0 → stab (heisenbergChar p β γ) = ⊥ := by
    intro β γ hγ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    rw [hstab (heisenbergChar p β γ) g, hdualhb] at hg
    obtain ⟨h1, -⟩ := heisenbergChar_inj p hg
    have hz : Multiplicative.toAdd g * γ = 0 := sub_eq_self.mp h1
    have htg : Multiplicative.toAdd g = 0 := (mul_eq_zero.mp hz).resolve_right hγ
    exact Multiplicative.toAdd.injective (by rw [htg]; rfl)
  -- Conjugation is trivial (`G` abelian): `h·g·h⁻¹ = g`.
  have hconj : ∀ (h g : Multiplicative (ZMod p)), h * g * h⁻¹ = g := by
    intro h g; rw [mul_right_comm, mul_inv_cancel, one_mul]
  -- Cardinality of the complement `G = ℤ/p`.
  have hcardG : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_eq_fintype_card, ZMod.card]
  haveI : Fintype (Multiplicative (ZMod p) →* ℂˣ) := Fintype.ofFinite _
  haveI : Finite (HeisenbergGroup p) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  -- **Closed-form character of the fixed-orbit (1-dim) reps.** (Proved below.)
  have fixed_charρ : ∀ (β : ZMod p) (ρ : Multiplicative (ZMod p) →* ℂˣ)
      (b c : ZMod p) (g : Multiplicative (ZMod p)),
      (V (heisenbergChar p β 0)
        (Etingof.AbelianFDRep.charFDRep
          (ρ.comp (stab (heisenbergChar p β 0)).subtype))).character
          ⟨Multiplicative.ofAdd (b, c), g⟩
      = ((ρ g : ℂˣ) : ℂ) * (heisenbergZeta p : ℂ) ^ (β * b).val := by
    intro β ρ b c g
    have hSimpleU := Etingof.AbelianFDRep.charFDRep_simple
      (ρ.comp (stab (heisenbergChar p β 0)).subtype)
    have hmemg : g ∈ stab (heisenbergChar p β 0) := by rw [hstab_f β]; exact Subgroup.mem_top g
    have hmemall : ∀ h : Multiplicative (ZMod p), h * g * h⁻¹ ∈ stab (heisenbergChar p β 0) := by
      intro h; rw [hstab_f β]; exact Subgroup.mem_top _
    have hcard : Fintype.card ↥(stab (heisenbergChar p β 0)) = p := by
      rw [← Nat.card_eq_fintype_card, hstab_f β, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
    have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).pos.ne'
    have hterm : ∀ h : Multiplicative (ZMod p),
        (if hh : h * g * h⁻¹ ∈ stab (heisenbergChar p β 0)
          then ((heisenbergChar p β 0
                ((heisenbergφ p h : MulAut _) (Multiplicative.ofAdd (b, c))) : ℂˣ) : ℂ)
              * (Etingof.AbelianFDRep.charFDRep
                  (ρ.comp (stab (heisenbergChar p β 0)).subtype)).character ⟨h * g * h⁻¹, hh⟩
          else 0)
        = ((ρ g : ℂˣ) : ℂ)
            * ((heisenbergChar p β 0
                (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ) := by
      intro h
      rw [dif_pos (hmemall h),
        show (⟨h * g * h⁻¹, hmemall h⟩ : ↥(stab (heisenbergChar p β 0))) = ⟨g, hmemg⟩ from
          Subtype.ext (hconj h g),
        Etingof.AbelianFDRep.charFDRep_character, heisenbergφ_apply_ofAdd,
        show ((ρ.comp (stab (heisenbergChar p β 0)).subtype) ⟨g, hmemg⟩ : ℂˣ) = ρ g from rfl,
        mul_comm]
    rw [hiv (heisenbergChar p β 0) _ hSimpleU (Multiplicative.ofAdd (b, c)) g,
      Finset.sum_congr rfl (fun h _ => hterm h), ← Finset.mul_sum, heisenberg_shear_sum, hcard,
      zero_mul, if_pos rfl, heisenbergChar_apply, Units.val_pow_eq_pow_val,
      show β * b + 0 * c = β * b from by ring]
    field_simp
  -- **Closed-form character of the free-orbit (p-dim) reps.** (Proved below.)
  have free_char : ∀ (β γ : ZMod p), γ ≠ 0 → ∀ (b c : ZMod p) (g : Multiplicative (ZMod p)),
      (V (heisenbergChar p β γ)
        (Etingof.AbelianFDRep.charFDRep
          (1 : ↥(stab (heisenbergChar p β γ)) →* ℂˣ))).character
          ⟨Multiplicative.ofAdd (b, c), g⟩
      = if g = 1 ∧ b = 0 then (p : ℂ) * (heisenbergZeta p : ℂ) ^ (γ * c).val else 0 := by
    intro β γ hγ b c g
    have hSimpleU := Etingof.AbelianFDRep.charFDRep_simple
      (1 : ↥(stab (heisenbergChar p β γ)) →* ℂˣ)
    have hcard1 : Fintype.card ↥(stab (heisenbergChar p β γ)) = 1 := by
      rw [← Nat.card_eq_fintype_card, hstab_r β γ hγ]; exact Subgroup.card_bot
    rw [hiv (heisenbergChar p β γ) _ hSimpleU (Multiplicative.ofAdd (b, c)) g, hcard1]
    simp only [Nat.cast_one, inv_one, one_mul]
    by_cases hg : g = 1
    · subst hg
      have hterm : ∀ h : Multiplicative (ZMod p),
          (if hh : h * 1 * h⁻¹ ∈ stab (heisenbergChar p β γ)
            then ((heisenbergChar p β γ
                  ((heisenbergφ p h : MulAut _) (Multiplicative.ofAdd (b, c))) : ℂˣ) : ℂ)
                * (Etingof.AbelianFDRep.charFDRep
                    (1 : ↥(stab (heisenbergChar p β γ)) →* ℂˣ)).character ⟨h * 1 * h⁻¹, hh⟩
            else 0)
          = ((heisenbergChar p β γ
              (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ) := by
        intro h
        have hmem : h * 1 * h⁻¹ ∈ stab (heisenbergChar p β γ) := by
          rw [hconj, hstab_r β γ hγ]; exact Subgroup.one_mem _
        rw [dif_pos hmem, Etingof.AbelianFDRep.charFDRep_character, MonoidHom.one_apply,
          Units.val_one, mul_one, heisenbergφ_apply_ofAdd]
      rw [Finset.sum_congr rfl (fun h _ => hterm h), heisenberg_shear_sum]
      by_cases hb : b = 0
      · subst hb
        rw [mul_zero, if_pos rfl, if_pos ⟨rfl, rfl⟩, heisenbergChar_apply,
          Units.val_pow_eq_pow_val, show β * 0 + γ * c = γ * c from by ring]
      · rw [if_neg (fun h => hb ((mul_eq_zero.mp h).resolve_left hγ)),
          if_neg (fun h => hb h.2), zero_mul]
    · have hterm0 : ∀ h : Multiplicative (ZMod p),
          (if hh : h * g * h⁻¹ ∈ stab (heisenbergChar p β γ)
            then ((heisenbergChar p β γ
                  ((heisenbergφ p h : MulAut _) (Multiplicative.ofAdd (b, c))) : ℂˣ) : ℂ)
                * (Etingof.AbelianFDRep.charFDRep
                    (1 : ↥(stab (heisenbergChar p β γ)) →* ℂˣ)).character ⟨h * g * h⁻¹, hh⟩
            else 0) = 0 := by
        intro h
        rw [dif_neg]
        intro hmem
        rw [hconj, hstab_r β γ hγ, Subgroup.mem_bot] at hmem
        exact hg hmem
      rw [Finset.sum_congr rfl (fun h _ => hterm0 h), Finset.sum_const_zero,
        if_neg (fun h => hg h.1)]
  -- The index type and family.
  let ι := (ZMod p × (Multiplicative (ZMod p) →* ℂˣ)) ⊕ {γ : ZMod p // γ ≠ 0}
  let F : ι → FDRep ℂ (HeisenbergGroup p) :=
    Sum.elim
      (fun x => V (heisenbergChar p x.1 0)
        (Etingof.AbelianFDRep.charFDRep (x.2.comp (stab (heisenbergChar p x.1 0)).subtype)))
      (fun y => V (heisenbergChar p 0 y.1)
        (Etingof.AbelianFDRep.charFDRep (1 : ↥(stab (heisenbergChar p 0 y.1)) →* ℂˣ)))
  have hFsimple : ∀ a : ι, Simple (F a) := by
    rintro (⟨β, ρ⟩ | ⟨γ, hγ⟩)
    · exact hi _ _ (Etingof.AbelianFDRep.charFDRep_simple _)
    · exact hi _ _ (Etingof.AbelianFDRep.charFDRep_simple _)
  have hFdim1 : ∀ (β : ZMod p) (ρ : Multiplicative (ZMod p) →* ℂˣ),
      finrank ℂ (F (Sum.inl (β, ρ)) : Type) = 1 := by
    intro β ρ
    change finrank ℂ (V (heisenbergChar p β 0) _ : Type) = 1
    rw [hv, hstab_f β, Subgroup.index_top, Etingof.AbelianFDRep.charFDRep_finrank, mul_one]
  have hFdimp : ∀ (γ : ZMod p) (hγ : γ ≠ 0),
      finrank ℂ (F (Sum.inr ⟨γ, hγ⟩) : Type) = p := by
    intro γ hγ
    change finrank ℂ (V (heisenbergChar p 0 γ) _ : Type) = p
    rw [hv, hstab_r 0 γ hγ, Subgroup.index_bot, Etingof.AbelianFDRep.charFDRep_finrank, mul_one,
      hcardG]
  have hFdim : ∀ a : ι, finrank ℂ (F a : Type) = 1 ∨ finrank ℂ (F a : Type) = p := by
    rintro (⟨β, ρ⟩ | ⟨γ, hγ⟩)
    · exact Or.inl (hFdim1 β ρ)
    · exact Or.inr (hFdimp γ hγ)
  have hFinj : ∀ a b : ι, Nonempty (F a ≅ F b) → a = b := by
    rintro (⟨β, ρ⟩ | ⟨γ, hγ⟩) (⟨β', ρ'⟩ | ⟨γ', hγ'⟩) ⟨α⟩
    · -- fixed vs fixed: distinguish `β` (via `(1,0,1)`) and `ρ` (via `(0,0,g)`)
      have hchar := FDRep.char_iso α
      have hρ : ρ = ρ' := by
        refine MonoidHom.ext fun g => ?_
        have e1 : (F (Sum.inl (β, ρ))).character
              (⟨Multiplicative.ofAdd ((0 : ZMod p), (0 : ZMod p)), g⟩ : HeisenbergGroup p)
            = ((ρ g : ℂˣ) : ℂ) * (heisenbergZeta p : ℂ) ^ (β * (0 : ZMod p)).val :=
          fixed_charρ β ρ 0 0 g
        have e2 : (F (Sum.inl (β', ρ'))).character
              (⟨Multiplicative.ofAdd ((0 : ZMod p), (0 : ZMod p)), g⟩ : HeisenbergGroup p)
            = ((ρ' g : ℂˣ) : ℂ) * (heisenbergZeta p : ℂ) ^ (β' * (0 : ZMod p)).val :=
          fixed_charρ β' ρ' 0 0 g
        have h0 := congrFun hchar
          (⟨Multiplicative.ofAdd ((0 : ZMod p), (0 : ZMod p)), g⟩ : HeisenbergGroup p)
        rw [e1, e2] at h0
        simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one] at h0
        exact Units.ext h0
      have hβ : β = β' := by
        have e1 : (F (Sum.inl (β, ρ))).character
              (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
                (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
            = ((ρ 1 : ℂˣ) : ℂ) * (heisenbergZeta p : ℂ) ^ (β * (1 : ZMod p)).val :=
          fixed_charρ β ρ 1 0 1
        have e2 : (F (Sum.inl (β', ρ'))).character
              (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
                (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
            = ((ρ' 1 : ℂˣ) : ℂ) * (heisenbergZeta p : ℂ) ^ (β' * (1 : ZMod p)).val :=
          fixed_charρ β' ρ' 1 0 1
        have h1 := congrFun hchar
          (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
            (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
        rw [e1, e2] at h1
        simp only [map_one, Units.val_one, one_mul, mul_one] at h1
        exact ZMod.val_injective p
          ((heisenbergZeta_coe_primitive p).pow_inj (ZMod.val_lt β) (ZMod.val_lt β') h1)
      exact congrArg Sum.inl (Prod.ext hβ hρ)
    · -- fixed vs free: impossible (`ζ^(β.val) ≠ 0` but free char there is `0`)
      exfalso
      have hchar := FDRep.char_iso α
      have e1 : (F (Sum.inl (β, ρ))).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
          = ((ρ 1 : ℂˣ) : ℂ) * (heisenbergZeta p : ℂ) ^ (β * (1 : ZMod p)).val :=
        fixed_charρ β ρ 1 0 1
      have e2 : (F (Sum.inr ⟨γ', hγ'⟩)).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (1 : ZMod p) = 0
              then (p : ℂ) * (heisenbergZeta p : ℂ) ^ (γ' * (0 : ZMod p)).val else 0 :=
        free_char 0 γ' hγ' 1 0 1
      have h1 := congrFun hchar
        (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
          (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
      rw [e1, e2, if_neg (fun h => one_ne_zero h.2)] at h1
      simp only [map_one, Units.val_one, one_mul, mul_one] at h1
      exact pow_ne_zero _ (Units.ne_zero (heisenbergZeta p)) h1
    · -- free vs fixed: symmetric impossibility
      exfalso
      have hchar := FDRep.char_iso α
      have e1 : (F (Sum.inr ⟨γ, hγ⟩)).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (1 : ZMod p) = 0
              then (p : ℂ) * (heisenbergZeta p : ℂ) ^ (γ * (0 : ZMod p)).val else 0 :=
        free_char 0 γ hγ 1 0 1
      have e2 : (F (Sum.inl (β', ρ'))).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
          = ((ρ' 1 : ℂˣ) : ℂ) * (heisenbergZeta p : ℂ) ^ (β' * (1 : ZMod p)).val :=
        fixed_charρ β' ρ' 1 0 1
      have h1 := congrFun hchar
        (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
          (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
      rw [e1, e2, if_neg (fun h => one_ne_zero h.2)] at h1
      simp only [map_one, Units.val_one, one_mul, mul_one] at h1
      exact pow_ne_zero _ (Units.ne_zero (heisenbergZeta p)) h1.symm
    · -- free vs free: distinguish `γ` (via `(0,1,1)`)
      have hchar := FDRep.char_iso α
      have e1 : (F (Sum.inr ⟨γ, hγ⟩)).character
            (⟨Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (0 : ZMod p) = 0
              then (p : ℂ) * (heisenbergZeta p : ℂ) ^ (γ * (1 : ZMod p)).val else 0 :=
        free_char 0 γ hγ 0 1 1
      have e2 : (F (Sum.inr ⟨γ', hγ'⟩)).character
            (⟨Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (0 : ZMod p) = 0
              then (p : ℂ) * (heisenbergZeta p : ℂ) ^ (γ' * (1 : ZMod p)).val else 0 :=
        free_char 0 γ' hγ' 0 1 1
      have h1 := congrFun hchar
        (⟨Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)),
          (1 : Multiplicative (ZMod p))⟩ : HeisenbergGroup p)
      rw [e1, e2, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, mul_one, mul_one] at h1
      have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).pos.ne'
      have h2 := mul_left_cancel₀ hp h1
      exact congrArg Sum.inr (Subtype.ext (ZMod.val_injective p
        ((heisenbergZeta_coe_primitive p).pow_inj (ZMod.val_lt γ) (ZMod.val_lt γ') h2)))
  have hFcomplete : ∀ S : FDRep ℂ (HeisenbergGroup p), Simple S → ∃ a : ι, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    obtain ⟨β, γ, rfl⟩ := heisenbergChar_surjective p χ
    haveI : Simple U := hU
    by_cases hγ : γ = 0
    · -- fixed orbit: `U ≅ charFDRep ξ`, recover `ρ : G →* ℂˣ` from `ξ` (stabilizer is `⊤`)
      subst hγ
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso U
      let eStab : ↥(stab (heisenbergChar p β 0)) ≃* Multiplicative (ZMod p) :=
        (MulEquiv.subgroupCongr (hstab_f β)).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab (heisenbergChar p β 0)).subtype s) := fun s => rfl
      refine ⟨Sum.inl (β, ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp
          (stab (heisenbergChar p β 0)).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab (heisenbergChar p β 0)).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (β, ξ.comp eStab.symm.toMonoidHom))
          = V (heisenbergChar p β 0) (Etingof.AbelianFDRep.charFDRep ξ) := by
        change V (heisenbergChar p β 0)
            (Etingof.AbelianFDRep.charFDRep
              ((ξ.comp eStab.symm.toMonoidHom).comp (stab (heisenbergChar p β 0)).subtype))
          = V (heisenbergChar p β 0) (Etingof.AbelianFDRep.charFDRep ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫
        (hvi (heisenbergChar p β 0) U (Etingof.AbelianFDRep.charFDRep ξ) hξ).some⟩
    · -- free orbit: `U ≅ charFDRep 1`, move base point `χ_{β,γ} ⇝ χ_{0,γ}` via equal characters
      refine ⟨Sum.inr ⟨γ, hγ⟩, ?_⟩
      haveI : Subsingleton ↥(stab (heisenbergChar p β γ)) := by
        rw [hstab_r β γ hγ]
        exact ⟨fun a b => Subtype.ext
          (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      obtain ⟨ξ, hξ⟩ := Etingof.AbelianFDRep.exists_charFDRep_iso U
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_
        rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ
      have hchareq : (V (heisenbergChar p β γ)
            (Etingof.AbelianFDRep.charFDRep
              (1 : ↥(stab (heisenbergChar p β γ)) →* ℂˣ))).character
          = (V (heisenbergChar p 0 γ)
            (Etingof.AbelianFDRep.charFDRep
              (1 : ↥(stab (heisenbergChar p 0 γ)) →* ℂˣ))).character := by
        funext x
        obtain ⟨a, gg⟩ := x
        obtain ⟨b, c, rfl⟩ : ∃ b c, a = Multiplicative.ofAdd (b, c) :=
          ⟨(Multiplicative.toAdd a).1, (Multiplicative.toAdd a).2, rfl⟩
        rw [free_char β γ hγ b c gg, free_char 0 γ hγ b c gg]
      exact ⟨hSU.some ≪≫ (hvi (heisenbergChar p β γ) U _ hξ).some
        ≪≫ (Etingof.charEq_iso _ _ hchareq).some⟩
  -- Cardinalities feeding the counts.
  have hcardHom : Fintype.card (Multiplicative (ZMod p) →* ℂˣ) = p := by
    rw [← Nat.card_eq_fintype_card, Etingof.AbelianFDRep.card_charFDRep_dual, hcardG]
  have hcardSub : Fintype.card {γ : ZMod p // γ ≠ 0} = p - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hleft1 : ∀ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
      (if finrank ℂ (F (Sum.inl x) : Type) = 1 then (1 : ℕ) else 0) = 1 := by
    rintro ⟨β, ρ⟩; rw [if_pos (hFdim1 β ρ)]
  have hright1 : ∀ y : {γ : ZMod p // γ ≠ 0},
      (if finrank ℂ (F (Sum.inr y) : Type) = 1 then (1 : ℕ) else 0) = 0 := by
    rintro ⟨γ, hγ⟩; rw [if_neg fun h => hp1 (by rw [hFdimp γ hγ] at h; exact h)]
  have hleftp : ∀ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
      (if finrank ℂ (F (Sum.inl x) : Type) = p then (1 : ℕ) else 0) = 0 := by
    rintro ⟨β, ρ⟩; rw [if_neg fun h => hp1 (by rw [hFdim1 β ρ] at h; exact h.symm)]
  have hrightp : ∀ y : {γ : ZMod p // γ ≠ 0},
      (if finrank ℂ (F (Sum.inr y) : Type) = p then (1 : ℕ) else 0) = 1 := by
    rintro ⟨γ, hγ⟩; rw [if_pos (hFdimp γ hγ)]
  -- Transport the family to `Fin (card ι)`.
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij
    exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · exact fun i => hFdim (e.symm i)
  · have hcard : Fintype.card ι
        = Fintype.card (ZMod p × (Multiplicative (ZMod p) →* ℂˣ))
          + Fintype.card {γ : ZMod p // γ ≠ 0} := Fintype.card_sum
    rw [hcard, Fintype.card_prod, ZMod.card, hcardHom, hcardSub, pow_two]
  · rw [Finset.card_filter,
      Equiv.sum_comp e.symm (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0)]
    have hsum : (∑ a : ι, if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0)
        = (∑ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
            if finrank ℂ (F (Sum.inl x) : Type) = 1 then (1 : ℕ) else 0)
          + ∑ y : {γ : ZMod p // γ ≠ 0},
            if finrank ℂ (F (Sum.inr y) : Type) = 1 then (1 : ℕ) else 0 :=
      Fintype.sum_sum_type _
    rw [hsum]
    simp only [hleft1, hright1, Finset.sum_const, smul_eq_mul, mul_one,
      mul_zero, add_zero, Finset.card_univ, Fintype.card_prod, ZMod.card, hcardHom, pow_two]
  · rw [Finset.card_filter,
      Equiv.sum_comp e.symm (fun a => if finrank ℂ (F a : Type) = p then (1 : ℕ) else 0)]
    have hsum : (∑ a : ι, if finrank ℂ (F a : Type) = p then (1 : ℕ) else 0)
        = (∑ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
            if finrank ℂ (F (Sum.inl x) : Type) = p then (1 : ℕ) else 0)
          + ∑ y : {γ : ZMod p // γ ≠ 0},
            if finrank ℂ (F (Sum.inr y) : Type) = p then (1 : ℕ) else 0 :=
      Fintype.sum_sum_type _
    rw [hsum]
    simp only [hleftp, hrightp, Finset.sum_const, smul_eq_mul, mul_one,
      mul_zero, zero_add, Finset.card_univ, hcardSub]

/-! ## Landing the classification on the group of Problem 4.12.2

Problem 4.12.2 studies the Heisenberg group as the `structure Problem4_12_2.Heisenberg p` of
unitriangular matrices `[[1,a,c],[0,1,b],[0,0,1]]`, with product
`⟨a,b,c⟩ * ⟨a',b',c'⟩ = ⟨a+a', b+b', c+c'+a·b'⟩`. That is a different type from the
semidirect-product model `HeisenbergGroup p` used above, so "redo Problem 4.12.2" is only
finished once the orbit-method classification is transported onto it. The identification sends
the matrix `⟨a,b,c⟩` to the pair `⟨(b, c), a⟩`: the abelian normal subgroup is the last two
entries and the complement is the first. -/

/-- **The Heisenberg group of Problem 4.12.2 is the semidirect-product model.** The
unitriangular matrix `⟨a,b,c⟩` corresponds to `⟨ofAdd (b, c), ofAdd a⟩`: no shear correction is
needed, because `⟨a,b,c⟩ * ⟨a',b',c'⟩ = ⟨a+a', b+b', c+c'+a·b'⟩` matches the semidirect product
`⟨(u₁,v₁), a₁⟩ * ⟨(u₂,v₂), a₂⟩ = ⟨(u₁+u₂, v₁+v₂+a₁·u₂), a₁+a₂⟩` under `u ↔ b`, `v ↔ c`. -/
def heisenbergEquiv : Problem4_12_2.Heisenberg p ≃* HeisenbergGroup p where
  toFun x := ⟨Multiplicative.ofAdd (x.b, x.c), Multiplicative.ofAdd x.a⟩
  invFun y := ⟨Multiplicative.toAdd y.right, (Multiplicative.toAdd y.left).1,
    (Multiplicative.toAdd y.left).2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := by
    refine SemidirectProduct.ext ?_ rfl
    change Multiplicative.ofAdd (x.b + y.b, x.c + y.c + x.a * y.b)
      = Multiplicative.ofAdd (x.b, x.c) * heisenbergShear p x.a (Multiplicative.ofAdd (y.b, y.c))
    apply Multiplicative.toAdd.injective
    exact Prod.ext rfl (by change x.c + y.c + x.a * y.b = x.c + (y.c + x.a * y.b); ring)

@[simp] lemma heisenbergEquiv_apply (x : Problem4_12_2.Heisenberg p) :
    heisenbergEquiv p x = ⟨Multiplicative.ofAdd (x.b, x.c), Multiplicative.ofAdd x.a⟩ := rfl

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.2.** The classification of the irreducible complex
representations of the Heisenberg group *as Problem 4.12.2 poses it* — the group
`Problem4_12_2.Heisenberg p` of `3 × 3` unitriangular matrices over `𝔽_p` — derived from the
orbit method of Theorem 5.27.1 by transporting `heisenberg_classification` along
`heisenbergEquiv`. There are `p² + (p-1)` irreducibles: `p²` of dimension `1` and `p - 1` of
dimension `p`. -/
theorem heisenberg_classification' :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Problem4_12_2.Heisenberg p)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Problem4_12_2.Heisenberg p), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = p) ∧
      n = p ^ 2 + (p - 1) ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = p ^ 2 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = p)).card = p - 1 := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hDim, hn, hcard1, hcardp⟩ := heisenberg_classification p
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    transport_classification (heisenbergEquiv p) V hSimple hInj hComplete
  have hfilt : ∀ d : ℕ, (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = d)) =
      (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) :=
    fun d => filter_finrank_congr hWdim d
  refine ⟨n, W, hW1, hW2, hW3, fun i => by rw [hWdim i]; exact hDim i, hn, ?_, ?_⟩
  · rw [hfilt]; exact hcard1
  · rw [hfilt]; exact hcardp

open Classical in
/-- **The orbit-method family is the book's family.** Problem 4.12.2 names its irreducibles:
the `p²` one-dimensional characters `charRep χ` and the `p - 1` representations
`R_z = rhoHom z` for `z ≠ 1` a `p`-th root of unity. The family produced by the orbit method
consists of exactly those, matched by dimension: every `1`-dimensional member is a character,
every `p`-dimensional member is some `R_z` with `z ≠ 1`, and conversely every character and
every `R_z` (`z ≠ 1`) occurs in the family. So "redo Problem 4.12.2 using Theorem 5.27.1"
lands on the book's own list of representations. -/
theorem heisenberg_classification_named :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Problem4_12_2.Heisenberg p)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Problem4_12_2.Heisenberg p), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = p ^ 2 + (p - 1) ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = p ^ 2 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = p)).card = p - 1 ∧
      (∀ i, finrank ℂ (W i : Type) = 1 → ∃ χ : Problem4_12_2.Heisenberg p →* ℂˣ,
        Nonempty (W i ≅ FDRep.of (Etingof.Example4_3_S3.charRep χ))) ∧
      (∀ i, finrank ℂ (W i : Type) = p → ∃ (z : ℂ) (hz : z ^ p = 1), z ≠ 1 ∧
        Nonempty (W i ≅ FDRep.of (Problem4_12_2.rhoHom z hz))) ∧
      (∀ χ : Problem4_12_2.Heisenberg p →* ℂˣ,
        ∃ i, Nonempty (FDRep.of (Etingof.Example4_3_S3.charRep χ) ≅ W i)) ∧
      (∀ (z : ℂ) (hz : z ^ p = 1), z ≠ 1 →
        ∃ i, Nonempty (FDRep.of (Problem4_12_2.rhoHom z hz) ≅ W i)) := by
  classical
  obtain ⟨n, W, hSimple, hInj, hComplete, _, hn, hcard1, hcardp⟩ := heisenberg_classification' p
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine ⟨n, W, hSimple, hInj, hComplete, hn, hcard1, hcardp, ?_, ?_, ?_, ?_⟩
  · -- a `1`-dimensional member cannot be an `R_z` (those have dimension `p > 1`)
    intro i hi
    haveI := hSimple i
    rcases Problem4_12_2.simple_iso_charRep_or_rhoHom (W i) with ⟨χ, hχ⟩ | ⟨z, hz, _, hiso⟩
    · exact ⟨χ, hχ⟩
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hiso.some)
      rw [hi, Problem4_12_2.finrank_rhoHom z hz] at hfr
      omega
  · -- a `p`-dimensional member cannot be a character (those have dimension `1 < p`)
    intro i hi
    haveI := hSimple i
    rcases Problem4_12_2.simple_iso_charRep_or_rhoHom (W i) with ⟨χ, hχ⟩ | ⟨z, hz, hz1, hiso⟩
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hχ.some)
      rw [hi, show finrank ℂ (FDRep.of (Etingof.Example4_3_S3.charRep χ)) = 1 from
        Module.finrank_self ℂ] at hfr
      omega
    · exact ⟨z, hz, hz1, hiso⟩
  · -- every character occurs: it is simple, so completeness catches it
    intro χ
    haveI : Simple (FDRep.of (Etingof.Example4_3_S3.charRep χ)) :=
      Etingof.Example4_3_S3.charRep_simple χ
    exact hComplete _ inferInstance
  · -- every `R_z` with `z ≠ 1` occurs: it is simple by Problem 4.12.2(b)
    intro z hz hz1
    haveI : IsSimpleModule (MonoidAlgebra ℂ (Problem4_12_2.Heisenberg p))
        (Problem4_12_2.rhoHom z hz).asModule :=
      (Problem4_12_2.irreducible_iff z hz (Problem4_12_2.rhoHom z hz)
        (Problem4_12_2.rhoHom_xGen z hz) (Problem4_12_2.rhoHom_yGen z hz)).mpr hz1
    haveI : Simple (FDRep.of (Problem4_12_2.rhoHom z hz)) :=
      Etingof.simple_fdRepOf_of_isSimpleModule _
    exact hComplete _ inferInstance

end Etingof.Exercise5_27_2
