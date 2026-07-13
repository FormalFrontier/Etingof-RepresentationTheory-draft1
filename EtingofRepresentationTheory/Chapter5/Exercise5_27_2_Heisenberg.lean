import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1

/-!
# Exercise 5.27.2 (Heisenberg group): redo Problem 4.12.2 using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the **Problem 4.12.2** part: classify all irreducible complex
representations of the Heisenberg group `H_p` — the group of `3 × 3` upper unitriangular
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
  one-dimensional irreducibles — exactly the characters of `H_p`, which factor through the
  abelianization `H_p / Z(H_p) ≅ (ℤ/p)²`.
* **Free orbits** are indexed by `γ ≠ 0` (there are `p - 1`), each of size `p` with trivial
  stabilizer; over each, Theorem 5.27.1 gives a single irreducible `V(χ, U)` of dimension
  `[G : G_χ] = p`. These are the `p - 1` representations `R_z` (`z ≠ 1`) of Problem 4.12.2.

So there are exactly `p² + (p - 1)` irreducibles: `p²` of dimension `1` and `p - 1` of
dimension `p`, consistent with `∑ dim² = p²·1 + (p-1)·p² = p³ = |H_p|`.

Statement pass: the group and its semidirect structure are constructed; the classification
is stated with the proof left as `sorry`.
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
    · show (Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1
        - a * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
      ring
  right_inv x := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · show (Multiplicative.toAdd x).2 - a * (Multiplicative.toAdd x).1
        + a * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
      ring
  map_mul' x y := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · show ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2)
          + a * ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1)
        = ((Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1)
          + ((Multiplicative.toAdd y).2 + a * (Multiplicative.toAdd y).1)
      ring

@[simp] lemma heisenbergShear_zero : heisenbergShear p 0 = 1 := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  apply Multiplicative.toAdd.injective
  show ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + 0 * (Multiplicative.toAdd x).1)
      = Multiplicative.toAdd x
  apply Prod.ext
  · rfl
  · show (Multiplicative.toAdd x).2 + 0 * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
    ring

lemma heisenbergShear_add (a a' : ZMod p) :
    heisenbergShear p (a + a') = heisenbergShear p a * heisenbergShear p a' := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply]
  apply Multiplicative.toAdd.injective
  show ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + (a + a') * (Multiplicative.toAdd x).1)
      = ((Multiplicative.toAdd x).1,
          (Multiplicative.toAdd x).2 + a' * (Multiplicative.toAdd x).1 + a * (Multiplicative.toAdd x).1)
  apply Prod.ext
  · rfl
  · show (Multiplicative.toAdd x).2 + (a + a') * (Multiplicative.toAdd x).1
        = (Multiplicative.toAdd x).2 + a' * (Multiplicative.toAdd x).1
          + a * ((Multiplicative.toAdd x).1)
    ring

/-- The `G`-action on the abelian normal subgroup `A` of the Heisenberg group: the
multiplicative element `a ∈ G = Multiplicative (ZMod p)` acts by the shear `φ a`. -/
def heisenbergφ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod p × ZMod p)) where
  toFun a := heisenbergShear p (Multiplicative.toAdd a)
  map_one' := by
    show heisenbergShear p (0 : ZMod p) = 1
    exact heisenbergShear_zero p
  map_mul' a a' := by
    show heisenbergShear p (Multiplicative.toAdd a + Multiplicative.toAdd a')
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

/-- **Dual-action formula.** Precomposing `χ_{β,γ}` with the shear `φ(g⁻¹)` — i.e. applying the
dual `G`-action of `g` — yields `χ_{β − a·γ, γ}` where `a = Multiplicative.toAdd g`. This is
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

/-- **Injectivity of the parametrization.** Distinct `(β, γ)` give distinct characters. -/
lemma heisenbergChar_injective :
    Function.Injective (fun bg : ZMod p × ZMod p => heisenbergChar p bg.1 bg.2) := by
  rintro ⟨β, γ⟩ ⟨β', γ'⟩ h
  simp only at h
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (1, 0))
  have h2 := DFunLike.congr_fun h (Multiplicative.ofAdd (0, 1))
  rw [heisenbergChar_apply, heisenbergChar_apply] at h1 h2
  simp only [mul_one, mul_zero, add_zero, zero_add] at h1 h2
  have hβ : β = β' := ZMod.val_injective p
    ((heisenbergZeta_primitive p).pow_inj (ZMod.val_lt β) (ZMod.val_lt β') h1)
  have hγ : γ = γ' := ZMod.val_injective p
    ((heisenbergZeta_primitive p).pow_inj (ZMod.val_lt γ) (ZMod.val_lt γ') h2)
  rw [hβ, hγ]

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
  sorry

end Etingof.Exercise5_27_2
