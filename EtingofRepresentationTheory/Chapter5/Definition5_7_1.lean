import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrrepClasses

/-!
# Definition 5.7.1: Virtual Representation

**Definition 5.7.1.** A *virtual representation* of a finite group `G` is an integer linear
combination of irreducible representations of `G`, `V = Σ nᵢ Vᵢ`, `nᵢ ∈ ℤ` (the `nᵢ` are not
assumed nonnegative). The character of `V` is `χ_V := Σ nᵢ χ_{Vᵢ}`.

## Formalization

The `Vᵢ` in the book's sum range over *the* irreducibles of `G`, i.e. over the irreducibles
taken up to isomorphism: there is one coefficient per isomorphism class, and two isomorphic
models of the same irreducible are the same summand. So a virtual representation is an
element of the free abelian group on `Etingof.IrrepClasses ℂ G`:

`VirtualRepresentation G := IrrepClasses ℂ G →₀ ℤ`.

Indexing coefficients by literal `FDRep ℂ G` objects instead would be wrong, not merely
inconvenient: `+1` on one model of an irreducible together with `-1` on an isomorphic copy
would be nonzero coefficient data although it is zero as a virtual representation. With the
quotient indexing this cannot happen — `IrrepClasses.mk` identifies isomorphic models
(`Etingof.VirtualRepresentation.coeff_congr_iso`).

Using `Finsupp` gives the group structure (`0`, `+`, `-`) and the "finitely many nonzero
coefficients" condition for free, and `Finsupp.single` gives the basis elements: the class of
a genuine irreducible `W` is `ofSingle W hW 1`.

The virtual character is packaged as an additive homomorphism
`character : VirtualRepresentation G →+ (G → ℂ)`, so that `χ_{V + V'} = χ_V + χ_{V'}`,
`χ_{-V} = -χ_V` and `χ_0 = 0` hold by construction. Its value formula is
`character_apply`, matching the book's `Σ nᵢ χ_{Vᵢ}`.

## Mathlib correspondence

Mathlib has no dedicated `VirtualRepresentation` type. The representation ring `R(G)` is
this group with the multiplication induced by tensor product; only the additive structure is
needed for Definition 5.7.1 and Lemma 5.7.2.
-/

open CategoryTheory

namespace Etingof

/-- A **virtual representation** of a finite group `G` is a formal integer linear combination
`V = Σ nᵢ Vᵢ` of irreducible representations of `G`, with `nᵢ ∈ ℤ` allowed to be negative.

We model it as a finitely supported integer-valued function on `IrrepClasses ℂ G`, the
irreducibles of `G` *taken up to isomorphism*: one coefficient per isomorphism class. Being
finitely supported is the book's "linear combination"; the quotient indexing is the book's
"of irreducible representations", where the `Vᵢ` are understood as the distinct irreducibles.
(Etingof Definition 5.7.1) -/
abbrev VirtualRepresentation (G : Type) [Group G] [Fintype G] : Type _ :=
  IrrepClasses ℂ G →₀ ℤ

namespace VirtualRepresentation

variable {G : Type} [Group G] [Fintype G]

/-! ### Coefficients

`V c` is already the coefficient at the class `c`. `coeff` is the version taking an actual
irreducible representation, which is how the book indexes the sum. -/

/-- The coefficient of the virtual representation `V` at the irreducible representation `W`.
By `coeff_congr_iso` this depends only on the isomorphism class of `W`. -/
noncomputable def coeff (V : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) : ℤ :=
  V (IrrepClasses.mk W hW)

/-- **Coefficients are isomorphism invariants.** Isomorphic models of an irreducible carry
the same coefficient. This is the property that fails for coefficient data indexed by
literal `FDRep ℂ G` objects, and it is what makes `+1` on one model plus `-1` on an
isomorphic copy impossible. -/
theorem coeff_congr_iso (V : VirtualRepresentation G) {W W' : FDRep ℂ G}
    (hW : Simple W) (hW' : Simple W') (e : W ≅ W') : V.coeff W hW = V.coeff W' hW' := by
  rw [coeff, coeff, IrrepClasses.mk_eq_mk_of_iso hW hW' e]

/-- The coefficient does not depend on the simplicity proof. -/
theorem coeff_congr_proof (V : VirtualRepresentation G) {W : FDRep ℂ G} (hW hW' : Simple W) :
    V.coeff W hW = V.coeff W hW' :=
  V.coeff_congr_iso hW hW' (Iso.refl W)

@[simp]
theorem coeff_zero (W : FDRep ℂ G) (hW : Simple W) :
    (0 : VirtualRepresentation G).coeff W hW = 0 := rfl

@[simp]
theorem coeff_add (V V' : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (V + V').coeff W hW = V.coeff W hW + V'.coeff W hW := rfl

@[simp]
theorem coeff_neg (V : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (-V).coeff W hW = -V.coeff W hW := rfl

@[simp]
theorem coeff_sub (V V' : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (V - V').coeff W hW = V.coeff W hW - V'.coeff W hW := rfl

/-- **Coefficient extensionality.** A virtual representation is determined by its
coefficients on genuine irreducible representations. -/
theorem ext_coeff {V V' : VirtualRepresentation G}
    (h : ∀ (W : FDRep ℂ G) (hW : Simple W), V.coeff W hW = V'.coeff W hW) : V = V' := by
  ext c
  induction c using Etingof.IrrepClasses.inductionOn with
  | _ W hW => exact h W hW

/-! ### Basis elements

`ofSingle W hW n` is the virtual representation `n · W`; in particular `ofSingle W hW 1` is
the class of the genuine irreducible `W`. -/

/-- The virtual representation `n · W` for an irreducible `W`. -/
noncomputable def ofSingle (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) : VirtualRepresentation G :=
  Finsupp.single (IrrepClasses.mk W hW) n

/-- **Isomorphic irreducibles give the same basis element.** -/
theorem ofSingle_congr_iso {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W') (e : W ≅ W')
    (n : ℤ) : ofSingle W hW n = ofSingle W' hW' n := by
  rw [ofSingle, ofSingle, IrrepClasses.mk_eq_mk_of_iso hW hW' e]

@[simp]
theorem ofSingle_zero (W : FDRep ℂ G) (hW : Simple W) : ofSingle W hW 0 = 0 :=
  Finsupp.single_zero _

@[simp]
theorem ofSingle_add (W : FDRep ℂ G) (hW : Simple W) (m n : ℤ) :
    ofSingle W hW (m + n) = ofSingle W hW m + ofSingle W hW n :=
  Finsupp.single_add _ _ _

theorem coeff_ofSingle_self (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    (ofSingle W hW n).coeff W hW = n := by
  simp [coeff, ofSingle]

/-- **Non-vacuity.** A basis element `n · W` vanishes only for `n = 0`; in particular the
class `ofSingle W hW 1` of a genuine irreducible is a nonzero virtual representation. -/
@[simp]
theorem ofSingle_eq_zero_iff (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    ofSingle W hW n = 0 ↔ n = 0 :=
  Finsupp.single_eq_zero

/-- `ofSingle · · n` (for `n ≠ 0`) separates isomorphism classes: two irreducibles give the
same basis element only if they are isomorphic. -/
theorem nonempty_iso_of_ofSingle_eq {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    {n : ℤ} (hn : n ≠ 0) (h : ofSingle W hW n = ofSingle W' hW' n) : Nonempty (W ≅ W') := by
  rw [← IrrepClasses.mk_eq_mk_iff hW hW']
  simpa [ofSingle, Finsupp.single_eq_single_iff, hn] using h

/-- **Non-vacuity, contrapositive form.** Non-isomorphic irreducibles are genuinely distinct
basis elements, so `VirtualRepresentation G` is not collapsed. -/
theorem ofSingle_ne_ofSingle {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    {n : ℤ} (hn : n ≠ 0) (h : IsEmpty (W ≅ W')) : ofSingle W hW n ≠ ofSingle W' hW' n :=
  fun heq => (nonempty_iso_of_ofSingle_eq hW hW' hn heq).elim h.elim

/-- **The literal-object defect is gone.** `+1` on one model of an irreducible together with
`-1` on an isomorphic copy is the *zero* virtual representation. With coefficients indexed by
literal `FDRep ℂ G` objects this combination would be nonzero data, which is exactly why the
quotient indexing is the correct reading of Definition 5.7.1. -/
theorem ofSingle_add_ofSingle_neg_of_iso {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    (e : W ≅ W') : ofSingle W hW 1 + ofSingle W' hW' (-1) = 0 := by
  rw [ofSingle_congr_iso hW hW' e 1, ofSingle, ofSingle, ← Finsupp.single_add, add_neg_cancel,
    Finsupp.single_zero]

/-! ### The virtual character -/

/-- The **virtual character** `χ_V := Σ nᵢ χ_{Vᵢ}` of a virtual representation, as an
additive homomorphism `VirtualRepresentation G →+ (G → ℂ)`. The character of an irreducible
class is well defined because isomorphic representations have equal characters
(`Etingof.IrrepClasses.character`). (Etingof Definition 5.7.1) -/
noncomputable def character : VirtualRepresentation G →+ (G → ℂ) :=
  Finsupp.liftAddHom (α := IrrepClasses ℂ G) (M := ℤ) (N := G → ℂ)
    fun c => zmultiplesHom (G → ℂ) (IrrepClasses.character c)

/-- The book's formula `χ_V = Σ nᵢ χ_{Vᵢ}`, the sum ranging over the (finite) support. -/
theorem character_apply (V : VirtualRepresentation G) (g : G) :
    character V g = ∑ c ∈ V.support, (V c : ℂ) * IrrepClasses.character c g := by
  rw [character, Finsupp.liftAddHom_apply]
  simp only [Finsupp.sum, zmultiplesHom_apply, Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply,
    Pi.intCast_apply]

@[simp]
theorem character_zero : character (0 : VirtualRepresentation G) = 0 :=
  map_zero _

@[simp]
theorem character_add (V V' : VirtualRepresentation G) :
    character (V + V') = character V + character V' :=
  map_add _ _ _

@[simp]
theorem character_neg (V : VirtualRepresentation G) : character (-V) = -character V :=
  map_neg _ _

@[simp]
theorem character_sub (V V' : VirtualRepresentation G) :
    character (V - V') = character V - character V' :=
  map_sub _ _ _

@[simp]
theorem character_single (c : IrrepClasses ℂ G) (n : ℤ) :
    character (Finsupp.single c n) = n • IrrepClasses.character c :=
  Finsupp.liftAddHom_apply_single _ _ _

@[simp]
theorem character_ofSingle (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    character (ofSingle W hW n) = n • W.character := by
  rw [ofSingle, character_single, IrrepClasses.character_mk]

/-- The class of a genuine irreducible has that irreducible's character. -/
theorem character_ofSingle_one (W : FDRep ℂ G) (hW : Simple W) :
    character (ofSingle W hW 1) = W.character := by
  rw [character_ofSingle, one_smul]

/-! ### The virtual dimension -/

/-- The virtual dimension `Σ nᵢ dim Vᵢ` of a virtual representation. It can be negative. -/
noncomputable def dim (V : VirtualRepresentation G) : ℤ :=
  V.sum fun c n => n * (IrrepClasses.finrank c : ℤ)

theorem dim_eq_sum (V : VirtualRepresentation G) :
    V.dim = ∑ c ∈ V.support, V c * (IrrepClasses.finrank c : ℤ) := rfl

/-- The book's `χ_V(1) = Σ nᵢ dim Vᵢ`. -/
theorem character_one_eq_dim (V : VirtualRepresentation G) :
    character V 1 = (V.dim : ℂ) := by
  rw [character_apply, dim_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by rw [IrrepClasses.character_one]

@[simp]
theorem dim_zero : (0 : VirtualRepresentation G).dim = 0 :=
  Finsupp.sum_zero_index

@[simp]
theorem dim_ofSingle (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    (ofSingle W hW n).dim = n * (Module.finrank ℂ W : ℤ) := by
  rw [dim, ofSingle, Finsupp.sum_single_index (by rw [zero_mul]), IrrepClasses.finrank_mk]

end VirtualRepresentation

end Etingof
