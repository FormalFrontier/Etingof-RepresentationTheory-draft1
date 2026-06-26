import Mathlib

/-!
# Remark 4.5.3: Frobenius's definition of characters via the convolution algebra

Characters of irreducible complex representations of a finite group `G` can be defined
*without* mentioning representations, following Frobenius. The construction:

* Equip the space `F(G, ℂ) = (G → ℂ)` of complex-valued functions on `G` with the
  **convolution product**
  `(f * g)(z) = Σ_{x y = z} f(x) g(y) = Σ_x f(x) g(x⁻¹ z)`.
  This makes `F(G, ℂ)` into an associative `ℂ`-algebra with unit `δ_e` (the indicator of
  the identity). Concretely, this algebra *is* the group algebra `ℂ[G] = MonoidAlgebra ℂ G`
  under the identification `f ↦ Σ_g f(g) · g`, so we reuse `MonoidAlgebra` rather than
  rebuilding convolution from scratch.

* The space `F_c(G, ℂ)` of **class functions** is a commutative subalgebra: it is exactly
  the centre of the group algebra.

* The **renormalized characters** `χ̃_i` are the **primitive idempotents** of this
  commutative algebra: nonzero solutions of `f * f = f` that cannot be written as a sum of
  two nonzero idempotents.

* The ordinary irreducible characters are recovered by
  `χ_i(g) = √(|G| / χ̃_i(1)) · χ̃_i(g)`.

This is essentially how Frobenius defined characters (see [Cu], equation (7)).

The objects (convolution algebra, class-function subalgebra, renormalized character
idempotent) are genuinely constructed here. The structural theorems (centre ↔ class
functions, primitivity, recovery formula) are stated and proved top-down, with some
proofs left as `sorry`.

## Sign convention

We take `χ̃_V` to be the primitive central idempotent whose *coefficient function* is
`g ↦ (χ_V(1)/|G|) · χ_V(g)` (this is the central idempotent attached to the dual
representation `V*`). With this normalization the book's recovery formula
`χ_V(g) = √(|G|/χ̃_V(1)) · χ̃_V(g)` holds on the nose, since
`χ̃_V(1) = χ_V(1)²/|G|` and `√(|G|/χ̃_V(1)) = |G|/χ_V(1)`.
-/

open scoped Classical
open MonoidAlgebra CategoryTheory

namespace Etingof.Remark4_5_3

universe u

/-- The **convolution algebra** `F(G, ℂ)`: complex-valued functions on `G` with the
convolution product `(f * g)(z) = Σ_{xy=z} f(x) g(y)`. Under `f ↦ Σ_g f(g) · g` this is the
group algebra `ℂ[G]`, so we define it as `MonoidAlgebra ℂ G`; the algebra structure
(associativity, unit `δ_e`) is then provided by Mathlib. -/
abbrev ConvolutionAlgebra (G : Type u) [Group G] : Type u := MonoidAlgebra ℂ G

variable {G : Type u} [Group G]

/-- The unit of the convolution algebra is `δ_e`, the indicator function of the identity
(`δ_e(z) = 1` if `z = e`, else `0`), realised as the basis element `single e 1`. -/
theorem one_eq_deltaE : (1 : ConvolutionAlgebra G) = single (1 : G) (1 : ℂ) := rfl

section Fintype

variable [Fintype G]

/-- The convolution formula: `(f * g)(z) = Σ_x f(x) · g(x⁻¹ z)`, the finite-group form of
`(f * g)(z) = Σ_{xy=z} f(x) g(y)`. This shows the `MonoidAlgebra` product really is the
convolution product of Remark 4.5.3. -/
theorem convolution_apply (f g : ConvolutionAlgebra G) (z : G) :
    (f * g) z = ∑ x : G, f x * g (x⁻¹ * z) := by
  have hinj : Function.Injective (fun x : G => (x, x⁻¹ * z)) := by
    intro a b h
    simpa using congrArg Prod.fst h
  rw [MonoidAlgebra.mul_apply_antidiagonal f g z
        (Finset.univ.map ⟨fun x : G => (x, x⁻¹ * z), hinj⟩)]
  · rw [Finset.sum_map]
    rfl
  · rintro ⟨p1, p2⟩
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨x, rfl, rfl⟩
      group
    · intro hp
      exact ⟨p1, rfl, by rw [← hp]; group⟩

end Fintype

/-! ## Class functions: the centre of the group algebra -/

/-- A function `f : G → ℂ` (equivalently an element of the convolution algebra) is a
**class function** if it is constant on conjugacy classes: `f(y x y⁻¹) = f(x)`. -/
def IsClassFunction (f : ConvolutionAlgebra G) : Prop :=
  ∀ x y : G, f (y * x * y⁻¹) = f x

/-- The **class functions** `F_c(G, ℂ)` form a subalgebra of the convolution algebra,
namely the centre of the group algebra. As the centre, it is commutative. -/
noncomputable def classFunctions (G : Type u) [Group G] : Subalgebra ℂ (MonoidAlgebra ℂ G) :=
  Subalgebra.center ℂ (MonoidAlgebra ℂ G)

/-- The class-function algebra is commutative (it is the centre). -/
noncomputable instance : CommRing (classFunctions G) :=
  inferInstanceAs (CommRing (Subalgebra.center ℂ (MonoidAlgebra ℂ G)))

/-- An element of the group algebra lies in the centre exactly when its coefficient
function is a class function. (Centre ↔ class functions.) -/
theorem mem_classFunctions_iff (f : ConvolutionAlgebra G) :
    f ∈ classFunctions G ↔ IsClassFunction f := by
  simp only [classFunctions, Subalgebra.mem_center_iff]
  constructor
  · -- Centrality ⇒ class function: test against `single y 1` and evaluate at `y * x`.
    intro h x y
    have happ := congrArg (fun F : ConvolutionAlgebra G => F (y * x)) (h (single y 1))
    simp only [single_mul_apply, mul_single_apply, one_mul, mul_one] at happ
    -- `happ : f (y⁻¹ * (y * x)) = f (y * x * y⁻¹)`
    rw [show y⁻¹ * (y * x) = x by group] at happ
    exact happ.symm
  · -- Class function ⇒ centrality: compare the two convolution expansions termwise.
    intro h b
    ext z
    rw [mul_apply_left, mul_apply_right]
    refine Finsupp.sum_congr (fun g _ => ?_)
    -- Pointwise: `(b g) * f (g⁻¹ * z) = f (z * g⁻¹) * (b g)`.
    have hc := h (z * g⁻¹) g⁻¹
    rw [show g⁻¹ * (z * g⁻¹) * g⁻¹⁻¹ = g⁻¹ * z by group] at hc
    rw [mul_comm, hc]

/-! ## Primitive idempotents and renormalized characters -/

/-- A **primitive idempotent** of a ring `A`: a nonzero solution of `e * e = e` that cannot
be decomposed as a sum of two nonzero idempotents. This is the book's definition of the
renormalized characters `χ̃_i` inside the class-function algebra. -/
def IsPrimitiveIdempotent {A : Type*} [Ring A] (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ a b : A, IsIdempotentElem a → IsIdempotentElem b → a ≠ 0 → b ≠ 0 → e ≠ a + b

variable [Fintype G]

/-- The group-algebra element underlying the renormalized character of `V`:
`χ̃_V = (χ_V(1)/|G|) · Σ_g χ_V(g) · g`. Its coefficient function is
`g ↦ (χ_V(1)/|G|) · χ_V(g)`. This is the primitive central idempotent attached to the dual
representation `V*`. -/
noncomputable def renormCharElt (V : FDRep ℂ G) : ConvolutionAlgebra G :=
  (V.character 1 / (Fintype.card G : ℂ)) • ∑ g : G, V.character g • single g (1 : ℂ)

/-- The coefficient function of the renormalized character:
`χ̃_V(z) = (χ_V(1)/|G|) · χ_V(z)`. -/
theorem renormCharElt_apply (V : FDRep ℂ G) (z : G) :
    renormCharElt V z = (V.character 1 / (Fintype.card G : ℂ)) * V.character z := by
  unfold renormCharElt
  have hsum : (∑ g : G, V.character g • single g (1 : ℂ)) z = V.character z := by
    rw [show (∑ g : G, V.character g • single g (1 : ℂ)) z
          = Finsupp.applyAddHom z (∑ g : G, V.character g • single g (1 : ℂ)) from rfl,
        map_sum]
    simp only [Finsupp.applyAddHom_apply]
    rw [show (fun g => (V.character g • single g (1 : ℂ)) z)
          = (fun g => if g = z then V.character g else 0) from
        funext fun g => by simp [Finsupp.single_apply]]
    rw [Finset.sum_ite_eq' Finset.univ z]
    simp
  -- the outer scalar multiplication
  have : ((V.character 1 / (Fintype.card G : ℂ)) • ∑ g : G, V.character g • single g (1 : ℂ)) z
      = (V.character 1 / (Fintype.card G : ℂ)) * (∑ g : G, V.character g • single g (1 : ℂ)) z := by
    simp
  rw [this, hsum]

/-- The renormalized character `χ̃_V` is a class function (lies in the centre). -/
theorem renormCharElt_mem_classFunctions (V : FDRep ℂ G) :
    renormCharElt V ∈ classFunctions G := by
  rw [mem_classFunctions_iff]
  intro x y
  rw [renormCharElt_apply, renormCharElt_apply]
  congr 1
  exact V.char_conj x y

/-- The **renormalized character** `χ̃_V ∈ F_c(G, ℂ)` of an irreducible representation `V`,
as an element of the class-function algebra. -/
noncomputable def renormChar (V : FDRep ℂ G) : classFunctions G :=
  ⟨renormCharElt V, renormCharElt_mem_classFunctions V⟩

/-- For an irreducible `V`, the renormalized character `χ̃_V` is a primitive idempotent of
the class-function algebra. -/
theorem renormChar_isPrimitiveIdempotent (V : FDRep ℂ G) [Simple V] :
    IsPrimitiveIdempotent (renormChar V) := by
  sorry

/-- A simple `FDRep ℂ G` has positive finrank (it is a nonzero object, so cannot be
the trivial module). -/
private lemma finrank_pos_of_simple (V : FDRep ℂ G) [Simple V] : 0 < Module.finrank ℂ V := by
  by_contra h
  push_neg at h
  have h0 : Module.finrank ℂ V = 0 := Nat.le_zero.mp h
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (V ⟶ V) := by
    refine ⟨fun f g => ?_⟩
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have e1 : Module.finrank ℂ (V ⟶ V) = 1 := by rw [FDRep.finrank_hom_simple_simple]; simp
  have e0 : Module.finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- **Recovery formula** (Remark 4.5.3): the ordinary irreducible character is recovered
from the renormalized character (primitive idempotent) by
`χ_V(g) = √(|G| / χ̃_V(1)) · χ̃_V(g)`.

We express `√` as the existence of a square root `c` of `|G| / χ̃_V(1)` with
`χ_V(g) = c · χ̃_V(g)` for all `g`. With our normalization the witness is `c = |G|/χ_V(1)`. -/
theorem character_recovery (V : FDRep ℂ G) [Simple V] :
    ∃ c : ℂ, c ^ 2 = (Fintype.card G : ℂ) / renormCharElt V 1 ∧
      ∀ g : G, V.character g = c * renormCharElt V g := by
  -- `χ_V(1) = dim V ≠ 0` since `V` is a nonzero (simple) representation.
  have hd : V.character 1 ≠ 0 := by
    rw [FDRep.char_one]
    exact_mod_cast (finrank_pos_of_simple V).ne'
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  -- With our normalization the square-root witness is exactly `c = |G| / χ_V(1)`.
  refine ⟨(Fintype.card G : ℂ) / V.character 1, ?_, ?_⟩
  · rw [renormCharElt_apply]
    field_simp
  · intro g
    rw [renormCharElt_apply]
    field_simp

end Etingof.Remark4_5_3
