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
functions, primitivity, recovery formula) are stated and proved top-down.

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

/-! ## Primitive idempotency of the renormalized character

The renormalized character `χ̃_V` is a primitive idempotent of the class-function algebra.
The engine is a single **absorption lemma**: for any class function `z`, the convolution
`χ̃_V ⋆ z` is a scalar multiple of `χ̃_V`. This is proved by the standard "central element
acts as a scalar" Schur argument — the equivariant endomorphism `S_z = Σ_y z(y)·ρ(y⁻¹)` of a
simple `V` is a scalar by Schur's lemma. Idempotency is the case `z = χ̃_V` (the scalar is `1`,
by character orthonormality), and primitivity is the standard minimal-idempotent argument. -/

/-- Schur's lemma in scalar form: a `G`-equivariant endomorphism of a simple `V : FDRep ℂ G`
is a scalar multiple of the identity. (Mirrors the scalar-extraction pattern of
`Etingof.Proposition4_7_1_ii`.) -/
private lemma exists_scalar_of_invariant (V : FDRep ℂ G) [Simple V]
    (T : V →ₗ[ℂ] V)
    (hT : T ∈ (Representation.linHom V.ρ V.ρ).invariants) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h1dim : Module.finrank ℂ (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ V
  have hid_mem : LinearMap.id ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_simple V).ne'
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro h
    have : (Module.finrank ℂ V : ℂ) = 0 := by
      rw [← LinearMap.trace_id (R := ℂ) (M := V), h, map_zero]
    exact hdim_ne this
  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim)
    ⟨T, hT⟩
  refine ⟨c, ?_⟩
  have := congr_arg Subtype.val hc
  simpa using this.symm

/-- **Absorption lemma.** For a simple `V` and any class function `z`, the convolution
`χ̃_V ⋆ z` is a scalar multiple of `χ̃_V`. The scalar comes from the equivariant operator
`S_z = Σ_y z(y) ρ(y⁻¹)` being a scalar by Schur's lemma. -/
private lemma renormCharElt_mul_classFunction (V : FDRep ℂ G) [Simple V]
    (z : ConvolutionAlgebra G) (hz : IsClassFunction z) :
    ∃ σ : ℂ, renormCharElt V * z = σ • renormCharElt V := by
  set S : V →ₗ[ℂ] V := ∑ y : G, z y • V.ρ y⁻¹ with hSdef
  -- `S` is `G`-equivariant: conjugating reindexes the sum using that `z` is a class function.
  have hmem : S ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g
    rw [Representation.linHom_apply]
    simp only [← Module.End.mul_eq_comp]
    rw [hSdef, Finset.sum_mul, Finset.mul_sum]
    have hterm : ∀ y : G, V.ρ g * ((z y • V.ρ y⁻¹) * V.ρ g⁻¹) = z y • V.ρ (g * y⁻¹ * g⁻¹) := by
      intro y
      rw [smul_mul_assoc, mul_smul_comm]
      congr 1
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [Finset.sum_congr rfl (fun y _ => hterm y)]
    apply Fintype.sum_equiv ((Equiv.mulLeft g).trans (Equiv.mulRight g⁻¹))
    intro y
    change z y • V.ρ (g * y⁻¹ * g⁻¹) = z (g * y * g⁻¹) • V.ρ ((g * y * g⁻¹)⁻¹)
    rw [hz y g, show (g * y * g⁻¹)⁻¹ = g * y⁻¹ * g⁻¹ by group]
  obtain ⟨σ, hσ⟩ := exists_scalar_of_invariant V S hmem
  refine ⟨σ, ?_⟩
  ext w
  rw [convolution_apply]
  -- The core convolution identity, via the trace of `ρ(w) ∘ S = ρ(w) ∘ (σ • id)`.
  have hcore : (∑ x : G, V.character x * z (x⁻¹ * w)) = σ * V.character w := by
    have hreindex : (∑ x : G, V.character x * z (x⁻¹ * w))
        = ∑ y : G, z y * V.character (w * y⁻¹) := by
      apply Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight w))
      intro x
      change V.character x * z (x⁻¹ * w) = z (x⁻¹ * w) * V.character (w * (x⁻¹ * w)⁻¹)
      rw [show w * (x⁻¹ * w)⁻¹ = x by group]
      ring
    have htrace : (∑ y : G, z y * V.character (w * y⁻¹)) = σ * V.character w := by
      have hstep : ∀ y : G, z y * V.character (w * y⁻¹)
          = LinearMap.trace ℂ V (V.ρ w * (z y • V.ρ y⁻¹)) := by
        intro y
        change z y * LinearMap.trace ℂ V (V.ρ (w * y⁻¹)) = _
        rw [map_mul, mul_smul_comm, map_smul, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun y _ => hstep y), ← map_sum, ← Finset.mul_sum,
          ← hSdef, hσ, mul_smul_comm, ← Module.End.one_eq_id, mul_one, map_smul, smul_eq_mul]
      rfl
    rw [hreindex, htrace]
  rw [Finsupp.smul_apply, smul_eq_mul, renormCharElt_apply]
  simp only [renormCharElt_apply]
  rw [show (∑ x : G, V.character 1 / (Fintype.card G : ℂ) * V.character x * z (x⁻¹ * w))
        = V.character 1 / (Fintype.card G : ℂ) * ∑ x : G, V.character x * z (x⁻¹ * w) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)]
  rw [hcore]
  ring

/-- For an irreducible `V`, the renormalized character `χ̃_V` is a primitive idempotent of
the class-function algebra. -/
theorem renormChar_isPrimitiveIdempotent (V : FDRep ℂ G) [Simple V] :
    IsPrimitiveIdempotent (renormChar V) := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : V.character 1 ≠ 0 := by
    rw [FDRep.char_one]; exact_mod_cast (finrank_pos_of_simple V).ne'
  -- `χ̃_V(1) = (dim V)²/|G| ≠ 0`, so `χ̃_V ≠ 0`.
  have he1 : renormCharElt V 1 ≠ 0 := by
    rw [renormCharElt_apply]; exact mul_ne_zero (div_ne_zero hd hG) hd
  have hne : renormCharElt V ≠ 0 := fun h => he1 (by rw [h]; rfl)
  -- Idempotency: apply the absorption lemma to `z = χ̃_V` and pin the scalar to `1` at `g = 1`.
  have hclass : IsClassFunction (renormCharElt V) :=
    (mem_classFunctions_iff (renormCharElt V)).mp (renormCharElt_mem_classFunctions V)
  obtain ⟨σ0, hσ0⟩ := renormCharElt_mul_classFunction V (renormCharElt V) hclass
  have hval1 : (renormCharElt V * renormCharElt V) 1 = renormCharElt V 1 := by
    rw [convolution_apply]
    have hterm : ∀ x : G, renormCharElt V x * renormCharElt V (x⁻¹ * 1)
        = (V.character 1 / (Fintype.card G : ℂ)) ^ 2 * (V.character x * V.character x⁻¹) := by
      intro x; rw [mul_one, renormCharElt_apply, renormCharElt_apply]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
    have horth := FDRep.char_orthonormal V V
    rw [if_pos ⟨Iso.refl V⟩] at horth
    have hsum : (∑ g : G, V.character g * V.character g⁻¹) = (Fintype.card G : ℂ) := by
      rw [invOf_smul_eq_iff] at horth; simpa using horth
    rw [hsum, renormCharElt_apply]
    field_simp
  have hidem : renormCharElt V * renormCharElt V = renormCharElt V := by
    have hcoef : renormCharElt V 1 = σ0 * renormCharElt V 1 := by
      have h : (renormCharElt V * renormCharElt V) 1 = (σ0 • renormCharElt V) 1 := by rw [hσ0]
      rw [hval1, Finsupp.smul_apply, smul_eq_mul] at h
      exact h
    have hσ1 : σ0 = 1 :=
      mul_right_cancel₀ he1 (by rw [one_mul]; exact hcoef.symm)
    rw [hσ0, hσ1, one_smul]
  -- Lift idempotency and nonvanishing to the class-function subalgebra.
  have he_idem : renormChar V * renormChar V = renormChar V := Subtype.ext hidem
  have he_ne : renormChar V ≠ 0 := by
    intro h
    apply hne
    have h2 := congrArg Subtype.val h
    rwa [ZeroMemClass.coe_zero] at h2
  -- Cancellation: `s • χ̃_V = t • χ̃_V → s = t` (evaluate the coefficient at `1`).
  have hsmul_cancel : ∀ s t : ℂ, s • renormChar V = t • renormChar V → s = t := by
    intro s t h
    have hv := congrArg (fun x : ↥(classFunctions G) => (x : ConvolutionAlgebra G) 1) h
    simp only [SetLike.val_smul, Finsupp.smul_apply, smul_eq_mul] at hv
    exact mul_right_cancel₀ he1 hv
  refine ⟨he_idem, he_ne, ?_⟩
  intro a b ha hb ha0 hb0 hEq
  -- `a, b` are orthogonal idempotents (char 0), so `ab = 0`.
  have h2u : IsUnit (2 : ↥(classFunctions G)) := by
    rw [show (2 : ↥(classFunctions G)) = algebraMap ℂ _ 2 by rw [map_ofNat]]
    exact ((two_ne_zero (α := ℂ)).isUnit).map (algebraMap ℂ (↥(classFunctions G)))
  have hab : a * b = 0 := by
    have hexp : (a + b) * (a + b) = a + b := by rw [← hEq]; exact he_idem
    rw [add_mul, mul_add, mul_add, ha, hb] at hexp
    have h2 : a * b + a * b = 0 := by
      rw [mul_comm b a] at hexp; linear_combination hexp
    have : (2 : ↥(classFunctions G)) * (a * b) = 0 := by rw [two_mul]; exact h2
    exact (h2u.mul_right_eq_zero).mp this
  have hba0 : b * a = 0 := by rw [mul_comm]; exact hab
  -- `χ̃_V * a = a`, hence `a = σa • χ̃_V`.
  have hea : renormChar V * a = a := by rw [hEq, add_mul, ha, hba0, add_zero]
  have ha_class : IsClassFunction (a : ConvolutionAlgebra G) :=
    (mem_classFunctions_iff (a : ConvolutionAlgebra G)).mp a.2
  obtain ⟨σa, hσa⟩ := renormCharElt_mul_classFunction V (a : ConvolutionAlgebra G) ha_class
  have hσa' : renormChar V * a = σa • renormChar V := by
    apply Subtype.ext; simp only [MulMemClass.coe_mul, SetLike.val_smul]; exact hσa
  have haσ : a = σa • renormChar V := hea ▸ hσa'
  have hσa_sq : σa * σa = σa := by
    have h' : a * a = a := ha
    rw [haσ, smul_mul_smul_comm, he_idem] at h'
    exact hsmul_cancel _ _ h'
  have hσa_ne : σa ≠ 0 := fun h0 => ha0 (by rw [haσ, h0, zero_smul])
  have hσa_one : σa = 1 := by
    have hz : σa * (σa - 1) = 0 := by linear_combination hσa_sq
    exact (mul_eq_zero.mp hz).resolve_left hσa_ne |> sub_eq_zero.mp
  have ha_eq : a = renormChar V := by rw [haσ, hσa_one, one_smul]
  -- Symmetrically, `b = χ̃_V`.
  have heb : renormChar V * b = b := by rw [hEq, add_mul, hb, hab, zero_add]
  have hb_class : IsClassFunction (b : ConvolutionAlgebra G) :=
    (mem_classFunctions_iff (b : ConvolutionAlgebra G)).mp b.2
  obtain ⟨σb, hσb⟩ := renormCharElt_mul_classFunction V (b : ConvolutionAlgebra G) hb_class
  have hσb' : renormChar V * b = σb • renormChar V := by
    apply Subtype.ext; simp only [MulMemClass.coe_mul, SetLike.val_smul]; exact hσb
  have hbσ : b = σb • renormChar V := heb ▸ hσb'
  have hσb_sq : σb * σb = σb := by
    have h' : b * b = b := hb
    rw [hbσ, smul_mul_smul_comm, he_idem] at h'
    exact hsmul_cancel _ _ h'
  have hσb_ne : σb ≠ 0 := fun h0 => hb0 (by rw [hbσ, h0, zero_smul])
  have hσb_one : σb = 1 := by
    have hz : σb * (σb - 1) = 0 := by linear_combination hσb_sq
    exact (mul_eq_zero.mp hz).resolve_left hσb_ne |> sub_eq_zero.mp
  have hb_eq : b = renormChar V := by rw [hbσ, hσb_one, one_smul]
  -- Then `χ̃_V = a + b = χ̃_V + χ̃_V`, forcing `χ̃_V = 0`, a contradiction.
  rw [ha_eq, hb_eq] at hEq
  apply he_ne
  have h0 : renormChar V + (0 : ↥(classFunctions G)) = renormChar V + renormChar V := by
    rw [add_zero]; exact hEq
  exact ((add_right_inj _).mp h0).symm

end Etingof.Remark4_5_3
