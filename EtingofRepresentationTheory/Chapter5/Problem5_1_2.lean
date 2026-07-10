import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1

/-!
# Problem 5.1.2: real endomorphism algebras and real forms

**Problem 5.1.2.** (a) Show that `End_{ℝ[G]} V` is `ℂ` for `V` of complex type, `Mat₂(ℝ)` for `V`
of real type, and `ℍ` for `V` of quaternionic type, which motivates the names above.

(b) Show that `V` is of real type if and only if `V` is the complexification of a representation
`V_ℝ` over the field of real numbers.

## Formalization

Let `V` be an irreducible complex representation of a finite group `G`. Viewing `V` as a **real**
representation (restriction of scalars `ℂ → ℝ`, carried by the `[Module ℝ V] [IsScalarTower ℝ ℂ V]`
hypotheses), the algebra `End_{ℝ[G]} V` of `ℝ`-linear `G`-equivariant endomorphisms is the
**centralizer** in `Module.End ℝ V` of the real operators `{(ρ g).restrictScalars ℝ}`. We call
this `Etingof.realGEndAlgebra ρ`.

* **(a)** For an irreducible `V`:
  - complex type ⟹ `End_{ℝ[G]} V ≃ₐ[ℝ] ℂ`;
  - real type ⟹ `End_{ℝ[G]} V ≃ₐ[ℝ] Mat₂(ℝ) = Matrix (Fin 2) (Fin 2) ℝ`;
  - quaternionic type ⟹ `End_{ℝ[G]} V ≃ₐ[ℝ] ℍ = Quaternion ℝ`.
* **(b)** `V` is of real type iff it admits a **real form**: a `G`-stable `ℝ`-subspace `W ⊆ V`
  whose `ℂ`-span is all of `V` and with `dim_ℝ W = dim_ℂ V` (so the inclusion induces an
  equivariant isomorphism `ℂ ⊗_ℝ W ≅ V`; the `G`-action restricts to a real representation on `W`).

Statement pass: the proofs are left as `sorry`.
-/

namespace Etingof

section Problem512

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
variable [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- `End_{ℝ[G]} V`: the `ℝ`-algebra of `ℝ`-linear `G`-equivariant endomorphisms of `V`, realized
as the centralizer in `Module.End ℝ V` of the real operators `(ρ g).restrictScalars ℝ`. -/
noncomputable def realGEndAlgebra (ρ : Representation ℂ G V) :
    Subalgebra ℝ (Module.End ℝ V) :=
  Subalgebra.centralizer ℝ (Set.range (fun g => LinearMap.restrictScalars ℝ (ρ g)))

/-- The `ℝ`-algebra embedding `ℂ ↪ End_{ℝ[G]} V`, `z ↦ (v ↦ z • v)`. This is the
`ℂ ⊆ End_{ℝ[G]} V` inclusion of the book: scalar multiplication by `z : ℂ` is an
`ℝ`-linear endomorphism of `V`, and it lands in the centralizer `realGEndAlgebra ρ`
because each `ρ g` is `ℂ`-linear, so `ρ g (z • v) = z • ρ g v`.

Realized as `AlgHom.codRestrict` of `Algebra.lsmul ℝ ℝ V : ℂ →ₐ[ℝ] Module.End ℝ V`. -/
noncomputable def complexToRealGEnd (ρ : Representation ℂ G V) :
    ℂ →ₐ[ℝ] realGEndAlgebra ρ :=
  AlgHom.codRestrict (Algebra.lsmul ℝ ℝ V : ℂ →ₐ[ℝ] Module.End ℝ V) (realGEndAlgebra ρ) <| by
    intro z
    rw [realGEndAlgebra, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply, Algebra.lsmul_apply]
    exact map_smul (ρ g) z v

omit [Fintype G] [Module.Finite ℂ V] in
@[simp]
theorem complexToRealGEnd_coe_apply (ρ : Representation ℂ G V) (z : ℂ) (v : V) :
    ((complexToRealGEnd ρ z : Module.End ℝ V)) v = z • v := rfl

omit [Fintype G] [Module.Finite ℂ V] in
/-- The `ℂ`-embedding is injective (when `V ≠ 0`): if `z • · = 0` then, evaluating at a
nonzero vector, `z • v = 0` forces `z = 0` since `ℂ` is a field. -/
theorem complexToRealGEnd_injective (ρ : Representation ℂ G V) [Nontrivial V] :
    Function.Injective (complexToRealGEnd ρ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hzv : z • v = 0 := by
    have := congrArg (fun s => (s : Module.End ℝ V) v) (congrArg Subtype.val hz)
    simpa using this
  rcases smul_eq_zero.mp hzv with h | h
  · exact h
  · exact absurd h hv

section ConjDecomp

/-- In any ring, if `j² = -1` then `j` commutes with `f - j·f·j` (the "`+`" part). -/
private lemma ring_conj_comm {R : Type*} [Ring R] {j : R} (hj : j * j = -1) (f : R) :
    j * (f - j * f * j) = (f - j * f * j) * j := by
  have h2 : j * (j * f * j) = -(f * j) := by
    rw [← mul_assoc, ← mul_assoc, hj, neg_one_mul, neg_mul]
  have h3 : j * f * j * j = -(j * f) := by rw [mul_assoc, hj, mul_neg_one]
  rw [mul_sub, sub_mul, h2, h3]; abel

/-- In any ring, if `j² = -1` then `j` anticommutes with `f + j·f·j` (the "`-`" part). -/
private lemma ring_conj_anticomm {R : Type*} [Ring R] {j : R} (hj : j * j = -1) (f : R) :
    j * (f + j * f * j) = -((f + j * f * j) * j) := by
  have h2 : j * (j * f * j) = -(f * j) := by
    rw [← mul_assoc, ← mul_assoc, hj, neg_one_mul, neg_mul]
  have h3 : j * f * j * j = -(j * f) := by rw [mul_assoc, hj, mul_neg_one]
  rw [mul_add, add_mul, h2, h3]; abel

variable (ρ : Representation ℂ G V)

/-- The operator `J = ·i` (multiplication by `i`) as an element of `End_{ℝ[G]} V`,
the image of `Complex.I` under the `ℂ`-embedding. It satisfies `J² = -1`. -/
noncomputable def realJ : realGEndAlgebra ρ := complexToRealGEnd ρ Complex.I

/-- `J² = -1`: since `J = complexToRealGEnd i` and `i·i = -1`. -/
theorem realJ_sq : realJ ρ * realJ ρ = -1 := by
  rw [realJ, ← map_mul, Complex.I_mul_I, map_neg, map_one]

variable {ρ}

/-- The `ℂ`-linear part of `f ∈ End_{ℝ[G]} V`: `f₊ = ½(f − J∘f∘J)`. It commutes with `J`. -/
noncomputable def realPlus (f : realGEndAlgebra ρ) : realGEndAlgebra ρ :=
  (2⁻¹ : ℝ) • (f - realJ ρ * f * realJ ρ)

/-- The `ℂ`-antilinear part of `f ∈ End_{ℝ[G]} V`: `f₋ = ½(f + J∘f∘J)`. It anticommutes with `J`. -/
noncomputable def realMinus (f : realGEndAlgebra ρ) : realGEndAlgebra ρ :=
  (2⁻¹ : ℝ) • (f + realJ ρ * f * realJ ρ)

/-- `f = f₊ + f₋`. -/
theorem realPlus_add_realMinus (f : realGEndAlgebra ρ) :
    realPlus f + realMinus f = f := by
  rw [realPlus, realMinus, ← smul_add]
  have : (f - realJ ρ * f * realJ ρ) + (f + realJ ρ * f * realJ ρ) = (2 : ℝ) • f := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

/-- `f₊` commutes with `J` (it is `ℂ`-linear). -/
theorem realJ_mul_realPlus (f : realGEndAlgebra ρ) :
    realJ ρ * realPlus f = realPlus f * realJ ρ := by
  rw [realPlus, mul_smul_comm, smul_mul_assoc, ring_conj_comm (realJ_sq ρ)]

/-- `f₋` anticommutes with `J` (it is `ℂ`-antilinear). -/
theorem realJ_mul_realMinus (f : realGEndAlgebra ρ) :
    realJ ρ * realMinus f = -(realMinus f * realJ ρ) := by
  rw [realMinus, mul_smul_comm, smul_mul_assoc, ring_conj_anticomm (realJ_sq ρ), smul_neg]

end ConjDecomp

/-- Problem 5.1.2(a), complex type. If the irreducible representation `V` is of complex type, then
`End_{ℝ[G]} V ≃ₐ[ℝ] ℂ`. -/
theorem realGEndAlgebra_equiv_complex_of_isComplexType
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsComplexType ρ) :
    Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] ℂ) := by
  sorry

/-- Problem 5.1.2(a), real type. If the irreducible representation `V` is of real type, then
`End_{ℝ[G]} V ≃ₐ[ℝ] Mat₂(ℝ)`. -/
theorem realGEndAlgebra_equiv_matrix_of_isRealType
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsRealType ρ) :
    Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  sorry

/-- Problem 5.1.2(a), quaternionic type. If the irreducible representation `V` is of quaternionic
type, then `End_{ℝ[G]} V ≃ₐ[ℝ] ℍ`. -/
theorem realGEndAlgebra_equiv_quaternion_of_isQuaternionicType
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsQuaternionicType ρ) :
    Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] Quaternion ℝ) := by
  sorry

/-- Problem 5.1.2(b). An irreducible complex representation `V` is of real type if and only if it
is the complexification of a real representation: there is a `G`-stable `ℝ`-subspace `W ⊆ V` (a
**real form**) whose `ℂ`-span is all of `V` and with `dim_ℝ W = dim_ℂ V`. -/
theorem isRealType_iff_exists_real_form
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.IsRealType ρ ↔
      ∃ W : Submodule ℝ V,
        (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) ∧
        Submodule.span ℂ (W : Set V) = ⊤ ∧
        Module.finrank ℝ W = Module.finrank ℂ V := by
  sorry

end Problem512

end Etingof
