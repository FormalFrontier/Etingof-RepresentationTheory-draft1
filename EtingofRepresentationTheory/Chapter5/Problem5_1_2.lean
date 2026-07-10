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

/-- The `ℂ`-embedding `ℂ ⊆ End_{ℝ[G]} V` of the book: multiplication by a complex scalar `z`
is an `ℝ`-linear endomorphism of `V` that commutes with every `(ρ g).restrictScalars ℝ`
(because each `ρ g` is `ℂ`-linear), hence lies in the centralizer `realGEndAlgebra ρ`. This
packages that as an `ℝ`-algebra hom `ℂ →ₐ[ℝ] realGEndAlgebra ρ`. Reusable toolkit shared by the
real (#6327) and quaternionic (#6328) cases. -/
noncomputable def complexToRealGEnd (ρ : Representation ℂ G V) :
    ℂ →ₐ[ℝ] realGEndAlgebra ρ :=
  (Algebra.lsmul ℝ ℝ V).codRestrict (realGEndAlgebra ρ) (by
    intro z
    rw [realGEndAlgebra, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply, Algebra.lsmul_apply,
      map_smul])

omit [Fintype G] [Module.Finite ℂ V] in
@[simp]
theorem complexToRealGEnd_coe_apply (ρ : Representation ℂ G V) (z : ℂ) (v : V) :
    (complexToRealGEnd ρ z : Module.End ℝ V) v = z • v := rfl

omit [Fintype G] [Module.Finite ℂ V] in
/-- The `ℂ`-embedding is injective when `V ≠ 0`: if `z • v = 0` for all `v`, choosing a nonzero
`v` forces `z = 0`. -/
theorem complexToRealGEnd_injective (ρ : Representation ℂ G V) [Nontrivial V] :
    Function.Injective (complexToRealGEnd ρ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : (complexToRealGEnd ρ z : Module.End ℝ V) v = 0 := by rw [hz]; rfl
  rw [complexToRealGEnd_coe_apply] at this
  rcases smul_eq_zero.mp this with h | h
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

omit [Module ℝ V] [IsScalarTower ℝ ℂ V] in
open scoped ComplexConjugate in
/-- **Invariant positive-definite Hermitian form** (shared toolkit). Every finite-dimensional
complex representation `ρ` of a finite group carries a `G`-invariant, positive-definite Hermitian
(sesquilinear, linear in the first slot and conjugate-linear in the second) form: average the
standard coordinate form `h₀(v, w) = ∑ᵢ (b.repr v)ᵢ · conj (b.repr w)ᵢ` over the group.

Reused by the real (#6327) and quaternionic (#6328) cases to build the `j`-operator. -/
theorem exists_invariant_posdef_hermitian (ρ : Representation ℂ G V) :
    ∃ H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ,
      (∀ g v w, H (ρ g v) (ρ g w) = H v w) ∧ (∀ v, v ≠ 0 → 0 < (H v v).re) := by
  classical
  set b := Module.finBasis ℂ V with hb
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => ∑ g : G, ∑ i, b.repr (ρ g v) i * conj (b.repr (ρ g w) i))
      ?_ ?_ ?_ ?_, ?_, ?_⟩
  · -- additive in the first slot
    intro v₁ v₂ w
    simp only [map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  · -- ℂ-linear in the first slot
    intro c v w
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      mul_assoc]
  · -- additive in the second slot
    intro v w₁ w₂
    simp only [map_add, Finsupp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · -- conjugate-linear in the second slot
    intro c v w
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => by ring
  · -- G-invariance
    intro h v w
    simp only [LinearMap.mk₂'ₛₗ_apply]
    have hcomp : ∀ (g : G) (x : V), ρ g (ρ h x) = ρ (g * h) x := fun g x => by
      rw [map_mul]; rfl
    simp_rw [hcomp]
    exact Equiv.sum_comp (Equiv.mulRight h)
      (fun g : G => ∑ i, b.repr (ρ g v) i * conj (b.repr (ρ g w) i))
  · -- positive-definiteness
    intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    have hcast : (∑ g : G, ∑ i, (Complex.normSq (b.repr (ρ g v) i) : ℂ))
        = ((∑ g : G, ∑ i, Complex.normSq (b.repr (ρ g v) i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast, Complex.ofReal_re]
    refine Finset.sum_pos' (fun g _ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) ?_
    refine ⟨1, Finset.mem_univ 1, ?_⟩
    simp only [map_one, Module.End.one_apply]
    obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv (b.repr.injective (by ext i; simp [hcon i]))
    exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

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
