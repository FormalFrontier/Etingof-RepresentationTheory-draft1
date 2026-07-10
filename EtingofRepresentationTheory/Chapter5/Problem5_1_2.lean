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
