import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Problem 2.3.16: The central character

Let `A` be an algebra over a field `k`. The center `Z(A)` is the set of elements commuting
with all of `A`.

**(a)** If `V` is an irreducible finite dimensional representation of `A` (over an algebraically
closed field), then any `z ∈ Z(A)` acts on `V` by multiplication by a scalar `χ_V(z)`, and
`χ_V : Z(A) → k` is a homomorphism (the **central character** of `V`).

This file formalizes part (a). The center is modelled by `Subalgebra.center k A` (its underlying
set is exactly the elements commuting with all of `A`, by `Subalgebra.mem_center_iff`).

The scalar action is a direct consequence of Schur's lemma for algebraically closed fields
(Corollary 2.3.10 / `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`): a central element
`z` acts by an `A`-linear endomorphism (it commutes with the `A`-action), hence by a scalar. The
homomorphism property is captured by packaging the whole assignment `z ↦ χ_V(z)` as a `k`-algebra
homomorphism `centralCharacter : Z(A) →ₐ[k] k`.

Parts (b) (indecomposable case) and (c) (need `ρ(z)` be scalar?) are tracked separately.
-/

namespace Etingof

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The action of a central element `z ∈ Z(A)` on `V`, packaged as an `A`-linear endomorphism.
Because `z` commutes with every element of `A`, the map `v ↦ z • v` commutes with the
`A`-action, so it is `A`-linear. -/
def centralAction (z : Subalgebra.center k A) : Module.End A V where
  toFun v := (z : A) • v
  map_add' := smul_add _
  map_smul' a v := by
    change (z : A) • (a • v) = a • ((z : A) • v)
    rw [smul_smul, smul_smul, Subalgebra.mem_center_iff.mp z.2 a]

omit [Module k V] [IsScalarTower k A V] in
@[simp]
theorem centralAction_apply (z : Subalgebra.center k A) (v : V) :
    centralAction z v = (z : A) • v := rfl

/-- The assignment `z ↦ (v ↦ z • v)` from the center of `A` to the `A`-linear endomorphisms of
`V`, as a `k`-algebra homomorphism. -/
def centralActionHom : Subalgebra.center k A →ₐ[k] Module.End A V where
  toFun := centralAction
  map_one' := by ext v; simp
  map_mul' z w := by
    ext v
    simp only [centralAction_apply, Module.End.mul_apply, Subalgebra.coe_mul, mul_smul]
  map_zero' := by ext v; simp
  map_add' z w := by ext v; simp [add_smul]
  commutes' r := by
    ext v
    simp only [centralAction_apply, Module.algebraMap_end_apply]
    exact algebraMap_smul A r v

variable [IsAlgClosed k] [IsSimpleModule A V] [FiniteDimensional k V]

/-- Schur's lemma (Corollary 2.3.10) packaged as a `k`-algebra isomorphism `k ≃ₐ End_A(V)`:
the algebra map `k → End_A(V)`, `c ↦ c • id`, is bijective. -/
noncomputable def endScalarEquiv : k ≃ₐ[k] Module.End A V :=
  AlgEquiv.ofBijective (Algebra.ofId k (Module.End A V))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)

@[simp]
theorem endScalarEquiv_apply (c : k) :
    endScalarEquiv (A := A) (V := V) c = algebraMap k (Module.End A V) c := rfl

/-- **The central character** `χ_V : Z(A) → k` of an irreducible finite dimensional
representation `V`, as a `k`-algebra homomorphism. (Etingof Problem 2.3.16(a))

It is defined by inverting Schur's isomorphism `k ≃ End_A(V)`: a central element `z` acts by a
scalar endomorphism, and `χ_V(z)` is that scalar. Being a composite of algebra homomorphisms it
is itself a homomorphism, which is the content of the second half of part (a). -/
noncomputable def centralCharacter : Subalgebra.center k A →ₐ[k] k :=
  (endScalarEquiv (k := k) (A := A) (V := V)).symm.toAlgHom.comp centralActionHom

/-- The defining property of the central character: every central element `z` acts on `V` by
multiplication by the scalar `χ_V(z)`. -/
theorem centralCharacter_smul (z : Subalgebra.center k A) (v : V) :
    (z : A) • v = centralCharacter (k := k) (V := V) z • v := by
  have h : endScalarEquiv (A := A) (V := V)
      (centralCharacter (k := k) (V := V) z) = centralActionHom (k := k) z :=
    endScalarEquiv.apply_symm_apply _
  rw [endScalarEquiv_apply] at h
  have hv := congrArg (fun f : Module.End A V => f v) h
  simp only [Module.algebraMap_end_apply] at hv
  -- `(centralActionHom z) v` is definitionally `(z : A) • v`
  exact hv.symm

/-- Part (a), existence form: any element of the center acts on an irreducible finite dimensional
representation by multiplication by some scalar. -/
theorem exists_central_scalar (z : Subalgebra.center k A) :
    ∃ c : k, ∀ v : V, (z : A) • v = c • v :=
  ⟨centralCharacter (k := k) (V := V) z, fun v => centralCharacter_smul z v⟩

end Etingof
