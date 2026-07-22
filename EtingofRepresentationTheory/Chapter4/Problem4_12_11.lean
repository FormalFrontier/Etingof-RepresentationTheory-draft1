import Mathlib

/-!
# Problem 4.12.11: elasticity theory and representations of `SO(3)`

**Problem 4.12.11.** (Elasticity theory.) Let `V = ℝ³` with its standard inner product, on
which `SO(3)` acts. The deformation tensor lives in `S²V` and the stress tensor in
`End(V)`, and Hooke's law is a linear `SO(3)`-equivariant map `f : S²V → End(V)`.

(a) Show that `End(V)` admits a decomposition `ℝ ⊕ V ⊕ W`, where `ℝ` is the trivial
representation, `V` is the standard `3`-dimensional representation, and `W` is a
`5`-dimensional representation of `SO(3)`. Show that `S²V = ℝ ⊕ W`.

(b) Show that `V` and `W` are irreducible, even after complexification. Deduce using Schur's
lemma that `S_P` is always symmetric, and for `x ∈ ℝ`, `y ∈ W` one has `f(x + y) = Kx + μy`
for some real numbers `K, μ` (the compression modulus `K` and shearing modulus `μ`).

## Formalization

We take `V = Fin 3 → ℝ` and `End(V) = Matrix (Fin 3) (Fin 3) ℝ`, with `SO(3)` modelled by
`Matrix.specialOrthogonalGroup (Fin 3) ℝ` acting on `End(V)` by conjugation
`M ↦ A · M · Aᵀ` (`conjRep`; for orthogonal `A`, `Aᵀ = A⁻¹`). Inside `End(V)`:

* `scalarSub` = scalar matrices `ℝ·1` (the trivial summand `ℝ`);
* `skewSub` = skew-symmetric matrices `Mᵀ = -M` (`3`-dimensional, isomorphic to the standard
  representation `V`);
* `symSub` = symmetric matrices `Mᵀ = M` (this is `S²V`, `6`-dimensional);
* `tracelessSymSub` = traceless symmetric matrices (the `5`-dimensional representation `W`).

Statements (faithful signatures, `sorry` proofs — a statement pass):

* **(a)** each subspace is `SO(3)`-invariant; `End(V) = scalarSub ⊕ skewSub ⊕ tracelessSymSub`
  and `symSub = scalarSub ⊕ tracelessSymSub`; the dimensions are `1, 3, 5`.
* **(b)** `skewSub` (`≅ V`) and `tracelessSymSub` (`= W`) are irreducible (stated over `ℝ`;
  the irreducibility survives complexification, recorded in this docstring). Hooke's law:
  any `SO(3)`-equivariant `f : End(V) → End(V)` acts as a scalar `K` on `scalarSub` and a
  scalar `μ` on `tracelessSymSub`, and maps symmetric matrices to symmetric matrices (so the
  stress tensor `S_P` is symmetric).
-/

open Matrix

noncomputable section

namespace Etingof.Problem4_12_11

/-- `SO(3)`, modelled as the special orthogonal group of `3 × 3` real matrices. -/
abbrev SO3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := specialOrthogonalGroup (Fin 3) ℝ

/-- `End(V) = Matrix (Fin 3) (Fin 3) ℝ`, on which `SO(3)` acts by conjugation. -/
abbrev EndV : Type := Matrix (Fin 3) (Fin 3) ℝ

/-- The conjugation action of `SO(3)` on `End(V)`: `conjRep A M = A · M · Aᵀ`. Since `A` is
orthogonal, `Aᵀ = A⁻¹`, so this is genuine conjugation. -/
def conjRep : Representation ℝ SO3 EndV where
  toFun A := (LinearMap.mulLeft ℝ (A : EndV)).comp
    (LinearMap.mulRight ℝ (star (A : EndV)))
  map_one' := by
    ext M
    simp
  map_mul' A B := by
    ext M
    simp only [Submonoid.coe_mul, star_mul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, Module.End.mul_apply]
    simp [mul_assoc]

@[simp]
theorem conjRep_apply (A : SO3) (M : EndV) :
    conjRep A M = (A : EndV) * M * star (A : EndV) := by
  simp [conjRep, mul_assoc]

/-- The trivial summand `ℝ ⊆ End(V)`: the scalar matrices `ℝ·1`. -/
def scalarSub : Submodule ℝ EndV := Submodule.span ℝ {(1 : EndV)}

/-- The skew-symmetric matrices `{M | Mᵀ = -M}` — a `3`-dimensional subrepresentation
isomorphic to the standard representation `V`. -/
def skewSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]; abel
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha, smul_neg]

/-- The symmetric matrices `{M | Mᵀ = M}` — this is `S²V ⊆ End(V)`. -/
def symSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha]

/-- The traceless symmetric matrices `{M | Mᵀ = M ∧ trace M = 0}` — the `5`-dimensional
representation `W`. -/
def tracelessSymSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = M ∧ M.trace = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact ⟨by rw [transpose_add, ha.1, hb.1], by rw [trace_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := by simp only [Set.mem_setOf_eq]; exact ⟨by simp, by simp⟩
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ⟨by rw [transpose_smul, ha.1], by rw [trace_smul, ha.2, smul_zero]⟩

theorem scalar_le_sym : scalarSub ≤ symSub := by
  intro M hM
  rw [scalarSub, Submodule.mem_span_singleton] at hM
  obtain ⟨c, rfl⟩ := hM
  change (c • (1 : EndV))ᵀ = c • 1
  rw [transpose_smul, transpose_one]

theorem tracelessSym_le_sym : tracelessSymSub ≤ symSub := fun _ hM => hM.1

/-! ### Part (a): the decomposition -/

/-- **(a)** Each of the three subspaces is `SO(3)`-invariant. -/
theorem conjRep_invariant (S : Submodule ℝ EndV)
    (hS : S = scalarSub ∨ S = skewSub ∨ S = tracelessSymSub)
    (A : SO3) (M : EndV) (hM : M ∈ S) : conjRep A M ∈ S := by
  sorry

/-- **(a)** `End(V) = ℝ ⊕ V ⊕ W`: the three subspaces form an internal direct sum of
`End(V)`. -/
theorem endV_isInternal :
    DirectSum.IsInternal ![scalarSub, skewSub, tracelessSymSub] := by
  sorry

/-- **(a)** `S²V = ℝ ⊕ W`: the symmetric matrices are the internal direct sum of the scalars
and the traceless symmetric matrices. -/
theorem symSub_eq_scalar_sup_tracelessSym :
    scalarSub ⊔ tracelessSymSub = symSub ∧ scalarSub ⊓ tracelessSymSub = ⊥ := by
  sorry

theorem scalarSub_finrank : Module.finrank ℝ scalarSub = 1 := by sorry
theorem skewSub_finrank : Module.finrank ℝ skewSub = 3 := by sorry
theorem tracelessSymSub_finrank : Module.finrank ℝ tracelessSymSub = 5 := by sorry

/-! ### Part (b): irreducibility and Hooke's law -/

/-- **(b)** The standard representation `V ≅ skewSub` is irreducible: every `SO(3)`-invariant
subspace contained in `skewSub` is `⊥` or all of `skewSub`. (Irreducibility survives
complexification.) -/
theorem skewSub_irreducible (U : Submodule ℝ EndV) (hUle : U ≤ skewSub)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRep A M ∈ U) :
    U = ⊥ ∨ U = skewSub := by
  sorry

/-- **(b)** The representation `W = tracelessSymSub` is irreducible: every `SO(3)`-invariant
subspace contained in `tracelessSymSub` is `⊥` or all of `tracelessSymSub`. (Irreducibility
survives complexification.) -/
theorem tracelessSymSub_irreducible (U : Submodule ℝ EndV) (hUle : U ≤ tracelessSymSub)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRep A M ∈ U) :
    U = ⊥ ∨ U = tracelessSymSub := by
  sorry

/-- **(b), Hooke's law.** Any `SO(3)`-equivariant linear map `f : End(V) → End(V)` acts as a
scalar `K` (the compression modulus) on the trivial component `scalarSub` and a scalar `μ`
(the shearing modulus) on the `W`-component `tracelessSymSub`, and it maps symmetric matrices
to symmetric matrices (so the stress tensor `S_P = f(d_P)` is always symmetric). Thus for
`x ∈ ℝ`, `y ∈ W`, `f(x + y) = Kx + μy`. -/
theorem hooke_law (f : EndV →ₗ[ℝ] EndV)
    (hf : ∀ A : SO3, f.comp (conjRep A) = (conjRep A).comp f) :
    ∃ K μ : ℝ,
      (∀ x ∈ scalarSub, f x = K • x) ∧
      (∀ y ∈ tracelessSymSub, f y = μ • y) ∧
      (∀ x ∈ symSub, f x ∈ symSub) := by
  sorry

end Etingof.Problem4_12_11
