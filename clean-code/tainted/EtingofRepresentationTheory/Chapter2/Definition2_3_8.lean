import Mathlib.LinearAlgebra.Projection

/-!
# Definition 2.3.8: Indecomposable Representation

A nonzero representation V of an algebra A is said to be **indecomposable** if it is
not isomorphic to a direct sum of two nonzero representations.

## Mathlib correspondence (partial)

Mathlib has `Indecomposable` for order theory but not directly for modules.
We define indecomposability for modules as: V is nontrivial and for any submodules
W₁, W₂ with V = W₁ ⊕ W₂, either W₁ = 0 or W₂ = 0.

This is equivalent to saying that V has no nontrivial complemented submodules.
-/

-- not in Mathlib as of v4.28
/-- A module is **indecomposable** if it is nontrivial and cannot be decomposed as a
direct sum of two nonzero submodules. Etingof Definition 2.3.8. -/
def Etingof.IsIndecomposable (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : Prop :=
  Nontrivial V ∧ ∀ (W₁ W₂ : Submodule A V),
    IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥

universe u v

/-- Data exhibiting a representation as a direct sum of two nonzero representations. This is the
literal formulation used in Definition 2.3.8; `IsIndecomposable` uses the equivalent internal
complement formulation because that is the useful API for subsequent proofs. -/
structure Etingof.NontrivialDirectSumDecomposition
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] where
  /-- The first summand. -/
  V₁ : Type v
  /-- The second summand. -/
  V₂ : Type v
  /-- The additive group structure on the first summand. -/
  [addCommGroupV₁ : AddCommGroup V₁]
  /-- The additive group structure on the second summand. -/
  [addCommGroupV₂ : AddCommGroup V₂]
  /-- The representation structure on the first summand. -/
  [moduleV₁ : Module A V₁]
  /-- The representation structure on the second summand. -/
  [moduleV₂ : Module A V₂]
  /-- The first summand is nonzero. -/
  [nontrivialV₁ : Nontrivial V₁]
  /-- The second summand is nonzero. -/
  [nontrivialV₂ : Nontrivial V₂]
  /-- The representation is isomorphic to the product of the two summands. -/
  equiv : V ≃ₗ[A] V₁ × V₂

/-- The book's direct formulation: `V` is nonzero and is not isomorphic to a direct sum of two
nonzero representations. -/
def Etingof.IsIndecomposableAsDirectSum
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] : Prop :=
  Nontrivial V ∧ IsEmpty (Etingof.NontrivialDirectSumDecomposition A V)

/-- The internal-complement definition used by the project is equivalent to the source's literal
"not isomorphic to a direct sum of two nonzero representations" definition. -/
theorem Etingof.isIndecomposable_iff_asDirectSum
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] :
    Etingof.IsIndecomposable A V ↔ Etingof.IsIndecomposableAsDirectSum A V := by
  constructor
  · rintro h
    refine ⟨h.1, ?_⟩
    constructor
    intro d
    letI : AddCommGroup d.V₁ := d.addCommGroupV₁
    letI : AddCommGroup d.V₂ := d.addCommGroupV₂
    letI : Module A d.V₁ := d.moduleV₁
    letI : Module A d.V₂ := d.moduleV₂
    let W₁ : Submodule A V :=
      LinearMap.ker (LinearMap.snd A d.V₁ d.V₂ ∘ₗ d.equiv.toLinearMap)
    let W₂ : Submodule A V :=
      LinearMap.ker (LinearMap.fst A d.V₁ d.V₂ ∘ₗ d.equiv.toLinearMap)
    have hcompl : IsCompl W₁ W₂ := by
      constructor
      · apply disjoint_iff.mpr
        rw [Submodule.eq_bot_iff]
        intro x hx
        rcases hx with ⟨hx₁, hx₂⟩
        have hfst : (d.equiv x).1 = 0 := by
          exact LinearMap.mem_ker.mp hx₂
        have hsnd : (d.equiv x).2 = 0 := by
          exact LinearMap.mem_ker.mp hx₁
        apply d.equiv.injective
        simpa only [map_zero] using Prod.ext hfst hsnd
      · rw [codisjoint_iff]
        apply top_unique
        intro x hx
        let x₁ : V := d.equiv.symm ((d.equiv x).1, 0)
        let x₂ : V := d.equiv.symm (0, (d.equiv x).2)
        have hx₁ : x₁ ∈ W₁ := by
          change (LinearMap.snd A d.V₁ d.V₂ ∘ₗ d.equiv.toLinearMap) x₁ = 0
          simp [x₁]
        have hx₂ : x₂ ∈ W₂ := by
          change (LinearMap.fst A d.V₁ d.V₂ ∘ₗ d.equiv.toLinearMap) x₂ = 0
          simp [x₂]
        have hsum : x₁ + x₂ = x := by
          apply d.equiv.injective
          simp [x₁, x₂]
        rw [← hsum]
        exact Submodule.add_mem_sup hx₁ hx₂
    rcases h.2 W₁ W₂ hcompl with hW₁ | hW₂
    · letI := d.nontrivialV₁
      obtain ⟨v₁, hv₁⟩ := exists_ne (0 : d.V₁)
      let x : V := d.equiv.symm (v₁, 0)
      have hx : x ∈ W₁ := by
        change (LinearMap.snd A d.V₁ d.V₂ ∘ₗ d.equiv.toLinearMap) x = 0
        simp [x]
      have hx0 : x = 0 := by simpa [hW₁] using hx
      apply hv₁
      have := congrArg (fun y => (d.equiv y).1) hx0
      simpa [x] using this
    · letI := d.nontrivialV₂
      obtain ⟨v₂, hv₂⟩ := exists_ne (0 : d.V₂)
      let x : V := d.equiv.symm (0, v₂)
      have hx : x ∈ W₂ := by
        change (LinearMap.fst A d.V₁ d.V₂ ∘ₗ d.equiv.toLinearMap) x = 0
        simp [x]
      have hx0 : x = 0 := by simpa [hW₂] using hx
      apply hv₂
      have := congrArg (fun y => (d.equiv y).2) hx0
      simpa [x] using this
  · rintro h
    refine ⟨h.1, ?_⟩
    intro W₁ W₂ hcompl
    by_cases hW₁ : W₁ = ⊥
    · exact Or.inl hW₁
    by_cases hW₂ : W₂ = ⊥
    · exact Or.inr hW₂
    letI : Nontrivial W₁ := Submodule.nontrivial_iff_ne_bot.mpr hW₁
    letI : Nontrivial W₂ := Submodule.nontrivial_iff_ne_bot.mpr hW₂
    let d : Etingof.NontrivialDirectSumDecomposition A V := {
      V₁ := W₁
      V₂ := W₂
      equiv := (W₁.prodEquivOfIsCompl W₂ hcompl).symm }
    letI : IsEmpty (Etingof.NontrivialDirectSumDecomposition A V) := h.2
    exact isEmptyElim d

/-- An indecomposable module has no nontrivial direct sum decomposition (negation form).
Useful for proofs that proceed by contradiction on a decomposition. -/
theorem Etingof.IsIndecomposable.not_exists_nontrivial_compl {A : Type*} {V : Type*}
    [Ring A] [AddCommGroup V] [Module A V]
    (h : Etingof.IsIndecomposable A V) :
    ¬ ∃ (M N : Submodule A V), M ≠ ⊥ ∧ N ≠ ⊥ ∧ M ⊔ N = ⊤ ∧ M ⊓ N = ⊥ := by
  rintro ⟨M, N, hM, hN, hSup, hInf⟩
  have hC : IsCompl M N :=
    ⟨disjoint_iff.mpr hInf, codisjoint_iff.mpr (top_le_iff.mp (hSup ▸ le_rfl))⟩
  rcases h.2 M N hC with rfl | rfl
  · exact hM rfl
  · exact hN rfl
