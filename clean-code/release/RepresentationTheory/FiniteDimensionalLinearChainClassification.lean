/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.FiniteDimensionalLinearChainRepresentations
import RepresentationTheory.Alignment.Attribute

/-!
# Classification of finite-dimensional linear-chain representations

This module constructs six standard linear-chain representations, proves that they are
indecomposable, and classifies every indecomposable linear-chain representation up to equivalence.
-/

namespace RepresentationTheory.FiniteDimensionalLinearChainRepresentations

open Module

/-- An equivalence between two finite-dimensional three-space linear-chain representations. -/
structure LinearChainRepresentation.Equiv {k : Type*} [Field k]
    (ρ σ : LinearChainRepresentation k) where
  /-- The linear equivalence between the left spaces of two equivalent chain representations. -/
  leftLinearEquiv : ρ.left ≃ₗ[k] σ.left
  /-- The linear equivalence between the middle spaces of two equivalent chain representations. -/
  middleLinearEquiv : ρ.middle ≃ₗ[k] σ.middle
  /-- The linear equivalence between the right spaces of two equivalent chain representations. -/
  rightLinearEquiv : ρ.right ≃ₗ[k] σ.right
  /-- The left and middle linear equivalences intertwine the first structure maps of equivalent chains. -/
  leftToMiddle_comm_apply : ∀ x,
    middleLinearEquiv (ρ.leftToMiddle x) = σ.leftToMiddle (leftLinearEquiv x)
  /-- The middle and right linear equivalences intertwine the second structure maps of equivalent chains. -/
  middleToRight_comm_apply : ∀ y,
    rightLinearEquiv (ρ.middleToRight y) = σ.middleToRight (middleLinearEquiv y)

namespace LinearChainRepresentation.Equiv

/-- The identity equivalence of a linear-chain representation. -/
def refl {k : Type*} [Field k] (ρ : LinearChainRepresentation k) : ρ.Equiv ρ where
  leftLinearEquiv := LinearEquiv.refl k ρ.left
  middleLinearEquiv := LinearEquiv.refl k ρ.middle
  rightLinearEquiv := LinearEquiv.refl k ρ.right
  leftToMiddle_comm_apply := fun _ => rfl
  middleToRight_comm_apply := fun _ => rfl

/-- Reverses an equivalence of linear-chain representations. -/
def symm {k : Type*} [Field k] {ρ σ : LinearChainRepresentation k}
    (e : ρ.Equiv σ) : σ.Equiv ρ where
  leftLinearEquiv := e.leftLinearEquiv.symm
  middleLinearEquiv := e.middleLinearEquiv.symm
  rightLinearEquiv := e.rightLinearEquiv.symm
  leftToMiddle_comm_apply := fun y => by
    apply e.middleLinearEquiv.injective
    rw [e.middleLinearEquiv.apply_symm_apply, e.leftToMiddle_comm_apply,
      e.leftLinearEquiv.apply_symm_apply]
  middleToRight_comm_apply := fun y => by
    apply e.rightLinearEquiv.injective
    rw [e.rightLinearEquiv.apply_symm_apply, e.middleToRight_comm_apply,
      e.middleLinearEquiv.apply_symm_apply]

/-- Composes two equivalences of linear-chain representations. -/
def trans {k : Type*} [Field k] {ρ σ τ : LinearChainRepresentation k}
    (e : ρ.Equiv σ) (e' : σ.Equiv τ) : ρ.Equiv τ where
  leftLinearEquiv := e.leftLinearEquiv.trans e'.leftLinearEquiv
  middleLinearEquiv := e.middleLinearEquiv.trans e'.middleLinearEquiv
  rightLinearEquiv := e.rightLinearEquiv.trans e'.rightLinearEquiv
  leftToMiddle_comm_apply := fun x => by
    simp only [LinearEquiv.trans_apply]
    rw [e.leftToMiddle_comm_apply, e'.leftToMiddle_comm_apply]
  middleToRight_comm_apply := fun y => by
    simp only [LinearEquiv.trans_apply]
    rw [e.middleToRight_comm_apply, e'.middleToRight_comm_apply]

/-- A chain-representation equivalence preserves the finranks of all three spaces. -/
lemma finrank_eq {k : Type*} [Field k] {ρ σ : LinearChainRepresentation k} (e : ρ.Equiv σ) :
    Module.finrank k ρ.left = Module.finrank k σ.left ∧
    Module.finrank k ρ.middle = Module.finrank k σ.middle ∧
    Module.finrank k ρ.right = Module.finrank k σ.right :=
  ⟨e.leftLinearEquiv.finrank_eq, e.middleLinearEquiv.finrank_eq,
    e.rightLinearEquiv.finrank_eq⟩

end LinearChainRepresentation.Equiv

/-- A standard linear-chain representation of dimension triple `(1, 0, 0)`. -/
abbrev LinearChainRepresentation.oneZeroZeroModel (k : Type*) [Field k] :
    LinearChainRepresentation k where
  left := k
  middle := PUnit
  right := PUnit
  leftToMiddle := 0
  middleToRight := 0

/-- A standard linear-chain representation of dimension triple `(0, 1, 0)`. -/
abbrev LinearChainRepresentation.zeroOneZeroModel (k : Type*) [Field k] :
    LinearChainRepresentation k where
  left := PUnit
  middle := k
  right := PUnit
  leftToMiddle := 0
  middleToRight := 0

/-- A standard linear-chain representation of dimension triple `(0, 0, 1)`. -/
abbrev LinearChainRepresentation.zeroZeroOneModel (k : Type*) [Field k] :
    LinearChainRepresentation k where
  left := PUnit
  middle := PUnit
  right := k
  leftToMiddle := 0
  middleToRight := 0

/-- A standard linear-chain representation of dimension triple `(1, 1, 0)`. -/
abbrev LinearChainRepresentation.oneOneZeroModel (k : Type*) [Field k] :
    LinearChainRepresentation k where
  left := k
  middle := k
  right := PUnit
  leftToMiddle := LinearMap.id
  middleToRight := 0

/-- A standard linear-chain representation of dimension triple `(0, 1, 1)`. -/
abbrev LinearChainRepresentation.zeroOneOneModel (k : Type*) [Field k] :
    LinearChainRepresentation k where
  left := PUnit
  middle := k
  right := k
  leftToMiddle := 0
  middleToRight := LinearMap.id

/-- A standard linear-chain representation of dimension triple `(1, 1, 1)`. -/
abbrev LinearChainRepresentation.oneOneOneModel (k : Type*) [Field k] :
    LinearChainRepresentation k where
  left := k
  middle := k
  right := k
  leftToMiddle := LinearMap.id
  middleToRight := LinearMap.id

namespace LinearChainRepresentation

/-- Every submodule of a subsingleton module is trivial. -/
private theorem submodule_eq_bot_of_subsingleton {k M : Type*} [Field k] [AddCommGroup M]
    [Module k M] [Subsingleton M] (p : Submodule k M) : p = ⊥ := by
  rw [eq_bot_iff]; intro x _; rw [Submodule.mem_bot]; exact Subsingleton.elim _ _

/-- The standard chain model of dimension triple `(1, 0, 0)` is indecomposable. -/
theorem oneZeroZeroModel_isIndecomposable (k : Type*) [Field k] :
    (oneZeroZeroModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ _ _ _ _ _ _
  have hsum : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, submodule_eq_bot_of_subsingleton p₂,
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega), submodule_eq_bot_of_subsingleton q₂,
      submodule_eq_bot_of_subsingleton q₃⟩

/-- The standard chain model of dimension triple `(0, 1, 0)` is indecomposable. -/
theorem zeroOneZeroModel_isIndecomposable (k : Type*) [Field k] :
    (zeroOneZeroModel k).IsIndecomposable := by
  refine ⟨Or.inr (Or.inl Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ hpq₂ _ _ _ _ _
  have hsum : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₂) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, Submodule.finrank_eq_zero.mp h0,
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁, Submodule.finrank_eq_zero.mp (by omega),
      submodule_eq_bot_of_subsingleton q₃⟩

/-- The standard chain model of dimension triple `(0, 0, 1)` is indecomposable. -/
theorem zeroZeroOneModel_isIndecomposable (k : Type*) [Field k] :
    (zeroZeroOneModel k).IsIndecomposable := by
  refine ⟨Or.inr (Or.inr Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ _ hpq₃ _ _ _ _
  have hsum : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₃) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, submodule_eq_bot_of_subsingleton p₂,
      Submodule.finrank_eq_zero.mp h0⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁, submodule_eq_bot_of_subsingleton q₂,
      Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The standard chain model of dimension triple `(1, 1, 0)` is indecomposable. -/
theorem oneOneZeroModel_isIndecomposable (k : Type*) [Field k] :
    (oneOneZeroModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ hpq₂ _ hfp hfq _ _
  have hsum₁ : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hfp' : Module.finrank k p₁ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfp x hx)
  have hfq' : Module.finrank k q₁ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfq x hx)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, Submodule.finrank_eq_zero.mp (by omega),
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega), submodule_eq_bot_of_subsingleton q₃⟩

/-- The standard chain model of dimension triple `(0, 1, 1)` is indecomposable. -/
theorem zeroOneOneModel_isIndecomposable (k : Type*) [Field k] :
    (zeroOneOneModel k).IsIndecomposable := by
  refine ⟨Or.inr (Or.inl Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ hpq₂ hpq₃ _ _ hgp hgq
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hsum₃ : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  have hgp' : Module.finrank k p₂ ≤ Module.finrank k p₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgp y hy)
  have hgq' : Module.finrank k q₂ ≤ Module.finrank k q₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgq y hy)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₂) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, Submodule.finrank_eq_zero.mp h0,
      Submodule.finrank_eq_zero.mp (by omega)⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁,
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The standard chain model of dimension triple `(1, 1, 1)` is indecomposable. -/
theorem oneOneOneModel_isIndecomposable (k : Type*) [Field k] :
    (oneOneOneModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ hpq₂ hpq₃ hfp hfq hgp hgq
  have hsum₁ : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hsum₃ : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  have hfp' : Module.finrank k p₁ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfp x hx)
  have hfq' : Module.finrank k q₁ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfq x hx)
  have hgp' : Module.finrank k p₂ ≤ Module.finrank k p₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgp y hy)
  have hgq' : Module.finrank k q₂ ≤ Module.finrank k q₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgq y hy)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega)⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The six-element indexed family of standard finite-dimensional linear-chain representations. -/
def standardModel (k : Type*) [Field k] : Fin 6 → LinearChainRepresentation k
  | 0 => oneZeroZeroModel k
  | 1 => zeroOneZeroModel k
  | 2 => zeroZeroOneModel k
  | 3 => oneOneZeroModel k
  | 4 => zeroOneOneModel k
  | 5 => oneOneOneModel k

/-- Every member of the six-element family of standard chain models is indecomposable. -/
@[source_ref "Chapter6/Example6.2.4" (role := primary)]
theorem standardModel_isIndecomposable (k : Type*) [Field k] (i : Fin 6) :
    (standardModel k i).IsIndecomposable := by
  fin_cases i
  · exact oneZeroZeroModel_isIndecomposable k
  · exact zeroOneZeroModel_isIndecomposable k
  · exact zeroZeroOneModel_isIndecomposable k
  · exact oneOneZeroModel_isIndecomposable k
  · exact zeroOneOneModel_isIndecomposable k
  · exact oneOneOneModel_isIndecomposable k

/-- The ordered triple of left, middle, and right dimensions of a linear-chain representation. -/
noncomputable def dimension (k : Type*) [Field k] (σ : LinearChainRepresentation k) :
    ℕ × ℕ × ℕ :=
  (Module.finrank k σ.left, Module.finrank k σ.middle, Module.finrank k σ.right)

/-- Equivalent linear-chain representations have the same ordered triple of dimensions. -/
theorem Equiv.dimension_eq {k : Type*} [Field k] {ρ σ : LinearChainRepresentation k}
    (e : ρ.Equiv σ) : dimension k ρ = dimension k σ := by
  obtain ⟨h₁, h₂, h₃⟩ := e.finrank_eq
  simp [dimension, h₁, h₂, h₃]

/-- The corresponding standard chain model has dimension triple `(1, 0, 0)`. -/
theorem oneZeroZeroModel_dimension (k : Type*) [Field k] :
    dimension k (oneZeroZeroModel k) = (1, 0, 0) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard chain model has dimension triple `(0, 1, 0)`. -/
theorem zeroOneZeroModel_dimension (k : Type*) [Field k] :
    dimension k (zeroOneZeroModel k) = (0, 1, 0) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard chain model has dimension triple `(0, 0, 1)`. -/
theorem zeroZeroOneModel_dimension (k : Type*) [Field k] :
    dimension k (zeroZeroOneModel k) = (0, 0, 1) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard chain model has dimension triple `(1, 1, 0)`. -/
theorem oneOneZeroModel_dimension (k : Type*) [Field k] :
    dimension k (oneOneZeroModel k) = (1, 1, 0) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard chain model has dimension triple `(0, 1, 1)`. -/
theorem zeroOneOneModel_dimension (k : Type*) [Field k] :
    dimension k (zeroOneOneModel k) = (0, 1, 1) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard chain model has dimension triple `(1, 1, 1)`. -/
theorem oneOneOneModel_dimension (k : Type*) [Field k] :
    dimension k (oneOneOneModel k) = (1, 1, 1) := by
  simp [dimension, finrank_self]

/-- Every indecomposable linear-chain representation is equivalent to a unique member of the six-element family of standard models. -/
@[source_ref "Chapter6/Example6.2.4" (role := supporting)]
theorem existsUnique_equiv_standardModel_of_isIndecomposable (k : Type*) [Field k]
    (ρ : LinearChainRepresentation k) (hind : ρ.IsIndecomposable) :
    ∃! i : Fin 6, Nonempty (ρ.Equiv (standardModel k i)) := by
  have hexists : ∃ i : Fin 6, Nonempty (ρ.Equiv (standardModel k i)) := by
    rcases RepresentationTheory.FiniteDimensionalLinearChainRepresentations.isIndecomposable_dimension_cases
      k ρ hind with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, hf⟩ | ⟨h1, h2, h3, hg⟩ |
        ⟨h1, h2, h3, hf, hg⟩
    · refine ⟨0, ?_⟩
      change Nonempty (ρ.Equiv (oneZeroZeroModel k))
      exact ⟨{ leftLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact (finrank_self k).symm)).some
               middleLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some
               rightLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
               leftToMiddle_comm_apply := fun _ => Subsingleton.elim _ _
               middleToRight_comm_apply := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨1, ?_⟩
      change Nonempty (ρ.Equiv (zeroOneZeroModel k))
      haveI hs₁ : Subsingleton ρ.left := Module.finrank_zero_iff.mp h1
      exact ⟨{ leftLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               middleLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact (finrank_self k).symm)).some
               rightLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
               leftToMiddle_comm_apply := fun x => by rw [Subsingleton.elim x 0]; simp
               middleToRight_comm_apply := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨2, ?_⟩
      change Nonempty (ρ.Equiv (zeroZeroOneModel k))
      haveI hs₂ : Subsingleton ρ.middle := Module.finrank_zero_iff.mp h2
      exact ⟨{ leftLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               middleLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some
               rightLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact (finrank_self k).symm)).some
               leftToMiddle_comm_apply := fun _ => Subsingleton.elim _ _
               middleToRight_comm_apply := fun y => by rw [Subsingleton.elim y 0]; simp }⟩
    · refine ⟨3, ?_⟩
      change Nonempty (ρ.Equiv (oneOneZeroModel k))
      haveI hs₃ : Subsingleton ρ.right := Module.finrank_zero_iff.mp h3
      have hf_bij : Function.Bijective ρ.leftToMiddle :=
        ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h1, h2])).mp hf⟩
      obtain ⟨e₁⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.left) (M' := k) (by rw [h1]; exact (finrank_self k).symm)
      let fEq : ρ.left ≃ₗ[k] ρ.middle := LinearEquiv.ofBijective ρ.leftToMiddle hf_bij
      refine ⟨{ leftLinearEquiv := e₁, middleLinearEquiv := fEq.symm.trans e₁,
                rightLinearEquiv := ?_
                leftToMiddle_comm_apply := fun x => ?_
                middleToRight_comm_apply := fun _ => Subsingleton.elim _ _ }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
      · have hfx : fEq.symm (ρ.leftToMiddle x) = x := fEq.symm_apply_apply x
        simp only [LinearEquiv.trans_apply, hfx]
        rfl
    · refine ⟨4, ?_⟩
      change Nonempty (ρ.Equiv (zeroOneOneModel k))
      haveI hs₁ : Subsingleton ρ.left := Module.finrank_zero_iff.mp h1
      have hg_bij : Function.Bijective ρ.middleToRight :=
        ⟨hg, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h2, h3])).mp hg⟩
      obtain ⟨e₂⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.middle) (M' := k) (by rw [h2]; exact (finrank_self k).symm)
      let gEq : ρ.middle ≃ₗ[k] ρ.right := LinearEquiv.ofBijective ρ.middleToRight hg_bij
      refine ⟨{ leftLinearEquiv := ?_, middleLinearEquiv := e₂,
                rightLinearEquiv := gEq.symm.trans e₂
                leftToMiddle_comm_apply := fun x => by rw [Subsingleton.elim x 0]; simp
                middleToRight_comm_apply := fun y => ?_ }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
      · have hgy : gEq.symm (ρ.middleToRight y) = y := gEq.symm_apply_apply y
        simp only [LinearEquiv.trans_apply, hgy]
        rfl
    · refine ⟨5, ?_⟩
      change Nonempty (ρ.Equiv (oneOneOneModel k))
      have hf_bij : Function.Bijective ρ.leftToMiddle :=
        ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h1, h2])).mp hf⟩
      have hg_bij : Function.Bijective ρ.middleToRight :=
        ⟨hg, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h2, h3])).mp hg⟩
      obtain ⟨e₁⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.left) (M' := k) (by rw [h1]; exact (finrank_self k).symm)
      let fEq : ρ.left ≃ₗ[k] ρ.middle := LinearEquiv.ofBijective ρ.leftToMiddle hf_bij
      let gEq : ρ.middle ≃ₗ[k] ρ.right := LinearEquiv.ofBijective ρ.middleToRight hg_bij
      refine ⟨{ leftLinearEquiv := e₁, middleLinearEquiv := fEq.symm.trans e₁,
                rightLinearEquiv := gEq.symm.trans (fEq.symm.trans e₁)
                leftToMiddle_comm_apply := fun x => ?_
                middleToRight_comm_apply := fun y => ?_ }⟩
      · have hfx : fEq.symm (ρ.leftToMiddle x) = x := fEq.symm_apply_apply x
        simp only [LinearEquiv.trans_apply, hfx]
        rfl
      · have hgy : gEq.symm (ρ.middleToRight y) = y := gEq.symm_apply_apply y
        simp only [LinearEquiv.trans_apply, hgy]
        rfl
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, hi, fun j hj => ?_⟩
  obtain ⟨ei⟩ := hi
  obtain ⟨ej⟩ := hj
  have hdv : dimension k (standardModel k j) = dimension k (standardModel k i) :=
    (ej.symm.trans ei).dimension_eq
  fin_cases i <;> fin_cases j <;>
    simp_all [standardModel, oneZeroZeroModel_dimension, zeroOneZeroModel_dimension,
      zeroZeroOneModel_dimension, oneOneZeroModel_dimension, zeroOneOneModel_dimension,
      oneOneOneModel_dimension]

end LinearChainRepresentation

end RepresentationTheory.FiniteDimensionalLinearChainRepresentations
