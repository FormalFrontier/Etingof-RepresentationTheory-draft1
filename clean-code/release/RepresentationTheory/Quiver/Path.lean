/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.PathDegreeDecomposition

universe u

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

set_option linter.dupNamespace false

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

omit [DecidableEq Q] in
/-- A path of successor length decomposes into a path of the preceding length followed by an
edge. -/
theorem exists_comp_toPath_of_length_succ {a c : Q} (q : Quiver.Path a c) {n : ℕ}
    (hq : q.length = n + 1) :
    ∃ (b : Q) (p : Quiver.Path a b) (e : b ⟶ c), q = p.comp e.toPath ∧ p.length = n := by
  have hne : q.length ≠ 0 := by rw [hq]; exact Nat.succ_ne_zero n
  obtain ⟨b, p, e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons q).1 hne
  refine ⟨b, p, e, (Quiver.Path.comp_toPath_eq_cons p e).symm, ?_⟩
  rw [Quiver.Path.length_cons] at hq
  exact Nat.succ_injective hq

omit [DecidableEq Q] in
/-- Equality of path composites ending in edges determines the intermediate vertex, path, and
edge. -/
theorem comp_toPath_injective {a c b₁ b₂ : Q}
    (p₁ : Quiver.Path a b₁) (e₁ : b₁ ⟶ c) (p₂ : Quiver.Path a b₂) (e₂ : b₂ ⟶ c)
    (h : p₁.comp e₁.toPath = p₂.comp e₂.toPath) :
    b₁ = b₂ ∧ HEq p₁ p₂ ∧ HEq e₁ e₂ := by
  rw [Quiver.Path.comp_toPath_eq_cons, Quiver.Path.comp_toPath_eq_cons] at h
  simp only [Quiver.Path.cons.injEq] at h
  exact h

/-- A successor-length path admits a product factorization through a preceding-length path and
an edge. -/
theorem exists_factorization_of_length_succ {a c : Q} (q : Quiver.Path a c) {n : ℕ}
    (hq : q.length = n + 1) :
    ∃ (b : Q) (p : Quiver.Path a b) (e : b ⟶ c),
      (auxiliaryOfPath (⟨a, c, q⟩ : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryPathType k Q) =
          (auxiliaryOfPath (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryPathType k Q) *
            ofEdge ⟨b, c, e⟩ ∧
        p.length = n := by
  obtain ⟨b, p, e, hcomp, hlen⟩ := exists_comp_toPath_of_length_succ q hq
  refine ⟨b, p, e, ?_, hlen⟩
  rw [path_mul_arrow_eq_comp, ← hcomp]

/-- Equality of displayed products from path-edge factorizations determines both factors and the
intermediate vertex. -/
theorem mul_factorization_injective {a c b₁ b₂ : Q}
    (p₁ : Quiver.Path a b₁) (e₁ : b₁ ⟶ c) (p₂ : Quiver.Path a b₂) (e₂ : b₂ ⟶ c)
    (h : (auxiliaryOfPath (⟨a, b₁, p₁⟩ : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryPathType k Q) *
          ofEdge ⟨b₁, c, e₁⟩ =
        (auxiliaryOfPath (⟨a, b₂, p₂⟩ : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryPathType k Q) *
          ofEdge ⟨b₂, c, e₂⟩) :
    b₁ = b₂ ∧ HEq p₁ p₂ ∧ HEq e₁ e₂ := by
  set_option backward.isDefEq.respectTransparency false in
    rw [path_mul_arrow_eq_comp, path_mul_arrow_eq_comp, auxiliaryOfPath, auxiliaryOfPath,
      Finsupp.single_left_inj (one_ne_zero)] at h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact comp_toPath_injective p₁ e₁ p₂ e₂ h

end RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
