import EtingofRepresentationTheory.Chapter6.Problem6_9_3
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4

/-!
# Problem 6.9.3(b) for the indecomposable `V_α`

`Chapter6/Problem6_9_3.lean` proves that any representation of a quiver equipped with an
enumeration of its vertices along which every arrow decreases has a Jordan–Hölder series whose
factors are the vertex simples, with multiplicities the dimension vector.

This file supplies the two remaining ingredients for the exercise as stated in the book:

* `Etingof.Problem6_9_3.exists_orderEquiv` — every orientation of a Dynkin diagram *has* such an
  enumeration, obtained from the topological sort `Etingof.exists_topoSort`. This is where the
  orientation enters, and it is why the series is a series "for that orientation".
* `Etingof.Problem6_9_3.exists_compositionSeries_of_positiveRoot` — combining this with
  Corollary 6.8.4 (every positive root is the dimension vector of an indecomposable
  representation) yields, for every positive root `α`, an indecomposable `V_α` together with a
  Jordan–Hölder series of `V_α` in which the vertex simple `S i` occurs exactly `α i` times.
-/

namespace Etingof.Problem6_9_3

open Etingof Module

universe u

/-- **The ordering read off from an orientation.** Every orientation of a Dynkin diagram admits
an enumeration of the vertices along which every arrow strictly decreases, i.e. a topological
sort. (Dynkin diagrams are trees, so no orientation of one has an oriented cycle; the sort is
produced by `Etingof.exists_topoSort`.) -/
theorem exists_orderEquiv {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    [Q : Quiver.{0, 0} (Fin n)] (hQ : Etingof.IsOrientationOf Q adj) :
    ∃ order : Fin n ≃ Fin n,
      ∀ {v w : Fin n}, (v ⟶ w) → (order w : ℕ) < (order v : ℕ) := by
  classical
  obtain ⟨ordering, hperm, hnodup, htopo⟩ := Etingof.exists_topoSort hDynkin hQ
  have hlen : ordering.length = n := by
    rw [hperm.length_eq, List.length_finRange]
  have hlt : ∀ j : Fin n, (j : ℕ) < ordering.length := fun j => by rw [hlen]; exact j.isLt
  set g : Fin n → Fin n := fun j => ordering.get ⟨(j : ℕ), hlt j⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := hnodup.injective_get hab
    have h2 : (a : ℕ) = (b : ℕ) := by simpa using h1
    exact Fin.ext h2
  set G : Fin n ≃ Fin n := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj) with hG
  refine ⟨G.symm, ?_⟩
  intro v w arr
  by_contra hcon
  have hle : ((G.symm v : Fin n) : ℕ) ≤ ((G.symm w : Fin n) : ℕ) := by omega
  have hv : ordering.get ⟨((G.symm v : Fin n) : ℕ), hlt _⟩ = v := G.apply_symm_apply v
  have hw : ordering.get ⟨((G.symm w : Fin n) : ℕ), hlt _⟩ = w := G.apply_symm_apply w
  have hempty := htopo ((G.symm v : Fin n) : ℕ) ((G.symm w : Fin n) : ℕ) (hlt _) (hlt _) hle
  rw [hv, hw] at hempty
  exact hempty.elim arr

/-- **Problem 6.9.3(b).** Let `Q` be an orientation of a Dynkin diagram and `α` a positive root.
Then the indecomposable representation `V_α` with dimension vector `α` (Corollary 6.8.4) has a
Jordan–Hölder series for that orientation: a chain of subrepresentations
`0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ V_N = V_α` whose successive subquotients are the vertex simples `S i`, with
`S i` occurring exactly `α i` times. -/
theorem exists_compositionSeries_of_positiveRoot
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (α : Fin n → ℤ) (hα : Etingof.IsPositiveRoot n adj α)
    (k : Type u) [Field k]
    [Q : Quiver.{0, 0} (Fin n)] (hQ : Etingof.IsOrientationOf Q adj)
    [∀ a b : Fin n, Subsingleton (a ⟶ b)] :
    ∃ Vα : Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin n),
      Vα.IsIndecomposable ∧
      (∀ v, (dimVec Vα v : ℤ) = α v) ∧
      ∃ s : Etingof.QuiverRepCompositionSeries Vα, ∀ i, (s.mult i : ℤ) = α i := by
  classical
  obtain ⟨Vα, hFree, hFinite, hIndec, hdim⟩ := Etingof.Corollary6_8_4 hDynkin α hα k hQ
  obtain ⟨order, horder⟩ := exists_orderEquiv hDynkin hQ
  have hdv : ∀ v, Module.finrank k (Vα.obj v) = (α v).toNat := by
    intro v
    have := hdim v
    omega
  have basis : ∀ v, Basis (Fin ((α v).toNat)) k (Vα.obj v) := by
    intro v
    haveI := hFree v
    haveI := hFinite v
    exact Module.finBasisOfFinrankEq k (Vα.obj v) (hdv v)
  obtain ⟨s, _, hmult⟩ :=
    Etingof.exists_compositionSeries Vα n order horder (fun v => (α v).toNat) basis
  refine ⟨Vα, hIndec, fun v => ?_, s, fun i => ?_⟩
  · rw [dimVec, hdv v]
    have := hdim v
    omega
  · rw [hmult i]
    have := hdim i
    omega

end Etingof.Problem6_9_3
