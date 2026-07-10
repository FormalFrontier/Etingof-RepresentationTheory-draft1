import EtingofRepresentationTheory.Chapter6.Problem6_9_3
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter2.Theorem2_1_2

/-!
# Problem 3.9.3: Irreducible representations and `Ext¹` for path algebras

Let `Q` be a quiver without oriented cycles and `P_Q` its path algebra. This problem asks to
find the irreducible representations of `P_Q`, compute `Ext¹` between them, and classify the
2-dimensional representations.

Representations of the path algebra `P_Q` are the same as **quiver representations** of `Q`:
a vector space at each vertex together with a linear map for each arrow. We use the project's
`Etingof.QuiverRepresentation k Q` (Definition 2.8.3) and reuse the `Ext¹` differential and
simple representations from `Chapter6/Problem6_9_3` (which formalises the same
`Ext¹`/simple-representation content for Section 6.9).

* **Irreducibles.** The irreducible representations are the simple representations `S_i`
  (`simpleRep i`): one-dimensional at vertex `i`, zero elsewhere, all arrows acting by `0`.
  Every irreducible representation is isomorphic to some `S_i`.
* **`Ext¹` between irreducibles.** `Ext¹(S_i, S_j)` has dimension equal to the number of
  arrows `i → j`; in particular it vanishes iff there are no arrows `i → j`.
* **2-dimensional representations.** A representation of total dimension `2` is either
  decomposable (a sum `S_i ⊕ S_j` of two simples) or indecomposable, in which case it is the
  representation supported on a single arrow `a : i → j` with `a` acting as an isomorphism.

Statement pass: all objects are genuinely constructed (reusing the quiver-representation
infrastructure); the proofs are `sorry`.
-/

namespace Etingof.Problem3_9_3

open Etingof (QuiverRepresentation QuiverRepresentationEquiv)
open Etingof.Problem6_9_3 (simpleRep Ext1Vanishes dimVec)

variable {k Q : Type*} [Field k] [Quiver Q]

/-- A quiver has **no oriented cycles** if the only path from a vertex to itself is the
trivial (nil) path. -/
def NoOrientedCycles (Q : Type*) [Quiver Q] : Prop :=
  ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil

/-- A quiver representation is **irreducible** (simple) if it is nonzero and its only
sub-representations are `0` and the whole representation. A sub-representation is a choice of
subspace `W v ⊆ ρ.obj v` at each vertex, stable under all arrow maps. -/
def IsIrreducible (ρ : QuiverRepresentation k Q) : Prop :=
  (∃ v, Nontrivial (ρ.obj v)) ∧
  ∀ (W : ∀ v, Submodule k (ρ.obj v)),
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, ρ.mapLinear e x ∈ W b) →
    (∀ v, W v = ⊥) ∨ (∀ v, W v = ⊤)

/-- **Irreducibles, existence.** The simple representation `S_i` is irreducible. -/
theorem simpleRep_isIrreducible [DecidableEq Q] (i : Q) :
    IsIrreducible (simpleRep (k := k) i) := by
  -- Off-vertices `v ≠ i` carry the zero space `Fin 0 → k`, which is a subsingleton.
  have hsub : ∀ v, v ≠ i → Subsingleton ((simpleRep (k := k) i).obj v) := by
    intro v hv
    show Subsingleton (Fin (if v = i then 1 else 0) → k)
    rw [if_neg hv]
    infer_instance
  refine ⟨⟨i, ?_⟩, ?_⟩
  · -- Nontriviality at vertex `i`: the fibre there is `Fin 1 → k`.
    have hobj : ((simpleRep (k := k) i).obj i) = (Fin 1 → k) := by
      show (Fin (if i = i then 1 else 0) → k) = (Fin 1 → k)
      rw [if_pos rfl]
    rw [hobj]
    have hne : (0 : Fin 1 → k) ≠ 1 := by
      intro h
      have := congrFun h 0
      simp only [Pi.zero_apply, Pi.one_apply] at this
      exact one_ne_zero this.symm
    exact ⟨0, 1, hne⟩
  · -- Any arrow-stable subspace family is all-`⊥` or all-`⊤`.
    intro W _
    -- The fibre at `i` is (defeq to) the 1-dimensional space `Fin 1 → k`.  Transport the
    -- submodule lattice there via the identity linear equivalence, where `Fin 1 → k` has the
    -- honest `Pi` instances that instance search can see through.
    let e : (simpleRep (k := k) i).obj i ≃ₗ[k] (Fin (if i = i then 1 else 0) → k) :=
      { toFun := fun x => x, invFun := fun x => x, left_inv := fun _ => rfl,
        right_inv := fun _ => rfl, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    haveI : IsSimpleOrder (Submodule k (Fin (if i = i then 1 else 0) → k)) :=
      is_simple_module_of_finrank_eq_one (K := k) (A := k)
        (by simp [Module.finrank_fin_fun])
    -- `W i` is `⊥` or `⊤` by transporting the simple-order dichotomy back along `e`.
    have hWi : W i = ⊥ ∨ W i = ⊤ := by
      have f := Submodule.orderIsoMapComap e
      rcases eq_bot_or_eq_top (f (W i)) with h | h
      · exact Or.inl (f.injective (by rw [h, map_bot]))
      · exact Or.inr (f.injective (by rw [h, map_top]))
    rcases hWi with hWi | hWi
    · left
      intro v
      rcases eq_or_ne v i with rfl | hv
      · exact hWi
      · have := hsub v hv
        rw [Submodule.eq_bot_iff]
        intro x _
        exact Subsingleton.elim x 0
    · right
      intro v
      rcases eq_or_ne v i with rfl | hv
      · exact hWi
      · have := hsub v hv
        rw [Submodule.eq_top_iff']
        intro x
        rw [Subsingleton.elim x (0 : (simpleRep (k := k) i).obj v)]
        exact Submodule.zero_mem _

/-- **Irreducibles, classification.** Every irreducible representation of `P_Q` is isomorphic
to a simple representation `S_i`. -/
theorem irreducible_isSimpleRep [DecidableEq Q] (ρ : QuiverRepresentation k Q)
    (hρ : IsIrreducible ρ) :
    ∃ i : Q, Nonempty (QuiverRepresentationEquiv k Q ρ (simpleRep i)) := by
  sorry

/-- **`Ext¹` between irreducibles.** `Ext¹(S_i, S_j) = 0` if and only if there are no arrows
`i → j`. (More precisely `dim Ext¹(S_i, S_j)` equals the number of arrows `i → j`.) -/
theorem ext1_simpleRep_vanishes_iff [DecidableEq Q] (i j : Q) :
    Ext1Vanishes (simpleRep (k := k) i) (simpleRep j) ↔ IsEmpty (i ⟶ j) := by
  sorry

/-- **Classification of 2-dimensional representations.** For a quiver without oriented cycles,
a representation `ρ` of total dimension `2` is either decomposable — necessarily a direct sum
`S_i ⊕ S_j` of two simples — or indecomposable, in which case there is a single arrow
`a : i → j` (with `i ≠ j`, since `Q` is acyclic) acting as an isomorphism, and `ρ` is the
representation supported on `a`. -/
theorem two_dim_classification [DecidableEq Q] [Fintype Q]
    (hQ : NoOrientedCycles Q) (ρ : QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (h2 : ∑ v, dimVec ρ v = 2) :
    (¬ ρ.IsIndecomposable)
      ∨ (∃ (i j : Q) (a : i ⟶ j), i ≠ j ∧ Function.Bijective (ρ.mapLinear a)) := by
  sorry

end Etingof.Problem3_9_3
