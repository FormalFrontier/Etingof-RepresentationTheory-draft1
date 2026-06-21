import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs

/-!
# Theorem (Problem 6.1.5): Finite Type iff Dynkin

A connected quiver Q is of finite type if and only if the corresponding unoriented
graph (i.e., with directions of arrows forgotten) is a Dynkin diagram
(see Theorem 6.5.2 / Gabriel's theorem).

## Mathlib correspondence

Gabriel's theorem is NOT in Mathlib. Quiver representations have basic support
(`Quiver`, `Representation`), but Gabriel's classification is absent.

## Formalization note

The statement uses `IsDynkinDiagram` (Definition 6.1.4) for the combinatorial
condition. `IsFiniteTypeQuiver` is defined in `FiniteTypeDefs.lean` as "finitely
many isomorphism classes of finite-dimensional indecomposable representations"
(the book's literal definition), quantified over all orientations and
algebraically closed fields.

## Status of the two directions

* **Backward** (Dynkin ⟹ finite type): proved here, sorry-free. Each
  finite-dimensional indecomposable has a dimension vector that is a positive
  root (Theorem 6.5.2b), positive roots are finite (Theorem 6.5.2a), each
  positive root is realized by a unique indecomposable up to isomorphism
  (Theorem 6.5.2c). The finite set of those realizers covers every
  indecomposable up to `AreIsomorphic`.
* **Forward** (finite type ⟹ Dynkin): the Tits-form positive-definiteness is the
  output of the orbit-counting chain of directive #4777
  (#4780 → #4782 → #4783 → #4784), to be wired into the positivity component by
  #4786. It is the single remaining `sorry` below.
-/

open Etingof in
/-- Gabriel's theorem: a connected quiver (given by its symmetric adjacency matrix)
is of finite type (finitely many indecomposable representations up to isomorphism)
if and only if its underlying unoriented graph is a Dynkin diagram.
(Etingof Problem 6.1.5 / Theorem 6.5.2) -/
theorem Etingof.Theorem_6_1_5 (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    Etingof.IsFiniteTypeQuiver n adj ↔ Etingof.IsDynkinDiagram n adj := by
  constructor
  · -- Forward: finite type → Dynkin diagram.
    -- The four combinatorial conditions hold by hypothesis; positive-definiteness
    -- of the Tits form is the orbit-counting output of directive #4777
    -- (#4780 → #4782 → #4783 → #4784), to be wired in by #4786.
    intro _hft
    refine ⟨hsymm, hdiag, h01, hconn, fun x hx => ?_⟩
    -- TODO(#4786): 0 < B(x, x) from finite type via the orbit-counting argument.
    sorry
  · -- Backward: Dynkin diagram → finite type.
    intro hDynkin k _inst_field _inst_algclosed Q _inst_ss hOrient
    classical
    -- The set of positive roots is finite (Theorem 6.5.2a).
    have hPR_fin : Set.Finite {α : Fin n → ℤ | Etingof.IsPositiveRoot n adj α} :=
      Etingof.Theorem_6_5_2a_finiteness hDynkin
    -- For each positive root, Theorem 6.5.2c gives an indecomposable representative.
    have hex : ∀ α : Fin n → ℤ, Etingof.IsPositiveRoot n adj α →
        ∃ ρ : @Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n) _ Q,
          (∀ v, Module.Free k (ρ.obj v)) ∧ (∀ v, Module.Finite k (ρ.obj v)) ∧
            ρ.IsIndecomposable ∧ ∀ v, α v = (Module.finrank k (ρ.obj v) : ℤ) := by
      intro α hα
      obtain ⟨ρ, hfree, hfin, hindec, hdim⟩ :=
        (Etingof.Theorem_6_5_2c_bijection hDynkin k hOrient α hα).1
      exact ⟨ρ, hfree, hfin, hindec, hdim⟩
    choose! g hg_free hg_fin hg_indec hg_dim using hex
    -- The chosen representatives, indexed by the (finite) set of positive roots; the
    -- representative set is the dependent image of the finite root set under `g`.
    refine ⟨_, hPR_fin.dependent_image (fun α hα => g α hα), ?_, ?_⟩
    · -- Each representative is indecomposable.
      rintro V ⟨α, hα, rfl⟩
      exact hg_indec α hα
    · -- Every finite-dimensional indecomposable is isomorphic to a representative.
      intro W hWfree hWfin hWindec
      haveI : ∀ v, Module.Free k (W.obj v) := hWfree
      haveI : ∀ v, Module.Finite k (W.obj v) := hWfin
      -- Dimension vector of W.
      set dW : Fin n → ℤ := fun v => (Module.finrank k (W.obj v) : ℤ) with hdW
      -- dW is a positive root (Theorem 6.5.2b).
      have hdW_root : Etingof.IsPositiveRoot n adj dW := by
        refine Etingof.Theorem_6_5_2b_dimvec_is_positive_root hDynkin dW
          (fun i => Int.natCast_nonneg _) ?_ ?_
        · -- dW ≠ 0: W is indecomposable, hence nontrivial at some vertex.
          obtain ⟨v, hv⟩ := hWindec.1
          intro heq
          have hv0 : Module.finrank k (W.obj v) = 0 := by
            have h := congr_fun heq v
            simpa [hdW] using h
          letI : AddCommGroup (W.obj v) := Etingof.addCommGroupOfRing (k := k)
          haveI : Subsingleton (W.obj v) := Module.finrank_zero_iff.mp hv0
          exact not_nontrivial (W.obj v) hv
        · -- B(dW, dW) = 2 (Tits form on an indecomposable dimension vector).
          exact Etingof.indecomposable_bilinearForm_eq_two hDynkin hOrient W hWindec
      -- The representative attached to dW.
      refine ⟨g dW hdW_root, ⟨dW, hdW_root, rfl⟩, ?_⟩
      -- W ≅ g dW by uniqueness (Theorem 6.5.2c), both indecomposable with dim vector dW.
      haveI : ∀ v, Module.Free k ((g dW hdW_root).obj v) := hg_free dW hdW_root
      haveI : ∀ v, Module.Finite k ((g dW hdW_root).obj v) := hg_fin dW hdW_root
      have huniq :=
        (Etingof.Theorem_6_5_2c_bijection hDynkin k hOrient dW hdW_root).2
          W (g dW hdW_root) hWindec (hg_indec dW hdW_root) (fun _ => rfl)
          (hg_dim dW hdW_root)
      obtain ⟨iso⟩ := huniq
      exact ⟨iso.equivAt, fun {a b} f => by ext x; simpa using iso.naturality f x⟩

/-- Corollary: A connected simple graph that is not a Dynkin diagram has infinite
representation type. (Non-circular version, proved as corollary of Theorem_6_1_5.) -/
theorem Etingof.non_Dynkin_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_dynkin : ¬ Etingof.IsDynkinDiagram n adj) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  intro hft
  exact h_not_dynkin ((Etingof.Theorem_6_1_5 n adj hsymm hdiag h01 hconn).mp hft)

/-- Corollary: A connected simple graph on n ≥ 1 vertices not isomorphic to any ADE type
has infinite representation type. -/
theorem Etingof.non_ADE_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_ade : ¬ ∃ t : Etingof.DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  apply Etingof.non_Dynkin_not_finite_type adj hsymm hdiag h01 hconn
  intro hD
  exact h_not_ade ((Etingof.Theorem_Dynkin_classification n adj hn).mp hD)
