import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_TitsBridge
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_DimBound
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_OrbitFiniteness

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
* **Forward** (finite type ⟹ Dynkin): proved here, sorry-free, via the
  orbit-counting chain of directive #4777. Picking the standard orientation `Q` of
  the graph and the algebraically closed field `ℂ`, finite type makes the group
  `G(m)` act on the representation space `W(m)` with finitely many orbits
  (`orbitRel_quotient_finite_of_isFiniteType`, #4780→#4798); a finite orbit set
  forces a dense orbit, an injective comorphism, and the strict dimension bound
  `dim W(m) < dim G(m)` (#4782→#4783→#4784, with the `−1` from the global scalars
  #4824); and that strict bound is exactly positive-definiteness of the Tits form
  (`isDynkinDiagram_of_strict_finrank`, #4785/#4816).
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
  · -- Forward: finite type → Dynkin diagram, via the orbit-counting chain (#4777).
    intro hft
    -- Fix the standard orientation `Q` of the graph and the field `ℂ`.
    letI Q : Quiver.{0} (Fin n) := Etingof.standardOrientation adj
    haveI hfin : ∀ a b : Fin n, Fintype (@Quiver.Hom (Fin n) Q a b) := by
      intro a b
      classical
      exact if h : Nonempty (@Quiver.Hom (Fin n) Q a b)
        then Fintype.ofSubsingleton h.some
        else @Fintype.ofIsEmpty _ (not_nonempty_iff.mp h)
    have hQ : Etingof.IsOrientationOf Q adj :=
      Etingof.standardOrientation_isOrientationOf adj hsymm hdiag
    -- Finite type ⟹ finitely many `G(m)`-orbits on `W(m)` over `ℂ`, for every `m`.
    haveI horb : ∀ m : Fin n → ℕ,
        Finite (MulAction.orbitRel.Quotient
          (Etingof.repGroup ℂ m) (Etingof.repSpace (k := ℂ) m)) := fun m =>
      Etingof.orbitRel_quotient_finite_of_isFiniteType (k := ℂ) adj hQ hft m
    -- The strict dimension bound `dim W(m) < dim G(m)` is positive-definiteness.
    exact Etingof.isDynkinDiagram_of_strict_finrank ℂ adj hsymm hdiag h01 hconn hQ
      (fun m hm =>
        Etingof.Problem6_1_5.repSpace_finrank_lt_repGroup_ambient_finrank (k := ℂ) m hm)
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
