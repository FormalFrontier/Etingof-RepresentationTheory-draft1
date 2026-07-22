import Mathlib
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_PosDef
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_OrbitSpace
import EtingofRepresentationTheory.Chapter6.OrientationDefs

/-!
# Problem 6.1.5, Step 3 wiring: the Tits matrix form is `2·(dim G − dim W)`

This file connects the matrix Tits form of Definition 6.1.4 to the orbit-side
dimension data of `Problem6_1_5_OrbitSpace.lean`, completing the arithmetic part of
**step 3** of the orbit-counting route to Gabriel's theorem (directive #4777).

`Problem6_1_5_PosDef.lean` already proves `titsForm_posDef_of_cone`: positivity of
the matrix form `xᵀ(2·I − adj)x` on the nonzero nonnegative integer cone (`hcone`)
upgrades to positive-definiteness on all nonzero integer vectors. What remains to
feed it is `hcone` itself, which this file produces from the *strict* dimension
bound `dim W(m) < dim G(m)` for nonzero `m`.

## The arithmetic identity

For a quiver `Q` orienting a simple graph `adj ∈ {0,1}` (`IsOrientationOf`), with
each `Hom` type a finite subsingleton, the arrow counts satisfy
`bᵢⱼ + bⱼᵢ = adjᵢⱼ` (`arrowCount_add_swap_eq_adj`). Plugging this into the
expansion of `titsBilinear_eq` collapses the directed double sum to twice the
undirected one, giving

`xᵀ(2·I − adj)x = 2·((Σᵢ mᵢ²) − Σᵢⱼ bᵢⱼ mᵢ mⱼ) = 2·(dim G(m) − dim W(m))`

(`titsForm_eq_two_mul_dim_diff`). Strict positivity of the left side is therefore
exactly `dim W(m) < dim G(m)`.

## What is left for S4 (#4786)

`hcone_of_strict_dim_bound` / `isDynkinDiagram_of_strict_dim_bound` reduce the
forward direction of `Theorem_6_1_5` to the single hypothesis
`dim W(m) < dim G(m)` for nonzero `m` — the `−1` strict refinement of the
non-strict `repSpace_finrank_le_repGroup_ambient_finrank` (`Problem6_1_5_DimBound`),
coming from the trivial action of the global scalars `k*`. That refinement is the
remaining genuinely-geometric step; everything here is sorry-free arithmetic.
-/

namespace Etingof

open Matrix

variable {n : ℕ} [Q : Quiver.{0} (Fin n)]
  [∀ i j : Fin n, Fintype (i ⟶ j)] [∀ i j : Fin n, Subsingleton (i ⟶ j)]

/-- For a quiver orienting the simple graph `adj` (`IsOrientationOf`), the directed
arrow counts add up to the undirected adjacency: `bᵢⱼ + bⱼᵢ = adjᵢⱼ`. Each edge
(`adjᵢⱼ = 1`) is oriented in exactly one direction (one arrow, the reverse empty),
and non-edges (`adjᵢⱼ = 0`) carry no arrows in either direction. -/
theorem arrowCount_add_swap_eq_adj (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hQ : Etingof.IsOrientationOf Q adj) (i j : Fin n) :
    (arrowCount i j : ℤ) + (arrowCount j i : ℤ) = adj i j := by
  classical
  have adj_symm : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congr_fun (congr_fun hsymm b) a
    simpa [Matrix.transpose_apply] using h
  -- `arrowCount` of a finite subsingleton arrow type is `1` if inhabited, else `0`.
  have card_eq : ∀ a b : Fin n, (arrowCount a b : ℤ) = if Nonempty (a ⟶ b) then 1 else 0 := by
    intro a b
    by_cases h : Nonempty (a ⟶ b)
    · have hc : arrowCount a b = 1 :=
        le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)
          (Fintype.card_pos_iff.mpr h)
      rw [hc, if_pos h]; norm_num
    · have hc : arrowCount a b = 0 := Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp h)
      rw [hc, if_neg h]; norm_num
  rw [card_eq i j, card_eq j i]
  rcases h01 i j with h0 | h1
  · -- non-edge: no arrows either way
    have hji : adj j i = 0 := by rw [adj_symm j i]; exact h0
    have e1 : ¬ Nonempty (i ⟶ j) :=
      not_nonempty_iff.mpr (hQ.1 i j (by rw [h0]; norm_num))
    have e2 : ¬ Nonempty (j ⟶ i) :=
      not_nonempty_iff.mpr (hQ.1 j i (by rw [hji]; norm_num))
    rw [if_neg e1, if_neg e2, h0]; norm_num
  · -- edge: exactly one orientation
    rcases hQ.2.1 i j h1 with hn | hn
    · have hnot : ¬ Nonempty (j ⟶ i) := fun hm => hQ.2.2 i j hn hm
      rw [if_pos hn, if_neg hnot, h1]; norm_num
    · have hnot : ¬ Nonempty (i ⟶ j) := fun hm => hQ.2.2 j i hn hm
      rw [if_neg hnot, if_pos hn, h1]; norm_num

/-- **The arithmetic bridge.** For any dimension vector `m`, the matrix Tits form of
Definition 6.1.4 equals twice the orbit-side dimension difference:

`xᵀ(2·I − adj)x = 2·((Σᵢ mᵢ²) − Σᵢⱼ bᵢⱼ mᵢ mⱼ) = 2·(dim G(m) − dim W(m))`,

where `xᵢ = (mᵢ : ℤ)`. The directed sum `Σᵢⱼ adjᵢⱼ mᵢ mⱼ` collapses to twice the
undirected arrow sum via `arrowCount_add_swap_eq_adj` and an `i ↔ j` reindexing. -/
theorem titsForm_eq_two_mul_dim_diff (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hQ : Etingof.IsOrientationOf Q adj) (m : Fin n → ℕ) :
    dotProduct (fun i => (m i : ℤ)) ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec
        (fun i => (m i : ℤ)))
      = 2 * ((∑ i, ((m i : ℤ)) ^ 2)
          - ∑ i, ∑ j, (arrowCount i j : ℤ) * ((m i : ℤ) * (m j : ℤ))) := by
  -- the `arrowCount j i` half reindexes to the `arrowCount i j` sum
  have hswap : (∑ i, ∑ j, (arrowCount j i : ℤ) * ((m i : ℤ) * (m j : ℤ)))
      = ∑ i, ∑ j, (arrowCount i j : ℤ) * ((m i : ℤ) * (m j : ℤ)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  -- the directed adjacency double sum is twice the undirected arrow sum
  have hadj_sum : (∑ i, ∑ j, adj i j * (m i : ℤ) * (m j : ℤ))
      = 2 * ∑ i, ∑ j, (arrowCount i j : ℤ) * ((m i : ℤ) * (m j : ℤ)) := by
    have hsplit : (∑ i, ∑ j, adj i j * (m i : ℤ) * (m j : ℤ))
        = (∑ i, ∑ j, (arrowCount i j : ℤ) * ((m i : ℤ) * (m j : ℤ)))
          + (∑ i, ∑ j, (arrowCount j i : ℤ) * ((m i : ℤ) * (m j : ℤ))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← arrowCount_add_swap_eq_adj adj hsymm h01 hQ i j]; ring
    rw [hsplit, hswap]; ring
  rw [titsBilinear_eq, hadj_sum]
  have hsq : (∑ i, (m i : ℤ) * (m i : ℤ)) = ∑ i, ((m i : ℤ)) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [hsq]; ring

/-- **Producing `hcone` from the strict dimension bound.** Given
`dim W(m) < dim G(m)` for every nonzero dimension vector `m` (the `−1` strict
refinement, in raw-sum form), the matrix Tits form is strictly positive on every
nonzero nonnegative integer vector — exactly the `hcone` hypothesis consumed by
`titsForm_posDef_of_cone`. -/
theorem hcone_of_strict_dim_bound (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hQ : Etingof.IsOrientationOf Q adj)
    (hstrict : ∀ m : Fin n → ℕ, m ≠ 0 →
        (∑ i, ∑ j, arrowCount i j * (m i * m j)) < ∑ i, (m i) ^ 2) :
    ∀ x : Fin n → ℤ, (∀ i, 0 ≤ x i) → x ≠ 0 →
        0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  intro x hx hne
  classical
  -- recover a nat dimension vector from the nonnegative integer vector
  set m : Fin n → ℕ := fun i => (x i).toNat with hm
  have hcast : ∀ i, ((m i : ℤ)) = x i := fun i => Int.toNat_of_nonneg (hx i)
  have hx_eq : x = fun i => (m i : ℤ) := funext fun i => (hcast i).symm
  have hmne : m ≠ 0 := by
    intro h
    apply hne
    funext i
    have hmi : (m i : ℤ) = 0 := by simp [congrFun h i]
    rw [← hcast i, hmi]; simp
  -- transport the strict nat inequality to ℤ
  have hltZ : (∑ i, ∑ j, (arrowCount i j : ℤ) * ((m i : ℤ) * (m j : ℤ)))
      < ∑ i, ((m i : ℤ)) ^ 2 := by
    have h : ((∑ i, ∑ j, arrowCount i j * (m i * m j) : ℕ) : ℤ)
        < ((∑ i, (m i) ^ 2 : ℕ) : ℤ) := by exact_mod_cast hstrict m hmne
    push_cast at h
    convert h using 2
  rw [hx_eq, titsForm_eq_two_mul_dim_diff adj hsymm h01 hQ m]
  have hX : 0 < (∑ i, ((m i : ℤ)) ^ 2)
      - ∑ i, ∑ j, (arrowCount i j : ℤ) * ((m i : ℤ) * (m j : ℤ)) := by linarith [hltZ]
  linarith [hX]

/-- **Forward direction of Gabriel's theorem from the strict dimension bound
(raw-sum form).** Given the graph-shape clauses and the strict orbit-dimension
bound `dim W(m) < dim G(m)` for nonzero `m`, the graph is a Dynkin diagram. This is
the interface consumed by the final wiring in S4 (#4786). -/
theorem isDynkinDiagram_of_strict_dim_bound (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hloop : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hQ : Etingof.IsOrientationOf Q adj)
    (hstrict : ∀ m : Fin n → ℕ, m ≠ 0 →
        (∑ i, ∑ j, arrowCount i j * (m i * m j)) < ∑ i, (m i) ^ 2) :
    Etingof.IsDynkinDiagram n adj :=
  isDynkinDiagram_of_cone adj hsymm hloop h01 hconn
    (hcone_of_strict_dim_bound adj hsymm h01 hQ hstrict)

set_option linter.unusedFintypeInType false in
/-- **Forward direction from the strict dimension bound (finrank form).** Same as
`isDynkinDiagram_of_strict_dim_bound`, but the hypothesis is phrased with the
`Module.finrank` quantities of `Problem6_1_5_OrbitSpace`/`Problem6_1_5_DimBound`:
`dim W(m) = finrank k (repSpace m) < finrank k (∏ᵢ Matrix (Fin mᵢ) (Fin mᵢ) k) =
dim G(m)`. This is the `−1` strict refinement of
`repSpace_finrank_le_repGroup_ambient_finrank` and is the directly-consumable hook
for S4 (#4786). -/
theorem isDynkinDiagram_of_strict_finrank (k : Type) [Field k]
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hloop : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hQ : Etingof.IsOrientationOf Q adj)
    (hstrict : ∀ m : Fin n → ℕ, m ≠ 0 →
        Module.finrank k (repSpace (k := k) m)
          < Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k)) :
    Etingof.IsDynkinDiagram n adj := by
  refine isDynkinDiagram_of_strict_dim_bound adj hsymm hloop h01 hconn hQ ?_
  intro m hmne
  have h := hstrict m hmne
  rwa [repSpace_finrank (k := k), repGroup_ambient_finrank (k := k)] at h

end Etingof
