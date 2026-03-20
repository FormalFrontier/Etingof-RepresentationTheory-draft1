import Mathlib
import EtingofRepresentationTheory.Chapter6.DynkinTypes
import EtingofRepresentationTheory.Chapter6.DynkinForward

namespace Etingof

open Matrix Finset

private lemma dynkin_unique_degree_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (v w : Fin n)
    (hv : vertexDegree adj v = 3) (hw : vertexDegree adj w = 3) : v = w := by
  -- The null vector argument: path vertices get weight 2, extra neighbors get weight 1.
  -- B(x,x) = 2·Σxᵢ² - 2·Σ_{edges} xᵢxⱼ = 0 for this vector.
  -- Each path vertex i has 2xᵢ = Σⱼ aᵢⱼxⱼ (deg 3 vertices: 2+1+1=4=2·2,
  -- deg 2 interior: 2+2=4=2·2). Each extra neighbor i has 2xᵢ=2=Σⱼ aᵢⱼxⱼ (adj to v or w).
  sorry

/-- In a Dynkin diagram with a degree-3 branch vertex v, at least one of v's
    neighbors is a leaf (degree 1). Proof: if all 3 neighbors had degree ≥ 2,
    the graph would contain T_{2,2,2} as a subgraph, whose Cartan form has
    the null vector (3,2,2,2,1,1,1), contradicting positive definiteness. -/
private lemma branch_has_leaf_neighbor {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (v : Fin n) (hv : vertexDegree adj v = 3) :
    ∃ u, adj v u = 1 ∧ vertexDegree adj u = 1 := by
  obtain ⟨hsymm, hdiag, h01, _, hpos⟩ := hD
  -- By contradiction: if every neighbor of v has degree ≥ 2
  by_contra h; push_neg at h
  -- Every neighbor u of v has vertexDegree ≠ 1, so degree ≥ 2 (it's ≥ 1 since adj v u = 1)
  have h_nbr_deg : ∀ u, adj v u = 1 → 2 ≤ vertexDegree adj u := by
    intro u hu
    have h1 : 1 ≤ vertexDegree adj u := by
      change 1 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card
      exact Finset.one_le_card.mpr ⟨v, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hsymm.apply v u).symm ▸ hu⟩⟩
    have h_ne1 : vertexDegree adj u ≠ 1 := h u hu
    omega
  -- Extract 3 neighbors of v
  set N := Finset.univ.filter (fun j => adj v j = 1) with hN_def
  have hN_card : N.card = 3 := hv
  -- Get 3 distinct neighbors
  obtain ⟨n₁, n₂, n₃, hne12, hne13, hne23, hcover⟩ :=
    Finset.card_eq_three.mp hN_card
  have hn₁_adj : adj v n₁ = 1 := by
    have : n₁ ∈ N := hcover ▸ Finset.mem_insert_self _ _
    exact (Finset.mem_filter.mp this).2
  have hn₂_adj : adj v n₂ = 1 := by
    have : n₂ ∈ N := hcover ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self _ _))
    exact (Finset.mem_filter.mp this).2
  have hn₃_adj : adj v n₃ = 1 := by
    have : n₃ ∈ N := hcover ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))
    exact (Finset.mem_filter.mp this).2
  -- Each neighbor has degree ≥ 2, so has another neighbor besides v
  have get_second_nbr : ∀ u, adj v u = 1 → u ≠ v →
      ∃ w, adj u w = 1 ∧ w ≠ v ∧ w ≠ u := by
    intro u hu hu_ne
    have hdeg : 2 ≤ vertexDegree adj u := h_nbr_deg u hu
    -- u has ≥ 2 neighbors, one is v, so there's another
    have : 2 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card := hdeg
    have hv_mem : v ∈ Finset.univ.filter (fun j => adj u j = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsymm.apply v u).symm ▸ hu⟩
    -- After removing v, still ≥ 1 neighbor
    have h_erase := Finset.card_erase_of_mem hv_mem
    have : 1 ≤ ((Finset.univ.filter (fun j => adj u j = 1)).erase v).card := by omega
    obtain ⟨w, hw_mem⟩ := Finset.one_le_card.mp this
    have hw := Finset.mem_erase.mp hw_mem
    have hw_ne_u : w ≠ u := by
      intro heq; subst heq
      have := (Finset.mem_filter.mp hw.2).2
      rw [hdiag] at this; omega
    exact ⟨w, (Finset.mem_filter.mp hw.2).2, hw.1, hw_ne_u⟩
  -- v ≠ nᵢ for each i
  have hv_ne1 : n₁ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₁_adj; omega
  have hv_ne2 : n₂ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₂_adj; omega
  have hv_ne3 : n₃ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₃_adj; omega
  obtain ⟨a₁, ha₁_adj, ha₁_nv, ha₁_nn⟩ := get_second_nbr n₁ hn₁_adj hv_ne1
  obtain ⟨a₂, ha₂_adj, ha₂_nv, ha₂_nn⟩ := get_second_nbr n₂ hn₂_adj hv_ne2
  obtain ⟨a₃, ha₃_adj, ha₃_nv, ha₃_nn⟩ := get_second_nbr n₃ hn₃_adj hv_ne3
  -- Now embed T_{2,2,2} = {v, n₁, n₂, n₃, a₁, a₂, a₃} as a subgraph
  -- Null vector: v→3, nᵢ→2, aᵢ→1. B = 2(9+4+4+4+1+1+1) - 2(3·2·3+2·1·3) =
  -- 2·24 - 2(18+6) = 48 - 48 = 0.
  -- Actually: let's put weights directly on Fin n.
  -- x(v)=3, x(nᵢ)=2, x(aᵢ)=1, x(else)=0.
  -- Then for each nonzero vertex i, 2xᵢ = Σⱼ aᵢⱼ xⱼ:
  --   v: 2·3=6 = x(n₁)+x(n₂)+x(n₃) = 2+2+2 = 6 ✓
  --   nᵢ: 2·2=4 = x(v)+x(aᵢ) = 3+1 = 4 ✓ (needs nᵢ adj to only v and aᵢ among nonzero)
  --   aᵢ: 2·1=2 = x(nᵢ) = 2 ✓ (needs aᵢ adj to only nᵢ among nonzero)
  -- Wait, nᵢ might also be adjacent to other nonzero vertices (e.g., n₁ adj n₂).
  -- In a tree, nᵢ~nⱼ would create a triangle v-nᵢ-nⱼ-v, which is a cycle!
  -- So no nᵢ~nⱼ edges in a tree. Similarly aᵢ can't be adjacent to v or nⱼ (j≠i).
  -- But we haven't formally proved "no cycles" for these specific vertices.
  -- Instead, use a direct computation showing B(x,x) ≤ 0.
  set x : Fin n → ℤ := fun a =>
    if a = v then 3
    else if a = n₁ ∨ a = n₂ ∨ a = n₃ then 2
    else if a = a₁ ∨ a = a₂ ∨ a = a₃ then 1
    else 0 with hx_def
  have hx_ne : x ≠ 0 := by
    intro h; have := congr_fun h v; simp [x] at this
  -- Show B(x,x) ≤ 0 by decomposing the sum
  have hB_le : dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) ≤ 0 := by
    -- B(x,x) = Σᵢ xᵢ · (2xᵢ - Σⱼ aᵢⱼ·xⱼ)
    -- For each nonzero xᵢ, show 2xᵢ ≤ Σⱼ aᵢⱼ·xⱼ
    -- Since xᵢ ≥ 0 for all i, each term xᵢ·(2xᵢ - Σⱼ) ≤ 0
    -- B(x,x) = Σᵢ xᵢ · (2xᵢ - Σⱼ aᵢⱼ·xⱼ)
    -- For each i with xᵢ > 0: 2xᵢ ≤ Σⱼ aᵢⱼ·xⱼ, so the term is ≤ 0.
    -- For i with xᵢ = 0: term is 0. Hence B(x,x) ≤ 0.
    sorry
  linarith [hpos x hx_ne]

/-- A tree with a degree-3 vertex (branch) and all degrees ≤ 3 has exactly one such vertex,
    three arms of lengths p ≤ q ≤ r with n = p + q + r + 1, and is uniquely determined
    (up to graph isomorphism) by its arm lengths. Given the arm-length constraint from
    positive definiteness, the graph must be isomorphic to D_n, E₆, E₇, or E₈. -/
private lemma branch_classification {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n)
    (hbranch : ∃ i, vertexDegree adj i = 3) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  obtain ⟨v, hv⟩ := hbranch
  -- Step 1: Get a leaf neighbor of v
  obtain ⟨u, hu_adj, hu_deg⟩ := branch_has_leaf_neighbor hD v hv
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  have hu_ne : u ≠ v := by
    intro h; subst h; rw [hdiag] at hu_adj; omega
  -- u has exactly one neighbor, which is v
  have hu_unique : ∀ w, adj u w = 1 → w = v := by
    intro w hw
    by_contra hne_w
    have : 2 ≤ vertexDegree adj u := by
      change 2 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card
      have hv_mem : v ∈ Finset.univ.filter (fun j => adj u j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply u v ▸ hu_adj⟩
      have hw_mem : w ∈ Finset.univ.filter (fun j => adj u j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
      calc 2 = ({v, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne_w)]
        _ ≤ _ := Finset.card_le_card (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl; exact hv_mem; exact hw_mem)
    omega
  -- Step 2: Remove u to get reduced graph adj' on Fin (n-1)
  -- Need n ≥ 2 (v and u are distinct vertices)
  have hn2 : 2 ≤ n := by
    by_contra h; push_neg at h; interval_cases n
    · exact absurd (show v = u from Subsingleton.elim v u) (Ne.symm hu_ne)
  -- Write n = k + 1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  set adj' : Matrix (Fin k) (Fin k) ℤ :=
    fun i j => adj (u.succAbove i) (u.succAbove j) with hadj'_def
  -- adj' is a Dynkin diagram (same proof pattern as in path_walk_construction)
  have hD' : IsDynkinDiagram k adj' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Matrix.IsSymm.ext (fun i j => hsymm.apply _ _)
    · intro i; exact hdiag _
    · intro i j; exact h01 _ _
    · -- Connectivity: removing a leaf preserves connectivity
      let G : SimpleGraph (Fin (k + 1)) :=
        { Adj := fun i j => adj i j = 1
          symm := fun {i j} (h : adj i j = 1) => (hsymm.apply i j).trans h
          loopless := ⟨fun i (h : adj i i = 1) => by linarith [hdiag i]⟩ }
      haveI : DecidableRel G.Adj :=
        fun i j => show Decidable (adj i j = 1) from inferInstance
      have hG_conn : G.Connected := by
        constructor
        intro a b
        obtain ⟨path, hhead, hlast, hedges⟩ := hconn a b
        exact list_path_reachable G path a b hhead hlast (fun k hk => hedges k hk)
      have hG_deg : G.degree u = 1 := by
        unfold SimpleGraph.degree
        have heq : G.neighborFinset u = Finset.univ.filter (adj u · = 1) := by
          ext j; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
            Finset.mem_univ, true_and]; exact ⟨fun h => h, fun h => h⟩
        rw [heq]; unfold vertexDegree at hu_deg; convert hu_deg
      have hG' := hG_conn.induce_compl_singleton_of_degree_eq_one hG_deg
      intro a b
      have ha_ne : u.succAbove a ≠ u := Fin.succAbove_ne u a
      have hb_ne : u.succAbove b ≠ u := Fin.succAbove_ne u b
      have ha_mem : u.succAbove a ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
        Set.mem_compl_singleton_iff.mpr ha_ne
      have hb_mem : u.succAbove b ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
        Set.mem_compl_singleton_iff.mpr hb_ne
      obtain ⟨walk⟩ := hG'.preconnected ⟨u.succAbove a, ha_mem⟩ ⟨u.succAbove b, hb_mem⟩
      let toFink : ↥({u}ᶜ : Set (Fin (k + 1))) → Fin k :=
        fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq
          (Set.mem_compl_singleton_iff.mp hx)).choose
      have htoFink_spec : ∀ (x : ↥({u}ᶜ : Set (Fin (k + 1)))),
          u.succAbove (toFink x) = x.val :=
        fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq
          (Set.mem_compl_singleton_iff.mp hx)).choose_spec
      have htoFink_adj : ∀ (x y : ↥({u}ᶜ : Set (Fin (k + 1)))),
          (G.induce ({u}ᶜ : Set _)).Adj x y →
          adj' (toFink x) (toFink y) = 1 := by
        intro x y hadj_xy
        simp only [hadj'_def, SimpleGraph.induce_adj] at hadj_xy ⊢
        rw [htoFink_spec x, htoFink_spec y]; exact hadj_xy
      suffices h_walk : ∀ (a b : ↥({u}ᶜ : Set (Fin (k+1))))
          (w' : (G.induce ({u}ᶜ : Set _)).Walk a b),
        ∃ path : List (Fin k),
          path.head? = some (toFink a) ∧
          path.getLast? = some (toFink b) ∧
          ∀ m, (hm : m + 1 < path.length) →
            adj' (path.get ⟨m, by omega⟩) (path.get ⟨m + 1, hm⟩) = 1 by
        obtain ⟨path, hhead, hlast, hedges⟩ := h_walk _ _ walk
        refine ⟨path, ?_, ?_, hedges⟩
        · convert hhead using 2
          exact (Fin.succAbove_right_injective
            (htoFink_spec ⟨u.succAbove a, ha_mem⟩)).symm
        · convert hlast using 2
          exact (Fin.succAbove_right_injective
            (htoFink_spec ⟨u.succAbove b, hb_mem⟩)).symm
      intro a b w'
      induction w' with
      | nil =>
        exact ⟨[toFink _], rfl, rfl, fun m hm => absurd hm (by simp)⟩
      | @cons c d _ hadj_edge rest ih =>
        obtain ⟨path_rest, hhead_rest, hlast_rest, hedges_rest⟩ := ih
        refine ⟨toFink c :: path_rest, by simp, ?_, ?_⟩
        · cases path_rest with
          | nil => simp at hhead_rest hlast_rest ⊢
          | cons y ys => simp only [List.getLast?_cons_cons]; exact hlast_rest
        · intro m hm
          match m with
          | 0 =>
            simp only [List.get_eq_getElem, List.getElem_cons_zero,
              List.getElem_cons_succ]
            have h0 : 0 < path_rest.length := by
              simp only [List.length_cons] at hm; omega
            have hd_eq : path_rest[0] = toFink d := by
              cases path_rest with
              | nil => simp at h0
              | cons y ys =>
                simp only [List.head?, Option.some.injEq] at hhead_rest
                simp only [List.getElem_cons_zero]; exact hhead_rest
            rw [hd_eq]; exact htoFink_adj c d hadj_edge
          | m' + 1 =>
            simp only [List.get_eq_getElem, List.getElem_cons_succ]
            exact hedges_rest m' (by simp only [List.length_cons] at hm; omega)
    · -- Positive definiteness: principal submatrix of pos-def
      intro x hx
      set x' : Fin (k + 1) → ℤ := fun a =>
        if h : a = u then 0 else x (Fin.exists_succAbove_eq h).choose
      have hx'_u : x' u = 0 := by simp [x']
      have hx'_sa : ∀ i, x' (u.succAbove i) = x i := by
        intro i; simp only [x']
        rw [dif_neg (Fin.succAbove_ne u i)]; congr 1
        exact Fin.succAbove_right_injective
          (Fin.exists_succAbove_eq (Fin.succAbove_ne u i)).choose_spec
      have hx'_ne : x' ≠ 0 := by
        intro heq; apply hx; ext b
        have := congr_fun heq (u.succAbove b)
        rw [hx'_sa, Pi.zero_apply] at this; exact this
      have hB_eq : dotProduct x' ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x') =
          dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj').mulVec x) := by
        simp only [dotProduct, mulVec]
        conv_lhs => rw [Fin.sum_univ_succAbove _ u]
        simp only [hx'_u, zero_mul, zero_add]
        congr 1; ext i; rw [hx'_sa]; congr 1
        conv_lhs => rw [Fin.sum_univ_succAbove _ u]
        simp only [hx'_u, mul_zero, zero_add]
        congr 1; ext j; rw [hx'_sa]; congr 1
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
          Fin.succAbove_right_inj]
      linarith [hpos x' hx'_ne]
  -- Step 3: All degrees ≤ 2 in adj' (unique branch + leaf removal)
  have hpath' : ∀ i, vertexDegree adj' i ≤ 2 := by
    intro i
    -- In adj', vertex degrees are:
    -- v' (preimage of v): degree = 3 - 1 = 2 (lost edge to u)
    -- others: degree unchanged from adj, ≤ 2 (no other vertex has degree 3)
    unfold vertexDegree
    have h_image : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image u.succAbove)
        ⊆ Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx; exact hy
    have h_card := Finset.card_le_card h_image
    rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card
    -- Degree in adj ≤ 3 for all vertices
    have hD_full : IsDynkinDiagram (k + 1) adj := ⟨hsymm, hdiag, h01, hconn, hpos⟩
    have hdeg_le3 := dynkin_degree_le_three hD_full (u.succAbove i)
    unfold vertexDegree at hdeg_le3
    -- If degree in adj = 3, then u.succAbove i = v (unique branch)
    by_cases hdeg3 : (Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1)).card = 3
    · -- This vertex has degree 3 in adj, so it must be v
      have hvi : u.succAbove i = v :=
        dynkin_unique_degree_three hD_full (u.succAbove i) v (by unfold vertexDegree; exact hdeg3) hv
      -- In adj', v' loses the edge to u, so degree ≤ 2
      -- adj' neighbors of i are a subset of adj neighbors of v minus u
      have h_image2 : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image u.succAbove)
          ⊆ (Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1)).erase u := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        refine Finset.mem_erase.mpr ⟨Fin.succAbove_ne u y, ?_⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [← hvi]; exact hy
      have h_card2 := Finset.card_le_card h_image2
      rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card2
      have hu_mem : u ∈ Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_adj⟩
      rw [Finset.card_erase_of_mem hu_mem] at h_card2
      -- hv : vertexDegree adj v = 3, so #{j | adj v j = 1} = 3
      have hv3 : (Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1)).card = 3 := hv
      omega
    · -- Degree in adj ≤ 2
      have : (Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1)).card ≤ 2 := by
        omega
      linarith
  -- Step 4: Find an endpoint and apply path_walk_construction
  obtain ⟨v₀', hv₀'_deg⟩ := dynkin_has_endpoint hD' hk1 hpath'
  obtain ⟨σ', hσ'0, hσ'_fwd, hσ'_only⟩ :=
    path_walk_construction hD' hk1 hpath' v₀' hv₀'_deg
  -- Step 5: Find v's position in the path
  -- v ≠ u so v has a preimage v' under u.succAbove
  have hv_ne_u : v ≠ u := Ne.symm hu_ne
  obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq hv_ne_u
  -- v's position in the path ordering
  set bfin := σ'.symm v' with hbfin_def
  set b := bfin.val with hb_def
  -- b < k (index in Fin k)
  have hb_lt : b < k := bfin.isLt
  -- v is at position b: σ' maps position b to v'
  have hσ'_b : σ' bfin = v' := σ'.apply_symm_apply v'
  -- v has degree 2 in adj' (was 3 in adj, lost edge to u)
  -- This means v is an interior vertex of the path, so b ≥ 1 and b ≤ k-2
  have hv'_deg2 : vertexDegree adj' v' = 2 := by
    -- v' maps to v via succAbove. v had degree 3 in adj.
    -- In adj', v' lost the edge to u, so degree = 3 - 1 = 2.
    -- Upper bound from hpath': vertexDegree adj' v' ≤ 2
    -- Lower bound: v had 3 neighbors {u, w₁, w₂} in adj.
    -- w₁, w₂ ≠ u map to neighbors of v' in adj' via succAbove⁻¹.
    sorry
  have hb_pos : 0 < b := by
    by_contra h; push_neg at h; have hb0 : b = 0 := by omega
    -- If b = 0, σ'⁻¹(v') has index 0, so σ'(⟨0,_⟩) = v', meaning v' = v₀'
    have hv'_eq : v' = v₀' := by
      have hbf0 : bfin = ⟨0, by omega⟩ := Fin.ext hb0
      have h1 : σ' bfin = v' := hσ'_b
      rw [hbf0] at h1
      exact h1.symm.trans hσ'0
    linarith [hv'_eq ▸ hv₀'_deg]
  have hb_lt_k1 : b < k - 1 := by
    by_contra h; push_neg at h; have hbk : b = k - 1 := by omega
    -- If b = k-1, v' is the last vertex of the path → degree ≤ 1
    -- But v' has degree 2. This is a contradiction.
    -- The last vertex of a path has degree ≤ 1.
    sorry
  -- Set up arm lengths
  set p := 1 with hp_def
  set q := min b (k - 1 - b) with hq_def
  set r := max b (k - 1 - b) with hr_def
  have hp1 : 1 ≤ p := le_refl 1
  have hpq : p ≤ q := by
    simp only [p, q]; exact Nat.one_le_iff_ne_zero.mpr (by omega)
  have hqr : q ≤ r := by simp only [q, r]; omega
  have hn_eq : k + 1 = p + q + r + 1 := by
    simp only [p, q, r, min_def, max_def]
    split_ifs <;> omega
  -- Derive the reciprocal-sum constraint from positive definiteness
  -- If 1/(p+1) + 1/(q+1) + 1/(r+1) ≤ 1, the T_{p,q,r} tree has a null vector
  -- This gives the integer constraint for arm_length_solutions
  have hrecip : (q + 1) * (r + 1) + (p + 1) * (r + 1) + (p + 1) * (q + 1) >
                (p + 1) * (q + 1) * (r + 1) := by
    sorry -- Derived from positive definiteness of the Cartan form
  -- Apply arm_length_solutions
  rcases arm_length_solutions p q r hp1 hpq hqr hrecip with
    ⟨_, hq1⟩ | ⟨_, hq2, hr2⟩ | ⟨_, hq2, hr3⟩ | ⟨_, hq2, hr4⟩
  · -- Case (1, 1, r): D_{r+3} type, n = k+1 ≥ 4
    have h4_le : 4 ≤ k + 1 := by omega
    -- Construct σ extending σ' with u mapped to position k (= n-1)
    -- σ maps: 0..k-2 via the path (possibly reversed), k-1 and k to the two short arms
    -- The branch vertex v is at position k-2 in D_{k+1} adjacency
    -- This requires careful construction based on v's position b in the path
    sorry
  · -- Case (1, 2, 2): E₆, k+1 = 6
    -- Construct σ from σ' (path of 5 vertices) + u
    -- Branch at position 2 in E₆ adjacency
    sorry
  · -- Case (1, 2, 3): E₇, k+1 = 7
    sorry
  · -- Case (1, 2, 4): E₈, k+1 = 8
    sorry

/-- Forward direction of the Dynkin classification: any Dynkin diagram on n ≥ 1 vertices
    is graph-isomorphic to one of the standard types A_n, D_n, E₆, E₇, or E₈. -/
private lemma dynkin_classification_forward {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  -- Every vertex has degree ≤ 3
  have hdeg := fun i => dynkin_degree_le_three hD i
  -- Case split: is there a vertex of degree 3?
  by_cases hbranch : ∃ i, vertexDegree adj i = 3
  · -- Branch case: tree with one branch → D_n or E-type
    exact branch_classification hD hn hbranch
  · -- Path case: all degrees ≤ 2 → A_n
    push_neg at hbranch
    have hpath : ∀ i, vertexDegree adj i ≤ 2 := by
      intro i; have := hdeg i
      rcases Nat.eq_or_lt_of_le this with h | h
      · exact absurd h (hbranch i)
      · omega
    obtain ⟨σ, hσ⟩ := path_iso_An hD hn hpath
    exact ⟨.A n hn, σ, hσ⟩

/-- Classification of Dynkin diagrams: a connected graph with positive-definite Cartan form
is a Dynkin diagram if and only if it is isomorphic (as a graph) to one of the standard
types A_n, D_n, E₆, E₇, or E₈.

Note: The hypothesis `1 ≤ n` is necessary because `IsDynkinDiagram 0 adj` is vacuously true
(all conditions quantify over `Fin 0`, which is empty) but no `DynkinType` has rank 0.
Mathematically, the empty graph is not a Dynkin diagram.
(Etingof Theorem, Section 6.1) -/
theorem Theorem_Dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsDynkinDiagram n adj ↔
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  constructor
  · -- Forward direction: any Dynkin diagram is isomorphic to a standard type
    exact fun hD => dynkin_classification_forward hD hn
  · -- Backward direction: isomorphism to a standard type → IsDynkinDiagram
    rintro ⟨t, σ, hiso⟩
    exact isDynkinDiagram_of_graph_iso σ hiso (isDynkinDiagram_of_type t)

end Etingof
