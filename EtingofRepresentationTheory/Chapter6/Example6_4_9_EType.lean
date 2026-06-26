import EtingofRepresentationTheory.Chapter6.Example6_4_9_Shared
import EtingofRepresentationTheory.Chapter6.DynkinTypes

/-!
# Example 6.4.9: E-type Root Counts

Root counts for E₆, E₇, E₈ Dynkin types. The proofs use sum-of-squares (LDLᵀ)
decompositions of the Tits quadratic form to bound coordinates, then count the
bounded positive roots with honest kernel `decide`: directly for E₆ (4⁶), and
for E₇ (5⁷) and E₈ (7⁸) via a branch-decomposition convolution that deletes the
central degree-3 vertex and counts the two independent components separately.
-/

section ETypeRootCounts

open Matrix Finset

/-! ### E₆ -/

/-- SOS decomposition for the E₆ Tits form. -/
private lemma E6_sos (a b c d e f : ℤ) :
    6 * (2*(a^2+b^2+c^2+d^2+e^2+f^2) -
      2*(a*b+b*c+c*d+d*e+c*f)) =
    3*(2*a-b)^2 + 3*(2*e-d)^2 + 3*(2*f-c)^2 +
    (3*b-2*c)^2 + (3*d-2*c)^2 + c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
private lemma E6_qf (x : Fin 6 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) -
        Etingof.DynkinType.E6.adj).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+x 2*x 5) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    Etingof.DynkinType.adj, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

/-- All positive roots of E₆ have each coordinate < 4. -/
private lemma E6_bound (x : Fin 6 → ℤ)
    (hr : Etingof.IsRoot 6 Etingof.DynkinType.E6.adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 4 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+x 2*x 5) = 2 := by
    have := hr.2; rw [E6_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2
  set d := x 3; set e := x 4; set f := x 5
  have hs : 3*(2*a-b)^2 + 3*(2*e-d)^2 + 3*(2*f-c)^2 +
      (3*b-2*c)^2 + (3*d-2*c)^2 + c^2 = 12 := by
    nlinarith [E6_sos a b c d e f]
  have hc : c ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*d-2*c), sq_nonneg (c-4)]
  have hb : b ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (3*b-2*c-4)]
  have hd : d ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*b-2*c),
      sq_nonneg c, sq_nonneg (3*d-2*c-4)]
  have ha : a ≤ 3 := by
    nlinarith [sq_nonneg (2*e-d), sq_nonneg (2*f-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*a-b-3)]
  have he : e ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*e-d-3)]
  have hf : f ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*f-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega

-- Honest kernel `decide` over the 4^6 = 4096 candidate vectors (no native code).
-- The whnf reduction of the filtered Pi-fintype needs raised recursion/heartbeat limits.
set_option linter.style.maxHeartbeats false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma E6_count :
    (rootCountFinset 6 Etingof.DynkinType.E6.adj 4).card = 36 := by
  decide

/-- E₆ has 36 positive roots. (Etingof Example 6.4.9) -/
theorem Etingof.Example_6_4_9_E6 :
    (Etingof.positiveRoots 6 Etingof.DynkinType.E6.adj).Finite ∧
    Set.ncard
      (Etingof.positiveRoots 6 Etingof.DynkinType.E6.adj) = 36 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq E6_bound
  exact ⟨hfin, hcard ▸ E6_count⟩

/-! ### Branch-decomposition convolution machinery (E₇, E₈)

The naive `decide` enumerating all `B^n` candidate vectors is infeasible for E₇
(5⁷) and E₈ (7⁸). Deleting the unique degree-3 vertex (vertex 2) of an E-type
diagram splits it into independent path components; fixing the central
coordinate `x₂ = c` makes the Tits form additive over the two component groups.
The root count then convolves the two component value-distributions, computed
once each via a histogram fold over the (small) component spaces — a kernel
`decide` no larger than `B^4`. The following is a small histogram/convolution
toolkit used by both E₇ and E₈. -/

/-- Increment the count of `v` in an association-list histogram. -/
private def addOne : List (ℤ × ℕ) → ℤ → List (ℤ × ℕ)
  | [], v => [(v, 1)]
  | (w, n) :: t, v => if v = w then (w, n + 1) :: t else (w, n) :: addOne t v

/-- Look up the count of `v` in an association-list histogram (0 if absent). -/
private def lookupH : List (ℤ × ℕ) → ℤ → ℕ
  | [], _ => 0
  | (w, n) :: t, v => if v = w then n else lookupH t v

/-- Build a histogram of a list of integers by a single left fold. -/
private def histL (l : List ℤ) : List (ℤ × ℕ) := l.foldl addOne []

/-- Convolution count: number of pairs `(a ∈ l1, b ∈ l2)` with `a + b = T`,
using the precomputed histogram `h2` of `l2`. -/
private def pairCount (l1 : List ℤ) (h2 : List (ℤ × ℕ)) (T : ℤ) : ℕ :=
  (l1.map (fun a => lookupH h2 (T - a))).sum

private lemma lookup_addOne (h : List (ℤ × ℕ)) (v s : ℤ) :
    lookupH (addOne h v) s = lookupH h s + (if s = v then 1 else 0) := by
  induction h with
  | nil => simp only [addOne, lookupH]; split <;> rename_i hsv <;> simp_all
  | cons hd tl ih =>
    obtain ⟨w, n⟩ := hd; simp only [addOne]
    split <;> rename_i hvw
    · subst hvw; simp only [lookupH]; split <;> rename_i hsw <;> simp_all
    · simp only [lookupH]; split <;> rename_i hsw <;> simp_all <;> omega

private lemma lookupH_foldl (l : List ℤ) (acc : List (ℤ × ℕ)) (s : ℤ) :
    lookupH (l.foldl addOne acc) s = lookupH acc s + l.count s := by
  induction l generalizing acc with
  | nil => simp [lookupH]
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, lookup_addOne, List.count_cons]
    simp only [beq_iff_eq]; split_ifs <;> omega

/-- The histogram lookup recovers the true multiplicity. -/
private lemma lookupH_histL (l : List ℤ) (s : ℤ) : lookupH (histL l) s = l.count s := by
  rw [histL, lookupH_foldl]; simp [lookupH]

/-- The number of points of a fintype mapping to `s` under `Q` is the multiplicity
of `s` in the multiset of values. -/
private lemma count_preimage {α : Type*} [Fintype α] [DecidableEq α] (Q : α → ℤ) (s : ℤ) :
    (univ.filter (fun a => Q a = s)).card = Multiset.count s (univ.val.map Q) := by
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  exact congrArg _ (Multiset.filter_congr (fun a _ => by rw [eq_comm]))

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1000000 in
/-- Master convolution identity: the number of pairs `(g₁, g₂)` with
`Q₁ g₁ + Q₂ g₂ = T` equals the histogram convolution of the value-lists. The
hypotheses say `l1`, `l2` enumerate the values of `Q₁`, `Q₂` over the two
component spaces (both supplied by `rfl` thanks to `List.finRange` enumeration). -/
private lemma pair_count_bridge {G1 G2 : Type*} [Fintype G1] [Fintype G2]
    [DecidableEq G1] [DecidableEq G2]
    (Q1 : G1 → ℤ) (Q2 : G2 → ℤ) (l1 l2 : List ℤ) (T : ℤ)
    (h1 : (l1 : Multiset ℤ) = univ.val.map Q1) (h2 : (l2 : Multiset ℤ) = univ.val.map Q2) :
    (univ.filter (fun p : G1 × G2 => Q1 p.1 + Q2 p.2 = T)).card = pairCount l1 (histL l2) T := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have inner : ∀ g1 : G1, (∑ g2 : G2, if Q1 g1 + Q2 g2 = T then 1 else 0)
      = lookupH (histL l2) (T - Q1 g1) := by
    intro g1
    rw [lookupH_histL, ← Multiset.coe_count, h2, ← count_preimage, Finset.card_filter]
    refine Finset.sum_congr rfl (fun g2 _ => ?_)
    congr 1; simp only [eq_iff_iff]; constructor <;> intro h <;> linarith
  simp_rw [inner]
  rw [pairCount, ← Multiset.sum_coe, ← Multiset.map_coe, h1, Multiset.map_map]; rfl

/-! ### E₇ -/

/-- SOS decomposition for the E₇ Tits form. -/
private lemma E7_sos (a b c d e f g : ℤ) :
    12 * (2*(a^2+b^2+c^2+d^2+e^2+f^2+g^2) -
      2*(a*b+b*c+c*d+d*e+e*f+c*g)) =
    6*(2*a-b)^2 + 6*(2*f-e)^2 + 6*(2*g-c)^2 +
    2*(3*b-2*c)^2 + 2*(3*e-2*d)^2 +
    (4*d-3*c)^2 + c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
private lemma E7_qf (x : Fin 7 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        Etingof.DynkinType.E7.adj).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2+x 6^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
      x 4*x 5+x 2*x 6) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    Etingof.DynkinType.adj, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

/-- All positive roots of E₇ have each coordinate < 5. -/
private lemma E7_bound (x : Fin 7 → ℤ)
    (hr : Etingof.IsRoot 7 Etingof.DynkinType.E7.adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 5 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
        x 4*x 5+x 2*x 6) = 2 :=
    by have := hr.2; rw [E7_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2; set d := x 3
  set e := x 4; set f := x 5; set g := x 6
  have hs : 6*(2*a-b)^2 + 6*(2*f-e)^2 + 6*(2*g-c)^2 +
      2*(3*b-2*c)^2 + 2*(3*e-2*d)^2 +
      (4*d-3*c)^2 + c^2 = 24 := by
    nlinarith [E7_sos a b c d e f g]
  have : c ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*e-2*d), sq_nonneg (4*d-3*c),
      sq_nonneg (c-5)]
  have : d ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*e-2*d), sq_nonneg c,
      sq_nonneg (4*d-3*c-5)]
  have : b ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (3*b-2*c-4)]
  have : e ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (3*e-2*d-4)]
  have : a ≤ 4 := by
    nlinarith [sq_nonneg (2*f-e), sq_nonneg (2*g-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*a-b-3)]
  have : f ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*f-e-3)]
  have : g ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*g-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega

/-! #### Honest root count for E₇ via branch-decomposition

Deleting the degree-3 vertex 2 of the E₇ diagram splits it into independent
path components; fixing `x₂ = c` makes the Tits form additive over the groups
`g₁ = (x₀,x₁,x₆)` and `g₂ = (x₃,x₄,x₅)`. A card-preserving reindexing turns the
root count over `Fin 7 → Fin 5` (5⁷ vectors) into a sum, over the five values of
`c`, of histogram convolutions of the two `Fin 5 × Fin 5 × Fin 5` component
spaces (5³ each) — a kernel `decide` well within reach without native code. -/

/-- A component triple of coordinates. -/
private abbrev E7.T3 := Fin 5 × Fin 5 × Fin 5

/-- Assemble a vector from the central coordinate `c` and the two path
components `g₁ ↦ {0,1,6}`, `g₂ ↦ {3,4,5}` of the E₇ diagram. -/
private def asm7 (c : Fin 5) (g1 g2 : E7.T3) : Fin 7 → Fin 5 :=
  ![g1.1, g1.2.1, c, g2.1, g2.2.1, g2.2.2, g1.2.2]

/-- Disassemble a vector into its central coordinate and two components. -/
private def dis7 (v : Fin 7 → Fin 5) : Fin 5 × E7.T3 × E7.T3 :=
  (v 2, (v 0, v 1, v 6), (v 3, v 4, v 5))

set_option maxRecDepth 8000 in
private def E7equiv : (Fin 7 → Fin 5) ≃ Fin 5 × E7.T3 × E7.T3 where
  toFun := dis7
  invFun w := asm7 w.1 w.2.1 w.2.2
  left_inv v := by funext i; fin_cases i <;> simp [asm7, dis7]
  right_inv w := by
    obtain ⟨c, ⟨a, b, d⟩, ⟨e, f, g⟩⟩ := w
    simp only [asm7, dis7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, Fin.isValue]

/-- Tits form contribution of the `{0,1,6}` component (edges 0-1, 1-2, 2-6). -/
private def q1_7 (c : Fin 5) (g : E7.T3) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(c:ℤ) - 2*(c:ℤ)*(g.2.2:ℤ)

/-- Tits form contribution of the `{3,4,5}` component (edges 3-4, 4-5, 2-3). -/
private def q2_7 (c : Fin 5) (g : E7.T3) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(g.2.2:ℤ) - 2*(c:ℤ)*(g.1:ℤ)

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1000000 in
/-- The Tits form is additive: `q(x) = 2c² + q₁(c,g₁) + q₂(c,g₂)`. -/
private lemma E7_form (c : Fin 5) (g1 g2 : E7.T3) :
    dotProduct (fun i => ((asm7 c g1 g2) i : ℤ))
      ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        Etingof.DynkinType.E7.adj).mulVec (fun i => ((asm7 c g1 g2) i : ℤ)))
    = 2*(c:ℤ)^2 + q1_7 c g1 + q2_7 c g2 := by
  rw [show (2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - Etingof.DynkinType.E7.adj) = !![
    (2:ℤ),-1,0,0,0,0,0; -1,2,-1,0,0,0,0; 0,-1,2,-1,0,0,-1; 0,0,-1,2,-1,0,0;
    0,0,0,-1,2,-1,0; 0,0,0,0,-1,2,0; 0,0,-1,0,0,0,2] from by decide]
  simp only [asm7, q1_7, q2_7, dotProduct, mulVec, Fin.sum_univ_seven, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- The Tits quadratic form for E₇. -/
private def qf7 (x : Fin 7 → ℤ) : ℤ :=
  dotProduct x ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - Etingof.DynkinType.E7.adj).mulVec x)

set_option maxRecDepth 10000 in
/-- `rootCountFinset` as a prop-filter: a vector with `q = 2` is automatically nonzero. -/
private lemma E7_root_filter : rootCountFinset 7 Etingof.DynkinType.E7.adj 5 =
    (univ.filter (fun v : Fin 7 → Fin 5 => qf7 (fun i => ((v i : ℤ))) = 2)) := by
  rw [rootCountFinset]
  apply Finset.filter_congr
  intro v _
  simp only [qf7, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    intro h0; rw [h0] at h; simp [dotProduct] at h

/-- Enumerated values of the `{0,1,6}` component form over all of `Fin 5 ³`. -/
private def vals1_7 (c : Fin 5) : List ℤ :=
  (List.finRange 5).flatMap fun a => (List.finRange 5).flatMap fun b =>
    (List.finRange 5).map fun d => q1_7 c (a, b, d)

/-- Enumerated values of the `{3,4,5}` component form over all of `Fin 5 ³`. -/
private def vals2_7 (c : Fin 5) : List ℤ :=
  (List.finRange 5).flatMap fun a => (List.finRange 5).flatMap fun b =>
    (List.finRange 5).map fun d => q2_7 c (a, b, d)

set_option maxRecDepth 10000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 2000000 in
/-- Branch-decomposition identity: the E₇ root count splits, over the central
coordinate `c`, into a sum of per-`c` component-pair counts. -/
private lemma E7_count_eq :
    (rootCountFinset 7 Etingof.DynkinType.E7.adj 5).card =
    ∑ c : Fin 5, (univ.filter (fun p : E7.T3 × E7.T3 =>
      q1_7 c p.1 + q2_7 c p.2 = 2 - 2*(c:ℤ)^2)).card := by
  rw [E7_root_filter]
  rw [show (univ.filter (fun v : Fin 7 → Fin 5 => qf7 (fun i => ((v i : ℤ))) = 2)).card
      = (univ.filter (fun w : Fin 5 × E7.T3 × E7.T3 =>
          2*(w.1:ℤ)^2 + q1_7 w.1 w.2.1 + q2_7 w.1 w.2.2 = 2)).card from ?_]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    congr 1
    simp only [eq_iff_iff]
    constructor <;> intro h <;> linarith
  · apply Finset.card_bij' (fun v _ => E7equiv v) (fun w _ => E7equiv.symm w)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      have hform : qf7 (fun i => ((a i : ℤ))) = 2*((E7equiv a).1:ℤ)^2
          + q1_7 (E7equiv a).1 (E7equiv a).2.1 + q2_7 (E7equiv a).1 (E7equiv a).2.2 := by
        conv_lhs => rw [show a = E7equiv.symm (E7equiv a) from (E7equiv.symm_apply_apply a).symm]
        rw [qf7]; exact E7_form _ _ _
      rw [hform] at ha; exact ha
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      have hform : qf7 (fun i => (((E7equiv.symm b) i : ℤ))) = 2*(b.1:ℤ)^2
          + q1_7 b.1 b.2.1 + q2_7 b.1 b.2.2 := by
        rw [qf7]; obtain ⟨c, g1, g2⟩ := b; exact E7_form _ _ _
      rw [hform]; exact hb
    · intro a _; exact E7equiv.symm_apply_apply a
    · intro b _; exact E7equiv.apply_symm_apply b

set_option maxRecDepth 100000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 10000000 in
private lemma E7_count :
    (rootCountFinset 7 Etingof.DynkinType.E7.adj 5).card = 63 := by
  rw [E7_count_eq]
  have hb : ∀ c : Fin 5, (univ.filter (fun p : E7.T3 × E7.T3 =>
        q1_7 c p.1 + q2_7 c p.2 = 2 - 2*(c:ℤ)^2)).card
      = pairCount (vals1_7 c) (histL (vals2_7 c)) (2 - 2*(c:ℤ)^2) :=
    fun c => pair_count_bridge (q1_7 c) (q2_7 c) _ _ _ rfl rfl
  rw [Finset.sum_congr rfl (fun c _ => hb c)]
  decide

/-- E₇ has 63 positive roots. (Etingof Example 6.4.9) -/
theorem Etingof.Example_6_4_9_E7 :
    (Etingof.positiveRoots 7 Etingof.DynkinType.E7.adj).Finite ∧
    Set.ncard
      (Etingof.positiveRoots 7 Etingof.DynkinType.E7.adj) = 63 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq E7_bound
  exact ⟨hfin, hcard ▸ E7_count⟩

/-! ### E₈ -/

/-- SOS decomposition for the E₈ Tits form. -/
private lemma E8_sos (a b c d e f g h : ℤ) :
    60 * (2*(a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2) -
      2*(a*b+b*c+c*d+d*e+e*f+f*g+c*h)) =
    30*(2*a-b)^2 + 30*(2*g-f)^2 + 30*(2*h-c)^2 +
    10*(3*b-2*c)^2 + 10*(3*f-2*e)^2 +
    5*(4*e-3*d)^2 + 3*(5*d-4*c)^2 + 2*c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
private lemma E8_qf (x : Fin 8 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        Etingof.DynkinType.E8.adj).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2+x 7^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
      x 4*x 5+x 5*x 6+x 2*x 7) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    Etingof.DynkinType.adj, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

set_option linter.style.maxHeartbeats false in
-- Integrality argument (c=7 → d=6 → no int e) needs extra heartbeats
set_option maxHeartbeats 1600000 in
/-- All positive roots of E₈ have each coordinate < 7.
Tighter than the naive SOS bound (< 8) via an integrality argument:
c = 7 forces d = 6 (unique integer in range), then no integer e exists. -/
private lemma E8_bound (x : Fin 8 → ℤ)
    (hr : Etingof.IsRoot 8 Etingof.DynkinType.E8.adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 7 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2+x 7^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
        x 4*x 5+x 5*x 6+x 2*x 7) = 2 :=
    by have := hr.2; rw [E8_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2; set d := x 3
  set e := x 4; set f := x 5; set g := x 6; set h := x 7
  have ha0 : 0 ≤ a := hp 0; have hb0 : 0 ≤ b := hp 1
  have hc0 : 0 ≤ c := hp 2; have hd0 : 0 ≤ d := hp 3
  have he0 : 0 ≤ e := hp 4; have hf0 : 0 ≤ f := hp 5
  have hg0 : 0 ≤ g := hp 6; have hh0 : 0 ≤ h := hp 7
  have hs : 30*(2*a-b)^2 + 30*(2*g-f)^2 +
      30*(2*h-c)^2 + 10*(3*b-2*c)^2 +
      10*(3*f-2*e)^2 + 5*(4*e-3*d)^2 +
      3*(5*d-4*c)^2 + 2*c^2 = 120 := by
    nlinarith [E8_sos a b c d e f g h]
  -- Step 1: c ≤ 7 from SOS alone (2c² ≤ 120)
  have hc7 : c ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg (5*d-4*c), sq_nonneg (c-8)]
  -- Step 2: c ≤ 6 via integrality (c = 7 → d = 6 → no integer e)
  have hc6 : c ≤ 6 := by
    by_contra hc_ge7
    push_neg at hc_ge7
    have hc_eq : c = 7 := le_antisymm hc7 hc_ge7
    -- Isolate the d-dependent term: 3*(5d-28)² ≤ 22
    have h3sq : 3 * (5 * d - 28) ^ 2 ≤ 22 := by
      nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
        sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
        sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d)]
    -- Coarse bound on d for interval_cases
    have hd_le : d ≤ 8 := by nlinarith [sq_nonneg (5*d-28-9)]
    -- Check each integer d ∈ [0,8]: only d = 6 satisfies 3*(5d-28)² ≤ 22
    -- For d = 6: continue to check e
    -- For d ≠ 6: 3*(5d-28)² > 22, contradiction
    have hd_eq : d = 6 := by interval_cases d <;> omega
    -- Now isolate e-dependent term: 5*(4e-18)² ≤ 10
    have h5sq : 5 * (4 * e - 18) ^ 2 ≤ 10 := by
      nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
        sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
        sq_nonneg (3*f-2*e)]
    -- Coarse bound on e for interval_cases
    have he_le : e ≤ 7 := by nlinarith [sq_nonneg (4*e-18-6)]
    -- Check each integer e ∈ [0,7]: 4e ∈ {17,18,19} has no solution
    have : False := by interval_cases e <;> omega
    exact this
  -- Step 3: Chain bounds through the SOS decomposition using c ≤ 6
  have hd6 : d ≤ 6 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg c, sq_nonneg (5*d-4*c-7)]
  have he5 : e ≤ 5 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (4*e-3*d-5)]
  have hb5 : b ≤ 5 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*b-2*c-4)]
  have hf4 : f ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*f-2*e-4)]
  have ha3 : a ≤ 3 := by
    nlinarith [sq_nonneg (2*g-f), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*a-b-3)]
  have hg3 : g ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*g-f-3)]
  have hh4 : h ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*h-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega

/-! #### Honest root count for E₈ via branch-decomposition

The same construction as E₇: deleting vertex 2 splits E₈ into the components
`g₁ = (x₀,x₁,x₇)` and `g₂ = (x₃,x₄,x₅,x₆)`. The root count over `Fin 8 → Fin 7`
(7⁸ ≈ 5.76M vectors) becomes a sum, over the seven values of `c`, of histogram
convolutions of a `Fin 7 ³` space and a `Fin 7 ⁴` space — at most `7⁴ = 2401`
points per fold, which kernel `decide` handles without native code. -/

/-- The `{0,1,7}` component triple. -/
private abbrev E8.U3 := Fin 7 × Fin 7 × Fin 7

/-- The `{3,4,5,6}` component quadruple. -/
private abbrev E8.U4 := Fin 7 × Fin 7 × Fin 7 × Fin 7

/-- Assemble a vector from the central coordinate and components
`g₁ ↦ {0,1,7}`, `g₂ ↦ {3,4,5,6}` of the E₈ diagram. -/
private def asm8 (c : Fin 7) (g1 : E8.U3) (g2 : E8.U4) : Fin 8 → Fin 7 :=
  ![g1.1, g1.2.1, c, g2.1, g2.2.1, g2.2.2.1, g2.2.2.2, g1.2.2]

/-- Disassemble a vector into its central coordinate and two components. -/
private def dis8 (v : Fin 8 → Fin 7) : Fin 7 × E8.U3 × E8.U4 :=
  (v 2, (v 0, v 1, v 7), (v 3, v 4, v 5, v 6))

set_option maxRecDepth 8000 in
private def E8equiv : (Fin 8 → Fin 7) ≃ Fin 7 × E8.U3 × E8.U4 where
  toFun := dis8
  invFun w := asm8 w.1 w.2.1 w.2.2
  left_inv v := by funext i; fin_cases i <;> simp [asm8, dis8]
  right_inv w := by
    obtain ⟨c, ⟨a, b, d⟩, ⟨e, f, g, h⟩⟩ := w
    simp only [asm8, dis8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, Fin.isValue]

/-- Tits form contribution of the `{0,1,7}` component (edges 0-1, 1-2, 2-7). -/
private def q1_8 (c : Fin 7) (g : E8.U3) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(c:ℤ) - 2*(c:ℤ)*(g.2.2:ℤ)

/-- Tits form contribution of the `{3,4,5,6}` component (edges 3-4, 4-5, 5-6, 2-3). -/
private def q2_8 (c : Fin 7) (g : E8.U4) : ℤ :=
  2*(g.1:ℤ)^2 + 2*(g.2.1:ℤ)^2 + 2*(g.2.2.1:ℤ)^2 + 2*(g.2.2.2:ℤ)^2
    - 2*(g.1:ℤ)*(g.2.1:ℤ) - 2*(g.2.1:ℤ)*(g.2.2.1:ℤ) - 2*(g.2.2.1:ℤ)*(g.2.2.2:ℤ)
    - 2*(c:ℤ)*(g.1:ℤ)

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 2000000 in
/-- The Tits form is additive: `q(x) = 2c² + q₁(c,g₁) + q₂(c,g₂)`. -/
private lemma E8_form (c : Fin 7) (g1 : E8.U3) (g2 : E8.U4) :
    dotProduct (fun i => ((asm8 c g1 g2) i : ℤ))
      ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        Etingof.DynkinType.E8.adj).mulVec (fun i => ((asm8 c g1 g2) i : ℤ)))
    = 2*(c:ℤ)^2 + q1_8 c g1 + q2_8 c g2 := by
  rw [show (2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - Etingof.DynkinType.E8.adj) = !![
    (2:ℤ),-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,-1; 0,0,-1,2,-1,0,0,0;
    0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0; 0,0,0,0,0,-1,2,0; 0,0,-1,0,0,0,0,2]
    from by decide]
  simp only [asm8, q1_8, q2_8, dotProduct, mulVec, Fin.sum_univ_eight, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- The Tits quadratic form for E₈. -/
private def qf8 (x : Fin 8 → ℤ) : ℤ :=
  dotProduct x ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - Etingof.DynkinType.E8.adj).mulVec x)

set_option maxRecDepth 10000 in
/-- `rootCountFinset` as a prop-filter: a vector with `q = 2` is automatically nonzero. -/
private lemma E8_root_filter : rootCountFinset 8 Etingof.DynkinType.E8.adj 7 =
    (univ.filter (fun v : Fin 8 → Fin 7 => qf8 (fun i => ((v i : ℤ))) = 2)) := by
  rw [rootCountFinset]
  apply Finset.filter_congr
  intro v _
  simp only [qf8, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    intro h0; rw [h0] at h; simp [dotProduct] at h

/-- Enumerated values of the `{0,1,7}` component form over all of `Fin 7 ³`. -/
private def vals1_8 (c : Fin 7) : List ℤ :=
  (List.finRange 7).flatMap fun a => (List.finRange 7).flatMap fun b =>
    (List.finRange 7).map fun d => q1_8 c (a, b, d)

/-- Enumerated values of the `{3,4,5,6}` component form over all of `Fin 7 ⁴`. -/
private def vals2_8 (c : Fin 7) : List ℤ :=
  (List.finRange 7).flatMap fun a => (List.finRange 7).flatMap fun b =>
    (List.finRange 7).flatMap fun d => (List.finRange 7).map fun e => q2_8 c (a, b, d, e)

set_option maxRecDepth 10000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 4000000 in
/-- Branch-decomposition identity: the E₈ root count splits, over the central
coordinate `c`, into a sum of per-`c` component-pair counts. -/
private lemma E8_count_eq :
    (rootCountFinset 8 Etingof.DynkinType.E8.adj 7).card =
    ∑ c : Fin 7, (univ.filter (fun p : E8.U3 × E8.U4 =>
      q1_8 c p.1 + q2_8 c p.2 = 2 - 2*(c:ℤ)^2)).card := by
  rw [E8_root_filter]
  rw [show (univ.filter (fun v : Fin 8 → Fin 7 => qf8 (fun i => ((v i : ℤ))) = 2)).card
      = (univ.filter (fun w : Fin 7 × E8.U3 × E8.U4 =>
          2*(w.1:ℤ)^2 + q1_8 w.1 w.2.1 + q2_8 w.1 w.2.2 = 2)).card from ?_]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    congr 1
    simp only [eq_iff_iff]
    constructor <;> intro h <;> linarith
  · apply Finset.card_bij' (fun v _ => E8equiv v) (fun w _ => E8equiv.symm w)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      have hform : qf8 (fun i => ((a i : ℤ))) = 2*((E8equiv a).1:ℤ)^2
          + q1_8 (E8equiv a).1 (E8equiv a).2.1 + q2_8 (E8equiv a).1 (E8equiv a).2.2 := by
        conv_lhs => rw [show a = E8equiv.symm (E8equiv a) from (E8equiv.symm_apply_apply a).symm]
        rw [qf8]; exact E8_form _ _ _
      rw [hform] at ha; exact ha
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      have hform : qf8 (fun i => (((E8equiv.symm b) i : ℤ))) = 2*(b.1:ℤ)^2
          + q1_8 b.1 b.2.1 + q2_8 b.1 b.2.2 := by
        rw [qf8]; obtain ⟨c, g1, g2⟩ := b; exact E8_form _ _ _
      rw [hform]; exact hb
    · intro a _; exact E8equiv.symm_apply_apply a
    · intro b _; exact E8equiv.apply_symm_apply b

set_option maxRecDepth 100000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 30000000 in
private lemma E8_count :
    (rootCountFinset 8 Etingof.DynkinType.E8.adj 7).card = 120 := by
  rw [E8_count_eq]
  have hb : ∀ c : Fin 7, (univ.filter (fun p : E8.U3 × E8.U4 =>
        q1_8 c p.1 + q2_8 c p.2 = 2 - 2*(c:ℤ)^2)).card
      = pairCount (vals1_8 c) (histL (vals2_8 c)) (2 - 2*(c:ℤ)^2) :=
    fun c => pair_count_bridge (q1_8 c) (q2_8 c) _ _ _ rfl rfl
  rw [Finset.sum_congr rfl (fun c _ => hb c)]
  decide

/-- E₈ has 120 positive roots. (Etingof Example 6.4.9) -/
theorem Etingof.Example_6_4_9_E8 :
    (Etingof.positiveRoots 8 Etingof.DynkinType.E8.adj).Finite ∧
    Set.ncard
      (Etingof.positiveRoots 8 Etingof.DynkinType.E8.adj) =
      120 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq E8_bound
  exact ⟨hfin, hcard ▸ E8_count⟩

end ETypeRootCounts
