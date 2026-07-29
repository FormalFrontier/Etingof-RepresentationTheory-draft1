import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Problem 6.1.5, Step 3: orbit-dimension bound ⟹ Tits form positive definite

This step of Etingof Problem 6.1.5 shows:

> From `dim W(m) ≤ dim G(m)` for every dimension vector `m`, conclude that the
> Tits form `q(m) = Σ mᵢ² − Σ bᵢⱼ mᵢ mⱼ` is positive definite, that is, the
> graph is a Dynkin diagram (Definition 6.1.4).

## The matrix quadratic form is `2·q`

`IsDynkinDiagram` (Definition 6.1.4) packages positive-definiteness as

`∀ x : Fin n → ℤ, x ≠ 0 → 0 < xᵀ (2·I − adj) x`,

a quadratic form over `ℤ`. A direct expansion (`titsBilinear_eq` below) gives

`xᵀ (2·I − adj) x = 2 · (Σ xᵢ²) − Σᵢ Σⱼ adjᵢⱼ xᵢ xⱼ`,

which is exactly `2 · q(x)` for the undirected adjacency `adj` (recall
`Σᵢⱼ adjᵢⱼ xᵢxⱼ = 2 Σ_{i<j} adjᵢⱼ xᵢxⱼ` since `adj` is symmetric with no loops).
So positive-definiteness of this matrix form is exactly positivity of the Tits
form, and because the definition only quantifies over integer vectors, no
real-density argument is needed.

## What the orbit-dimension bound supplies

The strict bound `dim W(m) ≤ dim G(m) − 1` for nonzero `m`, coming from the
trivial action of the global scalars `k*`, is, in matrix terms, positivity of
`xᵀ (2·I − adj) x` on every nonzero vector with nonnegative entries. The work
here extends that positivity from the nonnegative cone to all nonzero integer
vectors via the `|·|` trick, using only `adjᵢⱼ ≥ 0`.

`titsForm_posDef_of_cone` is the main lemma; `isDynkinDiagram_of_cone`
combines it with the graph-shape clauses to give `IsDynkinDiagram`.
-/

namespace Etingof

open Matrix Finset

variable {n : ℕ}

/-- Expand any integer matrix quadratic form `vᵀ M v` as the double sum
`Σᵢ Σⱼ Mᵢⱼ vᵢ vⱼ`. -/
theorem dotProduct_mulVec_eq_sum (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    dotProduct v (M.mulVec v) = ∑ i, ∑ j, M i j * v i * v j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `(2·I)ᵢⱼ = 2` on the diagonal and `0` off it. -/
private theorem two_smul_one_apply (i j : Fin n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = if i = j then (2 : ℤ) else 0 := by
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne h, h]

/-- The Tits bilinear form expanded: `xᵀ (2·I − adj) x = 2·(Σ xᵢ²) − Σᵢ Σⱼ adjᵢⱼ xᵢ xⱼ`.
This identifies the matrix form of Definition 6.1.4 with twice the Tits form, and
exposes the `dim G = Σ xᵢ²` / `dim W = ½ Σᵢⱼ adjᵢⱼ xᵢxⱼ` quantities for S4. -/
theorem titsBilinear_eq (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)
      = 2 * (∑ i, x i * x i) - ∑ i, ∑ j, adj i j * x i * x j := by
  rw [dotProduct_mulVec_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- per row `i`: `Σⱼ (2·I − adj)ᵢⱼ xᵢ xⱼ = 2·xᵢ² − Σⱼ adjᵢⱼ xᵢ xⱼ`
  have hsplit : ∀ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * x i * x j
      = (if i = j then (2 : ℤ) * (x i * x i) else 0) - adj i j * x i * x j := by
    intro j
    rw [Matrix.sub_apply, two_smul_one_apply, sub_mul, sub_mul]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq Finset.univ i (fun _ => (2 : ℤ) * (x i * x i))]
  simp

/-- **Step 3 of Problem 6.1.5 (core).** From positivity of the Tits matrix form
`xᵀ (2·I − adj) x` on every nonzero nonnegative integer vector (the
orbit-dimension bound `dim W ≤ dim G − 1`), the form is positive on every nonzero
integer vector. Only `adjᵢⱼ ≥ 0` is used: the `|·|`-trick replaces each `x` by
`|x|`, which can only decrease the form (`adjᵢⱼ (|xᵢ||xⱼ| − xᵢxⱼ) ≥ 0`). -/
theorem titsForm_posDef_of_cone (adj : Matrix (Fin n) (Fin n) ℤ)
    (hnonneg : ∀ i j, 0 ≤ adj i j)
    (hcone : ∀ m : Fin n → ℤ, (∀ i, 0 ≤ m i) → m ≠ 0 →
        0 < dotProduct m ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec m)) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
        0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  intro x hx
  set M := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hMdef
  -- replace `x` by its componentwise absolute value
  set ax : Fin n → ℤ := fun i => |x i| with haxdef
  have hax_nonneg : ∀ i, 0 ≤ ax i := fun i => abs_nonneg _
  have hax_ne : ax ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi : |x i| = 0 := by have := congrFun h i; simpa [haxdef] using this
    simpa using abs_eq_zero.mp hi
  have hpos : 0 < dotProduct ax (M.mulVec ax) := hcone ax hax_nonneg hax_ne
  -- the form can only decrease when each entry is replaced by its absolute value
  have hterm : ∀ i j, M i j * ax i * ax j ≤ M i j * x i * x j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have he : M i i * ax i * ax i = M i i * x i * x i := by
        rw [mul_assoc, mul_assoc]
        congr 1
        simp only [haxdef, abs_mul_abs_self]
      exact le_of_eq he
    · have hM : M i j = - adj i j := by
        rw [hMdef, Matrix.sub_apply, two_smul_one_apply, if_neg hij, zero_sub]
      rw [hM]
      have hxx : x i * x j ≤ |x i| * |x j| := by
        calc x i * x j ≤ |x i * x j| := le_abs_self _
          _ = |x i| * |x j| := abs_mul _ _
      have hmul := mul_le_mul_of_nonneg_left hxx (hnonneg i j)
      have e1 : -adj i j * ax i * ax j = -(adj i j * (|x i| * |x j|)) := by
        simp [haxdef]; ring
      have e2 : -adj i j * x i * x j = -(adj i j * (x i * x j)) := by ring
      rw [e1, e2]
      linarith [hmul]
  have hle : dotProduct ax (M.mulVec ax) ≤ dotProduct x (M.mulVec x) := by
    rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.sum_le_sum fun j _ => hterm i j
  linarith [hpos, hle]

/-- **Step 3 of Problem 6.1.5 (packaged).** Given the graph-shape clauses and the
orbit-dimension bound (positivity of the Tits matrix form on the nonzero
nonnegative cone), the graph is a Dynkin diagram. -/
theorem isDynkinDiagram_of_cone (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hloop : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hcone : ∀ m : Fin n → ℤ, (∀ i, 0 ≤ m i) → m ≠ 0 →
        0 < dotProduct m ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec m)) :
    Etingof.IsDynkinDiagram n adj := by
  have hnonneg : ∀ i j, 0 ≤ adj i j := by
    intro i j
    rcases h01 i j with h | h <;> omega
  exact ⟨hsymm, hloop, h01, hconn, titsForm_posDef_of_cone adj hnonneg hcone⟩

/-- **Problem 6.1.5(a), denominator-clearing step.** Positivity of the integral
Cartan/Tits form implies positivity of its scalar extension to every nonzero
rational vector.  This is the source hint "it suffices to check the result for
integers," made explicit. -/
theorem titsForm_rat_pos_of_int_pos (adj : Matrix (Fin n) (Fin n) ℤ)
    (hInt : ∀ y : Fin n → ℤ, y ≠ 0 →
      0 < dotProduct y ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec y)) :
    ∀ x : Fin n → ℚ, x ≠ 0 →
      0 < dotProduct x
        (((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map
          (Int.castRingHom ℚ)).mulVec x) := by
  intro x hx
  let d : ℕ := ∏ i, (x i).den
  let y : Fin n → ℤ := fun i => (x i).num * (d / (x i).den : ℕ)
  have hd : 0 < d := Finset.prod_pos fun i _ => (x i).den_pos
  have hscale : ∀ i, (d : ℚ) * x i = y i := by
    intro i
    have hdiv : (x i).den ∣ d := by
      exact Finset.dvd_prod_of_mem (fun j => (x j).den) (Finset.mem_univ i)
    have hden : ((x i).den : ℚ) ≠ 0 := by exact_mod_cast (x i).den_nz
    rw [← (x i).num_div_den]
    simp only [y, Int.cast_mul, Int.cast_natCast]
    rw [show ((d / (x i).den : ℕ) : ℚ) = (d : ℚ) / ((x i).den : ℚ) from
      Nat.cast_div hdiv hden]
    field_simp
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    funext i
    have hi := hscale i
    rw [hy] at hi
    simp only [Pi.zero_apply, Int.cast_zero] at hi
    exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast hd.ne')
  have hpos := hInt y hy
  have hcast :
      ((dotProduct y
          ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec y) : ℤ) : ℚ) =
        dotProduct (fun i => (y i : ℚ))
          (((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map (Int.castRingHom ℚ)).mulVec
            (fun i => (y i : ℚ))) := by
    simp [dotProduct, Matrix.mulVec]
  have hscaled :
      dotProduct (fun i => (y i : ℚ))
          (((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map (Int.castRingHom ℚ)).mulVec
            (fun i => (y i : ℚ))) =
        (d : ℚ) ^ 2 * dotProduct x
          (((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map
            (Int.castRingHom ℚ)).mulVec x) := by
    have hfun : (fun i => (y i : ℚ)) = (d : ℚ) • x := by
      funext i
      simpa [Pi.smul_apply, smul_eq_mul] using (hscale i).symm
    rw [hfun]
    simp [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, pow_two]
    ring
  have hposQ : 0 <
      dotProduct (fun i => (y i : ℚ))
        (((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map (Int.castRingHom ℚ)).mulVec
          (fun i => (y i : ℚ))) := by
    rw [← hcast]
    exact_mod_cast hpos
  rw [hscaled] at hposQ
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  nlinarith [sq_pos_of_pos hdQ]

/-- **Problem 6.1.5(b).** A symmetric integral Cartan/Tits matrix that is
positive on nonzero rational vectors is positive definite over `ℝ`.

Density first gives positive semidefiniteness over `ℝ`.  Rational strict
positivity makes the determinant nonzero, and hence upgrades the real matrix to
positive definite. -/
theorem titsForm_real_posDef_of_rat_pos (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hRat : ∀ x : Fin n → ℚ, x ≠ 0 →
      0 < dotProduct x
        (((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map
          (Int.castRingHom ℚ)).mulVec x)) :
    ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map
      (Int.castRingHom ℝ)).PosDef := by
  let MZ : Matrix (Fin n) (Fin n) ℤ := 2 • 1 - adj
  let MQ : Matrix (Fin n) (Fin n) ℚ := MZ.map (Int.castRingHom ℚ)
  let MR : Matrix (Fin n) (Fin n) ℝ := MZ.map (Int.castRingHom ℝ)
  have hMZsymm : MZ.IsSymm := (Matrix.isSymm_one.smul 2).sub hsymm
  have hMQherm : MQ.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have hij := congr_fun (congr_fun hMZsymm i) j
    simpa [MQ, Matrix.transpose_apply] using hij
  have hMRherm : MR.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have hij := congr_fun (congr_fun hMZsymm i) j
    simpa [MR, Matrix.transpose_apply] using hij
  have hMQpos : MQ.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos hMQherm <| by
    intro x hx
    exact hRat x hx
  have hdetQ : MQ.det ≠ 0 := by
    exact ((Matrix.isUnit_iff_isUnit_det MQ).mp hMQpos.isUnit).ne_zero
  have hdetZ : MZ.det ≠ 0 := by
    intro hz
    apply hdetQ
    change (MZ.map (Int.castRingHom ℚ)).det = 0
    have hmap : ((MZ.det : ℤ) : ℚ) = (MZ.map (Int.castRingHom ℚ)).det := by
      simpa using (Int.castRingHom ℚ).map_det MZ
    rw [← hmap]
    simp [hz]
  have hdetR : MR.det ≠ 0 := by
    change (MZ.map (Int.castRingHom ℝ)).det ≠ 0
    have hmap : ((MZ.det : ℤ) : ℝ) = (MZ.map (Int.castRingHom ℝ)).det := by
      simpa using (Int.castRingHom ℝ).map_det MZ
    rw [← hmap]
    exact_mod_cast hdetZ
  have hMRsem : MR.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hMRherm <| by
    intro x
    let q : (Fin n → ℝ) → ℝ := fun z => dotProduct z (MR.mulVec z)
    have hq : Continuous q := by
      dsimp [q]
      fun_prop
    refine (DenseRange.piMap (fun _ : Fin n => Rat.denseRange_cast)).induction_on x
      (isClosed_Ici.preimage hq) ?_
    intro z
    change 0 ≤ q (Pi.map (fun _ : Fin n => Rat.cast) z)
    by_cases hz : z = 0
    · subst z
      have hzero : Pi.map (fun _ : Fin n => Rat.cast) (0 : Fin n → ℚ) =
          (0 : Fin n → ℝ) := by
        ext i
        simp [Pi.map_apply]
      rw [hzero]
      simp [q]
    · have hp := (hRat z hz).le
      have hpR : (0 : ℝ) ≤
          ((dotProduct z (MQ.mulVec z) : ℚ) : ℝ) := by
        exact_mod_cast hp
      rw [show q (Pi.map (fun _ : Fin n => Rat.cast) z) =
          ((dotProduct z (MQ.mulVec z) : ℚ) : ℝ) by
        simp [q, MR, MQ, MZ, dotProduct, Matrix.mulVec, Pi.map_apply]]
      exact hpR
  exact hMRsem.posDef_iff_det_ne_zero.mpr hdetR

end Etingof
