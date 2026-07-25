import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Center

/-!
# The loop realization of the layer tower of `𝔤₄`

`EtingofRepresentationTheory/Chapter2/Problem2_16_3_Layers.lean` builds the two towers of layer
tops in `𝔤₄ = FreeLieAlgebra k (Fin 2) / (ad(x)²y, ad(y)⁵x)`,

* `evenTower k m`, the top of the even layer of `t`-degree `2m + 2`,
* `topOdd k m`, the top of the odd layer of `t`-degree `2m + 1`,

and the `LoopIdx`-indexed family `loopFam₄` of `ad(ȳ)`-strings on them. Nothing there evaluates
the loop realization `gbar : 𝔤₄ →ₗ[k] 𝔤𝔩₃(k[t])` on either tower, so nothing there can tell that
the towers are nonzero.

This file runs that computation. Both towers are `t`-homogeneous multiples of a *single* constant
matrix:

* `gbar_topOdd` — `gbar (topOdd k m) = 6ᵐ • (E₂₀ tᵐ⁺ᵐ⁺¹)`, i.e. `6ᵐ • emb (2m+1) (gone 4)`;
* `gbar_evenTower` — `gbar (evenTower k m) = 3 · 6ᵐ • emb (2m+2) (gzero 2)`.

The recursion `evenTower (m+1) = evenTop (oddTop (evenTower m))` is two brackets against the
fixed matrices `gbar a₁ = -E₁₀-E₂₁` and `gbar a₃ = 3(E₀₁+E₁₂)`, each of which moves the
`𝔤₀`-vector `gzero 2` to the `𝔤₁`-vector `gone 4` and back, multiplying by `2` and by `3`. That is
where the `6` comes from, and it is why `2 ≠ 0` and `3 ≠ 0` are exactly the hypotheses needed
(`5 ≠ 0` is not: the fifth Serre relation never enters).

Since `emb` is injective and `6ᵐ ≠ 0` in a field of characteristic `≠ 2, 3`, this gives the
nonvanishing statements the layer induction was missing: `topOdd_ne_zero`,
`evenTower_ne_zero`, `dY_one_evenTower_ne_zero`. The first of these discharges the hypothesis
`topOdd k (m+1) ≠ 0` of `topDefect_eq_zero_of_gDeg_le` in
`EtingofRepresentationTheory/Chapter2/Problem2_16_3_Bidegree.lean`.

The same induction, run along the whole `ad(ȳ)`-string rather than just at its top, gives the
full **fidelity** statement `gbar_loopFam₄`: `gbar` carries `loopFam₄ k I` to a nonzero multiple
of the graded basis vector `loopVec k (loopRev I)` of `𝔫₊(A₂⁽²⁾)`, where `loopRev` reverses the
`Fin`-index inside each degree (`ad(ȳ)` walks each string in the direction opposite to the one
`gone`/`gzero` are enumerated in). Reindexing `linearIndependent_loopVec` along the involution
`loopRev` therefore yields `linearIndependent_loopFam₄`.

Note what this does *not* do. `gbar` is a homomorphism, so it can witness that an element of
`𝔤₄` is nonzero, never that one is zero; `gbar_defect_eq_zero` already shows the loop model sends
every layer defect to `0`. So nothing here bears on the Gabber-Kac vanishing itself — it only
supplies the nonvanishing side.
-/

namespace Etingof.Problem2_16_3

attribute [local instance] LieRing.ofAssociativeRing

/-! ## The remaining entries of the constant-matrix bracket table

`EtingofRepresentationTheory/Chapter2/Problem2_16_3.lean` records the `ad(gzero 0)`-string on
`gone 4` and the brackets needed to show `range matHom₄ = 𝔫₊`. The tower recursion needs four
more entries: the two that turn `gzero 2` into `gone 4` and back, and the `ad(gzero 0)`-string
on `gzero 2` (which is the `ad(ȳ)`-string along an even layer). -/

section BracketTable

variable (k : Type*) [CommRing k]

/-- `⁅E₀₁+E₁₂, E₂₀⁆ = E₁₀-E₂₁`: bracketing the top `𝔤₁`-vector against `gone 1` lands on the top
`𝔤₀`-vector. This is `lie_gone4_gone1` with the arguments swapped, and it is the `evenTop` step
of the tower recursion. -/
theorem lie_gone1_gone4 : ⁅gone k 1, gone k 4⁆ = (1 : k) • gzero k 2 := by
  rw [← lie_skew, lie_gone4_gone1, ← neg_smul, neg_neg]

set_option linter.unnecessarySeqFocus false in
/-- `⁅E₁₀-E₂₁, E₁₀+E₂₁⁆ = -2E₂₀`: bracketing the top `𝔤₀`-vector against `gone 3` lands back on
the top `𝔤₁`-vector, with a factor `2`. This is the `oddTop` step of the tower recursion, and the
source of one half of the `6`. -/
theorem lie_gzero2_gone3 : ⁅gzero k 2, gone k 3⁆ = (-2 : k) • gone k 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gzero, gone, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-- `lie_gzero2_gone3` with the arguments in the order the `oddTop` step produces them. -/
theorem lie_gone3_gzero2 : ⁅gone k 3, gzero k 2⁆ = (2 : k) • gone k 4 := by
  rw [← lie_skew, lie_gzero2_gone3, ← neg_smul, neg_neg]

/-- `⁅E₀₁-E₁₂, E₁₀-E₂₁⁆ = E₀₀-E₂₂`: the first step of the `ad(ȳ)`-string along an even layer. -/
theorem lie_gzero0_gzero2 : ⁅gzero k 0, gzero k 2⁆ = (1 : k) • gzero k 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gzero, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]

/-- `⁅E₀₁-E₁₂, E₀₀-E₂₂⁆ = -(E₀₁-E₁₂)`: the second step of the `ad(ȳ)`-string along an even
layer. -/
theorem lie_gzero0_gzero1 : ⁅gzero k 0, gzero k 1⁆ = (-1 : k) • gzero k 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gzero, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]

/-- `⁅E₀₁-E₁₂, E₀₁-E₁₂⁆ = 0`: the `ad(ȳ)`-string along an even layer has length three. -/
theorem lie_gzero0_gzero0 : ⁅gzero k 0, gzero k 0⁆ = 0 := lie_self _

/-- `⁅E₀₁-E₁₂, E₀₂⁆ = 0`: the `ad(ȳ)`-string along an odd layer has length five, matching
`aElt_five_eq_zero`. -/
theorem lie_gzero0_gone0 : ⁅gzero k 0, gone k 0⁆ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gzero, gone, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply]

end BracketTable

/-! ## `gbar` on the generators of the layer recursion -/

section Generators

variable {k : Type*} [Field k]

/-- Brackets of `t`-homogeneous multiples of constant matrices. The whole tower computation is
this lemma applied repeatedly. -/
theorem lie_smul_emb_smul_emb {m n : ℕ} {c d : k} {A B : Matrix (Fin 3) (Fin 3) k} :
    ⁅c • emb k m A, d • emb k n B⁆ = (c * d) • emb k (m + n) ⁅A, B⁆ := by
  rw [lie_smul, smul_lie, emb_lie, smul_smul, ← map_smul, ← map_smul, mul_comm d c]

/-- `gbar` of `NY = ȳ` as a `t`-homogeneous multiple: `1 • (E₀₁-E₁₂) t⁰`. -/
theorem gbar_yb_eq : gbar k (yb k 4) = (1 : k) • emb k 0 (gzero k 0) := by
  rw [gbar_yb, NY_eq_emb, one_smul]

/-- `gbar` of `a₀ = x̄`: `1 • E₂₀ t`. -/
theorem gbar_aElt_zero : gbar k (aElt k 4 0) = (1 : k) • emb k 1 (gone k 4) := by
  rw [aElt_zero, gbar_xb, NX_eq_emb, one_smul]

/-- The `ad(ȳ)`-string on a `t`-homogeneous multiple of a constant matrix stays homogeneous:
`gbar` turns `dY k 1` into `ad(gzero 0)` on the constant matrix. -/
theorem gbar_dY_one_of {u : g k 4} {n : ℕ} {d : k} {A : Matrix (Fin 3) (Fin 3) k}
    (hu : gbar k u = d • emb k n A) :
    gbar k (dY k 1 u) = d • emb k n ⁅gzero k 0, A⁆ := by
  rw [dY_one, gbar_lie, hu, gbar_yb_eq, lie_smul_emb_smul_emb, one_mul, Nat.zero_add]

/-- The iterated form: `gbar (dY k j u)` is `ad(gzero 0)ʲ` applied to the constant matrix. -/
theorem gbar_dY_of {u : g k 4} {n : ℕ} {d : k} {A : Matrix (Fin 3) (Fin 3) k}
    (hu : gbar k u = d • emb k n A) (j : ℕ) :
    gbar k (dY k j u) = d • emb k n ((fun B => ⁅gzero k 0, B⁆)^[j] A) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [dY_succ, ← dY_one, gbar_dY_one_of ih, Function.iterate_succ_apply']

/-- **The `ad(ȳ)`-string of `𝔤₄` on `x̄` is the `ad(gzero 0)`-string of `𝔫₊` on `gone 4`**, placed
in `t`-degree `1`. Every value of `gbar` on the `aᵢ` is a specialization of this. -/
theorem gbar_aElt (j : ℕ) :
    gbar k (aElt k 4 j) = (1 : k) • emb k 1 ((fun B => ⁅gzero k 0, B⁆)^[j] (gone k 4)) := by
  have h := gbar_dY_of (gbar_aElt_zero (k := k)) j
  rwa [aElt_zero, dY_xb] at h

/-- `gbar a₁ = -(E₁₀+E₂₁) t`. -/
theorem gbar_aElt_one : gbar k (aElt k 4 1) = (-1 : k) • emb k 1 (gone k 3) := by
  rw [gbar_aElt, Function.iterate_one, lie_gzero0_gone4, map_smul, smul_smul, one_mul]

/-- `gbar a₃ = 3(E₀₁+E₁₂) t`. -/
theorem gbar_aElt_three : gbar k (aElt k 4 3) = (3 : k) • emb k 1 (gone k 1) := by
  have h : (fun B => ⁅gzero k 0, B⁆)^[3] (gone k 4) = (3 : k) • gone k 1 := by
    change ⁅gzero k 0, ⁅gzero k 0, ⁅gzero k 0, gone k 4⁆⁆⁆ = (3 : k) • gone k 1
    rw [lie_gzero0_gone4, lie_smul, lie_gzero0_gone3, lie_smul, lie_smul, lie_gzero0_gone2,
      smul_smul, smul_smul]
    norm_num
  rw [gbar_aElt, h, map_smul, smul_smul]
  norm_num

end Generators

/-! ## The closed forms along the tower -/

section Tower

variable {k : Type*} [Field k]

/-- The `oddTop` step in the loop model: it moves a multiple of the top `𝔤₀`-vector to twice that
multiple of the top `𝔤₁`-vector, one `t`-degree up. -/
theorem gbar_oddTop_of {c : g k 4} {n : ℕ} {d : k}
    (hc : gbar k c = d • emb k n (gzero k 2)) :
    gbar k (oddTop c) = (2 * d) • emb k (n + 1) (gone k 4) := by
  rw [oddTop, map_neg, gbar_lie, hc, gbar_aElt_one, lie_smul_emb_smul_emb, lie_gone3_gzero2,
    map_smul, smul_smul, Nat.add_comm 1 n, ← neg_smul]
  congr 1
  ring

/-- The `evenTop` step in the loop model: it moves a multiple of the top `𝔤₁`-vector to three
times that multiple of the top `𝔤₀`-vector, one `t`-degree up. -/
theorem gbar_evenTop_of {b : g k 4} {n : ℕ} {d : k}
    (hb : gbar k b = d • emb k n (gone k 4)) :
    gbar k (evenTop b) = (3 * d) • emb k (n + 1) (gzero k 2) := by
  rw [evenTop, gbar_lie, hb, gbar_aElt_three, lie_smul_emb_smul_emb, lie_gone1_gone4, map_smul,
    smul_smul, Nat.add_comm 1 n, mul_one]

/-- **The even tower in the loop model.** `evenTower k m` is the `3 · 6ᵐ`-multiple of the top
`𝔤₀`-vector `E₁₀-E₂₁` placed in `t`-degree `2m+2`. -/
theorem gbar_evenTower (m : ℕ) :
    gbar k (evenTower k m) = (3 * (6 : k) ^ m) • emb k (2 * m + 2) (gzero k 2) := by
  induction m with
  | zero =>
      rw [evenTower_zero, map_neg, gbar_lie, gbar_aElt_zero, gbar_aElt_three,
        lie_smul_emb_smul_emb, lie_gone4_gone1, map_smul, smul_smul, ← neg_smul]
      norm_num
  | succ m ih =>
      rw [evenTower_succ, gbar_evenTop_of (gbar_oddTop_of ih)]
      have hdeg : 2 * m + 2 + 1 + 1 = 2 * (m + 1) + 2 := by ring
      rw [hdeg]
      congr 1
      rw [pow_succ]
      ring

/-- **The odd tower in the loop model.** `topOdd k m` is the `6ᵐ`-multiple of the top
`𝔤₁`-vector `E₂₀` placed in `t`-degree `2m+1`. -/
theorem gbar_topOdd (m : ℕ) :
    gbar k (topOdd k m) = ((6 : k) ^ m) • emb k (2 * m + 1) (gone k 4) := by
  cases m with
  | zero => rw [topOdd_zero, gbar_xb, NX_eq_emb]; norm_num
  | succ m =>
      rw [topOdd_succ, gbar_oddTop_of (gbar_evenTower m)]
      have hdeg : 2 * m + 2 + 1 = 2 * (m + 1) + 1 := by ring
      rw [hdeg]
      congr 1
      rw [pow_succ]
      ring

/-- `gbar (D (evenTower k m))` is the `3 · 6ᵐ`-multiple of the middle `𝔤₀`-vector `E₀₀-E₂₂`, in
the same `t`-degree: `D` walks one step down the `ad(ȳ)`-string of the even layer. -/
theorem gbar_dY_one_evenTower (m : ℕ) :
    gbar k (dY k 1 (evenTower k m))
      = (3 * (6 : k) ^ m) • emb k (2 * m + 2) (gzero k 1) := by
  rw [gbar_dY_one_of (gbar_evenTower m), lie_gzero0_gzero2, map_smul, smul_smul, mul_one]

end Tower

/-! ## Nonvanishing -/

section NonVanishing

variable {k : Type*} [Field k]

/-- `emb` is injective: a `t`-homogeneous matrix vanishes only if its constant matrix does. -/
theorem emb_eq_zero_iff (n : ℕ) (A : Matrix (Fin 3) (Fin 3) k) :
    emb k n A = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have hz : ∀ a b, Polynomial.monomial n (A a b) = 0 := fun a b => by
    rw [← emb_apply k n A a b, h]; simp
  ext a b
  simpa using hz a b

theorem gone_ne_zero (i : Fin 5) : gone k i ≠ 0 := (linearIndependent_gone k).ne_zero i

theorem gzero_ne_zero (i : Fin 3) : gzero k i ≠ 0 := (linearIndependent_gzero k).ne_zero i

/-- `6 ≠ 0` in a field where `2 ≠ 0` and `3 ≠ 0`. -/
theorem six_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) : (6 : k) ≠ 0 := by
  have : (6 : k) = 2 * 3 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h3

/-- **The odd layer tops are nonzero.** Its image under `gbar` is `6ᵐ • E₂₀ t^{2m+1} ≠ 0`. -/
theorem topOdd_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (m : ℕ) : topOdd k m ≠ 0 := by
  intro h
  have hg : gbar k (topOdd k m) = 0 := by rw [h, map_zero]
  rw [gbar_topOdd] at hg
  rcases smul_eq_zero.1 hg with hc | hv
  · exact pow_ne_zero m (six_ne_zero h2 h3) hc
  · exact gone_ne_zero 4 ((emb_eq_zero_iff _ _).1 hv)

/-- **The even layer tops are nonzero.** Its image under `gbar` is
`3·6ᵐ • (E₁₀-E₂₁) t^{2m+2} ≠ 0`. -/
theorem evenTower_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (m : ℕ) : evenTower k m ≠ 0 := by
  intro h
  have hg : gbar k (evenTower k m) = 0 := by rw [h, map_zero]
  rw [gbar_evenTower] at hg
  rcases smul_eq_zero.1 hg with hc | hv
  · exact mul_ne_zero h3 (pow_ne_zero m (six_ne_zero h2 h3)) hc
  · exact gzero_ne_zero 2 ((emb_eq_zero_iff _ _).1 hv)

/-- **`D` does not kill the even layer tops.** This is the element that spans the imaginary
bidegree component of `𝔤₄` in `gDeg_le_span_singleton_of_topDefect_eq_zero`. -/
theorem dY_one_evenTower_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (m : ℕ) :
    dY k 1 (evenTower k m) ≠ 0 := by
  intro h
  have hg : gbar k (dY k 1 (evenTower k m)) = 0 := by rw [h, map_zero]
  rw [gbar_dY_one_evenTower] at hg
  rcases smul_eq_zero.1 hg with hc | hv
  · exact mul_ne_zero h3 (pow_ne_zero m (six_ne_zero h2 h3)) hc
  · exact gzero_ne_zero 1 ((emb_eq_zero_iff _ _).1 hv)

end NonVanishing

end Etingof.Problem2_16_3
