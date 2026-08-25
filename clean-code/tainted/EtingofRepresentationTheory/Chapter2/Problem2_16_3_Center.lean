import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Layers


/-!
# Problem 2.16.3(b): the centre of `𝔤₄` versus the twisted loop realization

`Problem2_16_3_Layers.lean` reduces the whole layer induction for `𝔤₄` to a single vanishing:
the *defect* `EvenLayer.defect c = ⁅a₄, oddTop c⁆ - 2 D (evenTop (oddTop c))` is a central element
of `𝔤₄` (`EvenLayer.central_defect`), and the induction closes exactly when it is `0`.

This file settles what the twisted `A₂⁽²⁾` loop realization
`matHom₄ : FreeLieAlgebra k (Fin 2) → 𝔤𝔩₃(k[t])` can say about that question, and the answer is a
sharp *negative*: the loop model kills the entire centre of `𝔤₄`, so it can never exhibit a defect
as nonzero, and it can only prove a defect zero by way of its own injectivity.

The two matrix facts are:

* `centralizer_NX_NY_eq_scalar` — over any commutative ring, a polynomial matrix commuting with
  both generator images `NX = E₂₀·t` and `NY = E₀₁ - E₁₂` is a scalar matrix. This is an entry
  chase: `⁅P, NX⁆ = 0` forces `P₀₂ = P₁₂ = P₀₁ = 0` and `P₂₂ = P₀₀`, and `⁅P, NY⁆ = 0` forces
  `P₁₀ = P₂₀ = P₂₁ = 0` and `P₀₀ = P₁₁`.
* `eq_zero_of_mem_loopPos_of_central` — hence the centre of `𝔫₊ = loopPos` is trivial as soon as
  `3 ≠ 0`: the only traceless scalar matrix is `0`, because `trace (a • 1) = 3a`. The hypothesis is
  sharp — in characteristic `3` the scalar matrices `a·1` with `a` an odd polynomial do lie in
  `loopPos` and are central, the same degeneration that collapses `range matHom₄` to four
  dimensions.

Consequences for the layer induction:

* `gbar_eq_zero_of_central` — every central element of `𝔤₄` is killed by `gbar`, the factored loop
  map. In particular `gbar_defect_eq_zero`: the defect maps to `0`, so no computation inside the
  loop model can ever detect it. Any proof of `EvenLayer.defect c = 0` must therefore use an input
  strictly beyond `matHom₄`.
* `oddLayer_evenTower_of_gbar_injective` — conversely, injectivity of `gbar` closes the whole layer
  induction. This is the precise sense in which the remaining gap in Problem 2.16.3(b) is the
  Gabber–Kac statement that the Serre relators generate *all* relations of `𝔫₊(A₂⁽²⁾)`.
-/

namespace Etingof.Problem2_16_3

open Polynomial

attribute [local instance] LieRing.ofAssociativeRing

/-! ## The centralizer of the two generator images in `𝔤𝔩₃(k[t])` -/

section Centralizer

variable {k : Type*} [CommRing k]

/-- Entries of the generator image `NX = E₂₀·t`. -/
theorem NX_apply (i j : Fin 3) :
    NX k i j = if 2 = i ∧ 0 = j then (X : Polynomial k) else 0 := rfl

/-- Entries of the generator image `NY = E₀₁ - E₁₂`. -/
theorem NY_apply (i j : Fin 3) :
    NY k i j = (if 0 = i ∧ 1 = j then (1 : Polynomial k) else 0)
      - (if 1 = i ∧ 2 = j then (1 : Polynomial k) else 0) := rfl

/-- **A polynomial matrix commuting with both generator images is scalar.**

`⁅P, NX⁆ = 0` pins the last column and the `(0,1)` entry and equates `P₂₂` with `P₀₀`;
`⁅P, NY⁆ = 0` pins the strictly lower triangle and equates `P₁₁` with `P₀₀`. No hypothesis on the
base ring is needed: multiplication by `t` is injective on `k[t]` over any commutative ring. -/
theorem centralizer_NX_NY_eq_scalar (P : Matrix (Fin 3) (Fin 3) (Polynomial k))
    (hX : ⁅P, NX k⁆ = 0) (hY : ⁅P, NY k⁆ = 0) :
    P = Matrix.scalar (Fin 3) (P 0 0) := by
  have eX : ∀ i j : Fin 3, (P * NX k - NX k * P) i j = 0 := by
    intro i j
    have := congrFun (congrFun hX i) j
    simpa [LieRing.of_associative_ring_bracket] using this
  have eY : ∀ i j : Fin 3, (P * NY k - NY k * P) i j = 0 := by
    intro i j
    have := congrFun (congrFun hY i) j
    simpa [LieRing.of_associative_ring_bracket] using this
  have h02 : P 0 2 = 0 := by have := eX 0 0; simpa [Matrix.mul_apply, NX_apply] using this
  have h12 : P 1 2 = 0 := by have := eX 1 0; simpa [Matrix.mul_apply, NX_apply] using this
  have h01 : P 0 1 = 0 := by have := eX 2 1; simpa [Matrix.mul_apply, NX_apply] using this
  have h22 : P 2 2 = P 0 0 := by
    have h : P 2 2 * X = X * P 0 0 := by
      have := eX 2 0
      simpa [Matrix.mul_apply, NX_apply, sub_eq_zero] using this
    have h' : (P 2 2 - P 0 0) * X = 0 := by linear_combination h
    simpa [sub_eq_zero] using h'
  have h10 : P 1 0 = 0 := by have := eY 0 0; simpa [Matrix.mul_apply, NY_apply] using this
  have h20 : P 2 0 = 0 := by have := eY 1 0; simpa [Matrix.mul_apply, NY_apply] using this
  have h21 : P 2 1 = 0 := by have := eY 2 2; simpa [Matrix.mul_apply, NY_apply] using this
  have h11 : P 0 0 = P 1 1 := by
    have := eY 0 1
    simpa [Matrix.mul_apply, NY_apply, sub_eq_zero] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal, h02, h12, h01, h22, h10, h20, h21, h11]

end Centralizer

/-! ## The centre of `𝔫₊ = loopPos` is trivial -/

section CentreLoopPos

variable {k : Type*} [Field k]

/-- **The centre of the twisted loop algebra `𝔫₊` is trivial** (for `3 ≠ 0`).

An element of `loopPos` commuting with the two generators is scalar by
`centralizer_NX_NY_eq_scalar`, and a scalar matrix `a·1` in `𝔤𝔩₃` has trace `3a`, so the trace
condition defining `loopPos` forces `a = 0`.

The hypothesis `3 ≠ 0` is sharp: in characteristic `3` the identity matrix is traceless, and
`a·1` with `a` an odd polynomial satisfies the two remaining conditions of `loopPos`, so it is a
nonzero central element. -/
theorem eq_zero_of_mem_loopPos_of_central (h3 : (3 : k) ≠ 0)
    {P : Matrix (Fin 3) (Fin 3) (Polynomial k)} (hP : P ∈ loopPos k)
    (hX : ⁅P, NX k⁆ = 0) (hY : ⁅P, NY k⁆ = 0) : P = 0 := by
  have hscal : P = Matrix.scalar (Fin 3) (P 0 0) := centralizer_NX_NY_eq_scalar P hX hY
  have htr : Matrix.trace P = 0 := hP.1
  rw [hscal] at htr
  have h : (3 : Polynomial k) = 0 ∨ P 0 0 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Matrix.scalar_apply] using htr
  have hzero : P 0 0 = 0 := by
    refine h.resolve_left fun hc => h3 ?_
    simpa using congrArg (fun p : Polynomial k => p.coeff 0) hc
  rw [hscal, hzero, map_zero]

end CentreLoopPos

/-! ## The loop model kills the centre of `𝔤₄` -/

section Gbar

variable {k : Type*} [Field k]

/-- The loop realization composed with the quotient projection is the free realization. -/
theorem gbar_proj (a : FreeLieAlgebra k (Fin 2)) :
    gbar k (proj k 4 a) = matHom₄ k a := rfl

/-- The loop realization sends x̄ to the degree-one loop generator. -/
@[simp] theorem gbar_xb : gbar k (xb k 4) = NX k := matHom₄_x k

/-- The loop realization sends ȳ to the degree-zero loop generator. -/
@[simp] theorem gbar_yb : gbar k (yb k 4) = NY k := matHom₄_y k

/-- `gbar` is a Lie algebra map, not merely `k`-linear: brackets are computed on representatives,
where `matHom₄` is a `LieHom`. -/
theorem gbar_lie (u v : g k 4) : gbar k ⁅u, v⁆ = ⁅gbar k u, gbar k v⁆ := by
  obtain ⟨a, rfl⟩ := proj_surjective k 4 u
  obtain ⟨b, rfl⟩ := proj_surjective k 4 v
  rw [← LieHom.map_lie, gbar_proj, gbar_proj, gbar_proj, LieHom.map_lie]

/-- Membership statement for `gbar_mem_loopPos`. -/
theorem gbar_mem_loopPos (u : g k 4) : gbar k u ∈ loopPos k := by
  obtain ⟨a, rfl⟩ := proj_surjective k 4 u
  exact range_matHom₄_le_loopPos k ⟨a, rfl⟩

/-- **The loop realization annihilates the centre of `𝔤₄`** (for `3 ≠ 0`).

The image of a central element commutes with the images of both generators and lies in
`loopPos`, so it is `0` by `eq_zero_of_mem_loopPos_of_central`. -/
theorem gbar_eq_zero_of_central (h3 : (3 : k) ≠ 0) {z : g k 4} (hz : ∀ v : g k 4, ⁅v, z⁆ = 0) :
    gbar k z = 0 := by
  refine eq_zero_of_mem_loopPos_of_central h3 (gbar_mem_loopPos z) ?_ ?_
  · rw [← gbar_xb (k := k), ← gbar_lie, ← lie_skew, hz, map_neg, map_zero, neg_zero]
  · rw [← gbar_yb (k := k), ← gbar_lie, ← lie_skew, hz, map_neg, map_zero, neg_zero]

/-- **The loop model cannot detect the defect.** `gbar` sends the obstruction to the even-to-odd
induction step to `0`, so any proof that `EvenLayer.defect c = 0` needs an input beyond
`matHom₄`. -/
theorem gbar_defect_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    {c : g k 4} (h : EvenLayer k c) : gbar k (EvenLayer.defect c) = 0 :=
  gbar_eq_zero_of_central h3 (h.central_defect h2 h3 h5)

/-! ## Injectivity of `gbar` closes the layer induction -/

/-- If `gbar` is injective then every defect vanishes: the defect is central, and `gbar` kills the
centre. -/
theorem defect_eq_zero_of_gbar_injective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective (gbar k)) {c : g k 4} (h : EvenLayer k c) :
    EvenLayer.defect c = 0 :=
  hinj (by rw [map_zero]; exact gbar_defect_eq_zero h2 h3 h5 h)

/-- **The remaining gap in the layer induction, restated as injectivity of an explicit matrix
map.** If `gbar : 𝔤₄ → 𝔤𝔩₃(k[t])` is injective then the odd-layer invariant holds in every odd
`t`-degree, which together with the unconditional `evenLayer_evenTower` closes the whole
induction. -/
theorem oddLayer_evenTower_of_gbar_injective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (hinj : Function.Injective (gbar k)) (m : ℕ) :
    OddLayer k (oddTop (evenTower k m)) (evenTop (oddTop (evenTower k m))) :=
  OddLayer.of_evenLayer h2 h3 (evenLayer_evenTower h2 h3 h5 m)
    (defect_eq_zero_of_gbar_injective h2 h3 h5 hinj (evenLayer_evenTower h2 h3 h5 m))

/-- The same conclusion in the reduced bracket form of `oddLayer_evenTower_of_lie_eq_zero`. -/
theorem lie_a1_a3_dY_one_evenTower_of_gbar_injective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (hinj : Function.Injective (gbar k)) (m : ℕ) :
    ⁅⁅aElt k 4 1, aElt k 4 3⁆, dY k 1 (evenTower k m)⁆ = 0 := by
  have h := evenLayer_evenTower h2 h3 h5 m
  rw [← h.defect_eq h2 h3]
  exact defect_eq_zero_of_gbar_injective h2 h3 h5 hinj h

/-! ### The spanning family, given injectivity -/

/-- Every layer defect vanishes once `gbar` is injective. -/
theorem topDefect_eq_zero_of_gbar_injective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (hinj : Function.Injective (gbar k)) (m : ℕ) : topDefect k m = 0 := by
  cases m with
  | zero => exact topDefect_zero_eq
  | succ m =>
      exact defect_eq_zero_of_gbar_injective h2 h3 h5 hinj (evenLayer_evenTower h2 h3 h5 m)

/-- The odd-layer invariant in every odd `t`-degree, indexed uniformly by `topOdd`. -/
theorem oddLayer_topOdd_of_gbar_injective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective (gbar k)) (m : ℕ) : OddLayer k (topOdd k m) (evenTower k m) :=
  oddLayer_topOdd h2 h3 h5 (topDefect_eq_zero_of_gbar_injective h2 h3 h5 hinj) m

/-- **The upper bound of Problem 2.16.3(b), given injectivity of `gbar`.** The `LoopIdx`-indexed
family `loopFam₄` spans `𝔤₄`, with `1` element in `t`-degree `0`, `5` in each odd degree and `3`
in each even degree `≥ 2` — the graded dimensions of `𝔫₊(A₂⁽²⁾)`. Together with
`range_matHom₄_eq_loopPos` this is what turns `matHom₄` into an isomorphism. -/
theorem span_range_loopFam₄_eq_top_of_gbar_injective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (hinj : Function.Injective (gbar k)) :
    Submodule.span k (Set.range (loopFam₄ k)) = ⊤ :=
  span_range_loopFam₄_eq_top h2 h3 h5 (topDefect_eq_zero_of_gbar_injective h2 h3 h5 hinj)

end Gbar

end Etingof.Problem2_16_3
