import Mathlib
import EtingofRepresentationTheory.Chapter6.DynkinTypes

/-!
# Problem 6.9.2: The `E₈` lattice and root system

> Let `L ⊂ ½ℤ⁸` be the lattice of vectors where the coordinates are either all
> integers or all half-integers (but not integers) and the sum of all
> coordinates is an even integer.
>
> **(a)** Let `αᵢ = eᵢ - eᵢ₊₁` for `i = 1, …, 6`, `α₇ = e₆ + e₇`,
> `α₈ = -½ ∑_{i=1}^8 eᵢ`. Show that the `αᵢ` are a basis of `L` (over `ℤ`).
>
> **(b)** Show that the roots in `L` (vectors of squared length `2`) form a root
> system of type `E₈` (compute the inner products of the `αᵢ`).
>
> **(c)** Show that the `E₇` and `E₆` lattices are the sets of vectors in the
> `E₈` lattice `L` where the first two, resp. three, coordinates are equal.
>
> **(d)** Show that `E₆, E₇, E₈` have `72, 126, 240` roots, respectively.

We model `½ℤ⁸` inside `Fin 8 → ℚ`, with the standard inner product
`⟪x, y⟫ = ∑ᵢ xᵢ yᵢ`. Roots are the vectors of the lattice with `⟪x, x⟫ = 2`.
Book indices `e₁, …, e₈` are the `0`-indexed standard basis of `Fin 8 → ℚ`.
-/

namespace Etingof.Problem6_9_2

open Finset

/-- The standard inner product on `Fin 8 → ℚ`, `⟪x, y⟫ = ∑ᵢ xᵢ yᵢ`. -/
def inner (x y : Fin 8 → ℚ) : ℚ := ∑ i, x i * y i

/-- A vector has all-integer coordinates. -/
def AllInt (x : Fin 8 → ℚ) : Prop := ∀ i, ∃ n : ℤ, x i = n

/-- A vector has all half-integer (non-integer) coordinates. -/
def AllHalfInt (x : Fin 8 → ℚ) : Prop := ∀ i, ∃ n : ℤ, x i = (n : ℚ) + 1 / 2

/-- The sum of coordinates is an even integer. -/
def EvenSum (x : Fin 8 → ℚ) : Prop := ∃ m : ℤ, (∑ i, x i) = 2 * m

/-- The `E₈` lattice `L ⊂ ½ℤ⁸`: coordinates all integers or all half-integers,
with even coordinate sum. -/
def E8Lattice : Set (Fin 8 → ℚ) :=
  {x | (AllInt x ∨ AllHalfInt x) ∧ EvenSum x}

/-- The set of **roots** of a subset `S`: its vectors of squared length `2`. -/
def rootsOf (S : Set (Fin 8 → ℚ)) : Set (Fin 8 → ℚ) := {x ∈ S | inner x x = 2}

/-- The standard basis vector `eⱼ` of `Fin 8 → ℚ`. -/
def e (j : Fin 8) : Fin 8 → ℚ := fun i => if i = j then 1 else 0

/-! ## Part (a): the simple roots `αᵢ` and the basis claim -/

/-- The simple roots `α₀, …, α₇` (book `α₁, …, α₈`) of `E₈`:
`αᵢ = eᵢ - eᵢ₊₁` for `i < 6`, `α₆ = e₅ + e₆`, `α₇ = -½ ∑ⱼ eⱼ`. -/
def α : Fin 8 → (Fin 8 → ℚ)
  | 0 => e 0 - e 1
  | 1 => e 1 - e 2
  | 2 => e 2 - e 3
  | 3 => e 3 - e 4
  | 4 => e 4 - e 5
  | 5 => e 5 - e 6
  | 6 => e 5 + e 6
  | 7 => fun _ => -(1 / 2)

/-- Expand the standard inner product on `Fin 8 → ℚ` as an eight-term sum. -/
private lemma inner_eq (x y : Fin 8 → ℚ) :
    inner x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3
      + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7 := by
  simp only [inner, Fin.sum_univ_eight]

/-- **(a)** The `αᵢ` are `ℤ`-linearly independent. -/
theorem α_linearIndependent (c : Fin 8 → ℤ)
    (h : (∑ i, (c i : ℚ) • α i) = 0) : c = 0 := by
  -- Extract the eight coordinate equations.
  have e0 := congr_fun h 0
  have e1 := congr_fun h 1
  have e2 := congr_fun h 2
  have e3 := congr_fun h 3
  have e4 := congr_fun h 4
  have e5 := congr_fun h 5
  have e6 := congr_fun h 6
  have e7 := congr_fun h 7
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Pi.zero_apply] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [α, e, Pi.sub_apply, Pi.add_apply, Fin.reduceEq,
    reduceIte] at e0 e1 e2 e3 e4 e5 e6 e7
  norm_num at e0 e1 e2 e3 e4 e5 e6 e7
  -- Solve the triangular system over ℚ, then cast back to ℤ.
  have h7 : (c 7 : ℚ) = 0 := by exact_mod_cast e7
  have h0 : (c 0 : ℚ) = 0 := by linarith
  have h1 : (c 1 : ℚ) = 0 := by linarith
  have h2 : (c 2 : ℚ) = 0 := by linarith
  have h3 : (c 3 : ℚ) = 0 := by linarith
  have h4 : (c 4 : ℚ) = 0 := by linarith
  have h5 : (c 5 : ℚ) = 0 := by linarith
  have h6 : (c 6 : ℚ) = 0 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · exact_mod_cast h7

set_option linter.unusedSimpArgs false in
/-- Each coordinate of the `ℤ`-combination `∑ᵢ cᵢ αᵢ` is an integer shifted by
`-c₇/2`. The integer part `aₖ` telescopes the coefficients. -/
private lemma sum_α_coord (c : Fin 8 → ℤ) (k : Fin 8) :
    ∃ a : ℤ, (∑ i, (c i : ℚ) • α i) k = (a : ℚ) - (c 7 : ℚ) / 2 := by
  refine ⟨![c 0, c 1 - c 0, c 2 - c 1, c 3 - c 2, c 4 - c 3,
    c 5 + c 6 - c 4, c 6 - c 5, 0] k, ?_⟩
  fin_cases k <;>
    (simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
        α, e, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val,
        Matrix.head_fin_const]
     push_cast
     ring)

set_option linter.unusedSimpArgs false in
/-- **(a)** The `αᵢ` span `L` over `ℤ`: every lattice vector is a `ℤ`-combination
of the `αᵢ`, and every `ℤ`-combination lies in `L`. Together with
`α_linearIndependent`, this says the `αᵢ` are a `ℤ`-basis of `L`. -/
theorem α_isBasis :
    (∀ x ∈ E8Lattice, ∃ c : Fin 8 → ℤ, x = ∑ i, (c i : ℚ) • α i) ∧
    (∀ c : Fin 8 → ℤ, (∑ i, (c i : ℚ) • α i) ∈ E8Lattice) := by
  refine ⟨?_, ?_⟩
  · -- Spanning: invert the (triangular) coordinate system.
    rintro x ⟨hdisj, M, hM⟩
    rcases hdisj with hInt | hHalf
    · -- All-integer coordinates `x i = n i`, with `∑ n i = 2M`.
      choose n hn using hInt
      refine ⟨![n 0 - n 7, n 0 + n 1 - 2 * n 7, n 0 + n 1 + n 2 - 3 * n 7,
        n 0 + n 1 + n 2 + n 3 - 4 * n 7, n 0 + n 1 + n 2 + n 3 + n 4 - 5 * n 7,
        M - n 6 - 3 * n 7, M - 4 * n 7, -2 * n 7], ?_⟩
      have hs : (n 0 : ℚ) + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 = 2 * M := by
        have h := hM; rw [Fin.sum_univ_eight] at h; simp only [hn] at h; push_cast; linarith [h]
      funext k
      fin_cases k <;>
        (simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
            α, e, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val,
            Matrix.head_fin_const, hn]
         push_cast
         first | linear_combination hs | ring)
    · -- All-half-integer coordinates `x i = n i + ½`, with `∑ n i = 2M - 4`.
      choose n hn using hHalf
      refine ⟨![n 0 - n 7, n 0 + n 1 - 2 * n 7, n 0 + n 1 + n 2 - 3 * n 7,
        n 0 + n 1 + n 2 + n 3 - 4 * n 7, n 0 + n 1 + n 2 + n 3 + n 4 - 5 * n 7,
        M - 2 - n 6 - 3 * n 7, M - 2 - 4 * n 7, -2 * n 7 - 1], ?_⟩
      have hs : (n 0 : ℚ) + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 = 2 * M - 4 := by
        have h := hM; rw [Fin.sum_univ_eight] at h; simp only [hn] at h; push_cast; linarith [h]
      funext k
      fin_cases k <;>
        (simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
            α, e, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val,
            Matrix.head_fin_const, hn]
         push_cast
         first | linear_combination hs | ring)
  · -- Closure: every `ℤ`-combination lies in `L`.
    intro c
    refine ⟨?_, ?_⟩
    · -- Coordinates are all integers or all half-integers, per parity of `c₇`.
      rcases Int.even_or_odd (c 7) with ⟨m, hm⟩ | ⟨m, hm⟩
      · left
        intro k
        obtain ⟨a, ha⟩ := sum_α_coord c k
        exact ⟨a - m, by rw [ha, hm]; push_cast; ring⟩
      · right
        intro k
        obtain ⟨a, ha⟩ := sum_α_coord c k
        exact ⟨a - m - 1, by rw [ha, hm]; push_cast; ring⟩
    · -- Even coordinate sum: `∑ₖ (∑ᵢ cᵢ αᵢ)ₖ = 2 (c₆ - 2 c₇)`.
      refine ⟨c 6 - 2 * c 7, ?_⟩
      rw [Fin.sum_univ_eight]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
        α, e, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte]
      push_cast; ring

/-! ## Part (b): the roots form a root system of type `E₈` -/

/-- The Gram matrix `⟪αᵢ, αⱼ⟫` of the simple roots, as an adjacency-style matrix
`gramAdj i j = -⟪αᵢ, αⱼ⟫` for `i ≠ j` (and `0` on the diagonal). -/
def gramAdj (i j : Fin 8) : ℤ :=
  if i = j then 0 else -(inner (α i) (α j)).num

/-- **(b)** Each `αᵢ` is a root: `⟪αᵢ, αᵢ⟫ = 2`. -/
theorem α_norm_two (i : Fin 8) : inner (α i) (α i) = 2 := by
  fin_cases i <;>
    simp only [inner_eq, α, e, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte] <;>
    norm_num

/-- **(b)** The roots are simply laced: distinct simple roots have inner product
`0` or `-1`. -/
theorem α_inner_offdiag (i j : Fin 8) (h : i ≠ j) :
    inner (α i) (α j) = 0 ∨ inner (α i) (α j) = -1 := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl h
      | (simp [inner_eq, α, e, Pi.sub_apply, Pi.add_apply] <;> norm_num)

/-- The explicit adjacency matrix `-⟪αᵢ, αⱼ⟫` of the simple roots (off diagonal).
The trivalent vertex is `α₄`, with legs `α₄–α₅` (length 1), `α₄–α₆–α₇` (length 2),
and `α₄–α₃–α₂–α₁–α₀` (length 4). -/
private def gramMat : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0,1,0,0,0,0,0,0;
     1,0,1,0,0,0,0,0;
     0,1,0,1,0,0,0,0;
     0,0,1,0,1,0,0,0;
     0,0,0,1,0,1,1,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,1,0,0,1;
     0,0,0,0,0,0,1,0]

/-- `gramAdj` is the explicit adjacency matrix `gramMat`. -/
private lemma gramAdj_eq : gramAdj = gramMat := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [gramAdj, gramMat, inner_eq, α, e, Pi.sub_apply, Pi.add_apply,
      Fin.reduceEq, reduceIte] <;>
    norm_num

/-- **(b)** The Gram matrix of the `αᵢ` is the Cartan matrix of a Dynkin diagram
of **type `E₈`**: it is positive definite and graph-isomorphic to the standard
`E₈` adjacency matrix. Hence the roots in `L` form a root system of type `E₈`. -/
theorem α_gram_is_E8 :
    IsDynkinDiagram 8 gramAdj ∧
    ∃ σ : Fin 8 ≃ Fin 8, ∀ i j, gramAdj (σ i) (σ j) = DynkinType.E8.adj i j := by
  -- The E₈-labelling `σ`: E₈ vertex `i` ↦ the simple root index below.
  -- `σ` sends the E₈ trivalent vertex `2` to `α₄`, the branch `7` to `α₅`,
  -- and unrolls the two legs `2-1-0 ↦ 4-6-7` and `2-3-4-5-6 ↦ 4-3-2-1-0`.
  let σ : Fin 8 ≃ Fin 8 :=
    ⟨![7, 6, 4, 3, 2, 1, 0, 5], ![6, 5, 4, 3, 2, 7, 1, 0], by decide, by decide⟩
  have hiso : ∀ i j, gramAdj (σ i) (σ j) = DynkinType.E8.adj i j := by
    intro i j
    change gramAdj (σ.toFun i) (σ.toFun j) = _
    rw [gramAdj_eq]
    fin_cases i <;> fin_cases j <;> rfl
  exact ⟨isDynkinDiagram_of_graph_iso σ hiso (isDynkinDiagram_of_type .E8), σ, hiso⟩

/-! ## Part (c): the `E₆` and `E₇` sublattices -/

/-- **(c)** The `E₇` lattice: vectors of `L` whose first two coordinates are
equal. -/
def E7Lattice : Set (Fin 8 → ℚ) := {x ∈ E8Lattice | x 0 = x 1}

/-- **(c)** The `E₆` lattice: vectors of `L` whose first three coordinates are
equal. -/
def E6Lattice : Set (Fin 8 → ℚ) := {x ∈ E8Lattice | x 0 = x 1 ∧ x 1 = x 2}

/-! ## Part (d): the root counts `72, 126, 240`

The roots of `E₈` split into **integer** roots `±eᵢ ± eⱼ` (`i < j`, all four sign
choices; `4·C(8,2) = 112` of them) and **half-integer** roots `½(±1, …, ±1)` with an
even number of `−` signs (`2⁷ = 128` of them), for a total of `240`. We package these
two families as images of decidable finite index sets, prove the root set equals that
image, and read off the cardinalities by `decide`. The `E₇` (`x₀ = x₁`) and `E₆`
(`x₀ = x₁ = x₂`) counts drop out by adding the corresponding coordinate constraint to
the index sets. -/

/-- The integer vector `±eᵢ ± eⱼ` as an `ℤ`-valued coordinate function (signs from
`a, b`); its `ℚ` cast is the integer root `intVec i j a b`. -/
def coordZ (i j : Fin 8) (a b : Bool) (k : Fin 8) : ℤ :=
  (if k = i then (if a then 1 else -1) else 0) + (if k = j then (if b then 1 else -1) else 0)

/-- The integer root `±eᵢ ± eⱼ` (signs from `a, b`). -/
def intVec (i j : Fin 8) (a b : Bool) : Fin 8 → ℚ := fun k => (coordZ i j a b k : ℚ)

/-- The half-integer sign vector `½(±1, …, ±1)` (`+½` where `s k` is `true`). -/
def halfVec (s : Fin 8 → Bool) : Fin 8 → ℚ := fun k => if s k then 1 / 2 else -1 / 2

/-- Index type for integer roots: an ordered pair of positions plus two signs. -/
abbrev Idx := Fin 8 × Fin 8 × Bool × Bool

/-- The integer root indexed by `p = (i, j, a, b)`. -/
def intVec' (p : Idx) : Fin 8 → ℚ := intVec p.1 p.2.1 p.2.2.1 p.2.2.2

/-- The `ℤ` coordinate function of the integer root indexed by `p`. -/
def cz (p : Idx) (k : Fin 8) : ℤ := coordZ p.1 p.2.1 p.2.2.1 p.2.2.2 k

/-- The number of `+` signs in a sign vector. -/
def numTrue (s : Fin 8 → Bool) : ℕ := (univ.filter (fun k => s k = true)).card

/-! ### Coordinate evaluation of `coordZ` -/

lemma coordZ_at_fst (i j a b) (h : i ≠ j) : coordZ i j a b i = if a then 1 else -1 := by
  unfold coordZ; simp [h]

lemma coordZ_at_snd (i j a b) (h : i ≠ j) : coordZ i j a b j = if b then 1 else -1 := by
  unfold coordZ; simp [Ne.symm h]

lemma coordZ_other (i j a b) (k) (hi : k ≠ i) (hj : k ≠ j) : coordZ i j a b k = 0 := by
  simp only [coordZ, if_neg hi, if_neg hj, add_zero]

lemma sgn_ne (a : Bool) : (if a then (1 : ℤ) else -1) ≠ 0 := by cases a <;> decide

/-! ### Norms and even-sum properties of the two root families -/

set_option maxRecDepth 4000 in
lemma sum_coordZ_sq (i j : Fin 8) (a b : Bool) (h : i ≠ j) :
    ∑ k, (coordZ i j a b k) ^ 2 = 2 := by
  revert h; revert a b
  fin_cases i <;> fin_cases j <;> decide

lemma inner_intVec (i j : Fin 8) (a b : Bool) (h : i ≠ j) :
    inner (intVec i j a b) (intVec i j a b) = 2 := by
  have hh : inner (intVec i j a b) (intVec i j a b)
      = ((∑ k, (coordZ i j a b k) ^ 2 : ℤ) : ℚ) := by
    simp only [inner, intVec]; push_cast; apply Finset.sum_congr rfl; intro k _; ring
  rw [hh, sum_coordZ_sq i j a b h]; norm_num

lemma inner_halfVec (s : Fin 8 → Bool) : inner (halfVec s) (halfVec s) = 2 := by
  have hsq : ∀ k, halfVec s k * halfVec s k = 1 / 4 := by
    intro k; simp only [halfVec]; split_ifs <;> norm_num
  simp only [inner, hsq]; norm_num

lemma allInt_intVec (i j a b) : AllInt (intVec i j a b) :=
  fun k => ⟨coordZ i j a b k, rfl⟩

lemma allHalfInt_halfVec (s) : AllHalfInt (halfVec s) := by
  intro k; simp only [halfVec]
  split_ifs
  · exact ⟨0, by norm_num⟩
  · exact ⟨-1, by norm_num⟩

set_option maxRecDepth 4000 in
lemma even_sum_coordZ (i j a b) : Even (∑ k, coordZ i j a b k) := by
  revert a b; fin_cases i <;> fin_cases j <;> decide

lemma evenSum_intVec (i j a b) : EvenSum (intVec i j a b) := by
  obtain ⟨r, hr⟩ := even_sum_coordZ i j a b
  refine ⟨r, ?_⟩
  have hcast : (∑ k, intVec i j a b k) = ((∑ k, coordZ i j a b k : ℤ) : ℚ) := by
    simp only [intVec]; push_cast; rfl
  rw [hcast, hr]; push_cast; ring

lemma sum_halfVec (s) : ∑ k, halfVec s k = (numTrue s : ℚ) - 4 := by
  have hpt : ∀ k, halfVec s k = (if s k = true then (1 : ℚ) else 0) - 1 / 2 := by
    intro k; simp only [halfVec]; split_ifs <;> norm_num
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, numTrue]
  push_cast; ring

lemma evenSum_halfVec (s) (hev : Even (numTrue s)) : EvenSum (halfVec s) := by
  obtain ⟨u, hu⟩ := hev
  exact ⟨u - 2, by rw [sum_halfVec, hu]; push_cast; ring⟩

lemma evenSum_halfVec_iff (s) : EvenSum (halfVec s) ↔ Even (numTrue s) := by
  refine ⟨fun ⟨m, hm⟩ => ?_, evenSum_halfVec s⟩
  rw [sum_halfVec] at hm
  have hz : (numTrue s : ℤ) = 2 * m + 4 := by
    have : (numTrue s : ℚ) = 2 * (m : ℚ) + 4 := by linarith [hm]
    exact_mod_cast this
  exact (Int.even_coe_nat _).1 ⟨m + 2, by rw [hz]; ring⟩

/-! ### Injectivity and disjointness of the two families -/

lemma halfVec_inj : Function.Injective halfVec := by
  intro s t h; funext k
  have hk := congr_fun h k; simp only [halfVec] at hk
  rcases Bool.eq_false_or_eq_true (s k) with hs | hs <;>
    rcases Bool.eq_false_or_eq_true (t k) with ht | ht <;>
    rw [hs, ht] at hk ⊢ <;> first | rfl | (norm_num at hk)

lemma halfVec_eq_iff (s k l) : halfVec s k = halfVec s l ↔ s k = s l := by
  refine ⟨fun h => ?_, fun h => by rw [halfVec, halfVec, h]⟩
  simp only [halfVec] at h
  rcases Bool.eq_false_or_eq_true (s k) with hk | hk <;>
    rcases Bool.eq_false_or_eq_true (s l) with hl | hl <;>
    rw [hk, hl] at h ⊢ <;> first | rfl | (norm_num at h)

lemma intVec'_injOn : Set.InjOn intVec' {p : Idx | p.1 < p.2.1} := by
  rintro ⟨i, j, a, b⟩ hp ⟨i', j', a', b'⟩ hp' heq
  simp only [Set.mem_setOf_eq] at hp hp'
  have hij : i ≠ j := hp.ne
  have hij' : i' ≠ j' := hp'.ne
  have hcoord : ∀ k, coordZ i j a b k = coordZ i' j' a' b' k := by
    intro k; have := congr_fun heq k
    simp only [intVec', intVec] at this; exact_mod_cast this
  have mem_i' : i' = i ∨ i' = j := by
    by_contra hc; simp only [not_or] at hc
    have h0 : coordZ i j a b i' = 0 := coordZ_other i j a b i' hc.1 hc.2
    have hne : coordZ i' j' a' b' i' ≠ 0 := by
      rw [coordZ_at_fst i' j' a' b' hij']; exact sgn_ne a'
    rw [← hcoord] at hne; exact hne h0
  have mem_j' : j' = i ∨ j' = j := by
    by_contra hc; simp only [not_or] at hc
    have h0 : coordZ i j a b j' = 0 := coordZ_other i j a b j' hc.1 hc.2
    have hne : coordZ i' j' a' b' j' ≠ 0 := by
      rw [coordZ_at_snd i' j' a' b' hij']; exact sgn_ne b'
    rw [← hcoord] at hne; exact hne h0
  have hii : i' = i := by
    rcases mem_i' with h | h
    · exact h
    · exfalso; subst h; rcases mem_j' with h2 | h2 <;> omega
  have hjj : j' = j := by
    rcases mem_j' with h | h
    · exfalso; subst hii; omega
    · exact h
  subst hii; subst hjj
  have ha : a = a' := by
    have h1 := coordZ_at_fst i' j' a b hij
    have h2 := coordZ_at_fst i' j' a' b' hij
    rw [hcoord i'] at h1; rw [h1] at h2; cases a <;> cases a' <;> simp_all
  have hb : b = b' := by
    have h1 := coordZ_at_snd i' j' a b hij
    have h2 := coordZ_at_snd i' j' a' b' hij
    rw [hcoord j'] at h1; rw [h1] at h2; cases b <;> cases b' <;> simp_all
  subst ha; subst hb; rfl

lemma intVec_ne_halfVec (i j a b s) : intVec i j a b ≠ halfVec s := by
  intro h
  have h0 := congr_fun h 0
  simp only [intVec, halfVec] at h0
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℚ) = if s 0 = true then (1 : ℚ) / 2 else -1 / 2 :=
    ⟨coordZ i j a b 0, by rw [h0]⟩
  have : (2 * n : ℤ) = 1 ∨ (2 * n : ℤ) = -1 := by
    split_ifs at hn
    · left; have : (2 * n : ℚ) = 1 := by rw [hn]; ring
      exact_mod_cast this
    · right; have : (2 * n : ℚ) = -1 := by rw [hn]; ring
      exact_mod_cast this
  omega

/-! ### The classification: exact shape of a root -/

lemma halfShape (x : Fin 8 → ℚ) (hHalf : AllHalfInt x) (hnorm : inner x x = 2) :
    ∃ s : Fin 8 → Bool, x = halfVec s := by
  choose n hn using hHalf
  have hgz : ∀ k, (0 : ℤ) ≤ n k * (n k + 1) := by
    intro k
    rcases lt_or_ge (n k) 0 with h | h
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -(n k) by linarith)
        (show (0 : ℤ) ≤ -(n k + 1) by linarith)]
    · exact mul_nonneg h (by linarith)
  have hge : ∀ k ∈ (univ : Finset (Fin 8)), (0 : ℚ) ≤ x k * x k - 1 / 4 := by
    intro k _
    have hc : (0 : ℚ) ≤ (n k : ℚ) * ((n k : ℚ) + 1) := by exact_mod_cast hgz k
    rw [hn k]; nlinarith [hc]
  have hsum0 : ∑ k, (x k * x k - 1 / 4) = 0 := by
    simp only [Finset.sum_sub_distrib]
    have h4 : (∑ _k : Fin 8, (1 : ℚ) / 4) = 2 := by
      rw [Finset.sum_const, card_univ]; norm_num
    rw [h4]; simp only [inner] at hnorm; rw [hnorm]; ring
  have heach : ∀ k ∈ (univ : Finset (Fin 8)), x k * x k - 1 / 4 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hge).1 hsum0
  refine ⟨fun k => decide (x k = 1 / 2), ?_⟩
  funext k
  have hk : x k * x k = 1 / 4 := by have := heach k (mem_univ k); linarith
  have hor : x k = 1 / 2 ∨ x k = -1 / 2 := by
    have hfac : (x k - 1 / 2) * (x k + 1 / 2) = 0 := by nlinarith [hk]
    rcases mul_eq_zero.1 hfac with h | h
    · left; linarith
    · right; linarith
  simp only [halfVec]
  rcases hor with h | h <;> simp [h]

lemma intShape (x : Fin 8 → ℚ) (hInt : AllInt x) (hnorm : inner x x = 2) :
    ∃ i j a b, i < j ∧ x = intVec i j a b := by
  choose c hc using hInt
  have hZ : ∑ k, (c k) ^ 2 = 2 := by
    have h : ((∑ k, (c k) ^ 2 : ℤ) : ℚ) = 2 := by
      push_cast; simp only [inner, hc] at hnorm
      rw [← hnorm]; apply Finset.sum_congr rfl; intro k _; ring
    exact_mod_cast h
  have hbound : ∀ k, c k = -1 ∨ c k = 0 ∨ c k = 1 := by
    intro k
    have hle : (c k) ^ 2 ≤ 2 := by
      have := Finset.single_le_sum (f := fun k => (c k) ^ 2)
        (fun i _ => sq_nonneg (c i)) (mem_univ k)
      rw [hZ] at this; exact this
    have h4 : (c k) ^ 2 ≤ 2 ^ 2 := by nlinarith [hle]
    obtain ⟨hlo, hhi⟩ := abs_le_of_sq_le_sq' h4 (by norm_num : (0 : ℤ) ≤ 2)
    interval_cases (c k) <;> simp_all
  set S := univ.filter (fun k => c k ≠ 0) with hS
  have memS : ∀ k, k ∈ S ↔ c k ≠ 0 := by intro k; rw [hS]; simp
  have hsq1 : ∀ k ∈ S, (c k) ^ 2 = 1 := by
    intro k hk; rw [memS] at hk
    rcases hbound k with h | h | h <;> simp_all
  have hsumS : ∑ k ∈ S, (c k) ^ 2 = 2 := by
    have hsub : ∑ k ∈ S, (c k) ^ 2 = ∑ k, (c k) ^ 2 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k _ hk; rw [memS, not_not] at hk; simp [hk]
    rw [hsub, hZ]
  have hcard : S.card = 2 := by
    have heq : (∑ k ∈ S, (c k) ^ 2) = (S.card : ℤ) := by
      rw [Finset.sum_congr rfl hsq1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [heq] at hsumS; exact_mod_cast hsumS
  obtain ⟨p, q, hpq, hSpq⟩ := Finset.card_eq_two.1 hcard
  have hpS : p ∈ S := by rw [hSpq]; simp
  have hqS : q ∈ S := by rw [hSpq]; simp
  have helper : ∀ (i j : Fin 8), i ≠ j → c i ≠ 0 → c j ≠ 0 →
      (∀ k, k ≠ i → k ≠ j → c k = 0) →
      (fun k => (c k : ℚ)) = intVec i j (decide (c i = 1)) (decide (c j = 1)) := by
    intro i j hij hci hcj hoth
    have keyi : (if decide (c i = 1) then (1 : ℤ) else -1) = c i := by
      rcases hbound i with h | h | h
      · simp [h]
      · exact absurd h hci
      · simp [h]
    have keyj : (if decide (c j = 1) then (1 : ℤ) else -1) = c j := by
      rcases hbound j with h | h | h
      · simp [h]
      · exact absurd h hcj
      · simp [h]
    funext k; simp only [intVec]
    have hint : c k = coordZ i j (decide (c i = 1)) (decide (c j = 1)) k := by
      rw [coordZ]
      by_cases hki : k = i
      · subst hki; rw [if_pos rfl, if_neg hij, keyi]; ring
      · rw [if_neg hki]
        by_cases hkj : k = j
        · subst hkj; rw [if_pos rfl, keyj]; ring
        · rw [if_neg hkj, hoth k hki hkj]; ring
    exact_mod_cast hint
  have hci : c p ≠ 0 := (memS p).1 hpS
  have hcj : c q ≠ 0 := (memS q).1 hqS
  have hoth : ∀ k, k ≠ p → k ≠ q → c k = 0 := by
    intro k hkp hkq; by_contra hne
    have hkS := (memS k).2 hne
    rw [hSpq] at hkS; simp only [mem_insert, mem_singleton] at hkS
    rcases hkS with h | h
    · exact hkp h
    · exact hkq h
  have hx : x = fun k => (c k : ℚ) := funext hc
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact ⟨p, q, _, _, hlt, hx.trans (helper p q hpq hci hcj hoth)⟩
  · refine ⟨q, p, _, _, hgt, hx.trans (helper q p (Ne.symm hpq) hcj hci ?_)⟩
    intro k hkq hkp; exact hoth k hkp hkq

/-! ### Backward membership: each indexed vector is a root -/

lemma intVec'_mem_rootsOf_E8 (p : Idx) (hp : p.1 < p.2.1) :
    intVec' p ∈ rootsOf E8Lattice :=
  ⟨⟨Or.inl (allInt_intVec _ _ _ _), evenSum_intVec _ _ _ _⟩, inner_intVec _ _ _ _ hp.ne⟩

lemma halfVec_mem_rootsOf_E8 (s) (hev : Even (numTrue s)) :
    halfVec s ∈ rootsOf E8Lattice :=
  ⟨⟨Or.inr (allHalfInt_halfVec _), evenSum_halfVec _ hev⟩, inner_halfVec _⟩

/-! ### The three root counts -/

/-- The finset of `E₈` roots: integer roots (`i < j`) and half-integer roots
(even weight), as images of decidable index sets. -/
def R8 : Finset (Fin 8 → ℚ) :=
  (univ.filter (fun p : Idx => p.1 < p.2.1)).image intVec' ∪
  (univ.filter (fun s => Even (numTrue s))).image halfVec

private lemma disjoint_int_half {I : Finset Idx} {J : Finset (Fin 8 → Bool)} :
    Disjoint (I.image intVec') (J.image halfVec) := by
  rw [Finset.disjoint_left]
  rintro x hx1 hx2
  rw [Finset.mem_image] at hx1 hx2
  obtain ⟨p, _, rfl⟩ := hx1
  obtain ⟨s, _, hs⟩ := hx2
  exact intVec_ne_halfVec p.1 p.2.1 p.2.2.1 p.2.2.2 s hs.symm

set_option maxRecDepth 10000 in
/-- **(d)** `E₈` has `240` roots. -/
theorem E8_root_count : (rootsOf E8Lattice).ncard = 240 := by
  have hset : rootsOf E8Lattice = ↑((univ.filter (fun p : Idx => p.1 < p.2.1)).image intVec' ∪
      (univ.filter (fun s => Even (numTrue s))).image halfVec) := by
    ext x
    simp only [rootsOf, E8Lattice, Set.mem_setOf_eq, Finset.coe_union,
      Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨hdisj, hev⟩, hnorm⟩
      rcases hdisj with hInt | hHalf
      · obtain ⟨i, j, a, b, hlt, hx⟩ := intShape x hInt hnorm
        exact Or.inl ⟨(i, j, a, b), hlt, hx.symm⟩
      · obtain ⟨s, hx⟩ := halfShape x hHalf hnorm
        exact Or.inr ⟨s, (evenSum_halfVec_iff s).1 (hx ▸ hev), hx.symm⟩
    · rintro (⟨p, hlt, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact intVec'_mem_rootsOf_E8 p hlt
      · exact halfVec_mem_rootsOf_E8 s hs
  have hinj : Set.InjOn intVec' ↑(univ.filter (fun p : Idx => p.1 < p.2.1)) := by
    refine intVec'_injOn.mono ?_
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint disjoint_int_half,
    Finset.card_image_of_injOn hinj, Finset.card_image_of_injOn halfVec_inj.injOn]
  decide

set_option maxRecDepth 40000 in
/-- **(d)** `E₇` has `126` roots. -/
theorem E7_root_count : (rootsOf E7Lattice).ncard = 126 := by
  have hset : rootsOf E7Lattice =
      ↑((univ.filter (fun p : Idx => p.1 < p.2.1 ∧ cz p 0 = cz p 1)).image intVec' ∪
        (univ.filter (fun s => Even (numTrue s) ∧ s 0 = s 1)).image halfVec) := by
    ext x
    simp only [rootsOf, E7Lattice, E8Lattice, Set.mem_setOf_eq,
      Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨hdisj, hev⟩, h01⟩, hnorm⟩
      rcases hdisj with hInt | hHalf
      · obtain ⟨i, j, a, b, hlt, hx⟩ := intShape x hInt hnorm
        refine Or.inl ⟨(i, j, a, b), ⟨hlt, ?_⟩, hx.symm⟩
        have : intVec i j a b 0 = intVec i j a b 1 := by rw [← hx]; exact h01
        simp only [cz, intVec] at this ⊢; exact_mod_cast this
      · obtain ⟨s, hx⟩ := halfShape x hHalf hnorm
        refine Or.inr ⟨s, ⟨(evenSum_halfVec_iff s).1 (hx ▸ hev), ?_⟩, hx.symm⟩
        have : halfVec s 0 = halfVec s 1 := by rw [← hx]; exact h01
        exact (halfVec_eq_iff s 0 1).1 this
    · rintro (⟨p, ⟨hlt, hcz⟩, rfl⟩ | ⟨s, ⟨hs, hs01⟩, rfl⟩)
      · refine ⟨⟨intVec'_mem_rootsOf_E8 p hlt |>.1, ?_⟩, intVec'_mem_rootsOf_E8 p hlt |>.2⟩
        simp only [intVec', intVec]; exact_mod_cast hcz
      · refine ⟨⟨halfVec_mem_rootsOf_E8 s hs |>.1, ?_⟩, halfVec_mem_rootsOf_E8 s hs |>.2⟩
        rw [halfVec_eq_iff]; exact hs01
  have hinj : Set.InjOn intVec' ↑(univ.filter (fun p : Idx => p.1 < p.2.1 ∧ cz p 0 = cz p 1)) := by
    refine intVec'_injOn.mono ?_
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.1
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint disjoint_int_half,
    Finset.card_image_of_injOn hinj, Finset.card_image_of_injOn halfVec_inj.injOn]
  decide

set_option maxRecDepth 40000 in
/-- **(d)** `E₆` has `72` roots. -/
theorem E6_root_count : (rootsOf E6Lattice).ncard = 72 := by
  have hset : rootsOf E6Lattice =
      ↑((univ.filter (fun p : Idx => p.1 < p.2.1 ∧ cz p 0 = cz p 1 ∧ cz p 1 = cz p 2)).image
          intVec' ∪
        (univ.filter (fun s => Even (numTrue s) ∧ s 0 = s 1 ∧ s 1 = s 2)).image halfVec) := by
    ext x
    simp only [rootsOf, E6Lattice, E8Lattice, Set.mem_setOf_eq,
      Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨hdisj, hev⟩, h01, h12⟩, hnorm⟩
      rcases hdisj with hInt | hHalf
      · obtain ⟨i, j, a, b, hlt, hx⟩ := intShape x hInt hnorm
        refine Or.inl ⟨(i, j, a, b), ⟨hlt, ?_, ?_⟩, hx.symm⟩
        · have : intVec i j a b 0 = intVec i j a b 1 := by rw [← hx]; exact h01
          simp only [cz, intVec] at this ⊢; exact_mod_cast this
        · have : intVec i j a b 1 = intVec i j a b 2 := by rw [← hx]; exact h12
          simp only [cz, intVec] at this ⊢; exact_mod_cast this
      · obtain ⟨s, hx⟩ := halfShape x hHalf hnorm
        refine Or.inr ⟨s, ⟨(evenSum_halfVec_iff s).1 (hx ▸ hev), ?_, ?_⟩, hx.symm⟩
        · have : halfVec s 0 = halfVec s 1 := by rw [← hx]; exact h01
          exact (halfVec_eq_iff s 0 1).1 this
        · have : halfVec s 1 = halfVec s 2 := by rw [← hx]; exact h12
          exact (halfVec_eq_iff s 1 2).1 this
    · rintro (⟨p, ⟨hlt, hcz01, hcz12⟩, rfl⟩ | ⟨s, ⟨hs, hs01, hs12⟩, rfl⟩)
      · refine ⟨⟨intVec'_mem_rootsOf_E8 p hlt |>.1, ?_, ?_⟩,
          intVec'_mem_rootsOf_E8 p hlt |>.2⟩
        · simp only [intVec', intVec]; exact_mod_cast hcz01
        · simp only [intVec', intVec]; exact_mod_cast hcz12
      · refine ⟨⟨halfVec_mem_rootsOf_E8 s hs |>.1, ?_, ?_⟩,
          halfVec_mem_rootsOf_E8 s hs |>.2⟩
        · rw [halfVec_eq_iff]; exact hs01
        · rw [halfVec_eq_iff]; exact hs12
  have hinj : Set.InjOn intVec'
      ↑(univ.filter (fun p : Idx => p.1 < p.2.1 ∧ cz p 0 = cz p 1 ∧ cz p 1 = cz p 2)) := by
    refine intVec'_injOn.mono ?_
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.1
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint disjoint_int_half,
    Finset.card_image_of_injOn hinj, Finset.card_image_of_injOn halfVec_inj.injOn]
  decide

end Etingof.Problem6_9_2
