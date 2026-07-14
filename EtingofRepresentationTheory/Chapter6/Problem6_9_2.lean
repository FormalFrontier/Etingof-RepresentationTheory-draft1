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
    show gramAdj (σ.toFun i) (σ.toFun j) = _
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

/-! ## Part (d): the root counts `72, 126, 240` -/

/-- **(d)** `E₈` has `240` roots. -/
theorem E8_root_count : (rootsOf E8Lattice).ncard = 240 := by
  sorry

/-- **(d)** `E₇` has `126` roots. -/
theorem E7_root_count : (rootsOf E7Lattice).ncard = 126 := by
  sorry

/-- **(d)** `E₆` has `72` roots. -/
theorem E6_root_count : (rootsOf E6Lattice).ncard = 72 := by
  sorry

end Etingof.Problem6_9_2
