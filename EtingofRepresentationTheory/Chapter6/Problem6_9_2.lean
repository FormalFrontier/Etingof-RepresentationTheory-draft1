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

/-- **(a)** The `αᵢ` are `ℤ`-linearly independent. -/
theorem α_linearIndependent (c : Fin 8 → ℤ)
    (h : (∑ i, (c i : ℚ) • α i) = 0) : c = 0 := by
  sorry

/-- **(a)** The `αᵢ` span `L` over `ℤ`: every lattice vector is a `ℤ`-combination
of the `αᵢ`, and every `ℤ`-combination lies in `L`. Together with
`α_linearIndependent`, this says the `αᵢ` are a `ℤ`-basis of `L`. -/
theorem α_isBasis :
    (∀ x ∈ E8Lattice, ∃ c : Fin 8 → ℤ, x = ∑ i, (c i : ℚ) • α i) ∧
    (∀ c : Fin 8 → ℤ, (∑ i, (c i : ℚ) • α i) ∈ E8Lattice) := by
  sorry

/-! ## Part (b): the roots form a root system of type `E₈` -/

/-- The Gram matrix `⟪αᵢ, αⱼ⟫` of the simple roots, as an adjacency-style matrix
`gramAdj i j = -⟪αᵢ, αⱼ⟫` for `i ≠ j` (and `0` on the diagonal). -/
def gramAdj (i j : Fin 8) : ℤ :=
  if i = j then 0 else -(inner (α i) (α j)).num

/-- **(b)** Each `αᵢ` is a root: `⟪αᵢ, αᵢ⟫ = 2`. -/
theorem α_norm_two (i : Fin 8) : inner (α i) (α i) = 2 := by
  sorry

/-- **(b)** The roots are simply laced: distinct simple roots have inner product
`0` or `-1`. -/
theorem α_inner_offdiag (i j : Fin 8) (h : i ≠ j) :
    inner (α i) (α j) = 0 ∨ inner (α i) (α j) = -1 := by
  sorry

/-- **(b)** The Gram matrix of the `αᵢ` is the Cartan matrix of a Dynkin diagram
of **type `E₈`**: it is positive definite and graph-isomorphic to the standard
`E₈` adjacency matrix. Hence the roots in `L` form a root system of type `E₈`. -/
theorem α_gram_is_E8 :
    IsDynkinDiagram 8 gramAdj ∧
    ∃ σ : Fin 8 ≃ Fin 8, ∀ i j, gramAdj (σ i) (σ j) = DynkinType.E8.adj i j := by
  sorry

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
