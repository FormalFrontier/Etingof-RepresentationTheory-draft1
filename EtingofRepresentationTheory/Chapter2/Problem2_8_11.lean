import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import EtingofRepresentationTheory.Chapter2.Definition2_8_4

/-!
# Problem 2.8.11: Hilbert series of graded algebras

For a `ℤ₊`-graded algebra `A = ⨁ₙ A[n]` with each `A[n]` finite dimensional, the **Hilbert
series** is `h_A(t) = ∑ₙ (dim A[n]) tⁿ`. The problem asks for the Hilbert series of four
graded algebras. We render the book's answers, the closed rational functions, as the
statement. Each is captured two ways: the closed formula for the graded dimension
`dim A[n]` (the coefficient of `tⁿ`), and, where clean, the closed rational form of the
generating function `h_A` as a formal power series identity.

The four answers (Etingof Problem 2.8.11):

* (a) `A = k[x₁,…,x_m]`, graded by degree: `h_A(t) = 1/(1-t)^m`, i.e. `dim A[n] = C(n+m-1, m-1)`.
* (b) `A = k⟨x₁,…,x_m⟩` (free algebra), graded by word length: `h_A(t) = 1/(1-mt)`,
  i.e. `dim A[n] = mⁿ`.
* (c) `A = ⋀_k[x₁,…,x_m]` (exterior algebra), graded by degree: `h_A(t) = (1+t)^m`,
  i.e. `dim A[n] = C(m, n)`.
* (d) `A = P_Q` (path algebra), `deg pᵢ = 0`, `deg a_h = 1`: `dim A[n]` is the number of paths
  of length `n`, i.e. the `(i,j)`-entry of `M_Q^n` summed over `i, j`, where `M_Q` is the
  adjacency matrix. The generating function is `∑ₙ (𝟙ᵀ M_Q^n 𝟙) tⁿ = 𝟙ᵀ (I - t M_Q)⁻¹ 𝟙`.
-/

namespace Etingof.Problem2_8_11

open scoped ExteriorAlgebra

/-! ## Locally finite positive gradings and their Hilbert series -/

/-- The data in the first paragraph of Problem 2.8.11: an internal `ℕ`-grading
`A = ⨁ₙ A[n]`, closed under multiplication, whose pieces are finite-dimensional. -/
structure LocallyFiniteNatGrading (k A : Type*) [Field k] [Ring A] [Algebra k A] where
  /-- The degree-`n` component `A[n]`. -/
  piece : ℕ → Submodule k A
  /-- The components form an internal direct sum equal to all of `A`. -/
  decomposition : DirectSum.IsInternal piece
  /-- Multiplication adds degrees: `A[n] A[m] ⊆ A[n+m]`. -/
  mul_mem : ∀ {n m : ℕ} {x y : A}, x ∈ piece n → y ∈ piece m → x * y ∈ piece (n + m)
  /-- Every homogeneous component is finite-dimensional. -/
  finite : ∀ n, Module.Finite k (piece n)

/-- The Hilbert series `h_A(t) = ∑ₙ dim(A[n])tⁿ` of a locally finite positive grading.
Its coefficients lie in `ℤ`, so the dimension data is not reduced modulo the characteristic of
the ground field. -/
noncomputable def hilbertSeries {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (G : LocallyFiniteNatGrading k A) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    letI : Module.Finite k (G.piece n) := G.finite n
    (Module.finrank k (G.piece n) : ℤ)

@[simp] theorem coeff_hilbertSeries {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (G : LocallyFiniteNatGrading k A) (n : ℕ) :
    PowerSeries.coeff n (hilbertSeries G) =
      letI : Module.Finite k (G.piece n) := G.finite n
      (Module.finrank k (G.piece n) : ℤ) :=
  PowerSeries.coeff_mk _ _

/-! ## (a) Polynomial algebra `k[x₁,…,x_m]` -/

/-- **(a)** The degree-`n` graded piece of `k[x₁,…,x_m]` has dimension `C(n+m-1, n)`, the number
of monomials of degree `n` in `m` variables (`stars and bars`). Equivalently the Hilbert series is
`1/(1-t)^m`.

The book writes the binomial as `C(n+m-1, m-1)`; for `m ≥ 1` this is the same number
(`C(n+m-1, n) = C(n+m-1, m-1)`), but we use the `C(n+m-1, n) = Nat.multichoose m n` form because
it is also correct in the degenerate case `m = 0` (where `k[]` ≅ `k` is concentrated in degree
`0`, so the dimension is `1` at `n = 0` and `0` otherwise). With natural-number subtraction the
literal `C(n+m-1, m-1)` collapses to `C(n-1, 0) = 1` for every `n` at `m = 0`, which is wrong. -/
theorem finrank_homogeneous_mvPolynomial (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin m) k n) = (n + m - 1).choose n := by
  classical
  -- The monomials of degree `n` in `m` variables are the finsupps `Fin m →₀ ℕ` of total sum `n`,
  -- enumerated by `Finset.finsuppAntidiag univ n`.
  set s : Finset (Fin m →₀ ℕ) := (Finset.univ : Finset (Fin m)).finsuppAntidiag n with hs
  have hset : {d : Fin m →₀ ℕ | d.degree = n} = (↑s : Set (Fin m →₀ ℕ)) := by
    ext d
    simp only [Set.mem_setOf_eq, hs, Finset.mem_coe, Finset.mem_finsuppAntidiag,
      Finsupp.degree_eq_sum]
    exact ⟨fun h => ⟨h, Finset.subset_univ _⟩, fun h => h.1⟩
  -- `homogeneousSubmodule` is exactly the span of those monomials, which has a monomial basis.
  have hsub : MvPolynomial.homogeneousSubmodule (Fin m) k n
      = MvPolynomial.restrictSupport k (↑s : Set (Fin m →₀ ℕ)) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hset]
    rfl
  rw [hsub, Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k
    (↑s : Set (Fin m →₀ ℕ))), Nat.card_coe_set_eq, Set.ncard_coe_finset, hs,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin, Nat.add_comm]

/-- **(a)**, generating-function form: the Hilbert series of `k[x₁,…,x_m]` is `1/(1-t)^m`,
expressed as the power-series identity `(1 - t)^m · h_A = 1`, where `h_A = ∑ C(n+m-1, n) tⁿ`.
(See `finrank_homogeneous_mvPolynomial` for why the coefficient is written `C(n+m-1, n)` rather than
the literal `C(n+m-1, m-1)` from the book.) -/
theorem hilbertSeries_mvPolynomial (k : Type*) [Field k] (m : ℕ) :
    (1 - PowerSeries.X : PowerSeries k) ^ m *
      PowerSeries.mk (fun n => ((n + m - 1).choose n : k)) = 1 := by
  rcases m with _ | d
  · -- `m = 0`: `h_A = 1` since `C(n-1, n) = 0` for `n ≥ 1` and `C(0, 0) = 1` at `n = 0`.
    ext l
    rw [pow_zero, one_mul, PowerSeries.coeff_mk]
    rcases l with _ | e
    · simp
    · rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero e),
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  · -- `m = d + 1`: this is the inverse `(1 - X)^(d+1) · invOneSubPow = 1` from Mathlib, after
    -- matching coefficients `C(d + n, d) = C(n + (d+1) - 1, n)`.
    have hval : (PowerSeries.invOneSubPow k (d + 1)).val
        = PowerSeries.mk (fun l => ((l + (d + 1) - 1).choose l : k)) := by
      rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
      apply PowerSeries.ext
      intro l
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      congr 1
      -- `C(d + l, d) = C(l + (d+1) - 1, l)`: simplify the index and apply `choose` symmetry.
      have harg : l + (d + 1) - 1 = d + l := by omega
      rw [harg, ← Nat.choose_symm (Nat.le_add_left l d)]
      congr 1
      omega
    have key := (PowerSeries.invOneSubPow k (d + 1)).inv_val
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, hval] at key
    exact key

/-! ## (b) Free algebra `k⟨x₁,…,x_m⟩` -/

/-- The canonical word-basis realization of the free algebra: `k⟨x₁,…,x_m⟩` is the monoid
algebra on words in `m` letters. -/
noncomputable def freeAlgebraWordEquiv (k : Type*) [Field k] (m : ℕ) :
    FreeAlgebra k (Fin m) ≃ₐ[k] MonoidAlgebra k (FreeMonoid (Fin m)) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := Fin m)

/-- The word-length-`n` homogeneous component in the canonical word-basis realization of the
free algebra. -/
noncomputable def freeAlgebraDegreePiece (k : Type*) [Field k] (m n : ℕ) :
    Submodule k (MonoidAlgebra k (FreeMonoid (Fin m))) :=
  Submodule.map (MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap
    (Finsupp.supported k k {w : FreeMonoid (Fin m) | w.length = n})

/-- **(b)** The number of words of length `n` in `m` letters is `mⁿ`; this is the dimension of the
length-`n` graded piece of the free algebra `k⟨x₁,…,x_m⟩` (whose basis is the set of words).
Equivalently the Hilbert series is `1/(1-mt)`. -/
theorem card_words_length (m n : ℕ) :
    Nat.card {l : List (Fin m) // l.length = n} = m ^ n := by
  -- A length-`n` word over `Fin m` is exactly a `List.Vector (Fin m) n`, equivalent to
  -- `Fin n → Fin m`, of which there are `mⁿ`.
  have e : {l : List (Fin m) // l.length = n} ≃ (Fin n → Fin m) :=
    Equiv.vectorEquivFin (Fin m) n
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- **(b), actual graded-piece dimension.** Via `freeAlgebraWordEquiv`, the degree-`n` piece of
`k⟨x₁,…,x_m⟩` is `freeAlgebraDegreePiece`, and its dimension is `mⁿ`. -/
theorem finrank_freeAlgebra_degreePiece (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (freeAlgebraDegreePiece k m n) = m ^ n := by
  let b : Module.Basis {w : FreeMonoid (Fin m) // w.length = n} k
      (freeAlgebraDegreePiece k m n) :=
    (Finsupp.basisSingleOne.map
      (Finsupp.supportedEquivFinsupp (R := k)
        {w : FreeMonoid (Fin m) | w.length = n}).symm).map
      ((MonoidAlgebra.coeffLinearEquiv k).symm.submoduleMap
        (Finsupp.supported k k {w : FreeMonoid (Fin m) | w.length = n}))
  calc
    Module.finrank k (freeAlgebraDegreePiece k m n) =
        Nat.card {w : FreeMonoid (Fin m) // w.length = n} :=
      Module.finrank_eq_nat_card_basis b
    _ = m ^ n := card_words_length m n

/-- **(b)**, generating-function form: the Hilbert series of `k⟨x₁,…,x_m⟩` is `1/(1-mt)`,
expressed as the power-series identity `(1 - m·t) · h_A = 1`. -/
theorem hilbertSeries_freeAlgebra (k : Type*) [Field k] (m : ℕ) :
    (1 - (m : ℕ) • PowerSeries.X : PowerSeries k) *
      PowerSeries.mk (fun n => ((m ^ n : ℕ) : k)) = 1 := by
  -- Geometric series `(1 - m·X)·∑ mⁿ Xⁿ = 1`, checked coefficient by coefficient.
  ext d
  rw [sub_mul, one_mul, smul_mul_assoc, map_sub, map_nsmul, PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  rcases d with _ | e
  · -- constant coefficient: `m⁰ - m·(coeff₀ (X·h)) = 1 - 0 = 1`
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · -- coefficient of `t^(e+1)`: `m^(e+1) - m·m^e = 0`
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, nsmul_eq_mul]
    push_cast [pow_succ]
    ring

/-! ## (c) Exterior (Grassmann) algebra `⋀_k[x₁,…,x_m]` -/

/-- **(c)** The degree-`n` graded piece of the exterior algebra on `m` generators is the `n`-th
exterior power of the `m`-dimensional space, of dimension `C(m, n)`. Equivalently the Hilbert
series is `(1+t)^m`. -/
theorem finrank_exteriorPower (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (⋀[k]^n (Fin m → k)) = m.choose n := by
  -- `⋀^n` of a rank-`m` free module has rank `C(m, n)`; here `finrank k (Fin m → k) = m`.
  rw [exteriorPower.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- **(c)**, generating-function form: the Hilbert series of the exterior algebra on `m`
generators is the polynomial `(1+t)^m`. -/
theorem hilbertSeries_exteriorAlgebra (k : Type*) [Field k] (m : ℕ) :
    PowerSeries.mk (fun n => ((m.choose n : ℕ) : k)) = (1 + PowerSeries.X : PowerSeries k) ^ m := by
  -- Coerce the polynomial identity `((1 + X)^m).coeff n = C(m, n)` to power series and match
  -- coefficients: `(1 + X)^m` as a power series is the coercion of the polynomial `(1 + X)^m`.
  have hcoe : ((1 + PowerSeries.X : PowerSeries k) ^ m) =
      ((((1 + Polynomial.X) ^ m : Polynomial k) : PowerSeries k)) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [hcoe]
  ext n
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-! ## (d) Path algebra `P_Q` -/

/-- The degree-`n` component of the path algebra: the subspace supported on basis paths of length
`n`. The book-facing opposite algebra has the same underlying graded vector space. -/
noncomputable def pathAlgebraDegreePiece (k : Type*) [Field k] (Q : Type*) [Quiver Q]
    [DecidableEq Q] (n : ℕ) : Submodule k (Etingof.PathAlgebra k Q) :=
  Finsupp.supported k k {p : Etingof.QuiverPathIndex Q | p.2.2.length = n}

/-- The adjacency matrix of a finite quiver `Q`: the `(i,j)`-entry is the number of arrows
`i ⟶ j`. -/
def adjacencyMatrix (Q : Type*) [Quiver Q] [∀ i j : Q, Fintype (i ⟶ j)] :
    Matrix Q Q ℕ :=
  fun i j => Fintype.card (i ⟶ j)

/-- A path of length `n + 1` from `i` to `j` decomposes uniquely as a length-`n` path
`i ⟶* b` followed by a final arrow `b ⟶ j` (matching the `Matrix.mul_apply` decomposition of
`M_Q ^ (n+1) = M_Q ^ n * M_Q`). -/
def pathSuccEquiv {Q : Type*} [Quiver Q] (i j : Q) (n : ℕ) :
    {p : Quiver.Path i j // p.length = n + 1} ≃
      Σ b : Q, {p : Quiver.Path i b // p.length = n} × (b ⟶ j) where
  toFun p := by
    obtain ⟨p, h⟩ := p
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => exact ⟨_, ⟨p', by rw [Quiver.Path.length_cons] at h; omega⟩, e⟩
  invFun x := ⟨x.2.1.1.cons x.2.2, by rw [Quiver.Path.length_cons, x.2.1.2]⟩
  left_inv p := by
    obtain ⟨p, h⟩ := p
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => rfl
  right_inv x := by
    obtain ⟨b, ⟨p', hp'⟩, e⟩ := x
    rfl

/-- The set of paths of a fixed length between two vertices of a finite quiver is finite. -/
instance instFinitePathLen {Q : Type*} [Quiver Q] [Finite Q] [∀ i j : Q, Finite (i ⟶ j)]
    (i j : Q) (n : ℕ) : Finite {p : Quiver.Path i j // p.length = n} := by
  induction n generalizing j with
  | zero =>
    haveI : Subsingleton {p : Quiver.Path i j // p.length = 0} := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨p, hp⟩ := a
      obtain ⟨q, hq⟩ := b
      have hij : i = j := Quiver.Path.eq_of_length_zero p hp
      subst hij
      rw [Subtype.mk_eq_mk, Quiver.Path.eq_nil_of_length_zero p hp,
        Quiver.Path.eq_nil_of_length_zero q hq]
    exact Finite.of_injective (fun _ => (0 : Fin 1)) fun a b _ => Subsingleton.elim a b
  | succ n ih =>
    haveI : ∀ b : Q, Finite {p : Quiver.Path i b // p.length = n} := ih
    exact Finite.of_equiv _ (pathSuccEquiv i j n).symm

/-- **(d)** The number of paths of length `n` from `i` to `j` in a finite quiver equals the
`(i,j)`-entry of the `n`-th power of the adjacency matrix. This is the graded-piece dimension of
the path algebra: the closed answer to the Hilbert series in terms of `M_Q`. -/
theorem card_paths_length_eq_adjacencyMatrix_pow (Q : Type*) [Quiver Q] [Fintype Q]
    [DecidableEq Q] [∀ i j : Q, Fintype (i ⟶ j)] (i j : Q) (n : ℕ) :
    Nat.card {p : Quiver.Path i j // p.length = n} = (adjacencyMatrix Q ^ n) i j := by
  induction n generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      haveI : Nonempty {p : Quiver.Path i i // p.length = 0} :=
        ⟨⟨Quiver.Path.nil, Quiver.Path.length_nil⟩⟩
      haveI : Subsingleton {p : Quiver.Path i i // p.length = 0} :=
        ⟨fun a b => Subtype.ext ((Quiver.Path.eq_nil_of_length_zero _ a.2).trans
          (Quiver.Path.eq_nil_of_length_zero _ b.2).symm)⟩
      exact Nat.card_unique
    · rw [if_neg h]
      haveI : IsEmpty {p : Quiver.Path i j // p.length = 0} :=
        ⟨fun p => h (Quiver.Path.eq_of_length_zero p.1 p.2)⟩
      exact Nat.card_of_isEmpty
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Nat.card_congr (pathSuccEquiv i j n), Nat.card_sigma]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.card_prod, ih b, Nat.card_eq_fintype_card]
    rfl

/-- **(d)** The dimension of the degree-`n` graded piece of the path algebra `P_Q` is the total
number of paths of length `n`, i.e. the sum of all entries of `M_Q^n`. -/
theorem dim_pathAlgebra_degree (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
    [∀ i j : Q, Fintype (i ⟶ j)] (n : ℕ) :
    ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n}
      = ∑ i : Q, ∑ j : Q, (adjacencyMatrix Q ^ n) i j := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact card_paths_length_eq_adjacencyMatrix_pow Q i j n

/-- **(d), actual graded-piece dimension.** The degree-`n` component of `P_Q` has as basis all
length-`n` oriented paths, so its dimension is their total number. -/
theorem finrank_pathAlgebra_degree (k : Type*) [Field k]
    (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
    [∀ i j : Q, Finite (i ⟶ j)] (n : ℕ) :
    Module.finrank k (pathAlgebraDegreePiece k Q n) =
      ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n} := by
  let T := Σ i : Q, Σ j : Q, {p : Quiver.Path i j // p.length = n}
  let e : {p : QuiverPathIndex Q // p.2.2.length = n} ≃ T := {
    toFun p := ⟨p.1.1, p.1.2.1, ⟨p.1.2.2, p.2⟩⟩
    invFun p := ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
    left_inv p := by rcases p with ⟨⟨i, j, p⟩, hp⟩; rfl
    right_inv p := by rcases p with ⟨i, j, p, hp⟩; rfl }
  let b : Module.Basis {p : QuiverPathIndex Q // p.2.2.length = n} k
      (pathAlgebraDegreePiece k Q n) :=
    Finsupp.basisSingleOne.map
      (Finsupp.supportedEquivFinsupp (R := k)
        {p : QuiverPathIndex Q | p.2.2.length = n}).symm
  calc
    Module.finrank k (pathAlgebraDegreePiece k Q n) =
        Nat.card {p : QuiverPathIndex Q // p.2.2.length = n} :=
      Module.finrank_eq_nat_card_basis b
    _ = Nat.card T := Nat.card_congr e
    _ = ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n} := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.card_sigma]

/-! ### (d), generating-function form

The coefficient computations above say that `dim P_Q[n] = 𝟙ᵀ M_Q^n 𝟙`. The book's answer is the
closed form of the generating function they assemble into,

`∑ₙ (𝟙ᵀ M_Q^n 𝟙) tⁿ = 𝟙ᵀ (I - t M_Q)⁻¹ 𝟙`,

an identity of formal power series. We prove it by exhibiting the matrix of power series
`resolvent Q i j = ∑ₙ (M_Q^n) i j tⁿ` as a genuine two-sided inverse of `I - t M_Q` over
`k⟦t⟧`, so the `(I - t M_Q)⁻¹` on the right is `Matrix.inv` of an honestly invertible matrix and
not a junk value. -/

section HilbertSeries

variable (k : Type*) [CommRing k] (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

open PowerSeries
open scoped Matrix

/-- The adjacency matrix of `Q` viewed over the power-series ring `k⟦t⟧`, so that `t • adjacencyPS`
is the matrix `t M_Q` appearing in the book's answer. -/
noncomputable def adjacencyPS : Matrix Q Q (PowerSeries k) :=
  (adjacencyMatrix Q).map fun a => C (a : k)

omit [Fintype Q] [DecidableEq Q] in
@[simp]
theorem adjacencyPS_apply (i j : Q) :
    adjacencyPS k Q i j = C ((adjacencyMatrix Q i j : ℕ) : k) :=
  rfl

/-- The resolvent `(I - t M_Q)⁻¹` written out as a matrix of power series: its `(i,j)` entry is
`∑ₙ (M_Q^n) i j tⁿ`, the generating function counting paths from `i` to `j` by length. -/
noncomputable def resolvent : Matrix Q Q (PowerSeries k) :=
  fun i j => mk fun n => (((adjacencyMatrix Q ^ n) i j : ℕ) : k)

@[simp]
theorem coeff_resolvent (i j : Q) (n : ℕ) :
    coeff n (resolvent k Q i j) = (((adjacencyMatrix Q ^ n) i j : ℕ) : k) :=
  coeff_mk n _

/-- Multiplying the resolvent by the adjacency matrix shifts the path-counting coefficients by
one: the `tᵈ`-coefficient of `(M_Q · resolvent) i j` counts paths of length `d + 1`. -/
theorem coeff_adjacencyPS_mul_resolvent (i j : Q) (d : ℕ) :
    coeff d ((adjacencyPS k Q * resolvent k Q) i j)
      = (((adjacencyMatrix Q ^ (d + 1)) i j : ℕ) : k) := by
  rw [Matrix.mul_apply, map_sum, pow_succ', Matrix.mul_apply]
  push_cast
  exact Finset.sum_congr rfl fun b _ => by rw [adjacencyPS_apply, coeff_C_mul, coeff_resolvent]

/-- The geometric-series identity `(I - t M_Q) · (∑ₙ M_Q^n tⁿ) = I` over `k⟦t⟧`. -/
theorem one_sub_smul_adjacencyPS_mul_resolvent :
    (1 - (X : PowerSeries k) • adjacencyPS k Q) * resolvent k Q = 1 := by
  have key : (1 - (X : PowerSeries k) • adjacencyPS k Q) * resolvent k Q
      = resolvent k Q - (X : PowerSeries k) • (adjacencyPS k Q * resolvent k Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [key]
  ext i j d
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_resolvent]
  rcases d with _ | e
  · rw [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul, sub_zero, pow_zero,
      Matrix.one_apply, Matrix.one_apply]
    split <;> simp
  · rw [coeff_succ_X_mul, coeff_adjacencyPS_mul_resolvent, sub_self, Matrix.one_apply]
    split <;> simp

/-- `I - t M_Q` is invertible over `k⟦t⟧` (its determinant is a unit). -/
theorem isUnit_det_one_sub_smul_adjacencyPS :
    IsUnit (1 - (X : PowerSeries k) • adjacencyPS k Q).det :=
  Matrix.isUnit_det_of_right_inverse (one_sub_smul_adjacencyPS_mul_resolvent k Q)

/-- The resolvent really is the inverse of `I - t M_Q`, so writing `(I - t M_Q)⁻¹` below is
legitimate. -/
theorem inv_one_sub_smul_adjacencyPS :
    (1 - (X : PowerSeries k) • adjacencyPS k Q)⁻¹ = resolvent k Q :=
  Matrix.inv_eq_right_inv (one_sub_smul_adjacencyPS_mul_resolvent k Q)

/-- `(I - t M_Q) · (I - t M_Q)⁻¹ = I`; recorded so that the inverse is visibly two-sided. -/
theorem resolvent_mul_one_sub_smul_adjacencyPS :
    resolvent k Q * (1 - (X : PowerSeries k) • adjacencyPS k Q) = 1 :=
  mul_eq_one_comm.mp (one_sub_smul_adjacencyPS_mul_resolvent k Q)

omit [Quiver Q] [DecidableEq Q] [∀ i j : Q, Fintype (i ⟶ j)] in
/-- `𝟙ᵀ A 𝟙` is the sum of all entries of `A`. -/
theorem one_vecMul_dotProduct_one (A : Matrix Q Q (PowerSeries k)) :
    (fun _ => 1) ᵥ* A ⬝ᵥ (fun _ => 1) = ∑ i : Q, ∑ j : Q, A i j := by
  simp only [Matrix.vecMul, dotProduct, one_mul, mul_one]
  exact Finset.sum_comm

/-- **(d)**, generating-function form. The Hilbert series of the path algebra `P_Q`, whose
degree-`n` coefficient is the number of paths of length `n` in `Q`, is `𝟙ᵀ (I - t M_Q)⁻¹ 𝟙`:

`∑ₙ (∑_{i,j} #{paths i ⟶ j of length n}) tⁿ = 𝟙ᵀ (I - t M_Q)⁻¹ 𝟙`.

This is the closed rational form asked for in part (d); `dim_pathAlgebra_degree` and
`card_paths_length_eq_adjacencyMatrix_pow` supply the coefficients. -/
theorem hilbertSeries_pathAlgebra :
    (mk fun n => ((∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n} : ℕ) : k))
      = (fun _ => 1) ᵥ* (1 - (X : PowerSeries k) • adjacencyPS k Q)⁻¹ ⬝ᵥ (fun _ => 1) := by
  rw [one_vecMul_dotProduct_one, inv_one_sub_smul_adjacencyPS]
  ext d
  rw [coeff_mk, dim_pathAlgebra_degree, map_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ => (coeff_resolvent k Q i j d).symm

/-- **(d)**, generating-function form, stated directly in terms of the adjacency matrix:

`∑ₙ (𝟙ᵀ M_Q^n 𝟙) tⁿ = 𝟙ᵀ (I - t M_Q)⁻¹ 𝟙`. -/
theorem hilbertSeries_pathAlgebra_adjacencyMatrix :
    (mk fun n => ((∑ i : Q, ∑ j : Q, (adjacencyMatrix Q ^ n) i j : ℕ) : k))
      = (fun _ => 1) ᵥ* (1 - (X : PowerSeries k) • adjacencyPS k Q)⁻¹ ⬝ᵥ (fun _ => 1) := by
  rw [← hilbertSeries_pathAlgebra k Q]
  congr 1
  funext n
  rw [dim_pathAlgebra_degree]

end HilbertSeries

end Etingof.Problem2_8_11

-- The leaf names follow Mathlib conventions; the underscore comes solely from the stable
-- book-number namespace `Problem2_8_11`, which is part of this project's public API.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_8_11.LocallyFiniteNatGrading.piece
  Etingof.Problem2_8_11.hilbertSeries Etingof.Problem2_8_11.freeAlgebraWordEquiv
  Etingof.Problem2_8_11.freeAlgebraDegreePiece Etingof.Problem2_8_11.pathAlgebraDegreePiece
  Etingof.Problem2_8_11.adjacencyMatrix Etingof.Problem2_8_11.pathSuccEquiv
  Etingof.Problem2_8_11.adjacencyPS Etingof.Problem2_8_11.resolvent
