import Mathlib

/-!
# Problem 4.12.4: Nonabelian automorphism group forces repeated adjacency eigenvalues

**Problem 4.12.4.** Recall that the adjacency matrix of a graph `Γ` (without multiple
edges) is the matrix in which the `ij`th entry is `1` if the vertices `i` and `j` are
connected with an edge, and zero otherwise. Let `Γ` be a finite graph whose automorphism
group is nonabelian. Show that the adjacency matrix of `Γ` must have repeated eigenvalues.

## Formalization

We work with a finite `SimpleGraph Γ` on a vertex type `W`. Its adjacency matrix
`Γ.adjMatrix ℝ` is a real symmetric matrix, so it is diagonalizable and its eigenvalues
are exactly the roots of its characteristic polynomial. "Has a repeated eigenvalue" is
formalized as: the characteristic polynomial is not squarefree; equivalently (for a
symmetric matrix) some eigenvalue occurs with multiplicity `≥ 2`.

The hypothesis that the automorphism group is nonabelian is expressed as the existence
of two automorphisms that do not commute.

The representation-theoretic content (which is the point of the exercise): each
eigenspace of the adjacency matrix is a real representation of `Aut(Γ)`, and a nonabelian
finite group has a representation of dimension `≥ 2`, forcing some eigenspace to have
dimension `≥ 2`.
-/

open Matrix Polynomial Finset in
/-- If the product `∏ (X - C (d i))` over a finite index set is squarefree, then the
family `d` is injective: a repeated value `d i = d j` (`i ≠ j`) would put the square of
the non-unit factor `X - C (d i)` into the product. -/
theorem Etingof.Problem4_12_4.injective_of_squarefree_prod {W : Type*} [Fintype W]
    {d : W → ℝ} (hsq : Squarefree (∏ i, (X - C (d i)))) : Function.Injective d := by
  classical
  intro i j hdij
  by_contra hne
  have hji : j ≠ i := fun h => hne h.symm
  -- `(X - C (d i))²` divides the product, hence it is a unit, which is impossible.
  have hdvd : (X - C (d i)) * (X - C (d i)) ∣ ∏ k, (X - C (d k)) := by
    refine ⟨∏ k ∈ (univ.erase i).erase j, (X - C (d k)), ?_⟩
    have h1 : (∏ k, (X - C (d k)))
        = (X - C (d i)) * ∏ k ∈ univ.erase i, (X - C (d k)) :=
      (Finset.mul_prod_erase univ _ (mem_univ i)).symm
    have h2 : (∏ k ∈ univ.erase i, (X - C (d k)))
        = (X - C (d j)) * ∏ k ∈ (univ.erase i).erase j, (X - C (d k)) :=
      (Finset.mul_prod_erase (univ.erase i) _ (mem_erase.mpr ⟨hji, mem_univ j⟩)).symm
    rw [h1, h2, ← hdij]
    ring
  exact Polynomial.not_isUnit_X_sub_C (d i) (hsq _ hdvd)

open Matrix in
/-- A matrix commuting with a diagonal matrix whose diagonal entries are pairwise distinct
is itself diagonal (its off-diagonal entries vanish). -/
theorem Etingof.Problem4_12_4.eq_diagonal_of_commute {W : Type*} [Fintype W] [DecidableEq W]
    {d : W → ℝ} (hd : Function.Injective d) {M : Matrix W W ℝ}
    (h : M * diagonal d = diagonal d * M) : M = diagonal (fun i => M i i) := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [diagonal_apply_ne _ hij]
    have hentry := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    -- `hentry : M i j * d j = d i * M i j`
    have hdne : d j - d i ≠ 0 := sub_ne_zero.mpr fun hEq => hij (hd hEq).symm
    have hkey : M i j * (d j - d i) = 0 := by rw [mul_sub, hentry]; ring
    exact (mul_eq_zero.mp hkey).resolve_right hdne

open Matrix Polynomial in
/-- The commutant lemma: if a Hermitian real matrix `A` has squarefree characteristic
polynomial (all eigenvalues simple), then any two matrices commuting with `A` commute with
each other. Diagonalize `A` by a unitary `U`; conjugating by `U` sends everything commuting
with `A` into the (commutative) algebra of diagonal matrices. -/
theorem Etingof.Problem4_12_4.commute_of_commute_isHermitian {W : Type*} [Fintype W]
    [DecidableEq W] {A : Matrix W W ℝ} (hA : A.IsHermitian) (hsq : Squarefree A.charpoly)
    {N₁ N₂ : Matrix W W ℝ} (h₁ : A * N₁ = N₁ * A) (h₂ : A * N₂ = N₂ * A) :
    N₁ * N₂ = N₂ * N₁ := by
  set d : W → ℝ := RCLike.ofReal ∘ hA.eigenvalues with hd_def
  have hinj : Function.Injective d :=
    injective_of_squarefree_prod (by rwa [hA.charpoly_eq] at hsq)
  -- The conjugation `Ψ X = star U * X * U` is a ⋆-algebra automorphism sending `A` to
  -- `diagonal d`.
  set Ψ := Unitary.conjStarAlgAut ℝ (Matrix W W ℝ) (star hA.eigenvectorUnitary) with hΨ_def
  have hΨA : Ψ A = diagonal d := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hdiag : ∀ N : Matrix W W ℝ, A * N = N * A → Ψ N = diagonal (fun i => Ψ N i i) := by
    intro N hN
    apply eq_diagonal_of_commute hinj
    have hcomm : Ψ A * Ψ N = Ψ N * Ψ A := by rw [← map_mul, ← map_mul, hN]
    rw [hΨA] at hcomm
    exact hcomm.symm
  have hd1 := hdiag N₁ h₁
  have hd2 := hdiag N₂ h₂
  have hcomm : Ψ N₁ * Ψ N₂ = Ψ N₂ * Ψ N₁ := by
    rw [hd1, hd2, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i; exact mul_comm _ _
  have : Ψ (N₁ * N₂) = Ψ (N₂ * N₁) := by rw [map_mul, map_mul, hcomm]
  exact Ψ.injective this

open Matrix in
/-- A graph automorphism `g` gives a permutation matrix that commutes with the adjacency
matrix, because `g` preserves adjacency. -/
theorem Etingof.Problem4_12_4.adjMatrix_commute {W : Type*} [Fintype W] [DecidableEq W]
    (Γ : SimpleGraph W) [DecidableRel Γ.Adj] (g : Γ ≃g Γ) :
    Γ.adjMatrix ℝ * g.toEquiv.toPEquiv.toMatrix
      = g.toEquiv.toPEquiv.toMatrix * Γ.adjMatrix ℝ := by
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, SimpleGraph.adjMatrix_apply]
  have hmap2 : ∀ a b : W, Γ.Adj (g.toEquiv a) (g.toEquiv b) ↔ Γ.Adj a b := fun a b => by
    simpa only [← RelIso.coe_fn_toEquiv] using g.map_adj_iff (v := a) (w := b)
  have hiff : Γ.Adj i (g.toEquiv.symm j) ↔ Γ.Adj (g.toEquiv i) j := by
    rw [← hmap2 i (g.toEquiv.symm j), Equiv.apply_symm_apply]
  exact if_congr hiff rfl rfl

/-- **Problem 4.12.4.** If a finite simple graph `Γ` has a nonabelian automorphism group,
then its adjacency matrix has a repeated eigenvalue: the characteristic polynomial (over
`ℝ`) is not squarefree. The automorphism group is `Γ ≃g Γ` (graph isomorphisms of `Γ`
with itself), and "nonabelian" is expressed by exhibiting two non-commuting elements. -/
theorem Etingof.Problem4_12_4 {W : Type*} [Fintype W] [DecidableEq W]
    (Γ : SimpleGraph W) [DecidableRel Γ.Adj]
    (hAut : ∃ σ τ : Γ ≃g Γ, σ * τ ≠ τ * σ) :
    ¬ Squarefree (Γ.adjMatrix ℝ).charpoly := by
  intro hsq
  obtain ⟨σ, τ, hστ⟩ := hAut
  apply hστ
  -- The adjacency matrix is real symmetric, hence Hermitian.
  have hA : (Γ.adjMatrix ℝ).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, SimpleGraph.adjMatrix_apply]
    exact if_congr (Γ.adj_comm j i) rfl rfl
  -- The two permutation matrices commute with the adjacency matrix, hence with each other.
  have hPcomm : σ.toEquiv.toPEquiv.toMatrix * τ.toEquiv.toPEquiv.toMatrix
      = τ.toEquiv.toPEquiv.toMatrix * σ.toEquiv.toPEquiv.toMatrix :=
    Etingof.Problem4_12_4.commute_of_commute_isHermitian hA hsq
      (Etingof.Problem4_12_4.adjMatrix_commute Γ σ)
      (Etingof.Problem4_12_4.adjMatrix_commute Γ τ)
  -- Translate the matrix identity back to the underlying permutations.
  have hEeq : σ.toEquiv.trans τ.toEquiv = τ.toEquiv.trans σ.toEquiv := by
    have hPeq : (σ.toEquiv.trans τ.toEquiv).toPEquiv = (τ.toEquiv.trans σ.toEquiv).toPEquiv := by
      apply PEquiv.toMatrix_injective (α := ℝ)
      rw [Equiv.toPEquiv_trans, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans, PEquiv.toMatrix_trans]
      exact hPcomm
    ext x
    have hx := DFunLike.congr_fun hPeq x
    rw [Equiv.toPEquiv_apply, Equiv.toPEquiv_apply] at hx
    exact Option.some.inj hx
  refine DFunLike.ext _ _ fun x => ?_
  have hxeq := Equiv.ext_iff.mp hEeq x
  simp only [Equiv.trans_apply] at hxeq
  simp only [RelIso.mul_apply, ← RelIso.coe_fn_toEquiv]
  exact hxeq.symm
