import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Scalar-matrix action on `GL_N` weight spaces

The scalar matrix `t • 1 ∈ GL_N` is the product of the `N` torus generators
`diagUnit i t`. On the weight space `M_μ` of a `GL_N`-representation it therefore
acts as multiplication by `t ^ (∑ i, μ i)`.

This is the operational core of "homogeneous of degree `n`": if every nonzero
weight space of `M` has `∑ μ = n` (and the weight spaces span `M`), then
`M.ρ (scalarUnit t) = t ^ n • id`, which is exactly the homogeneity hypothesis
consumed by the polynomial-rep embedding `polynomialRep_embeds_in_tensorPower'`
(Schur-Weyl, issues #2482 / #4598).

Products over `Fin N` are taken with `List` (the ambient monoids `GL_N` and
`Module.End k M` are non-commutative, so `Finset.prod` does not apply); the
torus generators do commute, so the order is immaterial for the value.

## Main results

* `Etingof.scalarUnit` — the scalar matrix `t • 1`, as `∏ i, diagUnit i t`.
* `Etingof.scalarUnit_val` — its underlying matrix is `t • 1`.
* `Etingof.rho_scalarUnit_apply_of_mem_glWeightSpace` — `M.ρ (scalarUnit t) v =
  t ^ (∑ i, μ i) • v` for `v ∈ M_μ`.
-/

open Matrix

namespace Etingof

variable {k : Type*} [Field k] {N : ℕ}

/-- The scalar matrix `t • 1 ∈ GL_N(k)`, realized as the product of the `N`
maximal-torus generators `diagUnit i t`. -/
noncomputable def scalarUnit (k : Type*) [Field k] (N : ℕ) (t : kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k :=
  ((List.finRange N).map (fun i => diagUnit k N i t)).prod

/-- A list-product of diagonal matrices is the diagonal of the pointwise
list-product of the diagonals. -/
private lemma listProd_diagonal (l : List (Fin N)) (d : Fin N → Fin N → k) :
    (l.map (fun i => Matrix.diagonal (d i))).prod
      = Matrix.diagonal (fun j => (l.map (fun i => d i j)).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal]
    congr 1

/-- The underlying matrix of `scalarUnit t` is the scalar matrix `t • 1`. -/
lemma scalarUnit_val (t : kˣ) :
    (scalarUnit k N t).val = (t : k) • (1 : Matrix (Fin N) (Fin N) k) := by
  classical
  rw [scalarUnit, ← Units.coeHom_apply, map_list_prod, List.map_map]
  -- The mapped list is the list of underlying diagonal matrices.
  have hmap : ((List.finRange N).map (Units.coeHom (Matrix (Fin N) (Fin N) k) ∘
        fun i => diagUnit k N i t)) =
      (List.finRange N).map (fun i =>
        Matrix.diagonal (Function.update (1 : Fin N → k) i (t : k))) := by
    rfl
  rw [hmap, listProd_diagonal]
  -- Each diagonal entry's list-product is `t`.
  have hcol : ∀ j : Fin N,
      ((List.finRange N).map
        (fun i => Function.update (1 : Fin N → k) i (t : k) j)).prod = (t : k) := by
    intro j
    rw [← Fin.prod_univ_def]
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hij
      rw [Function.update_of_ne (fun h => hij h.symm)]
      rfl
    · intro hj; exact absurd (Finset.mem_univ j) hj
  simp only [hcol]
  rw [Matrix.smul_one_eq_diagonal]

variable [IsAlgClosed k]
  (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))

/-- A vector of the weight space `M_μ` is a `t ^ μ i` eigenvector of the
torus generator `diagUnit i t`. (Extracted from the `iInf` defining
`glWeightSpace`; mirrors `glWeightSpace_le_maxGenEigenspace`.) -/
lemma rho_diagUnit_apply_of_mem_glWeightSpace
    {μ : Fin N → ℕ} {i : Fin N} {t : kˣ} {v : M}
    (hv : v ∈ glWeightSpace k N M μ) :
    M.ρ (diagUnit k N i t) v = ((t : k) ^ μ i) • v := by
  have h1 : glWeightSpace k N M μ ≤ ⨅ (s : kˣ),
      LinearMap.ker (M.ρ (diagUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ i
  have h2 : (⨅ (s : kˣ),
      LinearMap.ker (M.ρ (diagUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id)) ≤
      LinearMap.ker (M.ρ (diagUnit k N i t) - ((t : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ t
  have hker := LinearMap.mem_ker.mp (h2 (h1 hv))
  rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hker

/-- A list-product of endomorphisms, each scaling `v` by `c i`, scales `v` by
the list-product of the `c i`. (The line `⟨v⟩` is invariant under each factor.) -/
private lemma listProd_endo_apply_smul {ι : Type*} (l : List ι)
    (A : ι → Module.End k M) (c : ι → k) (v : M)
    (h : ∀ i ∈ l, A i v = c i • v) :
    (l.map A).prod v = (l.map c).prod • v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl : ∀ i ∈ l, A i v = c i • v := fun i hi => h i (by simp [hi])
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih hl, map_smul,
      h a (by simp), smul_smul, List.map_cons, List.prod_cons, mul_comm]

/-- **Scalar matrix acts by `t ^ (∑ μ)` on the weight space `M_μ`.**
The scalar `t • 1 ∈ GL_N` acts on a weight-`μ` vector by `t ^ (∑ i, μ i)`. -/
lemma rho_scalarUnit_apply_of_mem_glWeightSpace
    {μ : Fin N → ℕ} {t : kˣ} {v : M}
    (hv : v ∈ glWeightSpace k N M μ) :
    M.ρ (scalarUnit k N t) v = ((t : k) ^ (∑ i, μ i)) • v := by
  rw [scalarUnit, map_list_prod, List.map_map]
  simp only [Function.comp_def]
  rw [listProd_endo_apply_smul M (List.finRange N) (fun i => M.ρ (diagUnit k N i t))
    (fun i => (t : k) ^ μ i) v
    (fun i _ => rho_diagUnit_apply_of_mem_glWeightSpace M hv)]
  congr 1
  rw [← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]

end Etingof
