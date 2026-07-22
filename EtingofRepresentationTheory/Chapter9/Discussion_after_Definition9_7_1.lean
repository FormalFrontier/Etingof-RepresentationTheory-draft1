import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import EtingofRepresentationTheory.Chapter9.Introduction_9_7
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basis

universe w u v

/-!
# Discussion after Definition 9.7.1: the Cartan matrix and `dim B_𝐧`

Etingof, in the discussion following Definition 9.7.1 (page 220), records:

> Note that the dimension of `B_𝐧` is `∑ c_{ij} n_i n_j`, where `(c_{ij})` is the Cartan
> matrix of `𝒞`.

Here `B_𝐧 = End(P_𝐧)ᵒᵖ` is the basic algebra attached to the projective generator
`P_𝐧 = ⊕_i n_i P_i` (Theorem 9.6.4 / §9.7), and the **Cartan matrix** of the finite abelian
category `𝒞` is defined representation-theoretically by

`c_{ij} = dim_k Hom(P_i, P_j)`.

This file formalizes that dimension formula. We work with the family `P : ι → 𝒞` of
indecomposable projectives (as in `Introduction_9_7`, where the multiplicity biproduct
`Etingof.multBiproduct P n = ⊕_i n_i P_i` is already defined), and prove

`Module.finrank k ((End (multBiproduct P n))ᵐᵒᵖ) = ∑ i, ∑ j, cartanEntry k P i j * n i * n j`.

The proof is the elementary one indicated by Etingof:

* As a `k`-vector space `(End P_𝐧)ᵐᵒᵖ ≅ End P_𝐧 = Hom(P_𝐧, P_𝐧)` (the opposite algebra has
  the same underlying `k`-module).
* `Hom(⊕_p P_{p}, ⊕_q P_{q}) ≅ ∏_{p,q} Hom(P_p, P_q)` as `k`-vector spaces (a morphism of
  biproducts is a matrix of components; this is `k`-linear), so by additivity of `finrank`
  over finite products `dim End P_𝐧 = ∑_{p,q} dim Hom(P_{p}, P_{q})`.
* Re-indexing the biproduct index `Σ i, Fin (n i)` collapses the double sum to
  `∑_i ∑_j n_i n_j c_{ij}`.

Hom-finiteness of `P_i ⟶ P_j` is supplied by the §9.6 groundwork
(`Etingof.IsFiniteAbelianCategoryOverField.finiteDimensional_hom`).

Etingof continues:

> In particular, the algebra `B = B_𝐧` with the smallest possible dimension, `∑ c_{ij}`,
> corresponds to the case when all `n_i = 1`, i.e., to the projective generator `P = ⊕_i P_i`.
> It is easy to see that this algebra is the only one of the `B_𝐧` for which
> `B_𝐧 / Rad(B_𝐧) = ⊕_i Mat_{n_i}(k)` is commutative.

This file also formalizes these two "minimal basic algebra" claims:

* **Dimension is minimized at `𝐧 = (1,…,1)`.** With `c_{ij} ≥ 0` (a `finrank`, hence a `ℕ`),
  `c_{ii} ≥ 1` (the identity spans a line in `End(P_i)`), and every multiplicity `n_i ≥ 1`,
  the dimension `∑ c_{ij} n_i n_j` is at least `∑ c_{ij}`
  (`Etingof.sum_cartan_le_finrank_cartanAlgebra`), with equality **iff** every `n_i = 1`
  (`Etingof.finrank_cartanAlgebra_eq_sum_cartan_iff`). The diagonal term `c_{ii} n_i^2`
  strictly grows once any `n_i ≥ 2`.

* **Commutativity of the semisimple quotient.** The Wedderburn quotient
  `B_𝐧 / Rad(B_𝐧) ≅ ⊕_i Mat_{n_i}(k)` is commutative **iff** every `n_i = 1`, because a
  matrix algebra `Mat_{n_i}(k)` is commutative iff `n_i ≤ 1` (elementary matrices `E_{ab}`,
  `E_{ba}` fail to commute once there are two indices). We model the quotient by its
  Wedderburn form `∀ i, Matrix (Fin (n i)) (Fin (n i)) k` and prove the criterion directly
  (`Etingof.semisimpleQuotient_comm_iff`).
-/

open CategoryTheory CategoryTheory.Limits Module

namespace Etingof

section BiproductHom

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
variable {J : Type*} [Finite J] {K : Type*} [Finite K] (f : J → C) (g : K → C)

/-- A morphism between biproducts is its matrix of components, `k`-linearly:
`(⊕ⱼ fⱼ ⟶ ⊕ₖ gₖ) ≃ₗ[k] ∏ⱼ ∏ₖ (fⱼ ⟶ gₖ)`. The component map `m ↦ ιⱼ ≫ m ≫ πₖ` is
`k`-linear in a `k`-linear category, and `biproduct.matrix`/`biproduct.components`
witness the bijection. -/
noncomputable def biproductHomLinearEquiv :
    (⨁ f ⟶ ⨁ g) ≃ₗ[k] ∀ (j : J) (l : K), (f j ⟶ g l) where
  toFun m := fun j l => biproduct.ι f j ≫ m ≫ biproduct.π g l
  map_add' m m' := by
    funext j l; simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r m := by
    funext j l; simp [Linear.comp_smul, Linear.smul_comp]
  invFun M := biproduct.desc fun j => biproduct.lift fun l => M j l
  left_inv m := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro l
    simp
  right_inv M := by
    funext j l
    simp

/-- **Additivity of `finrank` over a biproduct Hom space.** In a `k`-linear category with
finite biproducts, if every `Hom(fⱼ, gₖ)` is finite dimensional then
`dim_k Hom(⊕ⱼ fⱼ, ⊕ₖ gₖ) = ∑ⱼ ∑ₖ dim_k Hom(fⱼ, gₖ)`. -/
theorem finrank_biproduct_hom [Fintype J] [Fintype K]
    (hfin : ∀ (j : J) (l : K), FiniteDimensional k (f j ⟶ g l)) :
    finrank k (⨁ f ⟶ ⨁ g) = ∑ j, ∑ l, finrank k (f j ⟶ g l) := by
  haveI : ∀ (j : J) (l : K), Module.Finite k (f j ⟶ g l) := hfin
  rw [(biproductHomLinearEquiv f g (k := k)).finrank_eq, Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Module.finrank_pi_fintype k]

end BiproductHom

section Cartan

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C] [Linear k C]
  [IsFiniteAbelianCategoryOverField k C] [HasFiniteBiproducts C]
variable {ι : Type v} [Fintype ι]

/-- The **representation-theoretic Cartan matrix** of a finite abelian category, evaluated on
the family `P : ι → 𝒞` of indecomposable projectives: `c_{ij} = dim_k Hom(P_i, P_j)`
(Etingof, discussion after Definition 9.7.1). -/
noncomputable def cartanEntry (k : Type w) [Field k] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear k C] (P : ι → C) (i j : ι) : ℕ :=
  finrank k (P i ⟶ P j)

/-- Re-indexing helper: a sum of an `ι`-indexed quantity over the biproduct index
`Σ i, Fin (n i)` weights each term by its multiplicity, `∑_{p} G p.1 = ∑_i n_i G i`. -/
private theorem sum_sigma_fin (n : ι → ℕ) (G : ι → ℕ) :
    (∑ p : Σ i, Fin (n i), G p.1) = ∑ i, n i * G i := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The double sum over biproduct indices of a Cartan-type matrix collapses to the
multiplicity-weighted sum `∑_i ∑_j c_{ij} n_i n_j`. -/
private theorem sum_sigma_cartan (c : ι → ι → ℕ) (n : ι → ℕ) :
    (∑ p : Σ i, Fin (n i), ∑ q : Σ j, Fin (n j), c p.1 q.1)
      = ∑ i, ∑ j, c i j * n i * n j := by
  calc (∑ p : Σ i, Fin (n i), ∑ q : Σ j, Fin (n j), c p.1 q.1)
      = ∑ i, n i * ∑ q : Σ j, Fin (n j), c i q.1 :=
        sum_sigma_fin n (fun x => ∑ q : Σ j, Fin (n j), c x q.1)
    _ = ∑ i, n i * ∑ j, n j * c i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_sigma_fin n (fun j => c i j)]
    _ = ∑ i, ∑ j, c i j * n i * n j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- `dim_k End(P_𝐧) = ∑_{p,q} dim_k Hom(P_{p}, P_{q})`, the biproduct Hom decomposition for
`P_𝐧 = ⊕_i n_i P_i`. -/
theorem finrank_end_multBiproduct (P : ι → C) (n : ι → ℕ) :
    finrank k (End (multBiproduct P n))
      = ∑ p : Σ i, Fin (n i), ∑ q : Σ j, Fin (n j), finrank k (P p.1 ⟶ P q.1) :=
  finrank_biproduct_hom (fun p : Σ i, Fin (n i) => P p.1) (fun q : Σ j, Fin (n j) => P q.1)
    fun p q => IsFiniteAbelianCategoryOverField.finiteDimensional_hom (P p.1) (P q.1)

/-- **Etingof, discussion after Definition 9.7.1.** The dimension of the basic algebra
`B_𝐧 = End(P_𝐧)ᵒᵖ` attached to the projective generator `P_𝐧 = ⊕_i n_i P_i` is

`dim_k B_𝐧 = ∑_i ∑_j c_{ij} n_i n_j`,

where `c_{ij} = dim_k Hom(P_i, P_j)` is the (representation-theoretic) Cartan matrix. -/
theorem finrank_cartanAlgebra (P : ι → C) (n : ι → ℕ) :
    finrank k ((End (multBiproduct P n))ᵐᵒᵖ)
      = ∑ i, ∑ j, cartanEntry k P i j * n i * n j := by
  rw [← (MulOpposite.opLinearEquiv k (M := End (multBiproduct P n))).finrank_eq,
    finrank_end_multBiproduct P n]
  exact sum_sigma_cartan (cartanEntry k P) n

end Cartan

section Minimal

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C] [Linear k C]
  [IsFiniteAbelianCategoryOverField k C] [HasFiniteBiproducts C]
variable {ι : Type v} [Fintype ι]

/-- A single Cartan term is non-decreasing in the multiplicities: `c ≤ c · n₁ · n₂`
whenever `n₁, n₂ ≥ 1`. -/
private theorem cartan_term_le (c n₁ n₂ : ℕ) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) :
    c ≤ c * n₁ * n₂ := by
  calc c = c * 1 * 1 := by ring
    _ ≤ c * n₁ * n₂ := by gcongr

/-- A diagonal Cartan term grows strictly once its multiplicity is `≥ 2`: `c < c · n · n`
whenever `c ≥ 1` and `n ≥ 2`. -/
private theorem cartan_term_lt (c n : ℕ) (hc : 1 ≤ c) (hn : 2 ≤ n) : c < c * n * n := by
  have h4 : 1 < n * n := by have := Nat.mul_le_mul hn hn; omega
  calc c = c * 1 := (mul_one c).symm
    _ < c * (n * n) := mul_lt_mul_of_pos_left h4 (by omega)
    _ = c * n * n := (mul_assoc c n n).symm

/-- **Lower bound on `dim B_𝐧` (Etingof, discussion after Definition 9.7.1).** With every
multiplicity `n_i ≥ 1`, the dimension `∑_i ∑_j c_{ij} n_i n_j` of the basic algebra `B_𝐧` is
bounded below by `∑_i ∑_j c_{ij}`, the dimension of the minimal member `B_(1,…,1)`. -/
theorem sum_cartan_le_finrank_cartanAlgebra (P : ι → C) (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    (∑ i, ∑ j, cartanEntry k P i j) ≤ finrank k ((End (multBiproduct P n))ᵐᵒᵖ) := by
  rw [finrank_cartanAlgebra]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact cartan_term_le _ _ _ (hn i) (hn j)

/-- The minimal member `B_(1,…,1)` (all multiplicities `1`, i.e. `P = ⊕_i P_i`) has dimension
exactly `∑_i ∑_j c_{ij}`. -/
theorem finrank_cartanAlgebra_one (P : ι → C) :
    finrank k ((End (multBiproduct P (fun _ => 1)))ᵐᵒᵖ) = ∑ i, ∑ j, cartanEntry k P i j := by
  rw [finrank_cartanAlgebra]
  simp

/-- **Minimal dimension iff `𝐧 = (1,…,1)` (Etingof, discussion after Definition 9.7.1).**
Assuming each multiplicity `n_i ≥ 1` and each diagonal Cartan number `c_{ii} ≥ 1` (the identity
spans a line in `End(P_i)`), the dimension `dim B_𝐧 = ∑ c_{ij} n_i n_j` attains its minimum value
`∑ c_{ij}` **exactly** when every `n_i = 1`. Any `n_i ≥ 2` strictly enlarges the diagonal term
`c_{ii} n_i^2`. -/
theorem finrank_cartanAlgebra_eq_sum_cartan_iff (P : ι → C) (n : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hdiag : ∀ i, 1 ≤ cartanEntry k P i i) :
    finrank k ((End (multBiproduct P n))ᵐᵒᵖ) = ∑ i, ∑ j, cartanEntry k P i j ↔ ∀ i, n i = 1 := by
  rw [finrank_cartanAlgebra]
  constructor
  · intro h
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hi₀2 : 2 ≤ n i₀ := by have := hn i₀; omega
    have hlt : (∑ i, ∑ j, cartanEntry k P i j)
        < ∑ i, ∑ j, cartanEntry k P i j * n i * n j := by
      refine Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ =>
        cartan_term_le _ _ _ (hn i) (hn j)) ⟨i₀, Finset.mem_univ _, ?_⟩
      refine Finset.sum_lt_sum (fun j _ => cartan_term_le _ _ _ (hn i₀) (hn j))
        ⟨i₀, Finset.mem_univ _, ?_⟩
      exact cartan_term_lt _ _ (hdiag i₀) hi₀2
    omega
  · intro h
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h i, h j]
    ring

omit [HasFiniteBiproducts C] [Fintype ι] in
/-- Convenience: if `End(P_i) = Hom(P_i, P_i)` is nontrivial (it always is — it contains the
nonzero identity when `P_i ≠ 0`), then `c_{ii} ≥ 1`, supplying the diagonal hypothesis of
`finrank_cartanAlgebra_eq_sum_cartan_iff`. -/
theorem one_le_cartanEntry_self (P : ι → C) (i : ι) [Nontrivial (P i ⟶ P i)] :
    1 ≤ cartanEntry k P i i := by
  haveI : FiniteDimensional k (P i ⟶ P i) :=
    IsFiniteAbelianCategoryOverField.finiteDimensional_hom (P i) (P i)
  exact Module.finrank_pos

end Minimal

section Commutativity

/-! ## Commutativity of the semisimple quotient

Etingof's second claim: `B_(1,…,1)` is the unique `B_𝐧` whose Wedderburn quotient
`B_𝐧 / Rad(B_𝐧) ≅ ⊕_i Mat_{n_i}(k)` is commutative. We model that quotient by its Wedderburn
form `∀ i, Matrix (Fin (n i)) (Fin (n i)) k` and prove commutativity holds iff every `n_i = 1`,
the elementary fact that `Mat_m(k)` is commutative iff `m ≤ 1`. -/

variable {k : Type w} [Field k]

/-- Over a nontrivial ring, a matrix algebra with two distinct indices is **non**commutative:
the elementary matrices `E_{ab}` and `E_{ba}` fail to commute (`E_{ab} E_{ba} = E_{aa}` but
`E_{ba} E_{ab} = E_{bb}`). -/
theorem exists_matrix_not_comm_of_ne {m : Type*} [Fintype m] {a b : m}
    (hab : a ≠ b) : ∃ x y : Matrix m m k, x * y ≠ y * x := by
  classical
  refine ⟨Matrix.single a b 1, Matrix.single b a 1, ?_⟩
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one]
  intro h
  have h2 := congrFun (congrFun h a) a
  rw [Matrix.single_apply_same, Matrix.single_apply_of_row_ne hab.symm b a 1] at h2
  exact one_ne_zero h2

/-- A matrix algebra indexed by a subsingleton is commutative: there is at most one index, so
multiplication reduces to the (commutative) coefficient multiplication. -/
theorem matrix_mul_comm_of_subsingleton {m : Type*} [Fintype m] [Subsingleton m]
    (x y : Matrix m m k) : x * y = y * x := by
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : l = i := Subsingleton.elim l i
  subst this
  exact mul_comm _ _

/-- **Etingof, discussion after Definition 9.7.1 (commutativity criterion).** The Wedderburn
semisimple quotient `B_𝐧 / Rad(B_𝐧) ≅ ⊕_i Mat_{n_i}(k)`, modelled as the product of matrix
algebras `∀ i, Matrix (Fin (n i)) (Fin (n i)) k`, is commutative **iff** every multiplicity
`n_i = 1` — i.e. iff `𝐧 = (1,…,1)`, the unique minimal member `B = B_(1,…,1)`. Each factor
`Mat_{n_i}(k)` is commutative iff `n_i ≤ 1`, and with `n_i ≥ 1` this is `n_i = 1`. -/
theorem semisimpleQuotient_comm_iff {ι : Type*} (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    (∀ x y : (∀ i, Matrix (Fin (n i)) (Fin (n i)) k), x * y = y * x) ↔ ∀ i, n i = 1 := by
  classical
  constructor
  · intro hcomm i
    by_contra hni
    have hi2 : 2 ≤ n i := by have := hn i; omega
    obtain ⟨x₀, y₀, hxy⟩ := exists_matrix_not_comm_of_ne (k := k)
      (m := Fin (n i)) (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (Fin.ne_of_val_ne (by simp))
    have key := congrFun (hcomm (Function.update 1 i x₀) (Function.update 1 i y₀)) i
    rw [Pi.mul_apply, Pi.mul_apply, Function.update_self, Function.update_self] at key
    exact hxy key
  · intro h x y
    funext i
    rw [Pi.mul_apply, Pi.mul_apply]
    haveI : Subsingleton (Fin (n i)) := by rw [h i]; infer_instance
    exact matrix_mul_comm_of_subsingleton _ _

end Commutativity

end Etingof
