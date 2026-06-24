import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import EtingofRepresentationTheory.Chapter9.Introduction_9_7
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

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

end Etingof
