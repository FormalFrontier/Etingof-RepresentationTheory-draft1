import EtingofRepresentationTheory.Chapter2.Problem2_11_3_SymPowBasis
import EtingofRepresentationTheory.Infrastructure.Triangularization

/-!
# Problem 2.11.3(f): the traces of `S^n A` and `⋀^n A`

Etingof asks: *"Suppose that `V = W` and that `dim V = N`, and that the eigenvalues of `A` are
`λ₁, …, λ_N`. Find `Tr(S^n A)` and `Tr(⋀^n A)`."*

The answers are the two classical families of symmetric functions in the eigenvalues:

* `Tr(⋀^n A) = e_n(λ) = ∑_{|s| = n} ∏_{i ∈ s} λ_i`, the `n`th **elementary** symmetric function;
* `Tr(S^n A) = h_n(λ) = ∑_{|m| = n} ∏_{i ∈ m} λ_i`, the `n`th **complete homogeneous** symmetric
  function, the sum now running over *multisets* of size `n`.

## The shape of the hypothesis

The book's proof is "put `A` in upper-triangular form"; the induced operators are then triangular
in the induced bases, with the products `∏ λ_i` down the diagonal. So the triangularizing basis is
what the two main theorems take as their hypothesis, packaged as
`Etingof.Problem2_11_3.IsTriangularizedBy`.

That this really is the "eigenvalues listed with multiplicity" hypothesis is certified by
`IsTriangularizedBy.charpoly`: it says exactly that `charpoly A = ∏ i, (X - λ i)`.

The converse — that the book's hypothesis produces such a basis — is
`EtingofRepresentationTheory.Infrastructure.Triangularization`, which supplies the
triangularization theorem Mathlib lacks. Combining the two gives the trace formulas under the
book's own hypothesis, with no basis mentioned: see `trace_extPowMap_of_charpoly` and
`trace_symPowMap_of_charpoly` below.

## Main results

* `Etingof.Problem2_11_3.IsTriangularizedBy` : `A` is upper-triangular in the basis `b` with
  diagonal `lam`.
* `Etingof.Problem2_11_3.IsTriangularizedBy.charpoly` : such a `lam` is precisely the list of
  eigenvalues of `A` with multiplicity, i.e. `A.charpoly = ∏ i, (X - C (lam i))`.
* `Etingof.Problem2_11_3.trace_extPowMap` : **Problem 2.11.3(f), exterior case** —
  `Tr(⋀^n A) = ∑_{s ⊆ Fin N, |s| = n} ∏_{i ∈ s} lam i`.
* `Etingof.Problem2_11_3.trace_symPowMap` : **Problem 2.11.3(f), symmetric case** —
  `Tr(S^n A) = ∑_{m : Sym (Fin N) n} ∏_{i ∈ m} lam i`.
* `Etingof.Problem2_11_3.trace_extPowMap_top`, `Etingof.Problem2_11_3.trace_extPowMap_one` and
  `Etingof.Problem2_11_3.trace_symPowMap_one` : the degenerate degrees, `n = N` (the determinant)
  and `n = 1` (the trace of `A` itself, from both sides).
* `Etingof.Problem2_11_3.exists_isTriangularizedBy` : a split characteristic polynomial produces
  the triangularizing data.
* `Etingof.Problem2_11_3.trace_extPowMap_of_charpoly` and
  `Etingof.Problem2_11_3.trace_symPowMap_of_charpoly` : **the book's statement of part (f)** — the
  same two formulas with `charpoly A = ∏ i, (X - C (lam i))` as the only hypothesis on `lam`.

## Proof strategy

Neither computation needs the *whole* induced matrix to be triangular: the trace only sees the
diagonal entries, and each diagonal entry can be computed on the nose.

* Exterior: the `s`-diagonal entry of `⋀^n A` is the determinant of the submatrix of `A` on the
  rows and columns indexed by `s` (`exteriorPower.ιMultiDual_apply_ιMulti` hands this over
  directly). That submatrix inherits upper-triangularity from `A`, so the determinant is
  `∏_{i ∈ s} lam i`.
* Symmetric: expanding `S^n A` multilinearly on the basis vector indexed by a tuple `g` writes the
  `g`-diagonal entry as `∑_{f : tupleSym f = tupleSym g} ∏_i A_{f i, g i}`. Upper-triangularity
  forces `f i ≤ g i` on every surviving term, and a tuple dominated by `g` with the same multiset
  of entries *is* `g` (`eq_of_tupleSym_eq_of_forall_le`), so exactly one term survives.
-/

namespace Etingof.Problem2_11_3

open Finset

/-! ### Two combinatorial ingredients -/

/-- If two tuples of `Fin N` have the same multiset of entries and one is pointwise `≤` the other,
they are equal: the two index sums agree, so no slack is available anywhere.

This is the combinatorial heart of the symmetric trace formula. -/
lemma eq_of_tupleSym_eq_of_forall_le {N n : ℕ} {f g : Fin n → Fin N}
    (hsym : tupleSym f = tupleSym g) (hle : ∀ i, f i ≤ g i) : f = g := by
  obtain ⟨σ, rfl⟩ := tupleSym_eq_iff.1 hsym
  have hsum : ∑ i, ((g (σ i) : ℕ)) = ∑ i, ((g i : ℕ)) :=
    Fintype.sum_equiv σ (fun i => ((g (σ i) : ℕ))) (fun i => ((g i : ℕ))) fun _ => rfl
  have hle' : ∀ i ∈ (Finset.univ : Finset (Fin n)), ((g (σ i) : ℕ)) ≤ ((g i : ℕ)) :=
    fun i _ => Fin.le_def.mp (hle i)
  have key := (Finset.sum_eq_sum_iff_of_le hle').1 hsum
  funext i
  exact Fin.ext (key i (Finset.mem_univ i))

/-- A product over the increasing enumeration of a finset is a product over the finset. -/
lemma prod_orderEmbOfFin {α M : Type*} [LinearOrder α] [CommMonoid M] (t : Finset α) {n : ℕ}
    (ht : t.card = n) (f : α → M) : ∏ i, f (t.orderEmbOfFin ht i) = ∏ x ∈ t, f x := by
  rw [← Finset.prod_coe_sort t f]
  exact Fintype.prod_equiv (t.orderIsoOfFin ht).toEquiv _ _ fun i => by
    rw [OrderIso.coe_toEquiv, Finset.coe_orderIsoOfFin_apply]

/-! ### Triangularizing data -/

section Triangular

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- `IsTriangularizedBy A b lam` says that the basis `b` puts `A` in upper-triangular form with
`lam` down the diagonal. By `IsTriangularizedBy.charpoly` this is exactly the statement that the
eigenvalues of `A`, listed with multiplicity, are `lam 0, …, lam (N-1)`. -/
structure IsTriangularizedBy {N : ℕ} (A : V →ₗ[k] V) (b : Module.Basis (Fin N) k V)
    (lam : Fin N → k) : Prop where
  /-- The matrix of `A` in the basis `b` is upper-triangular. -/
  blockTriangular : (LinearMap.toMatrix b b A).BlockTriangular id
  /-- Its diagonal is `lam`. -/
  diag : ∀ i, LinearMap.toMatrix b b A i i = lam i

variable {N : ℕ} {A : V →ₗ[k] V} {b : Module.Basis (Fin N) k V} {lam : Fin N → k}

/-- **The hypothesis is satisfiable.** Every upper-triangular matrix triangularizes the operator
it defines on `Fin N → k`, with its own diagonal as the eigenvalue list. -/
lemma isTriangularizedBy_toLin {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (hM : M.BlockTriangular id) :
    IsTriangularizedBy (Matrix.toLin (Pi.basisFun k (Fin N)) (Pi.basisFun k (Fin N)) M)
      (Pi.basisFun k (Fin N)) (fun i => M i i) :=
  ⟨by rwa [LinearMap.toMatrix_toLin], fun i => by rw [LinearMap.toMatrix_toLin]⟩

/-- **A triangularizing diagonal is the eigenvalue list.** If `b` puts `A` in upper-triangular
form with diagonal `lam`, then the characteristic polynomial of `A` is `∏ i, (X - lam i)`, i.e.
`lam` enumerates the eigenvalues of `A` with multiplicity. -/
theorem IsTriangularizedBy.charpoly (h : IsTriangularizedBy A b lam) :
    letI := Module.Finite.of_basis b
    letI := Module.Free.of_basis b
    LinearMap.charpoly A = ∏ i, (Polynomial.X - Polynomial.C (lam i)) := by
  letI := Module.Finite.of_basis b
  letI := Module.Free.of_basis b
  rw [← LinearMap.charpoly_toMatrix A b, Matrix.charpoly_of_upperTriangular _ h.blockTriangular]
  exact Finset.prod_congr rfl fun i _ => by rw [h.diag]

/-- Every term of the expansion of a diagonal entry of an induced operator away from the
"identity" tuple vanishes: upper-triangularity forces `f ≤ g` pointwise, and then having the same
multiset of entries forces `f = g`. -/
lemma prod_toMatrix_eq_zero_of_ne (h : IsTriangularizedBy A b lam) {n : ℕ} {f g : Fin n → Fin N}
    (hsym : tupleSym f = tupleSym g) (hfg : f ≠ g) :
    ∏ i, LinearMap.toMatrix b b A (f i) (g i) = 0 := by
  by_contra hne
  refine hfg (eq_of_tupleSym_eq_of_forall_le hsym fun i => ?_)
  by_contra hlt
  exact hne (Finset.prod_eq_zero (Finset.mem_univ i) (h.blockTriangular (not_le.1 hlt)))

end Triangular

/-! ### The exterior trace -/

section Exterior

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {N : ℕ} {A : V →ₗ[k] V} {b : Module.Basis (Fin N) k V} {lam : Fin N → k}

/-- The comparison isomorphism between Mathlib's exterior power and the book's model intertwines
the two induced operators. -/
lemma extPowMap_exteriorPowerEquiv (A : V →ₗ[k] V) (n : ℕ) (x : ⋀[k]^n V) :
    extPowMap A n (exteriorPowerEquiv (V := V) n x)
      = exteriorPowerEquiv (V := V) n (exteriorPower.map n A x) :=
  LinearMap.congr_fun (extPowOfExteriorPower_naturality A n) x

/-- **The diagonal entries of `⋀^n A` are the principal minors of `A`.** In the basis of `⋀^n V`
induced by `b`, the entry of `⋀^n A` at the `n`-element subset `s` is the determinant of the
submatrix of `A` on the rows and columns indexed by `s`. -/
lemma toMatrix_extPowBasis_diag (A : V →ₗ[k] V) (b : Module.Basis (Fin N) k V) {n : ℕ}
    (s : Set.powersetCard (Fin N) n) :
    LinearMap.toMatrix (extPowBasis b n) (extPowBasis b n) (extPowMap A n) s s
      = ((LinearMap.toMatrix b b A).submatrix
          (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))
          (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))).det := by
  classical
  rw [LinearMap.toMatrix_apply, extPowBasis, Module.Basis.map_apply,
    extPowMap_exteriorPowerEquiv, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.coord_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]

/-- **Problem 2.11.3(f), exterior case.** If `b` puts `A` in upper-triangular form with diagonal
`lam`, then the trace of `⋀^n A` is the `n`th elementary symmetric function of `lam`. -/
theorem trace_extPowMap (h : IsTriangularizedBy A b lam) (n : ℕ) :
    LinearMap.trace k (ExtPow k V n) (extPowMap A n)
      = ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i := by
  classical
  have hconv : ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i
      = ∑ s : Set.powersetCard (Fin N) n, ∏ i ∈ (s : Finset (Fin N)), lam i :=
    Finset.sum_subtype _ (fun x => by simp [Finset.mem_powersetCard]) _
  rw [LinearMap.trace_eq_matrix_trace k (extPowBasis b n) (extPowMap A n), Matrix.trace, hconv]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, toMatrix_extPowBasis_diag]
  have hmono : StrictMono
      (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s)) :=
    OrderEmbedding.strictMono _
  have htri : ((LinearMap.toMatrix b b A).submatrix
      (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))
      (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))).BlockTriangular
      id := fun _ _ hij => h.blockTriangular (hmono hij)
  rw [Matrix.det_of_upperTriangular htri]
  simpa [Matrix.submatrix_apply, h.diag] using
    prod_orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s) lam

/-- **Problem 2.11.3(f), top degree.** In degree `n = N` the elementary symmetric function is the
product of all the eigenvalues, i.e. the determinant of `A`. -/
theorem trace_extPowMap_top (h : IsTriangularizedBy A b lam) :
    LinearMap.trace k (ExtPow k V N) (extPowMap A N) = ∏ i, lam i := by
  classical
  have hself : Finset.powersetCard N (Finset.univ : Finset (Fin N)) = {Finset.univ} := by
    have hself := Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rwa [Finset.card_univ, Fintype.card_fin] at hself
  rw [trace_extPowMap h N, hself, Finset.sum_singleton]

/-- **Problem 2.11.3(f), degree one.** In degree `n = 1` the elementary symmetric function is the
sum of the eigenvalues, i.e. the trace of `A` itself. -/
theorem trace_extPowMap_one (h : IsTriangularizedBy A b lam) :
    LinearMap.trace k (ExtPow k V 1) (extPowMap A 1) = ∑ i, lam i := by
  classical
  rw [trace_extPowMap h 1, Finset.powersetCard_one, Finset.sum_map]
  simp

end Exterior

/-! ### The symmetric trace -/

section Symmetric

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {N : ℕ} {A : V →ₗ[k] V} {b : Module.Basis (Fin N) k V} {lam : Fin N → k}

/-- The coordinates of `S^n V` in the basis `symPowBasis b n` are computed by
`symPowToFinsupp`. -/
lemma symPowBasis_repr_symTprod {I : Type*} (b : Module.Basis I k V) (n : ℕ) (g : Fin n → I) :
    (symPowBasis b n).repr (symTprod k V n fun i => b (g i)) = Finsupp.single (tupleSym g) 1 :=
  symPowToFinsupp_symTprod b n g

/-- **Problem 2.11.3(f), symmetric case.** If `b` puts `A` in upper-triangular form with diagonal
`lam`, then the trace of `S^n A` is the `n`th complete homogeneous symmetric function of `lam`:
the sum, over all multisets of size `n` drawn from the eigenvalues, of their product. -/
theorem trace_symPowMap (h : IsTriangularizedBy A b lam) (n : ℕ) :
    LinearMap.trace k (SymPow k V n) (symPowMap A n)
      = ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map lam).prod := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (symPowBasis b n) (symPowMap A n), Matrix.trace]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- realise `s` by a tuple `g` and expand `S^n A` on the corresponding basis vector
  obtain ⟨g, rfl⟩ : ∃ g : Fin n → Fin N, tupleSym g = s :=
    ⟨symIndexRep n s, tupleSym_symIndexRep n s⟩
  have hprod : ((tupleSym g : Multiset (Fin N)).map lam).prod = ∏ i, lam (g i) := by
    rw [tupleSym_coe, Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  have hA : ∀ j, A (b j) = ∑ p, LinearMap.toMatrix b b A p j • b p := fun j => by
    conv_lhs => rw [← b.sum_repr (A (b j))]
    exact Finset.sum_congr rfl fun p _ => by rw [LinearMap.toMatrix_apply]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, symPowBasis_apply b n _ g rfl,
    symPowMap_symTprod]
  simp_rw [hA]
  rw [MultilinearMap.map_sum]
  simp_rw [MultilinearMap.map_smul_univ]
  rw [map_sum, Finsupp.finsetSum_apply]
  simp_rw [map_smul, Finsupp.smul_apply, symPowBasis_repr_symTprod, smul_eq_mul]
  -- only the tuple `g` itself survives
  rw [Finset.sum_eq_single g]
  · rw [Finsupp.single_eq_same, mul_one, hprod]
    exact Finset.prod_congr rfl fun i _ => h.diag (g i)
  · intro f _ hfg
    by_cases hfs : tupleSym f = tupleSym g
    · rw [prod_toMatrix_eq_zero_of_ne h hfs hfg, zero_mul]
    · rw [Finsupp.single_eq_of_ne' hfs, mul_zero]
  · exact fun hg => absurd (Finset.mem_univ g) hg

/-- **Problem 2.11.3(f), degree one.** In degree `n = 1` the complete homogeneous symmetric
function is the sum of the eigenvalues, i.e. the trace of `A` itself. -/
theorem trace_symPowMap_one (h : IsTriangularizedBy A b lam) :
    LinearMap.trace k (SymPow k V 1) (symPowMap A 1) = ∑ i, lam i := by
  classical
  rw [trace_symPowMap h 1]
  exact (Fintype.sum_equiv Sym.oneEquiv lam
    (fun s => ((s : Multiset (Fin N)).map lam).prod) fun i => by simp).symm

end Symmetric

/-! ### The book's hypothesis: the eigenvalue list

The two theorems above assume a triangularizing basis. The book assumes only that the eigenvalues
of `A` are `λ_1, …, λ_N`, i.e. that `charpoly A = ∏ i, (X - C (λ i))`. The triangularization
theorem of `Infrastructure.Triangularization` turns the latter into the former — at the cost of a
permutation of `Fin N`, since `lam` is determined by `charpoly A` only up to reordering. Both
right-hand sides are symmetric functions of `lam`, so the permutation washes out.
-/

section Charpoly

open Polynomial

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- **The triangularizing hypothesis is available whenever the book's is.** If the characteristic
polynomial of `A` splits, some basis puts `A` in upper-triangular form, with some diagonal.

This is `Etingof.exists_basis_blockTriangular_charpoly` repackaged into `IsTriangularizedBy`. -/
theorem exists_isTriangularizedBy {N : ℕ} (A : V →ₗ[k] V) (hN : Module.finrank k V = N)
    (hsplit : (LinearMap.charpoly A).Splits) :
    ∃ (b : Module.Basis (Fin N) k V) (lam : Fin N → k), IsTriangularizedBy A b lam := by
  obtain ⟨b, lam, hb, hdiag, -⟩ := Etingof.exists_basis_blockTriangular_charpoly A hN hsplit
  exact ⟨b, lam, hb, hdiag⟩

/-- **Problem 2.11.3(f), exterior case, as the book states it.** If the eigenvalues of `A`, with
multiplicity, are `lam 0, …, lam (N-1)` — that is, `charpoly A = ∏ i, (X - C (lam i))` — then
`Tr(⋀^n A)` is the `n`th elementary symmetric function of `lam`. No basis appears. -/
theorem trace_extPowMap_of_charpoly {N : ℕ} (A : V →ₗ[k] V) (hN : Module.finrank k V = N)
    (lam : Fin N → k) (hlam : LinearMap.charpoly A = ∏ i, (X - C (lam i))) (n : ℕ) :
    LinearMap.trace k (ExtPow k V n) (extPowMap A n)
      = ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i := by
  obtain ⟨b, e, hb, hdiag⟩ := Etingof.exists_basis_blockTriangular_diag_perm A hN lam hlam
  rw [trace_extPowMap (⟨hb, hdiag⟩ : IsTriangularizedBy A b fun i => lam (e i)) n]
  exact Etingof.sum_powersetCard_prod_comp lam e n

/-- **Problem 2.11.3(f), symmetric case, as the book states it.** If the eigenvalues of `A`, with
multiplicity, are `lam 0, …, lam (N-1)`, then `Tr(S^n A)` is the `n`th complete homogeneous
symmetric function of `lam`. No basis appears. -/
theorem trace_symPowMap_of_charpoly {N : ℕ} (A : V →ₗ[k] V) (hN : Module.finrank k V = N)
    (lam : Fin N → k) (hlam : LinearMap.charpoly A = ∏ i, (X - C (lam i))) (n : ℕ) :
    LinearMap.trace k (SymPow k V n) (symPowMap A n)
      = ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map lam).prod := by
  obtain ⟨b, e, hb, hdiag⟩ := Etingof.exists_basis_blockTriangular_diag_perm A hN lam hlam
  rw [trace_symPowMap (⟨hb, hdiag⟩ : IsTriangularizedBy A b fun i => lam (e i)) n]
  exact Etingof.sum_sym_prod_comp lam e n

end Charpoly

end Etingof.Problem2_11_3
