import Mathlib
import EtingofRepresentationTheory.Chapter4.Theorem4_6_2
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible
import EtingofRepresentationTheory.Chapter5.Problem5_16_2
import EtingofRepresentationTheory.Chapter5.SumTranspositionsEigenvalues
import EtingofRepresentationTheory.Chapter5.Problem5_16_1
import EtingofRepresentationTheory.Chapter5.CharacterMultiplicityBridge

/-!
# Problem 5.16.3: the sum `(12) + ⋯ + (1n)` of transpositions through `1`

**Problem 5.16.3.** (a) Let `V` be any finite-dimensional representation of `S_n`. Show that the
element `E := (12) + ⋯ + (1n)` is diagonalizable and has integer eigenvalues on `V` which are
between `1 - n` and `n - 1`.

*Hint.* Represent `E` as `C_n − C_{n-1}`, where `C_n = C` is the element from Problem 5.16.2.

(b) Show that the element `(12) + ⋯ + (1n)` acts on `V_λ` by a scalar if and only if `λ` is a
rectangular Young diagram, and compute this scalar.

## Formalization

`E = (12) + ⋯ + (1n)` is the sum of the transpositions through the first point. In the
`0`-indexed model `Fin n`, the first point is `0` and the transpositions `(1 j)` are
`Equiv.swap 0 j` for `j ≠ 0`; so `sumTranspositionsWith1 n = ∑_{0 < j} (0 j) ∈ ℂ[S_n]`.

* **(a)** For a representation `ρ : Representation ℂ S_n V` on a finite-dimensional `V`, `E` acts
  by the endomorphism `T = ρ.asAlgebraHom E`. The claim is that `T` is diagonalizable (there is a
  basis of `V` consisting of eigenvectors) and every eigenvalue is an integer `m` with
  `1 - n ≤ m ≤ n - 1`.
* **(b)** `E` acts on the Specht module `V_λ = ℂ[S_n]·c_λ` (by left multiplication) by a scalar if
  and only if `λ` is rectangular (`IsRectangular`: the parts multiset is `r` copies of a
  single value `c`).

## Proof structure (part a)

Following the book hint `E = C_n − C_{n-1}`:

* `sumTranspositionsWith1_eq_sub`: the algebra identity
  `E = sumTranspositions n − sumTranspositionsStab n`, where `sumTranspositionsStab n` is the sum
  of transpositions `(i j)` with `0 < i < j` (the transpositions fixing point `0`).
* `sumTranspositionsStab` is `sumTranspositions (n-1)` transported along the embedding
  `S_{n-1} ↪ S_n` fixing point `0` (`permEmbZero`, via `Fin.succ`); this lets the reusable
  eigenvalue lemma from `SumTranspositionsEigenvalues` apply.
* `sumTranspositionsWith1_hasEigenvalue_integer`: every eigenvalue of `T = A − B` is an integer,
  where `A = ρ E` for `C_n` and `B = ρ E` for `C_{n-1}`. Because `A` commutes with `B` (`C_n` is
  central), `A` preserves each eigenspace of `T`; on that eigenspace `A` has an eigenvector `w`
  with `A w = α w` (`α` a content, integer), hence `B w = (α − μ) w` (`α − μ` a content, integer),
  so the `T`-eigenvalue `μ = α − (α − μ)` is an integer.
* The eigenbasis (first conjunct) and the bound `|μ| ≤ n − 1` come from unitarizability: an
  invariant inner product makes `T = ∑_{0<j} ρ(0 j)` self-adjoint (each `ρ(0 j)` is a self-adjoint
  unitary involution), so `T` has an orthonormal eigenbasis with real eigenvalues bounded by the
  number of summands `n − 1`.
-/

namespace Etingof

open scoped Classical

/-- `E = (12) + ⋯ + (1n) = ∑_{0 < j} (0 j)`: the sum of transpositions through the first point,
as an element of `ℂ[S_n]`. -/
noncomputable def sumTranspositionsWith1 (n : ℕ) [NeZero n] : SymGroupAlgebra n :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (0 : Fin n) < j),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap 0 j)

/-- `C_stab n = ∑_{0 < i < j} (i j)`: the sum of transpositions `(i j)` fixing the point `0`
(both indices are positive). This is `C_{n-1}` sitting inside `ℂ[S_n]`. -/
noncomputable def sumTranspositionsStab (n : ℕ) [NeZero n] : SymGroupAlgebra n :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (0 : Fin n) < p.1 ∧ p.1 < p.2),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2)

/-- The embedding `S_m ↪ S_{m+1}` as the pointwise stabilizer of the point `0` of `Fin (m+1)`,
sending a permutation of `Fin m` to its extension by the identity via `Fin.succ`. -/
noncomputable def permEmbZero (m : ℕ) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.viaEmbeddingHom (Fin.succEmb m)

/-- The restriction of a representation of `S_{m+1}` to `S_m` along `permEmbZero` (the stabilizer
of the point `0`). -/
noncomputable def restrictRep (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    Representation ℂ (Equiv.Perm (Fin m)) V :=
  MonoidHom.comp ρ (permEmbZero m)

/-- A partition is **rectangular** if its Young diagram is a rectangle: the parts multiset is a
constant multiset `Multiset.replicate r c` (`r` rows each of length `c`). -/
def IsRectangular {n : ℕ} (la : Nat.Partition n) : Prop :=
  ∃ r c : ℕ, la.parts = Multiset.replicate r c

/-- `permEmbZero` sends a transposition `(i j)` in `S_m` to `(i+1 · j+1)` in `S_{m+1}`. -/
lemma permEmbZero_swap (m : ℕ) (i j : Fin m) :
    permEmbZero m (Equiv.swap i j) = Equiv.swap i.succ j.succ := by
  rw [permEmbZero, Equiv.Perm.viaEmbeddingHom_apply]
  ext x
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨k, rfl⟩
  · -- `x = 0` is not in the range of `Fin.succ`, so both sides fix it.
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
    · simp only [Fin.coe_succEmb, Set.mem_range, not_exists]
      exact fun a => (Fin.succ_ne_zero a)
  · -- `x = k.succ = succEmb k`; use naturality of `viaEmbedding`.
    rw [show k.succ = (Fin.succEmb m) k from (Fin.coe_succEmb ▸ rfl),
      Equiv.Perm.viaEmbedding_apply]
    simp only [Fin.coe_succEmb, Equiv.swap_apply_def, Fin.succ_inj]
    split_ifs <;> rfl

/-- **Step 1 (algebra identity).** `E = C_n − C_{n-1}`: the sum of transpositions through `1`
equals the sum of all transpositions minus the sum of transpositions fixing the point `0`. -/
lemma sumTranspositionsWith1_eq_sub (n : ℕ) [NeZero n] :
    sumTranspositionsWith1 n = sumTranspositions n - sumTranspositionsStab n := by
  rw [eq_sub_iff_add_eq]
  -- Split the filter `{p.1 < p.2}` by whether `p.1 = 0`.
  rw [sumTranspositions]
  rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) (fun p => p.1 = 0)]
  congr 1
  · -- The `p.1 = 0` block reindexes to `sumTranspositionsWith1 n` via `j ↦ (0, j)`.
    rw [sumTranspositionsWith1]
    have hset1 : ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).filter
          (fun p => p.1 = 0))
        = (Finset.univ.filter (fun j : Fin n => (0 : Fin n) < j)).map
            ⟨fun j => ((0 : Fin n), j), fun a b h => by simpa using h⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hlt, h0⟩
        exact ⟨p.2, by rw [h0] at hlt; exact hlt, Prod.ext h0.symm rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hj, rfl⟩
    rw [hset1, Finset.sum_map]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Function.Embedding.coeFn_mk]
  · -- The `p.1 ≠ 0` block is exactly `sumTranspositionsStab n`.
    rw [sumTranspositionsStab]
    apply Finset.sum_congr _ (fun p _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.pos_iff_ne_zero]
    tauto

/-- **Step 2 (restriction).** The action of `C_{n-1} = sumTranspositionsStab (m+1)` equals the
action of `C_{n-1} = sumTranspositions m` under the restricted representation. -/
lemma asAlgebraHom_sumTranspositionsStab (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    Representation.asAlgebraHom ρ (sumTranspositionsStab (m + 1))
      = Representation.asAlgebraHom (restrictRep m ρ) (sumTranspositions m) := by
  rw [sumTranspositionsStab, sumTranspositions, map_sum, map_sum]
  -- The stabilizer filter is the image of the `Fin m` filter under `(i,j) ↦ (i.succ, j.succ)`.
  have hset : (Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (m + 1) => (0 : Fin (m + 1)) < q.1 ∧ q.1 < q.2))
      = (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).map
          ((Fin.succEmb m).prodMap (Fin.succEmb m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coe_prodMap, Fin.coe_succEmb, Prod.exists,
      Prod.map_apply]
    constructor
    · rintro ⟨h0, hlt⟩
      refine ⟨q.1.pred (Fin.pos_iff_ne_zero.mp h0), q.2.pred (Fin.pos_iff_ne_zero.mp
        (lt_trans h0 hlt)), ?_, ?_⟩
      · rw [Fin.pred_lt_pred_iff]; exact hlt
      · rw [Fin.succ_pred, Fin.succ_pred]
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨Fin.succ_pos a, Fin.succ_lt_succ_iff.mpr hab⟩
  rw [hset, Finset.sum_map]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [Function.Embedding.coe_prodMap, Fin.coe_succEmb]
  rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
  change ρ (Equiv.swap p.1.succ p.2.succ) = ρ (permEmbZero m (Equiv.swap p.1 p.2))
  rw [permEmbZero_swap]

/-- **Step 3 (integer eigenvalues).** For any finite-dimensional representation `ρ` of `S_{m+1}`,
every eigenvalue of `T = ρ E` (where `E = (12) + ⋯ + (1n)`) is an integer.

Write `T = A − B` with `A = ρ C_n` and `B = ρ C_{n-1}`. As `A` commutes with `B` (`C_n` central),
`A` preserves each `T`-eigenspace `E_μ`; taking an eigenvector `w ∈ E_μ` of `A` (eigenvalue `α`, a
content, hence integer) gives `B w = (α − μ) w`, so `α − μ` is a `B`-eigenvalue (a content, hence
integer), and `μ = α − (α − μ)` is an integer. -/
lemma sumTranspositionsWith1_hasEigenvalue_integer (m : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue
        (Representation.asAlgebraHom ρ (sumTranspositionsWith1 (m + 1))) μ) :
    ∃ z : ℤ, μ = (z : ℂ) := by
  classical
  set A : Module.End ℂ V := Representation.asAlgebraHom ρ (sumTranspositions (m + 1)) with hA
  set B : Module.End ℂ V := Representation.asAlgebraHom ρ (sumTranspositionsStab (m + 1)) with hB
  set T : Module.End ℂ V := Representation.asAlgebraHom ρ (sumTranspositionsWith1 (m + 1)) with hT
  -- `T = A - B`.
  have hTAB : T = A - B := by
    rw [hT, hA, hB, ← map_sub, sumTranspositionsWith1_eq_sub]
  -- `A` commutes with `B` (`C_n` is central in `ℂ[S_n]`).
  have hAB : Commute A B := by
    change A * B = B * A
    rw [hA, hB, ← map_mul, ← map_mul,
      sumTranspositions_central (m + 1) (sumTranspositionsStab (m + 1))]
  -- `A` commutes with `T = A - B`.
  have hAT : Commute A T := by rw [hTAB]; exact (Commute.refl A).sub_right hAB
  -- Integer eigenvalues of `A` (contents of partitions of `m+1`).
  obtain ⟨_, hAeig⟩ := sumTranspositions_isSemisimple_and_integer_eigenvalues (m + 1) ρ
  have hAint : ∀ α : ℂ, Module.End.HasEigenvalue A α → ∃ z : ℤ, α = (z : ℂ) := by
    intro α hα
    obtain ⟨la, hla⟩ := hAeig α (by rw [hA] at hα; exact hα)
    exact ⟨content la, hla⟩
  -- Integer eigenvalues of `B` (contents of partitions of `m`, via the restricted rep).
  obtain ⟨_, hBeig⟩ := sumTranspositions_isSemisimple_and_integer_eigenvalues m (restrictRep m ρ)
  have hBint : ∀ β : ℂ, Module.End.HasEigenvalue B β → ∃ z : ℤ, β = (z : ℂ) := by
    intro β hβ
    rw [hB, asAlgebraHom_sumTranspositionsStab m ρ] at hβ
    obtain ⟨la, hla⟩ := hBeig β hβ
    exact ⟨content la, hla⟩
  -- `A` preserves the `T`-eigenspace `E_μ`.
  set E := Module.End.eigenspace T μ with hE
  have hAmaps : ∀ x ∈ E, A x ∈ E := by
    intro x hx
    rw [hE, Module.End.mem_eigenspace_iff] at hx ⊢
    calc T (A x) = (A * T) x := by rw [← hAT.symm.eq]; rfl
      _ = A (T x) := rfl
      _ = A (μ • x) := by rw [hx]
      _ = μ • A x := by rw [map_smul]
  haveI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hμ
  haveI : FiniteDimensional ℂ E := inferInstance
  -- Restrict `A` to `E` and pick an eigenvector.
  set A' : Module.End ℂ E := LinearMap.restrict A hAmaps with hA'
  obtain ⟨α, hα'⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨w', hw'mem, hw'ne⟩ := hα'.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hw'mem
  -- Transfer to `V`: `w = ↑w'`, `A w = α • w`, `w ∈ E` (so `T w = μ • w`), `w ≠ 0`.
  set w : V := (w' : V) with hw
  have hwne : w ≠ 0 := by rw [hw]; exact fun h => hw'ne (Submodule.coe_eq_zero.mp h)
  have hAw : A w = α • w := by
    have h := congrArg (Subtype.val) hw'mem
    simp only [Submodule.coe_smul] at h
    exact h
  have hTw : T w = μ • w := Module.End.mem_eigenspace_iff.mp w'.2
  -- `α` is an eigenvalue of `A`.
  have hAα : Module.End.HasEigenvalue A α :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hAw, hwne⟩
  -- `B w = (α − μ) • w`, so `α − μ` is an eigenvalue of `B`.
  have hBw : B w = (α - μ) • w := by
    have hBAT : B = A - T := by rw [hTAB]; abel
    rw [hBAT, LinearMap.sub_apply, hAw, hTw, sub_smul]
  have hBβ : Module.End.HasEigenvalue B (α - μ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hBw, hwne⟩
  obtain ⟨za, hza⟩ := hAint α hAα
  obtain ⟨zb, hzb⟩ := hBint (α - μ) hBβ
  refine ⟨za - zb, ?_⟩
  push_cast
  rw [← hza, ← hzb]; ring

/-- Problem 5.16.3(a). For any finite-dimensional representation `ρ` of `S_n`, the element
`E = (12) + ⋯ + (1n)` acts as a diagonalizable endomorphism `T = ρ.asAlgebraHom E` (there is a
basis of eigenvectors) whose eigenvalues are all integers `m` with `1 - n ≤ m ≤ n - 1`. -/
theorem sumTranspositionsWith1_diagonalizable_integer_eigenvalues
    (n : ℕ) [NeZero n]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V),
        ∀ i, ∃ μ : ℂ, (Representation.asAlgebraHom ρ) (sumTranspositionsWith1 n) (b i) = μ • b i) ∧
      (∀ μ : ℂ, Module.End.HasEigenvalue
          ((Representation.asAlgebraHom ρ) (sumTranspositionsWith1 n)) μ →
        ∃ m : ℤ, μ = (m : ℂ) ∧ (1 - (n : ℤ)) ≤ m ∧ m ≤ (n : ℤ) - 1) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  haveI : FiniteDimensional ℂ V := inferInstance
  -- Unitarizability: an invariant positive-definite Hermitian form from Theorem 4.6.2 turns `V`
  -- into an inner product space in which every `ρ g` is a unitary.
  obtain ⟨c, hc⟩ := Theorem4_6_2_existence (Equiv.Perm (Fin (m + 1))) V ρ
  letI icore : InnerProductSpace.Core ℂ V := c
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore inferInstance
  -- `G`-invariance of the inner product.
  have hc' : ∀ (g : Equiv.Perm (Fin (m + 1))) (v w : V),
      (inner ℂ (ρ g v) (ρ g w) : ℂ) = (inner ℂ v w : ℂ) := hc
  -- Each `ρ g` is an isometry.
  have hnorm : ∀ (g : Equiv.Perm (Fin (m + 1))) (x : V), ‖ρ g x‖ = ‖x‖ := by
    intro g x
    have h1 : ‖ρ g x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hc' g x x]
    rw [← Real.sqrt_sq (norm_nonneg (ρ g x)), ← Real.sqrt_sq (norm_nonneg x), h1]
  -- The sum of transpositions through `0`, and its cardinality.
  set S : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun j : Fin (m + 1) => (0 : Fin (m + 1)) < j) with hSdef
  have hScard : S.card = m := by
    have hSe : S = Finset.univ.erase (0 : Fin (m + 1)) := by
      ext j; simp [hSdef, Fin.pos_iff_ne_zero, Finset.mem_erase]
    rw [hSe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  set T : Module.End ℂ V :=
    Representation.asAlgebraHom ρ (sumTranspositionsWith1 (m + 1)) with hTdef
  -- `T = ∑_{0<j} ρ(0 j)`.
  have hTsum : T = ∑ j ∈ S, ρ (Equiv.swap 0 j) := by
    rw [hTdef, sumTranspositionsWith1, map_sum]
    exact Finset.sum_congr rfl (fun j _ => Representation.asAlgebraHom_of ρ (Equiv.swap 0 j))
  -- Each `ρ(0 j)` is symmetric: it is a unitary involution.
  have hswap_symm : ∀ j : Fin (m + 1), (ρ (Equiv.swap (0 : Fin (m + 1)) j)).IsSymmetric := by
    intro j x y
    have hinv : ρ (Equiv.swap (0 : Fin (m + 1)) j) (ρ (Equiv.swap 0 j) y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, Equiv.swap_mul_self, map_one, Module.End.one_apply]
    calc (inner ℂ (ρ (Equiv.swap 0 j) x) y : ℂ)
        = (inner ℂ (ρ (Equiv.swap 0 j) x)
            (ρ (Equiv.swap 0 j) (ρ (Equiv.swap 0 j) y)) : ℂ) := by rw [hinv]
      _ = (inner ℂ x (ρ (Equiv.swap 0 j) y) : ℂ) := hc' _ _ _
  -- Hence `T` is symmetric.
  have hTsym : T.IsSymmetric := by
    intro x y
    rw [hTsum, LinearMap.sum_apply, LinearMap.sum_apply, sum_inner, inner_sum]
    exact Finset.sum_congr rfl (fun j _ => hswap_symm j x y)
  refine ⟨?_, ?_⟩
  · -- Eigenbasis via the spectral theorem for the self-adjoint operator `T`.
    refine ⟨(hTsym.eigenvectorBasis rfl).toBasis, fun i => ⟨(hTsym.eigenvalues rfl i : ℂ), ?_⟩⟩
    rw [OrthonormalBasis.coe_toBasis]
    exact hTsym.apply_eigenvectorBasis rfl i
  · intro μ hμ
    obtain ⟨z, hz⟩ := sumTranspositionsWith1_hasEigenvalue_integer m ρ μ hμ
    -- Bound the eigenvalue via a normalized eigenvector `w'` with `‖w'‖ = 1`.
    obtain ⟨w, hwmem, hwne⟩ := hμ.exists_hasEigenvector
    have hTw : T w = μ • w := Module.End.mem_eigenspace_iff.mp hwmem
    have hwnorm_pos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
    set w' : V := ((‖w‖⁻¹ : ℝ) : ℂ) • w with hw'def
    have hw'norm : ‖w'‖ = 1 := by
      rw [hw'def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hwnorm_pos)]
    have hTw' : T w' = μ • w' := by rw [hw'def, map_smul, hTw, smul_comm]
    -- `μ = ⟪w', T w'⟫`.
    have hμeq : (inner ℂ w' (T w') : ℂ) = μ := by
      rw [hTw', inner_smul_right, inner_self_eq_norm_sq_to_K, hw'norm]; simp
    -- `‖μ‖ ≤ m`, since `⟪w', T w'⟫` is a sum of `m` terms each of modulus `≤ 1`.
    have hbound : ‖μ‖ ≤ (m : ℝ) := by
      rw [← hμeq]
      have hexp : (inner ℂ w' (T w') : ℂ)
          = ∑ j ∈ S, (inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ) := by
        rw [hTsum, LinearMap.sum_apply, inner_sum]
      rw [hexp]
      calc ‖∑ j ∈ S, (inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ)‖
          ≤ ∑ j ∈ S, ‖(inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ S, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            calc ‖(inner ℂ w' (ρ (Equiv.swap 0 j) w') : ℂ)‖
                ≤ ‖w'‖ * ‖ρ (Equiv.swap 0 j) w'‖ := norm_inner_le_norm _ _
              _ = 1 := by rw [hnorm, hw'norm]; norm_num
        _ = (m : ℝ) := by rw [Finset.sum_const, hScard]; simp
    -- Combine with integrality of `μ = z`.
    have hzabs : |z| ≤ (m : ℤ) := by
      have hnormμ : ‖μ‖ = |(z : ℝ)| := by rw [hz, Complex.norm_intCast]
      rw [hnormμ] at hbound
      exact_mod_cast hbound
    obtain ⟨hb1, hb2⟩ := abs_le.mp hzabs
    refine ⟨z, hz, ?_, ?_⟩
    · push_cast; omega
    · push_cast; omega

/-! ### Branching rule for `permEmbZero`

`res_spechtModule_character` (Problem 5.16.1) states the branching rule for the restriction along
`permEmb` (the stabiliser of the last point).  The central element `sumTranspositionsStab`
lives inside the stabiliser of the first point, restriction along `permEmbZero`.  The two
subgroups are conjugate by the cyclic rotation `finRotate (m+1)`; since the Specht character is a
class function, the branching rule transfers verbatim to `permEmbZero`. -/

/-- `permEmb` (last-point stabiliser) sends `Fin.castSucc k` to `Fin.castSucc (σ k)`. -/
lemma permEmb_castSucc (m : ℕ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    permEmb m σ (Fin.castSucc k) = Fin.castSucc (σ k) := by
  have h : permEmb m σ (Fin.castSuccEmb k) = Fin.castSuccEmb (σ k) := by
    rw [permEmb, Equiv.Perm.viaEmbeddingHom_apply]
    exact Equiv.Perm.viaEmbedding_apply σ Fin.castSuccEmb k
  simpa using h

/-- `permEmb` (last-point stabiliser) fixes the last point. -/
lemma permEmb_last (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    permEmb m σ (Fin.last m) = Fin.last m := by
  rw [permEmb, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply_of_notMem]
  simp only [Fin.coe_castSuccEmb, Set.mem_range, not_exists]
  exact fun k => ne_of_lt (Fin.castSucc_lt_last k)

/-- `permEmbZero` (first-point stabiliser) fixes the point `0`. -/
lemma permEmbZero_zero (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    permEmbZero m σ 0 = 0 := by
  rw [permEmbZero, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply_of_notMem]
  simp only [Fin.coe_succEmb, Set.mem_range, not_exists]
  exact fun k => Fin.succ_ne_zero k

/-- `permEmbZero` (first-point stabiliser) sends `Fin.succ k` to `Fin.succ (σ k)`. -/
lemma permEmbZero_succ (m : ℕ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    permEmbZero m σ (Fin.succ k) = Fin.succ (σ k) := by
  have h : permEmbZero m σ (Fin.succEmb m k) = Fin.succEmb m (σ k) := by
    rw [permEmbZero, Equiv.Perm.viaEmbeddingHom_apply]
    exact Equiv.Perm.viaEmbedding_apply σ (Fin.succEmb m) k
  simpa using h

/-- The cyclic rotation `finRotate (m+1)` sends `Fin.castSucc k` to `Fin.succ k`. -/
lemma finRotate_castSucc (m : ℕ) (k : Fin m) :
    finRotate (m + 1) (Fin.castSucc k) = Fin.succ k := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (ne_of_lt (Fin.castSucc_lt_last k))]
  simp [Fin.val_succ, Fin.val_castSucc]

/-- The first-point embedding is conjugate to the last-point embedding by `finRotate (m+1)`. -/
lemma permEmbZero_conj_permEmb (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    permEmbZero m σ = finRotate (m + 1) * permEmb m σ * (finRotate (m + 1))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  induction x using Fin.lastCases with
  | last => rw [finRotate_last, permEmb_last, finRotate_last, permEmbZero_zero]
  | cast k => rw [permEmb_castSucc, finRotate_castSucc, finRotate_castSucc, permEmbZero_succ]

/-- The Specht character is a class function, so it takes the same value on the two conjugate
embeddings `permEmbZero m σ` and `permEmb m σ`. -/
lemma spechtModuleCharacter_conj_permEmbZero (m : ℕ) (la : Nat.Partition (m + 1))
    (σ : Equiv.Perm (Fin m)) :
    spechtModuleCharacter (m + 1) la (permEmbZero m σ) =
      spechtModuleCharacter (m + 1) la (permEmb m σ) := by
  rw [permEmbZero_conj_permEmb]
  exact (spechtModuleRep (m + 1) la).char_conj (permEmb m σ) (finRotate (m + 1))

/-- **Branching rule for `permEmbZero`.** For `la ⊢ m+1` the character of `V_la` on the image of
`Sₘ` under `permEmbZero` (first-point stabiliser) decomposes over `removeSquare la`. -/
lemma spechtModuleCharacter_permEmbZero_eq_sum (m : ℕ) (la : Nat.Partition (m + 1))
    (σ : Equiv.Perm (Fin m)) :
    spechtModuleCharacter (m + 1) la (permEmbZero m σ) =
      ∑ ν ∈ removeSquare la, spechtModuleCharacter m ν σ := by
  rw [spechtModuleCharacter_conj_permEmbZero, res_spechtModule_character]

/-- **Branching is multiplicity-free.** The multiplicity of `V_ν` (`ν ⊢ m`) in the restriction of
`V_la` (`la ⊢ m+1`) to `Sₘ` (first-point stabiliser `permEmbZero`) is `1` if `ν ∈ removeSquare la`
and `0` otherwise. Recovered from the branching character identity by orthonormality of Specht
characters. -/
lemma repIsotypicMult_restrictRep_spechtModule (m : ℕ) (la : Nat.Partition (m + 1))
    (ν : Nat.Partition m) :
    repIsotypicMult m (restrictRep m (spechtModuleRep (m + 1) la)) ν
      = if ν ∈ removeSquare la then 1 else 0 := by
  classical
  set ρW := restrictRep m (spechtModuleRep (m + 1) la) with hρW
  haveI : Module.Finite ℂ ↥(SpechtModule (m + 1) la) := inferInstance
  -- The character of the restricted representation is the branching sum.
  have hchar : ∀ σ : Equiv.Perm (Fin m),
      moduleCharacter m ρW.asModule σ = ∑ ρ ∈ removeSquare la, spechtModuleCharacter m ρ σ := by
    intro σ
    rw [← repCharacter_eq_moduleCharacter m ρW σ]
    have h1 : LinearMap.trace ℂ _ (ρW σ) =
        spechtModuleCharacter (m + 1) la (permEmbZero m σ) := rfl
    rw [h1, spechtModuleCharacter_permEmbZero_eq_sum]
  -- Recover the multiplicity from the character via Specht-character orthonormality.
  have hfac := factorial_mul_isotypicMult m ρW.asModule ν
  have hrhs : ∑ σ : Equiv.Perm (Fin m),
        moduleCharacter m ρW.asModule σ * spechtModuleCharacter m ν σ⁻¹
      = (Nat.factorial m : ℂ) * (if ν ∈ removeSquare la then 1 else 0) := by
    simp_rw [hchar, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun ρ _ => specht_char_inner m ρ ν), ← Finset.mul_sum,
      Finset.sum_ite_eq' (removeSquare la) ν (fun _ => (1 : ℂ))]
  rw [hrhs] at hfac
  have hne : (Nat.factorial m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hmul := mul_left_cancel₀ hne hfac
  change isotypicMult m ρW.asModule ν = _
  by_cases h : ν ∈ removeSquare la
  · simp only [h, if_true] at hmul ⊢; exact_mod_cast hmul
  · simp only [h, if_false] at hmul ⊢; exact_mod_cast hmul

/-! ### `asAlgebraHom` acts by left multiplication on `V_λ`

The algebra homomorphism `asAlgebraHom (spechtModuleRep n la)` sends a group-algebra element `a`
to the endomorphism "left multiply by `a`" on `V_λ ⊆ ℂ[S_n]`. This coe lemma lets us translate
the abstract endomorphism condition back to the concrete left-multiplication condition. -/

/-- `asAlgebraHom (spechtModuleRep n la) a` acts on `V_λ` by left multiplication: its value at
`y ∈ V_λ`, coerced back into `ℂ[S_n]`, is `a * y`. -/
lemma spechtModuleRep_asAlgebraHom_coe (n : ℕ) (la : Nat.Partition n) (a : SymGroupAlgebra n)
    (y : ↥(SpechtModule n la)) :
    ((Representation.asAlgebraHom (spechtModuleRep n la) a) y : SymGroupAlgebra n)
      = a * (y : SymGroupAlgebra n) := by
  obtain ⟨mm, hmm⟩ := y
  induction a using MonoidAlgebra.induction_on with
  | hM σ =>
    rw [Representation.asAlgebraHom_of]
    rfl
  | hadd f g hf hg =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, hf, hg, add_mul]
  | hsmul r f hf =>
    have hsm : (Representation.asAlgebraHom (spechtModuleRep n la)) (r • f)
        = r • (Representation.asAlgebraHom (spechtModuleRep n la)) f := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, AlgHom.commutes]
    rw [hsm, LinearMap.smul_apply, Submodule.coe_smul_of_tower, hf, smul_mul_assoc]

/-! ### Scalar criterion via the branching spectrum

`C_{n-1} = sumTranspositionsStab (m+1)` acts on `V_la` by the scalar `c` iff every
`ν ∈ removeSquare la` has content `c`. The forward direction extracts, for each
`ν ∈ removeSquare la` (multiplicity one in the restriction), an embedded copy of `V_ν` on which
`C_{n-1}` acts by `content ν`; the backward direction uses that the simple constituents of the
restriction are exactly the `V_ν`, `ν ∈ removeSquare la`, on each of which `C_{n-1}` acts by the
common scalar. -/

/-- **Scalar criterion (pointwise).** For a fixed scalar `c`, `C_{n-1} = sumTranspositionsStab
(m+1)` acts on `V_la` by `c` if and only if every `ν ∈ removeSquare la` has content `c`. -/
lemma sumTranspositionsStab_acts_scalar_iff_content_const_of (m : ℕ)
    (la : Nat.Partition (m + 1)) (c : ℂ) :
    (∀ x ∈ SpechtModule (m + 1) la, sumTranspositionsStab (m + 1) * x = c • x)
      ↔ ∀ ν ∈ removeSquare la, (content ν : ℂ) = c := by
  set ρW := restrictRep m (spechtModuleRep (m + 1) la) with hρW
  set B : Module.End ℂ ↥(SpechtModule (m + 1) la) :=
    Representation.asAlgebraHom ρW (sumTranspositions m) with hB
  -- `B` is left multiplication by `C_{n-1}` on `V_la`.
  have hBcoe : ∀ y : ↥(SpechtModule (m + 1) la),
      (B y : SymGroupAlgebra (m + 1))
        = sumTranspositionsStab (m + 1) * (y : SymGroupAlgebra (m + 1)) := by
    intro y
    rw [hB, hρW, ← asAlgebraHom_sumTranspositionsStab m (spechtModuleRep (m + 1) la)]
    exact spechtModuleRep_asAlgebraHom_coe (m + 1) la _ y
  -- The group-algebra scalar condition is the endomorphism scalar condition for `B`.
  have hPiff : (∀ x ∈ SpechtModule (m + 1) la, sumTranspositionsStab (m + 1) * x = c • x)
      ↔ ∀ y : ↥(SpechtModule (m + 1) la), B y = c • y := by
    constructor
    · intro h y
      apply Subtype.ext
      rw [hBcoe, Submodule.coe_smul_of_tower]
      exact h _ y.2
    · intro h x hx
      have h2 := congrArg (Subtype.val) (h ⟨x, hx⟩)
      rwa [hBcoe, Submodule.coe_smul_of_tower] at h2
  rw [hPiff]
  constructor
  · -- (⟹) `B` scalar ⟹ every removable content equals `c`.
    intro hB' ν hν
    have hmult : repIsotypicMult m ρW ν ≠ 0 := by
      have : repIsotypicMult m ρW ν = 1 := by
        rw [hρW, repIsotypicMult_restrictRep_spechtModule, if_pos hν]
      rw [this]; exact one_ne_zero
    obtain ⟨f, hf_inj⟩ := repSpecht_embeds_of_mult_pos m ρW ν hmult
    set y₀ : ↥(SpechtModule m ν) := ⟨YoungSymmetrizer m ν, Submodule.subset_span rfl⟩ with hy0
    have hy0ne : y₀ ≠ 0 := by
      intro h
      have hz : (YoungSymmetrizer m ν : SymGroupAlgebra m) = 0 := congrArg Subtype.val h
      have h1 := youngSymmetrizer_identity_coeff m ν
      rw [hz] at h1
      exact zero_ne_one h1
    set w : ρW.asModule := f y₀ with hw
    have hwne : w ≠ 0 := by
      rw [hw]; intro h; exact hy0ne (hf_inj (h.trans (map_zero f).symm))
    -- `C_{n-1}` acts on `c_ν` by `content ν`.
    have hy0act : sumTranspositions m • y₀ = (content ν : ℂ) • y₀ := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_eq_mul]
      exact sumTranspositions_mul_youngSymmetrizer m ν
    -- transport along `f`: `C_{n-1}` acts on `w = f c_ν` by `content ν`.
    have hwact : sumTranspositions m • w = (content ν : ℂ) • w := by
      have hfy : f (sumTranspositions m • y₀) = f ((content ν : ℂ) • y₀) := by rw [hy0act]
      rw [map_smul, LinearMap.map_smul_of_tower] at hfy
      rw [hw]; exact hfy
    -- combine with the scalar action of `B` on `w`.
    have key : (content ν : ℂ) • (ρW.asModuleEquiv w) = c • (ρW.asModuleEquiv w) := by
      have e2 : ρW.asModuleEquiv (sumTranspositions m • w) = B (ρW.asModuleEquiv w) := by
        rw [Representation.asModuleEquiv_map_smul, hB]
      calc (content ν : ℂ) • (ρW.asModuleEquiv w)
          = ρW.asModuleEquiv ((content ν : ℂ) • w) := by rw [map_smul]
        _ = ρW.asModuleEquiv (sumTranspositions m • w) := by rw [hwact]
        _ = B (ρW.asModuleEquiv w) := e2
        _ = c • (ρW.asModuleEquiv w) := hB' _
    have hwne' : ρW.asModuleEquiv w ≠ 0 :=
      fun h => hwne (ρW.asModuleEquiv.injective (by rw [h, map_zero]))
    exact smul_left_injective ℂ hwne' key
  · -- (⟸) every removable content `= c` ⟹ `B` scalar.
    intro hQ
    set q : SymGroupAlgebra m := sumTranspositions m - algebraMap ℂ (SymGroupAlgebra m) c with hq
    have hqcentral : ∀ a : SymGroupAlgebra m, q * a = a * q := by
      intro a
      rw [hq, sub_mul, mul_sub, sumTranspositions_central, Algebra.commutes]
    set L : ρW.asModule →ₗ[SymGroupAlgebra m] ρW.asModule :=
      { toFun := fun y => q • y
        map_add' := fun a b => smul_add q a b
        map_smul' := fun a y => by
          simp only [RingHom.id_apply]
          rw [smul_smul, smul_smul, hqcentral] } with hL
    have hker : LinearMap.ker L = ⊤ := by
      rw [← top_le_iff, ← IsSemisimpleModule.sSup_simples_eq_top (SymGroupAlgebra m) ρW.asModule]
      refine sSup_le ?_
      rintro W hWsimple
      obtain ⟨ν, ⟨e⟩⟩ :=
        @gen_spechtModules_exhaust_simples m ρW.asModule inferInstance
          (Representation.instModuleMonoidAlgebraAsModule ρW) W hWsimple
      have hνmem : ν ∈ removeSquare la := by
        letI rhoWModule : Module (SymGroupAlgebra m) ρW.asModule :=
          Representation.instModuleMonoidAlgebraAsModule ρW
        letI wModule : Module (SymGroupAlgebra m) W :=
          @Submodule.module (SymGroupAlgebra m) ρW.asModule inferInstance inferInstance
            rhoWModule W
        letI : Module.Finite ℂ ρW.asModule := inferInstance
        letI : IsNoetherian ℂ ρW.asModule :=
          ⟨fun s ↦ Submodule.fg_of_fg_map_injective ρW.asModuleEquiv.toLinearMap
            ρW.asModuleEquiv.injective
            ((Submodule.fg_iff_finiteDimensional
              (s.map ρW.asModuleEquiv.toLinearMap)).2 inferInstance)⟩
        by_contra hνnot
        have hmult0 : repIsotypicMult m ρW ν = 0 := by
          rw [hρW, repIsotypicMult_restrictRep_spechtModule, if_neg hνnot]
        have hcompbot :
            isotypicComponent (SymGroupAlgebra m) ρW.asModule (SpechtModule m ν) = ⊥ := by
          rw [← Submodule.restrictScalars_eq_bot_iff (S := ℂ)]
          letI : Module.Finite ℂ (isotypicComp m ρW.asModule ν) := by
            exact Module.Finite.of_injective (isotypicComp m ρW.asModule ν).subtype
              (Submodule.injective_subtype _)
          have hfrz : isotypicComp m ρW.asModule ν = ⊥ := by
            rw [← Submodule.finrank_eq_zero (R := ℂ) (M := ρW.asModule), isotypicComp_finrank,
              show isotypicMult m ρW.asModule ν = repIsotypicMult m ρW ν from rfl, hmult0, zero_mul]
          exact hfrz
        have hWle :
            W ≤ isotypicComponent (SymGroupAlgebra m) ρW.asModule (SpechtModule m ν) :=
          (@Submodule.le_isotypicComponent (SymGroupAlgebra m) ρW.asModule inferInstance
            inferInstance rhoWModule W).trans_eq
              (@LinearEquiv.isotypicComponent_eq (SymGroupAlgebra m) ρW.asModule W
                (SpechtModule m ν) inferInstance inferInstance inferInstance inferInstance
                rhoWModule wModule inferInstance e)
        rw [hcompbot, le_bot_iff] at hWle
        haveI : Nontrivial (SpechtModule m ν) :=
          (Theorem5_12_2_irreducible m ν).nontrivial
        letI : Nontrivial W := e.toEquiv.nontrivial
        exact absurd hWle (Submodule.nontrivial_iff_ne_bot.mp inferInstance)
      have hcν : (content ν : ℂ) = c := hQ ν hνmem
      intro w hw
      rw [LinearMap.mem_ker]
      change q • w = 0
      set wW : ↥W := ⟨w, hw⟩ with hwW
      have hact_Vnu : sumTranspositions m • (e wW) = (content ν : ℂ) • (e wW) := by
        apply Subtype.ext
        rw [Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_eq_mul]
        exact sumTranspositions_mul_eq_content_smul m ν _ (e wW).2
      have hq_eWW : q • (e wW) = 0 := by
        rw [hq]
        calc
          (sumTranspositions m - algebraMap ℂ (SymGroupAlgebra m) c) • e wW =
              sumTranspositions m • e wW -
                algebraMap ℂ (SymGroupAlgebra m) c • e wW :=
            @sub_smul (SymGroupAlgebra m) (SpechtModule m ν) inferInstance inferInstance
              inferInstance _ _ _
          _ = 0 := by rw [hact_Vnu, algebraMap_smul, hcν, sub_self]
      have hq_wW : q • wW = 0 := by
        apply e.injective
        rw [map_smul, map_zero, hq_eWW]
      have hcoe := congrArg (Subtype.val) hq_wW
      rw [Submodule.coe_smul, Submodule.coe_zero] at hcoe
      exact hcoe
    have hLzero : L = 0 := LinearMap.ker_eq_top.mp hker
    have hgoal : ∀ z : ρW.asModule, sumTranspositions m • z = c • z := by
      intro z
      have hqz : q • z = 0 := by
        have h : L z = 0 := by rw [hLzero, LinearMap.zero_apply]
        exact h
      rw [hq] at hqz
      have hsub :
          (sumTranspositions m - algebraMap ℂ (SymGroupAlgebra m) c) • z =
            sumTranspositions m • z - algebraMap ℂ (SymGroupAlgebra m) c • z :=
        @sub_smul (SymGroupAlgebra m) ρW.asModule inferInstance inferInstance
          (Representation.instModuleMonoidAlgebraAsModule ρW) _ _ _
      have halg : algebraMap ℂ (SymGroupAlgebra m) c • z = c • z :=
        @algebraMap_smul ℂ inferInstance (SymGroupAlgebra m) inferInstance inferInstance
          ρW.asModule inferInstance (Representation.instModuleMonoidAlgebraAsModule ρW)
          inferInstance inferInstance c z
      have hqz' : sumTranspositions m • z - c • z = 0 := by
        rw [← halg, ← hsub]
        exact hqz
      exact sub_eq_zero.mp hqz'
    intro y
    have hgy := hgoal (ρW.asModuleEquiv.symm y)
    have e1 : ρW.asModuleEquiv (sumTranspositions m • ρW.asModuleEquiv.symm y) = B y := by
      rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, hB]
    calc B y = ρW.asModuleEquiv (sumTranspositions m • ρW.asModuleEquiv.symm y) := e1.symm
      _ = ρW.asModuleEquiv (c • ρW.asModuleEquiv.symm y) := by rw [hgy]
      _ = c • ρW.asModuleEquiv (ρW.asModuleEquiv.symm y) := by rw [map_smul]
      _ = c • y := by rw [LinearEquiv.apply_symm_apply]

/-- **Scalar criterion.** `C_{n-1} = sumTranspositionsStab (m+1)` acts on `V_la` by a scalar `c`
if and only if every `ν ∈ removeSquare la` has content `c`. -/
lemma sumTranspositionsStab_acts_scalar_iff_content_const (m : ℕ) (la : Nat.Partition (m + 1)) :
    (∃ c : ℂ, ∀ x ∈ SpechtModule (m + 1) la, sumTranspositionsStab (m + 1) * x = c • x)
      ↔ ∃ c : ℂ, ∀ ν ∈ removeSquare la, (content ν : ℂ) = c :=
  exists_congr (sumTranspositionsStab_acts_scalar_iff_content_const_of m la)

/-! ### Corner/content combinatorics

`content` is constant on `removeSquare la` if and only if `la` is rectangular. Removable corners
of `la` occupy strictly decreasing rows with strictly decreasing columns, so their box contents
`col − row` are pairwise distinct; hence `content` is injective on the (nonempty) set
`removeSquare la`, and constancy forces a single removable corner, i.e. a rectangle. -/

/-- Cell membership in a partition's Young diagram, via sorted row lengths. -/
private lemma mem_cells_iff_getD {n : ℕ} (la : Nat.Partition n) (i j : ℕ) :
    (i, j) ∈ la.toYoungDiagram.cells ↔ j < la.sortedParts.getD i 0 := by
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    Nat.Partition.toYoungDiagram_rowLen_eq_getD]

/-- Outer-corner characterisation via sorted parts: `(i, j)` is an outer corner iff row `i`
is nonempty with rightmost cell `j = L[i] − 1` and is strictly longer than row `i + 1`. -/
private lemma isOuterCorner_iff {n : ℕ} (la : Nat.Partition n) (i j : ℕ) :
    la.toYoungDiagram.IsOuterCorner i j ↔
      j + 1 = la.sortedParts.getD i 0 ∧
        la.sortedParts.getD (i + 1) 0 < la.sortedParts.getD i 0 := by
  simp only [YoungDiagram.IsOuterCorner, mem_cells_iff_getD, not_lt]
  omega

/-- Removing an outer corner drops the content by that corner's `col − row`. -/
private lemma content_removeOuterCorner {m : ℕ} (la : Nat.Partition (m + 1)) (c : ℕ × ℕ)
    (hc : la.toYoungDiagram.IsOuterCorner c.1 c.2) :
    content (la.removeOuterCorner c hc) = content la - ((c.2 : ℤ) - c.1) := by
  rw [content, content, Nat.Partition.toYoungDiagram_removeOuterCorner,
    show (la.toYoungDiagram.removeCorner c.1 c.2 hc).cells
      = la.toYoungDiagram.cells.erase (c.1, c.2) from rfl,
    Finset.sum_erase_eq_sub hc.1]

/-- Removing an outer corner lands inside `removeSquare la`. -/
private lemma removeOuterCorner_mem_removeSquare {m : ℕ} (la : Nat.Partition (m + 1)) (c : ℕ × ℕ)
    (hc : la.toYoungDiagram.IsOuterCorner c.1 c.2) :
    la.removeOuterCorner c hc ∈ removeSquare la := by
  rw [removeSquare, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← YoungDiagram.cells_subset_iff, Nat.Partition.toYoungDiagram_removeOuterCorner,
    show (la.toYoungDiagram.removeCorner c.1 c.2 hc).cells
      = la.toYoungDiagram.cells.erase (c.1, c.2) from rfl]
  exact Finset.erase_subset _ _

/-- Every `ν ∈ removeSquare la` arises by deleting a single outer corner `d`, and its content is
`content la − (col(d) − row(d))`. -/
private lemma removeSquare_content {m : ℕ} (la : Nat.Partition (m + 1)) (ν : Nat.Partition m)
    (hν : ν ∈ removeSquare la) :
    ∃ d : ℕ × ℕ, la.toYoungDiagram.IsOuterCorner d.1 d.2 ∧
      content ν = content la - ((d.2 : ℤ) - d.1) := by
  rw [removeSquare, Finset.mem_filter] at hν
  have hle : ν.toYoungDiagram ≤ la.toYoungDiagram := hν.2
  have hsub : ν.toYoungDiagram.cells ⊆ la.toYoungDiagram.cells :=
    YoungDiagram.cells_subset_iff.mpr hle
  have hcardla : la.toYoungDiagram.cells.card = m + 1 := la.toYoungDiagram_card
  have hcardν : ν.toYoungDiagram.cells.card = m := ν.toYoungDiagram_card
  have hcardsdiff : (la.toYoungDiagram.cells \ ν.toYoungDiagram.cells).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcardla, hcardν]; omega
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcardsdiff
  have hd_mem : d ∈ la.toYoungDiagram.cells \ ν.toYoungDiagram.cells := by
    rw [hd]; exact Finset.mem_singleton_self d
  rw [Finset.mem_sdiff] at hd_mem
  obtain ⟨hd_la, hd_nν⟩ := hd_mem
  have hcontent : content la = content ν + ((d.2 : ℤ) - d.1) := by
    rw [content, content, ← Finset.sum_sdiff hsub, hd, Finset.sum_singleton]; ring
  have hcorner : la.toYoungDiagram.IsOuterCorner d.1 d.2 := by
    refine ⟨hd_la, ?_, ?_⟩
    · intro hbelow
      by_cases hb_ν : (d.1 + 1, d.2) ∈ ν.toYoungDiagram.cells
      · exact hd_nν ((YoungDiagram.mem_cells _).mpr
          (ν.toYoungDiagram.up_left_mem (Nat.le_succ _) le_rfl
            ((YoungDiagram.mem_cells _).mp hb_ν)))
      · have hmemsd : (d.1 + 1, d.2) ∈ la.toYoungDiagram.cells \ ν.toYoungDiagram.cells :=
          Finset.mem_sdiff.mpr ⟨hbelow, hb_ν⟩
        rw [hd, Finset.mem_singleton] at hmemsd
        have hcontra : d.1 + 1 = d.1 := congrArg Prod.fst hmemsd
        omega
    · intro hright
      by_cases hr_ν : (d.1, d.2 + 1) ∈ ν.toYoungDiagram.cells
      · exact hd_nν ((YoungDiagram.mem_cells _).mpr
          (ν.toYoungDiagram.up_left_mem le_rfl (Nat.le_succ _)
            ((YoungDiagram.mem_cells _).mp hr_ν)))
      · have hmemsd : (d.1, d.2 + 1) ∈ la.toYoungDiagram.cells \ ν.toYoungDiagram.cells :=
          Finset.mem_sdiff.mpr ⟨hright, hr_ν⟩
        rw [hd, Finset.mem_singleton] at hmemsd
        have hcontra : d.2 + 1 = d.2 := congrArg Prod.snd hmemsd
        omega
  exact ⟨d, hcorner, by rw [hcontent]; ring⟩

/-- **Corner/content criterion.** `content` is constant on `removeSquare la` iff `la` is
rectangular. -/
lemma content_const_removeSquare_iff_rectangular (m : ℕ) (la : Nat.Partition (m + 1)) :
    (∃ c : ℂ, ∀ ν ∈ removeSquare la, (content ν : ℂ) = c) ↔ IsRectangular la := by
  set r := la.sortedParts.length with hr
  have hsum : la.sortedParts.sum = m + 1 := by
    have h1 : Multiset.sum (↑la.sortedParts) = la.sortedParts.sum := Multiset.sum_coe _
    rw [← h1, show (↑la.sortedParts : Multiset ℕ) = la.parts from
      Multiset.sort_eq la.parts (· ≥ ·), la.parts_sum]
  have hrpos : 0 < r := by
    rw [hr]
    by_contra h
    push Not at h
    have hnil : la.sortedParts = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    rw [hnil, List.sum_nil] at hsum
    exact absurd hsum (by omega)
  have hpos : ∀ i, i < r → 0 < la.sortedParts.getD i 0 := by
    intro i hi
    rw [List.getD_eq_getElem la.sortedParts 0 (hr ▸ hi)]
    apply la.parts_pos
    rw [← show (↑la.sortedParts : Multiset ℕ) = la.parts from Multiset.sort_eq la.parts (· ≥ ·)]
    exact Multiset.mem_coe.mpr (List.getElem_mem (hr ▸ hi))
  have hanti : ∀ i, la.sortedParts.getD (i + 1) 0 ≤ la.sortedParts.getD i 0 := by
    intro i
    rw [← Nat.Partition.toYoungDiagram_rowLen_eq_getD la i,
        ← Nat.Partition.toYoungDiagram_rowLen_eq_getD la (i + 1)]
    exact la.toYoungDiagram.rowLen_anti i (i + 1) (Nat.le_succ i)
  have hzero : ∀ i, r ≤ i → la.sortedParts.getD i 0 = 0 := by
    intro i hi
    exact List.getD_eq_default la.sortedParts 0 (hr ▸ hi)
  -- the bottom removable corner, always present
  have hbot : la.toYoungDiagram.IsOuterCorner
      (r - 1, la.sortedParts.getD (r - 1) 0 - 1).1
      (r - 1, la.sortedParts.getD (r - 1) 0 - 1).2 := by
    change la.toYoungDiagram.IsOuterCorner (r - 1) (la.sortedParts.getD (r - 1) 0 - 1)
    rw [isOuterCorner_iff]
    have h1 : 0 < la.sortedParts.getD (r - 1) 0 := hpos (r - 1) (by omega)
    have h2 : la.sortedParts.getD r 0 = 0 := hzero r le_rfl
    have hr1 : r - 1 + 1 = r := by omega
    exact ⟨by omega, by rw [hr1, h2]; exact h1⟩
  constructor
  · -- content constant ⟹ rectangular
    rintro ⟨cc, hc⟩
    by_contra hnrect
    -- some interior strict descent exists
    have hdescent : ∃ i, i + 1 < r ∧ la.sortedParts.getD (i + 1) 0 < la.sortedParts.getD i 0 := by
      by_contra hno
      push Not at hno
      apply hnrect
      have hconst : ∀ k, k < r → la.sortedParts.getD k 0 = la.sortedParts.getD 0 0 := by
        intro k
        induction k with
        | zero => intro _; rfl
        | succ j ih =>
          intro hjr
          have hle := hno j (by omega)
          have hge := hanti j
          have hij := ih (by omega)
          omega
      have hallc : ∀ x ∈ la.sortedParts, x = la.sortedParts.getD 0 0 := by
        rw [List.forall_mem_iff_getElem]
        intro i hi
        rw [← List.getD_eq_getElem la.sortedParts 0 hi]
        exact hconst i (hr.symm ▸ hi)
      have hcoe : (↑la.sortedParts : Multiset ℕ) = la.parts :=
        Multiset.sort_eq la.parts (· ≥ ·)
      refine ⟨r, la.sortedParts.getD 0 0, ?_⟩
      have hrep : la.sortedParts = List.replicate r (la.sortedParts.getD 0 0) := by
        rw [hr]; exact List.eq_replicate_length.mpr hallc
      calc la.parts = (↑la.sortedParts : Multiset ℕ) := hcoe.symm
        _ = (↑(List.replicate r (la.sortedParts.getD 0 0)) : Multiset ℕ) := by rw [← hrep]
        _ = Multiset.replicate r (la.sortedParts.getD 0 0) := Multiset.coe_replicate _ _
    obtain ⟨i₀, hi₀r, hi₀desc⟩ := hdescent
    have hcorner1 : la.toYoungDiagram.IsOuterCorner
        (i₀, la.sortedParts.getD i₀ 0 - 1).1
        (i₀, la.sortedParts.getD i₀ 0 - 1).2 := by
      change la.toYoungDiagram.IsOuterCorner i₀ (la.sortedParts.getD i₀ 0 - 1)
      rw [isOuterCorner_iff]
      have hpi : 0 < la.sortedParts.getD i₀ 0 := hpos i₀ (by omega)
      exact ⟨by omega, hi₀desc⟩
    have hmem1 := removeOuterCorner_mem_removeSquare la (i₀, la.sortedParts.getD i₀ 0 - 1) hcorner1
    have hmem2 :=
      removeOuterCorner_mem_removeSquare la (r - 1, la.sortedParts.getD (r - 1) 0 - 1) hbot
    have hval1 := hc _ hmem1
    have hval2 := hc _ hmem2
    rw [content_removeOuterCorner] at hval1 hval2
    have hZ := Int.cast_injective (α := ℂ) (hval1.trans hval2.symm)
    have hpi : 0 < la.sortedParts.getD i₀ 0 := hpos i₀ (by omega)
    have hpb : 0 < la.sortedParts.getD (r - 1) 0 := hpos (r - 1) (by omega)
    have hmono : la.sortedParts.getD (r - 1) 0 ≤ la.sortedParts.getD i₀ 0 := by
      rw [← Nat.Partition.toYoungDiagram_rowLen_eq_getD la i₀,
          ← Nat.Partition.toYoungDiagram_rowLen_eq_getD la (r - 1)]
      exact la.toYoungDiagram.rowLen_anti i₀ (r - 1) (by omega)
    omega
  · -- rectangular ⟹ content constant
    intro hrect
    obtain ⟨R, cval, hRc⟩ := hrect
    have hLc : ∀ x ∈ la.sortedParts, x = cval := by
      intro x hx
      have hmem : x ∈ la.parts := by
        rw [← show (↑la.sortedParts : Multiset ℕ) = la.parts from Multiset.sort_eq la.parts (· ≥ ·)]
        exact Multiset.mem_coe.mpr hx
      rw [hRc] at hmem
      exact Multiset.eq_of_mem_replicate hmem
    have hconst : ∀ i, i < r → la.sortedParts.getD i 0 = cval := by
      intro i hi
      rw [List.getD_eq_getElem la.sortedParts 0 (hr ▸ hi)]
      exact hLc _ (List.getElem_mem (hr ▸ hi))
    refine ⟨((content la - (((cval - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))) : ℂ), ?_⟩
    intro ν hν
    obtain ⟨d, hd_corner, hd_content⟩ := removeSquare_content la ν hν
    rw [isOuterCorner_iff] at hd_corner
    obtain ⟨hd1, hd2⟩ := hd_corner
    have hd1r : d.1 < r := by
      by_contra h
      push Not at h
      rw [hzero d.1 h] at hd1
      omega
    have hd1eq : d.1 = r - 1 := by
      by_contra h
      have hd1lt : d.1 + 1 < r := by omega
      rw [hconst d.1 hd1r, hconst (d.1 + 1) hd1lt] at hd2
      omega
    have hval : la.sortedParts.getD d.1 0 = cval := hconst d.1 hd1r
    have hd2val : d.2 = cval - 1 := by
      have hh := hd1
      rw [hval] at hh
      omega
    rw [hd_content, hd2val, hd1eq]
    push_cast
    ring

/-- Problem 5.16.3(b). The element `E = (12) + ⋯ + (1n)` acts on the Specht module
`V_λ = ℂ[S_n]·c_λ` (by left multiplication) by a scalar if and only if `λ` is a rectangular
Young diagram. -/
theorem sumTranspositionsWith1_acts_scalar_iff_rectangular
    (n : ℕ) [NeZero n] (la : Nat.Partition n) :
    (∃ c : ℂ, ∀ x ∈ SpechtModule n la, sumTranspositionsWith1 n * x = c • x) ↔
      IsRectangular la := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  rw [← content_const_removeSquare_iff_rectangular m la,
    ← sumTranspositionsStab_acts_scalar_iff_content_const m la]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(content la : ℂ) - c, fun x hx => ?_⟩
    have hCn := sumTranspositions_mul_eq_content_smul (m + 1) la x hx
    have hE := hc x hx
    have hstabx : sumTranspositionsStab (m + 1) * x
        = sumTranspositions (m + 1) * x - sumTranspositionsWith1 (m + 1) * x := by
      have hsub : sumTranspositionsStab (m + 1)
          = sumTranspositions (m + 1) - sumTranspositionsWith1 (m + 1) := by
        rw [sumTranspositionsWith1_eq_sub]; abel
      rw [hsub, sub_mul]
    rw [hstabx, hCn, hE, ← sub_smul]
  · rintro ⟨c, hc⟩
    refine ⟨(content la : ℂ) - c, fun x hx => ?_⟩
    have hCn := sumTranspositions_mul_eq_content_smul (m + 1) la x hx
    have hstab := hc x hx
    have hEx : sumTranspositionsWith1 (m + 1) * x
        = sumTranspositions (m + 1) * x - sumTranspositionsStab (m + 1) * x := by
      rw [sumTranspositionsWith1_eq_sub, sub_mul]
    rw [hEx, hCn, hstab, ← sub_smul]

/-- **Problem 5.16.3(b), the scalar.** For a *rectangular* `λ` with `r` rows each of length `c`
(`la.parts = Multiset.replicate r c`, so `r · c = n`), the element `E = (12) + ⋯ + (1n)` acts on
the Specht module `V_λ = ℂ[S_n]·c_λ` (by left multiplication) by the scalar `c − r`.

This is the content `(c − 1) − (r − 1)` of the unique removable corner `(r − 1, c − 1)`. Endpoint
sanity checks against the part-(a) bound `[1 − n, n − 1]`: the trivial representation
`λ = (n)` (`r = 1`, `c = n`) gives `n − 1`, and the sign representation `λ = (1ⁿ)`
(`r = n`, `c = 1`) gives `1 − n`. -/
theorem sumTranspositionsWith1_scalar_on_rectangular
    (n : ℕ) [NeZero n] (la : Nat.Partition n) (r c : ℕ)
    (hrc : la.parts = Multiset.replicate r c) :
    ∀ x ∈ SpechtModule n la, sumTranspositionsWith1 n * x = ((c : ℤ) - r : ℂ) • x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  -- Read off the sorted-row data from the rectangle: `r` rows, each of length `c`.
  have hcoe : (↑la.sortedParts : Multiset ℕ) = la.parts := Multiset.sort_eq la.parts (· ≥ ·)
  have hlen : la.sortedParts.length = r := by
    rw [← Multiset.coe_card, hcoe, hrc, Multiset.card_replicate]
  have hval : ∀ i, i < r → la.sortedParts.getD i 0 = c := by
    intro i hi
    have hib : i < la.sortedParts.length := by omega
    rw [List.getD_eq_getElem la.sortedParts 0 hib]
    have hmem : la.sortedParts[i] ∈ la.parts := by
      rw [← hcoe]; exact Multiset.mem_coe.mpr (List.getElem_mem hib)
    rw [hrc] at hmem
    exact Multiset.eq_of_mem_replicate hmem
  have hz : ∀ i, r ≤ i → la.sortedParts.getD i 0 = 0 := fun i hi =>
    List.getD_eq_default la.sortedParts 0 (by omega)
  -- `r · c = n = m + 1`, so both dimensions are positive.
  have hmul : r * c = m + 1 := by
    have h := la.parts_sum
    rwa [hrc, Multiset.sum_replicate, smul_eq_mul] at h
  have hrpos : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hmul)
  have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hmul)
  -- Every `ν ∈ removeSquare la` has content `content λ − (c − r)`: the unique removable corner of
  -- a rectangle is `(r − 1, c − 1)`, with content `(c − 1) − (r − 1) = c − r`.
  have hcontent_const : ∀ ν ∈ removeSquare la,
      (content ν : ℂ) = (content la : ℂ) - ((c : ℂ) - r) := by
    intro ν hν
    obtain ⟨d, hd_corner, hd_content⟩ := removeSquare_content la ν hν
    rw [isOuterCorner_iff] at hd_corner
    obtain ⟨hd1, hd2⟩ := hd_corner
    -- Row `d.1` is nonempty, so `d.1 < r` and its length is `c`.
    have hpos1 : 0 < la.sortedParts.getD d.1 0 := lt_of_le_of_lt (Nat.zero_le _) hd2
    have hd1r : d.1 < r := by
      by_contra h; push Not at h; rw [hz d.1 h] at hpos1; omega
    have hvald1 : la.sortedParts.getD d.1 0 = c := hval d.1 hd1r
    -- Row `d.1 + 1` is strictly shorter, forcing `d.1 + 1 ≥ r`, hence `d.1 = r − 1`.
    have hd1eq : d.1 = r - 1 := by
      by_contra h
      have hlt : d.1 + 1 < r := by omega
      rw [hval (d.1 + 1) hlt, hvald1] at hd2; omega
    have hd2eq : d.2 = c - 1 := by rw [hvald1] at hd1; omega
    have hZ : content ν = content la - ((c : ℤ) - r) := by
      rw [hd_content, hd1eq, hd2eq]; omega
    rw [hZ]; push_cast; ring
  -- On `V_λ`, `C_{n-1} = sumTranspositionsStab` acts by that same scalar `content λ − (c − r)`.
  have hstab : ∀ x ∈ SpechtModule (m + 1) la,
      sumTranspositionsStab (m + 1) * x = ((content la : ℂ) - ((c : ℂ) - r)) • x :=
    (sumTranspositionsStab_acts_scalar_iff_content_const_of m la _).mpr hcontent_const
  -- `E = C_n − C_{n-1}`; subtract the two scalars: `content λ − (content λ − (c − r)) = c − r`.
  intro x hx
  have hCn := sumTranspositions_mul_eq_content_smul (m + 1) la x hx
  have hEx : sumTranspositionsWith1 (m + 1) * x
      = sumTranspositions (m + 1) * x - sumTranspositionsStab (m + 1) * x := by
    rw [sumTranspositionsWith1_eq_sub, sub_mul]
  rw [hEx, hCn, hstab x hx, ← sub_smul]
  congr 1
  push_cast
  ring

end Etingof
