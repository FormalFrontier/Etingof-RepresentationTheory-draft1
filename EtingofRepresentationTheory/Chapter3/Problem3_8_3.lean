import EtingofRepresentationTheory.Chapter3.Lemma3_8_2
import EtingofRepresentationTheory.Chapter3.Theorem3_8_1

/-!
# Problem 3.8.3: Krull-Schmidt theorem without algebraic closure

> The above proof of Lemma 3.8.2 uses the condition that `k` is an algebraically
> closed field. Prove Lemma 3.8.2 (and hence the Krull-Schmidt theorem) without
> this condition.

The book proves Lemma 3.8.2(i) — every endomorphism of a finite dimensional
indecomposable representation is an isomorphism or nilpotent — by decomposing `W`
into generalized eigenspaces of `θ`. That argument needs an eigenvalue to exist,
i.e. it needs `k` algebraically closed.

The formalization of Lemma 3.8.2 in `Chapter3/Lemma3_8_2.lean` never uses this
hypothesis. `Etingof.endo_indecomposable_iso_or_nilpotent` replaces the
generalized-eigenspace decomposition with the **Fitting decomposition**
`W = ⨆ₙ ker(θⁿ) ⊕ ⨅ₙ range(θⁿ)`
(`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`), which holds for any endomorphism
of a module that is both Noetherian and Artinian. A finite dimensional module over
`k` is Noetherian and Artinian as an `A`-module regardless of whether `k` is
algebraically closed, so both parts of Lemma 3.8.2 — and consequently the existence
and uniqueness halves of Theorem 3.8.1 — are already established over an arbitrary
field.

This file therefore contains no new proof: it records Problem 3.8.3 as the
observation that the general-field statements are exactly the lemmas that were
proved, and gives named citation targets. In particular Problem 3.8.4 cites "the
Krull-Schmidt theorem, valid over any field by Problem 3.8.3"; the referent is
`Etingof.Problem3_8_3.krull_schmidt_uniqueness` below.

Every statement here assumes only `[Field k]`, with no `IsAlgClosed k`.
-/

namespace Etingof.Problem3_8_3

/-- Lemma 3.8.2(i) over an arbitrary (not necessarily algebraically closed) field:
any endomorphism of a finite dimensional indecomposable representation is an
isomorphism or nilpotent. This is `Etingof.endo_indecomposable_iso_or_nilpotent`,
whose proof uses the Fitting decomposition rather than generalized eigenspaces and
so needs no algebraic-closure hypothesis. -/
theorem endo_iso_or_nilpotent (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : Etingof.IsIndecomposable A W) (θ : W →ₗ[A] W) :
    Function.Bijective θ ∨ IsNilpotent θ :=
  Etingof.endo_indecomposable_iso_or_nilpotent k A W hW θ

/-- Lemma 3.8.2(ii) over an arbitrary field: a sum of nilpotent endomorphisms of a
finite dimensional indecomposable representation is nilpotent. Derived from part (i)
by induction, so likewise valid without algebraic closure. -/
theorem sum_nilpotent_endo (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : Etingof.IsIndecomposable A W)
    {n : ℕ} (θ : Fin n → (W →ₗ[A] W)) (hθ : ∀ i, IsNilpotent (θ i)) :
    IsNilpotent (∑ i, θ i) :=
  Etingof.sum_nilpotent_endo_indecomposable k A W hW θ hθ

/-- The Krull-Schmidt theorem (existence half) over an arbitrary field: every finite
dimensional representation decomposes as an internal direct sum of indecomposable
submodules. -/
theorem krull_schmidt_existence (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, Etingof.IsIndecomposable A (W i)) ∧
      iSup W = ⊤ ∧ iSupIndep W :=
  Etingof.krull_schmidt_existence k A V

/-- The Krull-Schmidt theorem (uniqueness half) over an arbitrary field: any two
decompositions of a finite dimensional representation into indecomposable summands
have the same length and are matched by an isomorphism-preserving permutation. This
is the statement cited by Problem 3.8.4 as "the Krull-Schmidt theorem, valid over
any field by Problem 3.8.3". -/
theorem krull_schmidt_uniqueness (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, Etingof.IsIndecomposable A (W i))
    (hW'_indec : ∀ i, Etingof.IsIndecomposable A (W' i))
    (hW_ne : ∀ i, W i ≠ ⊥) (hW'_ne : ∀ i, W' i ≠ ⊥)
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W') :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) :=
  Etingof.krull_schmidt_uniqueness k A V W W'
    hW_indec hW'_indec hW_ne hW'_ne hW_sup hW_ind hW'_sup hW'_ind

end Etingof.Problem3_8_3
