import Mathlib

/-!
# Coordinate submodules of a diagonal operator, and an irreducibility criterion

This file isolates the *linear-algebra* heart of Problem 4.12.3 from Etingof's book (the
irreducibility of `SⁿV` and `∧ⁿV` as `GL(V)`-representations, cited in Example 5.19.3).

The argument there has two reusable, representation-free ingredients:

* **Diagonal ⟹ coordinate submodule.** If a linear operator `T` acts diagonally on a basis
  `b` with *pairwise distinct* eigenvalues (`w` injective), then every `T`-invariant submodule
  `W` is a *coordinate submodule*: a basis vector's coordinate of an element of `W` can only be
  nonzero on basis vectors that themselves lie in `W` (`mem_of_repr_ne_zero`). This is the
  "distinct eigenvalues ⟹ a subrepresentation is spanned by a subset of the eigenbasis" step of
  the Hint. We prove it directly with a Lagrange-style product `∏ (T - wₛ)`, so it needs no
  finite-dimensionality and no eigenspace machinery.

* **Connectivity ⟹ irreducible.** If, on top of that, the basis indices are connected by a
  relation `Adj` that is *realised inside* `W` (whenever `b s ∈ W` and `Adj s t` then `b t ∈ W`),
  then `W` is `⊥` or the whole space. This is the "use the transvections `ρ(1 + Eᵢⱼ)` to show the
  spanning subset is everything once it is nonempty" step of the Hint.

Both are stated for an arbitrary basis over a field; the case-specific work (exhibiting the
diagonal element with distinct eigenvalues, and realising `Adj` via transvections) is done by the
caller.
-/

open scoped BigOperators
open Module

namespace Etingof.DiagonalCoordinate

variable {k : Type*} [Field k]
  {M : Type*} [AddCommGroup M] [Module k M]
  {B : Type*} (b : Basis B k M)

section CoordinateSubmodule

variable {T : Module.End k M} {w : B → k}

open Polynomial

/-- A polynomial in a `W`-invariant operator preserves `W`. -/
private lemma aeval_mem {W : Submodule k M} (hW : ∀ x ∈ W, T x ∈ W) (q : k[X]) :
    ∀ z ∈ W, aeval T q z ∈ W := by
  induction q using Polynomial.induction_on with
  | C a => intro z hz; rw [aeval_C, Module.algebraMap_end_apply]; exact W.smul_mem a hz
  | add p q hp hq =>
    intro z hz; rw [map_add, LinearMap.add_apply]; exact W.add_mem (hp z hz) (hq z hz)
  | monomial n a ih =>
    intro z hz
    rw [show C a * X ^ (n + 1) = (C a * X ^ n) * X by ring, map_mul, Module.End.mul_apply, aeval_X]
    exact ih (T z) (hW z hz)

/-- **Diagonal operator ⟹ coordinate submodule.** If `T` acts diagonally on the basis `b` with
pairwise distinct eigenvalues `w`, then any `T`-invariant submodule `W` contains every basis
vector `b t` whose coordinate appears in some element of `W`. Equivalently, `W` is spanned by a
subset of the eigenbasis.

The proof is the Lagrange-interpolation argument: the polynomial `p = ∏_{s ≠ t} (X - w s)`
evaluated at `T` annihilates every eigencomponent of `y` except the `t`-component, which it
scales by the nonzero `∏_{s ≠ t} (w t - w s)`; since `aeval T p` preserves `W`, the surviving
component `b t` lies in `W`. -/
theorem mem_of_repr_ne_zero (hT : ∀ s, T (b s) = w s • b s) (hw : Function.Injective w)
    {W : Submodule k M} (hW : ∀ x ∈ W, T x ∈ W)
    {y : M} (hy : y ∈ W) {t : B} (ht : b.repr y t ≠ 0) : b t ∈ W := by
  classical
  set σ := (b.repr y).support with hσ
  have htσ : t ∈ σ := Finsupp.mem_support_iff.mpr ht
  -- The interpolating polynomial killing every eigenvalue except `w t`.
  set p : k[X] := ∏ s ∈ σ.erase t, (X - C (w s)) with hp
  -- Scalar that survives at `t`.
  set c := ∏ s ∈ σ.erase t, (w t - w s) with hc
  have hcne : c ≠ 0 := by
    rw [hc, Finset.prod_ne_zero_iff]
    intro s hs
    exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hw h).symm)
  -- `aeval T p` acts on each basis vector `b u` as the scalar `p.eval (w u)`.
  have heval : ∀ u, aeval T p (b u) = (∏ s ∈ σ.erase t, (w u - w s)) • b u := by
    intro u
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hT u)]
    congr 1
    rw [hp, eval_prod]
    exact Finset.prod_congr rfl (fun s _ => by rw [eval_sub, eval_X, eval_C])
  -- Expand `y` along the basis and push `aeval T p` through.
  have hyexp : y = (b.repr y).sum (fun i a => a • b i) := by
    conv_lhs => rw [← b.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply]
  have hPy : aeval T p y = (b.repr y t * c) • b t := by
    conv_lhs => rw [hyexp]
    rw [map_finsuppSum, Finsupp.sum, Finset.sum_eq_single t]
    · rw [map_smul, heval t, smul_smul]
    · intro u hu hut
      rw [map_smul, heval u]
      have : (∏ s ∈ σ.erase t, (w u - w s)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hut, hu⟩) (by simp)
      rw [this, zero_smul, smul_zero]
    · intro h; exact absurd htσ h
  -- `aeval T p y ∈ W`, and the surviving scalar is nonzero, so `b t ∈ W`.
  have hPyW : aeval T p y ∈ W := aeval_mem hW p y hy
  rw [hPy] at hPyW
  have hscale : b.repr y t * c ≠ 0 := mul_ne_zero ht hcne
  have := W.smul_mem (b.repr y t * c)⁻¹ hPyW
  rwa [smul_smul, inv_mul_cancel₀ hscale, one_smul] at this

end CoordinateSubmodule

section Irreducible

variable {T : Module.End k M} {w : B → k}

/-- **Connectivity ⟹ irreducible.** Suppose `T` acts diagonally on the basis `b` with pairwise
distinct eigenvalues, and `Adj` is a relation on the index set `B` such that:

* any two indices are connected by `Adj` (`hconn`), and
* `Adj` is *realised inside* `W`: whenever `b s ∈ W` and `Adj s t`, also `b t ∈ W` (`hstep`).

Then a `T`-invariant submodule `W` is `⊥` or `⊤`. This packages Problem 4.12.3: the diagonal
element supplies the distinct eigenvalues, and the transvections supply `Adj`. -/
theorem eq_bot_or_eq_top_of_connected
    (hT : ∀ s, T (b s) = w s • b s) (hw : Function.Injective w)
    {W : Submodule k M} (hW : ∀ x ∈ W, T x ∈ W)
    (Adj : B → B → Prop)
    (hconn : ∀ s t, Relation.ReflTransGen Adj s t)
    (hstep : ∀ s t, b s ∈ W → Adj s t → b t ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  rcases eq_or_ne W ⊥ with hbot | hbot
  · exact Or.inl hbot
  -- `W ≠ ⊥`, so some basis vector lies in `W`.
  right
  obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff W).mp hbot
  obtain ⟨s, hs⟩ : ∃ s, b.repr y s ≠ 0 := by
    have hry : b.repr y ≠ 0 := fun h => hy0 (by simpa using congrArg b.repr.symm h)
    simpa using Finsupp.ne_iff.mp hry
  have hsW : b s ∈ W := mem_of_repr_ne_zero b hT hw hW hyW hs
  -- Propagate membership along the connected `Adj`-graph to every basis vector.
  have hall : ∀ t, b t ∈ W := by
    intro t
    have : Relation.ReflTransGen Adj s t := hconn s t
    induction this with
    | refl => exact hsW
    | tail _ hadj ih => exact hstep _ _ ih hadj
  rw [eq_top_iff, ← b.span_eq]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hall)

end Irreducible

end Etingof.DiagonalCoordinate
