import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_2_5

/-!
# Remark 5.2.8: A modification of the vanishing-of-characters argument

> **Remark 5.2.8.** Here is a modification of this argument, which does not use
> (a). Let `N = |G|`. For any `0 < j < N` coprime to `N`, show that the map
> `g ↦ gʲ` is a bijection `G → G`. Deduce that `∏_{g ≠ 1} |χ_V(gʲ)|² = β`. Then
> show that `β ∈ K := ℚ(ζ)`, `ζ = e^{2πi/N}`, and that it does not change under
> the automorphism of `K` given by `ζ ↦ ζʲ`. Deduce that `β` is an integer, and
> derive a contradiction.

This remark is an *alternative proof* of the vanishing statement of
**Problem 5.2.7(b)**: if `V` is an irreducible complex representation of a finite
group `G` with `dim V > 1`, then `χ_V(g) = 0` for some `g ∈ G`. The main argument
of Problem 5.2.7(b) shows `0 < β < 1` for `β := ∏_{g ≠ 1} |χ_V(g)|²` (assuming
the characters never vanish) and rules this out by passing to the Galois
conjugates of the representation supplied by part (a). Remark 5.2.8 replaces that
step by a purely arithmetic argument.

## What is formalized here

The remark decomposes into five steps. Three of them are elementary and
self-contained; they are formalized in this file as real, `sorry`-free theorems:

* **Step 1** (`pow_coprime_bijective`): for `gcd(|G|, j) = 1` the map `g ↦ gʲ` is a
  bijection `G → G`. This is `Nat.Coprime.pow_left_bijective` / `powCoprime` from
  Mathlib, restated in the form the remark uses.

* **Step 2** (`prod_ne_one_pow`): the bijection of Step 1 fixes `1`, hence
  restricts to a bijection of `G ∖ {1}`; reindexing the product along it gives
  `∏_{g ≠ 1} f(gʲ) = ∏_{g ≠ 1} f(g)` for any `f` into a commutative monoid. Taking
  `f g = |χ_V(g)|²` this is exactly "`∏_{g ≠ 1} |χ_V(gʲ)|² = β`".

* **Step 5 + contradiction** (`not_isIntegral_rat_mem_Ioo`): an algebraic integer
  that is rational and lies strictly between `0` and `1` does not exist. Combined
  with Step 2's identity (which forces `β` to be Galois-invariant, hence rational)
  and the fact that `β` is a product of algebraic integers, this "deduce that `β`
  is an integer, and derive a contradiction" step closes the argument. The
  algebraic-integer-∩-ℚ-is-ℤ input is `Etingof.Proposition5_2_5`.

## What remains (foundation sub-issue)

Steps 3 and 4 — that `β ∈ K = ℚ(ζ_N)` (character values are sums of `N`-th roots
of unity) and that `β` is fixed by the automorphism `ζ ↦ ζʲ` of `K` (via the
identity `σ_j(χ_V(g)) = χ_V(gʲ)`, so `σ_j(β) = ∏_{g≠1} |χ_V(gʲ)|² = β` by Step 2),
forcing `β ∈ ℚ` — require the cyclotomic field `ℚ(ζ_N)`, the Galois action of
`Gal(ℚ(ζ_N)/ℚ) ≅ (ℤ/Nℤ)ˣ`, and the representation-theoretic fact that character
values are sums of roots of unity with `σ_j(χ_V(g)) = χ_V(gʲ)`. That is a large,
standalone foundation and is tracked as a separate sub-issue; this file lands the
elementary and closing steps incrementally.
-/

namespace Etingof.Remark5_2_8

open Finset

variable {G : Type*} [Group G]

/-- **Step 1 of Remark 5.2.8.** For `j` coprime to `|G|`, the `j`-th power map
`g ↦ gʲ` is a bijection `G → G`. -/
theorem pow_coprime_bijective {j : ℕ} (h : (Nat.card G).Coprime j) :
    Function.Bijective (fun g : G => g ^ j) :=
  Nat.Coprime.pow_left_bijective h

/-- The `j`-th power map fixes the identity and is injective, so `gʲ = 1 ↔ g = 1`
when `j` is coprime to `|G|`. -/
theorem pow_eq_one_iff {j : ℕ} (h : (Nat.card G).Coprime j) {g : G} :
    g ^ j = 1 ↔ g = 1 := by
  refine ⟨fun hg => (pow_coprime_bijective h).injective ?_, fun hg => by rw [hg, one_pow]⟩
  simpa using hg

/-- **Step 2 of Remark 5.2.8.** Since `g ↦ gʲ` (for `gcd(|G|, j) = 1`) is a
bijection of `G` fixing `1`, reindexing the product over `G ∖ {1}` along it leaves
the product unchanged:
`∏_{g ≠ 1} f(gʲ) = ∏_{g ≠ 1} f(g)`.
Taking `f g = |χ_V(g)|²` this is the identity `∏_{g ≠ 1} |χ_V(gʲ)|² = β`. -/
theorem prod_ne_one_pow {M : Type*} [CommMonoid M] [Fintype G] [DecidableEq G] {j : ℕ}
    (h : (Nat.card G).Coprime j) (f : G → M) :
    ∏ g ∈ univ.filter (· ≠ 1), f (g ^ j) = ∏ g ∈ univ.filter (· ≠ 1), f g := by
  refine Finset.prod_bij (fun g _ => g ^ j) ?_ ?_ ?_ ?_
  · -- the map sends `G ∖ {1}` into `G ∖ {1}`
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rwa [Ne, pow_eq_one_iff h]
  · -- injective on `G ∖ {1}`
    intro a₁ _ a₂ _ hab
    exact (pow_coprime_bijective h).injective hab
  · -- surjective onto `G ∖ {1}`
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    obtain ⟨a, ha⟩ := (pow_coprime_bijective h).surjective b
    refine ⟨a, ?_, ha⟩
    simp only [mem_filter, mem_univ, true_and]
    rintro rfl
    exact hb (by simpa using ha.symm)
  · intro a _; rfl

/-- **Step 5 of Remark 5.2.8, with the contradiction.** There is no rational
algebraic integer strictly between `0` and `1`. Concretely, if `q : ℚ` maps to an
algebraic integer in `ℂ` and `0 < q < 1`, we reach a contradiction: by
`Etingof.Proposition5_2_5` such a `q` is an integer, and there is no integer in
`(0, 1)`.

In the remark, `β` is Galois-invariant (Step 4, using Step 2's identity), hence
rational, and it is a product of algebraic integers, hence an algebraic integer;
the main argument of Problem 5.2.7(b) gives `0 < β < 1`. This lemma is exactly the
final "deduce that `β` is an integer, and derive a contradiction". -/
theorem not_isIntegral_rat_mem_Ioo {q : ℚ}
    (hint : IsIntegral ℤ (algebraMap ℚ ℂ q)) (h0 : 0 < q) (h1 : q < 1) : False := by
  obtain ⟨n, rfl⟩ := (Etingof.Proposition5_2_5 q).mp hint
  have hn0 : (0 : ℤ) < n := by exact_mod_cast h0
  have hn1 : n < 1 := by exact_mod_cast h1
  omega

end Etingof.Remark5_2_8
