/-!
# Remark 5.2.8: A modification of the vanishing-of-characters argument

> **Remark 5.2.8.** Here is a modification of this argument, which does not use
> (a). Let `N = |G|`. For any `0 < j < N` coprime to `N`, show that the map
> `g ↦ gʲ` is a bijection `G → G`. Deduce that `∏_{g ≠ 1} |χ_V(gʲ)|² = β`. Then
> show that `β ∈ K := ℚ(ζ)`, `ζ = e^{2πi/N}`, and that it does not change under
> the automorphism of `K` given by `ζ ↦ ζʲ`. Deduce that `β` is an integer, and
> derive a contradiction.

This remark is an *alternative proof* of the vanishing statement of
**Problem 5.2.7(b)**: if `V` is an irreducible complex representation of a
finite group `G` with `dim V > 1`, then `χ_V(g) = 0` for some `g ∈ G`. The main
argument of Problem 5.2.7(b) shows `0 < β < 1` for `β := ∏_{g ≠ 1} |χ_V(g)|²`
(assuming the characters never vanish) and rules this out by passing to the
Galois conjugates of the representation `V` supplied by part (a) — the existence
of a number field `K` over which all matrix entries are defined. Remark 5.2.8
replaces that step: instead of conjugating the *representation*, it argues purely
arithmetically. The elementary bijection `g ↦ gʲ` (for `gcd(j, N) = 1`) shows
`β` is fixed by every element `ζ ↦ ζʲ` of `Gal(ℚ(ζ)/ℚ)`, so `β ∈ ℚ`; being a
product of algebraic integers (sums of `|χ_V(·)|²`, i.e. sums of products of
roots of unity), `β` is an algebraic integer, hence `β ∈ ℤ`, contradicting
`0 < β < 1`.

## Coverage status (fidelity audit, epic #5338, issue #5654)

Re-confirming the Wave-2 fidelity finding: **Remark 5.2.8 is not load-bearing for
any formalized content**, and it is recorded here as a covered-inline audit
conclusion rather than separately formalized.

* **No Lean declaration references it.** Neither Remark 5.2.8 nor its parent
  Problem 5.2.7 appears in any Lean file. Problem 5.2.7 itself — the exercise
  whose part (b) this remark re-proves — is not formalized (it carried a stale
  `sorry_free` marker with no accompanying Lean declaration).

* **Nothing formalized consumes the vanishing statement of Problem 5.2.7(b).**
  The internal dependency graph records exactly one dependent of Remark 5.2.8,
  namely `Chapter5/Introduction_5.3` (the "5.3 Frobenius divisibility" section
  header). That edge is the conservative linear-chain default between adjacent
  blobs, not a genuine mathematical dependency: `Introduction_5.3` is a
  one-line section-intro discussion blob with no Lean file. No formalized theorem
  takes "an irreducible representation of dimension `> 1` has a vanishing
  character value" as a hypothesis or lemma.

* **`Theorem 5.4.4` is a different, independent result.** It happens to conclude
  `χ_V(g) = 0 ∨ g acts as a scalar` under the coprimality hypothesis
  `gcd(|C|, dim V) = 1` (Frobenius divisibility), and is formalized directly in
  `Chapter5/Theorem5_4_4.lean` without reference to Problem 5.2.7 or Remark
  5.2.8. It is not a consumer of the Problem 5.2.7(b) vanishing statement.

* **A faithful formalization would be large standalone infrastructure with no
  downstream consumer.** It would require the cyclotomic field `ℚ(ζ_N)`, the
  action of `Gal(ℚ(ζ_N)/ℚ) ≅ (ℤ/Nℤ)ˣ` via `ζ ↦ ζʲ`, the fixed-field
  characterization forcing a Galois-invariant element into `ℚ`, and the
  algebraic-integer argument closing `β ∈ ℚ` to `β ∈ ℤ`, all layered on top of
  the (unformalized) main argument of Problem 5.2.7(b). Building this to serve
  only a remark that no formalized item depends on is disproportionate; per the
  audit task it is tracked here as a conclusion, not formalized.

This mirrors the resolution recorded for `Chapter2/Problem2_11_6.lean`
(completeness audit, same epic): a self-contained exercise/remark with no
formalized consumer, documented rather than formalized.

This file records the audit conclusion and carries no proof.
-/
