# Stage 3.7 audit — Problem 4.1.4 (irreducible reps of a `p`-group in char `p` are trivial)

**Issue:** #7270 (statement-fidelity & non-vacuity audit; report-only).
**File:** `EtingofRepresentationTheory/Chapter4/Problem4_1_4.lean` (199 lines).
**Blob:** `blobs/Chapter4/Problem4.1.4.md`.
**HEAD:** `7c6b932d` (`origin/main`).
**Verdict:** **VERIFIED** — statement-faithful, non-vacuous, `covered_full`.

## Build / axiom check

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_1_4` exits 0
  (`✔ [8580/8580] Built ... (3.4s)`), no warnings.
- `#print axioms Etingof.Problem4_1_4` returns exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, axiom-clean.

## Book text

> **Problem 4.1.4.** Let `G` be a group of order `pⁿ`. Show that every irreducible
> representation of `G` over a field `k` of characteristic `p` is trivial.

## Headline declaration

```lean
theorem Etingof.Problem4_1_4 {p n : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = p ^ n)
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρ.asModule) :
    ∀ g : G, ρ g = LinearMap.id
```

## Hypothesis faithfulness

- **`[Fact p.Prime]`** — `p` is prime. Genuine and required: without primality
  "order `pⁿ`" is not a `p`-group and the center-nontriviality argument driving
  `exists_fixed_vector` fails. Not vacuous. ✓
- **`[Field k] [CharP k p]`** — `k` is a field of characteristic exactly `p`. With
  `p` prime this is a genuine positive-characteristic field (e.g. `𝔽_p`), not
  characteristic `0` in disguise; `CharP k p` pins the characteristic exactly. Both
  are used (the char-`p` nilpotency `(ρz − 1)^{p^j} = (ρz)^{p^j} − 1` in
  `exists_fixed_vector`). Not vacuous, not over-strong. ✓
- **`hG : Fintype.card G = p ^ n`** — `|G| = pⁿ`, exactly "order `pⁿ`". The exponent
  `n : ℕ` is implicit and **universally quantified**, so the theorem covers every
  power, including the boundary. Faithful, not over-strong. ✓
  - **`n = 0` boundary:** admitted and harmless. `|G| = p⁰ = 1` forces `G` trivial;
    the supporting `exists_fixed_vector` has an explicit `Nat.card G = 1` base case
    (lines 45–51), and the conclusion `∀ g, ρ g = id` holds because the only element
    is `1` (`ρ 1 = id`). No vacuity is introduced — a trivial group does have a
    (unique, trivial) irreducible representation.
- **`hV : IsSimpleModule (MonoidAlgebra k G) ρ.asModule`** — the genuine
  irreducibility hypothesis. `ρ.asModule` is Mathlib's standard
  `Representation → MonoidAlgebra k G`-module reconstruction (scalar action given by
  `ρ.asAlgebraHom`), so its `MonoidAlgebra k G`-submodules are exactly the
  `G`-subrepresentations of `ρ`. `IsSimpleModule R M` = `M` nontrivial with no proper
  nonzero submodule = the representation is irreducible. This is the correct, on-target
  object, not a weaker one (e.g. not "indecomposable", not simplicity over `k` alone).
  It is genuinely used: line 164 extracts `Nontrivial V`, and lines 182–183 use
  `IsSimpleModule.span_singleton_eq_top` to show the fixed vector generates all of `V`. ✓

## Conclusion faithfulness — the key check

Book claim: an irreducible representation "is trivial." Lean conclusion:
`∀ g : G, ρ g = LinearMap.id`, i.e. **every group element acts as the identity
endomorphism** of `V` (`ρ g : Module.End k V`, `LinearMap.id` the identity `k`-linear
map — equality of endomorphisms, the right object).

"Trivial representation" means precisely "`G` acts trivially", i.e. every `g` acts as
the identity operator — exactly the Lean conclusion. This is the **strongest faithful
reading**, and in particular is *not* one of the weaker statements it could have been
mistaken for:

- it is **not** merely "there exists a nonzero fixed vector" (that only exhibits a
  trivial *sub*representation — the content of the auxiliary `exists_fixed_vector`, not
  the headline);
- it is **not** merely "each `g` acts as some scalar" (that would also admit a
  *nontrivial* one-dimensional character).

Together with the standing irreducibility hypothesis `hV`, "every `g` acts as the
identity" is logically equivalent to "`V` is the trivial one-dimensional irreducible
representation": once the action is trivial, every `k`-subspace is `G`-invariant, so
simplicity forces `dim_k V = 1`. Hence the theorem delivers exactly "irreducible ⟹
trivial (one-dimensional trivial rep)" with no gap; the one-dimensionality is a logical
consequence of the conclusion plus `hV` (noted in the file docstring, lines 9–12) and
need not be asserted separately. `covered_full`. ✓

## Non-vacuity

- **Hypotheses jointly satisfiable.** Take `p = 2`, `n = 1`, `k = 𝔽₂`, `G = C₂`,
  `V = 𝔽₂` the trivial one-dimensional representation: `Fact (2).Prime` ✓,
  `CharP 𝔽₂ 2` ✓, `card G = 2 = 2¹` ✓, `ρ.asModule` is one-dimensional hence
  `IsSimpleModule` ✓. So the theorem is not vacuously true. ✓
- **`V` forced nonempty/nontrivial.** `IsSimpleModule` carries a `Nontrivial`
  requirement; the proof extracts `Nontrivial V := IsSimpleModule.nontrivial` at
  line 164, so `V ≠ 0`. No degenerate `V = 0` reading. ✓
- **No `True`-typed or trivially-dischargeable hypothesis.** Every hypothesis is a
  genuine mathematical constraint and each is used in the proof. ✓

## Supporting lemma (soundness note, not headline)

`exists_fixed_vector` (line 37) is the char-`p` fixed-vector theorem for `p`-groups,
proved by strong induction on `Nat.card G` via the nontrivial center of a `p`-group
(`IsPGroup.center_nontrivial`), the nilpotency of `ρz − 1`, and descent to
`G ⧸ ⟨z⟩`. It is an internal ingredient, not the audited statement; the axiom check on
the headline already certifies it is `sorry`-free.

## Verdict

**VERIFIED.** `Etingof.Problem4_1_4` is a faithful, non-vacuous, `covered_full`
formalization of Problem 4.1.4: hypotheses encode "`G` of order `pⁿ` over a field of
characteristic `p`" with a genuine irreducibility hypothesis, and the conclusion
`∀ g, ρ g = id` is exactly "the representation is trivial." No gap; no repair issue
filed; no `.lean` edits.
