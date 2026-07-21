# Fidelity audit: Chapter 8, Theorem 8.1.1 — equivalent characterisations of projective modules (#7137)

**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session a7d96fe5)
**Scope:** `EtingofRepresentationTheory/Chapter8/Theorem8_1_1.lean`
(`Etingof.Theorem_8_1_1_i_iff_ii`, `Etingof.Theorem_8_1_1_i_iff_iii`,
`Etingof.Theorem_8_1_1_i_iff_iv`)
**Method:** book statement/proof + cited dependencies
(`blobs/Chapter8/Theorem8.1.1.md`, `.refs.md`) first, then statement-vs-blob
fidelity of each declaration, then non-vacuity, then axiom-cleanliness.
Mirrors the established confidence-phase pattern
(`2026-07-20-ch8-horseshoe-tor-fidelity.md`,
`2026-07-21-ch3-theorem3_2_2-density-fidelity.md`).

## Overall verdict: **FAITHFUL**

All three declarations are genuine, axiom-clean formalisations of the pairwise
equivalences that make up Etingof Theorem 8.1.1. The book states four properties
(i)–(iv) as mutually equivalent; the Lean file anchors on `Module.Projective R P`
(which **is** the book's condition (i), the lifting property) and proves the three
biconditionals (i)↔(ii), (i)↔(iii), (i)↔(iv). A star of three equivalences through
(i) is logically equivalent to the full mutual equivalence of the four, so the
split is a faithful — and cleaner — rendering of the theorem, not a partial one.

The only non-book hypotheses are universe-technical: `[Small.{v} R]` on i↔ii and
i↔iv, and the `Q : Type (max u v)` universe of the free module in i↔iii. Section
below assesses these in detail — the single most important fidelity question for
this theorem. Conclusion: they are harmless universe bookkeeping, **not** a
restriction of the book's mathematical scope. No defect filed; no follow-up issue
filed for `[Small.{v} R]`.

## Build and axioms

- `lake exe cache get` then
  `lake build EtingofRepresentationTheory.Chapter8.Theorem8_1_1` exits **0**
  (1592 jobs, `Built EtingofRepresentationTheory.Chapter8.Theorem8_1_1`). No
  warnings.

`#print axioms`:

| Declaration | Axioms |
|---|---|
| `Etingof.Theorem_8_1_1_i_iff_ii`  | `propext, Classical.choice, Quot.sound` |
| `Etingof.Theorem_8_1_1_i_iff_iii` | `propext, Classical.choice, Quot.sound` |
| `Etingof.Theorem_8_1_1_i_iff_iv`  | `propext, Classical.choice, Quot.sound` |

No `sorryAx`, no custom axioms. **Axiom-clean** (exactly the standard set).

## The anchor: `Module.Projective R P` is condition (i)

Book (i) is the lifting property: for a surjection `α : M → N` and any `ν : P → N`
there is `μ : P → M` with `α ∘ μ = ν`. Mathlib's `Module.Projective R P` is defined
via a splitting of the canonical surjection `(P →₀ R) → P`, and is *provably*
interchangeable with the lifting property through the Mathlib API the proofs use:
`Module.projective_lifting_property` (Projective ⇒ lifting, used in the i↔iv
forward step) and `Module.Projective.of_lifting_property''` (lifting ⇒ Projective,
used in the i↔ii and i↔iv backward steps). So anchoring the three biconditionals on
`Module.Projective R P` genuinely anchors them on book condition (i). **Faithful.**

## Per-declaration audit

### `Etingof.Theorem_8_1_1_i_iff_ii` — (i) ↔ (ii): every surjection onto P splits — FAITHFUL

- **RHS** = `∀ {M} (f : M →ₗ[R] P), Surjective f → ∃ g : P →ₗ[R] M, f.comp g = id`.
  This is verbatim book (ii): "any surjective morphism `α : M → P` splits; i.e.
  there exists `μ : P → M` such that `α ∘ μ = id`".
- **Genuine biconditional.** Forward (Projective → splitting) is
  `LinearMap.exists_rightInverse_of_surjective` applied to `f`. Backward
  (splitting → Projective) instantiates the hypothesis at the free cover
  `p ∘ₗ e` (with `e` transporting `P →₀ Shrink R` to `P →₀ R`) and feeds the
  resulting section to `Module.Projective.of_lifting_property''`. Both directions
  carry real content; neither side is trivialised.
- **Book (i)⇒(ii) "take N = P".** The book proves (i)⇒(ii) by specialising the
  lifting property to `N = P`, `ν = id`. The Lean forward direction reaches the
  same conclusion through the equivalent `exists_rightInverse_of_surjective`; the
  content ("a surjection onto P has a section") is exactly the `N = P`
  specialisation. Faithful, not a weaker claim.
- **Universe quantifier** discussed in the dedicated section below.

### `Etingof.Theorem_8_1_1_i_iff_iii` — (i) ↔ (iii): direct summand of a free module — FAITHFUL

- **RHS** = `∃ (Q) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.Free R Q)
  (i : P →ₗ[R] Q) (s : Q →ₗ[R] P), s.comp i = id`, i.e. P is a **retract** (split
  submodule) of a free module Q.
- **Faithful to book (iii).** The book writes (iii) as "there exists `Q` such that
  `P ⊕ Q` is free". "P is a split submodule of a free module" and "`P ⊕ (complement)`
  is free" are the two standard equivalent phrasings of "direct summand of a free
  module": a retraction `s ∘ i = id` makes `Q ≅ P ⊕ ker s`, so P is a summand of a
  free module; conversely if `P ⊕ Q'` is free then P retracts off it. Same notion.
- **`Module.Free` vs "a direct sum of copies of A".** The book gloss on (iii) is
  "i.e., a direct sum of copies of A". `Module.Free R Q` means Q admits an R-basis,
  equivalently `Q ≅ ⊕_{b∈basis} R`, i.e. a direct sum of copies of `A = R`. This is
  **exactly** the book's gloss, not a generalisation — an arbitrary basis is
  precisely "copies of A" indexed by that basis. Faithful.
- **Genuine biconditional.** Forward takes `Q = P →₀ R` (free) with `s` the given
  splitting of `Module.Projective.out` and `i = Finsupp.linearCombination R id`;
  backward is `Module.Projective.of_split`. Both directions real.

### `Etingof.Theorem_8_1_1_i_iff_iv` — (i) ↔ (iv): Hom_A(P, ?) is exact — FAITHFUL

- **RHS** formalises "the functor `Hom_A(P, ?)` is exact" as **preservation of
  short exact sequences**: for every SES `0 → K →[ι] M →[π] N → 0` (`ι` injective,
  `π` surjective, `range ι = ker π`), the image
  `0 → Hom(P,K) →[ι∘·] Hom(P,M) →[π∘·] Hom(P,N) → 0` is again short exact —
  encoded as the three conjuncts (a) `ι∘·` injective, (b) exactness at `Hom(P,M)`
  (`π∘h = 0 ↔ ∃ g, ι∘g = h`), (c) `π∘·` surjective.
- **Faithful rendering of "exact functor".** An additive functor is exact iff it
  preserves short exact sequences; the SES-preservation predicate here is the
  standard unfolding of that. Conjuncts (a),(b) are left-exactness (automatic for
  `Hom(P,-)` for every P — the proof establishes them unconditionally from the
  SES data); conjunct (c), surjectivity of post-composition with `π`, is exactly
  the lifting property, hence projectivity. The docstring states this split
  correctly.
- **Genuine biconditional and faithful to the book proof.** Forward
  (Projective → SES-preservation): (a),(b) proved directly from
  `range ι = ker π`; (c) is `Module.projective_lifting_property`. Backward
  (SES-preservation → Projective): instantiates the hypothesis at the specific SES
  `0 → ker(p∘e) → (P →₀ R) → P → 0` (the free cover of P), extracts surjectivity
  conjunct (c), lifts `id` to a section, and concludes via
  `of_lifting_property''`. This mirrors the book's (iv)⇒(i) argument to the letter:
  "let K be the kernel of α and apply the exact functor Hom(P,?) to
  `0 → K → M → N → 0`". Both directions real.

## Universe hypotheses — the central fidelity question

The book quantifies over "the category of A-modules" with no smallness caveat. The
Lean statements carry universe conditions the book does not mention. Assessment:

**`[Small.{v} R]` on i↔ii and i↔iv (with `M`, and `K M N`, in `Type v`).**
- What it does: `Small.{v} R` asserts R (in `Type u`) has an equiv copy in
  `Type v`. It is used **only** in the backward directions, to build the free
  cover of P — which must live in the same universe `v` as P — via
  `Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)`, transporting
  `P →₀ Shrink.{v} R` (in `Type v`) to `P →₀ R`.
- Why it is not a scope restriction:
  1. In the ordinary situation where R and P share a universe (`u = v`),
     `Small.{v} R` holds automatically (`small_self`), so the hypothesis is
     vacuous in every case the book actually contemplates. It only becomes a real
     assumption when P is placed in a *strictly smaller* universe than R — a
     configuration the book never considers and which has no mathematical content
     for the theorem.
  2. The RHS quantifiers restrict the auxiliary modules `M` (resp. `K,M,N`) to
     `Type v`. Because each biconditional is proved **equivalent to
     `Module.Projective R P`** — the genuine, universe-polymorphic notion, which
     implies splitting/exactness for auxiliary modules in *every* universe — the
     `Type v` restriction on the quantifier loses no content: the LHS already
     carries the full-strength statement, and the RHS need only reach the single
     free-cover witness (which lives in `Type v`) to recover it. The nominal
     universe restriction on the quantifier and the `Small.{v} R` side-condition
     are exactly the bookkeeping that lets that witness be constructed in `Type v`.
- Verdict: **harmless universe-technical hypothesis, faithful.** Not a restriction
  of the book's scope. No follow-up issue filed.

**`Q : Type (max u v)` on i↔iii.**
- The existential over Q ranges over the *larger* universe `max u v`, the natural
  home of the free cover `P →₀ R` (`P : Type v`, `R : Type u`). Enlarging the
  universe of an **existential witness** makes the statement *easier* to satisfy,
  never harder — it is strictly more permissive than restricting Q to `Type v`, and
  the backward direction accepts a Q in that universe with no extra hypothesis.
- Verdict: **harmless universe bump, faithful.** No smallness side-condition is even
  needed here.

## Non-vacuity summary

- Each of the three theorems is a real biconditional with both directions proved on
  genuine content (tabulated per-declaration above); no direction is discharged by
  `True`/`trivial` or by collapsing one side.
- `Module.Projective R P` is a non-trivial predicate (free modules satisfy it,
  e.g. `ℤ/2` over `ℤ` does not), so the equivalences are not vacuously true.
- Axiom-clean, no `sorryAx` (table above).

## Conclusion

Verdict **FAITHFUL** for all three declarations. The three-biconditional split
faithfully renders the book's four-way equivalence; the anchor `Module.Projective`
is book condition (i); (ii), (iii), (iv) are each rendered without weakening
(including `Module.Free` = "copies of A" in (iii) and SES-preservation = "exact
functor" in (iv)); and the universe hypotheses `[Small.{v} R]` / `Q : Type (max u v)`
are harmless universe bookkeeping, not a scope restriction. No defect issue and no
`[Small.{v} R]` follow-up issue filed. Report-only: no `.lean` file modified.
