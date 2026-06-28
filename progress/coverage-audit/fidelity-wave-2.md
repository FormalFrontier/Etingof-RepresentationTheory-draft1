# Stage 3.7 Fidelity Sweep — Wave 2 adjudication certificate

Wave 2 re-judges the 11 `unsure` verdicts from wave 1 (`fidelity-wave-1.md`) plus the 1 added by the wave-2 pilot (`Chapter5/Definition5.1.4`), per epic #5338 / parent issue #5387. Each item was re-read against its blob with a **different model** (Opus 4.8) than the wave-1 triage, applying the anti-vacuity + conjunct-by-conjunct fidelity test (PLAN.md §3.2 steps 6–7), and resolved to `verified` or `gap`.

## Headline

- Adjudicated this batch: **12/12** (0 `unsure` remain).
- **Verified: 6** — `verified` count 244 → 250.
- **Gap: 6** — `gap` count 1 → 7; six new repair issues opened (#5589–#5594).

## Resolutions

### → `gap`

| Item | Kind | Issue | One-line reason |
|---|---|---|---|
| `Chapter2/Remark2.3.11` | coverage (no decl) | #5589 | Elementary counterexample to Cor 2.3.10 over ℝ (A=ℂ/ℝ, V=A); formalizable, absent |
| `Chapter2/Remark2.3.13` | coverage (no decl) | #5590 | `finrank=1 ⟹ IsSimpleModule`; elementary, formalizable, absent |
| `Chapter2/Remark2.3.2` | coverage (no decl) | #5591 | Left⇄right modules over a commutative ring; formalizable, absent (low value) |
| `Chapter2/Remark2.7.2` | coverage (no decl) | #5592 | Weyl algebra = polynomial differential operators on `k[t]`; formalizable, absent |
| `Chapter3/Definition3.3.2` | statement weaker | #5593 | `Module.Dual k V` omits the `Aᵒᵖ`-action `(f·a)(v)=f(av)`; same pattern as #5355/#5356 |
| `Chapter7/Example7.1.5` | statement weaker | #5594 | Asserts only `Category CommGrpCat`, not "full subcategory of Groups" (fully-faithful forgetful functor) |

### → `verified`

| Item | Reason |
|---|---|
| `Chapter2/Remark2.9.14` | Non-formalizable narrative: Lie groups / manifolds / Lie's correspondence, out of scope; absence is the correct resting state |
| `Chapter2/Remark2.9.4` | Motivational narrative: differentiable families of automorphisms, `e^{tD}`; analytic framing + reader exercises; absence defensible |
| `Chapter3/Remark3.10.3` | Narrative counterexample (Thm 3.10.2 fails infinite-dim; `ℂ(x)⊗ℂ(x)` not a field); hard, low value; absence defensible |
| `Chapter3/Remark3.8.6` | Narrative (Krull-Schmidt fails infinite-dim, holds finite length; positive content is Ch9); absence defensible |
| `Chapter5/Corollary5.19.2` | `Etingof.Corollary5_19_2` statement is faithful and non-vacuous (partition-indexed decomposition + simplicity + distinctness; iso conjunct defeats all-zero witness). Proof's `sorry` is the separate Specht-labelling dependency #5326/#5383 — a sorry-arm matter, not fidelity |
| `Chapter5/Definition5.1.4` | `Etingof.frobeniusSchurIndicator` constructs the genuine FS indicator via the standard equivalent formula `(1/|G|)Σχ(g²)`; type trichotomy tied to it by `Etingof.Theorem5_1_5` and `isRealType_of_frobeniusSchurIndicator_eq_one` |

## Calibration notes

- **Coverage gaps vs. acceptable absence.** A remark with no declaration is a `gap` when its claim is clean, self-contained, and formalizable at this project's level (2.3.11/2.3.13/2.3.2/2.7.2 — matching the wave-1 coverage-gap precedent #5366/#5367/#5372/#5378/#5379). It is `verified` (absence correct) when the content needs out-of-scope machinery (manifolds, differential geometry — 2.9.14/2.9.4) or is a hard, low-value infinite-dimensional narrative counterexample (3.10.3/3.8.6).
- **Definitions construct objects, not propositions.** `frobeniusSchurIndicator` (5.1.4) defines the right object via a provably-equivalent formula and is tied to the book's type trichotomy downstream → faithful. `DualRepresentation` (3.3.2) is a `gap` because the *defining data* (the action) is absent, not because it picks an equivalent encoding.
- **Fidelity ≠ sorry-freeness.** `Corollary5.19.2` has a faithful statement; its proof's `sorry` belongs to the sorry/coverage arm (#5326/#5383), so fidelity is `verified`.

## Status

Wave-2 adjudication batch complete: **0 `unsure` remain**. This is not a dry wave (6 new gaps found), so the epic's "two consecutive dry waves" done-condition is not yet met. The 6 repair issues (#5589–#5594) feed back into the normal worker queue; once they land, a subsequent verification wave can test for a dry result.
