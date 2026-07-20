# Ch8 review: Horseshoe + Problem 8.2.6 (Tor/bar-resolution) — axiom cleanliness + statement fidelity

**Issue:** #7020 (review) · **Date:** 2026-07-20 (UTC) · **Verdict: SOUND**

Report-only fidelity + axiom-cleanliness audit of the Chapter 8 homological-algebra
cluster: `EtingofRepresentationTheory/Chapter8/Horseshoe.lean` (horseshoe lemma /
projective-resolution-of-`X₂` construction) and
`EtingofRepresentationTheory/Chapter8/Problem8_2_6.lean` (Tor/Ext basic properties,
second-argument functoriality, balancing theorem). Both modules build clean
(`lake build`, only unrelated lint warnings in a `Problem8_2_6_ii_Crux` dependency).

## 1. Axiom cleanliness

`#print axioms` on every headline declaration of both files (and the second-argument
infrastructure the issue names). **All report exactly `[propext, Classical.choice,
Quot.sound]`** — no `sorryAx`, no custom `axiom`. Because a sorried `def`/`instance`
body injects `sorryAx`, the clean result on the data constructions
(`horseshoeComplex`, `horseshoeResolution`, `barResolution`, `torSndMap`,
`tensorLeftFunctor`, `tensorSndMap`, `balancingIsoZero`, …) directly certifies their
bodies are genuinely built, not stubbed.

| Declaration | File | Axioms |
|---|---|---|
| `horseshoe` | Horseshoe | propext, Classical.choice, Quot.sound |
| `horseshoeResolution` | Horseshoe | propext, Classical.choice, Quot.sound |
| `horseshoeShortComplex_shortExact` | Horseshoe | propext, Classical.choice, Quot.sound |
| `horseshoeπ_quasiIso` | Horseshoe | propext, Classical.choice, Quot.sound |
| `horseshoeComplex` (def) | Horseshoe | propext, Classical.choice, Quot.sound |
| `horseshoeD` (def) | Horseshoe | propext, Classical.choice, Quot.sound |
| `horseshoeTwist` (def) | Horseshoe | propext, Classical.choice, Quot.sound |
| `horseshoeπZero` (def) | Horseshoe | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_i_tor` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_i_ext` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_ii` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_iii_ext` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_iii_tor` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_iv` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_v_ext` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `Problem_8_2_6_v_tor` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `tensorRightNatTrans` (def) | Problem8_2_6_Core | propext, Classical.choice, Quot.sound |
| `tensorSndMap` (def) | Problem8_2_6_Core | propext, Classical.choice, Quot.sound |
| `torSndMap` (def) | Problem8_2_6_Core | propext, Classical.choice, Quot.sound |
| `tensorLeftFunctor` (def) | Problem8_2_6_Core | propext, Classical.choice, Quot.sound |
| `balancingIsoZero` (def) | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `torBalancing_sixTerm` | Problem8_2_6 | propext, Classical.choice, Quot.sound |
| `barResolution` (def) | BarResolution | propext, Classical.choice, Quot.sound |

## 2. Statement fidelity + non-vacuity

Checked against `blobs/Chapter8/Problem8.2.6.md` and the horseshoe exposition it supports.

- **`horseshoe`** — produces a genuine `ProjectiveResolution S.X₂`, chain maps `α`, `β`,
  a proof the resulting `ShortComplex.mk α β w` is `ShortExact`, and both augmentation
  compatibility squares. The terms are exactly the biproduct `P₁.X n ⊞ P₃.X n`
  (`horseshoeComplex`), matching Problem 8.2.6(v)'s "construct a resolution of `M₂` with
  terms `P²ᵢ := P¹ᵢ ⊕ P³ᵢ`". The construction is fully explicit: `horseshoeD` (upper-
  triangular twisted differential), `horseshoeTwist`/`horseshoeTwistAux` (the inductive
  off-diagonal lift built against the exactness of the *given* resolutions), `horseshoeπ`,
  and `horseshoeπ_quasiIso` (via the middle three-lemma on homology). Faithful,
  non-vacuous.
- **(i) `Problem_8_2_6_i_tor` / `_i_ext`** — `Tor₀(M,N) ≅ M ⊗_A N` and `Ext⁰ ≃+ Hom_A`.
  Matches the blob. Real isos (`leftDerivedZeroIsoSelf`, `Abelian.Ext.addEquiv₀`).
- **(ii) `Problem_8_2_6_ii`** — `Ext¹` (Def 8.2.4) `≃+ Problem3_9_1.Ext1`, routed through
  the relative bar resolution and the crux `cohomologyClassEquivExt1`. Matches the blob.
- **(iii) `_iii_ext`** — covariant `Abelian.Ext.covariantSequence` exact (objects are the
  `Etingof.Ext` groups). **`_iii_tor`** — six-term homology window in the **second**
  argument with an existentially-quantified connecting map `δ`; exactness is asserted at
  the `δ` nodes (positions 2–3–4), so the existential is not vacuous. Horizontal maps are
  the genuine second-argument functoriality `torSndMap`.
- **(iv) `Problem_8_2_6_iv`** — balancing: `Tor A N M n ≅ (leftDerived (tensorLeftFunctor
  A M) n).obj (of A N)`, proved by an honest dimension shift (strong induction, `n=1`
  kernel comparison via `balancing_zero_naturality`, `n≥2` via `iso_of_sixTerm_exact`
  collapsing both windows on projectives). Matches the blob's hint (resolve either
  argument). Non-vacuous.
- **(v) `_v_ext`** — contravariant `Abelian.Ext.contravariantSequence` exact.
  **`_v_tor`** — six-term window in the **first** argument (`Etingof.TorFunctor`
  functoriality), same faithful encoding. Matches the blob.
- **Infrastructure non-vacuity** — `tensorSndMap` (quotient of `TensorProduct.map`),
  `tensorRightNatTrans` (real `NatTrans` with `naturality` proved), `torSndMap`
  (`NatTrans.leftDerived`), `tensorLeftFunctor` (real functor, `map_id`/`map_comp`
  proved), and `barResolution` (real `ProjectiveResolution`: complex + π + `projective`
  instances + `quasiIso`) are all genuine objects, no `True`/`trivial` placeholders.

### Note on the Tor long-exact-sequence encoding (not a defect)

The book states the Tor sequences of (iii)/(v) as full (infinite) long exact sequences.
The formalization encodes them as **six-term windows** (`ComposableArrows _ 5`) with a
per-`(n₀,n₁)` existentially-quantified `δ`; the module docstrings state explicitly that
splicing the windows over all `n` recovers the book's long exact sequence. This is the
standard, faithful way to certify a homological LES (the `Ext` side likewise uses
Mathlib's genuine `covariantSequence`/`contravariantSequence`). Recorded for the reader,
not a weakening — exactness including the connecting-map nodes is asserted.

## 3. In-PR docstring fix

`Horseshoe.lean` carried a stale `## Status` block (lines 61,65) reading "Spec-first: …
the construction/proof is deferred (`sorry`) … the theorem should become sorry-free",
contradicting the finished, `sorry`-free construction. Rewritten in this PR to describe
the completed construction and its discharged obligations (docstring-only; module
rebuilds clean). No other source changes.

## Verdict

**SOUND.** 23/23 audited declarations axiom-clean; all headline statements faithful to
`blobs/Chapter8/Problem8.2.6.md` and non-vacuous; all data constructions (horseshoe
resolution, bar resolution, second-argument Tor infrastructure) are real objects. No
follow-up issue warranted.
