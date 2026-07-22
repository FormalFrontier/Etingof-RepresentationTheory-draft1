# Sorry Landscape Analysis — general-`k` Schur-Weyl push

Generated 2026-06-22 02:40 UTC by summarize session (issue #5018, branch
`agent/a81ac7dd`) at HEAD `2a990bc4`. Supersedes the wave-63 (2026-05-20)
snapshot, which was stale by ~200 merged PRs and still pointed at Chapter 6
infinite-type (D̃₇ / non-adjacent-branches) work that is no longer the frontier.

## Headline: 4 real sorries, all in Chapter 5

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
**entire** `EtingofRepresentationTheory/` tree contains exactly **4 genuine
proof-gap `sorry` tactics**, all in Chapter 5. There are **no `axiom`
declarations and no `admit`s** anywhere in the source.

> **Read the counts correctly.** A bare `grep -rc sorry` is wildly misleading
> here: it reports e.g. `SchurWeylSimplesClassificationComplex.lean:13`,
> `SchurWeylSimplesClassification.lean:9`, `SchurWeylFormalCharacterIso.lean:7`,
> `KernelLemmaKPrime.lean:4`, `CauchyCharacterRight.lean:4`, `Chapter9/…`,
> `Chapter6/…` — but **almost all of those are docstring/comment prose**
> ("sorry-free", "isolated `sorry`", "currently a sorry'd dependency (#4832)",
> "(sorry'd)"). The project's culture of documenting *where the sorries are and
> are not* inflates the raw grep by ~18×. The table below gives both numbers so
> the discrepancy is auditable.

### The 4 genuine sorries

| # | File:line | Declaration | Tracking issue(s) | Crux |
|---|-----------|-------------|-------------------|------|
| 1 | `Chapter5/CauchyDetQuotient.lean:124` | `quotDetRep_irreducible_constituent_lastWeight_zero` | **#4905** (#4896 assembly) ← #4961 ← #5003 ← PR #4997 | A/det Cauchy-decomposition + det-shift character identity |
| 2 | `Chapter5/SchurWeylFormalCharacterIso.lean:200` | `schurModule_isSimple_general` | **#4946** → #4973–#4976; #4976 ← #4992/#5005 | general-`k` Schur-module simplicity |
| 3 | `Chapter5/SchurWeylSimplesClassification.lean:132` | `schurWeyl_simples_formalCharacter_classification_core` | **#4721** (historical); active relocation/retire in **#5023/#5024** (#4994), review **#5017** | "simple polynomial `GL_N`-rep is character-determined ⇒ char = `schurPoly`" (Tier-4 highest weight) |
| 4 | `Chapter5/SpechtModuleBasis.lean:2345` | `twistedPolytabloid_residual_invariant` | **#5010** (#4998 residual) | James/Fulton column-straightening invariant |

### Raw `grep -rc sorry` per file (for audit; mostly prose)

Chapter 5 (frontier): `SchurWeylSimplesClassificationComplex 13`,
`SchurWeylSimplesClassification 9`, `SchurWeylFormalCharacterIso 7`,
`SpechtModuleBasis 4`, `KernelLemmaKPrime 4`, `CauchyDetQuotient 4`,
`CauchyCharacterRight 4`, `PolytabloidBasis 2`, `KernelLemmaK 2`,
`TabloidModule 1`, `PolyRightGrading 1`, `DetIrreducible 1`, `DetInvElim 1`,
`CharacterOrthogonality 1`, `CharValueHookFormula 1`.

Other chapters (all prose — **0 real sorries**):
`Chapter9/Theorem9_2_1 4`, `Chapter6/Corollary6_8_4 4`,
`Infrastructure/BasicAlgebraExistence 2`, `Chapter6/Problem6_1_5_theorem 2`,
`Chapter6/Corollary6_8_3 2`, plus eight files at 1 each across Chapters 6/9 and
Infrastructure. Every one of these is a docstring reference (e.g.
`KernelLemmaK` cites "(K′) is a sorry'd dependency (#4832)" but the
comment-stripped count is 0). `grep -rc` grand total: **76**. Real total: **4**.

Verification method: an awk pass with a `/- … -/` depth counter that also
truncates at `--`, then matches whole-word `sorry` in the surviving code only.
Spot-checked against `SpechtModuleBasis` (issue #5010 asserts "exactly one
sorry" → matches line 2345) and `SchurWeylSimplesClassification` (grep -rc 9 →
1 real, line 132).

## Chapter 5 dependency picture (the critical path)

The frontier is a **general-`k` Schur-Weyl / Specht push**. There are three
mostly-independent threads, plus an active infrastructure emergency.

### ⚠ Active: main is broken

`main` does not build at HEAD `2a990bc4`. Repair issue **#5021** / PR **#5022**
(`agent/c4445299-fixmain`, "rename stale seam reference in leaf") is the fix —
a stale seam name in `SchurWeylSimplesClassificationComplex.lean`. As of this
snapshot its CI is QUEUED/IN_PROGRESS. **Until #5022 merges, every feature PR
based on `main` will fail CI**; this is the single highest-priority unblock.

### Thread A — A/det grading & character (the #4896/#4905 chain)

Targets sorry #1 (`quotDetRep_irreducible_constituent_lastWeight_zero`).

```
PR #4997 (OPEN, CI FAILED — quotDetDegreeFDRep + formal-character SES infra)
  └─ #5003  quotDetDegreeFDRep_formalCharacter        [blocked: infra only in #4997, not on main]
       └─ #4961  GL-grading of A/det + single-degree reduction   [blocked]
            └─ #4905  discharge quotDetRep_…_lastWeight_zero  →  removes sorry #1   [blocked]
```

The entire chain is gated on **PR #4997** (MERGEABLE but CI FAILED — `ring`
errors + a ~55-min build timeout). `quotDetDegreeFDRep`,
`formalCharacter_add_of_shortExact`, `polyRight_iSup_glWeightSpace_eq_top`,
`twistFDRep` exist **only** on `agent/8063b0cd` (#4997), not on `main`. Repairing
#4997's CI unblocks #5003 → #4961 → #4905 in one stroke. This is `repair`-agent
work, not worker work.

### Thread B — general-`k` Schur-module simplicity (the #4946 chain)

Targets sorry #2 (`schurModule_isSimple_general`).

```
PR #5002 (#4991 sub-B1, merged)
#4992  generalize Specht bridge + trace_symGroupAction/simpleSubmodule_iso to general k  [CLAIMED]
  ├─ #5005  general-k exists_unique_special_block assembly + helpers   [blocked on #4992]
  └─ #4976  general-k schurModule_isSimple_general assembly + resolve hN  →  removes sorry #2
            [blocked on #4992, #5005; carries replan]
```

Root obstruction (recorded in `lean-formalization` SKILL.md ~line 91, #2708 /
C-4a): the per-block inputs are hardcoded to `ℂ` and generic `k` does not
base-change from `ℂ` — `trace_symGroupAction_eq_spechtModuleCharacter`,
`youngSym_action_vanishes_off_block`,
`youngSym_action_on_special_block_rank_one_scaled_proj`,
`exists_unique_special_block`. The intended Sub-C predecessor (#4975) closed
COMPLETED but **landed no code**; #5014 (sub-C1) has since landed the general-`k`
vanishing + rank-one_scaled_proj lemmas. Live blocker is **#4992** (claimed).

### Thread C — Specht standard basis / Garnir straightening (the #4881/#4998 chain)

Targets sorry #4 (`twistedPolytabloid_residual_invariant`).

The leading-term elimination engine (`maxSrRankSupp`, `cardAtMaxSrRank`,
`resMeasure`, `resMeasure_sub_lt`, strong-induction assembly) and the consumer
`twistedPolytabloid_residual_in_V` are **fully proved, sorry-free** (PR #5011,
#5006). The lone remaining sorry is the isolated combinatorial invariant,
tracked by **#5010** — see "Design walls" below. Independent of Threads A/B and
of the broken-main emergency (the file builds green on its own).

### Thread D — the classification-core crux (sorry #3)

`schurWeyl_simples_formalCharacter_classification_core` (#4721) is the abstract
"simple polynomial rep ⇒ character is a `schurPoly`" step. It is being
**relocated/retired**, not filled in place: blocked issues **#5023** (#4994
sub-A, relocate general-`k` classification core + support into
`SchurWeylFormalCharacterIso`, emit `hSne`) and **#5024** (#4994 sub-B, retarget
the decompose-chain and *delete the false classification crux*) are the active
redesign, both blocked on the #5021 main repair. Review **#5017** audits the
surrounding cluster (#4985/#4989/#5009).

## Design walls — the genuinely hard remaining cruxes

1. **`twistedPolytabloid_residual_invariant` (#5010, sorry #4) — the James/Fulton
   column-straightening nut.** The frontier's hardest single lemma: 4+ sessions,
   no Lean landed. The global `Q ∩ w⁻¹Pw` coset/antisymmetry route was refuted
   (#4604); pointwise-Δ-vanishing, cross-region involution, and circular
   `tabloidSupport_straightening` are all refuted (see `progress/r2b-*.md`). The
   issue forbids a "fill the sorry" pass and demands a committed scoped route —
   **(R1)** per-tableau James conjugate-column antisymmetry at a column-standard
   tableau, or **(R2)** redesign the (sorry-free)
   `twistedPolytabloid_residual_in_V` to peel `f_w(σ)`'s own dominance-maximal
   term first. (C) tabloid-preservation and (I) IH-availability are provably
   inseparable in the equal-tabloid case, so a separable scaffold only relocates
   the sorry.

2. **A/det character identity (#4905, sorry #1) — blocked, not hard-blocked.**
   The mathematics (Cauchy decomposition + `det·A ≅ A⊗χ` highest-weight shift) is
   laid out and `detShiftLinearEquiv_intertwine` is sorry-free; the obstruction
   is purely logistical: the degree-`d` (A/det) packaging sits in **PR #4997**
   with failing CI. Land #4997 and this becomes ordinary assembly work.

3. **general-`k` special-block assembly (#4946/#4976, sorry #2) — base-change
   wall.** Schur-module simplicity over a general char-0 field cannot be obtained
   by base change from `ℂ`; each `ℂ`-specialised block lemma must be re-proved
   field-generically. Half the inputs are done (#5014); the Specht-bridge
   generalization (#4992) is the live gate.

4. **classification-core retire (#4721/#4994, sorry #3) — design, not proof.**
   The plan is to *delete* this crux by relocating the general-`k` classification
   core into `SchurWeylFormalCharacterIso` and emitting `hSne` from the
   equivariant decomposition (#5023/#5024), rather than discharge the abstract
   "character-determined ⇒ `schurPoly`" statement directly. Gated on the #5021
   main repair.

## One-glance status

- **Real sorries:** 4 (all Ch5). **Axioms/admits:** 0. **grep -rc noise factor:** ~18×.
- **Highest-priority unblock:** merge repair PR **#5022** (broken main), then
  repair CI on **PR #4997** (unblocks Thread A: #5003→#4961→#4905).
- **Live worker-actionable:** #4992 (claimed, Thread B gate); #5010 (Thread C nut,
  needs a committed R1/R2 route — not a casual claim).
- **Everything else** in the unclaimed feature queue (#4961, #4905, #5003, #4976,
  #5005, #5023, #5024) is `blocked` on the four in-flight PRs / main repair above.
- **Deferred infra:** #2841/#2564 Mathlib pin bump (v4.28.1 → v4.31.0, ~120
  errors / ~20 modules) — a coordinated atomic bump, not a single-session task.
</content>
