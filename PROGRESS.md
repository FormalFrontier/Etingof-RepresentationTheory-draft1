# Formalization Progress

Progress is recorded here as stages from PLAN.md are completed.

## Completion policy

Completion requires zero blocking proof placeholders: no `sorry`, `admit`, or
project axiom declarations. A `proof_wanted` is non-blocking only when its item
has `scope_approved_proof_wanted` status in `progress/items.json` and is
individually justified in `skipped-exercises.md`. Remark 2.9.3's Ado–Iwasawa
marker is the sole current approval and is outside the project's proof
obligation; it must not be counted as active mathematical work. New approvals
require an explicit scope entry, matching metadata, and review.

## Stage 1.1: Page Extraction
- **Status:** Complete
- **Date:** 2026-03-14
- **Notes:** 235 pages extracted from `source/original.pdf` into `pdf/raw-pages/`.

## Stage 1.2: Lean Build
- **Status:** Complete
- **Date:** 2026-03-15
- **Notes:** Lean project initialized, Mathlib built. CI workflow active on PRs.

## Stage 1.3: Frontmatter Detection
- **Status:** Complete
- **Date:** 2026-03-15
- **Notes:** 8 frontmatter pages, 227 main content pages (1–227). Mapping in `pdf/pages/mapping.json`.

## Stage 1.4: Page Transcription
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 235 pages transcribed (8 frontmatter + 227 main content). 235 `.md` files in `pages/`. Spurious PDF running headers cleaned up across all pages. Quality spot-check passed on 10-page sample.

## Stage 1.5: Structure Analysis
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 10 chapters structured. 583 items identified across frontmatter, 9 chapters, and backmatter. Contiguity validation passed. `items.json` assembled.

## Stage 1.6: Blob Extraction
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 583 blob files extracted. 1:1 correspondence validated — no gaps, overlaps, or orphans.

## Stage 2.1: Internal Dependency Analysis
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 583 internal dependency entries (conservative: each item depends on all predecessors). Accuracy validated — 100% correct on spot check.

## Stage 2.2: External Dependency Analysis
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 58 external dependencies identified (33 undergrad prerequisites, 15 external results, 10 folklore). 163/583 items (28%) reference external deps. Descriptions accurate; item attribution ~50% error rate (to be fixed in Stage 3.3).

## Stage 2.3: Blueprint Assembly
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 583-item leanblueprint DAG generated. HTML blueprint builds via plastex. All items and dependency edges validated.

## Stage 2.4: Mathlib Coverage Research
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** External deps: 34 exact (59%), 15 partial (26%), 9 missing (16%). Book definitions (83 total): 46 exact (55%), 21 partial (25%), 16 gap (19%). 4 wrong Mathlib names corrected during review.

## Stage 2.5: External Sources Research
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 52 gap/partial items have identified external sources (87 entries, 66 high-usefulness). Primary formal source: MathComp. No uncovered gaps.

## Stage 2.6: Readiness Report
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** Readiness report compiled (#498). Reviewed and validated (#512). Risk assessments calibrated for all chapters.

## Stage 2.7: Reference Attachment
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** Stage 2.7 tooling built (#505). .refs.md companion files generated for all items (#515). Output reviewed and validated (#529).

## Stage 3.1: Scaffolding
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 8 chapters (2–9) scaffolded: 231 Lean files, ~249 sorry placeholders. Module structure established (#535). Chapter 2 reviewed (#539). Remaining chapter reviews pending (#531, #541, #542, #543). Three scaffolding patterns: Mathlib alias, custom definition, sorry'd statement.

## Stage 3.2: Proof Filling
- **Status:** Complete
- **Date started:** 2026-03-16
- **Completion date:** 2026-07-29
- **Notes:** The release scan reports zero blocking `sorry`, `admit`, wanted-definition/instance, or project-axiom declarations. The sole wanted theorem is the individually approved, non-blocking `Etingof.ado` marker, whose deliberate omission is documented in `skipped-exercises.md` and machine-readable metadata. Exercise reconciliation reports 96 fully covered exercises, six documented scope/correction partials, and zero untracked gaps. All chapter aggregates build.

## Stage 3.4: Dependency Trimming
- **Status:** Complete
- **Completion date:** 2026-08-01
- **Notes:** Imported kernel types and theorem/opaque bodies were inspected with
  `allowOpaque := true`: 32,904 declarations across 839 current imported
  modules. The certificate records every source-level proof declaration and all
  cross-module constants, bound to source, extractor, toolchain, raw extraction,
  and full-build hashes. Re-export hubs are expanded to their implementation
  modules under a deterministic single-owner attribution. Against the 521-edge
  import baseline, 133 edges were not recovered through the owned-module
  kernel proof/type projection and were trimmed,
  while 203 proof-supported associations were discovered beyond it. The mapped
  relation has six item-level cyclic components; the shipped 583-edge graph is
  its maximal deterministic acyclic subset, with all eight cycle-excluded edges and
  their paths retained explicitly in
  `progress/reviews/2026-08-01-stage3-4-proof-terms.json`.
  Imported modules without an unambiguous item owner remain fully inventoried in
  that certificate and are deliberately omitted from the item-level projection.

## Stage 3.5: Proof Polishing
- **Status:** Complete
- **Completion date:** 2026-08-01
- **Notes:** The source-bound screening certificate covers all 403 provider-backed
  partition items plus ten derived overlays and conservatively inventories
  11,427 source-facing theorem/opaque declarations (private declarations are
  included; some generated declarations may also remain), out of 26,858 kernel
  proof declarations. The final repository sweep succeeded with the Mathlib
  standard linter set. All 1,145 unique remaining diagnostics in 199
  files have an exact source location, nearest source command, category, and
  explicit disposition; none is a blocking `sorry`, metavariable, unsolved-goal,
  or multi-goal proof diagnostic. Retained findings are represented honestly as
  nonblocking compile-sensitive tactic suggestions, API-generality/style,
  formatting, or resource-annotation follow-ups in
  `progress/reviews/2026-08-01-stage3-5-proof-polishing.json`.

## Stage 3.6: Completeness Audit
- **Status:** Complete (bounded audit; not a completeness proof)
- **Completion date:** 2026-08-01
- **Notes:** The final certificate is
  `progress/coverage-audit/completeness-audit-wave-1.md`. Two consecutive dry
  coverage passes closed the search; all 266 claim-bearing partition items have
  verified fidelity and structured claim coverage; all ten accepted derived
  claims have sorry-free providers; and all 102 exercises are reconciled (96
  full, six documented partial, zero untracked gaps). The certificate records
  the bounded method and residual false-negative risk.
