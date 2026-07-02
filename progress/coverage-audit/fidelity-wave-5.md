# Stage 3.7 Fidelity Sweep — Wave 5 certificate (Chapter 2 verified-bucket re-audit, Opus)

Issue #5339 (epic #5338). A careful, model-diverse re-audit of **all 48 `verified` claim-bearing items** in Chapter 2, judged by Opus (diverse from the Sonnet waves 2–3 and calibrated against the Opus wave-1 that first flagged many of these as gaps). Six parallel auditors, each reading the book blob → locating the whole declaration family → reading the full statement, then applying PLAN.md §3.2 steps 6–7 (anti-vacuity decision test + conjunct-by-conjunct fidelity). Wave-4's methodology fix (give the auditor the whole declaration family, not one sub-declaration) was enforced to avoid 5.18.1-style false gaps.

## Headline

- Re-audited **48/48** Chapter-2 `verified` items.
- **Confirmed verified: 45.**
- **New fidelity gaps: 0.** This is a **dry pass** for the Chapter-2 verified bucket.
- **Unsure (bookkeeping, not statement gaps): 3** — one transcription gap filed, two narrative-remark justification records added.

Chapter 2 was the chapter wave-1 called shakiest (34 verified / 13 gap / 6 unsure of 53). Since then the concurrent pod repaired every wave-1/2 statement gap (2.14.1, 2.14.2, 2.3.3 part 4, 2.3.14, 2.3.14_continued, 2.9.2, 2.9.8, 2.9.12, 2.9.13, 2.3.11, 2.3.13, 2.9.3, 2.11.4). This wave confirms each repair genuinely attaches the required structure and asserts the substantive content — a fresh, adversarial Opus pass found nothing further to downgrade.

## The 3 unsure items (none is a statement-fidelity gap)

- **Definition2.8.10** (homomorphism of quiver representations) — the Lean `QuiverRepresentationHom` (per-vertex component maps + naturality) is a correct standard definition, but the **book blob is empty (1 byte)**: a Stage-1.7 transcription failure, so fidelity cannot be checked against book text. Filed re-extract **#5829** (mirrors #5666, which fixed the then-empty sibling 2.8.9). Wave-1 and wave-3 misattributed the empty blob to 2.8.9; 2.8.9 now has real content (152 B) and its Lean is faithful. Rests at `verified` on construction merits pending re-extraction.
- **Remark2.8.7** — purely narrative (advises using Definition 2.8.3's viewpoint for quiver reps); no crisp formalizable claim, no declaration. Non-formalizable; a justification record was added to `items.json` (was previously `verified` with no note).
- **Remark2.9.10** — purely narrative meta-comment on Definition 2.9.9 (basis-dependence, to be replaced by a basis-independent definition later); no formalizable claim, no declaration. Non-formalizable; justification record added.

## Notable confirmations (formerly-flagged items, now genuinely faithful)

- **2.9.12 / 2.9.13** — sl(2) and Heisenberg built concretely on k×k×k, bracket relations verified by `ring`, U(𝔤) relations (HE−EH=2E …; YX−XY=C …) proven via ι, Weyl algebra = U(ℋ)/(C−1). Not the old generic `inferInstance`.
- **2.14.1 / 2.14.2** — the Leibniz tensor action and the contragredient dual action are attached via real Mathlib `LieRingModule`/`LieModule` instances plus proved characterizing lemmas (`lie_tmul`, `lieDualRepresentation_lie_apply`), not docstring-only.
- **2.7.1** — part (ii) (q-Weyl basis) is now present alongside part (i); both assert independence AND spanning.
- **2.3.11 / 2.3.13 / 2.9.3 / 2.11.4** — the counterexample over ℝ, the 1-dim⟹irreducible fact, Ado's theorem (as a genuine `proof_wanted`, no axiom/sorry), and the tensor-product-over-a-noncommutative-ring construction are all now real declarations.

## Method & scope

- One Opus auditor per batch (theorems/cors/props; defs 2.2–2.3; defs 2.7–2.9; defs 2.11–2.14; examples; remarks). Full declaration-family reads; several auditors also confirmed the files type-check.
- Per-item verdicts recorded in `progress/coverage-audit/verdicts-w5-Chapter2.json` and folded into `items.json` (`fidelity_note` for the 3 unsure items).
- Bounded single-judge audit, not a completeness proof. Two medium-confidence type-alias definitions (2.9.1 defers Jacobi to the `LieRing` typeclass; 2.9.7 keeps the action in the presupposed `LieRingModule` argument) are faithful read with their binder context — the standard Mathlib encoding — and are recorded as such.

## Convergence

For **issue #5339** the done criterion — every Chapter-2 worklist item `verified` or `gap` — was already met by waves 2–4; this wave provides the model-diverse confirmation the epic asked for. The Chapter-2 verified bucket is now a **dry pass** (0 new gaps) under an adversarial Opus judge. The 3 gaps recorded earlier (Definition2.2.1 #5616, Definition2.2.2 #5617, Remark2.3.2 #5650) remain open repair items; Remark2.9.4 was repaired (#5661) and Remark2.9.14 is `non_formalizable` (n/a). The one new artifact is transcription issue **#5829** (empty 2.8.10 blob).
