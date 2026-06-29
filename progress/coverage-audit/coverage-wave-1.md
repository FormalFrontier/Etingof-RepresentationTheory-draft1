# Stage 3.7 Coverage Arm — certificate

Sweep of all **211 prose blobs** (type discussion/introduction; exercises and proof-correctness out of scope) for formalizable mathematical claims with no Lean declaration. Model-diverse Sonnet subagents; Codex cross-vendor tiebreak; recording = lightweight + per-blob `coverage_swept` stamp (user decision).

## Waves

- **Wave 1 (full):** 12 batches, every one of the 211 prose blobs read and judged against current `main`. Result: 126 none · 62 covered · 9 non_formalizable · 4 trivial · 10 gap-blobs (11 claims).
- **Wave 2 (adversarial):** skeptical re-sweep of the 35 displayed-math blobs wave-1 marked none/covered. Found **1** new gap (Ch5 conjugacy-class counts, `Discussion_5.25.1`); Ch2/3/4/6/7 confirmed dry.
- **Codex tiebreak:** the two Ch2 tensor candidates (`Discussion_pure_tensors`, `Discussion_tensor_product_maps`) ruled `trivial_mathlib` (`TensorProduct.assoc`/`.map`) — excluded from gaps.
- **Wave 3 (dry-confirmation, Ch5):** DRY — re-read all 17 Ch5 displayed-math blobs, 0 new gaps. (A first attempt was blocked by a Claude subagent token rotation; re-run after re-auth.)
- **Wave 4 (final dry-confirmation, all high-risk):** DRY — re-read all 35 high-risk blobs (Ch5 + Ch2/3/4/6/7), 0 new gaps.

## Genuine coverage gaps filed (9 issues + `derived` items)

- #5676 — `Chapter2/Discussion_2.1_irreducible_indecomposable`
- #5677 — `Chapter5/Discussion_1dim_reps`
- #5678 — `Chapter5/Discussion_5.11_examples`
- #5679 — `Chapter5/Discussion_5.25.1`
- #5680 — `Chapter5/Discussion_after_Definition5.23.1`
- #5681 — `Chapter5/Discussion_complementary_series_summary`
- #5682 — `Chapter5/Discussion_footnote_5.15`
- #5683 — `Chapter7/Discussion_after_Definition7.9.1`
- #5684 — `Chapter7/Discussion_after_Example7.9.5`

(The lex-ordering claim spans both `Discussion_footnote_5.15` and `Discussion_proof_of_Frobenius_character_formula`; filed once as #5682.)

## Pre-existing [coverage] gaps (already tracked by the fidelity arm — NOT re-filed)

- #5624 — Corollary6.8.2
- #5657 — Corollary9.7.3
- #5655 — Definition7.9.1
- #5632 — Example4.3_Q8
- #5647 — Example7.9.6
- #5648 — Example9.5.2
- #5651 — Remark2.3.11
- #5649 — Remark2.3.13
- #5650 — Remark2.3.2
- #5661 — Remark2.9.4
- #5663 — Remark3.10.3
- #5662 — Remark3.8.6
- #5654 — Remark5.2.8
- #5652 — Remark5.8.3
- #5653 — Remark5.9.2
- #5656 — Theorem4.1.1

## Durability / verification

- Every one of the 211 prose blobs carries a `coverage_swept: {wave, result}` stamp in `progress/items.json`; the nothing-skipped query returns **0 violators**.
- The 9 accepted gaps are `derived` items (status=accepted) with `coverage_issue` pointers.
- Chapters 3, 4, 6, 8, 9 prose came back clean (0 new gaps); the suspected "Ch9 Morita B_n family missing" was false.

## Residual risk / termination

- This is a bounded audit, NOT a completeness proof. Wave 1 was a full read of all 211 prose blobs; waves 2–4 were adversarial re-sweeps of the 35 high-risk (displayed-math) blobs. **Two consecutive dry waves WERE achieved:** Ch2/3/4/6/7 were dry in wave 2 and again in wave 4; Ch5 was dry in wave 3 and again in wave 4. Strict loop-until-2-dry termination met.
- Single-judge-per-claim with cross-vendor tiebreak on disputes; residual false-negatives possible, concentrated in Ch5 (the densest chapter).