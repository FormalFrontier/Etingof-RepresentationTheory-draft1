# Stage 3.7 Fidelity Sweep — Wave 4 (cross-vendor verified-bucket probe, Codex)

Cross-vendor (Codex, OpenAI — no Claude quota) spot-check of 5 headline `verified` theorems to bound residual false-negatives in the verified bucket.

## Results (5 probed)
- **Faithful (cross-vendor confirmed): 2** — Theorem 4.5.1 (orthogonality), Lemma 7.5.1 (Yoneda).
- **Real gap caught: 1** — **Theorem 9.2.1(i)**: book says "**unique** indecomposable projective P_i"; Lean omits the uniqueness conjunct. Two prior passes missed it. → issue #5669.
- **Minor/tightening: 1** — Theorem 6.5.2: combined Gabriel decl only re-exports finiteness; part (b) standalone assumes B(d,d)=2 (discharged elsewhere). Parts a/b/c exist and are faithful. → issue #5670.
- **False alarm (methodology): 1** — Theorem 5.18.1: flagged only because I pointed Codex at one sub-declaration; the double-centralizer + semisimplicity are in sibling declarations. Stays verified.

## Takeaways
- The `verified` bucket is broadly sound but **not perfect even for headliners**: a third vendor found 1 genuine dropped-conjunct (uniqueness) + 1 worth tightening, out of 5. A full verified re-audit would likely surface a handful more uniqueness/explicit-conjunct omissions — lower severity than the wave-2 downgrades.
- **Methodology fix for any verified re-audit:** give the auditor the whole theorem's *declaration family*, not a single sub-declaration, or you get 5.18.1-style false gaps.
- Cross-vendor (Codex) is cheap (OpenAI billing) and complementary — worth using as the tiebreak/third-opinion layer.
