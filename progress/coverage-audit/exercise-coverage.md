# Exercise / problem coverage

Final audit date: 2026-08-01.

This file is the human-readable projection of the per-item/per-subpart ledger in
`progress/items.json`. Regenerate both with
`python3 scripts/reconcile_exercise_coverage.py` and verify the ratchet with
`python3 scripts/validate_exercise_coverage.py`.

## Final totals

- Exercise/problem items: **102** (96 `covered_full`, 6 `covered_partial`).
- Audited source claim units: **407**.
- Formalized or accepted derived units: **382**.
- Scope/correction-justified units: **17** (16 intentional omissions, 1 documented source correction).
- Non-formalizable source prompts: **8**.
- Untracked gaps: **0**.

A `covered_partial` verdict is permitted only for the exact units linked to a current
scope entry in `skipped-exercises.md`. Open-ended prompts are enumerated rather than
silently dropped, but do not count as formal proof obligations.

## Book-order ledger

| Item | Coverage | Units | Unit verdicts |
| --- | --- | ---: | --- |
| `Chapter2/Problem2.3.15` | `covered_full` | 2 | 2 formalized |
| `Chapter2/Problem2.3.16` | `covered_full` | 7 | 2 covered_elsewhere, 5 formalized |
| `Chapter2/Problem2.3.17` | `covered_full` | 3 | 1 covered_elsewhere, 2 formalized |
| `Chapter2/Problem2.3.18` | `covered_full` | 4 | 4 formalized |
| `Chapter2/Problem2.4.1` | `covered_full` | 4 | 1 covered_elsewhere, 3 formalized |
| `Chapter2/Problem2.5.1` | `covered_full` | 2 | 2 formalized |
| `Chapter2/Problem2.5.2` | `covered_full` | 10 | 10 formalized |
| `Chapter2/Problem2.7.4` | `covered_full` | 7 | 7 formalized |
| `Chapter2/Problem2.7.5` | `covered_full` | 7 | 7 formalized |
| `Chapter2/Problem2.8.6` | `covered_full` | 5 | 5 formalized |
| `Chapter2/Problem2.8.11` | `covered_full` | 5 | 5 formalized |
| `Chapter2/Exercise2.9.5` | `covered_full` | 1 | 1 formalized |
| `Chapter2/Exercise2.9.11` | `covered_full` | 1 | 1 formalized |
| `Chapter2/Exercise2.11.2` | `covered_full` | 2 | 2 formalized |
| `Chapter2/Problem2.11.3` | `covered_full` | 16 | 16 formalized |
| `Chapter2/Exercise2.11.5` | `covered_full` | 2 | 2 formalized |
| `Chapter2/Problem2.11.6` | `covered_partial` | 7 | 1 covered_elsewhere, 1 formalized, 5 intentional_omission |
| `Chapter2/Exercise2.11.7` | `covered_full` | 1 | 1 formalized |
| `Chapter2/Problem2.13.1` | `covered_partial` | 9 | 2 formalized, 5 intentional_omission, 2 non_formalizable |
| `Chapter2/Problem2.14.3` | `covered_full` | 2 | 1 covered_elsewhere, 1 formalized |
| `Chapter2/Problem2.15.1` | `covered_full` | 16 | 4 covered_elsewhere, 12 formalized |
| `Chapter2/Problem2.16.1` | `covered_full` | 4 | 2 covered_elsewhere, 1 formalized, 1 non_formalizable |
| `Chapter2/Problem2.16.2` | `covered_full` | 6 | 6 formalized |
| `Chapter2/Problem2.16.3` | `covered_full` | 7 | 7 formalized |
| `Chapter2/Problem2.16.4` | `covered_full` | 5 | 5 formalized |
| `Chapter2/Problem2.16.5` | `covered_partial` | 9 | 6 formalized, 2 intentional_omission, 1 non_formalizable |
| `Chapter3/Problem3.3.3` | `covered_full` | 17 | 6 covered_elsewhere, 10 formalized, 1 non_formalizable |
| `Chapter3/Exercise3.6.1` | `covered_full` | 1 | 1 formalized |
| `Chapter3/Problem3.8.3` | `covered_full` | 1 | 1 formalized |
| `Chapter3/Problem3.8.4` | `covered_full` | 6 | 2 covered_elsewhere, 4 formalized |
| `Chapter3/Problem3.8.5` | `covered_full` | 5 | 5 formalized |
| `Chapter3/Problem3.9.1` | `covered_full` | 12 | 1 covered_elsewhere, 11 formalized |
| `Chapter3/Problem3.9.2` | `covered_full` | 9 | 9 formalized |
| `Chapter3/Problem3.9.3` | `covered_full` | 7 | 7 formalized |
| `Chapter3/Problem3.9.4` | `covered_full` | 5 | 4 formalized, 1 non_formalizable |
| `Chapter3/Problem3.9.5` | `covered_full` | 10 | 2 covered_elsewhere, 8 formalized |
| `Chapter3/Exercise3.10.1` | `covered_full` | 1 | 1 formalized |
| `Chapter4/Problem4.1.4` | `covered_full` | 1 | 1 formalized |
| `Chapter4/Exercise4.2.3` | `covered_full` | 1 | 1 formalized |
| `Chapter4/Exercise4.3.1` | `covered_full` | 1 | 1 formalized |
| `Chapter4/Problem4.5.2` | `covered_full` | 2 | 2 formalized |
| `Chapter4/Problem4.12.1` | `covered_full` | 2 | 2 formalized |
| `Chapter4/Problem4.12.2` | `covered_full` | 4 | 4 formalized |
| `Chapter4/Problem4.12.3` | `covered_full` | 2 | 2 formalized |
| `Chapter4/Problem4.12.4` | `covered_full` | 1 | 1 formalized |
| `Chapter4/Problem4.12.5` | `covered_full` | 3 | 3 formalized |
| `Chapter4/Problem4.12.6` | `covered_full` | 3 | 3 formalized |
| `Chapter4/Problem4.12.7` | `covered_full` | 6 | 6 formalized |
| `Chapter4/Problem4.12.8` | `covered_full` | 2 | 2 formalized |
| `Chapter4/Problem4.12.9` | `covered_full` | 2 | 2 formalized |
| `Chapter4/Problem4.12.10` | `covered_full` | 3 | 3 formalized |
| `Chapter4/Problem4.12.11` | `covered_full` | 5 | 5 formalized |
| `Chapter5/Problem5.1.2` | `covered_full` | 4 | 4 formalized |
| `Chapter5/Exercise5.1.7` | `covered_full` | 1 | 1 formalized |
| `Chapter5/Problem5.2.7` | `covered_full` | 2 | 2 formalized |
| `Chapter5/Exercise5.3.3` | `covered_full` | 1 | 1 formalized |
| `Chapter5/Problem5.8.4` | `covered_full` | 1 | 1 formalized |
| `Chapter5/Exercise5.8.5` | `covered_full` | 2 | 2 formalized |
| `Chapter5/Problem5.10.2` | `covered_full` | 1 | 1 non_formalizable |
| `Chapter5/Discussion_Problem5.10.2_parts` | `covered_full` | 6 | 6 formalized |
| `Chapter5/Problem5.11.1` | `covered_full` | 5 | 5 formalized |
| `Chapter5/Problem5.12.5` | `covered_full` | 1 | 1 formalized |
| `Chapter5/Problem5.16.1` | `covered_full` | 2 | 2 formalized |
| `Chapter5/Problem5.16.2` | `covered_full` | 1 | 1 formalized |
| `Chapter5/Problem5.16.3` | `covered_full` | 3 | 3 formalized |
| `Chapter5/Problem5.24.1` | `covered_full` | 3 | 3 formalized |
| `Chapter5/Problem5.24.2` | `covered_full` | 1 | 1 formalized |
| `Chapter5/Exercise5.27.2` | `covered_full` | 3 | 3 formalized |
| `Chapter5/Exercise5.27.3` | `covered_full` | 3 | 3 formalized |
| `Chapter6/Problem6.1.1` | `covered_full` | 2 | 2 formalized |
| `Chapter6/Problem6.1.2` | `covered_full` | 3 | 3 formalized |
| `Chapter6/Problem6.1.3` | `covered_full` | 1 | 1 formalized |
| `Chapter6/Problem6.1.3_continued_E7_E8` | `covered_full` | 5 | 5 formalized |
| `Chapter6/Problem6.1.3_continued_tildeE` | `covered_full` | 3 | 3 formalized |
| `Chapter6/Problem6.1.5` | `covered_full` | 1 | 1 formalized |
| `Chapter6/Problem6.1.5_parts` | `covered_full` | 3 | 3 formalized |
| `Chapter6/Problem6.1.6` | `covered_partial` | 7 | 4 formalized, 3 intentional_omission |
| `Chapter6/Problem6.9.1` | `covered_partial` | 6 | 4 formalized, 1 intentional_omission, 1 non_formalizable |
| `Chapter6/Problem6.9.2` | `covered_full` | 4 | 4 formalized |
| `Chapter6/Problem6.9.3` | `covered_full` | 3 | 3 formalized |
| `Chapter7/Problem7.7.3` | `covered_full` | 1 | 1 formalized |
| `Chapter7/Exercise7.8.4` | `covered_full` | 3 | 3 formalized |
| `Chapter7/Problem7.8.5` | `covered_full` | 2 | 2 formalized |
| `Chapter7/Problem7.8.7` | `covered_full` | 4 | 4 formalized |
| `Chapter7/Exercise7.9.7` | `covered_full` | 2 | 2 formalized |
| `Chapter7/Exercise7.9.8` | `covered_full` | 2 | 2 formalized |
| `Chapter8/Problem8.1.3` | `covered_full` | 4 | 4 formalized |
| `Chapter8/Exercise8.1.4` | `covered_full` | 1 | 1 formalized |
| `Chapter8/Exercise8.2.2` | `covered_full` | 2 | 2 formalized |
| `Chapter8/Problem8.2.5` | `covered_full` | 5 | 5 formalized |
| `Chapter8/Problem8.2.6` | `covered_full` | 6 | 6 formalized |
| `Chapter8/Problem8.2.7` | `covered_full` | 4 | 4 formalized |
| `Chapter8/Problem8.2.8` | `covered_partial` | 3 | 2 formalized, 1 source_correction |
| `Chapter8/Exercise8.2.9` | `covered_full` | 3 | 3 formalized |
| `Chapter8/Problem8.2.10` | `covered_full` | 6 | 6 formalized |
| `Chapter9/Problem9.3.2` | `covered_full` | 3 | 3 formalized |
| `Chapter9/Problem9.4.2` | `covered_full` | 5 | 5 formalized |
| `Chapter9/Problem9.4.5` | `covered_full` | 3 | 3 formalized |
| `Chapter9/Problem9.4.6` | `covered_full` | 3 | 3 formalized |
| `Chapter9/Problem9.5.3` | `covered_full` | 5 | 5 formalized |
| `Chapter9/Exercise9.6.3` | `covered_full` | 2 | 2 formalized |
| `Chapter9/Problem9.6.5` | `covered_full` | 4 | 4 formalized |
