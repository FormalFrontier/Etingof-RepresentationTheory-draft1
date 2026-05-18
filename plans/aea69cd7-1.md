## Current state

Wave 62 landed three per-(F, Q) wrappers in the D2.* (i.e.,
`not_posdef_infinite_type_per_kQ` subgraph dispatch) family, none of
which received a dedicated audit. The same pattern (placement,
`[IsAlgClosed F]` propagation, statement-form fidelity to the
`_kQ`-free original) was previously audited by issue #2892 / PR #2894
for the fourth sibling `degree_ge_4_infinite_type_per_kQ` (PR #2891).
The three new siblings are now load-bearing in the
`not_posdef_infinite_type_per_kQ` outer assembly (merged via PR #2921
on top of the bridge architecture), so any pattern drift here will
silently affect the Theorem 2.1.2 forward direction.

The three wrappers (with sizes / files):

- **#2897 (D2.cycle)** — `graph_with_list_cycle_infinite_type_per_kQ`
  at `Chapter6/FieldGenericCycle.lean:440`. Universal counterpart:
  `graph_with_list_cycle_infinite_type`
  (`InfiniteTypeConstructions.lean:3910`). +241 lines, 2 files.
- **#2900 (D2.adjacent)** — `adjacent_branches_infinite_type_per_kQ`
  at `Chapter6/FieldGenericD5Tilde.lean:1043`. Universal counterpart:
  `adjacent_branches_infinite_type`
  (`InfiniteTypeConstructions.lean:4764`). +280 lines, 3 files.
- **#2903 (D2.single)** —
  `single_branch_not_posdef_infinite_type_per_kQ` at
  `Chapter6/FieldGenericTpqr.lean:1408`. Universal counterpart:
  `single_branch_not_posdef_infinite_type`
  (`InfiniteTypeConstructions.lean:8401`). +494 lines, 3 files.
  This PR also introduces a leaf-case stub
  (`single_branch_leaf_case_per_kQ`) — the audit scope is the
  *wrapper* portion only; the leaf-case body is separately tracked
  by #2904 / #2906.

**Open anomaly worth confirming, not just accepting.** The cycle
wrapper #2897 takes only `(F : Type) [Field F]` — it does **not**
carry `[IsAlgClosed F]`. The other two wrappers (#2900, #2903) and
the previously-audited #2891 all carry `[IsAlgClosed F]`. The
reviewer must determine whether dropping `[IsAlgClosed F]` in the
cycle case is correct (because the cycle subgraph dispatch genuinely
does not require algebraic closure) or whether it is a latent
inconsistency that will block downstream callers that expect a
uniform per-(F, Q) signature.

## Deliverables

Audit the three wrappers against their `_kQ`-free originals. Reuse
the five-deliverable structure from
`progress/reviews/2026-05-18-degree4-per-kQ-placement.md` (the #2894
template), but applied per-wrapper. Report verdict per-wrapper.

1. **Statement fidelity (per wrapper).** For each of the three
   wrappers, build a row-by-row diff against the `_kQ`-free original:
   adjacency args (`adj, hsymm, hdiag, h01`), subgraph-specific args
   (cycle / v₀,w,hv₀_deg,hw_deg,hvw_adj /
   hconn,h_acyclic,h_deg,v₀,hv₀,h_unique,h_not_posdef), field args
   `(F : Type) [Field F]` ± `[IsAlgClosed F]`, quiver args
   `(Q : @Quiver.{0,0} (Fin n)) [∀ a b, Subsingleton …]`, orientation
   arg `(hOrient : @Etingof.IsOrientationOf n Q adj)`, and the
   conclusion shape (`¬ IsFiniteTypeQuiver n adj` → per-(F, Q) set
   non-finiteness). Confirm no subgraph-specific hypothesis was
   silently dropped or reshaped.

2. **`[IsAlgClosed F]` carriage decision (cycle vs. adjacent/single).**
   Determine whether the cycle wrapper's omission of `[IsAlgClosed F]`
   is correct.
   * Trace the proof body of `graph_with_list_cycle_infinite_type_per_kQ`
     (`FieldGenericCycle.lean:440-…`): does any downstream call it makes
     actually require `[IsAlgClosed F]`? In particular, examine
     whatever per-(F, Q) cycle-shortening / cycle-recursion machinery
     it dispatches to, and confirm none of those callees secretly
     introduce a fresh `[IsAlgClosed F]` via `haveI`.
   * If `[IsAlgClosed F]` is genuinely unneeded for the cycle case,
     verify that every existing caller (search via
     `Grep "graph_with_list_cycle_infinite_type_per_kQ"`) supplies the
     three required arguments and only those, with no implicit
     `[IsAlgClosed F]` inference dangling.
   * If it *is* needed (e.g., for downstream dispatch into D2.adjacent
     or any other D2 sibling), file a FAIL with a fix issue: the
     wrapper must carry `[IsAlgClosed F]` for signature uniformity.
   * Either way, document the decision so future D2.* siblings have a
     clear precedent.

3. **Proof body fidelity (per wrapper).** For each wrapper, walk
   through the body and confirm it is **structurally parallel** to
   the universal original. Per-wrapper checklist:
   * `graph_with_list_cycle_infinite_type_per_kQ`: strong induction
     on cycle length is preserved; the chord-shortening case carves
     the cycle the same way; the no-chord base case dispatches to the
     same minimal-cycle lemma. Confirm the induction motive is the
     per-(F, Q) Set.Finite conclusion, not the universal
     `IsFiniteTypeQuiver` conclusion.
   * `adjacent_branches_infinite_type_per_kQ`: neighbor extraction
     (`set S₀`, `hS₀_card`, `Finset.card_eq_two.mp …`,
     `Equiv` construction) matches the universal. The dispatch into
     the four sub-cases (degree-3 ⨯ degree-3 neighbor configurations)
     reuses the same per-(F, Q) subgraph dispatch helpers as the
     universal uses, with `F, Q, hOrient` threaded consistently.
   * `single_branch_not_posdef_infinite_type_per_kQ`: the degree-3
     uniqueness reduction (`h_deg_le2`) and the subsequent dispatch
     into leaf-case vs. extend-case sub-helpers preserve the universal
     argument structure. The leaf-case stub (`sorry` or
     `single_branch_leaf_case_per_kQ` reference) is acceptable for the
     wrapper audit — its body is out of scope here.

4. **Outer-assembly call-site fidelity.** The three wrappers must be
   used inside
   `not_posdef_infinite_type_per_kQ`
   (`Chapter6/FieldGenericInfiniteType.lean` or
   `FieldGenericAssembly.lean` — locate via
   `Grep`). For each wrapper, find the call site and verify:
   * The wrapper is called with the same argument *positions* as the
     universal version (modulo the appended `F, Q, hOrient`).
   * If the cycle wrapper is called without `[IsAlgClosed F]`, the
     surrounding call site does not gratuitously assume it either.
   * No call site silently introduces a fresh hypothesis that should
     have been threaded through the wrapper.

5. **Cross-wrapper signature uniformity.** Compare the three wrapper
   signatures against each other and against the previously-audited
   #2891. Three uniformity properties to confirm:
   * Conclusion form is **byte-identical** across all four wrappers
     (modulo the universal `n`).
   * Field/quiver/orientation carriage is consistently placed at the
     end of the argument list (subject to the `[IsAlgClosed F]`
     decision from deliverable 2).
   * Variable naming (`F, Q, hOrient`) is uniform across all four.

Write the audit report to
`progress/reviews/2026-05-19-d2-wrapper-trilogy-per-kQ.md` using the
standard PASS / FAIL-with-fix-recommendations verdict structure.
Report one verdict per deliverable per wrapper (so up to 15
per-deliverable verdicts total: 5 deliverables × 3 wrappers, with
deliverable 5 combined across all three).

If FAIL on any deliverable, file the necessary fix issues and link
them in the report. If PASS, no code changes — just the report.

## Context

- Pattern reference (D2.degree4 audit, PR #2891 = #2892 closure):
  `progress/reviews/2026-05-18-degree4-per-kQ-placement.md`. Same
  five-deliverable depth expected; signature-uniformity dimension
  added because we now have four wrappers to compare.
- Outer assembly (consumes all four wrappers):
  `not_posdef_infinite_type_per_kQ` — landed in PR #2921.
  Locate the current definition via
  `Grep "theorem not_posdef_infinite_type_per_kQ"`.
- Universal originals:
  * `graph_with_list_cycle_infinite_type`
    (`Chapter6/InfiniteTypeConstructions.lean:3910`)
  * `adjacent_branches_infinite_type`
    (`Chapter6/InfiniteTypeConstructions.lean:4764`)
  * `single_branch_not_posdef_infinite_type`
    (`Chapter6/InfiniteTypeConstructions.lean:8401`)
- Universal outer assembly: roughly
  `Chapter6/InfiniteTypeConstructions.lean:10620-10660` —
  search for `not_posdef_not_finite_type` /
  `non_adjacent_branches_infinite_type` to locate the universal
  dispatcher that calls all four siblings.
- Per-(F, Q) wrappers (audit targets):
  * `Chapter6/FieldGenericCycle.lean:440` —
    `graph_with_list_cycle_infinite_type_per_kQ`
    (no `[IsAlgClosed F]`)
  * `Chapter6/FieldGenericD5Tilde.lean:1043` —
    `adjacent_branches_infinite_type_per_kQ`
    (has `[IsAlgClosed F]`)
  * `Chapter6/FieldGenericTpqr.lean:1408` —
    `single_branch_not_posdef_infinite_type_per_kQ`
    (has `[IsAlgClosed F]`)
- Previously-audited sibling (precedent):
  * `Chapter6/FieldGenericStar.lean:649` —
    `degree_ge_4_infinite_type_per_kQ`
    (audited in PR #2894; has `[IsAlgClosed F]`)
- Out of scope for this audit: the `single_branch_leaf_case_per_kQ`
  stub introduced inside #2903 — its body is tracked by #2904 /
  #2906 and will get its own audit cycle once filled.

## Verification

- Audit report posted at
  `progress/reviews/2026-05-19-d2-wrapper-trilogy-per-kQ.md`
  with one verdict per (deliverable, wrapper) pair.
- The `[IsAlgClosed F]` carriage decision from deliverable 2 is
  written down explicitly (correct / latent inconsistency / requires
  follow-up fix), with a one-paragraph rationale tied to actual
  body inspection — not just signature staring.
- Any FAIL has a tracking fix issue filed and linked.
- No code changes from this audit unless deliverable 2 surfaces a
  blocking inconsistency — even then, file a fix issue rather than
  patching in this PR.
