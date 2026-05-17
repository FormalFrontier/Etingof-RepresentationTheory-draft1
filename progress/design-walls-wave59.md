# Wave 59 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress.
Wave 58 recorded one wall (Wall 1, 4 waves stale) plus two active
chains (Wall 3 with three pivots, Schur-Weyl C-tier in motion). Wave
59 records the same structural shape but with substantial movement
on both chains and a **major refactor of the Wall 1 dependency
surface**: per-(F, Q) decomposition pushes the framework question off
the ℂ-specific stubs and onto two new F-generic stubs, while
deliverable 1 of the Ch2 forward bridge has landed.

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework — RESTRUCTURED, NOT CLOSED

**Context.** Same framework question as waves 54-58. The current
single-nilpotent-twist construction is provably **false** for every
m ≥ 1: the e_m direction peels off as a 1-dim summand at the center.
The wave-54 doc
`progress/indecomposability-framework-investigation.md` carries
explicit counter-examples for `etilde6v2Rep 1`, `etilde7Rep 1`,
`t125Rep 1`. No mathematical movement since wave 54.

**File state (substantively changed).** Wave 58 had 3 framework-wall
sorries, all in `Chapter6/InfiniteTypeConstructions.lean` (lines
3344, 3599, 3826). Wave 59 has **5 framework-wall sorries** across
three files:

- `Chapter6/InfiniteTypeConstructions.lean:3344` —
  `etilde6v2Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/InfiniteTypeConstructions.lean:3599` —
  `etilde7Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/InfiniteTypeConstructions.lean:3826` —
  `t125Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/FieldGenericETilde6.lean:283` —
  `etilde6Rep_kQ_isIndecomposable` (F-generic, **on active chain**).
- `Chapter6/FieldGenericETilde7.lean:292` —
  `etilde7Rep_kQ_isIndecomposable` (F-generic, **on active chain**).

The three ℂ-specific stubs are no longer routed through by Theorem
2.1.2 forward (which now uses the per-(F, Q) chain). They can be
deleted post-closure but currently remain in source.

The two new F-generic stubs were introduced by:
- PR #2809 (sub of #2807) for `etilde6Rep_kQ_isIndecomposable`.
- PR #2810 (closes #2792) for `etilde7Rep_kQ_isIndecomposable`.

Both stubs carry the same single-nilpotent-twist structure as their
ℂ-specific predecessors and inherit the same framework question.
Until #2436 produces a framework answer, neither closes; until they
close, Theorem 2.1.2 forward bridge cannot fully close.

**Options** (unchanged from wave 54):

- **Option A — Book's Tits-form / orbit-counting argument.** Lean
  algebraic-geometry infrastructure (orbit maps, dimension of
  quasi-projective varieties, constructible sets). Estimate: 6+
  months.

- **Option B — Stronger explicit construction.** Couple multiple arms
  to block D/F with independent nilpotents, or add a γ-style
  center-to-center iso bridging independent arms. Estimate: weeks per
  case. Would apply directly to the F-generic stubs in
  `FieldGenericETilde6.lean` / `FieldGenericETilde7.lean` (and a
  future `FieldGenericT125.lean` analogue once #2793 is decomposed).

- **Option C — Subgraph transfer for non-sporadic T(p,q,r).** Partial
  step; does not close the sporadic Ẽ₆ / Ẽ₇ / Ẽ₈ but would lighten
  the load on the F-generic chain. The cycle and K_{1,4}
  D̃₄ F-generic cases (PRs #2799, #2798) plus the per-(F, Q)
  subgraph transfer (PR #2805) demonstrate that this can work
  end-to-end for non-sporadic cases.

**Blocks (revised wave 59).** 2 live F-generic Ch6 sorries +
1 Ch2 downstream (Theorem 2.1.2 forward, partially decomposed via
#2774 but with end-to-end closure still gated on the two F-generic
Wall 1 stubs). The 3 ℂ-specific stubs are dead code w.r.t. the
forward bridge but remain in source.

**Status.** Issue #2436 is still `human-oversight`, `replan`. Wave 59
is the **fifth** consecutive wave with no Wall 1 movement. Still the
longest-running open item in the project. The per-(F, Q) refactor
is a structural workaround that narrows where Wall 1 is felt — it
doesn't replace the framework decision.

**Asks of Kim:** select Option A, B, A+C, or B+C. The per-(F, Q)
refactor makes Option B particularly tractable (the new F-generic
constructions are 250-310 lines each; a stronger construction would
slot in cleanly).

---

## Wall 2 — `dTildeDim` vertex-type strategy — REMOVED

**Status: still closed.** No regression in wave 59. Ch6 Wall 2 line
remains sorry-free.

---

## Wall 3 — Garnir straightening induction measure — CHAIN IN FLIGHT, FOUR PIVOTS TOTAL

**Context.** `garnir_twisted_in_lower_span`
(`SpechtModuleBasis.lean:1958`, was 1726 in wave 58) — combinatorial
heart of the straightening theorem. Promoted from "wall" to "chain"
in wave 56 with the dominance-induction commitment (PR #2529).

**Wave-59 chain delta (substantial):**

- **Part A** — `garnirColReindex` + sign tracking. **Landed** wave 56
  (PR #2503).
- **Part B** — `garnir_pigeonhole_collapse`. **Landed** wave 56
  (PR #2505).
- **Part C** — residual whole-sum grouping (parent #2499):
  - **C.1** — parent #2519, decomposed into:
    - **C.1.a** — support bound. Main theorem landed wave 56 (PR
      #2536). Helpers:
      - **C.1.a.i** — fibre-coefficient-zero. Landed wave 56 (PR #2544).
      - **C.1.a.ii** — `twistedPolytabloid_pigeonhole_pair`.
        **Issue #2543, has-pr (PR #2550 open, `CONFLICTING`,
        static ~23 days).** No change in wave 59 — repair flow
        has been dispatched every cycle but produced no result.
        The rebase surface has only grown (now over the wave-58
        Schur-Weyl PRs plus wave-59 R2.a + R3-bis additions).
    - **C.1.b** — Leading-tabloid elimination. **Landed** wave 57.
    - **C.1.c** — glue C.1.a + C.1.b. **FOURTH STRATEGIC PIVOT
      this wave.** Wave-58's redesign produced R1 ✅ (PR #2669) +
      R2 (#2667 → escalated to meditate #2676). Wave-59 closed
      #2676 → PR #2687 (Q_high involution analysis); the worker
      result was that R2 needed further decomposition into R2.a +
      R2.b. Wave-59 then:
      - **R2.a** — `twistedPolytabloid_per_q_decomp`. **Landed**
        via PR #2707. Extracts the Q_low ∪ Q_eq contribution via
        IH and isolates the residual Δ.
      - **R2.b** — `twistedPolytabloid_residual_in_V`. **Decomposed**
        this wave (worker session `be98eed5`) into:
        - **R2.b.i** (#2769) — `residual_no_colStd_zero`: the
          combinatorial cancellation involution. Claimed once,
          worker stalled at "region-mapping" step (Step 4 of
          original outline), escalated to **R3-bis meditate
          #2776**. PR #2779 produced
          `progress/r3-bis-residual-cancellation.md` with a
          refined cross-region `φ : (q ∈ eqHi∪high, r=1) ↔ (q ∈
          low∪eq, r ≠ 1)` involution, validated on the running
          example (λ=(2,2), σ=swap(0,1), w=(0 2 1)). #2769 is
          `replan` awaiting a fresh worker.
        - **R2.b.ii** (#2770) — `residual_in_V` assembly via
          inner induction on `srRank`. Filed, blocked on #2769.
      - **R2.c** (#2703) — `garnir_twisted_in_lower_span` final
        assembly via R1 + R2.a + R2.b. Filed, blocked on R2.b.
  - **C.2** — τ classification. **#2520 superseded this wave**;
    its body referenced closed deps (cf. wave-58 doc warning that
    the body would need re-narration after R3 output).
- **Part D** — final assembly closing `garnir_twisted_in_lower_span`.
  Wave-58 issue #2500 superseded this wave; the active issue is
  R2.c (#2703).

**Strategic pivot rationale (wave 59, fourth pivot):** The wave-58
plan committed to Strategy A from `algorithm-A-redesign.md` (per-`q`
dispatch with Q_low / Q_eq / Q_eq' / Q_high regions). The Q_high
involution meditate #2676 → PR #2687 confirmed that Strategy A is
workable but requires a structural split into R2.a (Q_low ∪ Q_eq
extraction via IH) + R2.b (Δ-cancellation on the residual). R2.b
itself splits further: R2.b.i is the pure-combinatorial cancellation,
R2.b.ii is the assembly into V via inner induction. The R3-bis
meditate caught a misformulation in the original R2.b.i statement
(the single-coordinate involution was wrong) and produced a refined
cross-region involution. This is the **fourth** Wall 3 pivot:
1. Per-fibre (wave 56, retired).
2. TP ∈ V^λ first (wave 57, retired).
3. col-std-at-tabloid existence (wave 58, retired).
4. Single-coordinate Q_high involution (wave 59, retired in favor of
   cross-region `(q, r)`-domain involution).

Each retirement was caught by a worker before substantial Lean work
was wasted — the meditate-driven process continues to work.

**Status.** One open PR carry-over (#2550, `CONFLICTING` ~23d). One
fresh strategy doc (`progress/r3-bis-residual-cancellation.md`).
Three issues in the active R2.b → R2.c → final-assembly chain
(#2769 replan, #2770 blocked, #2703 blocked).

**Risk.** Fourth strategic pivot for Wall 3 in four waves. Each
pivot has cost roughly one wave of planner/worker turnover. The
R3-bis cross-region involution has been **validated on the (2,2)
running example** but not on the suggested (3,2) example in §6 of
`r3-bis-residual-cancellation.md`. Recommend the next R2.b.i worker
run the (3,2) enumeration before committing to multi-day Lean work
on the involution. If the cross-region involution fails on (3,2),
Strategy B (Q_eq'-via-cosets) or Strategy C (refactor TP into a
different basis) from `algorithm-A-redesign.md` would be the next
fallback, costing another pivot.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:399`) — the top-of-chain goal
sorry. Wave 55 scoped the chain; wave 58 closed C-3 and most of C-4;
wave 59 closes the C-4a-i sub-β tier in full and lands the C-4c
body, leaving the C-4a aggregation (#2708) as the residual algebraic
obligation plus the γ-cluster as the residual sub-issue.

**Sub-issue progress (wave 59 delta vs wave 58):**

| Sub | Issue | Wave-58 | Wave-59 | Summary |
|-----|-------|---------|---------|---------|
| #1  | #2461 | ✅ merged | ✅ merged | Tensor-degree homogeneity |
| #2a | #2477 | ✅ merged | ✅ merged | Polynomial bridge |
| #2b | #2478 | ✅ merged | ✅ merged | `polynomialRep_embeds_in_tensorPower` |
| #3 A | #2491 | ✅ merged | ✅ merged | L_i FDRep GL_N structure |
| #3 B | #2492 / #2540 | ✅ merged | ✅ merged | Equivariance anchor |
| #3 C-1 | #2580 | ✅ merged | ✅ merged | formalCharacter (∑ Xᵢ)^n |
| #3 C-2 | #2581 | ✅ merged | ✅ merged | Polynomial identity |
| #3 C-2 combined | (none) | ✅ merged | ✅ merged | Combined dimension form |
| #3 C-3 | #2582 | ✅ closed via decomposition | ✅ merged | Irreducibility of `L_i` |
| #3 C-3 wrapper | #2633 | ✅ merged | ✅ merged | `Theorem5_18_4_GL_rep_decomposition_simple` |
| #3 C-4a | #2610 | ✅ merged (decomposed) | ✅ merged (residual sub-γ + aggregation pending) | Image of `c_λ` is simple |
| #3 C-4a-i sub-α | #2655 | ✅ merged | ✅ merged | Block factorization of `c_λ` |
| #3 C-4a-i β.1 | #2682 | claimed | ✅ merged (PR #2689) | A-equivariant trace formula |
| #3 C-4a-i β.2 | #2683 | blocked on #2682 | ✅ merged (PR #2697) | Specht bridge |
| #3 C-4a-i β.3 | #2684 | blocked on #2682+#2683 | ✅ merged (PR #2795) | Off-block assembly |
| #3 C-4a-i sub-γ | #2657 | blocked on #2656 cluster | ✅ closed; replaced by γ.A (PR #2694 CONFLICTING) + γ.B (#2693 replan) | Rank-1 projection |
| #3 C-4a-ii | #2644 | claimed ~6d (possibly stale) | ✅ merged (PR #2698) | Abstract idempotent simplicity |
| #3 C-4b | #2611 | ✅ merged | ✅ merged | Transfer simplicity to GL_N |
| #3 C-4c body | #2612 | blocked on #2644+#2657 | ✅ merged body (PR #2706); aggregation isolated as #2708 | Final `schurModule_isSimple` |
| #3 C-4 aggregation | #2708 | not yet filed | blocked on γ.A (#2694 CONFLICTING) + γ.B (#2693) | NEW sorry at `SchurModuleSimple.lean:148` |
| #3 C  | #2493 | blocked on #2612 | blocked on #2708 | Final `schurWeyl_gl_decomposition` |
| #4  | #2462 | ✅ merged | ✅ merged | `schurPoly_linearIndependent` |
| #5  | #2482 | blocked on #2493 | blocked on #2493 | polynomial GL_N-rep ⊕ Schur modules |
| #6  | #2483 | blocked on #2482 | blocked on #2482 | Final assembly |

**Collateral infra landed this wave:**
- PR #2689: β.1 A-equivariant trace formula.
- PR #2691: review audit PASS (SchurWeylGLTransfer.lean).
- PR #2692: infrastructure for `image_of_primitive_idempotent_isSimple`.
- PR #2697: β.2 Specht bridge (trace identity).
- PR #2698: C-4a-ii body — resolves Module ↥B instance diamond.
- PR #2706: C-4c body via C-4b transfer (introduces #2708 sorry).
- PR #2781: review audit PASS (β.2 + C-4a-ii).
- PR #2785: β.2 section lint cleanup.
- PR #2795: β.3 off-block vanishing assembly.

**Why still not a wall.** The chain remains on schedule even with
γ-cluster sub-issues pending. The C-4a-i sub-β tier closed in full
(β.1 + β.2 + β.3 all landed). C-4a-ii body landed. C-4c body landed
(with aggregation sorry isolated). The only true outstanding work
is:
1. γ.A (PR #2694, CONFLICTING — needs repair).
2. γ.B (#2693, replan — needs a worker to claim).
3. C-4a aggregation (#2708 — mechanical once γ closes).
4. Part C → #5 → #6 (cascade once aggregation closes).

No framework decision needed.

**Remaining sorries on the chain:**
- `iso_of_formalCharacter_eq_schurPoly`
  (`FormalCharacterIso.lean:399`) — closes via #2483.
- `schurModuleSubmodule_isSimple_centralizer`
  (`SchurModuleSimple.lean:148`) — NEW this wave from C-4c
  body closure; closes via #2708.

---

## Active design topic (not a wall) — Ch2 forward bridge per-(F, Q) refactor

**Context.** `not_posdef_not_HasFiniteRepresentationType`
(`Chapter2/Theorem2_1_2.lean:173`). Wave 58 reported this as
blocked on Wall 1; wave 59 partially broke that dependency via the
per-(F, Q) refactor (#2773 + #2774).

**Wave-59 movement:**

- **#2773** — six per-(F, Q) sub-theorems for forbidden subgraphs.
  Three landed in full this wave:
  - `cycle_not_finite_type_per_kQ` ✅ PR #2799 (introduced shared
    `compl_le_forces_eq` infrastructure).
  - `K_{1,4}` D̃₄ F-generic `star_not_finite_type_F` ✅ PR #2798
    (#2796 closed).
  - `etilde7_not_finite_type_per_kQ` ✅ PR #2810 (#2792 closed,
    carries new F-generic Wall 1 stub).

  Three landing in pieces:
  - **D̃₅** (#2790): #2803 construction ← PR #2813 (just opened,
    MERGEABLE) + #2804 indecomposability blocked.
  - **Ẽ₆** (#2791 closed): #2806 construction ✅ PR #2808 + #2807
    indecomposability ✅ PR #2809 (carries new F-generic Wall 1
    stub).
  - **K_{1,4} Q-extension** (#2797): #2800 construction ← PR #2802
    (CONFLICTING) + #2801 indecomposability blocked.

  Two still untriaged:
  - **K_{1,4} canonical** (#2789): `replan`.
  - **T(1,2,5)** (#2793): `replan`.

- **#2774** — Ch2 assembly. **Deliverable 1 landed via PR #2805**
  (per-(F, Q) subgraph transfer). #2774 is `replan` for re-scoping
  deliverables 2 + 3 (final per-quiver classification + close of
  Theorem 2.1.2 forward).

**Net effect on line 173:** The forward bridge is **structurally
closer** to closure than wave 58. The assembly pattern is concrete
(deliverable 1 demonstrates it works). But it transitively still
depends on each per-(F, Q) sub-theorem's `IsIndecomposable` step,
two of which (Ẽ₆ at `FieldGenericETilde6.lean:283`, Ẽ₇ at
`FieldGenericETilde7.lean:292`) carry the new F-generic Wall 1
stubs. End-to-end closure of line 173 is still gated on Wall 1.

---

## Meta

- **Wall 1** still needs Kim's framework decision (#2436); fifth
  consecutive wave with no movement. Refactored from 3 ℂ-specific
  sorries to 3 dead ℂ-specific + 2 live F-generic = 5 sorries
  total; 2 are on the active per-(F, Q) chain.
- **Wall 2** is closed. No further design needed.
- **Wall 3** is a chain with **four strategic pivots** since wave 56.
  R2.a (#2707) + R3-bis meditate (#2779) landed this wave. R2.b.i
  (#2769) is `replan` with a concrete cross-region involution
  strategy validated on the (2,2) example. R2.b.ii (#2770) +
  R2.c (#2703) filed and blocked. Final assembly (line 1958)
  still 3 PRs from closure.
- **Schur-Weyl chain** advanced significantly: β.1/β.2/β.3 all
  landed, C-4a-ii body landed, C-4c body landed. Residual
  γ-cluster (γ.A PR #2694 CONFLICTING, γ.B #2693 replan) plus
  C-4a aggregation (#2708 blocked on γ-cluster). 4 PRs from
  closure of line 399.
- **Ch2 forward bridge** partially unblocked. #2774 deliverable 1
  landed (PR #2805); deliverables 2 + 3 await re-scoping. Three
  per-(F, Q) sub-theorems landed in full; three in flight; two
  untriaged. End-to-end closure of line 173 still gated on
  Wall 1 via the F-generic Ẽ₆/Ẽ₇ stubs.

**For comparison with wave 58:** wave-58 had 1 wall (Wall 1,
human-gated, 4 waves stale) + 1 active chain (Wall 3, three
pivots, in-flight meditate) + 1 ongoing chain (Schur-Weyl, C-3
closed, C-4 well-decomposed). Wave-59 has the same structural shape
plus **one new active topic** (Ch2 forward bridge per-(F, Q)
refactor): **1 wall** (Wall 1, restructured, 5 waves stale) + **1
active chain** (Wall 3, four pivots, R3-bis just landed) + **1
ongoing chain** (Schur-Weyl, C-4 closed body/aggregation isolated)
+ **1 new active topic** (Ch2 forward bridge half-landed via
per-(F, Q) refactor). The wave-59 distinguishing event is the
**Theorem 2.1.2 forward-bridge unblock via per-(F, Q) refactor**
(PRs #2773, #2774, #2796 → #2798/#2799/#2805/#2808/#2809/#2810
plus PRs in flight). Net sorry count rose 7 → 10 for the first
time since wave 50; the rise reflects structural decomposition,
not regression.
