# Backlog Tractability Assessment (Issue #1013)

## Overview

Assessed 23 uncovered items (21 `statement_formalized` + 2 `attention_needed`) that lack
existing feature issues. Classified each by tractability and mapped dependency chains.

---

## Tractability Classifications

### HIGH — Mechanical or clear path, 1-2 sorries, standard APIs

| Item | Sorries | Rationale |
|------|---------|-----------|
| **Proposition5.25.1** (GL₂ commutator) | 1 | Self-contained classical group theory. No sorry'd deps. Show det([x,y])=1 then SL₂ ⊆ [G,G] via transvections. Already has issue #980 (claimed). |
| **Corollary5.26.3** (chars from cyclic subgroups) | 2 | Direct application of Theorem5.26.1 to cyclic subgroups. Proof strategy is clear: cyclic subgroups form conjugation-invariant cover. |

### MEDIUM — Substantive but clear path, may need exploration

| Item | Sorries | Rationale |
|------|---------|-----------|
| **Theorem5.26.1** (Artin's theorem) | 1 | Deep but self-contained. `inducedCharacter` fully defined. No sorry'd deps. Needs character theory + induction machinery. Already has issue #1017. |
| **Theorem5.18.2** (centralizer = U(gl) image) | 4 | Lie bracket map properties need work. Locally scoped, no external blockers. Already has infra issue #1011 (claimed). |
| **Theorem_Dynkin_classification** | 1 | Finite case analysis (A_n, D_n, E₆₇₈). Adjacency matrices defined explicitly. Needs positive-definiteness verification per type. |
| **Theorem6.8.1** (reaching simple roots) | 1 | Prop 6.6.5 is sorry-free. Mathematical proof strategy outlined in comments. Needs careful work with reflection functors + root systems. Already has issue #1015. |
| **Problem6.9.1** (Q₂ classification) | 3 | Part c already complete. Parts a/b need Jordan block definitions. Main classification is straightforward finrank constraint. |

### LOW — Blocked on infrastructure, deep math, or missing Mathlib

| Item | Sorries | Rationale |
|------|---------|-----------|
| **Theorem5.18.4** (Schur-Weyl duality) | 3 | All definitions complete but proofs need centralizer theory, semisimplicity, and Specht decomposition. No external blockers but very deep math. |
| **Proposition5.19.1** (GL(V) span = centralizer) | 1 | Requires Zariski-density argument (polynomial density of GL in End). Advanced algebraic geometry not in Mathlib. |
| **Theorem5.25.2** (principal series irreducibility) | 8 | Three core definitions (principalSeries, detChar, complementW) are all sorry'd. Must define induced representations from Borel subgroup first. |
| **Lemma5.25.3** (complementary series character) | 3 | Needs ellipticSubgroup definition (finite field embedding). Virtual character formula requires three component representations. |
| **Theorem5.27.1** (orbit method) | 1 | Orbit method classification not in Mathlib. Requires dual G-action, orbit enumeration, stabilizer computation. Sophisticated. |
| **Proposition5.22.2** (determinant twist) | 2 | `detRep` and `SchurModule` are sorry'd. Depends on Theorem5.22.1 chain. Already has issue #1016. |
| **Proposition6.6.7** (reflection preserves indecomp.) | 2 | Sink case mostly done but blocked on dependent type issues with `Decidable.rec`. Source case blocked on Definition6.6.4 sorry status (actually sorry-free — needs re-check). |
| **Theorem5.15.1** (Frobenius character formula) | 4 | Blocked on `cycleTypeHsymmProduct` from Theorem5.14.3 (1 sorry). Cannot proceed until upstream is proven. |
| **Lemma5.18.3** (symmetric power span) | sorry'd | Has issue #974 (claimed). |

### BLOCKED — Confirmed blocker, cannot proceed

| Item | Sorries | Rationale |
|------|---------|-----------|
| **Theorem2.1.2** (Gabriel's theorem) | 1 | Capstone theorem. Requires ALL of Ch5-6 infrastructure (reflection functors, root systems, Dynkin classification). |
| **Problem6.1.5_theorem** (Gabriel restated) | 2 | `IsFiniteTypeQuiver` is placeholder. Needs indecomposable rep infrastructure not yet present. |
| **Corollary5.19.2** (Schur-Weyl decomposition) | 1 | Depends on Theorem5.18.4 (all 3 parts sorry'd). Cannot start until upstream complete. |
| **Proposition5.21.1** (character expansion in Schur polys) | 4 | `schurPoly` definition is sorry'd. Needs Murnaghan-Nakayama rule (not in Mathlib). |
| **Theorem5.22.1** (Weyl character formula) | 3 | Depends on Prop5.21.1's `schurPoly`. Blocked by entire upstream chain. |
| **Theorem5.23.2** (complete reducibility + Peter-Weyl) | 8+ | `AlgIrrepGL` skeleton definitions. Depends on entire upstream chain (5.22.1 → 5.21.1). |
| **Corollary6.8.3** (dim vector determines indecomp.) | 1 | Depends on Theorem6.8.1 (unproven). |
| **Corollary6.8.4** (every positive root realized) | 1 | Depends on Theorem6.8.1 (unproven). |

---

## Dependency Chains

### Chain 1: Schur-Weyl → GL(V) Representation Theory (Ch5, 7 items)

```
Theorem5.18.4 (Schur-Weyl duality, 3 sorries)
  └→ Proposition5.19.1 (GL(V) span = centralizer)
  └→ Corollary5.19.2 (Schur-Weyl decomposition)
      └→ Proposition5.21.1 (character expansion, needs schurPoly)
          └→ Theorem5.22.1 (Weyl character formula)
              └→ Proposition5.22.2 (determinant twist)
              └→ Theorem5.23.2 (complete reducibility + Peter-Weyl)
```

**Bottleneck**: Theorem5.18.4. Unblocking it enables the entire GL(V) chain.
**Secondary bottleneck**: Prop5.21.1 needs Schur polynomial definition (not in Mathlib).

### Chain 2: Reflection Functors → Gabriel's Theorem (Ch6, 5 items)

```
Proposition6.6.6 (reflection functor invertibility, 2 sorries)
  └→ Proposition6.6.7 (reflection preserves indecomposability)
Theorem6.8.1 (reaching simple roots via reflections)
  └→ Corollary6.8.3 (dim vector determines indecomp.)
  └→ Corollary6.8.4 (every positive root realized)
      └→ Theorem2.1.2 / Problem6.1.5_theorem (Gabriel's theorem)
```

**Bottleneck**: Theorem6.8.1. Already has issue #1015.
**Note**: Prop6.6.5 and Def6.6.4 are sorry-free, so Theorem6.8.1 can be attempted now.

### Chain 3: Character Theory (Ch5, 3 items)

```
Theorem5.26.1 (Artin's theorem) — independent
  └→ Corollary5.26.3 (characters from cyclic subgroups)
Theorem5.14.3 (1 sorry) → Theorem5.15.1 (Frobenius character formula)
```

**Note**: Theorem5.26.1 is independent with no sorry'd deps. Good candidate.

### Chain 4: Independent Items (no downstream dependents)

- Theorem_Dynkin_classification (standalone classification)
- Problem6.9.1 (Q₂ classification, part c already done)
- Theorem5.27.1 (orbit method, standalone)
- Proposition5.25.1 (already has issue #980)
- Theorem5.25.2 + Lemma5.25.3 (principal series, self-contained cluster)

---

## Priority Recommendations for Planners

### Tier 1: Create issues immediately (HIGH/MEDIUM, high impact)

1. **Corollary5.26.3** — HIGH success rate, depends only on Theorem5.26.1 (already issued as #1017). Create after #1017 completes.
2. **Theorem_Dynkin_classification** — MEDIUM, finite case analysis. No dependencies. Standalone win for Ch6.
3. **Problem6.9.1 parts a/b** — MEDIUM, part c already done. Needs Jordan block definitions.

### Tier 2: Worth attempting (MEDIUM, moderate impact)

4. **Proposition6.6.7** — Re-assess: Definition6.6.4 is actually sorry-free. Sink case is mostly done. Dependent type issue is the main blocker but may be solvable.
5. **Theorem5.18.4** — No external blockers but very deep math. This is the highest-impact item if solved (unlocks 6+ downstream items). Consider splitting into sub-issues per sorry.

### Tier 3: Defer (LOW/BLOCKED)

6. **Proposition5.19.1** — Needs Zariski density. Skip unless Mathlib adds this.
7. **Proposition5.21.1** — Needs Schur polynomial infrastructure. Consider defining schurPoly first as separate issue.
8. **Theorem5.25.2 cluster** — Too many sorry'd definitions to be tractable now.
9. **Theorem5.27.1** — Orbit method not in Mathlib. Low priority.
10. **All BLOCKED items** — Wait for upstream dependencies.

### Infrastructure-first items

- **Theorem5.14.3** (1 sorry, upstream of Theorem5.15.1) — Not in uncovered list but worth proving to unblock 5.15.1.
- **Proposition6.6.6** (2 sorries, upstream of Prop6.6.7) — Proving this unblocks reflection preserves indecomposability.

---

## Status Corrections for items.json

1. **Problem6.9.1**: Part c (`Problem6_9_1c`) has a full proof — the item is partially sorry-free. Status should note partial completion.
2. **Proposition6.6.7**: Partially proved (sink helpers complete, main sink case mostly done). `attention_needed` is correct.
3. **Theorem5.18.4**: 3 sorries but all definitions complete. `attention_needed` is correct — the blocker is proof complexity, not formalization.
