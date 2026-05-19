# Review: D2 wrapper trilogy — per-(F, Q) wrappers from wave 62

**Verdicts** (one row per (deliverable, wrapper); D5 combined):

| Deliverable | D2.cycle (#2897) | D2.adjacent (#2900) | D2.single (#2903) |
|---|---|---|---|
| D1 — Statement fidelity | PASS | PASS | PASS |
| D2 — `[IsAlgClosed F]` decision | PASS (correct to omit) | PASS (correct to carry) | PASS (correct to carry) |
| D3 — Proof body fidelity | PASS | PASS | PASS (wrapper portion) |
| D4 — Outer-assembly call site | PASS | PASS | PASS |
| D5 — Cross-wrapper uniformity | PASS (3 + 1 wrappers consistent) | | |

No code changes recommended. The `[IsAlgClosed F]` divergence on the
cycle wrapper is the **correct** design — it matches the precedent's
"a wrapper carries `[IsAlgClosed F]` iff any dispatch leaf does" rule.

- Issue: #2934 (this audit)
- PRs audited: #2897 / #2900 / #2903 (wave 62)
- Files touched: `FieldGenericCycle.lean:440`, `FieldGenericD5Tilde.lean:1043`,
  `FieldGenericTpqr.lean:1408`, with cross-check at `FieldGenericAssembly.lean`
- Precedent: `progress/reviews/2026-05-18-degree4-per-kQ-placement.md`
  (PR #2891 = #2892 closure)
- Session: `ce0a605d`

## Build state at audit time

`lake build EtingofRepresentationTheory.Chapter6.FieldGenericAssembly`
passes at **8047 / 8047 jobs** on `main` (commit `729a10b`). Two
`declaration uses sorry` warnings are pre-existing:

- `FieldGenericTpqr.lean:1233` — `single_branch_leaf_case_both_extend_per_kQ`
  API stub (PR #2906 partial; follow-up tracked)
- `FieldGenericAssembly.lean:64` — `non_adjacent_branches_infinite_type_per_kQ`
  API stub (issue #2919 / #2923 in flight)

Both are outside the audit scope. Raw sorry count `Chapter6/`: **16 lines**
across 11 files (unchanged from the previous review session).

## D1 — Statement fidelity (PASS on all three wrappers)

Per-wrapper row-by-row diff vs. the universal `_kQ`-free originals.

### D2.cycle — `graph_with_list_cycle_infinite_type_per_kQ`

`Chapter6/FieldGenericCycle.lean:440-459` vs. universal
`Chapter6/InfiniteTypeConstructions.lean:3910-3921`.

| Aspect | universal | per-(F, Q) |
|---|---|---|
| `adj, hsymm, hdiag, h01` | identical | identical |
| `cycle, hlen, hnodup, hedge, hclose` | identical | identical |
| field args | — | `(F : Type) [Field F]` — **no** `[IsAlgClosed F]` |
| quiver args | — | `(Q : @Quiver.{0,0} (Fin n)) [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]` |
| orientation arg | — | `(hOrient : @Etingof.IsOrientationOf n Q adj)` |
| conclusion | `¬ IsFiniteTypeQuiver n adj` | canonical per-(F, Q) `¬ Set.Finite { d \| ∃ V, V.IsIndecomposable ∧ … }` |

No subgraph-specific hypothesis was reshaped: cycle data is passed
unchanged, including the slightly-awkward `cycle.get ⟨cycle.length - 1, _⟩`
form of `hclose` (preserved verbatim from the original to keep
call-site call-shape stable).

### D2.adjacent — `adjacent_branches_infinite_type_per_kQ`

`Chapter6/FieldGenericD5Tilde.lean:1043-1062` vs. universal
`Chapter6/InfiniteTypeConstructions.lean:4764-4775`.

| Aspect | universal | per-(F, Q) |
|---|---|---|
| `adj, hsymm, hdiag, h01` | identical | identical |
| `h_acyclic` | identical | identical |
| `v₀, w, hv₀_deg, hw_deg, hvw_adj` | identical | identical |
| field args | — | `(F : Type) [Field F] [IsAlgClosed F]` |
| quiver args | — | added (standard form) |
| orientation arg | — | added (standard form) |
| conclusion | universal | canonical per-(F, Q) |

The `set_option maxHeartbeats 3200000 in` declaration prefix
(`FieldGenericD5Tilde.lean:1029`) is preserved with the same rationale
(15 distinctness facts plus the 36-case `fin_cases` adjacency proof),
mirroring `InfiniteTypeConstructions.lean:4760` exactly.

### D2.single — `single_branch_not_posdef_infinite_type_per_kQ`

`Chapter6/FieldGenericTpqr.lean:1408-1434` vs. universal
`Chapter6/InfiniteTypeConstructions.lean:8401-8419`.

| Aspect | universal | per-(F, Q) |
|---|---|---|
| `adj, hn, hsymm, hdiag, h01` | identical | identical |
| `hconn, h_acyclic` | identical | identical |
| `h_deg, v₀, hv₀, h_unique, h_not_posdef` | identical | identical |
| field args | — | `(F : Type) [Field F] [IsAlgClosed F]` |
| quiver args | — | added (standard form) |
| orientation arg | — | added (standard form) |
| conclusion | universal | canonical per-(F, Q) |

The `set_option maxHeartbeats 3200000 in` declaration prefix
(`FieldGenericTpqr.lean:1393`) is preserved with the same rationale
(~30 distinctness facts plus the 49-case `fin_cases` Ẽ₆ embedding),
mirroring `InfiniteTypeConstructions.lean:8392`.

The leaf-case stub call (`single_branch_leaf_case_per_kQ`,
`FieldGenericTpqr.lean:1706-1707` and twin calls) takes the same
argument shape as the universal `single_branch_leaf_case` and is the
correct delegation target. The leaf-case body itself is out of scope
for this audit (tracked by #2904 / #2906).

## D2 — `[IsAlgClosed F]` carriage decision (PASS — cycle correctly omits)

The "open anomaly" in the planner's issue body resolves to a **PASS**:
the cycle wrapper correctly omits `[IsAlgClosed F]`. Rationale follows
from body inspection, not signature staring.

### Cycle wrapper dispatch chain

The body of `graph_with_list_cycle_infinite_type_per_kQ` only calls:

1. The strong-induction hypothesis `ih` (same per-(F, Q) shape — no
   `[IsAlgClosed F]`), at `FieldGenericCycle.lean:523`.
2. `subgraph_infinite_type_transfer_per_kQ` at
   `FieldGenericCycle.lean:593`. Signature at
   `FieldGenericInfiniteType.lean:374-384`: takes
   `(F : Type) [Field F] (Q : …) [Subsingleton …]` — **no**
   `[IsAlgClosed F]`.
3. `cycle_not_finite_type_per_kQ` at `FieldGenericCycle.lean:594`.
   Signature at `FieldGenericCycle.lean:326-330`: takes
   `(F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k) (Q : …) [Subsingleton …]
    (hOrient : @Etingof.IsOrientationOf k Q (cycleAdj k hk))` — **no**
   `[IsAlgClosed F]`.

`grep -n` in `FieldGenericCycle.lean` confirms the entire cycle stack
(`cycleAdj`, `cycleRep_kQ`, `cycleRep_kQ_isIndecomposable`,
`cycleRep_kQ_dimVec`, `chordless_cycle_infinite_type_per_kQ`,
`triangle_infinite_type_per_kQ`) is in the field-only regime — none
introduces a `haveI [IsAlgClosed F]` mid-proof.

### Caller side

The cycle wrapper is called exactly once from the per-(F, Q) chain, at
`FieldGenericAssembly.lean:215-216`:

```lean
exact graph_with_list_cycle_infinite_type_per_kQ adj hsymm hdiag h01
  cycle hlen hnodup hedges hclose' F Q hOrient
```

The enclosing theorem `not_posdef_infinite_type_per_kQ`
(`FieldGenericAssembly.lean:177`) does carry `[IsAlgClosed F]`, but the
call site does **not** supply or rely on it for the cycle dispatch —
the three explicit args `F Q hOrient` exactly match the wrapper's
signature. No implicit `[IsAlgClosed F]` is "dangling".

### Decision recorded

The cycle wrapper correctly **omits** `[IsAlgClosed F]`. This matches
the precedent rule from PR #2894 ("a wrapper carries `[IsAlgClosed F]`
iff any of its dispatch leaves does"): the cycle dispatch path goes
through `cycle_not_finite_type_per_kQ` only (via
`subgraph_infinite_type_transfer_per_kQ`), and the cycle
representations are constructed by polynomial actions on
`Fin (m+1) → F` — pure linear algebra over an arbitrary field.

The precedent's table predicted this exact outcome (D2.cycle row:
"dispatches to `chordless_cycle_*_per_kQ` → **no** `[IsAlgClosed F]`").
This audit confirms the prediction held.

**Precedent for future D2 / D3 sub-wrappers**: when a wrapper's
dispatch chain is entirely in `FieldGenericCycle.lean` (or otherwise
avoids the Ẽ_n / D̃_n / Star / T₁₂₅ family), it should likewise omit
`[IsAlgClosed F]`. Asymmetry vs. the rest of the per-(F, Q) leaf API
is the signal, not the bug.

## D3 — Proof body fidelity (PASS on all three wrappers)

### D2.cycle

Strong induction on cycle length is preserved verbatim
(`Nat.strongRecOn` + the inner `key` lemma quantifying over all cycles
of length `m`). Chord case: identical sub-cycle extraction
(`(cyc.drop p.val).take (q.val - p.val + 1)`), same `hsublen` / `hsublt`
arithmetic, same `hsubget` / `hsub_nodup` / `hsub_edge` / `hsub_close`
helpers, same recursive `ih` call. Chordless case: identical
embedding `φ : Fin m ↪ Fin n` and identical `hembed` adjacency-equality
proof (the `split_ifs` + `Nat.mod_eq_of_lt` + `convert` cascade is
copied line-for-line). The induction motive on `key` is the per-(F, Q)
`¬ Set.Finite { d | … }` shape — **not** the universal
`¬ IsFiniteTypeQuiver`, as required.

Final dispatch (chordless leaf):

| variant | call |
|---|---|
| universal | `subgraph_infinite_type_transfer φ adj (cycleAdj m hm) hsymm (fun v h => by linarith [hdiag v]) hembed (cycle_not_finite_type m hm)` |
| per-(F, Q) | `subgraph_infinite_type_transfer_per_kQ φ F Q (cycle_not_finite_type_per_kQ F m hm (restrictOrientationViaEmb φ Q) (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))` |

The per-(F, Q) leaf threads the orientation through the
`restrictOrientationViaEmb` / `restrictOrientationViaEmb_isOrientationOf`
pair — same machinery already used by
`chordless_cycle_infinite_type_per_kQ` (`FieldGenericCycle.lean:388-390`)
and `triangle_infinite_type_per_kQ` (line ≈420). No new infrastructure
introduced for this wrapper.

### D2.adjacent

Neighbour extraction (`set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1)`,
`hS₀_card`, `Finset.card_eq_two.mp …`, `Equiv` construction) is copied
verbatim from `InfiniteTypeConstructions.lean:4782-4795`. The full
distinctness cascade (`hu₁_ne_v₀`, `hw₁_ne_w`, …, `path_nodup`,
`path_edges`, `hu_w` non-edges via `acyclic_no_triangle` /
`acyclic_path_nonadj`) is copied verbatim, line for line, lines
`FieldGenericD5Tilde.lean:1063-1190` matching
`InfiniteTypeConstructions.lean:4776-4912`. The `Fin 6 ↪ Fin n`
embedding match (six `match | ⟨0,_⟩ => u₁ | …`) and the 36-case
`fin_cases i <;> fin_cases j` adjacency proof
(`hembed : ∀ i j, d5tildeAdj i j = adj (φ i) (φ j)`) are byte-identical.

Final dispatch:

| variant | call |
|---|---|
| universal | `subgraph_infinite_type_transfer φ adj d5tildeAdj hsymm (fun v h => by linarith [hdiag v]) hembed d5tilde_not_finite_type` |
| per-(F, Q) | `subgraph_infinite_type_transfer_per_kQ φ F Q (d5tilde_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q) (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))` |

`F, Q, hOrient` are threaded consistently; no fresh `haveI` synthesised.

### D2.single

Three-level `by_cases` on `2 ≤ vertexDegree adj aᵢ` for `i ∈ {1, 2, 3}`
(`FieldGenericTpqr.lean:1467-1469`) reproduces the universal
case-split at `InfiniteTypeConstructions.lean:8455-8457`. The
all-extend (Ẽ₆) branch builds the same `Fin 7 ↪ Fin n` embedding from
`v₀, a₁, b₁, a₂, b₂, a₃, b₃`, with the same 7² = 49 `fin_cases`
adjacency match against `etilde6Adj`. The leaf branches each delegate
to `single_branch_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn
h_acyclic h_deg v₀ hv₀ h_unique h_not_posdef aᵢ haᵢ_adj haᵢ_deg1 F Q
hOrient` — same argument shape as the universal
`single_branch_leaf_case ... aᵢ haᵢ_adj haᵢ_deg1` modulo the appended
`F Q hOrient`.

Final dispatch (Ẽ₆):

| variant | call |
|---|---|
| universal | `subgraph_infinite_type_transfer φ adj etilde6Adj hsymm (fun v h => by linarith [hdiag v]) hembed etilde6_not_finite_type` |
| per-(F, Q) | `subgraph_infinite_type_transfer_per_kQ φ F Q (etilde6_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q) (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))` |

`single_branch_leaf_case_per_kQ` itself contains a downstream `sorry`
(`single_branch_leaf_case_both_extend_per_kQ`, `FieldGenericTpqr.lean:1286`),
but the wrapper-portion proof is structurally complete and correctly
parallel to the universal. Leaf-body audit is tracked separately by
#2935 + the #2904 / #2906 chain.

## D4 — Outer-assembly call sites (PASS on all three wrappers)

Universal dispatcher is split into two layers:

- `acyclic_branch_not_posdef_infinite_type` (universal helper, ≈ line 10605)
  → adjacent / single / non-adjacent branch-point sub-dispatch
- `not_posdef_infinite_type` (`InfiniteTypeConstructions.lean:10661`)
  → degree-4 / cycle / branch / path

The per-(F, Q) mirror is two parallel theorems in
`FieldGenericAssembly.lean`:

- `acyclic_branch_not_posdef_infinite_type_per_kQ` (line 113)
- `not_posdef_infinite_type_per_kQ` (line 177)

Call-site verification:

### D2.cycle call

`FieldGenericAssembly.lean:215-216`:
```lean
exact graph_with_list_cycle_infinite_type_per_kQ adj hsymm hdiag h01
  cycle hlen hnodup hedges hclose' F Q hOrient
```

Universal counterpart (`InfiniteTypeConstructions.lean:10692-10693`):
```lean
exact graph_with_list_cycle_infinite_type adj hsymm hdiag h01
  cycle hlen hnodup hedges hclose'
```

Argument positions match exactly modulo the appended `F Q hOrient`.
The surrounding `not_posdef_infinite_type_per_kQ` *does* have
`[IsAlgClosed F]` in scope, but the call site does not introduce it —
no `haveI`, no `(_ : IsAlgClosed F)` placeholder. Clean.

### D2.adjacent call

`FieldGenericAssembly.lean:144-145`:
```lean
exact adjacent_branches_infinite_type_per_kQ adj hsymm hdiag h01 h_acyclic
  v₀ w hv₀ hw_deg hw_adj F Q hOrient
```

Universal counterpart (`InfiniteTypeConstructions.lean:10633`):
```lean
exact adjacent_branches_infinite_type adj hsymm hdiag h01 h_acyclic v₀ w hv₀ hw_deg hw_adj
```

Match modulo the appended `F Q hOrient`. `[IsAlgClosed F]` is correctly
threaded through implicitly from the enclosing
`acyclic_branch_not_posdef_infinite_type_per_kQ` signature
(`FieldGenericAssembly.lean:131`).

### D2.single call

`FieldGenericAssembly.lean:155-156`:
```lean
exact single_branch_not_posdef_infinite_type_per_kQ adj hn hsymm hdiag h01
  hconn h_acyclic h_deg v₀ hv₀ h_unique h_not_posdef F Q hOrient
```

Universal counterpart (`InfiniteTypeConstructions.lean:10643-10644`):
```lean
exact single_branch_not_posdef_infinite_type adj hn hsymm hdiag h01 hconn
  h_acyclic h_deg v₀ hv₀ h_unique h_not_posdef
```

Match modulo the appended `F Q hOrient`. Same `[IsAlgClosed F]`
threading from the enclosing signature.

No call site silently introduces a fresh hypothesis that should have
been threaded through the wrapper.

## D5 — Cross-wrapper signature uniformity (PASS)

Comparing the four D2 wrappers (the trilogy in this audit + the
previously-audited D2.degree4) by extracting their declaration heads.

### Conclusion form — byte-identical across all four

```lean
¬ Set.Finite
  {d : Fin n → ℕ |
    ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
      V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))}
```

Verified at `FieldGenericStar.lean:649-662` (degree4),
`FieldGenericCycle.lean:440-459` (cycle),
`FieldGenericD5Tilde.lean:1043-1062` (adjacent),
`FieldGenericTpqr.lean:1408-1434` (single). All match.

### Field / quiver / orientation carriage — consistent placement

All four wrappers append the per-(F, Q) data at the **end** of the
explicit argument list, in the exact order

```lean
(F : Type) [Field F] (_? [IsAlgClosed F])?
(Q : @Quiver.{0, 0} (Fin n))
[∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
(hOrient : @Etingof.IsOrientationOf n Q adj)
```

`[IsAlgClosed F]` is present iff the dispatch leaf needs it:

| wrapper | dispatch leaf | `[IsAlgClosed F]`? | confirmed |
|---|---|---|---|
| D2.degree4 (PR #2891) | `star_subgraph_*` + `triangle_*` | yes | ✓ (precedent) |
| D2.cycle (PR #2897) | `cycle_*` only | **no** | ✓ (this audit) |
| D2.adjacent (PR #2900) | `d5tilde_*` | yes | ✓ (this audit) |
| D2.single (PR #2903) | `etilde6_*` (+ leaf-case → `etilde7_*` / `t125_*`) | yes | ✓ (this audit) |

Pattern is consistent.

### Variable naming — uniform

All four wrappers use `F, Q, hOrient` — never `K`, never `quiv`, never
`hOrient'`. The `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
CategoryTheory.ReflQuiver.toQuiver in` declaration prefix is present on
all four (required at every `_per_kQ` wrapper to suppress the
category-theory quiver instance synthesised from `Field F`).

## Audit precedent summary

This is the 6th wave-61/62 audit in the per-(F, Q) wrapper series
(after #2861, #2866, #2879, #2885, #2892). All PASS, no defects. The
per-(F, Q) recipe — append `(F, [Field], optional [IsAlgClosed], Q,
[Subsingleton hom], hOrient)`, swap leaf names to `_per_kQ`, thread
orientation through `restrictOrientationViaEmb` — is stable. Wave-62
PRs that landed via this recipe (#2897, #2900, #2903) followed it
without deviation.

Recommended adjustment to audit cadence for the remaining D2 / D3
work: the recipe-conformance dimension can be deprecated as a primary
deliverable (it has reached saturation). Future audits should focus on
the `_per_kQ` body of the wave-62 partials (#2906, #2914, #2916,
#2932) where the proof body is itself novel and recipe-conformance is
less relevant.

## No code changes

This audit recommends **no edits to `main`**. Sorry-count delta: **0**.
