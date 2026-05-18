# Review: `single_branch_leaf_both_extend_t122_per_kQ` — T(1,2,2) = D₅ posdef contradiction (per-(F, Q))

**Verdict: PASS** on all five deliverables. No code changes recommended.
No follow-up issues filed.

- Audit target: `Chapter6/FieldGenericTpqr.lean:64-491` —
  `single_branch_leaf_both_extend_t122_per_kQ` (introduced by PR #2912,
  merge commit `ca2ce6e`).
- Universal reference: `Chapter6/InfiniteTypeConstructions.lean:7964-8352`
  — the inline T(1, 2, 2) = D₅ positive-definiteness contradiction inside
  `single_branch_leaf_case` (`InfiniteTypeConstructions.lean:6901`).
- Issue: #2935 (this audit).
- Reviewed at `main` = `729a10b` (PR #2912 merged in wave 62; helper is
  on `main` but has no call site yet — dispatcher closure in #2905 chain
  remains open).
- Session: `58d864dc`.

The per-(F, Q) helper is a faithful port of the universal proof,
modulo three principled and well-scoped divergences (each detailed
below): (i) carriage hypothesis prelude for `F, Q, hOrient`; (ii)
inline derivation of `adj_comm, ne_of_adj', hleaf_ne_v₀, ha₂_ne_v₀,
ha₃_ne_v₀` (these are outer-scope facts in the universal proof, so the
helper must reconstruct them locally); (iii) the LHS of the
quadratic-form equation is the spelled-out `dotProduct x ((2 • 1 -
adj).mulVec x)` rather than the `QF adj x` abbreviation (because `QF`
is `private abbrev` in `InfiniteTypeConstructions.lean:4131` and is
not exported across the module boundary).

## D1 — Signature fidelity (PASS)

Side-by-side against the implicit signature implied by the universal's
context at line 7964 (the case-split entry):

| Parameter group | Universal context (lines 6901-7964) | Per-(F, Q) helper (lines 64-100) |
|---|---|---|
| Implicit arity | `{n : ℕ}` (6901) | identical (64) ✓ |
| Adjacency matrix | `(adj : Matrix (Fin n) (Fin n) ℤ)` (6902) | identical (65) ✓ |
| Symmetry / diagonal / 0-1 | `hsymm, hdiag, h01` (6903-6905) | identical (66-68) ✓ |
| Connectivity | `hconn : ∀ i j, ∃ path, …` (6906-6909) | identical (69-72) ✓ |
| Acyclicity | `h_acyclic : ∀ cycle, …` (6910-6914) | identical (73-77) ✓ |
| Six named vertices | `v₀, leaf, a₂, a₃, b₂, b₃` (6916, 6920, 6932, 6959, 6966) | `v₀ leaf a₂ a₃ b₂ b₃` (78) ✓ |
| Adjacencies | `h_leaf_adj, ha₂_adj, ha₃_adj, hb₂_adj, hb₃_adj` (6920, 6937, 6939, 6963, 6970) | identical (79-81) ✓ |
| Degree hypotheses | `h_leaf_deg : … = 1` (6921); `hb₂_deg1` derived at 7642; `hb₃_deg1` derived at 7968 | `h_leaf_deg, hb₂_deg1, hb₃_deg1` all hoisted to hypotheses (82-84) ✓ |
| Distinctness | `ha₂₃` (6932); `ha₂_ne_leaf, ha₃_ne_leaf` (6941-6942); `hb₂_ne_v₀` (6965); `hb₃_ne_v₀` (6972) | `ha₂₃, ha₂_ne_leaf, ha₃_ne_leaf, hb₂_ne_v₀, hb₃_ne_v₀` (85-87) ✓ |
| Finset equalities | `hS₀_eq : S₀.erase leaf = {a₂, a₃}` (6932); `hb₂_eq` (6959); `hb₃_eq` (6966) | `hS₀_eq : (Finset.univ.filter (adj v₀ · = 1)).erase leaf = {a₂, a₃}` (88); `hb₂_eq` (89); `hb₃_eq` (90) — `S₀` inlined ✓ |
| Non-posdef | `h_not_posdef` (6918-6919) | identical (91-92) ✓ |

`S₀` inlining: the universal proof uses `set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1)` at line 6930, so `hS₀_eq` reads as `S₀.erase leaf = {a₂, a₃}`. The per-(F, Q) port spells out the underlying form `(Finset.univ.filter (adj v₀ · = 1)).erase leaf = {a₂, a₃}` (88) — definitionally equal, no semantic difference. The two `hb*_eq` hypotheses are likewise spelled out.

Degree hypotheses hoisted: the universal proof derives `hb₂_deg1` from `h_deg_le2 b₂ hb₂_ne_v₀` plus `¬h_b2_ext` (line 7642), and `hb₃_deg1` from `h_deg_le2 b₃ hb₃_ne_v₀` plus `¬h_b3_ext'` (line 7968). The per-(F, Q) helper has no access to `h_deg_le2` (it would require `h_unique` and `h_deg`, neither of which is carried by the helper), so both must come in as hypotheses. The dispatcher (eventually `single_branch_leaf_both_extend_per_kQ`) discharges them at the call site. No degree hypothesis silently dropped.

Per-(F, Q) appends the standard carriage at lines 93-96:

```lean
(F : Type) [Field F] [IsAlgClosed F]
(Q : @Quiver.{0, 0} (Fin n))
[∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
(hOrient : @Etingof.IsOrientationOf n Q adj)
```

This is verbatim the standard carriage form used across sibling per-(F, Q) leaves in `FieldGenericTpqr.lean` (single_branch_*, degree_*, adjacent_*, graph_*), as well as `FieldGenericT125.lean`, `FieldGenericETilde6.lean`, `FieldGenericETilde7.lean`.

`[IsAlgClosed F]` present (line 93). Consistent with the four sibling per-(F, Q) leaves in `FieldGenericTpqr.lean` (lines 38-42 of the file's docstring enumerate the pattern) and with the file's recipe documented in the module docstring (lines 31-42 of `FieldGenericTpqr.lean`). This is the opposite of the `graph_with_list_cycle_infinite_type_per_kQ` cycle-wrapper case (#2934/#2897), where `[IsAlgClosed F]` was omitted — but the cycle wrapper is a different file, and the per-file decision is consistent within `FieldGenericTpqr.lean`. The outer dispatcher (when closed) will need to propagate `[IsAlgClosed F]` from `single_branch_leaf_case_per_kQ`'s signature to this leaf; the dispatcher already carries `[IsAlgClosed F]` (see `single_branch_leaf_case_per_kQ` stub at `FieldGenericTpqr.lean:` later in the file), so no typeclass-propagation gap exists.

## D2 — Quadratic form expansion fidelity (PASS)

Universal `h_qf` (lines 8285-8315):

```lean
have h_qf : QF adj x =
    2 * V ^ 2 + 2 * L ^ 2 + 2 * A₂ ^ 2 +
    2 * B₂ ^ 2 + 2 * A₃ ^ 2 + 2 * B₃ ^ 2 -
    2 * V * L - 2 * V * A₂ - 2 * A₂ * B₂ -
    2 * V * A₃ - 2 * A₃ * B₃ := by
  unfold QF
  simp only [dotProduct, Matrix.mulVec, h_sum,
    Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, hdiag,
    hv₀_adj_eq, hleaf_adj_eq, ha₂_adj_eq,
    hb₂_adj_eq, ha₃_adj_eq, hb₃_adj_eq,
    eq_self_iff_true, ite_true, ite_false,
    hleaf_ne_v₀, Ne.symm hleaf_ne_v₀,
    ha₂_ne_v₀, Ne.symm ha₂_ne_v₀,
    ha₃_ne_v₀, Ne.symm ha₃_ne_v₀,
    hb₂_ne_v₀, Ne.symm hb₂_ne_v₀,
    hb₃_ne_v₀, Ne.symm hb₃_ne_v₀,
    ha₂_ne_leaf, Ne.symm ha₂_ne_leaf,
    ha₃_ne_leaf, Ne.symm ha₃_ne_leaf,
    hb₂_ne_leaf, Ne.symm hb₂_ne_leaf,
    hb₃_ne_leaf, Ne.symm hb₃_ne_leaf,
    ha₂₃, Ne.symm ha₂₃,
    ha₂_ne_b₂, Ne.symm ha₂_ne_b₂,
    ha₂_ne_b₃, Ne.symm ha₂_ne_b₃,
    hb₂_ne_a₃, Ne.symm hb₂_ne_a₃,
    hb₂_ne_b₃, Ne.symm hb₂_ne_b₃,
    ha₃_ne_b₃, Ne.symm ha₃_ne_b₃,
    ite_mul, one_mul, zero_mul,
    true_or, or_true, false_or, or_false,
    mul_one, mul_zero, sub_zero, zero_sub]
  ring
```

Per-(F, Q) `h_qf` (lines 426-456): same RHS polynomial, same variable
names `V, L, A₂, B₂, A₃, B₃`, same `set` bindings (424-425 vs.
8283-8284), same simp argument list (in the same order, with the same
`Ne.symm` companions), same closing `ring`.

The single divergence is the LHS:
- Universal: `QF adj x = …`, then `unfold QF`.
- Per-(F, Q): `dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = …` (no `unfold` needed).

This is forced by API surface: `QF` is `private abbrev` at
`InfiniteTypeConstructions.lean:4131` and is not exported to
`FieldGenericTpqr.lean`. The per-(F, Q) port writes the spelled-out
form, which is definitionally equal to `QF adj x`. The downstream `rw
[h_qf]` (per-(F, Q) line 458) matches the universal's `rw [show
dotProduct x … = QF adj x from rfl, h_qf]` (universal 8316-8319) — the
per-(F, Q) version is one `rw` step simpler because no bridge through
`QF` is needed.

The 35 simp lemmas (excluding the `Ne.symm` companions) and their
grouping are byte-identical between the two versions. The 12
distinctness facts feeding the simp set (`hleaf_ne_v₀, ha₂_ne_v₀,
ha₃_ne_v₀, hb₂_ne_v₀, hb₃_ne_v₀, ha₂_ne_leaf, ha₃_ne_leaf,
hb₂_ne_leaf, hb₃_ne_leaf, ha₂₃, ha₂_ne_b₂, ha₂_ne_b₃, hb₂_ne_a₃,
hb₂_ne_b₃, ha₃_ne_b₃`) are present in identical order. No simp
argument has been added or removed.

## D3 — Sum-of-squares closure fidelity (PASS)

Universal closure (lines 8320-8352):

```lean
suffices h60 :
    0 < 30 * (2 * V - L - A₂ - A₃) ^ 2 +
    10 * (3 * L - A₂ - A₃) ^ 2 +
    5 * (4 * A₂ - 3 * B₂ - 2 * A₃) ^ 2 +
    3 * (5 * B₂ - 2 * A₃) ^ 2 +
    3 * (4 * A₃ - 5 * B₃) ^ 2 +
    45 * B₃ ^ 2 by nlinarith
by_contra h_le; push_neg at h_le
have h_all_zero :
    2 * V - L - A₂ - A₃ = 0 ∧
    3 * L - A₂ - A₃ = 0 ∧
    4 * A₂ - 3 * B₂ - 2 * A₃ = 0 ∧
    5 * B₂ - 2 * A₃ = 0 ∧
    4 * A₃ - 5 * B₃ = 0 ∧ B₃ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  nlinarith [sq_nonneg (2 * V - L - A₂ - A₃),
    sq_nonneg (3 * L - A₂ - A₃),
    sq_nonneg (4 * A₂ - 3 * B₂ - 2 * A₃),
    sq_nonneg (5 * B₂ - 2 * A₃),
    sq_nonneg (4 * A₃ - 5 * B₃),
    sq_nonneg B₃]
obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_all_zero
have hB₃ : B₃ = 0 := h6
have hA₃ : A₃ = 0 := by nlinarith
have hB₂ : B₂ = 0 := by nlinarith
have hA₂ : A₂ = 0 := by nlinarith
have hL : L = 0 := by nlinarith
have hV : V = 0 := by nlinarith
apply hx; ext i
rcases h_all_named i with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  [exact hV; exact hL; exact hA₂;
   exact hB₂; exact hA₃; exact hB₃]
```

Per-(F, Q) closure (lines 459-491): byte-identical (modulo
indentation). Same `30/10/5/3/3/45` coefficients, same square
expressions `(2V-L-A₂-A₃), (3L-A₂-A₃), (4A₂-3B₂-2A₃), (5B₂-2A₃),
(4A₃-5B₃), B₃` in the same order, same `nlinarith` hint list with the
same `sq_nonneg` invocations, same `B₃ → A₃ → B₂ → A₂ → L → V` peeling
order, same final 6-case dispatch via `rcases … with rfl | rfl | rfl |
rfl | rfl | rfl <;> [exact hV; exact hL; exact hA₂; exact hB₂; exact
hA₃; exact hB₃]`.

The case-list ordering in the final `[exact hV; exact hL; exact hA₂;
exact hB₂; exact hA₃; exact hB₃]` line exactly mirrors the
`h_all_named` enumeration `v₀, leaf, a₂, b₂, a₃, b₃` from both the
helper's (217-219) and the universal's (8076-8078) definitions.

## D4 — Neighbor-list lemma fidelity (PASS)

Six neighbor lemmas, in the same order, with the same derivation
strategy:

| Lemma | Universal | Per-(F, Q) | Derivation |
|---|---|---|---|
| `hv₀_nbrs : adj v₀ j = 1 → j ∈ {leaf, a₂, a₃}` | 7971-7982 | 112-123 | erase-then-`hS₀_eq` |
| `hleaf_nbrs : adj leaf j = 1 → j = v₀` | 7983-7997 | 124-138 | pigeonhole via `h_leaf_deg` |
| `ha₂_nbrs : adj a₂ j = 1 → j ∈ {v₀, b₂}` | 7998-8009 | 139-150 | erase-then-`hb₂_eq` |
| `hb₂_nbrs : adj b₂ j = 1 → j = a₂` | 8010-8024 | 151-165 | pigeonhole via `hb₂_deg1` |
| `ha₃_nbrs : adj a₃ j = 1 → j ∈ {v₀, b₃}` | 8025-8036 | 166-177 | erase-then-`hb₃_eq` |
| `hb₃_nbrs : adj b₃ j = 1 → j = a₃` | 8037-8051 | 178-192 | pigeonhole via `hb₃_deg1` |

Each body is structurally identical between the two versions: the
two-branch `by_cases` for the erase-style proofs (`hv₀, ha₂, ha₃`),
and the `Finset.card_pair`-via-`Finset.card_le_card` pigeonhole for
the degree-1 vertices (`hleaf, hb₂, hb₃`).

The per-(F, Q) helper introduces *no* additional helper lemmas beyond
those in the universal. Compared head-to-head against the universal
proof body, the per-(F, Q) version's locally-derived facts (lines
102-107, the carriage prelude — `adj_comm, ne_of_adj', hleaf_ne_v₀,
ha₂_ne_v₀, ha₃_ne_v₀`) and the inner Steps 5/6 facts (lines 255-309,
`ha₂_ne_b₂, ha₃_ne_b₃, hb₂_ne_leaf, hb₃_ne_leaf, ha₃a₂_zero,
hb₂_ne_a₃, ha₂_ne_b₃, hb₂_ne_b₃`) are all present in the universal
proof at the matching positions (universal 6923-6924 for the first
two, 6943-6945 for the three `_ne_v₀` facts; 8114-8168 for the inner
Step 5/6 facts). The downstream `huniv` (per-(F, Q) 311-318 = universal
8170-8177), `h_sum` (319-351 = 8178-8210), and adj-row equations
(353-421 = 8212-8280) are byte-identical modulo indentation.

The `acyclic_path_nonadj` invocation for `ha₃a₂_zero` (per-(F, Q)
267-282 = universal 8126-8141) uses the same 3-vertex cycle path `[a₂,
v₀, a₃]`, the same `simp only` arguments for nodup/length, and the
same `k = 0 ∨ k = 1` case split with the same closing witnesses.

## D5 — Carriage discharge (PASS)

Per-(F, Q) line 101:

```lean
let _ := F; let _ := Q; let _ := hOrient
```

This is the first wave-62 per-(F, Q) helper to use the
`let _ := F; let _ := Q; let _ := hOrient` discharge pattern visibly
(other per-(F, Q) leaves — `degree_ge_4_per_kQ`,
`graph_with_list_cycle_per_kQ`, `adjacent_branches_per_kQ`,
`single_branch_not_posdef_per_kQ` — substantively use `F, Q, hOrient`
in their bodies via dispatch to `etilde6_/etilde7_/t125_per_kQ`).

The discharge is correct: `F, Q, hOrient` are not referenced anywhere
in lines 102-491. I verified by reading the full body; no `F`, no `Q`,
no `hOrient` symbol appears in any tactic, term, or proof step
downstream. The contradiction lives entirely at the level of
integer-coefficient positive-definiteness on the six named vertices,
which is exactly what the docstring (lines 61-63) claims:

> The proof does not depend on `F` or `Q` substantively; those are
> carried through for API consistency with the sibling sub-case
> helpers.

The `let _ := …` pattern is the canonical way in Lean 4 to suppress
"unused argument" warnings without affecting elaboration (it binds the
hypothesis to a wildcard, creating an artificial use). This is a
cleaner pattern than `attribute [-instance]` (which only suppresses
instance resolution warnings, not unused-argument linting). The
docstring matches the body.

## Style and `maxHeartbeats` setting

The per-(F, Q) helper sets `maxHeartbeats 6400000` (line 49) with the
documented reason "T(1,2,2) posdef proof unfolds the QF over 6
vertices via a single `simp only` with ~30 distinctness facts plus
extensive `acyclic_path_nonadj` and `Finset.sum_insert` reasoning,
pushing elaboration past the default budget; mirrors the same setting
on `single_branch_leaf_case` (`InfiniteTypeConstructions.lean:6896`)."

Verified: `InfiniteTypeConstructions.lean:6896` does set the same
budget on `single_branch_leaf_case`. The two settings are coherent.
The `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
CategoryTheory.ReflQuiver.toQuiver in` prelude (lines 55-56) is the
standard per-(F, Q) device for avoiding ambiguous Quiver instance
resolution with the explicit `Q` argument.

## Verdict summary

| Deliverable | Verdict |
|---|---|
| D1 — Signature fidelity | PASS |
| D2 — Quadratic form expansion fidelity | PASS |
| D3 — Sum-of-squares closure fidelity | PASS |
| D4 — Neighbor-list lemma fidelity | PASS |
| D5 — Carriage discharge | PASS |

No code changes. No follow-up issues. The helper is a faithful
per-(F, Q) port of the universal T(1, 2, 2) = D₅ posdef contradiction
and is ready to be called from `single_branch_leaf_both_extend_per_kQ`
once the dispatcher closes (#2905 chain).

## Future-of-this-helper note (out of scope)

When the `single_branch_leaf_both_extend_per_kQ` dispatcher closes,
the universal proof's lines 7964-8352 should be considered for a
refactor: extract the inline T(1, 2, 2) contradiction at universal
7964-8352 into a standalone universal lemma
`single_branch_leaf_both_extend_t122` parallel to the per-(F, Q)
helper. This would parallelize the universal/per-(F, Q) layout for
T(1, 2, 2), as already exists for `embed_t125_in_tree` /
`embed_t125_in_tree_per_kQ`. Filing this would be a planner's call
once #2905 lands; not in scope for this audit.
