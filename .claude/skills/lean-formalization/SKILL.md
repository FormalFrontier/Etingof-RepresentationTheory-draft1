---
name: lean-formalization
description: Use when working on Phase 3 formalization — translating mathematical text into Lean 4 statements and proofs, or filling sorry placeholders.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Lean Formalization Skill

Patterns for formalizing mathematics textbooks into Lean 4 with Mathlib. Derived from Phase 2 analysis of 583 items across 10 chapters of Etingof's Representation Theory.

## Session Setup

Before the first `lake build` or `lake env lean` in any session:
```bash
lake exe cache get
```
This downloads pre-built Mathlib oleans. Skipping it triggers a full Mathlib rebuild (1800+ jobs).

**Typecheck with `lake build EtingofRepresentationTheory.<Module>`, NOT `lake env lean
<file>`.** `lake env lean` does **not** apply the lakefile's `[leanOptions]` — in
particular `maxSynthPendingDepth = 3` (lakefile.toml; the Lean default is 2). Deep
instance chains in this project (e.g. the `Subalgebra → Module.End` centralizer-module
instances: `Module ↥(centralizer A) (V →ₗ[A] E)` from `centralizerModuleHom`) need depth
3, so under `lake env lean` they throw **spurious** `synthInstanceFailed` errors that do
not occur under `lake build`. If a file fails `lake env lean` with instance-synthesis
errors on centralizer/Subalgebra hom-spaces but you suspect the proof is fine, re-check
with `lake build <Module>` before debugging — the on-`main` file fails `lake env lean`
too. (Some places below still say `lake env lean`; prefer `lake build` when the file uses
these instances.)

**Reading background-build results: grep the teed log for `error:`, do not trust a
wrapper's exit code or `tail`.** `lake build` prints Lean errors *before* the final
`Build completed` / `✖` summary, so `... | tee log | tail -40` can hide them, and a
separate poller/`sleep`-loop you spawn to wait has its own exit status unrelated to
the build's. Always confirm success by `grep -nE "error:|✖|Build completed" log`
on the full teed file (and check `#print axioms` for `sorryAx`) — never infer "build
passed" from a poller returning exit 0.

**Build-environment recovery (shared `.lake/packages` across pod worktrees):**
- `Lean exited with code 139` (SIGSEGV) on *dependency* files you did not touch has
  two distinct causes. (a) Corrupted Mathlib oleans from a concurrent `lake exe cache
  get` writing the shared dir — fix with `lake exe cache get!`, then rebuild. (b)
  **Memory pressure from build parallelism** — if the SAME heavy file builds fine in
  isolation (`lake build EtingofRepresentationTheory.Chapter5.<File>`) but segfaults
  during a big parallel build, it is OOM, not corruption. Build the heavy files one
  at a time, then the target.
- `failed to read file '...olean', incompatible header` means `main` bumped the Lean
  toolchain mid-session. `lake exe cache get` only fetches **Mathlib** oleans, NOT
  the upstream deps (batteries/aesop/Qq/importGraph/Cli/plausible) — those keep
  old-toolchain oleans and keep throwing `incompatible header`. Recovery order:
  1. `git fetch origin main`; if `origin/main:lean-toolchain` changed, rebase onto
     `origin/main`.
  2. The shared `.lake/packages/mathlib` checkout itself can lag the manifest
     (`lake update` may not move it): `grep -A2 '"name": "mathlib"' lake-manifest.json`
     for the pinned `rev`, then `git -C .lake/packages/mathlib checkout <rev>` so its
     `lean-toolchain` matches the project.
  3. `lake exe cache get`, then rebuild the stale upstream deps (`lake build Batteries
     Aesop ...`, or just build your target and let lake regenerate them).
- A **stale session in another worktree** still on the pre-bump toolchain can rebuild
  the shared dep oleans back to the old version, re-corrupting your build in a loop.
  Check `pgrep -fl 'v4.28'` (the old version); if a `lake`/`lean` from an obsolete
  worktree is running, terminate that specific PID (targeted, not `pkill`).

## Pre-Flight Checklist (Before Starting Any Proof)

Run this checklist before writing a single tactic. Skipping it has caused agents to waste entire context windows on dead-ends.

1. **Check Known Dead-Ends.** Scan the "Known Dead-Ends" section below. If your proof requires any of these patterns, sorry it immediately and move on:
   - ExteriorAlgebra ↔ PiTensorProduct bridging
   - `if`-branching `obj` fields in QuiverRepresentation-like structures
   - `Decidable.casesOn` **composition** (double round-trip) in `reflectionFunctorPlus`/`Minus` proofs — the composition F⁻(F⁺(V)) creates types Lean can't reduce through. **Note:** Individual arrow-level helper lemmas (e.g., `reversedArrow_ne_ne_is_cast`, `reversedArrow_ne_ne_twice`) ARE provable using `eqRec_heq_self` and `Subsingleton.elim` patterns (see HEq section below). The dead-end is the full Sigma-level round-trip, not individual components.
   - `reflFunctorPlus_mapLinear_ne_ne` / `reflFunctorMinus_mapLinear_ne_ne` API (missing; needed for reflection functor naturality in the ne/ne case)
   - ~~Definition-level `sorry : Type` for `AlgIrrepGL`~~ — **RESOLVED** (Wave 35): SchurModule constructed in PR #1740, AlgIrrepGL instances via `show ... from inferInstance` in PR #1752. Some downstream definition sorrys remain (`formalCharacter`, `kostkaNumber`).
   - ~~Nilpotent operator structure theorem (cyclic decomposition / Jordan chains) — not in Mathlib, blocks Problem6_9_1.~~ — **RESOLVED** (Wave 47): Problem6_9_1 proved without cyclic decomposition via direct IsCompl argument (#2215).
   - ~~Clifford theory (semidirect product orbit method) — blocks Mackey machine (Theorem5_27_1)~~ — **RESOLVED** (Wave 47): All Mackey machine sorries proved. PRs #2034, #2047, #2049 all merged after CI fix (#2240). The original 500-line estimate was too pessimistic — bypass approaches proved sufficient.
   - ~~`Submodule.map` of complementary submodules through non-injective maps — does NOT preserve complementarity. Problem6_9_1 IsCompl conditions hit this fundamental gap.~~ — **RESOLVED** (Wave 47): Bypassed via 7-step IsCompl proof that avoids map_of_complementary entirely (#2215).
   - `Lemma5_13_3` (Young symmetrizer idempotency) over general fields — currently only works over ℂ. Blocks the trace-based approach to Weyl character formula.
   - Corner ring Morita equivalence (`eAe` Morita equivalent to `A` for full idempotent `e`) — not in Mathlib, ~200-300 lines. Blocks BasicAlgebraExistence.
   - `basic_morita_algEquiv` (basic + Morita equivalent ⟹ isomorphic) — fundamental circularity: all non-circular approaches require Krull-Schmidt theorem or progenerator theory, neither in Mathlib.
   - ~~Right-multiplication dominance for polytabloids~~ — **RESOLVED** (Wave 46): The tabloid module approach (`TabloidModule.lean`) bypasses the right-multiplication issue entirely. Linear independence uses tabloid projections + unitriangularity, not direct dominance comparison. The remaining bottleneck is `polytabloid_syt_dominance` which needs a cross-column entry comparison argument (issue #2124).
   - `columnInvCount'` as straightening WF order — **PROVEN FALSE** (counterexample in #2104): for partition (2,2), σ = swap(1,2) has columnInvCount' = 1, but Garnir terms can also have columnInvCount' = 1. The correct WF order is tabloid dominance (multiset-based), not pointwise column inversion count. PR #2119 was closed as stale; straightening needs a fresh implementation using `tabloidDominance` from TabloidModule.lean.
   - Non-commutative `TensorProduct` — Mathlib requires `CommSemiring`. Balanced tensor product `A ⊗_{eAe} N` must be built as a manual quotient (~100 lines boilerplate). Blocks corner ring Morita equivalence and BasicAlgebraExistence.
   - `garnir_reduction'` algebraic approach — The standard approach using `a_λ · G = 0` (Garnir element annihilated by row symmetrizer) and Lemma 5.13.1 collapses to a tautology when trying to extract the linear combination. The algebraic identity only shows the existing tabloid is in the span — it doesn't produce the *smaller* tabloids needed for the inductive step. Needs tabloid-level reasoning (James' approach: work with equivalence classes of fillings under row permutations) instead.
   - Polytabloid transfer map `tabloidProjection(polytabloid T) = polytabloidTab T` — **PROVEN FALSE** (Wave 46-49): For partition (3,2), two distinct SYTs can map to the same inverse-tabloid. The dominance property (`swap_column_dominance`) fails for σ_T⁻¹. 4+ agent sessions were wasted on this approach across issues #2189, #2212. The correct approach uses tabloid-level unitriangularity (Track 2 in TabloidModule.lean), not direct transfer.
   - `iso_of_formalCharacter_eq_schurPoly` — Requires GL_N complete reducibility (Schur-Weyl duality), which is NOT in Mathlib. The supporting lemmas are all proved (schurPoly_injective, finrank equality, weight space independence), but the core reduction step needs polynomial GL_N representation theory that would be ~300+ lines of new infrastructure. Mark as a Mathlib dependency gap. (Wave 49 meditate assessment.)

2. **Search for existing definitions and infrastructure.** Before defining any concept or building any equivalence/isomorphism, search the codebase:
   ```bash
   grep -r "def.*YourConceptName\|abbrev.*YourConceptName" EtingofRepresentationTheory/
   ```
   Duplicate definitions across chapters create incompatibility bugs that require manual refactoring later (e.g., duplicate `inducedCharacter'` in Ch5, duplicate `IsIndecomposable` in Ch2/Ch6). **Also search for infrastructure you might need** — PRs #1682, #1685, #1690 independently built the same GL₂(𝔽_q) BorelSubgroup equivalence because agents didn't check what already existed. Before building group/subgroup equivalences, coset decompositions, or character computation helpers, search for them first.

3. **Verify the statement.** Cross-reference the Lean statement against the book's text. Missing hypotheses (algebraic closure, field characteristic, orientation constraints) are a recurring source of wasted proof attempts. If the proof fails at a fundamental level after 1 attempt, suspect a statement bug before trying alternative tactics.

4. **Estimate your context budget.** Difficulty 3/3 proofs consume 60-80% of a context window on average. If you're already past the midpoint of your session, consider claiming an easier item instead. Partial progress on a hard proof with no commit is worth zero — a completed easy proof is worth one sorry removed.

5. **Check dependency readiness.** Verify that imports compile and key helper lemmas are sorry-free (or that sorry'd helpers won't block your proof). Use `lake build <module>` for the specific file. **A "closed/merged" dependency can still fail to compile.** A `.lean` file absent from its `ChapterN.lean` aggregator is never built by CI, so it rots silently when an upstream lemma it cites changes signature. Before consuming a cited dependency, `grep "ChapterN.Module" EtingofRepresentationTheory/ChapterN.lean` to confirm it is in the build graph, then `lake build` that exact module — do not trust that #closed ⟹ compiles. **And when you create a new file, add it to the `ChapterN.lean` aggregator in the same PR** (otherwise it will not be CI-checked and the next signature change will break it undetected). Concretely (#4695): `KernelLemmaK.lean` (the #4694 kernel-lemma assembly) was never in the aggregator and had stopped compiling against the corrected `kernelLemmaK'`; the fix had to be made before the assembly could even be attempted. Note also: when wiring a low-level file (e.g. a localization stack) back into a higher-level one, watch for `import` cycles — if file `A` imports `B` only for one small lemma, relocate that lemma to a leaf (Mathlib-only) file imported by both, rather than creating the cycle.

   Use `set -o pipefail` when piping `lake build` through `tee`/`tail` — otherwise the pipeline's exit code is `tee`'s `0` and a real build failure reads as success. **For "mechanical glue"/aggregation issues, also audit that the *generality* of every input lemma matches the goal — closed/merged ≠ usable.** An issue can have all its named dependencies merged yet still be unwritable because the inputs are proved at a narrower generality than the target. Concretely (#2708, Schur-Weyl C-4a): the goal `schurModuleSubmodule_isSimple_centralizer` is over a generic alg-closed CharZero field `k`, but every per-block input it must feed (`trace_symGroupAction_eq_spechtModuleCharacter`:1029, `youngSym_action_vanishes_off_block`:2158, `youngSym_action_on_special_block_rank_one_scaled_proj`:2279) is hardcoded to `ℂ`, and generic `k` does not base-change from `ℂ`. `grep` the input lemmas' signatures for the field type before claiming. If they are `ℂ`-only while the goal is generic, the issue is mis-scoped: `coordination skip` to `replan` with the two paths (specialize the goal to `ℂ` — usually correct when the rest of that chapter's backbone is `ℂ`-only and nothing consumes the generic statement; or first generalize the inputs to generic `k`). Do not rewrite the goal's generality unilaterally.

6. **Code the framework before deep analysis.** When a proof has an obvious high-level structure (e.g., "use Schur's lemma + nonvanishing"), code that framework with sorry placeholders within the first 15 minutes. Don't spend the majority of your session analyzing whether the hard step is provable before writing any Lean. The framework commit has value even if the hard sorry remains — it reduces the problem for future agents. Deep mathematical analysis should happen AFTER the framework compiles, focused on the specific sorry goals.

## Endgame Protocol (≥99% Sorry-Free)

When the project is near completion (581/583 items sorry-free as of Wave 49), the remaining sorries are qualitatively different — they're the hardest problems, not low-hanging fruit. Agents must adjust their approach.

### Definition Audit Before Proof Attempts

**When a proof is stuck after 2 attempts, audit the definition against the textbook BEFORE trying more proof approaches.**

The polytabloid definition was non-standard (T-dependent form `κ_T · of(τ) · a_λ` instead of standard `of(τ) · c_λ`). This caused **4+ agent sessions** of wasted work across multiple waves. Once the definition was refactored to match the textbook, 3 sorries were eliminated trivially.

**Checklist when stuck:**
1. Read the blob file for the relevant definition
2. Compare the Lean definition's structure against the book's mathematical definition
3. Check: does the Lean definition use the same decomposition/factoring as the book?
4. If not, consider whether a definition refactoring would simplify the proof
5. A definition refactoring that makes proofs trivial is MORE valuable than a clever proof of a bad definition

### Counterexample-First Verification

Before investing a full session in a hard proof, spend 5-10 minutes checking the statement is correct:

1. **Instantiate with concrete examples.** If the theorem is about all graphs with property P, check P for the simplest non-trivial case.
2. **Check boundary cases.** The hypothesis `h_dim : Module.finrank k M = Module.finrank k (SchurModule k N lam)` was added to `iso_of_formalCharacter_eq_schurPoly` after discovering a counterexample: `M = SchurModule ⊕ det⁻¹`. **`formalCharacter` is a *truncated* invariant — it records only `ℕ`-valued weight spaces and is blind to `det`-twists — so it is NOT a complete invariant, and SIMPLICITY does not rescue it.** Any lemma deriving "`M` is polynomial" (`⨆ μ, glWeightSpace = ⊤`) or "`M ≅ L_λ`" from `IsSimpleModule` + `formalCharacter M = schurPoly N lam` *alone* is **false** (#4948): counterexample `M = det⁻¹ ⊗ Sym³(std)`, `N=2` — simple, 4-dim, `formalCharacter = x₁+x₂ = schurPoly 2 (1,0)` (the `(-1,-1)` shift sends `(3,0),(2,1),(1,2),(0,3) ↦ (2,-1),(1,0),(0,1),(-1,2)`, only `(1,0),(0,1) ∈ ℕ²` survive) yet ℕ-weight spaces span only 2 of 4 dims and `M ≇ std`. Polynomiality must be a **threaded hypothesis** (`hLtop : ⨆ μ, glWeightSpace = ⊤`), discharged from the rep's actual polynomial source (e.g. transport `M`'s `h_span` to a simple summand `L` across the equivariant iso via `glWeightSpace_map_eq_of_rep_iso` + `Submodule.map_iSup`), never manufactured from simplicity. When a planner decomposes a hard theorem into "isolated `sorry` ingredients", an ingredient can itself be *unsound* — verify each ingredient is TRUE (seek a counterexample) before grinding on its proof.
3. **If two "different" accounts/objects produce suspiciously similar data, investigate.**
4. **Indecomposability of explicit affine-Dynkin reps: build a small decomposition first.** The Ch6 `*Rep_kQ_isIndecomposable` family (D̃/Ẽ/T(p,q,r), orientation-generic) is built from a single nilpotent twist `N`, which is **too weakly coupled** and yields *decomposable* reps. Already refuted for the sporadic cases (Ẽ₆/Ẽ₇/T(1,2,5), #4548, `progress/indecomposability-framework-investigation.md`) and for the D̃ family in **reversed-leaf** orientations (D̃₄ #4523 → #4566: explicit `m=1` complementary pair). The needed fix is the homogeneous-tube redesign, not a cleverer proof. Before claiming any open `d5/d6/d7/d8/dTilde/etilde/t125 *_kQ_isIndecomposable` issue, check #4566/#4548 — most are likely still false. A reversed leaf removes the coupling its forward edge supplied, so test a reversed orientation at `m=1` for `span`-level decompositions. (Note: the canonical all-sink D̃₄ `starRepGen_isIndecomposable` is genuinely indecomposable — only the orientation-generic statements are at risk.) **This also refutes the `*_kQ_leaf_equalities` sub-lemmas** (e.g. #2853, and the d6/d7/d8 analogs) that feed those `_isIndecomposable` theorems: the *mixed* orientations (one leaf pushed, one pulled at a shared center) force only an M-twisted relation `M(W⟨leaf⟩) = W⟨other⟩` with `M = (I−N)⁻¹` (derivable via `linearEquiv_invariant_isCompl_symm_mem` + `gammaInv_embed_general_F` + the v=2 `core_F`), and no edge supplies the leaf N-invariance needed to untwist it — so leaf equality is *false* there (D̃₅ m=1: `W⟨0⟩=span{(1,1)}`, forced `W⟨5⟩=(I−N)W⟨0⟩=span{(0,1)}`). Don't grind on a `_leaf_equalities` issue over arbitrary orientations; only the all-canonical and all-leaves-reversed branches are provable. **To land a sorry-free `_leaf_equalities`, restrict the statement rather than leaving bare sorries (#4743 for D̃₅):** add explicit Hom-direction hypotheses to the signature (`hc02/hc12/hc23 : Nonempty (@Quiver.Hom (Fin n) Q ⟨a⟩ ⟨b⟩)` pinning each canonical edge, plus a same-direction `Iff` for the two shared-center leaves, e.g. `hv3 : Nonempty (Hom 4 3) ↔ Nonempty (Hom 5 3)`), then discharge every off-restriction `rcases hOrient_edge` branch with `(hOrient.2.2 i j h_canonical h_reversed).elim` — `IsOrientationOf`'s third conjunct (`OrientationDefs.lean:41`) is exactly the antisymmetry "no arrows both ways". This keeps the existing case tree intact; only the previously-`sorry` leaves change to one-line contradictions (minimal diff). If the lemma is consumed generically (e.g. by `_isIndecomposable`, which only uses it in its all-canonical branch), **move the call into the branch that can supply the hypotheses** — there the canonical arrows give `⟨a02⟩ ⟨a12⟩ ⟨a23⟩` and same-direction `v3` leaves give `iff_of_true ⟨a43⟩ ⟨a53⟩`. Reusable across the open D̃₆/₇ leaf_equalities (#4722/#4689). **Construction tip for the homogeneous-tube `def` (sub-A of each shape, e.g. `t125Rep_kQ` #4559 mirroring `etilde7Rep_kQ` #4568):** the `*RepMap_kQ` match must produce `(Fin (*Dim m a) → F) →ₗ (Fin (*Dim m b) → F)`, and the leaf vertex has dimension `m+1` (not `1*(m+1)`) in `*Dim`. Since `1*(m+1)` is **not** defeq to `m+1`, the `a=1` block maps (`suffixBlockEmbed_F F 1 2`, `prefixBlockEmbed_F F 1 _`) fail to typecheck at the leaf — use `starEmbed2_F`/`starSecond_F` (suffix) or `starEmbed1_F`/`starFirst_F` (prefix), which produce the bare `Fin (m+1)` shape. The `2…6`-coefficient block maps are fine. To extract `>2` input blocks for a wide eigenvalue arm (T(1,2,5)'s arm 1 is `F^{3(m+1)}`), the fixed-`N` `blockEmbedAt_F` won't fit; use the general `blockEmbedAtN_F`/`blockProjAtN_F` (`FieldGenericT125.lean`, target dim a raw `ℕ`). **3-arm tube caveat (Ẽ₆/T(p,q,r), #4638): even the *all-canonical* "three leaf subspaces equal `W⟨leaf_i⟩` all equal" collapse is circular and NOT a usable stepping stone** — unlike D̃₄ where each arm's diagonal embed hits *both* center blocks (so `compl_le_forces_eq` gives `W⟨leaf⟩=W⟨1⟩=W⟨2⟩` for any pair), each tube arm embeds its leaf line into only 2 of the ≥3 center blocks. The proven membership criteria (`etilde6_arm{A,B,C}_criterion`, `FieldGenericETilde6.lean`) give `x∈W₁⟨2⟩ ↔ (0,x,x)∈W₁⟨0⟩`, `x∈W₁⟨4⟩ ↔ (x,0,x)∈W₁⟨0⟩`; the inclusion `W₁⟨2⟩≤W₁⟨4⟩` that `compl_le_forces_eq` needs is `(0,x,x)∈W₁⟨0⟩ ⟹ (x,0,x)∈W₁⟨0⟩`, **false** for general `W₁⟨0⟩` (e.g. `⟨(0,1,1)⟩`). Leaf-equality holds only because the surviving pairs are trivial — i.e. it is a *corollary* of indecomposability, not a route to it. The correct route (sub-C assembly) is the §3 **brick contradiction** consuming the criteria + `etilde6_arm*_plane_split` (each plane `π_i=(W₁⟨0⟩⊓π_i)⊕(W₂⟨0⟩⊓π_i)`) + the eigenvalue site, concluding `W₁⟨0⟩∈{⊥,⊤}` directly. **Once a shape's corrected homogeneous-tube `def` lands, its `_isIndecomposable` flips from false to TRUE — stop trying to refute it.** Scope construction and proof as *separate* deliverables (the ETilde6/7 + D̃₄ pattern): the `*Rep_kQ` def gains an explicit `(lam : F)` parameter with the fourth/eigenvalue arm = `starEmbedTube_F F lam m` (`λ•id + J`, a *square* Jordan block — relocated into `FieldGenericStar.lean`, #4648), the `*_not_finite_type_per_kQ` consumer fixes `lam = 1`, and the orientation-generic `_isIndecomposable` proof is sorried "for every lam", **deferred to a shared family-wide center-crux wall** (open across D̃₄ #4674 / D̃₅–D̃₈ / Ẽ₆ `etilde6Rep_kQ_isIndecomposable` / Ẽ₇). The worked canonical-orientation proof `starTubeRepGen_isIndecomposable` (`FieldGenericTube.lean`) + the leaf reductions `forward_leaf_subspace_eq`/`reversed_leaf_subspace_eq` + the center lemma `eigenvalue_jordan_invariant_compl_trivial_gen` are the assembly pieces. So: don't re-investigate whether these are tractable as one unit, and don't refute a shape whose corrected tube already landed — check the construction's arm map first.

5. **"Follows via Schur's lemma / character matching" can be circular — check the nonzero-hom prerequisite.** When an issue claims a decomposition/iso "follows by Schur's lemma" from two reps being simple, remember Schur's lemma (`finrank_hom_simple_simple`) only gives `Hom ∈ {0,1}`-dim; concluding *iso* needs a **nonzero** equivariant map, which usually presupposes the very character/highest-weight match being sought. Example (#2493): identifying the abstract Schur-Weyl summand `Lᵢ` with `SchurModule k N λ` was claimed to follow from `Lᵢ` simple (C-3) + `SchurModule` simple (C-4) + Schur's lemma, but that route is circular — it needs `char(Lᵢ) = schurPoly N λ` (the highest-weight classification, downstream #2482/#2483) to produce the nonzero map. The character-level assembly (`formalCharacter(V^⊗n) = ∑_λ dim(Sλ)·sλ`) is reachable from C-1∘C-2; the concrete-module iso is not. Land the reachable character identity and route the classification gap to the downstream issue rather than forcing a circular "Schur's lemma" proof. Also: do not "rescue" such an iso with a pure `finrank`-equality `≃ₗ[k]` — it type-checks but is mathematically vacuous (any equal-dimension spaces are k-linearly isomorphic), violating the no-vacuous-theorems principle.
6. **"Vanishes pointwise" lemmas about an element already known to lie in a span are usually false — refute by direct computation.** A lemma claiming an explicit element has *zero coefficient* at certain basis points (e.g. a residual `Δ`'s coefficient at tabloids with no column-standard rep, Ch5 Wall 3 R2.b.i #2769) is suspicious whenever the true reason `Δ` sits in the target span `V` is **global** rather than pointwise. If `Δ` equals a single polytabloid `±ψ_τ` (τ col-standard), it carries `±1` at *every* column-class of τ — including non-standardizable ones — so pointwise vanishing fails even though `Δ ∈ V` holds. Brute-force the smallest example by replicating the Lean definitional conventions exactly (`toTabloid` = entry→row map, `ColumnSubgroup`, `tabloidStrictDominates`, signed-polytabloid form of the construction), and **validate your model reproduces a known ground truth** (e.g. the design note's hand-computed values) before trusting a refutation. This refuted #2769 in minutes (`progress/r2bi-counterexample-check.py`, redesign tracked in #4584). **A hand-checked *confirmation* is no safer than a hand-checked refutation — brute-force both directions.** A prior meditate note (#2776, `progress/r3-bis-residual-cancellation.md` §3) claimed the *same* statement was TRUE via a cross-region involution, "validated on the running example; sign reversal verified" — the faithful brute force refuted it on that very example. When you assert a tricky combinatorial identity *holds*, run the script; never ship "verified by hand". And refuting the lemma does not refute the goal: the global span-membership a dead pointwise route was serving is often still true by a *direct* identification (here `Δ = ±ψ_τ`, discharged by the existing `(srRank, rowInvCount')` induction — see `progress/r2b-redesign-direct-polytabloid.md`). Also beware the inverse circularity trap: a "straightening" lemma that *consumes* `v ∈ V` as a hypothesis (e.g. `tabloidSupport_straightening`) cannot be the route that *establishes* `v ∈ V`; and a design note claiming a proof is "just re-packaging the internals of lemma X" is circular whenever X takes the goal as a hypothesis — check before adopting the plan. **When your validation script tests a *measure/ordering* condition (e.g. `srRank τ' < srRank σ`, IH-availability, dominance), pin the measure's DIRECTION to the codebase definition before trusting PASS/FAIL.** A flipped sign silently inverts the verdict: here `srRank σ = #{τ : σ strictly dominates τ}` counts tabloids *below* σ, so a tabloid dominated by σ has *smaller* srRank (IH-available) — an early script that counted tabloids *above* spuriously reported every constituent "above σ" and nearly condemned a sound route (Ch5 R2.b #4593, validated route → #4604/#4605). Re-derive one row by hand against the Lean `def` before reading the table.

7. **Character / multiplicity identities: dimension-count both sides (evaluate at all-ones) before attempting.** Any claimed `formalCharacter M = ∑_λ (coeff_λ)·S_λ` must match in *total dimension*: setting every torus variable to `1` makes each `S_λ` evaluate to `dim V_λ = s_λ(1,…,1)` and the LHS to `dim M`. This is a 30-second check that catches multiplicity errors instantly. It refuted #4944: `polyRightDegreeFDRep_formalCharacter` claimed the degree-`d` part `A_d` of `k[Xᵢⱼ]` had a *multiplicity-one* decomposition `formalCharacter k N A_d = ∑_{ν : BoundedPartition N d} schurPoly N ν.parts`, but for `N=2, d=1`, `dim A_1 = 4` (the four `Xᵢⱼ`) while `∑_ν dim V_ν = dim V_{(1,0)} = 2` — unequal, so false. The actual right-`GL_N` multiplicity is `dim S_ν(k^N) = s_ν(1,…,1)` (the left Schur-factor of the GL×GL Cauchy bi-rep `Sym^d(V⊗W) = ⊕_ν S_ν(V)⊗S_ν(W)`), **not** one. The fix is to correct the statement to the multiplicity-bearing form `∑_ν (eval 1 (schurPoly N ν.parts)) • schurPoly N ν.parts` (Cauchy at `x=1^N`) — and since a sorried *false* theorem is a landmine even unused, correct it openly (per "Definition seems wrong: don't silently work around bad definitions") rather than leaving it. Watch for "multiplicity one" / "each ν exactly once" claims about a *forgetful restriction* of a bi-representation: forgetting one factor of `V_λ ⊠ V_λ` leaves `dim V_λ` copies, never one (except `dim V_λ = 1`, i.e. powers of `det`). The qualitative *support* conclusion a consumer wants (e.g. "constituents of `A/det` have `ν_N = 0`") usually survives the multiplicity correction (the `dim V_{ν-(1,…,1)} = dim V_ν` factors cancel termwise), so re-spec the proof, don't abandon the consumer.

This saved 2+ sessions in Waves 47-49 by catching false statements early, an entire D̃₄ proof attempt (#4566), a Ch5 Wall 3 R2.b.i attempt against a false pointwise-vanishing residual lemma (#2769 → #4584), and a research-level Cauchy proof attempt against a false multiplicity-one character identity (#4944).

### Sorry Decomposition as Primary Strategy

In endgame, **decomposing a hard sorry into 2-4 smaller sorries is often more valuable than attempting the hard sorry directly.**

**When to decompose (not attempt directly):**
- Difficulty ≥ 7 and no clear single-session proof strategy
- The proof has independent sub-cases or sub-lemmas
- Multiple agents could work on different sub-sorries in parallel

**How to decompose well:**
1. Code the proof framework with `sorry` placeholders for each independent step
2. Each sorry should have a clear mathematical description in a comment
3. Each sorry should be independently attackable (no circular dependencies between sub-sorries)
4. Create issues for each sub-sorry with proper `depends-on` relationships

**Evidence:** Problem6_1_5_theorem (1→0), Theorem2_1_2 (1→2 smaller), InfiniteTypeConstructions (0→4 targeted), PolytabloidBasis (3→0 via restructure) — all used decomposition as the winning strategy.

### When to Accept a Long-Term Sorry

Some sorries may represent genuinely hard formalization work beyond current Mathlib infrastructure. Accept them when:
- The sorry requires 200+ lines of new mathematical infrastructure not in Mathlib
- 3+ agents have attempted different approaches and all failed
- The sorry is not blocking other items (leaf node in dependency graph)

**Current long-term candidates (Wave 49):**
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (difficulty 8)
- `basic_morita_algEquiv` — requires Krull-Schmidt theorem (not in Mathlib)
- 3× `*_isIndecomposable` proofs — may require explicit matrix computation

**Never accept a sorry silently.** Document it in an issue with: what's needed, why it's hard, and what would unblock it.

## Translation Pipeline

Formalizing an item follows three stages: **translate**, **scaffold**, **prove**.

### 1. Translate: Natural Language to Formal Statement

Read the item's blob text and its `.refs.md` file (Mathlib coverage + external sources). Then:

1. **Identify the Mathlib types.** Check `.refs.md` for exact/partial matches. For exact matches, use the Mathlib declaration directly. For partial matches, read the Mathlib source to understand the gap.
2. **State the theorem/definition.** Write the Lean signature with `sorry` as body. Include a docstring with the book's natural language statement.
3. **Check it compiles.** Run `lake env lean <file>` — fix import and type errors before proceeding.

**Common pitfalls:**
- **No `-/` inside doc-comments.** A stray `-/` sequence in prose (e.g. writing `one-/two-sided`, or `f⁻¹/g`) closes the `/-! … -/` or `/-- … -/` block early, and the remaining text is parsed as commands — producing baffling "unexpected identifier; expected command" errors far from the real spot. Reword to `one- or two-sided`. Likewise avoid an accidental `/-` opening a nested comment.
- Don't invent type classes. If Mathlib doesn't have a concept, use a `structure` or `def` with explicit fields.
- Don't use `True` as a placeholder for propositions — it compiles but hides the real requirement.
- Check that universe levels are consistent. Representation theory often needs `Type*` not `Type`.
- **WF-recursive definitions** (`termination_by`): Don't use `rw [f]` or `simp [f]` to unfold — they fail on WF-recursive functions. Instead, prove a separate `have` using `unfold f` (works inside `conv` blocks), or extract a standalone unfolding lemma.
- **`Finset.prod`/`∏`-style products need `CommMonoid`.** `GL_N k`, `Matrix n n k`, and `Module.End` are non-commutative, so `∏ i, g i` over them does **not** typecheck (`failed to synthesize CommMonoid (GL …)`). For diagonal/torus elements that *do* commute, don't fight the typeclass: induct over the `Finset` with a partial helper (e.g. `diagTorusOn s` = the partial product over `s`, with `_empty`/`_insert`/`_univ` lemmas) and assemble one factor at a time via `map_mul`. See `Chapter5/FormalCharacterTorusTrace.lean`.
- **Diagonalizing a distinct-eigenvalue matrix (conjugate to a diagonal) — full recipe.** Mathlib has no "distinct eigenvalues ⟹ diagonalizable" shortcut; build the eigenbasis. The chain (over an alg-closed field, here `ℂ`): roots of `A.charpoly` ↔ eigenvalues via `Matrix.mem_spectrum_iff_isRoot_charpoly` + `Matrix.spectrum_toLin'` + `Module.End.hasEigenvalue_iff_mem_spectrum`; `0` is not an eigenvalue of a unit via `spectrum.zero_mem_iff` (**`R` is an explicit arg — write `(spectrum.zero_mem_iff ℂ).mp`, not `spectrum.zero_mem_iff.mp`**, else "unknown constant `…mp`"); one eigenvector per eigenvalue is linearly independent via `Module.End.eigenvectors_linearIndependent'` (needs an *injective* eigenvalue family); `N` independent vectors in `Fin N → ℂ` give a basis via `basisOfLinearIndependentOfCardEqFinrank` (**needs `[Nonempty (Fin N)]` — handle `N = 0` separately; `GL_0` is a `Subsingleton`, close with `Subsingleton.elim`**); the column matrix `V := (Pi.basisFun ℂ (Fin N)).toMatrix ⇑b` is invertible via `Basis.invertibleToMatrix`, and `A * V = V * diagonal eigenvalues` follows columnwise from the eigenvector equation (`A *ᵥ vⱼ = tⱼ • vⱼ`), giving `A = V * D * V⁻¹` (`Matrix.mul_inv_of_invertible`). Package `h := unitOfInvertible V` (GL is `abbrev … := (Matrix …)ˣ`, so `unitOfInvertible` *is* a GL element), prove the GL equation via `Units.ext` + `Matrix.GeneralLinearGroup.coe_mul`/`coe_inv`. **Dot-notation gotcha: `f.HasEigenvalue` fails (`LinearMap.HasEigenvalue` does not exist) when `f : … →ₗ[R] …`; annotate `f : Module.End R M` so dot notation resolves to the `Module.End.*` API.** Full worked proof: `Chapter5/DiagonalizableConj.lean` (`gl_conj_diagTorus_of_distinct_eigenvalues`).

### 2. Scaffold: Set Up the Proof Structure

Before attempting the proof:

1. **Read the book's proof sketch.** Identify the key steps and what facts they use.
2. **Check dependencies.** All items this proof depends on should be sorry-free (or admitted for now). If not, either work on those first or use `admit` temporarily.
3. **Outline the proof.** Use `sorry` for each major step:

```lean
theorem foo : statement := by
  -- Step 1: reduce to case X
  sorry
  -- Step 2: apply theorem Y
  sorry
  -- Step 3: algebraic manipulation
  sorry
```

### 3. Prove: Fill In Sorries One at a Time

Follow the global CLAUDE.md proof rules strictly:

1. **One tactic at a time.** Write one tactic, check diagnostics.
2. **Use `done` to see remaining goals.** Don't guess what the goal state is.
3. **Error priority:** syntax > type > unsolved goals > warnings.
4. **Stop at first error.** Don't continue writing tactics after an error.
5. **Hardest case first.** For case splits, sorry the easy cases and focus on the hard one.

### Private Abbreviation Gotcha

Multiple files define `private abbrev GL2 = ...` / `private abbrev GL2' = ...` for the same underlying type. When using lemmas across files, `rw`/`simp`/`show` may fail because the elaborator sees different abbreviation names. Workarounds:
- Use `have h := lemma_from_other_file ...` then `rw [h]` (let unification handle it)
- Use `change` instead of `show` when the target uses a different abbreviation
- For sorry'd lemmas that need `[Fintype F] [DecidableEq F]` instances (needed by callers and the sorry body): wrap in a `section` with `set_option linter.unusedFintypeInType false` / `set_option linter.unusedDecidableInType false`. The `set_option ... in` syntax doesn't work before `private`.

### Stuck `Module ?m (M i)` Metavariable Errors

When working over a *family* `(M : ι → Type*) [∀ i, Module A (M i)] [∀ i, Module 𝕜 (M i)] [∀ i, IsScalarTower 𝕜 A (M i)]` (common for representation families), `lake build` errors like `typeclass instance problem is stuck … (i : ι) → Module ?m (M i)` mean a ring/field implicit was left undetermined. Three concrete causes, each with a one-line fix (diagnosed across ~5 build cycles in #4885, `CharacterIndependence.lean`):

1. **An `abbrev`/`def` over the section `M` silently absorbs `M`'s instances.** `abbrev Pim : Type _ := ∀ i, M i` carries `[∀ i, Module A (M i)]` into its signature, so `Pim M` needs `A` — which `∀ i, M i` does not determine → stuck `Module ?A (M i)`. **Fix:** take a *fresh* type-family argument: `abbrev Pim (N : ι → Type*) : Type _ := ∀ i, N i`, then use `Pim M`.
2. **A helper `def proj … : Pim M →ₗ[A] Pim M` has an implicit `A` invisible at use sites.** When applied (`proj M j x`), neither the argument nor result type mentions `A`, so `A` is a free metavariable. **Fix:** pin it with a named argument everywhere — `proj (A := A) M j x`.
3. **A lemma statement / `LinearIndependent 𝕜 (fun i => f M i)` whose body doesn't pin `𝕜` or `A`.** Restating `Algebra.lsmul 𝕜 𝕜 (M i)` or `traceChar M i` standalone leaves the acting algebra/base field ambiguous. **Fix:** ascribe the codomain — `(traceChar M i : A →ₗ[𝕜] 𝕜)` — or route through a named `def repEnd (i) : A →ₐ[𝕜] End 𝕜 (M i)`.
4. **In-proof `set M := fun i => asModule (L i).ρ` blocks instance search.** Abbreviating a type family with `set`/`let` inside a proof makes `M i` an opaque local fvar, so `Module A (M i)` / `IsScalarTower` / defeq like `asModule (L i).ρ = ↥(L i).V` no longer resolve (instances are registered on the *unfolded* `asModule (L i).ρ`). Symptoms: `failed to synthesize Ring (G →₀ ℂ)` and unsolved `trace ℂ (M i) … = trace ℂ ↑(L i).V …` defeq goals. **Fix:** don't abbreviate — inline `(fun i => Representation.asModule (L i).ρ)` at every call site (a literal lambda beta-reduces during instance search; an fvar does not). This is how the existing `hLsimp`-style hypotheses are written. Diagnosed across 2 build cycles in #4908.

General rule: if an implicit type/ring/field appears only *inside* a definition's body (not in any argument or result type visible at the call site), pin it explicitly. Test a suspect term in isolation in `/tmp/foo.lean` — it compiles there when the surrounding context determines the implicit, which localizes the bug fast.

### `MonoidAlgebra` Ext: Don't Use `Finsupp.lhom_ext`

`MonoidAlgebra k G` is `def`-equal to `G →₀ k`, so `Finsupp.lhom_ext` *applies* to a goal `F = 0` for `F : MonoidAlgebra k G →ₗ[k] N` — but it unifies the domain with the bare `G →₀ k`, which pries the type open and breaks instance search for everything registered on `MonoidAlgebra` (`failed to synthesize Ring (G →₀ ℂ)` / `Algebra ℂ (G →₀ ℂ)` / `Module (G →₀ ℂ) (M i)`). **To show a linear functional on `MonoidAlgebra k G` vanishes**, keep the type intact: prove `∀ a, F a = 0` by `induction a using MonoidAlgebra.induction_on` (base case `of k G g` — exactly the group-element evaluation you have a bridge lemma for; `hadd`/`hsmul` close by `simp only [map_add, …]` / `simp only [map_smul, …]`), then package via `LinearMap.ext`. (#4908)

### `k`-trace lemmas on a group-algebra submodule need `restrictScalars k`

When generalizing a character/trace from `ℂ` to general `k` (the #4946 chain), the Specht-type
modules are left ideals `SpechtModuleK k n la = k[S_n]·c_λ` — i.e. a `Submodule (MonoidAlgebra k G) (MonoidAlgebra k G)`
(over the *algebra*), not a `Submodule k _`. Mathlib's `k`-trace lemmas (`LinearMap.trace_restrict_eq_of_forall_mem`,
`LinearMap.trace_baseChange`) require a `Submodule k M`, so passing the algebra-submodule leaves `p`/`q` stuck as
metavars. **Fix:** phrase the hypothesis and the `.restrict` over `(SpechtModuleK k n la).restrictScalars k` (same
carrier, so the action `→ₗ[k]` on `↥(SpechtModuleK …)` is defeq to the one on `↥(… .restrictScalars k)`); close the
final step with `exact` (which uses defeq) rather than `rw` (syntactic). Field-independence of such a trace then comes
cheaply: the idempotent `α⁻¹·c_λ` makes `χ(σ) = trace(L_σ ∘ R_{α⁻¹c}) = (N₀:k)⁻¹·(M₀:k)` with `N₀,M₀ ∈ ℤ` from the
ℤ-coefficients of `c_λ` (`YoungSymmetrizerZ` + `mapRangeRingHom`), so `χ_k = algebraMap ℚ k (χ_ℚ)` and ℂ injectivity
transfers. Worked example: `Chapter5/SpechtCharacterGeneral.lean` (#4991). Also: `set G := Equiv.Perm (Fin n)` where
`G` is *also* a binder's type duplicates the variable (`σ✝` vs `σ`) — write the type literally instead of `set`.

### Heavy Instance Resolves Abstractly but Fails Concretely

**A heavy instance (e.g. `centralizerModuleHom : Module ↥(centralizer …) (V →ₗ[A] E)`) that resolves for an *abstract* carrier `V` can fail fresh typeclass search for a *concrete* one (`V = Fin N → k`), at the same `synthInstance.maxHeartbeats` — it is structural, not a heartbeat shortfall (diagnosed across ~7 build cycles in #4860, `SchurWeylLDistinct.lean`).** Symptom: `failed to synthesize HSMul … ?m` (an `outParam` output stuck as a metavar) on a `•`/instance you wrote *freshly* in the concrete proof, while the *same* `•` typechecks when it comes from *specializing* a polymorphic lemma's signature. Two non-fixes and the fix:
- `haveI hI : Module … := …` registers the instance but makes it **opaque** — the `•` no longer reduces (`show (c • f) v = c.val (f v)` fails defeq), and it **shadows** the canonical instance so APIs expecting the canonical one mismatch.
- `letI hI := …` keeps it transparent (reduces) but **still shadows** — passing your term to a lemma whose signature used the canonical instance gives an "application type mismatch" unless your `letI` body is syntactically the canonical instance.
- **Fix:** never write the offending notation freshly in the concrete proof. (a) Obtain the goal *by specialization* — `refine polymorphicLemma … ?_` so the `•` in the `?_` goal is substituted from the lemma's signature, not searched. (b) Add an **abstract** `:= rfl` rewrite lemma over a general `V` (where the instance resolves), e.g. `theorem c_smul_eq (f) : c • f = (centralizerToEndA … c).comp f := rfl`, and `simp only [c_smul_eq]` in the concrete proof to eliminate the `•` entirely. The concrete proof then stays instance-notation-free.

### Tactic Selection Guide

| Goal Shape | Try First | Then Try |
|-----------|-----------|----------|
| `⊢ a = b` (algebraic) | `ring`, `field_simp; ring` | `simp`, manual `rw` |
| `⊢ a = b` (categorical) | `simp [CategoryTheory...]` | `ext`, `aesop_cat` |
| `⊢ P ∧ Q` | `exact ⟨..., ...⟩` or `constructor` | split into subgoals |
| `⊢ ∃ x, P x` | `exact ⟨witness, proof⟩` | `use witness` |
| `⊢ P → Q` | `intro h` | `fun h => ...` |
| `⊢ ∀ x, P x` | `intro x` | lambda |
| Finite group theory | `decide` (small groups) | case analysis |
| Linear algebra | `ext`, `simp [LinearMap...]` | `apply LinearMap.ext` |
| Module homomorphisms | `ext`, `simp` | manual composition |

### `rw`/`simp` fail to match Finsupp applications over `Tabloid` (Ch5 TabloidModule)

`Tabloid n la` is a `def` for `Quotient (TabloidSetoid n la)` (semireducible, NOT
reducible). `rw` and `simp only` match at *reducible* transparency, so when an
element `t` comes from `ext`/`Finset.ext` (typed `Quotient (TabloidSetoid …)`) a
Finsupp value `ψ t` produced by `Finsupp.smul_apply`/`sub_apply` is **not
syntactically equal** to a hand-written `ψ t` (or to a `ψ t = 0` from a lemma
whose binder is `: Tabloid n la`), even though they are defeq. Symptom: `rw [h]`
/`simp only [h]` reports "did not find pattern `ψ t`" or "unused" on a term that
visibly contains `ψ t`. This cost ~7 build iterations in #4998. Workarounds, in
order of preference:

1. **Introduce an explicit representative.** After `apply Finset.ext; intro t`,
   do `obtain ⟨a, rfl⟩ : ∃ a, toTabloid n la a = t := ⟨Quotient.out t, toTabloid_out t⟩`.
   Now every Finsupp application is over `toTabloid n la a`, which `rw` matches
   (this is why proofs like `twistedPolytabloid_per_q_decomp` that apply Finsupps
   to `toTabloid n la α` never hit the gremlin).
2. **Prefer `exact`/function application over `rw`.** Application typechecks up to
   defeq, so `exact h₁ h₂`, `hEq ▸ h`, and `Finsupp.support_smul hmem` work where
   `rw` fails. Reserve `rw` for terms you constructed yourself in the same goal.
3. **`show` to a hand-written / defeq form.** `Finsupp.smul_apply` is `rfl`, so
   `show c • ψ (toTabloid n la a) = 0` reaches a defeq goal whose hand-written
   `ψ (…)` then matches a `rw [hψ0]`; `show … ≠ 0` likewise re-normalizes a
   simp-mangled goal back so the next `rw` finds its pattern.

Separately: `Finset.le_sup`/`Finset.exists_mem_eq_sup` over a `ℕ`-valued
`f` need the `(f := fun t => …)` named argument, else instance resolution stalls
on `OrderBot ?m`.

### Assembling short exact sequences of `FDRep`s (Ch5 Cauchy det-quotient)

Feeding `formalCharacter_add_of_shortExact` (or any map between FDReps built as
`FDRep.of ρ`) hits three recurring defeq gremlins. Cost 4 build cycles in #5003
(`CauchyDetQuotientDegree.lean`, `quotDetDegreeFDRep_formalCharacter`); the
working pattern:

1. **The carrier `↑(FDRep.of ρ).V` does NOT accept a `(u : MvPolynomial …)`
   coercion.** SetLike isn't seen through the `FGModuleCat` wrapper, so
   `(u : MvPolynomial …)` fails with "type mismatch: ↑(twistFDRep …).V". Extract
   the underlying element with an explicit subtype map, like the existing
   `polyOf d := (homogeneousSubmodule …).subtype` (its `polyOf_rho` is `rfl`).
   Define one such `eU/eV/eW` per FDRep (ascribe its type `FDRep →ₗ[k] (ambient)`;
   the domain unifies by defeq) and state the action/inclusion facts as
   `rfl`-backed `have`s: `eU (M.ρ g u) = (ambient ρ) g (eU u)` and
   `eV (ι u) = mulDet (eU u)` are all `fun _ _ => rfl`, since `FDRep.of_ρ'`,
   `Subrepresentation.toRepresentation`, and `LinearMap.restrict` are definitional.
2. **`let`-bound maps hide `LinearMap.restrict` from `rw`.** `rw
   [LinearMap.restrict_coe_apply]` fails ("did not find pattern") when the map is a
   local `let ι := … .restrict …`, because the goal shows the opaque `ι`, not
   `restrict`. Don't rewrite with `restrict_coe_apply`; use the `rfl`-backed
   per-`let` `have`s from (1), and prove injectivity via
   `eU_inj := Subtype.coe_injective` then `apply mulDet_injective`.
3. **A term-mode `calc … := (lemma …).symm` over `glWeightSpace` of an FDRep can
   hang `isDefEq` (still timed out at 3.2M heartbeats).** Matching the calc's
   stated endpoint against the lemma's type triggers whnf of the FDRep carriers;
   if the weight-function arguments differ only by a beta-redex, Lean still unfolds
   the whole rep. Replace the `calc` with `rw [glWeightSpace_twistFDRep_pos …
   (fun i => …)]` supplying the weight **explicitly** (syntactic keyed matching, no
   whnf), then `congr 1; funext i; simp only [Finsupp.add_apply, …]; omega`. The
   SES assembly still needs `set_option maxHeartbeats` raised (~3200000) for the
   rank-nullity character argument even after these fixes.

### Dependent Pi Types and Pi.single

When working with `Pi.single` for dependent function types (e.g., `∀ i, Matrix (Fin (d i)) (Fin (d i)) k`), standard lemmas like `Pi.single_eq_same`, `Pi.single_add` do NOT work with `simp` because types differ across indices.

**Working pattern** — unfold to `Function.update` and manipulate `dite`:
```lean
ext t r s  -- go all the way to scalar level
simp only [Pi.single, Function.update, dite_apply, Pi.zero_apply, ...]
split
· next h => subst h; rfl  -- or simp
· simp  -- the ¬(i = t) case gives 0
```

Key insight: `ext t` alone leaves dependent casts (`⋯ ▸ x`). Go deeper with `ext t r s` to reach scalar goals where `subst` eliminates the cast.

### Representation Theory Patterns

This book covers:
- **Chapters 1-3:** Basic algebra (associative algebras, quivers, Lie algebras)
- **Chapters 4-6:** Representation theory fundamentals (representations, characters, tensor products)
- **Chapters 7-10:** Advanced topics (structure theorems, categories, Hopf algebras)

**Key Mathlib imports for this book:**
```
Mathlib.Algebra.Algebra.Basic
Mathlib.RingTheory.TensorProduct.Basic
Mathlib.Representation.Basic
Mathlib.Algebra.Lie.Basic
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.LinearAlgebra.TensorProduct.Basic
Mathlib.GroupTheory.GroupAction.Basic
```

**When Mathlib doesn't have it:** This is the most important work in the project — prove it here. Check the `.refs.md` file for the item. If coverage is "gap", build the definition and proof from scratch. These are the highest-priority items, not items to defer. If the book proves the result (or assigns it as an exercise with hints), follow the book's approach. If it's genuinely external mathematics, prove it anyway — that's what this project is for.

#### FDRep of a homogeneous polynomial component (Ch5 Cauchy/Schur-Weyl, #4934)

To state a `formalCharacter` identity on a degree-`d` piece of `A = k[Xᵢⱼ]` you
need that piece as an `FDRep`. Recipe (sorry-free):
- finite-dimensionality of `MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d`:
  it sits inside `MvPolynomial.restrictTotalDegree _ _ d` (a degree-`d`
  homogeneous poly has total degree `≤ d` via `IsHomogeneous.totalDegree_le` +
  `mem_restrictTotalDegree`), which is `Module.Finite` for finitely many vars —
  conclude with `Submodule.finiteDimensional_of_le`.
- package: take the existing `Subrepresentation` of the homogeneous component
  (e.g. `polyRightHomogeneousSubrep`, `PolyRightGrading.lean`), then
  `FDRep.of (subrep.toRepresentation)`. `FDRep.of` needs `[Module.Finite k V]`,
  which the `FiniteDimensional` instance supplies (defeq over a field).
- Gotcha: `open MvPolynomial` did **not** expose `homogeneousSubmodule` /
  `restrictTotalDegree` / `mem_restrictTotalDegree` in an `instance` signature
  under `relaxedAutoImplicit false` — fully qualify with `MvPolynomial.`.

The canonical Fintype indexing set for "dominant weights `ν ∈ ℕ^N` of size `d`"
is `BoundedPartition N d` (`Proposition5_21_1.lean`: antitone `ν : Fin N → ℕ`
with `∑ ν = d`; has `Fintype` + `DecidableEq`). Use it to write a
multiplicity-one decomposition as a single `Finset.sum`
(`∑ ν : BoundedPartition N d, schurPoly N ν.parts`) — each `ν` once = mult one,
no ad-hoc partition bookkeeping.

### `_kQ` rep `obj` projection does not reduce in signatures (sporadic tube family)

The per-(field, orientation) reps `<X>Rep_kQ` (`FieldGeneric{Star,D5/6/7Tilde,ETilde6/7,T125,Tube}.lean`) are built tactically: `noncomputable def … := by letI := Q; exact { obj := fun v => Fin (<X>Dim m v) → F, … }`. The structure projection `(<X>Rep_kQ …).obj ⟨v, _⟩` does **not** reduce to `Fin (k·(m+1)) → F` under the transparency that `Membership`-instance synthesis uses. Consequences when stating lemmas over the rep family `W : ∀ v, Submodule F ((<X>Rep_kQ …).obj v)`:

- A **top-level signature** with a concrete-element membership — `∀ (x : Fin (k·(m+1)) → F), x ∈ W ⟨v, _⟩ → …` — fails to elaborate (`failed to synthesize Membership (Fin … → F) (Submodule F ((…).obj ⟨v, ?⟩))`). Equalities/`≤` between two `W ⟨v⟩` only typecheck when the two vertices share a dim (e.g. the four dim-`(m+1)` leaves of the D̃ family); for distinct-dim vertices (e.g. T(1,2,5)) they don't.
- `(…).obj ⟨v,_⟩ = (Fin (<X>Dim m ⟨v,_⟩) → F) := rfl` ✓ (projection reduces with `<X>Dim` symbolic), but `… = (Fin (k·(m+1)) → F) := rfl` ✗ (the `<X>Dim` match won't reduce in the same step).

**Workarounds.** (1) State reusable arm/flag helpers over **explicit `Fin (k·(m+1)) → F` carriers** plus per-edge hypotheses (as `t125_prefix_sub` / `t125_canonical_collapse` do) — these elaborate cleanly. (2) Do the `W ⟨v⟩` → explicit-carrier bridge **inside a proof body**, where `simp only [<X>Rep_kQ, <X>RepMap_kQ]` unfolds the rep and concrete memberships elaborate at default transparency (this is why the local `core`/`leaf*_sub` haves inside `starTubeRepGen_isIndecomposable` work). Do not try to expose a rep-level `…_leaf_equalities` theorem whose *conclusion* carries concrete memberships; assemble that content in the consuming indecomposability proof instead.

### Direct sums / decompositions of `QuiverRepresentation` (Ch6, #4781)

Two gotchas bite anyone building iterated direct sums or decomposition results
(`DecompositionExistence.lean` is the reference; `exists_decomposition` is the
existence-of-decomposition-into-indecomposables workhorse).

1. **`obj` carries only `AddCommMonoid` — `FiniteDimensional` is ill-typed.**
   `Etingof.QuiverRepresentation.obj` bundles `AddCommMonoid` + `Module`, not
   `AddCommGroup`. So a hypothesis `[∀ v, FiniteDimensional k (V.obj v)]` does
   **not** elaborate (`FiniteDimensional` needs `AddCommGroup`). Use
   `[∀ v, Module.Finite k (V.obj v)]` instead (works over `AddCommMonoid`;
   `Module.finrank` is fine too). Where you genuinely need group structure
   (complements, `IsCompl`, `prodEquivOfIsCompl`, `finrank` additivity), add it
   locally and *only there*:
   `letI : ∀ v, AddCommGroup (V.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)`
   (it extends the bundled `AddCommMonoid`, no diamond). Under that `letI`,
   `FiniteDimensional k (V.obj v)` becomes defeq-derivable from `Module.Finite`,
   so `Submodule.finrank_add_eq_of_isCompl`, `Submodule.finrank_eq_zero`, and the
   submodule-`Module.Finite` instance all resolve.

2. **`directSum` returns obj-universe `max u₁ u₂` — pin the fold base to `Type 0`.**
   `Etingof.QuiverRepresentation.directSum.{…}` has `ρ₁ : QR.{…,u₄,…}`,
   `ρ₂ : QR.{…,u₅,…}`, result `QR.{…,max u₅ u₄,…}`. A `foldr`-based `directSumList`
   with a *universe-polymorphic* zero base (`obj := fun _ => PUnit`) therefore
   leaks a **free universe** (the base's `PUnit` universe stays an independent
   param, and unification fails with `directSumList.{…,?u}` mismatches). Fix: make
   the zero rep `obj := fun _ => PUnit.{1}` (concretely `Type 0`) and state the
   decomposition theorem at obj-universe `0`
   (`QuiverRepresentation.{uk, 0, 0, uh} k (Fin n)`). Then `max u 0 = u` collapses
   cleanly and `directSumList` is monomorphic. Obj-universe `0` is exactly what the
   orbit-counting application needs (`V.obj v ≃ Fin (d v) → k`). Tie `V` and the
   existential summand list to the **same** explicit universes, or the witness
   `[V]`/`L₁ ++ L₂` fails with a `List.cons` universe mismatch.

   Defeq-but-not-syntactic `(subRep …).obj v` ↦ `↥(W v)`: `rw [subRep_obj]` in a
   `finrank` goal triggers a "motive is not type correct" (the `AddCommMonoid`
   instance depends on the rewritten term). Use `change`/`show` to the reduced
   form (defeq) or `simp only [subRep_obj]` instead of `rw`.

## Scaffolding Anti-Patterns

These patterns were discovered during Chapter 2 and 7-8 reviews. Avoid them in all scaffolding work.

### Never sorry a Type

```lean
-- BAD: sorry'd type breaks all downstream usage
noncomputable def Etingof.PathAlgebra ... : Type* := sorry

-- GOOD: define carrier concretely, sorry the algebraic instances
def Etingof.PathAlgebra ... := FreeModule k (Quiver.Path ...)
instance : Algebra k (Etingof.PathAlgebra ...) := sorry
```

A sorry producing `Type*` gives `sorryAx Type*` — no instances can be built on it. Define the carrier type concretely and sorry the structure instances.

### Don't alias only the carrier type

```lean
-- BAD: misses the Lie module structure (the actual content of the definition)
abbrev Etingof.LieTensorProduct ... := TensorProduct k V W

-- GOOD: alias and import the relevant instance
import Mathlib.Algebra.Lie.TensorProduct
abbrev Etingof.LieTensorProduct ... := TensorProduct k V W
-- The Lie module instance is provided by the import
```

When a definition is about *structure on a type*, the alias must capture the structure, not just the carrier.

### Don't scaffold definitions as theorems

```lean
-- BAD: book definition scaffolded as theorem
theorem Etingof.Definition_8_2_3 : (sorry : Prop) := sorry

-- GOOD: use def/abbrev for definitions
noncomputable def Etingof.TorFunctor ... := sorry
```

Use `def`/`abbrev`/`noncomputable def` for definitions, `theorem`/`lemma` for propositions.

### Don't write tautological examples

```lean
-- BAD: proves nothing
example (A : Type*) [Ring A] : (1 : A) = 1 := rfl

-- GOOD: demonstrate actual properties
example (A : Type*) [Ring A] (a : A) : 1 * a = a := one_mul a
```

### Verify blob content before scaffolding

If a blob file is empty, flag it rather than scaffolding from the title alone. Title-only scaffolding produces low-quality formalizations.

### Use minimal imports

Prefer the most specific Mathlib module. Don't import `Mathlib.LinearAlgebra.DirectSum.Finite` when `Mathlib.Algebra.Module.Prod` suffices.

### Verify "import-cleanliness" with a real transitive trace, never a grep or an agent claim

When a task requires a file to avoid some module (e.g. the Chapter 5 `DetInvElim`-clean work for #5072/#5075/#5078: a file must NOT transitively import `DetInvElim`, else it creates a build cycle), do not trust a direct-import grep or a subagent's pollution claim — both miss/invent transitive edges. An Explore agent confidently mis-reported `FormalCharacterTorusTrace` as importing `DetInvElim` when it does not; a real trace caught it. Compute the transitive closure yourself before relying on it:

```bash
python3 - <<'PY'
import os, re
root="EtingofRepresentationTheory"; imports={}
for dp,_,fs in os.walk(root):
    for f in fs:
        if f.endswith(".lean"):
            mod="EtingofRepresentationTheory"+dp[len(root):].replace("/",".")+"."+f[:-5]
            imports[mod.replace("..",".")]=[m.group(1) for line in open(os.path.join(dp,f))
                if (m:=re.match(r'^import (EtingofRepresentationTheory\.[\w.]+)',line))]
def trans(s,seen=None):
    seen=seen or set()
    for d in imports.get(s,[]):
        if d not in seen: seen.add(d); trans(d,seen)
    return seen
target="EtingofRepresentationTheory.Chapter5.<File>"
print([x for x in trans(target) if "DetInvElim" in x] or "CLEAN")
PY
```

The lemma you need may live in a *polluted* file even though its own proof is clean (this is common — additivity/weight-space helpers stranded in files that import `DetInvElim` for unrelated reasons). The fix is to **relocate the clean statement+proof into a new file importing only clean ancestors**, leaving the polluted original in place; verify the new file with the trace above.

### Match Mathlib's generality for type class assumptions

If Mathlib uses `[Semiring R]`, don't restrict to `[CommRing R]`. Use the same or a compatible assumption. Within a chapter, be consistent — don't use `[CommRing R]` in one definition and `[Ring R]` in the adjacent one.

## Scaffolding Review Checklist

When reviewing scaffolded files, check each item against this list:

1. **Compilation**: `lake build <module>` passes with only expected sorry warnings
2. **Lean↔Blob↔items.json alignment**: every items.json entry has a .lean file and a blob file, no orphans
3. **Mathlib alias correctness**: `#check` the referenced declaration, verify it exists and is non-deprecated
4. **Type class consistency**: assumptions match Mathlib's (or are intentionally more specific with documented rationale)
5. **Anti-pattern scan**: no sorry'd types, no carrier-only aliases, no definitions-as-theorems, no tautological examples
6. **Import minimality**: imports are the most specific Mathlib module needed
7. **Doc-string quality**: matches the blob text, identifies Mathlib correspondence
8. **Gap definitions**: carrier type is concrete (not sorry'd), instances are sorry'd

Write findings to `reviews/<chapter>-scaffolding-review.md` with per-file scores and systematic pattern analysis.

## Quality Checks

Before submitting a PR for a formalized item:

1. **`lake env lean <file>` passes** — no errors
2. **No `sorry` remaining** in the target item (sorry in dependencies is OK)
3. **No `admit`** anywhere in committed code
4. **Docstring present** with book's natural language statement
5. **Imports are minimal** — only import what's actually used
6. **No duplicate declarations** — search for the declaration name across all files before adding. Duplicate names (even private ones) cause CI failures when files are compiled together. PRs #1655, #1657 were CI fixes for this exact issue.
7. **Heartbeat budget** — if your proof uses heavy `decide`, `omega`, or trace computations, test with the CI heartbeat limit. Use `set_option maxHeartbeats N in` to increase locally if needed. Guidelines:
   - **≤ 400000**: Normal, no annotation needed
   - **400000–800000**: Acceptable for trace/character computations over finite groups. Add a comment explaining why.
   - **800000–1600000**: Borderline. Acceptable only for GL₂(𝔽_q) trace computations or similar unavoidable large finite sums. Must have a comment. Consider whether `simp` can be replaced with targeted `rw` to reduce heartbeats.
   - **> 1600000**: Refactor the proof. Extract helper lemmas, precompute intermediate results, or use `native_decide` for finite checks.
   - **Placement:** `set_option ... in` lines must come *before* the `/-- ... -/` docstring (the docstring must sit immediately above `theorem`/`def`). Putting the docstring first gives `unexpected token 'set_option'; expected 'lemma'`. The **same rule applies to `omit [Inst] in`** (used to drop an auto-included-but-unused section variable, e.g. `omit [CharZero k] in`; the linter's "automatically included section variable unused" warning names exactly which instances to omit): it must precede the docstring, else `unexpected token 'omit'; expected 'lemma'`.
   - **`whnf` timeout despite a high budget** usually means Lean is eagerly reducing through a *non-reducible* coercion (e.g. an `FDRep`/`FGModuleCat` carrier identified with a hom-space, re-typed mid-proof via `let e' := e`). Fix it by paying that coercion *once* in a helper theorem whose output is already stated in the target type, then consume the result opaquely — do not re-coerce inside the heavy proof.
   - **`whnf` timeout through a `Quotient.liftOn'` definition** (e.g. `MulAction.orbitRel.Quotient.orbit`, relevant to the Ch6 orbit-counting chain #4777). Proving a membership like `a ∈ (Quotient.mk'' a).orbit` via `orbitRel.Quotient.mem_orbit.mpr rfl` forces Lean to whnf-unfold the `liftOn'` and blows the heartbeat budget for a one-line goal. Fix: don't lean on defeq — rewrite with the `_mk` simp lemma first (`rw [orbitRel.Quotient.orbit_mk]`, turning the quotient orbit into `MulAction.orbit G a`), then close with the plain-orbit API (`mem_orbit_self`). Also pin the quotient index explicitly (`Set.mem_biUnion (Set.mem_univ (Quotient.mk'' a)) …`) rather than letting unification infer it through the `liftOn'`. With both, the proof drops back under the default 200000 budget.
   - **Pushing an `AlgEquiv`/`RingEquiv` through `Polynomial.eval₂`/`aeval`** (e.g. the scaling-action transcendence argument in `Problem6_1_5_StrictDimBound`, #4828). To rewrite `(e : K ≃ₐ[k] K) (eval₂ f x p)` with `Polynomial.hom_eval₂` (which is stated for a bare `RingHom`), first bridge the coercion: `rw [show (e) (eval₂ f x p) = e.toRingHom (eval₂ f x p) from rfl]`, then `rw [Polynomial.hom_eval₂]`. The `⇑e` vs `⇑e.toRingHom` coercions are defeq, so `show … from rfl` matches — but an ascribed `(rfl : … = …)` does **not** match under `rw` (it fails to find the pattern). Express `aeval` as `eval₂` first via `Polynomial.aeval_def`. CI runs only `lake build` (no separate linter), so the `show`-tactic style warning on the `from rfl` term is harmless.

## Issue Sizing for Formalization

Based on Phase 2 experience with issue sizing:

- **Definitions:** 1-3 per issue (fast, low risk)
- **Easy theorems** (direct application of Mathlib): 2-5 per issue
- **Medium theorems** (multi-step proofs): 1-2 per issue
- **Hard theorems**: 1 per issue
- **Never mix difficulty levels** in one issue — a hard theorem blocks the easy ones

### Verify cited "model" files actually close the analogous case

When an issue says "mirror the proven branch in sibling file X" or "models: Y, Z",
**grep the cited file for `sorry` at the analogous declaration before assuming the
branch is tractable**. In the D̃-family tube work (#4692) the issue cited D̃₆
(`FieldGenericD6Tilde.lean`) and T(2,2,2) as models for the mixed-direction
(combo C/C′) and central-reversed leaf-equality branches — but D̃₆ carries the
**same five branches still `sorry`**, and no tube member had closed a mixed
combo-C branch anywhere. A branch that is unsolved across *every* sibling is
frontier-difficulty regardless of how the issue frames it. In that case prefer
landing reusable infrastructure plus a documented reduction (e.g. combo C′
reduces exactly to leaf `Λ`-invariance, the indecomposability crux) over a
heroic full-closure attempt, and partial-PR. Confirm the tractability premise
early — it sets scope and avoids rediscovering the obstruction from scratch.

### Before creating a NEW named file, re-fetch main — concurrent sessions land it too

Skill #4853 ("verify cited 'already-landed' deps exist") has a twin failure mode:
the artifact you are about to **create** may already exist on `main`, landed by a
**concurrent** session while you worked. If your branch base is several commits
behind, `git fetch origin main` and check before you write `Chapter5/Foo.lean` —
especially for a planned/obvious filename the whole pod is converging on. In
#4695's kernel-lemma (K) assembly, a worker built `Chapter5/KernelLemmaK.lean`
from scratch, then on rebase found `main` already had a complete sorry-free
`KernelLemmaK.lean` from a sibling session; the entire branch (plus a follow-up
issue resting on a gap the landed version sidestepped) was redundant and got
closed. Cheap guard: `git fetch origin main && git show origin/main:<intended
path>` (or `git log origin/main --oneline -15` for the area) right before the
first `Write` of a new file. If it exists, build *on* it, not beside it. Bonus:
the landed version often reveals a cleaner formulation — there, stating (K) over
explicit **weight-vector generators** (each in a single `glWeightSpaceℤ`) made the
descent need no torus-semisimplicity of `O`, which the abstract-submodule framing
had wrongly demanded.

### "Residual sorry" issue whose file isn't on main yet — prove the lemma in its home, don't skip

A `... residual` issue often quotes a sorry'd theorem "in `Chapter5/FooAssembly.lean`"
and gives a `lake build ...FooAssembly` verification — but that file ships with a
**sibling PR still in progress** (claimed, no PR), so it does not exist on `main`.
Do **not** `coordination skip` as "stale": the *deliverable* is the lemma's proof, and
the lemma is almost always a standalone, reusable fact. Prove it in its natural
building-block home (the file where its subject and ingredients live — e.g.
`schurPoly_coeff_self_ne_zero` belongs in `Proposition5_21_1.lean` beside `schurPoly`,
`schurPoly_mul_vandermonde`, `alternant_coeff_kronecker`), with the **exact signature**
the issue quotes. The eventual assembly imports that home transitively
(`KernelLemmaKPrime` → `Theorem5_22_1` → `Proposition5_21_1`), so when the sibling PR
lands it deletes its sorry'd copy and calls your lemma. Note this hand-off in the PR
body and progress file. (#4949: proved sorry-free in `Proposition5_21_1.lean` while the
consuming `KernelLemmaKPrimeAssembly.lean` from #4923 was unlanded.) Watch for name
collision: use the issue's exact theorem name so the sibling references rather than
re-declares it.

### Adding a hypothesis the consumer must supply: check the import direction first

When an issue says "add hypothesis `h` to lemma `L`, the consumer supplies it",
verify *before* editing `L`'s signature that the term the consumer will pass is
reachable **without an import cycle**. A *property* lemma (`X_isAlgebraic`,
`X_isSimple`, `X_isPolynomial`, …) is usually defined **downstream** of the object
`X` it describes — but the consumer of `L` often lives in the same upstream file
where `X` itself is defined, so it cannot import the downstream property. The plan
will read as if `h := X_property` is a one-liner; it is an import cycle. Fix by
extracting the *general* infrastructure the property is built from into an upstream
file and proving the consumer's instance **inline**; leave only the concrete
packaging downstream. (#4882: `iso_of_formalCharacter_eq_schurPoly` gained `halg`,
but `detTwistedSchurModuleRep_isAlgebraic` lives in `DetTwistAlgebraic`, which
imports `Proposition5_22_2` — where both the consumer *and* `detTwistedSchurModuleRep`
live — a cycle. Resolved by extracting `GLRepAlgebraic.lean` with the reusable
`glTensorRep_isAlgebraic` / `.restrict` / `.detTwist` and building `halg` inline.)
A second, related trap in the same issue: a plan step asserted "the simple summand
`≅ L_λ` at the asModule level" as if free, but the existing classification exposes
only *characters*, not the iso — that step needed a strictly stronger (deferred)
lemma. Treat every "obviously follows" step in a plan as a claim to check against
an actual existing declaration before committing to a sorry-free target.

**Generalizing a ℂ lemma "in place" when its general-`k` support is downstream:
put the general version in a NEW downstream file, don't edit the ℂ file.** A plan
that says "lift `foo` (ℂ) to general `k` in `FooFile.lean`" is mis-scoped whenever
`foo`'s proof needs general-`k` infrastructure (`SpechtModuleK_isSimpleModule_general`,
`Theorem5_12_2_distinct_general`, `youngSymmetrizerK_annihilates_specht`, …) that
lives in files which *import* `FooFile.lean` — editing in place is an import cycle.
When the generalized lemma is **not itself consumed upstream** (only by a still-later
assembly), the cleanest fix is a new *downstream* file importing both `FooFile.lean`
and the general-`k` machinery; leave the ℂ original untouched. The "already generic"
helpers in `FooFile.lean` (e.g. `trace_youngSymEndomorphism_restrict_eq_sum`,
`youngSymEndomorphism_restrict_sq_scalar`) still apply by proof-irrelevance even when
your `.restrict` supplies a different (defeq) membership proof, so you can re-state the
theorems verbatim. Working over `k` throughout often *removes* ℂ-specific helpers (the
ℚ→ℂ base-change `youngSym_sq_ℂ'` / `youngSymmetrizerK_complex_eq` vanish — the scalar
comes straight from `YoungSymmetrizerK_sq_scalar k`). To stay independent of a sibling
"general-`k` character" PR you can't import yet, define a local Specht character
(`spechtBlockCharacterK := trace of left-mult-by-`of σ` on `SpechtModuleK`) that is
*definitionally equal* to the bridge's `spechtModuleCharacterK`, so the eventual
consumer reconciles `h_label` by `rfl`. (#5004: `SchurWeylSpecialBlockGeneral.lean`,
the two `youngSym_action_*_general` lemmas — built first try this way.) **Check the
import DAG of the support lemmas before writing any code; don't discover the cycle
after editing the ℂ file.**

**Multi-block tubes: don't fix the `_leaf_equalities` *statement shape* ahead of
the center-collapse design.** For the ≥3-arm / >2-block-center tubes (Ẽ₆ #4638,
Ẽ₇ #4746, and the entangled D̃₅ #4743) the eigenvalue site is a **separate
vertex** (not a leaf) mapping to *all* center blocks, while the deep flag leaves
reach only the edge blocks (Ẽ₇: leaf-4→block 0, leaf-7→block 3; interior blocks
1,2 come only from the flag *intermediate* vertices). So N-invariance on the
common `F^{m+1}` cannot be read off one leaf — it must be derived **jointly** with
the flag collapse, and a center-core decomposition needs the intermediate
vertices' W-spans. Stating `…_leaf_equalities` with a guessed conclusion first
risks an *un-derivable* statement (the d5tilde #4743 outcome). Build the concrete
center-core primitive first, fix the conclusion shape from it, then prove
leaf-equalities and `_isIndecomposable` jointly. The mechanical eigenvalue
readout (e.g. `etilde7_arm1Tube_blockProj_F`: the four block projections of the
arm-1 tube = `(p+q, p+Λq, p+Λ²q, p+Λ³q)`) is the reusable piece to land first.

**Star `_leaf_equalities`: the non-canonical *orientation* branches fold too —
they are not the mechanical d5/d6tilde reversed-leaf pattern.** For a *star*
(Ẽ₆ #4701, Ẽ₇ #4769) the conclusion `W₁⟨leafᵢ⟩` all-equal couples every arm
through the single shared center, whose composite planes pairwise overlap.
Reversing an arm edge only swaps an embed criterion for a projection criterion;
it does **not** decouple the arms, so every orientation branch hits the *same*
overlapping-plane center-collapse wall as the canonical branch and folds into
`…Rep_kQ_isIndecomposable`. The d5/d6tilde reversed-leaf branches close only
because those are *chains* with one central γ-tube (combo-D reads reversed leaves
off one shared block) — no analog exists for the star. So an issue framed as
"close the non-canonical branches by mirroring d6tilde" is mis-scoped: grep the
canonical branch first; if its center collapse is already re-scoped to the
indecomposability fold (e.g. #4750/#4765 left `hcenter` as a documented `sorry`),
the reversed branches inherit it. Re-scope via a doc PR (`--partial`) rather than
attempting closure.

## Proven Proof Strategies

Patterns that have succeeded in this project, derived from 110+ merged proof PRs (through wave 20).

### Mathlib Alias Pattern (Chapter 2)

When a book definition matches a Mathlib concept exactly, use a simple alias:

```lean
/-- Definition 2.1.1: An associative algebra over k. -/
abbrev Etingof.Algebra (k : Type*) [CommRing k] (A : Type*) := Algebra k A
```

This pattern covered 19/25 Chapter 2 definitions. Check `.refs.md` — if coverage is "exact match", alias first, prove later. Don't build custom definitions when Mathlib already has the concept.

### Type Class Instance Examples

For "example" items that demonstrate a type satisfies a definition, use `inferInstance`:

```lean
/-- Example 2.2.1: M_n(k) is an algebra. -/
instance : Algebra k (Matrix (Fin n) (Fin n) k) := inferInstance
```

This compiles cleanly when Mathlib already provides the instance. Check with `#check` first.

### Module-theory instance gotchas (semisimple / submodule work)

Two traps recur when using Mathlib's `IsSemisimpleModule` / `IsSimpleModule` API:

- **`List.TFAE.out` chokes on named type args.** Writing
  `(IsSemisimpleModule.finite_tfae (R := R) (M := X)).out 0 1` fails with
  "type class instance expected". Instead let the *goal type* drive inference
  exactly as Mathlib does internally:
  `haveI : IsNoetherian R X := (IsSemisimpleModule.finite_tfae.out 0 1).mp ‹_›`
  (TFAE order is `[Module.Finite, IsNoetherian, IsArtinian, IsFiniteLength, …]`).
  The `‹_›` finds the source instance; the `M` is unified from the goal.

- **AddCommGroup vs AddCommMonoid diamond on `↥(submodule)`.** Transferring
  simplicity along an equiv with `IsSimpleModule.congr e` can fail with an
  AddCommMonoid mismatch (`p.addCommGroup.toAddCommMonoid` vs `p.addCommMonoid`)
  when one side is a submodule type. Use `(LinearEquiv.isSimpleModule_iff e).mp`
  instead — it sidesteps the re-synthesis that triggers the diamond.

- **`sub_mem` fails on `QuiverRepresentation` submodules.** The `obj v` carriers
  of `Etingof.QuiverRepresentation` (Chapter 6 indecomposability proofs) are
  wired with `instAddCommMonoid` only, so `Submodule.sub_mem` on a `W v` errors
  with an opaque application-type-mismatch (the `p` metavar never unifies). Mirror
  the established `core` pattern in `FieldGenericStar.lean`: build subtractions as
  `(W v).add_mem h ((W v).smul_mem (-1 : F) h')` and discharge the algebraic
  identity pointwise (`ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring`).
  Relatedly, when introducing a center vector for `eq_bot_iff`, annotate its type
  (`intro (w : Fin (2*(m+1)) → F) hw`) — an under-determined `w` cascades into
  spurious "No goals"/type-mismatch errors downstream. Keep `⟨i, by omega⟩` Fin
  literals (not `(i : Fin 5)`) so the `mapLinear`/`starRepMap_kQ` match reduces
  definitionally for `change`/defeq steps.

- **Upgrading a `k`-linear bijection to an `A`-linear equiv: prove `map_smul`
  on the composite, do NOT transport the `A`-module (Ch5, #4926 biduality).**
  When the target is `↥S ≃ₗ[A] ↥T` but the natural maps factor through a
  hom-of-hom space `D := (↥S →ₗ[A] E) →ₗ[C] E` whose only canonical action is by
  `↥(centralizer C)` (= `A` by double-centralizer), resist putting an
  `A`-module on `D` via `Module.compHom`/scalar transport — the `map_smul`
  obligations then force you to unfold `compHom` everywhere and the elaboration
  is brutal. Instead: build *all* intermediate equivs `k`-linearly (the
  curried-evaluation `↥S ≃ₗ[k] D` via `LinearEquiv.ofInjectiveOfFinrankEq`, the
  precomposition via the already-`k`-linear `homCongrLeftOverSubring`), thread
  them to a `Φ : ↥S ≃ₗ[k] ↥T`, then package the *final* `↥S ≃ₗ[A] ↥T` with the
  explicit constructor `{ toFun := Φ, map_add' := Φ.map_add, invFun := Φ.symm,
  left_inv := Φ.left_inv, right_inv := Φ.right_inv, map_smul' := fun a v => ... }`
  and prove the lone `A`-`map_smul'` by hand (`apply (last equiv).injective; ext;
  rewrite the definitional apply-formulas`). The double-hom space never needs an
  `A`-module structure at all. Bonus: isolate the genuine content as a *pure
  `k`-finrank* lemma (`finrank k ↥S = finrank k D`) whose statement mentions no
  exotic module — clean to state and to attack separately.
- **`centralizerModuleHom` firing twice needs an `IsScalarTower` companion
  (Ch5, #4926).** To get `Module ↥(centralizer C) ((V →ₗ[A] E) →ₗ[C] E)` you
  re-apply `Theorem5_18_1.centralizerModuleHom` with `C` in the `A`-slot; this
  requires `IsScalarTower k ↥C (V →ₗ[A] E)`, which is NOT automatic. Provide it
  (`smul_assoc r b f := LinearMap.ext fun v => by change (r•b).val (f v) = …;
  rw [Subalgebra.coe_smul, LinearMap.smul_apply]`). Note: even *stating* this
  instance (its `SMul` in the signature) overruns the default 20000 synth
  heartbeats — bump `synthInstance.maxHeartbeats` on the instance itself.
- **Bundled instances from a destructured existential are already usable — do
  NOT re-`haveI` them (Ch5, #4716).** Decomposition theorems
  (`glTensorRep_..._decomposition...`) return `∃ (S : ι → Type u)
  (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module k (S i)) …`. After
  `obtain ⟨…, S, hSacg, hSmod, hSfin, …⟩`, those hypotheses are automatically
  local instances: `Module k (S i)`, `S i ⊗[k] (L i)`, `trivial k G (S i)`
  all resolve with no `haveI`. Pitfalls that cost real debugging time:
  - The anonymous form `haveI := hSmod` for a *Pi-quantified* instance can fail
    to register a usable instance. Always use the type-ascribed form
    `haveI iSmod : ∀ i, Module k (S i) := hSmod` — or, better, just rely on the
    `obtain` hypotheses directly and add nothing.
  - Re-introducing an instance that already exists (e.g. `haveI iSacg : ∀ i,
    AddCommGroup (S i) := hSacg` when `hSacg` is in scope) creates a *competing*
    instance term; later `Module k (S i)` picks the new one while the source
    hypothesis still carries the old one, producing `AddCommGroup`-diamond
    type-mismatches.
  - Symptom of getting this wrong: a cascade of misleading
    `failed to synthesize Module k (S i)` errors plus a `(deterministic)
    timeout at whnf` (the fallback global instance search is what blows the
    heartbeats — bumping `maxHeartbeats` does NOT fix it, fixing the instance
    setup does). Only `haveI` instances that are genuinely *missing*, e.g.
    `Module.Free` over a field: `haveI : ∀ i, Module.Free k (S i) :=
    fun i => Module.Free.of_divisionRing k (S i)`. For a `Type 0` basis index
    (needed when the result type demands `Type`, not `Type u`), use
    `Fin (Module.finrank k (S i))` with `Module.finBasis k (S i)`.

### Proving `IsAlgebraicRepresentation` (Ch5 §5.23, #4756)

`detTwistedSchurModuleRep_isAlgebraic` (`Chapter5/DetTwistAlgebraic.lean`) is the
first algebraicity proof for a concrete rep, and ships **three reusable lemmas** —
reach for these before re-deriving for any other `GL_N` rep (e.g. bare
`schurModuleRep`, `glTensorRep`, further twists):

- `glTensorRep_isAlgebraic` — the diagonal action is algebraic; matrix coefficient
  in `tBasisAlg` is the monomial `∏ₘ X_{(h m, f m)}`.
- `IsAlgebraicRepresentation.restrict (W) (hW)` — restrict to a `ρ`-invariant
  submodule. (`schurModuleRep` algebraicity falls out as the intermediate step.)
- `IsAlgebraicRepresentation.detTwist` — twist by the `det` character.

Plus `evalAtGL_{mul,sum,prod,C,X_inl}`: `evalAtGL g` is `MvPolynomial.eval σ`, a
ring hom, so it commutes with `*`/`∑`/`∏`/`C`; prove each by
`simp only [Etingof.evalAtGL, map_mul]` etc. The det polynomial is `detPolyGL`
(det of the generic `(Xᵢⱼ)` matrix); `evalAtGL g detPolyGL = det g` via
`RingHom.map_det`.

Three API gotchas that cost build cycles here:
- **Tensor-basis coefficients:** `Basis.piTensorProduct_repr_tprod_apply` gives
  `(piTensorProduct b).repr (⨂ₜ x) p = ∏ i, (b i).repr (x i) (p i)` — the clean way
  to read a coefficient of `PiTensorProduct.map f (tprod …)`.
- **`Matrix.col` has no `col_apply`.** `M.col j = Mᵀ`, so `(M.col j) i` is
  *definitionally* `M i j` (via `transpose`/`of_apply`). After
  `rw [Matrix.mulVec_single_one]` just close the entry goal with `rfl`, not a
  `col_apply` simp (which does not exist).
- **`Basis.repr_reindex_apply` needs full qualification** as
  `Module.Basis.repr_reindex_apply` (and `Module.Basis.reindex_apply`); the bare
  `Basis.`-prefixed forms fail to resolve. Use these to fit a non-`Fin`-indexed
  basis (e.g. `tBasisAlg : Basis (Fin n → Fin N)`) into the `Fin m`-indexed
  `IsAlgebraicRepresentation` predicate by reindexing through `Fintype.equivFin`.
- **`let` not `set` for locals whose *defeq* you rely on** (here a projection `π`
  and the functional `φ y = b'.repr (π y) a`): `set` introduces an *opaque* local,
  so terms like `linearProjOfIsCompl_apply_left` (which mention the unfolded
  expression) no longer typecheck against it, and `fun _ => rfl` proofs break.

- **GL-element inverse coercion to `Matrix` is ambiguous — annotate, or use `.val`.**
  Writing `((g i)⁻¹ : Matrix _ _ k)` for `g i : GL (Fin p) k` (e.g. the base-change
  action `g j · M · (g i)⁻¹` in `Problem6_1_5_OrbitSpace.lean`) elaborates with
  unresolved metavariables and times out typeclass synthesis: Lean cannot decide
  between *GL-inverse-then-coerce* and *coerce-then-`Matrix.inv`*, and the `_ _`
  dimensions never pin down. Write `(↑(g i)⁻¹ : Matrix (Fin p) (Fin p) k)` with the
  coercion arrow **and** explicit dimensions, or `(g i)⁻¹.val`. Then the GL coe lemmas
  (`Matrix.GeneralLinearGroup.coe_mul/coe_inv/coe_one`) drive the proofs, and
  `(↑g)⁻¹ * ↑g = 1` comes via `← coe_mul; (mul_inv_cancel/inv_mul_cancel); coe_one`.
  To turn a vertex `≃ₗ` into a `GL` element, build the `Units` directly
  (`⟨toMatrix' e, toMatrix' e.symm, _, _⟩`, val/inv discharged by `← toMatrix'_comp`,
  `e ∘ₗ e.symm = id` via `ext; simp`, `toMatrix'_id`) — its coe to `Matrix` is then
  `rfl`-equal to `toMatrix' e`, which makes the orbit↔iso intertwining a clean
  `toMatrix'`/`toLin'` round-trip. Rectangular matrices need `Matrix.mul_one`/
  `Matrix.mul_assoc`, **not** the monoid `mul_one`/`mul_assoc`.

- **`DirectSum ι L` semisimple/finite instances** resolve through the `Π₀`
  (`DFinsupp`) instances: `inferInstanceAs (IsSemisimpleModule R (Π₀ i, L i))`.
  `DirectSum.lof R ι L i` is *defeq* to `DFinsupp.lsingle i`, so its injectivity
  comes from `DirectSum.component.lof_self` (a left inverse) and the coordinate
  lines span via `DFinsupp.iSup_range_lsingle`.

- **Transferring `IsSimpleModule` across a `Subalgebra` equality of acting rings**
  (recurs in Schur-Weyl: `diagonalActionImage = centralizer(symGroupImage)` via
  `Theorem5_18_4_centralizers`). The two `↥A`-module structures are over
  *propositionally* equal subalgebras, so there is no shared-ring `LinearEquiv`.
  Route: `φ := (Subalgebra.equivOfEq _ _ h).toRingEquiv`, build a `φ.toRingHom`-
  **semilinear** equiv `e : ↥M₁ ≃ₛₗ[φ.toRingHom] ↥M₂` (often the carrier-identity
  map — both submodules' carriers are defeq, both smuls are `b.val • x.val` and
  `(φ a).val = a.val` defeq, so `toFun/invFun = fun x => ⟨x.val, _⟩` and
  `map_add'/left_inv/right_inv = rfl`; `map_smul'` closes with
  `Subtype.ext` + the smul-coe lemmas + `SetLike.val_smul` then `rfl`). Then
  `Submodule.orderIsoMapComap e : Submodule R₁ M₁ ≃o Submodule R₂ M₂` and
  `(…).isSimpleOrder_iff.mpr h.toIsSimpleOrder`. Two gotchas: (1) **`RingHomInvPair
  φ.toRingHom φ.symm.toRingHom` is NOT a Mathlib instance for a `RingEquiv`** —
  provide both directions locally (`haveI : RingHomInvPair … := ⟨by ext x; simpa
  using φ.symm_apply_apply x, by ext x; simpa using φ.apply_symm_apply x⟩`), else
  the `≃ₛₗ` and `orderIsoMapComap` fail to synthesize. (2) `IsSimpleModule` is a
  *class extending* `IsSimpleOrder` (not defeq) — rebuild with
  `exact { toIsSimpleOrder := hso }`, and pin the semilinear ring hom explicitly
  (`≃ₛₗ[φ.toRingHom]`, not `≃ₛₗ[(φ : _ →+* _)]`) or it stays a metavariable and
  blocks `SetLike.val_smul`.

- **Reconstructing a public lemma's `LinearMap.restrict` map when its membership
  proof is `private`.** Lemmas like `youngSym_action_vanishes_off_block` /
  `_rank_one_scaled_proj` state their conclusion about
  `(f).restrict (p := S.restrictScalars k) … (private_mem_proof)`. You can still
  feed that map to an interface expecting `g : ∀ i, ↥(S i) →ₗ[k] ↥(S i)`: define
  `g i := (f).restrict … (your_own_mem_proof)` with a public membership lemma —
  the proof argument is a `Prop`, so the two `restrict`s are **defeq** (proof
  irrelevance), and `have hzero : g i = 0 := <the public lemma>` typechecks by
  defeq. Also: `↥(S.restrictScalars k)` is defeq to `↥S` (restrictScalars keeps
  the carrier), and for an `A`-submodule `S` with `IsScalarTower k A E` the two
  `Module k` structures on `↥S` and `↥(S.restrictScalars k)` agree by defeq, so
  the restrict-typed map slots in where `↥(S i) →ₗ[k] ↥(S i)` is expected. When a
  per-block scalar `α'` (from a rank-1 lemma's existential) must match an
  independently-obtained `α` (`c² = α•c`), reconcile via `f² = α•f`, `f = α'•π'`,
  `π' ≠ 0`, `smul_left_injective k hπ'_ne`, then `mul_right_cancel₀`.

- **Opaque-parameter isolation defeats `whnf`/`isDefEq` heartbeat timeouts in
  `compHom`/`restrictScalars` transfer constructions.** When building a
  `LinearEquiv` over the deep `Subalgebra → Subsemiring → Module` chain (e.g.
  transferring a `SymGroupAlgebra`-iso to a `symGroupImage`-iso through
  `symGroupAlgHomToImage`), a complex equiv held in a local `let`
  (`set g := e₁.trans e₂.symm`) makes the structure-field proofs time out —
  `whnf` unfolds the large source isos (here `Theorem5_12_2_classification`).
  `clear_value g` does **not** help. Fix: move the construction into a standalone
  `def` that takes the big equiv as an explicit **parameter** (`letI`-typed if it
  needs the `compHom` module instance); the body elaborates once with the equiv
  genuinely opaque. Then the caller is a one-line `exact ⟨transferDef S S' g⟩`.

- **Pin `f (N := N) (n := n)` on a hom application feeding a `•`** whose scalar
  type is being inferred (e.g. `(symGroupAlgHomToImage (N := N) (n := n) a) • x`).
  Otherwise `N` is a stuck metavariable ("typeclass instance problem is stuck").

- **`congrArg Subtype.val (g.<lemma> ⟨x.val, x.property⟩)`** discharges the
  `left_inv`/`right_inv`/`map_add'` fields of a carrier-identity submodule
  `LinearEquiv` by defeq. Prefer it over `rw [show ⟨…⟩ = g … from rfl, …]`, which
  fails on "pattern not found" because the post-`Subtype.ext` goal is not
  syntactically normalised.

- **`set` reverts/shadows any hypothesis whose *type* mentions the set term —
  spawns a `S✝` that no longer unifies (Ch5, #4731).** Proving over Schur-Weyl
  hom-spaces `↥S →ₗ[symGroupImage k V n] TensorPower k V n`, writing
  `set A := symGroupImage k V n` / `set E := TensorPower k V n` for brevity
  abstracts those terms *inside* the types of `S`, `W`, `ψ`, forcing `set` to
  revert and reintroduce them — the binder comes back as inaccessible `S✝` and a
  later `exact`/`show` against the original `S` fails with a type mismatch. Only
  `set` the term that does **not** appear in any in-scope binder's type (here the
  centralizer `C`); leave `symGroupImage`/`TensorPower` written out literally.

- **`Algebra.adjoin_induction` over a `Subalgebra` element: `obtain ⟨cval, hcmem⟩
  := c` up front (Ch5, #4731).** The predicate
  `p := fun x _ => ∀ (hx : x ∈ C) …, … (⟨x, hx⟩ : ↥C) • l …` produces a goal in
  the `⟨cval, hcmem⟩` shape; if `c : ↥C` is still bundled, the final
  `… hgen c.2 l` leaves `ψ (⟨↑c, _⟩ • l) = …` versus goal `ψ (c • l) = …`, which
  is only `Subtype`-eta-defeq and a `show`/`exact` bridge **times out** (or hits
  the `c✝` shadow from a prior `set`). Destructuring `c` first makes the goal
  literally match. Mirror the model proof
  `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem`
  (`SchurWeylGLTransfer.lean`); since the generating set is the *units* one
  (`adjoin_unitsTensorPow_eq_diagonalActionImage`), no inner
  `Submodule.span_induction` is needed. In the `mul` case apply the IH to the
  *bundled* `(⟨y, hyC⟩ : ↥C) • l`, never the raw `y • l` (no `HSMul (End …)
  (hom-space)`). These heavy `Module.End (TensorPower)` chains need
  `maxHeartbeats 6400000 / synthInstance.maxHeartbeats 3200000`, matching the
  source theorems.

### Fraction-field bridge: principal open shares the polynomial ring's k(g) (Ch6, #4783)

To send an injective comorphism `φ : MvPolynomial (Fin N) k →ₐ[k] B` into
`FractionRing (MvPolynomial (Fin M) k)` when `B` is a localization of
`P := MvPolynomial (Fin M) k` (the coordinate ring of a principal open `{det ≠ 0}`,
e.g. the `det⁻¹`-localization forced by a base-change `g_j·M·g_i⁻¹` action), do **not**
hunt for an `Algebra B (FractionRing P)` instance — none exists. Build it:

```lean
set P := MvPolynomial (Fin M) k; set K := FractionRing P
have hSle : S ≤ nonZeroDivisors P := ...        -- 0 ∉ S since `IsDomain B`
have hunit : ∀ y : S, IsUnit (algebraMap P K y) :=
  fun y => IsLocalization.map_units K (⟨y, hSle y.2⟩ : nonZeroDivisors P)
letI : Algebra B K := (IsLocalization.lift (M := S) (g := algebraMap P K) hunit).toAlgebra
have hcomp : (algebraMap B K).comp (algebraMap P B) = algebraMap P K := by
  change (IsLocalization.lift hunit).comp (algebraMap P B) = algebraMap P K  -- `change`, not `show`
  exact IsLocalization.lift_comp hunit
haveI : IsScalarTower P B K := IsScalarTower.of_algebraMap_eq' hcomp.symm
haveI : IsFractionRing B K :=                    -- the principal-open identification
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S B K
haveI : IsScalarTower k B K := IsScalarTower.of_algebraMap_eq fun x => by
  rw [IsScalarTower.algebraMap_apply k P K x, ← hcomp, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply k P B x]
```

`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` (in
`Mathlib/RingTheory/Localization/LocalizationLocalization.lean`) is load-bearing — over
a domain it needs no `S ≤ nonZeroDivisors` side goal. `Algebra k (FractionRing P)` and
`IsScalarTower k P (FractionRing P)` are already global instances. Gotcha: when a helper
lemma's `{M}`/`{S}` appear only in *instance* args and the conclusion (not in an explicit
value arg like `φ`), pass them explicitly (`(M := M) (S := S)`) or TC resolution stalls
on a metavariable. See `Problem6_1_5_FieldEmbedding.lean`.

### Orbit-map comorphism: generic matrices over the det-localization (Ch6, #4803)

Building the comorphism `k[W] → B` of an orbit map `g ↦ g•v₀` into the principal-open
coordinate ring `B` (the `det⁻¹`-localization the bridge above consumes). Four idioms:

- **Index `MvPolynomial` by the sigma type, not `Fin N`.** Use
  `GIdx m := Σ i, Fin (m i) × Fin (m i)` and `WIdx m := Σ i j, (i⟶j) × (Fin (m j) × Fin (m i))`
  directly as the `MvPolynomial` index. `Fintype.card_sigma`/`card_prod` give the dimension
  formulas (`gIdx_card = Σmᵢ²`, `wIdx_card = Σbᵢⱼmᵢmⱼ`). Defer the `Fin N`/`Fin M` form the
  bridge wants to a `MvPolynomial.renameEquiv (Fintype.equivFin _)` at the assembly step.
- **A polynomial (or determinant) is nonzero by *evaluating at a concrete point*, not by
  Leibniz expansion.** For `detProd = ∏ᵢ det(genMat m i)`, build `evalId := aeval (fun w =>
  if w.2.1 = w.2.2 then 1 else 0)` (the identity matrix), then `evalId detProd = ∏ det 1 = 1`
  via `map_prod` + `AlgHom.map_det` + `Matrix.det_one`; a ring hom sends `0 ↦ 0`, so `≠ 0`.
- **`AlgHom.map_det f M` produces `(f.mapMatrix M).det`, NOT `(M.map ⇑f).det`.** State the
  "mapped matrix = 1" helper with `AlgHom.mapMatrix` (`simp [..., AlgHom.mapMatrix_apply,
  Matrix.map_apply, Matrix.one_apply]`) so it rewrites after `map_det`.
- **Two confusing-error gotchas when building `aeval`-style endomorphisms of
  `MvPolynomial`.** (1) Bare `X`/`C` do **not** resolve under `open MvPolynomial`
  with `import Mathlib` (another `X` is in scope) — symptom is a misleading
  `Function expected at ...`. Qualify `MvPolynomial.X` / `MvPolynomial.C`
  everywhere, including inside statements and `simp` args. (2) An unannotated sum
  binder `∑ l, ...` whose index type is only pinned by the body also throws
  `Function expected`; write `∑ l : Fin N, ...`. (3) `Finset.sum_congr rfl ...`
  can fail with `typeclass instance problem is stuck` when the two sides' sums
  carry syntactically different `Fintype`/`univ` instances even though both are
  `Finset.univ`; `simp only [mul_comm]` (or the relevant per-term rewrite under
  the binder) is instance-robust where `sum_congr` chokes.
- **Parametrize the comorphism `def` over an *abstract* localization `B`**
  (`[Algebra (MvPolynomial (GIdx m) k) B] [IsLocalization (Submonoid.powers (detProd m)) B]
  [Algebra k B] [IsScalarTower k _ B]`), not a concrete `Localization`: there is no
  `Algebra k (Localization S)` instance, and abstract `B` matches the bridge's style.
  Det-units come from `IsLocalization.map_units B ⟨detProd, Submonoid.mem_powers _⟩` plus
  `isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem ..))`; invert via
  `Matrix.mul_nonsing_inv _ (isUnit_det ..)`. See `Problem6_1_5_OrbitComorphism.lean`.
- **Orbit-comorphism injectivity via per-element evaluation (`Problem6_1_5_OrbitInjective.lean`,
  #4807).** To prove `orbitComorphism v₀ : k[W] →ₐ B` (into the abstract `detProd⁻¹`
  localization) injective, evaluate at each group element: `evalAt g := IsLocalization.liftAlgHom`
  of `aeval (groupEntries g)` (the `detProd`-units hypothesis discharges via
  `(Submonoid.mem_powers_iff _ _).mp y.2` + `map_pow` + `IsUnit.pow`). Prove the identity
  `evalAt g ∘ orbitComorphism v₀ = aeval (pointCoords (g • v₀))` by `MvPolynomial.algHom_ext`.
  The base-change product `g_j · M · g_i⁻¹` is **rectangular**, so `AlgHom.mapMatrix`/`map_mul`
  (square only) do NOT apply: push the ring hom through entrywise with
  `key : ∀ M, evalAt g (M a b) = (M.map (evalAt g)) a b := fun _ => rfl`, then `Matrix.map_mul`
  (a `NonUnitalRingHomClass` lemma — works for rectangular) twice. Map generic matrices via
  `evalAt_algebraMap` (= `IsLocalization.lift_eq`); for the inverse, get `(g i)⁻¹` from
  `Matrix.inv_eq_right_inv` (avoids `Ring.inverse`) and **match the GL-inverse-then-coerce form
  of `repSpace_smul_apply`** by stating the lemma RHS as `(((g i)⁻¹ : GL (Fin (m i)) k) : Matrix ..)`,
  not `((g i)⁻¹ : Matrix ..)`. Injectivity then follows from algebraic density of the orbit
  (`injective_iff_map_eq_zero` + the density predicate). The density itself (Problem 6.1.2a) is
  purely algebraic: finitely many orbits ⟹ a dense orbit by product-of-vanishing-witnesses
  (`Finset.prod_eq_zero`/`prod_ne_zero_iff`) + `MvPolynomial.funext` over `[Infinite k]` — no
  Zariski topology. Group-side lemmas (GIdx/genMat/detProd) need `omit [Quiver ..] [∀ i j, Fintype ..] in`
  to silence section-var linters; the `omit` must precede any docstring.

### Index-agnostic dimension bound: transport a localization bridge to `Fin` (Ch6, #4808)

Assembling `card σ ≤ card τ` (`dim W ≤ dim G`) from an injective comorphism
`φ : k[xσ] → B`, where `B` is a domain localization of `k[xτ]` at `S`, by reusing a
bridge phrased over `Fin N`/`Fin M` (`Problem6_1_5_DimBound.lean`). Both indices move
to `Fin` via `MvPolynomial.renameEquiv (Fintype.equivFin _)`:

- **Source: precompose.** `φ.comp (renameEquiv k (Fintype.equivFin σ).symm).toAlgHom`,
  injective via `hφ.comp (renameEquiv ..).injective` (align the coe with `AlgHom.coe_comp`
  / an `ext` + `simp` if `exact` balks).
- **Base: carry `IsLocalization` across the rename ring equiv.** Let
  `h := (renameEquiv k eτ).toRingEquiv`. `IsLocalization.isLocalization_of_base_ringEquiv S B h`
  proves `IsLocalization (S.map h) B` **but for a specific new algebra instance**
  `((algebraMap (MvPolynomial τ k) B).comp h.symm.toRingHom).toAlgebra` — you must
  `letI algB := that exact term` so the instance it returns matches. Then build
  `IsScalarTower k (MvPolynomial (Fin M) k) B` by hand: `IsScalarTower.of_algebraMap_eq`,
  unfold the new map with `RingHom.algebraMap_toAlgebra`, and discharge
  `h.symm.toRingHom (algebraMap k _ x) = algebraMap k _ x` by `(renameEquiv k eτ).symm.commutes x`
  (defeq: `h.symm.toRingHom` applied IS `(renameEquiv k eτ).symm` applied, since `h` is a `let`).
- **Pin the transported submonoid at the bridge call:** `bridge (S := S.map h) φ' hφ'` — the
  bridge's `{S}` is not fixed by its value args, so TC stalls otherwise (same metavar idiom as
  the FieldEmbedding note above).
- **The concrete `B = Localization (Submonoid.powers (detProd m))` has all instances.**
  `Algebra (MvPolynomial (GIdx m) k) B`, `IsLocalization`, `Algebra k B`, and
  `IsScalarTower k _ B` all synthesize **when `Localization S` is written directly** — contra
  the #4803 note's "no `Algebra k (Localization S)`", which bites only if you `let B := …`
  (a `let`-bound local blocks instance synthesis; inline the type instead). `IsDomain B` via
  `IsLocalization.isDomain_localization (M := …) (powers_le_nonZeroDivisors_of_noZeroDivisors
  (detProd_ne_zero ..))`.

### Norm-Based Contradiction (Analysis Proofs)

For proofs requiring algebraic integer arguments (e.g., Lemma 5.4.5):
1. Use `Algebra.norm` to map from the algebraic number to a rational integer
2. Establish `|Norm(α)| ≥ 1` (since α is a nonzero algebraic integer, its norm is a nonzero integer)
3. Establish `|Norm(α)| < 1` via triangle inequality and `norm_sum_lt_of_strictConvexSpace`
4. Derive contradiction

This two-step norm approach works whenever you need to show an algebraic quantity equals zero or a root of unity.

### `sorry : Prop` for Unprovable Statements

When Mathlib lacks the types to express a theorem's statement at all (not just the proof), use:

```lean
/-- Theorem X.Y.Z: [natural language statement].
    Statement requires infrastructure not yet in Mathlib. -/
theorem theorem_X_Y_Z : (sorry : Prop) := sorry
```

This is sanctioned for items where the *statement itself* cannot be formalized (e.g., Gabriel's theorem needing quiver representation types, sl(2) classification). These items cannot be proved until infrastructure is built. Track them with status `needs_infrastructure` in items.json.

**Never use `True` as a placeholder** — it compiles silently and hides the gap.

### Multipart Theorem Strategy

When a theorem has multiple parts (e.g., existence + uniqueness, or (i)+(ii)+(iii)), prove them independently and leave unsolved parts as `sorry`:

```lean
theorem foo : Part1 ∧ Part2 ∧ Part3 := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: proved
    exact proof1
  · -- Part 2: hardest, work on this first
    sorry
  · -- Part 3: easy, fill in after Part 2
    sorry
```

**Always work on the hardest part first.** If Part 2 fails, all effort on Parts 1 and 3 is wasted. Commit partial proofs — they document exactly what's missing and unblock downstream work that doesn't need the sorry'd parts.

This pattern succeeded for Theorem 3.10.2 (part i proved, part ii sorry'd), Theorem 5.4.4 (main structure done, one ingredient sorry'd), and IrreducibleEnumeration (injectivity + simplicity proved, surjectivity sorry'd).

### Character Orthogonality for Span/Independence (Wave 30)

When proving that a set of characters spans or is linearly independent, use inner product orthogonality:

```lean
-- Prove ℚ-span via orthogonality + induction
have h_orth := FDRep.char_orthonormal
-- Use span_induction to reduce to showing each basis element is in the span
apply Submodule.span_induction ...
```

**Key APIs:** `FDRep.char_orthonormal`, `ClassFunction.inner_eq_zero_of_ne`, `Submodule.exists_le_ker_of_notMem`.

**Evidence:** This proved Theorem5_26_1 (Artin's theorem) completely — both `class_fun_vanishes_on_subgroup_of_orthogonal` and `artin_Q_span_of_induced_chars` used character inner products. Also proved the character orthogonality lemma for `principalSeries_simple_of_ne`.

**Pattern:** For any "show X is in the span of Y" problem in representation theory, first check if orthogonality gives you a clean proof. It usually does.

### IsSplitMono + Cokernel for Representation Decomposition (Wave 30)

When proving a representation decomposes as a direct sum V ≅ A ⊕ B:

1. Construct a nonzero mono `f : A ⟶ V` (e.g., an embedding)
2. Apply Maschke's theorem to get `IsSplitMono f`
3. Use `binaryBiconeOfIsSplitMonoOfCokernel` to get V ≅ A ⊞ cokernel(f)
4. Identify cokernel(f) ≅ B (often via dimension counting)

```lean
-- Step 1: Get IsSplitMono from Maschke
have hsm : IsSplitMono detCharEmbedding := Abelian.IsSplitMono_of_mono _
-- Step 2: Build biproduct via cokernel
exact binaryBiconeOfIsSplitMonoOfCokernel detCharEmbedding
```

**Evidence:** This approach is set up for `principalSeries_decomp` (V(μ,μ) ≅ ℂ_μ ⊕ W_μ). The infrastructure lemmas (detChar_simple, detCharEmbedding_mono, detCharEmbedding_ne_zero) proved in PRs #1624, #1658 feed directly into this pattern.

### Dimension Contradiction Pattern (Wave 30)

For proving properties by contradiction using `Module.finrank`:

```lean
-- Show two finite-rank subspaces can't both fit
have h1 : Module.finrank k S₁ ≥ 1 := ...
have h2 : Module.finrank k S₂ ≥ 1 := ...
have h3 : Module.finrank k V = Module.finrank k S₁ + Module.finrank k S₂ := ...
-- Derive contradiction from dimension inequality
omega
```

**Evidence:** Proved nilpotent_nontrivial_decomp (d=1 contradiction in PR #1628, subrepresentation arguments in PR #1632). Also used in decomp_of_ker_sum_ge_two dimension argument (PR #1633).

### Graph Isomorphism for Classification Proofs (Wave 30)

For Dynkin-type classification proofs requiring graph isomorphisms between combinatorially-defined graphs:

```lean
-- Build explicit bijection via path permutation
def tree_branch_iso : G₁ ≃g G₂ where
  toEquiv := pathPermutation ...  -- permute vertices along a canonical path
  map_rel_iff' := ...
```

**Evidence:** PR #1634 used `tree_branch_iso` to prove all 4 arm cases (D_n, E₆, E₇, E₈) in `branch_classification`, reducing Theorem_Dynkin_classification from 6 sorries to 0. The key insight: express graph isomorphisms as path permutations with optional reversal.

### PolytabloidBasis Dual-Track Architecture (Wave 46)

The polytabloid basis proof uses **two complementary tracks**:

**Track 1: Group algebra (PolytabloidBasis.lean)** — works with elements of ℂ[S_n]:
- `polytabloid T = κ_T · of(σ_T) · a_λ` where κ_T is the T-dependent column antisymmetrizer
- Coefficient formulas (`polytabloid_apply`, `polytabloid_self_coeff`, `polytabloid_support`)
- Straightening: reducing arbitrary σ · c_λ to a sum of polytabloids (needs Garnir + WF order)
- Handles the **spanning** direction

**Track 2: Tabloid module (TabloidModule.lean)** — works with tabloid equivalence classes:
- Tabloid = left P_λ-coset = equivalence class under row permutations
- `tabloidDominance`: partial order via cumulative entry counts
- `polytabloid_syt_dominance`: if e_{T₁}(σ_{T₂}) ≠ 0 then tabloid(T₁) dominates tabloid(T₂)
- Unitriangular projection matrix → **linear independence**

**When to use which track:**
- Coefficient computations (evaluating e_T at σ) → Track 1
- Linear independence arguments → Track 2 (via tabloid dominance + unitriangularity)
- Spanning arguments → Track 1 (via straightening algorithm)
- The two tracks connect through `polytabloid_support` (Track 1 feeds into Track 2's dominance argument)

**Key pitfall:** Don't try to prove linear independence by direct evaluation in ℂ[S_n]. The evaluation matrix c_λ(σ_{T₁}⁻¹ · σ_{T₂}) is NOT upper-triangular — it can be nonzero in both directions for distinct T₁, T₂. Only the tabloid projection approach gives the triangularity structure.

### MonoidAlgebra Coefficient Computation (Wave 46)

For proving coefficient formulas in `MonoidAlgebra ℂ (Equiv.Perm (Fin n))`:

```lean
-- Evaluating (a * b)(σ) where a, b : MonoidAlgebra ℂ G
-- Uses: MonoidAlgebra.mul_apply, Finsupp.sum
-- Key: (a * b)(σ) = Σ_{g} a(g) * b(g⁻¹ * σ)

-- For sums like RowSymmetrizer:
-- (RowSymmetrizer)(σ) = if σ ∈ P_λ then 1 else 0
-- Use: Finsupp.single_apply, Finset.sum_ite

-- For products with of(σ):
-- (of(σ) * a)(τ) = a(σ⁻¹ * τ)
-- Use: MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply
```

**Pattern:** Expand definitions → use `Finsupp.sum` / `Finset.sum` manipulation → simplify using subgroup membership predicates. The hardest part is usually showing that sums over subgroups telescope to 0 or 1 using intersection triviality (e.g., `row_col_inter_trivial'`: P_λ ∩ Q_λ = {1}).

### FDRep Categorical Plumbing

Working with `FDRep` (finite-dimensional representations as a category) requires navigating multiple abstraction layers. This is the #1 blocker in Chapters 4-5.

**The problem:** Book proofs work with concrete linear maps `V →ₗ[k] V`, but Mathlib's FDRep uses categorical morphisms. Converting requires unwrapping 3 levels: `Action.Hom → FGModuleCat.Hom → ModuleCat.Hom → LinearMap`.

**Pattern 1: Reflect through a full+faithful functor**

When you need to prove a property about FDRep objects (like simplicity), prove it for the underlying module and reflect through the functor:

```lean
-- Prove simplicity for the concrete module first
have h : IsSimpleModule k M := Matrix.instIsSimpleModule ...
-- Reflect to FDRep via full+faithful functor
exact Simple.of_full_faithful_preservesMono FDRep.forget₂ h
```

This avoids working inside the categorical abstraction entirely.

**Pattern 2: Use Representation directly instead of FDRep**

For character theory, prefer `Representation k G V` (which gives you `V →ₗ[k] V` directly) over `FDRep k G` (which wraps in a category). Most character computations don't need the categorical structure.

**Pattern 3: Avoid `.hom.hom` chains**

If your proof requires distributing `.hom.hom` over `Finset.sum` or similar, you're fighting the abstraction. Instead:
- Define a helper that states the result directly on `LinearMap`
- Or use `Representation.averageMap` which already works at the LinearMap level

**When stuck on FDRep plumbing after 2 attempts:** Sorry the categorical step with a comment explaining what's needed, and file an issue. Don't spend an entire session on unwrapping functors.

### Bezout Reduction for Integrality

When proving `IsIntegral ℤ (a / b)` where `a` and `b` are related by coprimality:

1. Find `m, n` with `m * b + n * a = 1` via `Nat.Coprime` and `Nat.gcd_eq_gcd_ab`
2. Rewrite `a / b = m * (stuff₁) + n * (stuff₂)` where both summands are provably integral
3. Apply `IsIntegral.add` and `IsIntegral.mul`

This avoids dependent type issues from rewriting `a/b` directly. Used successfully in Theorem 5.4.4.

### Full+Faithful Functor Reflection for Simplicity

To prove an FDRep is simple:
1. Prove `IsSimpleModule k M` for the underlying module (often via `Matrix.instIsSimpleModule`)
2. Lift through `IsSimpleModule.compHom` if needed (for algebra homomorphisms)
3. Reflect to categorical `Simple` via `Simple.of_full_faithful_preservesMono`

This chain: concrete simplicity → algebra hom transfer → functor reflection was the successful pattern for IrreducibleEnumeration (#678).

### Permutation Matrix Arguments

For character identities involving the regular representation (e.g., χ_reg(g) = 0 for g ≠ 1):
- Express the representation matrix as a permutation matrix of left-multiplication
- Show the permutation has no fixed points when g ≠ 1
- Conclude the trace (= character value) is zero

This is more concrete than abstract character theory and avoids FDRep entirely.

### Jacobson Radical for Injectivity

To prove a ring homomorphism from a semisimple ring is injective:
1. Show every element of the kernel acts as zero on all simple modules
2. Therefore the kernel element is in every maximal left ideal
3. The intersection of all maximal left ideals is the Jacobson radical
4. For semisimple rings, Jacobson radical = ⊥
5. Hence kernel = ⊥, so the map is injective

**Lean tip:** May need explicit universe parameters (`.{v}`) to make the Jacobson radical API work with the correct universe level.

## Mathlib Gap Handling

When you discover a Mathlib API gap during formalization, follow this escalation ladder:

### Level 1: Local Workaround (< 30 min)
If you can define the missing concept locally in ≤ 20 lines and it unblocks the proof:
```lean
-- Local definition until Mathlib adds IsIndecomposable
def IsIndecomposable (M : Type*) [AddCommMonoid M] [Module R M] : Prop :=
  ¬IsZero M ∧ ∀ N₁ N₂ : Submodule R M, N₁ ⊓ N₂ = ⊥ → N₁ ⊔ N₂ = ⊤ → N₁ = ⊥ ∨ N₂ = ⊥
```

### Level 2: `sorry` the Gap, File an Issue (> 30 min)
If building the infrastructure would take > 30 min:
1. Use `sorry` for the missing fact
2. Add a comment: `-- Requires [description], not in Mathlib as of v4.28`
3. File a GitHub issue with label `needs-mathlib-api` describing exactly what's needed
4. Move on to the next item

### Level 3: Infrastructure Issue (Blocks Multiple Items)
If the same gap blocks 3+ items (e.g., column orthogonality blocking all character theory):
1. File a detailed GitHub issue documenting:
   - What's missing (with mathematical description)
   - Which items are blocked
   - Whether Mathlib has partial coverage (e.g., row orthogonality exists but not column)
   - Estimated effort to build locally
2. Mark all blocked items as `needs_infrastructure` in items.json
3. Don't attempt to build major infrastructure during a proof session — that's a separate planned issue

### Known Gaps in This Project

| Gap | What Exists | What's Missing | Blocks | Status |
|-----|------------|----------------|--------|--------|
| Column orthogonality | `FDRep.char_orthonormal` (row) | `∑_V χ_V(g) · χ_V(h⁻¹) = \|C_G(g)\| · δ` | Thm 5.4.6, Burnside | Issue #633 |
| Regular rep decomposition | `FDRep`, `Simple` | `k[G] ≅ ⊕ dim(V_i) · V_i` | Thm 5.4.6 | Issue #643 |
| Simple module classification | `Simple` predicate | Every simple FDRep ≅ some columnFDRep | IrrepEnum surjectivity | Issue #655 |
| FDRep ↔ LinearMap plumbing | `.hom` unwrapping | Distributing `.hom.hom` over sums, Schur at LinearMap level | Prop 5.3.2 | Workaround: non-categorical pattern |
| Quiver representations | `Quiver`, `PathAlgebra` | `QuiverRepresentation`, hom, subobjects | Ch6 items | Workaround: concrete constructions |
| Pigeonhole transposition | `Finset` API | Row/column counting for Young tableaux | Lemmas 5.13.1, 5.13.2 | Issues #776, #777 |
| Non-commutative TensorProduct | `TensorProduct` (CommSemiring only) | Balanced tensor product `A ⊗_{eAe} N` for non-commutative rings | BasicAlgebraExistence, MoritaStructural | Manual quotient construction needed |
| Krull-Schmidt theorem | None | Unique decomposition of modules into indecomposables | basic_morita_algEquiv (#1877) | Not in Mathlib, blocks Morita isomorphism |
| ~~Clifford theory~~ | ~~None~~ | ~~Semidirect product orbit method~~ | ~~Theorem5_27_1~~ | **RESOLVED** (Wave 47): All Mackey machine sorries proved via bypass |
| ~~Right-multiplication dominance~~ | ~~Left-mult dominance proved~~ | ~~Right `σ · e_T` ≠ left `σ · e_T`~~ | ~~PolytabloidBasis~~ | **RESOLVED** (Wave 46): Tabloid module approach bypasses entirely |

## Proof Chain Completion Strategy

When multiple sorry'd items exist, **prioritize completing already-started chains** over beginning new proofs. A "chain" is a sequence of items where proving one unblocks the next.

**Why this works:** Chain completion has the highest ROI per agent-hour. Completing one helper lemma can cascade to chapter-level completion. In Wave 4, focusing on the Theorem 4.10.2 chain (2 helper lemmas) completed all of Chapter 4.

**How to identify chains:**
1. Look for items whose dependencies are all sorry-free except one
2. Look for chapters near 100% — one or two proofs may close them out
3. Check if a sorry'd helper lemma is used by 2+ other proofs

**Priority order for proof selection:**
1. Chain-completing proofs (unblock downstream items)
2. Chapter-completing proofs (achieve 100% for a chapter)
3. Infrastructure proofs (unblock 3+ items across chapters)
4. Standalone proofs (no downstream dependents)

## Quiver Representation Patterns

Chapter 6 quiver representations use concrete finite-dimensional constructions rather than abstract quiver theory. This approach was discovered in Wave 4 (Examples 6.2.2-6.2.4) after three waves of zero progress with abstract approaches.

### Concrete Construction Pattern

For quiver representations with vertices V₁, ..., Vₙ and arrows between them:

```lean
-- Represent each vertex space as Fin d →₀ k (or Fin d → k)
-- Represent each arrow as a concrete LinearMap between vertex spaces
structure D₄Rep (k : Type*) [Field k] where
  V  : Type* -- central vertex
  V₁ : Type* -- arm vertices
  V₂ : Type*
  V₃ : Type*
  A₁ : V₁ →ₗ[k] V  -- arrow maps
  A₂ : V₂ →ₗ[k] V
  A₃ : V₃ →ₗ[k] V
```

**Key insight:** Work with explicit `LinearMap`s between finite-dimensional spaces, not abstract `QuiverRepresentation` types. Mathlib's quiver infrastructure is insufficient for the proofs we need, but the concrete linear algebra API is rich.

**Helper-lemma signatures: state them over explicit block spaces, not `(rep…).obj v`.** A flag/collapse helper whose statement mentions `x ∈ W ⟨k⟩` with `W : ∀ v, Submodule F ((someRep_kQ …).obj v)` can fail `Membership` synthesis *in the signature* (`failed to synthesize Membership (Fin (a*(m+1)) → F) (Submodule F ((rep …).obj ⟨k, ?m⟩))`): the `obj`/`*Dim` match does not reduce, especially under the `attribute [-instance] …toQuiver` pragma the rep lemmas carry. The robust fix for any helper that is *pure linear algebra over the per-vertex spaces* (e.g. `t125_prefix_sub`/`t125_suffix_sub`, `FieldGenericT125.lean` Section 3b) is to take **explicit block submodules** `W0 : Submodule F (Fin (6*(m+1)) → F)`, `W2 : Submodule F (Fin (4*(m+1)) → F)`, … instead of the rep family `W`. It elaborates cleanly, drops the `attribute`/`IsAlgClosed`/`Q`/`hOrient` clutter, and is reusable across shapes (one prefix-flag lemma serves Ẽ₆/Ẽ₇/T(1,2,5)). Call sites pass `W ⟨0⟩`, `W ⟨2⟩`, …; the dims match `*Dim` by defeq *at the call site*, where the expected type is known so `isDefEq` (default transparency) unfolds `obj`/`*Dim`. (In-proof `have`s and some standalone lemmas do tolerate `obj v` membership, so it is not a hard rule — but reach for explicit block spaces the moment a signature throws a Membership-synthesis error.) Also place such helpers *after* the rep `def` only if they reference it; pure block lemmas can sit anywhere after the block-map defs.

### Indecomposability via Kernel Splitting

For classifying indecomposable representations:
1. Check kernels of arrow maps — if `ker Aᵢ ≠ ⊥`, split off the kernel as a direct summand
2. This reduces to the "all injective" case, which is the hard subspace-configuration problem
3. For the injective case, use `Submodule.IsCompl` and `Module.finrank` to classify

### Indecomposability via Nilpotent Complement (Extended Dynkin Types)

For extended Dynkin quiver representations (Ẽ₆, Ẽ₇, T(1,2,5), D̃_n), the established
proof pattern uses `nilpotent_invariant_compl_trivial` (InfiniteTypeConstructions.lean:158).
Reference implementation: `cycleRep_isIndecomposable` (lines 304-372).

**Pattern:**
1. **Nontriviality:** Show representation is nonzero at some vertex
2. **Setup:** Assume complementary invariant submodules W₁, W₂ at all vertices
3. **Propagate to leaf:** Use map injectivity to show W₁(leaf) ≤ W₁(leaf') for
   leaves connected through arm chains. Establish W(leaf₁) = W(leaf₂) or similar.
4. **Nilpotent invariance:** Show W₁(leaf) and W₂(leaf) are both invariant under
   the nilpotent shift `nilpotentShiftLin m` at a leaf vertex. This is the HARD step —
   the nilpotent enters through one arm but must be shown to propagate to the leaf.
5. **Apply lemma:** `nilpotent_invariant_compl_trivial` gives W₁(leaf) = ⊥ or W₂(leaf) = ⊥
6. **Propagate back:** From W(leaf) = ⊥, propagate via injectivity of all edge maps
   to show W(v) = ⊥ for all vertices.

**Critical:** The m ≥ 1 hypothesis is essential. For m = 0, the nilpotent is zero and
the representations are genuinely decomposable (issues #2342, #2374, #2376).

### Refuting indecomposability (counterexample-first)

Single-twist D̃/Ẽ `_kQ` indecomposability theorems are frequently **false** for
reversed-leaf orientations (issue #4566: `starRep_kQ_isIndecomposable` is false
when the diagonal leaf is reversed). Before grinding a `sorry` on
`<X>Rep_kQ_isIndecomposable`, try to refute it at `m = 1`. Worked, sorry-free
example: `starRep_kQ_reversedLeaf3_decomposable` (`FieldGenericStar.lean`).

`IsIndecomposable` is `(∃ v, Nontrivial) ∧ (∀ W₁ W₂, inv₁ → inv₂ → compl → all-⊥)`.
To refute, exhibit explicit invariant complementary `W₁ W₂` with neither
everywhere `⊥`: `rintro ⟨-, hno⟩; have := hno W₁ W₂ ?inv1 ?inv2 ?compl` then derive
a contradiction from a vertex where both are nonzero. Reusable helpers
`isCompl_coordLines_two` / `isCompl_coordPlanes_four` (in `FieldGenericStar.lean`)
give `IsCompl` for coordinate-axis spans.

Three non-obvious Lean gotchas when building such counterexamples:

1. **Ambient `Quiver` instance interference.** Outside the
   `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
   CategoryTheory.ReflQuiver.toQuiver in` guard, a spurious category `Quiver`
   instance is active. `rw` with `ReversedAtVertexHom_eq_*` lemmas then fails to
   match — pass the base quiver explicitly:
   `rw [@Etingof.ReversedAtVertexHom_eq_eq (Fin n) _ starQuiver i a b ha hb]`.
   Also `reversedAtVertex` is noncomputable: use `@[reducible] noncomputable def`,
   not `abbrev`, for a named oriented quiver.
2. **`simp only [matchDef]` does not reduce a `match` on `Fin` literals.**
   `starRepMap_kQ F 1 1 0` will not rewrite to `starEmbed1_F F 1` via simp.
   Convert the map by a defeq `show starEmbed1_F F 1 x ∈ _` (do this *before*
   destructuring `x`, to avoid cross-type `HAdd` errors in the `show`).
3. **Arrow case order + empty Homs.** After `fin_cases a <;> fin_cases b`, arrow
   goals appear in `(a,b)` lexicographic order (e.g. `(0,3)` before `(1,0)`). In a
   `reversedAtVertex` orientation every non-arrow pair has empty Hom, closable
   uniformly by `first | exact absurd e.down (by decide) | skip`.

### Dimension Vector Pattern

Track dimension vectors `(dim V, dim V₁, ..., dim Vₙ)` as the primary classification tool. Indecomposability constraints on dimension vectors are often finite and enumerable.

## Combinatorial Counting Arguments

Pigeonhole-style counting arguments (e.g., "by counting, some row must have two elements mapping to the same column") are a persistent difficulty in Lean formalization. The mathematical intuition is simple but the formal proof requires careful API navigation.

### Recommended Approach

1. **State the counting lemma separately** — don't inline pigeonhole arguments in larger proofs
2. **Use `Finset.exists_ne_map_eq_of_card_lt`** (pigeonhole principle) when available
3. **For partition-based counting:** Express the constraint as a `Finpartition` or use `Finset.sum_card_fiberwise_eq_card` to relate partition sizes to totals
4. **For injection-based arguments:** Use `Fintype.card_lt_of_injective_of_not_surjective` or `Function.Injective.card_le`

### When Stuck on Combinatorial Proofs

After 2 serious attempts:
1. Sorry the combinatorial core with a precise comment describing the counting argument
2. Complete the algebraic frame around it (this is valuable and independently reviewable)
3. File an issue with status `attention_needed`

This "algebraic frame + combinatorial sorry" pattern was successfully used in Lemmas 5.13.1 and 5.13.2 (Young symmetrizer proofs).

## Non-Categorical Workaround Pattern

When a proof requires FDRep categorical machinery that's blocked by `.hom` plumbing, try reformulating the argument to avoid categories entirely.

**Example (Theorem 5.4.4, PR #721):** Instead of using the categorical Schur's lemma via FDRep:
- Used eigenvalues of central elements acting on simple modules
- Proved `character_div_dim_isIntegral` via direct algebraic argument
- Completely bypassed FDRep plumbing

**When to try this:**
- The proof fundamentally needs a fact about linear maps (traces, eigenvalues, determinants)
- The categorical formulation adds structure you don't actually need
- You've spent > 30 min fighting `.hom` unwrapping

**How to find the workaround:**
1. Write out the mathematical argument in terms of linear maps and matrices
2. Check if Mathlib has the needed lemmas at the `LinearMap` / `Matrix` level
3. If yes, build the proof there — it's usually cleaner than the categorical version

## Helper Lemma Extraction Pattern

When a proof is too complex for a single session, extract helper lemmas into separate declarations. This pattern was critical for Theorem 4.10.2 (block polynomial irreducibility) and the Young symmetrizer chain (5.13.1-5.13.4).

### When to Extract

- A proof attempt reveals a non-trivial subgoal that's independently meaningful
- The same fact is needed by 2+ proofs (e.g., `pigeonhole_transposition` used by both 5.13.1 and 5.13.2)
- A proof exceeds ~50 lines of tactics — break it up

### How to Extract

1. **State the helper as a separate `lemma`** in the same file, above the main theorem
2. **Use `sorry` for the helper's proof** — this lets you test the main theorem's proof structure immediately
3. **Commit the main theorem using the sorry'd helper** — this is valuable progress even if the helper is hard
4. **Work on the helper separately**

```lean
-- Helper extracted from complex proof
lemma helper_fact (n : ℕ) (h : n > 0) : some_property n := sorry

-- Main theorem uses the helper
theorem main_result : conclusion := by
  have h := helper_fact n hn
  exact ...
```

### Multi-PR Proof Chains

Complex theorems may span multiple PRs. This is expected and desirable:
- **PR 1**: State theorem + helpers, prove the algebraic frame, sorry the hard core
- **PR 2**: Prove helper lemmas
- **PR 3**: Close the last sorry

Each PR must compile. Label intermediate PRs with the item ID so reviewers can track the chain.

## Chapter Closure Tactics

When a chapter is within 1-3 items of 100% completion, prioritize closing it. Chapter closures have outsized value:
- Psychological milestone for the project
- Eliminates an entire category from the work queue
- Proves the formalization approach works end-to-end for that chapter

**Identifying closure candidates:**
1. Check `items.json` for chapters with high completion percentage
2. Look for items where all dependencies are sorry-free
3. Prefer the easiest remaining item to close the chapter first

**Evidence:** Ch3 closed via Jordan-Hölder (#831), Ch4 via block polynomial (#812). Both were chain-completion efforts that required focused multi-session work but had outsized impact on project morale and metrics.

## Endgame Priorities (Wave 47, 2026-04-11)

With **9 sorries** across 6 files, the project is at 99.5% items sorry-free (581/583). All definition-level sorries are resolved. The remaining sorries are the hardest in the project — each requires either deep combinatorial argument, new infrastructure, or architectural rethink.

**Trajectory:** 66 sorries (wave 28, Mar 22) → 13 (wave 43, Apr 4) → 15 (wave 45, Apr 6, architectural decomposition) → **9 (wave 47, Apr 11)**. Wave 47 broke through a two-wave plateau at 15 sorries via coefficient lemma proofs, Problem6_9_1 closure, and TabloidModule cleanup.

**Recently completed (Waves 44-47, PRs #2209–#2221):**
- Young symmetrizer coefficients: 4 lemmas proved (#2221) — PolytabloidBasis 8→4 sorries
- Problem6_9_1: compatible_product_decomp fully proved (#2215) — 0 sorry
- TabloidModule: unused polytabloid_syt_dominance removed (#2209) — 0 sorry
- CI fixed (#2213, #2214) — main branch CI breakage resolved

**Remaining sorry map (9 sorries, 6 files):**

```
Cluster A: Polytabloid Basis (Ch5, 5 sorries)
├── PolytabloidBasis (4): polytabloid_mem_spechtModule, polytabloid_linearIndependent,
│                         column_standard_in_span', perm_mul_youngSymmetrizer_mem_span_polytabloids
└── FormalCharacterIso (1): iso_of_glWeightSpace_finrank_eq (GL_N complete reducibility)

Cluster B: Gabriel Theorem Chain (Ch6, 2 sorries)
├── Corollary6_8_4 (1): mixed vertex case [PR #2208 in CI]
└── Problem6_1_5_theorem (1): positive definiteness → finite type [blocked on #2143 chain]

Cluster C: Morita Theory (Ch9, 1 sorry)
└── MoritaStructural (1): head_isomorphism [blocked on PR #2175]

Isolated:
└── Theorem2_1_2 (1): Gabriel's theorem classification [depends on Clusters A + B]
```

**6 PRs in CI (all re-triggered, infrastructure failures not code):**
- #2175 (Module.Finite) → unblocks #2174 (head_isomorphism)
- #2191 (D̃_n infinite type) → unblocks #2187 (non-ADE case analysis)
- #2198 (Ẽ_6 construction) → unblocks #2199 (indecomposability)
- #2200, #2219 → contribute to #2143 chain → unblocks Problem6_1_5_theorem
- #2208 → Corollary6_8_4 mixed vertex case (direct sorry reduction)

**Priority tiers:**

**Tier 1 — Highest ROI (waiting on CI):**
- **Wait for 6 PRs to pass CI.** When they merge, 3 blocked issues unblock (#2174, #2187, #2199). This is the highest-leverage action requiring zero code work.
- **PR #2208** — If CI passes, Corollary6_8_4 sorry may be directly resolved.

**Tier 2 — Tractable now:**
- **polytabloid_linearIndependent** (#2212, unclaimed) — Transfer from tabloid-module proof. Well-scoped, difficulty 4. Would reduce PolytabloidBasis to 3 sorries.
- **head_isomorphism** (#2174) — Becomes actionable when #2175 merges.

**Tier 3 — Hard but well-scoped:**
- **polytabloid straightening** (#2217) — column_standard_in_span' + perm_mul_youngSymmetrizer_mem_span. Difficulty 7. Tabloid-level Garnir + dominance induction.
- **polytabloid_mem_spechtModule** — T-dependent definition complicates membership proof. No open issue yet.

**Tier 4 — Deep infrastructure:**
- **FormalCharacterIso** — GL_N complete reducibility. Needs Schur-Weyl infrastructure. Lowest priority.
- **Theorem2_1_2** — Gabriel's theorem. Depends on both Clusters A and B.

**Key endgame insights:**
1. **All definitions are constructed.** Every remaining sorry is a pure proof obligation.
2. **Decomposition is the dominant value-creation pattern.** Converting a monolithic sorry into structured sub-goals (with 60-80% proved) is often the best outcome for a single session.
3. **Approach cycling is expensive.** After 3 genuinely different approaches, document and move on.
4. **Pessimism about infrastructure requirements can be wrong.** The Mackey machine was estimated to need ~500 lines of Clifford theory. It was proved without Clifford theory at all — direct constructions sufficed. Always try the simplest approach first.
5. **Element-level proofs bridge SMul instance diamonds.** When two Module instances are propositionally but not definitionally equal, work at element level with `ext`, then use `conv_lhs => rw [...]` to bridge the instances.
6. **Multi-PR iteration is normal for hard items.** Complex theorems routinely require 2-4 PRs: restructure → build infrastructure → prove.
7. **CI infrastructure failures are the #1 time sink.** Runner OOM/disconnects cause CANCELLED status. The fix is always re-triggering — never waste time diagnosing "code issues" when the build log shows runner communication lost.
8. **The tabloid module approach works.** TabloidModule.lean's dominance order + unitriangularity has been the successful path for polytabloid independence. Garnir straightening at the group algebra level was a dead end (tautology). Use tabloid-level reasoning for all remaining polytabloid sorries.

## Non-Commutative Ring Workarounds

Mathlib's `TensorProduct` requires `CommSemiring`. Multiple agents across 4+ sessions have hit this wall when working on Morita theory and corner rings. Here are the known workarounds:

### The Problem
`TensorProduct R M N` requires `[CommSemiring R]`. But Morita equivalence needs `A ⊗_{eAe} N` where `eAe` is a corner ring (non-commutative in general).

### Workaround 1: Balanced Tensor Product as Quotient
Construct `A ⊗_{eAe} N` as a quotient of `A ⊗_k N` by the balanced submodule:
```lean
-- The balanced submodule: generated by (a · r) ⊗ n - a ⊗ (r · n) for r ∈ eAe
def balancedSubmodule : Submodule k (TensorProduct k A N) := ...
def BalancedTensorProduct := (TensorProduct k A N) ⧸ balancedSubmodule
```
This construction appeared in BasicAlgebraExistence and was used in 3+ sessions.

### Workaround 2: Use `isUnit_of_sub_one_mem_jacobson_bot` alternatives
The `isUnit_of_sub_one_mem_jacobson_bot` API requires `CommRing`. For non-commutative rings, use `IsNilpotent.isUnit_one_sub` instead (only requires `Ring`).

### Workaround 3: Avoid `linarith`/`linear_combination` over non-commutative rings
These tactics need `CommSemiring`. Use manual algebra (`calc` blocks with `mul_assoc`, `mul_comm` where applicable, or `ring_nf` after establishing commutativity of specific elements).

### Status
Non-commutative tensor products remain the hardest infrastructure gap. No clean resolution exists in Mathlib. The balanced quotient approach works but requires ~100 lines of boilerplate per use site.

## Type-Level If/Else Diamond Issue

When defining a structure whose `obj` field branches on vertex equality (e.g., `if v = i then T₁ else T₂`), Lean's typeclass system creates a diamond:

**The problem:** Structure fields like `[instAddCommMonoid : ∀ v, AddCommMonoid (obj v)]` and `[instModule : ∀ v, Module k (obj v)]` are filled sequentially. After `instAddCommMonoid` is filled (e.g., via `split; infer_instance`), it becomes opaque. The `instModule` field's type depends on `instAddCommMonoid`, but the opaque term prevents `split` from decomposing the `if` inside it.

**What doesn't work:**
- `split <;> infer_instance` for the Module field (can't split opaque match)
- `by_cases h; subst h; simp; infer_instance` (simp can't reduce `if` with opaque Decidable)
- `convert inferInstance` (leaves unsolvable HEq goals between opaque and concrete instances)
- Helper instances `iteAddCommMonoid`/`iteModule` (Module's AddCommMonoid dependency doesn't match)
- Sharing a `let`-bound `Decidable` value (doesn't reduce at type level)

**Current workaround:** Sorry the `instModule` field and the `mapLinear` field. The `obj` field (the mathematical content) and `instAddCommMonoid` can be concrete. This is acceptable per issue guidelines ("specific field obligations sorry'd").

**Potential solutions for a future refactor:**
1. Change `QuiverRepresentation` to not use `[...]` instance fields — use explicit bundled instances instead
2. Use `@[reducible]` on the obj definition so the `if` reduces
3. Define the representation for each case separately and combine using `Sigma`/`Sum`

This affects: Definition 6.6.3 (F⁺ᵢ), Definition 6.6.4 (F⁻ᵢ), and any future definition that branches `obj` on a proposition.

## Fintype Instance Mismatch in Sum Comparisons

When comparing two `Finset.sum` expressions over `Finset.univ` for a subtype (e.g., `↑(RowSubgroup n la)`), the `Fintype` instances may differ if one comes from a local `haveI : DecidablePred ... := Classical.decPred _` at the proof level and the other from a `haveI` inside the original definition. This makes the two `Finset.univ` propositionally but not definitionally equal.

**Symptoms:** `rfl` fails, `Finset.sum_congr rfl` fails, `congr 1; funext` fails, all with messages about `Finset.univ` not being definitionally equal.

**Fix:** Use `convert rfl using N` (typically `N = 2`) to handle the instance mismatch automatically via `Subsingleton (Fintype α)`. Then close remaining subgoals (e.g., summand equality) with `ext` + `simp`/`rw`.

```lean
-- Two sums that are "the same" but have different Fintype instances
-- ∑ x ∈ @Finset.univ _ inst₁, f x = ∑ x ∈ @Finset.univ _ inst₂, g x
convert rfl using 2
-- Remaining goal: f = g (pointwise)
ext ⟨σ, hσ⟩
simp [...]
```

**Preferred fix:** Add `open scoped Classical` at the section level (before any definitions that use `haveI : DecidablePred ... := Classical.decPred _`). This ensures all `DecidablePred` instances come from the same source, avoiding the mismatch entirely. This is better than `convert rfl` because it prevents the issue rather than patching it.

**Alternative:** Prove equality via `Finsupp.ext` (coefficient-wise) to sidestep sum comparison entirely.

## MonoidAlgebra Coefficient Computation

`MonoidAlgebra k G` is a `def` (not `abbrev`) alias for `G →₀ k`. This means `simp_rw` and `simp only` cannot see through it to apply `Finsupp` lemmas like `Finsupp.smul_apply`, `Finsupp.single_apply`, etc.

**Symptom:** `simp_rw [Finsupp.smul_apply, Finsupp.single_apply]` makes no progress on a goal involving `MonoidAlgebra` terms.

**Fix:** Use `Finset.sum_congr rfl` with `change` to coerce the term to `Finsupp` before `rw`:
```lean
rw [Finset.sum_congr rfl (fun i _ => show _ = _ from by
  change (c • (Finsupp.single g (1 : k))) σ = _
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply])]
```

**Key lemmas for MonoidAlgebra coefficients:**
- `MonoidAlgebra.single_mul_apply`: `(single g r * x) h = r * x (g⁻¹ * h)` (for groups)
- `MonoidAlgebra.mul_single_apply`: `(x * single g r) h = x (h * g⁻¹) * r` (for groups)
- `Finsupp.finset_sum_apply`: `(∑ i ∈ S, f i) a = ∑ i ∈ S, f i a`
- `Finsupp.smul_apply`: `(b • v) a = b • v a` (definitional, but needs coercion via `change`)

## Mathlib API Naming Gotchas

These naming mismatches have bitten multiple agents across waves 44-47. Check this list before reaching for `exact?` or `apply?`.

| What You Want | Wrong Name | Right Name | Notes |
|--------------|-----------|------------|-------|
| `a^(n+1) = a^n * a` | `pow_succ` | `pow_succ'` | `pow_succ` is `a^(n+1) = a * a^n` (reversed) |
| `u⁻¹ * u = 1` (Units) | `Units.inv_mul` | `Units.val_inv_mul` | `inv_mul` is for `Group`, not `Units` |
| Span induction | `Submodule.span_induction` (old sig) | `Submodule.span_induction` (new sig) | Signature changed: now uses a dependent predicate `{p : ∀ x, x ∈ span R s → Prop}` instead of `{p : M → Prop}`. Check the current type with `#check @Submodule.span_induction`. |
| `Finsupp.sum_apply` | `Finsupp.sum_apply` | `Finsupp.finset_sum_apply` | For `(∑ i ∈ S, f i) a = ∑ i ∈ S, f i a`. Needs explicit `(N := C)` type annotation when used with `MonoidAlgebra`. |
| DecidableEq for Finset.image | (missing) | Add `haveI : DecidableEq α := Classical.decEq _` | `Finset.image` requires `DecidableEq` on the codomain. Easy to forget. |
| `DFinsupp.smul_apply` | `DFinsupp.smul_apply` | Use `Finsupp.smul_apply` via `change` | `DFinsupp` and `Finsupp` have different APIs. MonoidAlgebra is `Finsupp`-based. |

**General principle:** When a `rw`/`simp` doesn't fire on a MonoidAlgebra goal, the issue is usually that MonoidAlgebra is a `def` (not `abbrev`), so `simp` can't see through to `Finsupp` lemmas. Use `change` to coerce to `Finsupp` form first.

**When unsure about a lemma name:** Use `#check` or `exact?` on a small test goal. Don't guess and iterate — the 30 seconds spent checking saves 10 minutes of mysterious failures.

## Trace-Based Proof Pattern

When a proof involves showing a group algebra element is nonzero, or bounding the dimension of a representation, try using traces of left-multiplication operators.

**Pattern (Young symmetrizer squared nonzero, Theorem 5.12.2):**
1. Prove `trace_lmul_monoidAlgebra`: `Tr(L_a) = |G| · a(1)` for any group algebra element `a`
2. Show that if `c² = 0` then `L_c` is nilpotent, hence `Tr(L_c) = 0`
3. But `Tr(L_c) = |G| · c(id) = n! ≠ 0` in characteristic zero
4. Contradiction

**When to use:** Whenever the mathematical argument involves "evaluate at the identity element" or "take the trace of left multiplication". This is cleaner than trying to work with the group algebra directly because traces are computed via `LinearMap.trace`.

**Key Mathlib APIs:** `LinearMap.trace`, `MonoidAlgebra.lmul`, `IsNilpotent`, `LinearMap.trace_eq_zero_of_isNilpotent`

## Reynolds Operator / Symmetrization Pattern

For proofs involving invariant subspaces under group actions (e.g., `V^G ≅ Sym^n V`):

1. Construct the symmetrization/averaging map: `symSum(x) = Σ_{σ ∈ G} σ · x`
2. Show `symSum` factors through the quotient (e.g., `SymmetricPower.mk`) via `AddCon.addConGen_le`
3. For injectivity on invariants: `symSum(x) = |G| · x` when `x` is invariant, so if images agree, `|G| · (a - b) = 0`, giving `a = b` by `CharZero`
4. For surjectivity: use `(|G|)⁻¹ · symSum(lift(y))` as preimage

**Key insight:** The Reynolds operator `R = (1/|G|) Σ_σ σ` is an idempotent projection onto invariants. Most invariant-subspace identifications reduce to showing `R` factors through the target construction.

## `decide` for Concrete Finite Computations

For theorems about specific small finite structures (e.g., D₄ quiver with 4 vertices):

```lean
-- Example 6.8.5: concrete D₄ reflection functor computations
example : reflectionResult₁ = expected₁ := by decide
```

**When to use:** The statement involves only `Fin n` for small `n`, concrete matrices, or specific permutations. If `decide` doesn't terminate in reasonable time (< 30s), fall back to `native_decide` or manual proof.

**Caution:** `decide` only works when all types are decidable and small. It won't work for general `n` or abstract algebraic structures.

## Strong Induction on Coordinate Sums (Root System Pattern)

For proofs involving positive roots or dimension vectors where the claim is "every element can be reached from simple elements via reflections":

1. **Induct on `∑ dᵢ`** (the coordinate sum of the dimension vector)
2. **Base case:** When `∑ dᵢ` is minimal (e.g., a simple root `eᵢ`), the claim holds trivially
3. **Inductive step:** Find a "good vertex" `k₀` where `(B·d)_{k₀} > 0` (positive entry in Cartan matrix product)
4. **Key lemma:** If no good vertex exists, construct `d' = d - e_{k₀}` and show `B(d', d') ≤ 0`, contradicting positive-definiteness

**Implementation pattern:** Build helper lemmas systematically:
- Cartan matrix symmetry (`cartanMatrix_symm`)
- Simple reflection properties (`simpleReflection_preserves_bilinearForm`)
- `exists_good_vertex` (by contradiction using positive-definiteness)
- Main induction with `Nat.strongRecOn` or `WellFoundedRelation`

This pattern proved Theorem 6.8.1 (reaching simple roots via reflections) — the linchpin of Gabriel's theorem. It's applicable to any root-system argument requiring structural induction.

## Rank-Nullity for Non-Commutative Hom Spaces

For proofs about `Hom_A(P, M)` where `A` is a non-commutative algebra:

1. Use `LinearMap.finrank_range_add_finrank_ker` for Hom additivity on short exact sequences
2. Use `Submodule.comapSubtypeEquivOfLe` for relating submodule preimages
3. For composition factor simplicity: `covBy_iff_quot_is_simple`

**Key workaround:** `LinearEquiv.congrRight` requires commutativity. For non-commutative algebras, manually construct k-linear equivalences on Hom spaces instead. This was the successful pattern for Proposition 9.2.3.

## Partial Proof Publication Pattern

When a theorem has conceptually independent parts (e.g., symmetric power + exterior power):

1. **Split the theorem** into independent sub-declarations
2. **Prove the tractable part** completely (sorry-free)
3. **Sorry the hard part** with an explicit issue filed
4. **Submit as `proof_partial`** in items.json

This is strictly better than leaving the entire theorem sorry'd. Downstream work that only needs the proved part can proceed. Example: Example 5.19.3 symmetric power was proved completely while the exterior power part (blocked by the ExteriorAlgebra/PiTensorProduct coercion gap) was sorry'd with an issue.

## Verify Statement Correctness Before Proving (Convention Check)

**Before attempting any proof involving Mathlib conventions** (signs, orderings, normalizations), verify the statement is correct with a small concrete example.

**The problem:** Convention mismatches between the book and Mathlib silently make statements unprovable. These appear as "unprovable goals" rather than type errors. Agents spend entire sessions trying proof strategies before discovering the statement itself is wrong.

**Known convention differences:**
- `vandermondePoly` uses `∏_{i<j}(x_j - x_i)` (Mathlib) vs the book's `∏_{i<j}(x_i - x_j)`, differing by `Equiv.Perm.sign(Fin.revPerm)`
- Alternating sum conventions may differ in sign
- Partition/Young diagram indexing conventions may differ

**Verification pattern:**
```lean
-- Before proving: test with n=2 or smallest non-trivial case
#eval do
  let lhs := <your_LHS_computed_for_n_2>
  let rhs := <your_RHS_computed_for_n_2>
  return (lhs == rhs)  -- should be true!
```

If the concrete example fails, the statement has a convention bug. Fix the statement before attempting the proof. This check takes 5 minutes and can save an entire session.

## Dependent Type Rewriting Patterns

Direct `rw` on dependent types is a recurring friction point. These patterns work:

### Pattern 1: `congrArg` with `Fin.ext` (for Fin-indexed access)
When you need to rewrite a `Fin` value inside a dependent context (e.g., cycle access, list indexing):
```lean
-- Instead of: rw [some_fin_equality]  -- fails with "motive is not type correct"
-- Use:
exact congrArg cycle.get (Fin.ext (by omega))
```

### Pattern 2: `suffices ∀ s, ...` (generalize-then-instantiate)
When rewriting a term `b` that appears in dependent types like `hab : a ≤ b`:
```lean
suffices ∀ s, statement_about s by
  convert this ?_ <;> exact the_specific_equality
intro s
-- Now prove for arbitrary s (no dependent type issues)
```

### Pattern 3: `show`/`change` for `Fin.cons` goals
`Fin.cons_zero`/`Fin.cons_succ` don't match literal `(0, _)`/`(n+1, _)` syntactically:
```lean
-- Instead of relying on simp to reduce Fin.cons:
show <explicit_expected_form>  -- or use `change`
-- Then apply the appropriate lemma
```

### Pattern 4: `convert rfl using N` for Fintype instance mismatches
When two `Finset.univ` expressions use different `Fintype` instances:
```lean
convert rfl using 2  -- handles instance mismatch via Subsingleton
```

### Pattern 5: `unfold + match` for `Decidable.casesOn` composition
When two functions both use `match inst a b, inst c d with ...` on the same decidable instances,
their composition should reduce to identity. Standard tactics (`rw`, `simp`, `▸`, `split`, `cases`)
ALL fail because the scrutinee is an opaque application. Use `match` in the proof itself:
```lean
-- After unfolding both function definitions:
unfold foo bar
simp only [id]  -- remove @id wrappers from `change`/`unfold` in tactic definitions
revert e  -- revert the variable so its type enters the goal
exact match inst a b, inst c d with
| .isFalse h, _ => fun _ => (absurd rfl h).elim  -- vacuous
| .isTrue _, .isTrue h => fun _ => (absurd h hne).elim  -- vacuous
| .isTrue _, .isFalse _ => fun _ => rfl  -- both matches reduce to id
```
**Limitation**: This works for arrow-level (homogeneous) equalities but NOT for Sigma-level
equalities where the Sigma TYPE itself contains `Decidable.casesOn`. For Sigma-level round-trips,
define both conversion directions in the SAME file as the type definition, or use `Equiv.ofBijective`.

**Stop after 3 failed approaches** — if `match`-based proof doesn't work, the issue is structural
(needs upstream definition changes), not tactical.

### Pattern 6: freeze a derived term before `rw [h]` substitutes its variable

When a hypothesis `h : f = <expr>` is rewritten into a goal that *also* mentions
`f` **inside** a derived term like `detExp f`, `Nat.find _`, `degree f`, etc.,
`rw [h]` replaces **every** `f` — including the one inside `detExp f` — corrupting
the exponent/index (symptom: the goal sprouts `detExp (<expr>)` where you wanted a
plain `detExp f`). Freeze the derived term as an opaque local first:
```lean
obtain ⟨s, hsdef⟩ : ∃ s, detExp f = s := ⟨_, rfl⟩
rw [hsdef] at h ⊢   -- now the goal/h talk about `s`, not `detExp f`
rw [h]              -- safe: `s` contains no `f`
-- recover at the end:  rw [hsdef] at <the ≤ fact>; omega
```
Cleaner than `nth_rewrite`/`conv` targeting because it removes the `f`-dependence
everywhere at once. Use it whenever the minimal-exponent / `Nat.find` value of the
very element you are rewriting appears in the goal.

## Issue Description Feasibility Check

**Issue descriptions sometimes contain mathematically incorrect proof strategies.** Before committing to a proof approach described in an issue:

1. **Spend 10 minutes verifying feasibility** — check whether the described approach actually works mathematically
2. **Look for hidden complexity** — "the terms vanish individually" may only be true in special cases
3. **Test with small examples** — if the strategy says "by counting" or "by cancellation", check on a 2×2 or 3×3 case

**Evidence:** The alternating Kostka delta identity issue claimed "all non-rev terms vanish individually" — true only for λ=ν, not in general. The hook quotient identity was estimated at difficulty 2/3 but required 3 fundamentally different approaches before being decomposed into 4 sub-issues.

## Statement Correctness: Common Missing Hypotheses

Multiple sessions were wasted proving statements that turned out to be false due to missing hypotheses. Check for these **before** attempting the proof:

| Missing Hypothesis | Symptom | Example |
|-------------------|---------|---------|
| `[IsAlgClosed k]` | Classification/uniqueness fails | Corollary9_7_3 needed algebraic closure for basic algebra existence |
| `[IsBasicAlgebra A]` | Morita equivalence `B ≅ eAe` fails without basic assumption | MoritaStructural was false without this |
| `[CharZero k]` | Averaging/Reynolds operator arguments fail | Theorem5_18_4 `symGroupImage_faithful` needed char 0 |
| `Module.Finite k V` | Finite-dimensionality needed for rank-nullity | MoritaStructural needed explicit finiteness |
| Orientation constraints | Sink/source confusion in quiver proofs | Prop6_6_6 sink vs source cases |

**Pattern:** If a proof fails at a fundamental level (not a tactic issue but a mathematical impossibility) after 1 serious attempt, **suspect a statement bug**. Check the book's hypotheses carefully before trying more proof strategies.

## Sorry-to-Helper Extraction Pattern (Endgame)

The dominant value-creation pattern in the endgame. Instead of trying to prove a hard sorry directly, extract it into a well-documented helper lemma.

**When to use:** Any sorry that has resisted 2+ attempts, or any theorem with 3+ sorries where the proof structure is unclear.

**Pattern:**
```lean
-- BEFORE: monolithic sorry
theorem main_result : conclusion := by sorry

-- AFTER: structured proof with isolated helper sorries
private lemma helper_1 : intermediate_fact_1 := sorry
private lemma helper_2 : intermediate_fact_2 := sorry

theorem main_result : conclusion := by
  have h1 := helper_1
  have h2 := helper_2
  exact final_combination h1 h2
```

**Why this is high-value:**
1. The main theorem file now has a complete proof term — only helpers are sorry'd
2. Each helper sorry is independently claimable by a future agent
3. The proof structure documents exactly what's needed, reducing onboarding time
4. Partial progress is visible and committable

**Evidence (waves 25-27):**
- Theorem5_25_2: parts 1, 2, 3a proved; sorry isolated in 6 helpers (#1545, #1562)
- Theorem5_26_1: forward direction decomposed into helper lemmas (#1568, #1569)
- Theorem9_2_1: sorry decomposed into targeted sub-goals (#1567)
- Corollary9_7_3: sorry pushed to infrastructure files (#1560)

**Infrastructure absorption pattern:** When helper lemmas are reusable across theorems, extract them into dedicated infrastructure files (e.g., `Infrastructure/BasicAlgebraExistence.lean`, `Infrastructure/MoritaStructural.lean`). This cleanly separates mathematical infrastructure from theorem proofs.

## SMul Instance Diamond Bridge (Wave 43)

When two `Module` instances on the same type are propositionally but not definitionally equal (common with equivalences, transport, or `restrictScalars`), direct `rfl` and `congr` fail.

**Symptoms:**
- `rfl` fails on what looks like `r • x = r • x`
- Error mentions two different `SMul` or `Module` instances
- `convert` leaves `HEq` goals between instances

**Pattern: Element-level proof with conv rewrite**
```lean
-- Two instances: inst₁ and inst₂ on the same carrier type M
-- You have: h : ∀ (r : R) (m : M), @SMul.smul R M inst₁.toSMul r m = @SMul.smul R M inst₂.toSMul r m
-- Goal: some statement involving inst₂ that you can prove using inst₁

ext m  -- reduce to element level
show @SMul.smul R M inst₂.toSMul r m = ...
conv_lhs => rw [show @SMul.smul R M inst₂.toSMul r m = @SMul.smul R M inst₁.toSMul r m from (h r m).symm]
-- Now the goal uses inst₁, which you can work with
```

**Evidence:** This resolved equivEndAlgEquiv scalar preservation in MoritaStructural (#2082), the hardest sub-task in Cluster E. The key was proving scalar action agreement at element level, then using `conv_lhs => rw [...]` to swap instances within larger expressions.

**When NOT to use:** If the instances are definitionally equal but Lean can't see it, try `change` or `show` first. This pattern is for genuinely different instances that happen to agree propositionally.

## Recognizing Design-Level Blockers vs Proof Difficulty (Wave 43)

**Critical distinction:** A "hard sorry" needs more effort on the same approach. A "design blocker" means the current approach is provably wrong and no amount of effort will fix it.

**How to tell them apart:**

| Signal | Proof Difficulty | Design Blocker |
|--------|-----------------|----------------|
| Counterexample exists | No | Yes — approach fails on specific inputs |
| "All other swaps also fail" | No | Yes — no variant of the approach works |
| Missing lemma | Yes — prove it | Maybe — check if lemma is actually false |
| Tactic timeout | Yes — simplify | No — not relevant |
| 3+ failed attempts, all similar | Yes — try harder | Check for counterexample first |

**The garnir_columnInvCount_decrease lesson (issue #2055):**
The swap-based approach was supposed to decrease `columnInvCount'` for the multi-column case. Analysis showed:
1. For partition (2,1,1), σ with filling [0,3,2,1], the swap preserves the column inversion at (2,3)
2. ALL other possible swaps for this σ INCREASE the count
3. The Garnir element approach gives `0 = 0` (trivial identity) due to row absorption

This is NOT "hard" — it's provably impossible with the current metric. The fix requires changing the induction measure or the entire proof architecture.

**Action when you identify a design blocker:**
1. Document the counterexample in a GitHub issue
2. Propose 2-3 alternative approaches
3. Do NOT attempt further proofs on the broken approach
4. Mark difficulty as 9-10 and add `replan` label

## Bypass Strategies That Worked (Waves 41-43)

Several sorry reductions succeeded by finding simpler approaches than originally estimated:

**1. Mackey machine without Clifford theory (#2047, #2049)**
- Original estimate: ~500 lines of Clifford theory infrastructure
- Actual approach: Direct construction using Frobenius reciprocity + simple subrepresentation existence
- Lesson: Always try the simplest approach first. Infrastructure estimates are often pessimistic.

**2. KLinearMoritaEquivalent bypass (#2073)**
- Original approach: Prove k-linear Morita equivalence (requires tensor product infrastructure)
- Bypass: Skip k-linearity entirely and work with the underlying additive equivalence + separate scalar preservation
- Lesson: If a type class requirement is hard to satisfy, check if you can decompose the proof to avoid needing the full type class.

**3. charValue stability chain (#2068)**
- Original approach: Direct polynomial manipulation
- Actual approach: Induction on the stability chain length, reducing each step to a base case
- Lesson: When polynomial arguments are complex, look for inductive structure.

## MonoidAlgebra.lift Pattern for Group Algebra Homomorphisms

When constructing algebra homomorphisms out of `MonoidAlgebra k G`, use `MonoidAlgebra.lift`:

```lean
-- MonoidAlgebra.lift : (G →* A) → (MonoidAlgebra k G →ₐ[k] A)
-- Given a group hom f : G →* A, lift it to an algebra hom
def myAlgHom : MonoidAlgebra k G →ₐ[k] A :=
  MonoidAlgebra.lift k G A f
```

**Key insight:** Don't try to define algebra homs on `MonoidAlgebra` by working with `Finsupp` directly. `MonoidAlgebra.lift` is the universal property and handles all the algebraic structure automatically.

**Companion pattern:** Use `Finsupp.induction_linear` (cases: zero, add, single) instead of `Finsupp.induction` when proving properties of `MonoidAlgebra` elements. The `induction_linear` variant is easier because it doesn't require tracking a `not_mem_support` hypothesis.

## HEq and eqRec Patterns for Dependent Type Transport

When working with dependent types where direct `rw` fails (common in reflection functor proofs):

### Pattern: `eqRec_heq_self` with field projection motive

When you need to show that transporting a value along a proof and then projecting a field gives the same result:

```lean
-- When goal involves: (Eq.rec x proof).field = x.field
-- Use eqRec_heq_self to get HEq between the transported and original value
have : HEq (Eq.rec x proof) x := eqRec_heq_self proof x
-- Then use field projection congruence
exact heq_of_field_projection this
```

### Pattern: `Subsingleton.elim` for Decidable proof irrelevance

When two `Decidable` instances block definitional equality:

```lean
-- When inst₁ inst₂ : Decidable P appear in the goal and prevent reduction
have : inst₁ = inst₂ := Subsingleton.elim _ _
subst this  -- Now only one instance, and dif_pos/dif_neg can reduce
```

This was critical for the `reversedArrow_ne_ne_twice` proof in Prop6_6_6 (#1561).

If the issue's strategy doesn't work after verification, **update the issue comment** with your findings before trying alternative approaches. This saves the next agent from repeating your investigation.

## Module Instance Agreement Pattern

When two `Module R M` instances exist on the same type (e.g., one from `Representation.asModule` and one from `Submodule.module`), direct `rfl` or `congr` fails because the instances are constructed differently.

**Pattern: Prove pointwise agreement via algebra induction**

```lean
-- Two Module (MonoidAlgebra ℂ G) M instances that act identically
-- inst₁ comes from Representation.asModule, inst₂ from Submodule.module
-- They agree on all elements but are not definitionally equal

-- Step 1: Prove the SMul actions agree on generators
have smul_agree : ∀ (g : G) (m : M), @SMul.smul _ _ inst₁.toSMul (single g 1) m
    = @SMul.smul _ _ inst₂.toSMul (single g 1) m := by
  intro g m; simp [...]

-- Step 2: Lift to all MonoidAlgebra elements via induction
have : inst₁ = inst₂ := by
  ext a m
  induction a using MonoidAlgebra.induction_on with
  | single g r => simp [smul_agree g m, ...]
  | zero => simp
  | add x y hx hy => simp [add_smul, hx, hy]
```

**When to use:** Module instance diamonds from `FDRep`/`Representation.asModule` vs. submodule inheritance. This was critical for the FDRep bridge (#1601) — `spechtModuleFDRep_simple` required proving `IsSimpleModule` transfers across instance-incompatible equivalences.

**Companion:** Use `Finsupp.induction_linear` instead of `MonoidAlgebra.induction_on` when working with Finsupp directly (cases: zero, add, single — no `not_mem_support` hypothesis needed).

## Submodules of `Representation.asModule`: Missing Instances

When working with a simple submodule `m : Submodule (MonoidAlgebra ℂ A) ρ.asModule`, several instances needed for Schur-type arguments must be registered explicitly:

```lean
-- FiniteDimensional over the base field (not auto-derived from the algebra module)
haveI : FiniteDimensional ℂ m :=
  Module.Finite.of_injective (m.subtype.restrictScalars ℂ) Subtype.val_injective

-- IsMulCommutative for MonoidAlgebra (not auto-derived from CommSemiring)
haveI : IsMulCommutative (MonoidAlgebra ℂ A) := ⟨⟨mul_comm⟩⟩

-- Nontrivial (IsSimpleModule.nontrivial is a theorem, not an instance; both args explicit)
haveI : Nontrivial m := IsSimpleModule.nontrivial (MonoidAlgebra ℂ A) ↥m
```

**Connecting FDRep action to MonoidAlgebra action:** `W.ρ ⟨a, 1⟩` and `MonoidAlgebra.of ℂ A a • v` are related through `Representation.asAlgebraHom_of`, which is proved by `simp` (not `rfl`). Use explicit `rw [show ... from rfl, show ... from (asAlgebraHom_of ..).symm]` to bridge the gap.

**When to use:** Any proof that extracts characters from representations of commutative groups (e.g., `exists_character_in_rep` in the Mackey machine, #2036).

## Building `≃ₗ[k[G]]` equivalences between `asModule`s (glue-A/B, #4714/#4715)

When promoting a `k`-linear intertwiner to a `MonoidAlgebra k G`-linear equivalence (the Schur-Weyl Step E "glue" cluster, `Chapter5/PolynomialGLDecomposition.lean`), three instance/unification stalls recur:

1. **Keep both sides genuine `asModule`s; never map straight to a raw `DirectSum` of carriers.** A `k`-linear equiv `e : V ≃ₗ[k] ⨁_β W` has codomain `DirectSum β (fun _ => W)`, and bare `W` carries *no* `k[G]`-module, so the `r • _` on the target in `map_smul'` is a **stuck instance** ("typeclass instance problem is stuck", `(i : ?m) → AddCommMonoid …`). Land in `asModule (Representation.directSum (fun _ => σ))` first (both sides are `asModule`s of representations, so `single_smul` and the `k[G]`-action resolve), then `.trans asModule_directSum_equiv` (glue-A) to reach `DirectSum β (fun _ => asModule σ)`.

2. **Pin `Representation.directSum`'s family `V` explicitly.** `Representation.directSum (fun _ : β => σ)` leaves `V : β → Type` as a higher-order-unification metavar → the same stuck-instance error. Write `Representation.directSum (V := fun _ => W) (fun _ : β => σ)`, and call glue-A as `asModule_directSum_equiv (ι := β) (V := fun _ => W) (fun _ : β => σ)`. Use the *same* `(V := …)` everywhere so the `.trans` typechecks.

3. **`DirectSum.ext`'s family implicit is named `β`.** If your index type is also `β`, supply it: `refine DirectSum.ext (β := fun _ : β => W) fun i => ?_`. Then close componentwise with `tprodSplitEquiv_tmul_apply`, `Representation.directSum_apply`, `DirectSum.lmap_apply`, `DirectSum.smul_apply`, `map_smul`.

The `map_smul'` of the `asModule`-to-`asModule` aux reduces to the carrier-level intertwiner via `rw [single_smul, single_smul, map_smul]; simp only [Representation.asModuleEquiv]; congr 1; exact <intertwiner>` (`asModuleEquiv` is `LinearEquiv.refl`, so it normalizes away with the def-unfold alone — `LinearEquiv.refl_apply` is then an unused simp arg).

**Dot notation on a `Representation`-typed value resolves to `MonoidHom`, not your `Representation.*` lemmas.** `Representation k G V` is definitionally `G →* (V →ₗ[k] V)`, so for `ρ : Representation k G V` the term `ρ.myLemma` elaborates as `MonoidHom.myLemma ρ` and fails with `Invalid field 'myLemma': … does not contain MonoidHom.myLemma`. Even when you *defined* `Representation.myLemma`, you must call it with the **fully-qualified name** `Representation.myLemma ρ …` (not `ρ.myLemma`). This bit me defining `Representation.stableSubmodule` (#4902) — both the definition's own `@[simp]` mem-lemma and every call site needed the explicit `Representation.stableSubmodule ρ …` form.

## FDRep Morphism Extensionality Patterns

FDRep morphisms are `Action.Hom` wrapping `FGModuleCat.Hom` wrapping `ModuleCat.Hom` wrapping `LinearMap`. Proving `f = g` for FDRep morphisms requires decomposing through all layers.

**Pattern 1: Standalone lemma proofs** (f ≫ g = 0, f ≫ g = 𝟙, etc.)
```lean
apply Action.Hom.ext
simp only [Action.comp_hom, Action.zero_hom]  -- or Action.id_hom
apply FGModuleCat.hom_ext
ext c
-- Now at LinearMap level. Use `show` to set the expected form.
show <expected_pointwise_equality>
```

Key lemmas: `Action.comp_hom`, `Action.zero_hom`, `Action.id_hom` (from `Mathlib.CategoryTheory.Action.Basic` and `Limits`).

**Pattern 2: Term-mode** (useful in `exact` or `refine`)
```lean
exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => ...)))
```

**Pattern 3: Inside `where` clause `comm` proofs**
The `comm` field is already at FGModuleCat level. Use:
```lean
comm g := by
  apply FGModuleCat.hom_ext; ext ⟨f, hf⟩
  -- For subtypes: apply Subtype.ext; funext g
  show <expected_pointwise_form>
  ...
```

**WARNING**: With high `maxHeartbeats`, Lean may eagerly reduce definitions, causing `show`/`change` to fail because the normal form differs from the expected mathematical form. If `show` fails, try `sorry` and revisit with lower heartbeats or restructured definitions.

**Evidence:** Discovered during principalSeries_decomp (#1647, #1674) — ~15 build iterations were spent fighting FDRep morphism equality before these patterns were identified.

## PID Structure Theorem Bridge Pattern

When using Mathlib's `Module.torsion_by_prime_power_decomposition` to decompose a module over a PID (e.g., ℂ[X]-modules for nilpotent operators), the output is a `DirectSum` of quotient modules `ℂ[X] ⧸ Ideal.span {X^nᵢ}`. Bridging this to concrete vector subspaces requires careful infrastructure.

**Pattern:**

```lean
-- Step 1: Get the PID decomposition
-- The polynomial ring ℂ[X] is a PID (EuclideanDomain → PrincipalIdealRing)
-- T : V →ₗ[ℂ] V nilpotent gives a ℂ[X]-module structure on V via X ↦ T

-- Step 2: Map quotient modules to kernel spaces
-- Key fact: ℂ[X] ⧸ Ideal.span {X^n} ≅ ker(T^n) / ker(T^(n-1)) as ℂ-vector spaces
-- This requires:
private lemma quotient_poly_dim (n : ℕ) :
    Module.finrank ℂ (Polynomial ℂ ⧸ Ideal.span {X ^ n}) = n := sorry

-- Step 3: Track dimensions through the decomposition
-- dim(ker T^k on ℂ[X]/(X^n)) = min(k, n)
-- This determines the Jordan block structure
```

**Key difficulties:**
- The `Module.torsion_by_prime_power_decomposition` API produces existential types (primes, exponents) that need careful handling with `Exists.choose`
- ℂ[X]-module structure on V must be constructed explicitly from the linear map T
- Dimension tracking through quotients requires `Module.finrank` lemmas for polynomial quotient rings

**Evidence:** Problem6_9_1 Case 2b (#1617) — proved 4/5 nilpotent decomp cases using this bridge. The remaining case (2b-ii) is blocked on the kernel dimension computation.

## Type Class Shadowing for Instance Pollution

When a typeclass instance leaks through from an outer scope and interferes with proof goals, use `letI` to shadow it with the correct instance.

**Pattern:**
```lean
-- Problem: `inst✝ : Quiver Q` in context is wrong/opaque, preventing reduction
-- Solution: Shadow it with the concrete instance you want
letI : Quiver Q := concreteQuiverInstance
-- Now tactics see the concrete instance, not the opaque one
```

**When to use:** Proposition6_6_6 hdim proof (#1598) needed this to shadow a `Quiver` instance that was preventing `simp` from reducing. Also useful when `inferInstance` finds the wrong instance in the presence of multiple candidates.

**Caution:** Only shadow when you're sure the shadowed instance agrees with the one you're replacing — otherwise proofs may become inconsistent.

## Inductive Construction on Finite Sets (Finset.strongInduction)

For existence proofs that build a structure incrementally on a finite set (e.g., constructing orderings, colorings, assignments), use `Finset.strongInduction` or equivalent well-founded recursion on `Finset.card`.

**Pattern:**
```lean
-- Construct an admissible ordering of vertices by repeatedly finding local sinks
-- At each step, remove a local sink from the remaining set and recurse

theorem exists_ordering : ∃ (l : List V), l.Nodup ∧ l.toFinset = Finset.univ ∧ P l := by
  -- Use strong induction on |remaining vertices|
  suffices ∀ (S : Finset V), ∃ (l : List V), l.Nodup ∧ l.toFinset = S ∧ P' S l from
    this Finset.univ
  intro S
  induction S using Finset.strongInduction with
  | ind S ih =>
    -- Find an element to remove (e.g., a local sink)
    obtain ⟨v, hv, hprop⟩ := exists_special_element S hS
    -- Recurse on S \ {v}
    obtain ⟨l, hl⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
    exact ⟨v :: l, ...⟩
```

**Evidence:** admissibleOrdering_exists (#1613) — constructed admissible orderings for Dynkin quivers by iteratively removing local sinks, proved via `Finset.strongInduction`. Helper lemmas for sink existence were proved separately using a counting argument on forward/backward edge pairs.

**Key helper pattern:** When the "special element" existence requires a counting/pigeonhole argument, prove it as a separate lemma first. The inductive construction is cleaner when the "find next element" step is a black box.

## Decidable.casesOn Workaround Patterns (Quiver Reflection Functors)

The `reflectionFunctorPlus`/`Minus` definitions use `Decidable.casesOn` via `if h : v = i then ... else ...`. Outside these definitions, Lean cannot reduce through `Decidable.rec`, causing type mismatches. Three workaround variants exist, discovered across PRs #1723, #1735, #1739, #1760:

### Variant A: Revert-Unfold-Rewrite-Intro (most common)

Used 6+ times across Proposition6_6_7 and Proposition6_6_6. The canonical pattern for ne/ne cases:

```lean
-- Fix the decidable instances to their known values
have h_da : DecidableEq Q a' i = .isFalse ha' := by
  cases DecidableEq Q a' i with | isTrue h => exact absurd h ha' | isFalse _ => rfl
have h_db : DecidableEq Q b' i = .isFalse hb' := by
  cases DecidableEq Q b' i with | isTrue h => exact absurd h hb' | isFalse _ => rfl
-- Revert ALL dependent variables
revert hw w e' hsubrep Sb Sa
-- Unfold the definitions containing Decidable.casesOn
unfold reflFunctorMinus_equivAt_ne reflectionFunctorMinus reversedAtVertex ReversedAtVertexHom
simp only []
-- Rewrite with the fixed decidable values
rw [h_da, h_db]
simp only []
-- Re-introduce the variables
intro Sa Sb hsubrep e' w hw
```

### Variant B: Refine-Match (for definitions)

Preferred when defining equivs at specific vertices:

```lean
refine match inst_dec i i with
| .isFalse h => absurd rfl h
| .isTrue _ => ?_
```

Avoids `Eq.mpr` wrappers from `rw` that block downstream computation.

### Variant C: Two-variable fix (for naturality proofs)

When both equality and inequality branches need fixing simultaneously:

```lean
have h_ii : inst_dec i i = .isTrue rfl := by match ...
have h_bi : inst_dec b i = .isFalse hb := by match ...
```

### Key Insight: Avoid `= 0` with Decidable dependency

When `0 : F(rho).obj i` has `Decidable.rec` in its type, prove `f x = mkQ(0)` (where `0 : DirectSum` has no Decidable dependency) then use `map_zero`.

## Instance Construction via `show ... from inferInstance`

When a definition is a type alias (e.g., `AlgIrrepGL` wrapping `SchurModuleSubmodule`), derive instances by showing they follow from the underlying type:

```lean
noncomputable instance AlgIrrepGL.addCommGroup : AddCommGroup (AlgIrrepGL n lam k) :=
  show AddCommGroup (SchurModuleSubmodule k n lam.toNatWeight) from inferInstance
```

Works for `AddCommGroup`, `Module k`, `Module.Finite k`. Discovered in PR #1752. More reliable than `@inferInstance` or manual instance construction.

## Tabloid and Young Tableau Infrastructure Patterns

### Quotient type via Setoid (PR #1754)

```lean
-- TabloidSetoid: two fillings are equivalent if row assignments agree up to permutation
instance : Setoid (Filling n la) where
  r f g := ∃ σ ∈ RowSubgroup n la, σ • f = g
  iseqv := ⟨fun _ => ⟨1, one_mem _, one_smul _ _⟩,
            fun ⟨σ, h, e⟩ => ⟨σ⁻¹, inv_mem h, by rw [← e]; group⟩,
            fun ⟨σ, h1, e1⟩ ⟨τ, h2, e2⟩ => ⟨τ * σ, mul_mem h2 h1, by rw [← e2, ← e1]; group⟩⟩
```

### Fintype for quotient types

```lean
noncomputable instance : Fintype (Tabloid n la) := by
  haveI : DecidableRel (TabloidSetoid n la).r := Classical.decRel _
  unfold Tabloid
  exact Quotient.fintype (TabloidSetoid n la)
```

Must provide `DecidableRel` via `Classical.decRel` before `Quotient.fintype` works.

### False theorem discovery pattern (PRs #1769, #1771)

`RelColumnSubgroup_ne_tabloid` was initially stated with wrong conjugation direction (`σ_T Q_λ σ_T⁻¹` vs `σ_T⁻¹ Q_λ σ_T`). A concrete counterexample for partition (2,2) was found. **Always verify conjugation/action direction with a small example before proving.**

## Orbit-Stabilizer via Burnside's Lemma (PR #1755)

For counting arguments involving group orbits on combinatorial structures:

1. `FiberPerm h ≅ stabilizer h` via `Equiv.subtypeEquiv`
2. Sigma swap `(Σ h, stab h) ≅ (Σ σ, fixedBy σ)` via `Equiv.subtypeProdEquivSigmaSubtype` + `Equiv.prodComm`
3. Burnside: `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
4. Orbit classification: `Equiv.ofBijective` with `Quotient.lift` on fiber sizes

Use `Equiv.ofFiberEquiv` to show structures with the same fiber sizes are in the same orbit — leverages `Fintype.equivOfCardEq` per fiber.

## Simp Lemma Instability Across Lean/Mathlib Versions

`simp` arguments that work locally may stop working after Lean/Mathlib version bumps (PR #1767 was entirely a CI fix for this). Common culprits:
- `LinearEquiv.refl_apply`, `LinearEquiv.coe_toLinearMap` — may be removed from simp set
- `Submodule.coe_mk` — behavior changes across versions

**Mitigation:** After CI failure on `simp` calls, try removing specific simp lemmas rather than adding new ones. Use `simp?` to find the current minimal simp set.

## Known Dead-Ends (Don't Waste Context Windows)

These are proof approaches that multiple agents have attempted and failed. Don't retry them without new Mathlib infrastructure.

### ExteriorAlgebra / PiTensorProduct Coercion Gap

**Problem:** Proving `∧^n V ≅ (V⊗ⁿ)^{Alt}` (the alternating subspace of the tensor power is the exterior power) requires bridging two incompatible Mathlib constructions:
- `exteriorPower n V` is a `Submodule` of `ExteriorAlgebra V` (built on `CliffordAlgebra`)
- The alternating subspace lives in `PiTensorProduct` (or `TensorProduct`)

**What fails:**
- `exteriorPower.linearMap_ext` creates `compAlternatingMap` goals with `↑` coercions that `simp` cannot resolve
- `Fintype.sum_equiv` gets type mismatches when goals are wrapped in `compMultilinearMap`
- `congr 1` strips one coercion layer but leaves incompatible goal forms

**Status:** 3+ agents have attempted this (Example 5.19.3 exterior part). All failed. **Sorry and move on.** This requires new Mathlib bridging infrastructure between `ExteriorAlgebra` and `PiTensorProduct`.

### Dependent Type Issues with `if`-branching `obj` Fields

**Problem:** When a `QuiverRepresentation`-like structure has `obj v := if v = i then T₁ else T₂`, filling `Module` instance fields fails because the `AddCommMonoid` instance becomes opaque after filling.

**Status:** Documented in detail above (Type-Level If/Else Diamond Issue). The workaround is to sorry the `instModule` field. Don't attempt to solve the diamond — it requires a structural refactor.

### Decidable.casesOn Opacity in reflectionFunctorPlus Proofs

**Problem:** `reflectionFunctorPlus` (Definition 6.6.3) defines vertex objects and maps using `Decidable.casesOn` on the `DecidableEq` instance. Any proof that needs to relate the F⁺ maps to the underlying representation maps requires reducing this `casesOn`, but:
- `rw`/`simp` with `inst a i = .isFalse ha` fails: "motive is not type correct"
- `generalize` on `inst a i` fails: "result is not type correct"
- Term-mode `match` on `inst a i` resolves the outer match but does NOT substitute `inst a i` in the inner goal (non-dependent motive inferred)
- `exact rfl` fails: types are not definitionally equal across the casesOn boundary

**Affected items:** Prop 6.6.7 (all sink-case sorry's), Prop 6.6.6 (equivAt lemmas), any proof composing reflection functor maps.

**What to do — depends on which vertices are involved:**
- **Both vertices ≠ i (ne_ne case):** SOLVABLE. Use `.trans` composition of equivAt_ne equivs instead of monolithic equivAt_ne_sink/source. Then apply API lemmas (`reflFunctorMinus_mapLinear_ne_ne`, `reflFunctorPlus_mapLinear_ne_ne`, `reversedArrow_ne_ne_twice`) via `rw`. See Proposition6_6_6_sink ne_ne case for the working pattern.
- **One vertex = i (ne_eq or eq_ne case):** BLOCKED. The `(reflectionFunctor...).obj i` type is opaque — API lemma statements can't even typecheck because Lean can't see through `Decidable.casesOn` to recognize it as a quotient/kernel. **Sorry immediately.** The fix requires refactoring `reflectionFunctorPlus`/`Minus` to avoid `Decidable.casesOn`.

**Workaround for API lemma application:** When proofs have local `let instR := reversedAtVertex Q i` bindings, Lean's type class synthesis finds `instR` for `[Quiver Q]` instead of the registered `inst`, causing "synthesized type class instance is not definitionally equal" errors when applying API lemmas. **Fix**: Extract the computation as a separate top-level theorem (outside the proof) where `instR` doesn't exist as a local binding. Use explicit `@`-prefixed terms with `Etingof.reversedAtVertex Q _ inst i` to control instance resolution. See `Φ_comp_source_eq_zero` in Proposition6_6_6.lean and `reflFunctorPlus_mapLinear_eq_ne` in Definition6_6_3.lean for examples of this pattern.

## Common Failure Modes

### Explicit Bijection Construction (Counting Proofs)

When proving cardinality results or counting arguments, prefer explicit bijection constructions over abstract reasoning:

1. Define the forward map explicitly
2. Define the inverse map explicitly
3. Prove round-trip properties

This pattern proved GL2 conjugacy class cardinalities (disc=0 split into g01=0 and g01≠0 cases) and the `invColorEquivMC` equivalence (σ-invariant colorings ↔ monochromatic colorings). It works well because Lean's `Equiv` API is rich and `simp` handles most round-trip goals.

**Avoid `Finset.univ.image f` + `Finset.card_image_of_injective` for cardinality proofs.**
This approach requires `DecidableEq` on the codomain, causes elaboration issues with
`fin_cases` (producing unreduced `σ ^ ↑((fun i ↦ i) ⟨0, ⋯⟩)` terms), and anonymous
constructor matching in `Finset.mem_image` existentials is fragile. Instead use
`Fintype.card_congr` with an explicit `Equiv`, or `Finset.card_union_of_disjoint`.

### Well-Founded Recursion on Natural Measures

For recursive definitions where termination isn't structural:

1. Identify a natural `ℕ`-valued measure that strictly decreases
2. Prove the decrease lemmas as separate helper lemmas first
3. Define the function using `WellFoundedRelation` or `termination_by`

This pattern defined the hook walk weight function with termination via strictly decreasing hook length. Prove the decrease lemmas before attempting the definition — interleaving them causes elaboration issues.

### Fin.cons + Equiv.ofBijective for Explicit Equivalences

When constructing an equivalence between a finite type and `Fin n` (e.g., for counting conjugacy classes, enumerating roots):

1. Build the forward map inductively using `Fin.cons` to handle each case
2. Prove injectivity by case analysis on each pair
3. Prove surjectivity by showing the image covers all elements
4. Combine via `Equiv.ofBijective`

```lean
-- Example: equivalence between conjugacy class representatives and Fin 4
def classEquiv : Fin 4 → ConjClass G :=
  Fin.cons scalar (Fin.cons splitSS (Fin.cons parabolic (Fin.cons elliptic Fin.elim0)))

theorem classEquiv_bijective : Function.Bijective classEquiv := by
  refine ⟨fun i j h => ?_, fun c => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [classEquiv]
  · obtain ⟨g, rfl⟩ := c.exists_rep
    -- case analysis on g to find preimage
    sorry

noncomputable def classFinEquiv : ConjClass G ≃ Fin 4 :=
  (Equiv.ofBijective classEquiv classEquiv_bijective).symm
```

This pattern proved GL₂(𝔽_q) conjugacy class cardinalities and `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`. It works well because `fin_cases` handles all pairs for injectivity automatically.

### Finite set of representatives indexed by a finite predicate-set

"Finitely many iso classes" / "finite covering set of representatives" goals (the
Ch6 finite-type definition, the orbit-counting chain #4780–#4786) reduce to:
pick one representative per element of a finite set `S = {x | P x}` (e.g. the
positive roots, finite by Theorem 6.5.2a), then show the representatives form a
finite set. Two gotchas, both hit in #4779:

- `choose!` on `∀ x, P x → ∃ y, Q y` returns a **dependent** function
  `g : ∀ x, P x → β` — the hypothesis argument is **kept**, not dropped. So `g`
  is not a plain `α → β` and `Set.image g` / `hS.image g` fail with a type
  mismatch.
- Use `Set.Finite.dependent_image` for finiteness: from `hS : S.Finite` and
  `F : ∀ x ∈ S, β` it gives `{y | ∃ x hx, F x hx = y}.Finite`. Let the set be
  inferred — `refine ⟨_, hS.dependent_image (fun x hx => g x hx), ?_, ?_⟩` —
  rather than writing a nested set-builder `{y | ∃ x (hx : x ∈ {x | P x}), …}`,
  which fails to parse. `x ∈ {x | P x}` is defeq to `P x`, so `g x hx`
  typechecks directly; recover witnesses downstream with `rintro y ⟨x, hx, rfl⟩`.

### Bridge to Mathlib's Native Abstractions

When the project uses a custom representation (e.g., list-based paths, adjacency matrices) but Mathlib has richer API for a different representation (e.g., `SimpleGraph`):

1. Build a conversion function to Mathlib's type
2. Prove key properties transfer across the conversion
3. Use Mathlib's existing API on the converted representation

This proved `dynkin_edge_count` by converting adjacency matrices to `SimpleGraph` and leveraging Mathlib's connected graph theory.

## Issue Feasibility Triage (Before Committing to Work)

Before spending a full session on an issue, spend 10-15 minutes on feasibility triage:

### Step 1: Check sorry count and location
```bash
grep -n "sorry" <target-file>.lean | head -20
```
Count the sorries. If the issue claims "1 sorry remains" but the file has 5, the issue is stale.

### Step 2: Identify the mathematical core
Read the blob (`blobs/<Chapter>/<Item>.md`) and identify what mathematical result is needed. Ask:
- Is this a computation (finite cases, arithmetic)? → Likely Tier 1
- Does it need a named theorem not in Mathlib (Krull-Schmidt, Schur-Weyl)? → Likely Tier 3
- Is it standard algebra/linear algebra with Mathlib API? → Likely Tier 1-2

### Step 3: Check for known dead-ends
Search the "Known Dead-Ends" section above. If the proof touches `Decidable.casesOn` in Ch6, `ExteriorAlgebra ↔ PiTensorProduct`, or `SchurModule`, it's blocked.

### Step 4: Verify infrastructure exists
For each dependency the proof needs:
```bash
grep -rn "theorem <dep_name>\|def <dep_name>" EtingofRepresentationTheory/
```
If a dependency is sorry'd, that's OK (sorry acts as axiom). But if a dependency doesn't exist at all, you need to build it — factor that into your time estimate.

### Step 5: Skip or decompose if needed
- If blocked → `coordination skip <N> "reason"` immediately
- If too large → decompose into sub-issues (see agent-worker-flow Step 4b)
- If feasible → proceed with confidence

**Common triage mistakes:**
- Spending 2 hours before realizing a theorem needs Krull-Schmidt
- Not checking if the issue's sorry count matches reality (other agents may have merged changes)
- Assuming a "1 sorry" issue is easy — the sorry may hide a 200-line proof

## Common Failure Modes

From Phase 2 review patterns and Stage 3.2 proof experience (110+ merged PRs through wave 20):

1. **Wrong Mathlib declaration name.** Always `#check` the declaration before using it.
2. **Fabricated references.** If `.refs.md` cites a Mathlib declaration, verify it exists.
3. **Scope mismatch.** The book may state a theorem for a specific case (e.g., finite-dimensional) but Mathlib has it more generally. Use the general version.
4. **Missing instances.** Representation theory needs many type class instances. If Lean can't find one, check if Mathlib has it under a different name or if you need to `open` a namespace.
5. **Hidden hypotheses in book statements.** The book may omit hypotheses that are implicit in context (e.g., algebraic closure, field characteristic). Discovered examples: Theorem 3.10.2 needed `[IsAlgClosed k]`, Example 8.1.7 needed `Field k` not `CommRing R`. When a proof attempt fails at a fundamental level, check whether the statement needs additional hypotheses.
6. **Status tracking lag.** After proving a theorem, update `items.json` immediately in the same commit. Audits have found items marked `scaffolded` that were actually `sorry_free`. Always update proactively — manual tracking in `progress/items.json` is the only status tracking mechanism.
7. **FDRep abstraction fighting.** If your proof requires distributing `.hom.hom` over sums or otherwise unwrapping 3+ layers of categorical abstraction, you're fighting the wrong abstraction. See the FDRep Categorical Plumbing patterns above for alternatives.
8. **Universe level mismatches.** Representation theory proofs sometimes need explicit universe annotations (`.{v}`) especially when working with Jacobson radical or maximal ideal APIs. If type unification fails mysteriously, try adding explicit universe parameters.
9. **Sinking entire context windows on known dead-ends.** Before starting a proof, check the "Known Dead-Ends" section above. If the proof requires bridging `ExteriorAlgebra` ↔ `PiTensorProduct` or resolving the `if`-branching diamond, sorry it immediately and move on. Multiple agents have confirmed these are blocked on missing infrastructure.
10. **Opaque placeholder accumulation.** Defining key structures as `sorry : FDRep k G` (e.g., `SchurModule k N lam`) creates downstream dependency chains that block entire proof clusters. When you must sorry a definition, prefer making the carrier type concrete and sorry-ing only specific operations/instances (see "Never sorry a Type" above). Each opaque placeholder blocks all items that depend on it.
11. **Convention mismatch between book and Mathlib.** Sign conventions, ordering conventions, and normalization conventions can silently make statements unprovable. See "Verify Statement Correctness Before Proving" section above. The vandermondePoly sign mismatch wasted multiple agent sessions before being discovered via a concrete n=2 counterexample.
12. **Issue description proof strategies are sometimes wrong.** The proof approach described in an issue body may be mathematically incorrect or only work for special cases. Always spend 10 minutes verifying the described approach before committing to it. See "Issue Description Feasibility Check" section above.
13. **A prior agent's "circular / needs missing theorem" skip can be wrong.** When an issue was already skipped as circular or blocked on a named result "not in the project," do not just re-skip — check whether an existing **off-block / orthogonality / character lemma's diagonal (special) case** already supplies the missing independent input. Concrete example (#2693): the rank-1 Young-symmetrizer fact was twice skipped as "needs primitivity `c_λ k[S_n] c_λ = k·c_λ`, not in project." But the diagonal case of the existing `youngSym_trace_kronecker'` is exactly `trace(c_λ|_S) = α` (an independent `ℂ[S_n]` computation), and `trace(α⁻¹·c_λ|_S) = 1` via `IsProj.trace` gives rank 1 directly — no primitivity, no whole-space trace, no dimension bridge. Pattern: if a proved `..._vanishes_off_block` lemma gives the off-diagonal value (`if h_ne then 0`), its `if_pos rfl` diagonal twin usually gives the special-block value you need. Spend 10 minutes looking for the diagonal twin before re-skipping.
14. **Namespace dot-notation mismatch.** Most Lean files in this project wrap code in `namespace Etingof` (and `noncomputable section`). If you define `def YoungDiagram.foo` inside `namespace Etingof`, the full name is `Etingof.YoungDiagram.foo` — dot notation `μ.foo` (where `μ : YoungDiagram`) will NOT find it. **Symptoms:** The definition silently fails to register (no error reported) and downstream references get "Invalid field" errors. **Fix:** Close the namespace before defining `YoungDiagram.*` declarations that need dot-notation access, then reopen it. Remember to also close/reopen any `noncomputable section`.


### Tactic Gotchas with `rw`, `omega`, and `nsmul`

0. **`(i : ℕ)` inside a `∑`/`∏` binder *binds* `i : ℕ`, it does not coerce.** Writing `∑ i, B ^ (i : ℕ) * f i` where `f : Fin n → ℕ` makes Lean infer the sum index type as `ℕ` (from the ascription `(i : ℕ)`), giving a confusing cascade: `failed to synthesize Fintype ℕ` *and* `Application type mismatch: argument i has type ℕ but is expected to have type Fin n in f i`. The `(i : ℕ)` is read as a *binder type ascription*, not a `Fin n → ℕ` coercion. **Fix:** pin the binder type — `∑ i : Fin n, B ^ (i : ℕ) * f i` — so `i : Fin n` and `(i : ℕ)` then coerces (`Fin.val`). (Same trap in `∏`.) Relatedly, `Finset.le_sup`/`Finset.exists_mem_eq_sup` over a non-`ℕ`-valued or inference-ambiguous `f` need the `(f := fun μ => …)` named argument or they stall on `OrderBot ?m` / leave the family a metavariable.

1. **`rw [← Finset.sum_filter]` fails on lambda matching.** `rw` does strict term matching and often can't unify `fun x => if x ∈ S then f x else 0` with `Finset.sum_filter`'s pattern. Use `simp only [← Finset.sum_filter]` instead — `simp` is more flexible with lambda matching.

2. **`omega` can't see through `Fin` equalities.** After `Fin.val_eq_of_eq`, omega may not recognize the resulting Nat equality. Fix: use `simp only [Fin.mk.injEq] at h` to normalize `⟨a, _⟩ = ⟨b, _⟩` into `a = b` before calling `omega`.

3. **`omega` can't handle `min`/`if` from `List.length_take`.** `List.length_take` gives `(l.take n).length = min n l.length`, and `min` unfolds to `if n ≤ l.length then n else l.length`. omega can't simplify `if`. Fix: extract the bound you need with `lt_of_lt_of_le h (min_le_left a b)` or `min_le_right`.

4. **`nsmul_eq_mul` produces `↑n * x` not `n * x`.** Converting `n • x` (where `n : ℕ`, `x : ℤ`) via `nsmul_eq_mul` gives `↑n * x` with a Nat cast. `linarith` can't equate `↑2 * x` with `(2 : ℤ) * x`. Add `push_cast` after `nsmul_eq_mul` to normalize.

5. **`linarith` requires a linear order — use `linear_combination` over ℂ.** `linarith` only works on linearly ordered types (ℝ, ℤ, ℕ, etc.). For goals over ℂ like `a + b = 0 → a = -b`, use `linear_combination h` instead. The `linear_combination` tactic works over any commutative ring.

## Breadth-vs-Depth Phase Awareness

The project alternates between **breadth phases** (statement formalization) and **depth phases** (proof completion). Recognizing which phase you're in prevents misallocating effort.

### Breadth Phase (Statement Formalization)
- **Trigger:** Proof backlog < 30 items, or agents are running out of proof targets
- **Focus:** Formalize new theorem/definition statements across multiple chapters
- **Expected metrics:** Low items/PR ratio, sorry count may increase (new sorry'd statements added)
- **This is not a failure mode** — it's strategic investment in the proof pipeline

### Depth Phase (Proof Completion)
- **Trigger:** Proof backlog > 40 items, or enough targets exist across 3+ chapters
- **Focus:** Prove sorry'd items, prioritizing chain completion and chapter closures
- **Expected metrics:** Higher items/PR ratio, sorry count declining
- **Planners should create 80%+ proof issues** during this phase

### Current Status (as of Wave 42, 2026-04-03)
The project has 25 sorries across 14 files (down from 66 at wave 28). Sorry-free rate: 266/280 files (95.0%). 577/583 items (98.9%) sorry-free. This is deep in a **depth phase** — all remaining work is proof completion on hard items. Statement formalization is complete.

**Chapter status (Wave 42):** Ch3, Ch4, Ch7, Ch8 are 100% sorry-free. Ch2 has 1 sorry (Theorem2_1_2). Ch5 has 13 sorries across 6 files. Ch6 has 7 sorries across 6 files. Ch9 has 4 sorries across 1 file (MoritaStructural).

**Major milestones since wave 40:**
- **Proposition5_14_1 sorry-free** (#2048) — Convention swap regression fully recovered (2→0)
- **PolytabloidBasis 6→3** (#2018, #2041) — T_col_inc proved, garnirSet helpers proved
- **Corollary6_8_3 restructured** (#2050) — parallel reflection chain approach
- **Theorem5_22_1 decomposed** (#2042, #2058) — 2→5 sorries from strategic scaffolding
- **FormalCharacterIso 2→1** (#2059) — shift formula proved
- **Mackey machine progress** (#2034) — Theorem5_27_1 from 4→2 sorries
- **OrientationDefs extracted** (#2057) — circular import broken for Corollary6_8_4

**Major blocker clusters (updated wave 42):**
1. **Weyl character formula** (7 sorries, 3 files): Theorem5_22_1 (5), FormalCharacterIso (1), Proposition5_22_2 (1). Active: #2054 targeting charValue chain (5→1)
2. **Gabriel's theorem chain** (7 sorries, 6 files): Corollary6_8_3 (2), Corollary6_8_4 (1), CoxeterInfrastructure (1, universe-blocked), Problem6_1_5_theorem (1), Problem6_9_1 (1), Theorem6_5_2 (1). Active: #2053
3. **Polytabloid basis** (4 sorries, 2 files): PolytabloidBasis (3), TabloidModule (1). Active: #2055
4. **Morita/Eilenberg-Watts** (4 sorries, 1 file): MoritaStructural — all 4 relate to k-linearity gap. No active work.
5. **Mackey machine** (2 sorries, 1 file): Theorem5_27_1 — two open PRs (#2047, #2049) pending CI fixes

**Velocity trend:** 66 → 43 → 36 → 27 → 29 → 28 → 25 sorries over waves 28-42. Rate decelerating as remaining items are increasingly hard. The bump at wave 39 (27→29) was from strategic decomposition; steady decline resumed.

**Key velocity insight:** Difficulty 3/3 items have a ~30% single-session success rate — agents should budget accordingly and commit partial progress early. **Agents that don't commit intermediate work produce zero value** — stale claims continue to be a recurring problem.

## Convention Swap Regressions

**Lesson from Wave 41-42:** Changing a foundational convention (e.g., YoungSymmetrizer from `a_λ * b_λ` to `b_λ * a_λ`, PR #2002) can cause cascading regressions in downstream files that depend on the old convention. The Proposition5_14_1 regression (#2048) took a dedicated PR to fix.

**Wave 44 update:** Meditate #2102 determined that the current `b_λ * a_λ` convention MUST be switched BACK to `a_λ * b_λ` (#2103). The `b_λ * a_λ` convention fundamentally blocks the straightening lemma (no left P_λ absorption). The previous convention change was premature — it was done to make `polytabloid_self_coeff` work but broke the more important straightening proof. Budget ~150 lines for the switch and downstream fixes.

**Prevention pattern:**
1. Before swapping any convention, `grep` for ALL downstream uses across the codebase
2. Fix ALL downstream files in the SAME PR as the convention change
3. If the blast radius is too large for one PR, create issues for each affected file before merging
4. Never merge a convention swap that breaks existing sorry-free theorems — this is a net regression even if the new convention is "more correct"

**Detection:** After merging a convention change, immediately build ALL files that import the changed module: `lake build <ImportingModule1> <ImportingModule2> ...`

## `simp` Doesn't See Through Local `let` Bindings

When `simp` fails to make progress on a goal involving a term bound by a local `let`:

**The problem:** `simp` and `simp_rw` do not beta-reduce through local `let` bindings. If you have:
```lean
let f := DirectSum.component R i
-- Goal: ... f (Finset.sum ...) ...
simp [DirectSum.component.of]  -- makes no progress!
```

**Workaround 1: Use `rw` before `simp`**
```lean
rw [DFinsupp.finset_sum_apply]  -- expand the sum application first
simp_rw [show f x = ... from rfl]  -- then rewrite with explicit `show`
```

**Workaround 2: Use `change` to eliminate the `let`**
```lean
change <explicit_form_without_let>
simp [...]  -- now simp can see the structure
```

**Workaround 3: Use `dsimp only` to reduce `let` bindings**
```lean
dsimp only []  -- reduces let-bindings in the goal
simp [...]  -- now works
```

**Evidence:** Discovered independently in Proposition6_6_7 (#1800) and Problem6_9_1 (#1807). The `DFinsupp.finset_sum_apply` + `show` pattern was the successful resolution in both cases.

## Decidable Instance Mismatch Patterns (Comprehensive)

Decidable instance mismatches are a recurring friction point across the project. They arise when `classical` decidability and concrete `DecidableEq`/`DecidablePred` instances coexist, creating terms that look identical but are not definitionally equal.

### Symptom Recognition

- `rfl` fails on two expressions that are "obviously equal"
- `rw` fails with "motive is not type correct" on a Decidable-dependent term
- Two `Finset.univ` expressions have different `Fintype` instances
- `if`/`dite` expressions don't reduce under `simp` because the `Decidable` instance is opaque

### Strategy 1: `open scoped Classical` (Prevention)

Add at the section level, **before** any definitions that use `haveI : DecidablePred ... := Classical.decPred _`:
```lean
open scoped Classical
```
This ensures all `DecidablePred` instances come from the same source. **Best approach** — prevents the problem rather than patching it.

### Strategy 2: `convert rfl using N` (Patching)

When two sums over `Finset.univ` differ only in their `Fintype` instance:
```lean
convert rfl using 2  -- handles via Subsingleton (Fintype α)
```

### Strategy 3: `trans` + separate goals

When `rw` fails due to a dependent Decidable in the motive, split into two steps:
```lean
-- Instead of: rw [h]  -- fails with "motive is not type correct"
calc lhs = middle := by <prove_without_h>
       _ = rhs := by <prove_using_h>
```

### Strategy 4: `Subsingleton.elim` for proof irrelevance

When two `Decidable` instances block definitional equality:
```lean
have : inst₁ = inst₂ := Subsingleton.elim _ _
subst this  -- now only one instance exists
```

### Strategy 5: Avoid `set` for local definitions

The `set x := expr` tactic introduces a local definition that can capture the "wrong" Decidable instance. Prefer `have` or `let` with explicit type annotations instead.

**Evidence:** Decidable mismatches appeared in Theorem5_27_1 (sessions #5, #15), Proposition6_6_7 (#1800), and Proposition6_6_6_source (#1821). Strategy 1 (`open scoped Classical`) is the most reliable prevention.

## Universe Pinning Strategy

When universe level errors or mismatches arise (common in representation theory where multiple universe levels interact):

**Pattern:** Change from `Type*` to explicit `universe u v` declarations:
```lean
universe u v

theorem my_theorem
    (k : Type u) [Field k]
    (V : Type v) [AddCommGroup V] [Module k V] :
    ... := by
  ...
```

**When to use:**
- `universe polymorphism` errors
- Sigma types with universe-level mismatches
- `MoritaEquivalent`, `FDRep`, or other constructions that require universe alignment
- `SchurModule`, `AlgIrrepGL`, or similar constructions that mix multiple universe-polymorphic types

**Evidence:** Universe pinning resolved issues in Theorem5_18_4 (SchurModule universe annotations), IsFiniteTypeQuiver (pinned to `Type` to avoid universe mismatch), and BasicAlgebraExistence (explicit `Type u` throughout).

## Section Variable Auto-Inclusion Gotcha

Lean 4 section variables declared with `variable (h : P)` are only auto-included
in declarations where they appear **syntactically** in the type or proof body.
Dot notation like `h.eq` may not trigger auto-inclusion — Lean's variable scanner
doesn't always resolve dot notation to find the underlying variable.

**Symptom**: "Unknown identifier `h.eq`" or "Unknown identifier `h`" inside a
proof in a `section` block, even though `h` is declared as a `variable`.

**Fix**: Add `include h` after the `variable` declaration to force inclusion in
all subsequent declarations in the section:
```lean
section Foo
variable {e : A} (he : IsIdempotentElem e)
include he  -- forces he into all declarations in this section

lemma bar ... := by
  ... he.eq ...  -- works now
end Foo
```

**Alternative**: Explicitly add the parameter to each declaration (the pattern
used in this project's `cornerSubmodule_left_mul` etc.).

### Calling a section-variabled lemma: don't guess positional args

When you *apply* a lemma defined under a `variable (k : Type*) [Field k]
(N n : ℕ)` block, the used section variables are prepended as **explicit**
arguments in declaration order — so `foo` may really take `foo k N n M halg …`
even though its written signature starts at `M`. The order is often
non-obvious (a section `n` redeclared locally by an earlier lemma can drop out;
an implicit-looking variable can be explicit and vice versa). Guessing
positionally wastes build cycles on `Application type mismatch: argument … has
type ℕ but is expected to have type FDRep …`.

**Fix**: before the first call, run `#check @Namespace.foo` (in a throwaway file
or scratch `#check`) to read the real binder list, then either match it
positionally or pass the data argument by name (`foo (M := M) …`) and let the
preceding section variables infer. Thirty seconds of `#check` beats four failed
`lake build`s.

## When to Decompose vs. Attempt Directly

**Decompose immediately** when:
- The sorry has resisted 2+ attempts by prior agents (check issue comments)
- The proof has 3+ conceptually independent sub-goals
- You estimate the proof at 100+ lines of tactics
- The file is 500+ lines and you need to understand most of it
- You're past the midpoint of your context window

**Attempt directly** when:
- The sorry is in a Tier 1 (achievable) category
- A clear tactic sequence is visible after reading the book's proof
- The file is short (<200 lines) and self-contained
- No prior agent has attempted this sorry

**The decomposition output pattern:**
```lean
-- BEFORE: monolithic sorry
theorem hard_theorem : conclusion := by sorry

-- AFTER: structured proof with isolated helper sorries
private lemma step1 : ... := sorry  -- clear, independently claimable
private lemma step2 : ... := sorry  -- clear, independently claimable

theorem hard_theorem : conclusion := by
  have h1 := step1
  have h2 := step2
  exact final_combination h1 h2
```

**Value assessment:** A session that decomposes a monolithic sorry into 5 sub-goals and proves 3 of them is MORE valuable than a session that attempts the monolithic sorry directly and fails. Decomposition creates independently claimable work items and documents the proof strategy.

**Evidence:** Problem6_9_1 was decomposed from 1 sorry into 8 sub-goals, 6 proved (#1807). Theorem5_22_1 was decomposed into coefficient extraction + core identity (#1806). BasicAlgebraExistence was split into 2 targeted helpers (#1803). All three patterns created visible, committable progress.

## Rewriting Inside Coercion Wrappers (`.ker`, `↥`, `Module.finrank`)

When `rw [h]` fails to find a pattern that is visibly present in the goal — especially inside
`LinearMap.ker`, `↥(Submodule)`, or `Module.finrank k ↥(...)` — the issue is coercion mismatch.

**Don't iterate**: If `rw`, `simp only`, `conv`, and `show` all fail on the same pattern, stop
trying variations. Instead:

1. **For `.ker` rewrites**: Use `calc` with `congr_arg LinearMap.ker h` to rewrite the argument:
   ```lean
   calc LinearMap.ker LHS
       = LinearMap.ker RHS1 := congr_arg LinearMap.ker h_eq
     _ = LinearMap.ker RHS2 := LinearMap.ker_smul _ _ h_ne_zero
   ```

2. **For `Module.finrank` on equal submodules**: Add a helper:
   ```lean
   private lemma finrank_submodule_congr {S₁ S₂ : Submodule R M} (h : S₁ = S₂) :
       Module.finrank R S₁ = Module.finrank R S₂ := by subst h; rfl
   ```
   Direct `h ▸ rfl` may timeout due to expensive coercion unification.

3. **For `iInf` equality**: Use `iInf_congr` (not `iInf_mono` + `le_antisymm`) when you need
   equality, not just inequality.

## Quiver Hom Universe in Lean 4/Mathlib

`Quiver.{v, u}` has `Hom : V → V → Type v`, NOT `Sort v`. You CANNOT have
Prop-valued arrows directly. For Prop-valued quiver arrows (as used in
`IsFiniteTypeQuiver` with `@Quiver.{0, 0}`), wrap with `PLift`:

```lean
def myQuiver : Quiver (Fin k) where
  Hom i j := PLift (j.val = (i.val + 1) % k)  -- Type 0, not Prop
```

The CategoryTheory instances on `Fin k` (`CategoryStruct.toQuiver`,
`ReflQuiver.toQuiver`) conflict with custom quivers. Suppress per-declaration:

```lean
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
def/theorem ... := by letI := myQuiver k hk; ...
```

Dot notation on `QuiverRepresentation` fields (e.g., `.obj`) triggers Quiver
instance synthesis. Use explicit `@QuiverRepresentation.obj ... inst ...` when
instances are suppressed.

## `Finsupp.lmapDomain` Coercion Gotcha

`Finsupp.lmapDomain` is a `LinearMap` wrapper around `Finsupp.mapDomain`. They are
**definitionally equal**, but `simp [Finsupp.lmapDomain_apply]` often fails because
the coercion `⇑(lmapDomain ...)` doesn't match the simp lemma's LHS pattern.

**Workaround:** Don't try to simp through the coercion. Instead, unfold the
definition manually with `simp only [myDef]` (where `myDef` uses `lmapDomain`),
then use `Finsupp.mapDomain_single`, `Finsupp.mapDomain_zero`, etc. directly.
Since `lmapDomain` is definitionally `mapDomain`, the `mapDomain` lemmas apply
without any conversion step.

## `Nat.card` vs `Fintype.card` in Theorem Statements

Prefer `Nat.card` over `Fintype.card` in theorem **statements** (not just proofs).
`Fintype.card` requires a `Fintype` instance, which for subgroups needs
`DecidablePred (· ∈ S)` — unavailable outside `classical` blocks. This means
theorems using `Fintype.card` can't be applied without `classical`.

`Nat.card` works without decidability instances. Inside proofs, convert via:
```lean
classical
rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
```

## Lean 4 List API Naming Conventions

Many Lean 3 / old Mathlib List lemma names have changed. Common pitfalls:

| What you want | Wrong name | Correct name |
|---|---|---|
| Map preserves indexing | `List.get_map` | `List.getElem_map` |
| Nodup + injection | `List.Nodup.get_inj` | `List.Nodup.get_inj_iff` |
| getLast? to getLast | `List.getLast?_eq_getLast` | `List.getLast?_eq_some_getLast` |
| getLast as getElem | `List.getLast_eq_get` | `List.getLast_eq_getElem` |

**Pattern for `head?` extraction:** Don't chain `head?_eq_getElem?` + `getElem?_eq_getElem`.
Instead, pattern-match directly:
```lean
cases path with
| nil => absurd hlast (by simp)
| cons a t => simpa using hhead
```

**`Matrix.IsSymm.apply` direction:** `hsymm.apply a b` gives `adj b a = adj a b`
(swapped from what you might expect). So `hsymm.apply (φ i) (φ j)` gives
`adj (φ j) (φ i) = adj (φ i) (φ j)` — useful when rewriting a hypothesis
that has `adj (φ j) (φ i)`.

## Fin Arithmetic in Proofs

When proving `Fin.ext` goals where the nat-level equality needs `omega`
(e.g., `chain.length - 2 + 1 = chain.length - 1`), **extract the nat proof first**:
```lean
have h_nat : chain.length - 2 + 1 = chain.length - 1 := by omega
congr 1; exact Fin.ext h_nat
```
Don't try `Fin.ext (by omega)` in term mode — omega often can't see the goal
through the Fin wrapper.

**Finset.erase parsing:** `S.erase a |>.erase b` in a type annotation
parses as `(S.erase a).erase b` in term position but `(x ∈ S.erase a).erase b`
in proposition position. Always use explicit parentheses: `(S.erase a).erase b`.

## obj↔concrete type bridge in `leaf_equalities` (quiver-rep collapse proofs)

When writing an orientation-generic `leaf_equalities`/collapse lemma over a
quiver representation, the invariant subspaces are typed
`W : ∀ v, Submodule F ((someRep_kQ …).obj v)`. The per-vertex object
`(someRep_kQ …).obj ⟨v, _⟩` is **definitionally** `Fin (k·(m+1)) → F`, but the
unifier will **not** reduce it to the concrete form — not even under an explicit
ascription `(W ⟨v,_⟩ : Submodule F (Fin (k·(m+1)) → F))`, which errors with a
"type mismatch … `(someRep_kQ …).obj ⟨v, ?m⟩` vs `Fin (k·(m+1)) → F`". This bites
hardest when the per-vertex dimension `…Dim` is defined by `match v.val with …`
(does not reduce through the `Fin 8` proof metavar); an `if … then … else …`
dimension reduces and avoids the wall (this is why some `_kQ_leaf_equalities`
families compile in obj-form and others do not).

**Consequence:** you cannot directly pass obj-typed `W ⟨v⟩` into a foundation
lemma stated over concrete `Fin (k·(m+1)) → F` spaces. Two fixes:
1. **Stay obj-form (preferred, mirrors the working D̃₇ family).** Build the
   leaf→center map `e` as a composite of the rep's **own** `mapLinear` along the
   relevant arrows (e.g.
   `(rep).mapLinear a20 ∘ (rep).mapLinear a32 ∘ (rep).mapLinear a43`), which is
   obj-typed by construction, and apply a space-generic criterion like
   `leaf_center_mem_iff_of_forward` (`FieldGenericETilde6.lean`). Then
   `simp only [someRep_kQ, someRepMap_kQ]` rewrites that composite to the concrete
   map (`blockEmbedAt_F …`, etc.) only where you actually need the concrete form.
2. Add obj-form wrappers of the concrete foundation lemmas.

A membership *statement* `concreteMap x ∈ W ⟨0,_⟩` (deposit into an obj-typed
submodule) elaborates if you ascribe the element to the obj type:
`(concreteMap x : (rep).obj ⟨0, by omega⟩) ∈ W ⟨0, by omega⟩` — the ascription
forces a default-transparency defeq that *does* reduce. The proof body still
needs fix (1) or (2).

### Working recipe for fix (1) on a `match`-`Dim` family (landed for Ẽ₇)

`etilde7Rep_kQ_{prefix,suffix}Arm_collapse` (`FieldGenericETilde7.lean`,
Section 3b, #4642) are the first obj-form collapse criteria actually carried to a
compile over a `match`-based `Dim`. Two non-obvious gotchas beyond "build the
obj composite + call `leaf_center_mem_iff_of_forward`":

1. **Instance wall + diamond.** `leaf_center_mem_iff_of_forward` (and any lemma
   with `[AddCommGroup Vᵢ] [Module F Vᵢ]`) needs those instances on the stuck
   obj-type `(rep).obj ⟨v,_⟩`; synthesis fails (reducible transparency won't
   reduce the `match`). Supply them with `letI` + `inferInstanceAs`, but use the
   **stuck index form**, not the reduced one:
   ```
   letI : AddCommGroup ((rep).obj ⟨v, by omega⟩) :=
     inferInstanceAs (AddCommGroup (Fin (someDim m ⟨v, by omega⟩) → F))
   letI : Module F ((rep).obj ⟨v, by omega⟩) :=
     inferInstanceAs (Module F (Fin (someDim m ⟨v, by omega⟩) → F))
   ```
   Using the **reduced** form `Fin (k*(m+1)) → F` typechecks but produces a
   `.toAddCommMonoid` that does **not** match the rep's bundled
   `instAddCommMonoid ⟨v,_⟩` (which is `Pi.addCommMonoid` at the *stuck* index),
   so the subsequent `W ⟨v⟩` argument fails with an "Application type mismatch …
   `this✝.toAddCommMonoid` vs `(rep).instAddCommMonoid ⟨v,_⟩`" instance diamond.
   The stuck-index form keeps `Pi.addCommMonoid` at the same index and the
   diamond closes.
2. **Conclusion membership index must be inferred, not re-proved.** Writing the
   conclusion as `… ∈ W₁ ⟨0, by omega⟩` while the element already pins vertex `0`
   (via the composite's target / the bound `x`'s type) makes the second
   `by omega` run against an already-unified metavar and report a spurious
   `No goals to be solved`. Write `… ∈ W₁ _` and let the index infer from the
   element type.

With both, containments come from pure invariance chaining
(`hW₁_inv a20 _ (hW₁_inv a32 _ (hW₁_inv a43 p hp))`) and injectivity descends via
`simp only [LinearMap.comp_apply, rep, repMap] at h` then the concrete
`*ArmComp_F_injective` (term-mode defeq unfolds the `match` at the leaves).

## Bundled-hom defeq blowup: `ρ g f = underlyingHom f` is cheap *only* in the defining file

`polyRightRep g f = rTransAlgHom (↑g) f` (a `Representation` applied, vs the
underlying `AlgHom`) holds by `rfl`. But proving it as a fresh `have ... := rfl`
— or relying on the defeq through `exact`/`show` — in a **downstream** file
**diverges at `whnf`** (times out even at 1.6M heartbeats): reconciling the two
FunLike coercion paths (`Representation`/`LinearMap` vs `AlgHom`) forces Lean to
whnf into `aeval`/the underlying function. The identical `rfl` is cheap *inside*
the file where the rep is defined (its `_apply_X` lemmas already use it).

Fix: put the equation as a named lemma in the **defining** file
(`theorem foo_apply (g) (f) : ρ g f = underlyingHom (↑g) f := rfl`), then
downstream use `rw [foo_apply]` — the proof is already compiled, so no `rfl`
re-elaboration. After the `rw`, close with the underlying lemma but let Lean
**infer the matrix/group argument with `_`** (`exact bar _ hf`, not `bar (↑g) hf`):
pinning `↑g` yourself reintroduces a second coercion spelling and re-triggers the
same whnf blowup. Symptom to recognize: `(deterministic) timeout at whnf` on a
line that is "obviously" `rfl` or a trivial `exact`.

**Same trap when proving `Commute`/equality *of* such endos** (e.g. left and
right `GL_N`-actions on `k[Xᵢⱼ]` commute). `exact AlgHom.congr_fun h_comp f` —
where `h_comp` equates the underlying `AlgHom.comp`s — blows up `whnf` (even at
6.4M heartbeats): Lean reconciles the `Module.End` product form against the
applied form through `aeval`. Make every step syntactic instead:
1. `apply LinearMap.ext; intro f` — **not** bare `ext f`, which over-applies into
   `MvPolynomial` *coefficient* extensionality (`f` becomes a `Finsupp` exponent).
2. `rw [Module.End.mul_apply, Module.End.mul_apply, ρ_apply, σ_apply, …]` (all
   `rfl`-lemmas) to reach the applied form on both sides.
3. Normalise the underlying lemma the same way and close by matching, not defeq:
   `have h2 := AlgHom.congr_fun h_comp f; rw [AlgHom.comp_apply, AlgHom.comp_apply] at h2; exact h2`.
With the fully-syntactic route the proof needs **no** `maxHeartbeats` bump at all.

## Extracting a simple sub-representation from an infinite-dim graded rep (#4922)

`Chapter5/SimpleSubrepExtraction.lean` builds `exists_simple_subrep_of_quotDetRep`
— from a nonzero `GL_N`-invariant submodule of `A/det` (infinite-dim) produce a
simple `FDRep` constituent with an injective equivariant embedding. Reusable recipe
when you need a *simple sub-representation* and `Theorem5_23_2_i` only gives the
vacuous `IsSemisimpleModule k` (k-vector-space) semisimplicity:

- **Finite-dim reduction in a graded rep:** lift a nonzero `w` to a polynomial of
  total degree `D`; `MvPolynomial.restrictTotalDegree σ k D` is a ready
  `Module.Finite k` submodule (instance), and the degree-preserving action keeps it
  invariant (decompose into `homogeneousComponent`s + `IsHomogeneous.totalDegree_le`).
  Push it through `mkQ` (`Module.Finite.map` is an instance) and intersect with the
  invariant `W` for a *nonzero, finite-dim, invariant* `M₀ ≤ W`.
- **Atom = simple sub-rep (the reusable lemma `Etingof.exists_isSimpleModule_le`):**
  a nonzero `k[G]`-submodule of `ρ.asModule` finite over `k` is Artinian over `k[G]`
  via `isArtinian_of_tower k inferInstance` (needs `IsScalarTower k k[G] ↥W`,
  auto), so `isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf` gives an atom;
  `isSimpleModule_iff_isAtom.mpr` + push forward along `W.subtype`
  (`Submodule.equivMapOfInjective ... |>.symm` + `IsSimpleModule.congr`) gives the
  simple submodule. (`IsArtinian` is an `abbrev` for `WellFoundedLT (Submodule …)`,
  so `IsWellFounded.wf` supplies the `WellFounded` term directly.)
- **`asModule` ↔ `asSubmodule` simplicity bridge:** packaging the atom as an
  `FDRep.of σ.toRepresentation` forces proving `IsSimpleModule k[G]
  (σ.toRepresentation).asModule`, which is NOT defeq to `IsSimpleModule k[G]
  ↥σ.asSubmodule` (the `Module k[G]` instances differ — `:= h` fails). Build the
  k[G]-linear equiv `(σ.toRepresentation).asModule ≃ₗ[k[G]] ↥σ.asSubmodule` by hand:
  carriers coincide on `σ.toSubmodule` (use `σ.toRepresentation.asModuleEquiv`, which
  is `LinearEquiv.refl`, to access `.1`/`.2`); `map_smul'` reduces via
  `MonoidAlgebra.induction_linear`, and the `single g t` case closes by **`rfl`**
  after `rw [Representation.single_smul, Representation.single_smul]` (both sides are
  `t • ρ g y`). Then `IsSimpleModule.congr`. Mathlib's
  `Subrepresentation.{asSubmodule, ofSubmodule', subrepresentationSubmoduleOrderIso}`
  give the order iso between subrepresentations and `Submodule k[G] ρ.asModule`.
- **Gotcha:** `MvPolynomial.mem_restrictTotalDegree` takes the index type `σ` and
  the degree `m` as *explicit* positional args before `p` (`mem_restrictTotalDegree
  (Fin N × Fin N) D p`), even though `R` is implicit — term-mode calls need all
  three. `rw` forms infer them fine.
- **`open MvPolynomial` inside `namespace Etingof.*` opens the WRONG namespace.**
  `EvalEqOnGL.lean` declares an `Etingof.MvPolynomial` namespace, so a bare
  `open MvPolynomial` inside any `namespace Etingof.Foo` resolves to *that* (the
  relative match wins), and `monomial`/`coeff`/`C` come up as "unknown identifier"
  (autoImplicit then mis-reports them as "function expected at monomial"). Use
  `open _root_.MvPolynomial`. Same trap for any root namespace shadowed by an
  `Etingof.<Name>` subnamespace.
- **Reading the underlying object from an `FDRep.of σ.toRepresentation` carrier:**
  `(FDRep.of ρ').ρ g w`'s coercion to the ambient type is not auto-inserted, but the
  carrier is defeq to `↥σ.toSubmodule`, so `σ.toSubmodule.subtype` typechecks directly
  as a `LinearMap` *from the FDRep carrier* (`def polyOf := (homog…).subtype`). Use it
  to read elements / the `.ρ` action on the ambient module (`polyOf (M.ρ g w) =
  ambientRep g (polyOf w)` holds by `rfl`), sidestepping all `.V`/`FGModuleCat` coe pain.
- **`rw` won't close `finrank ↥A = finrank ↥A` when `A` came from rewriting across two
  *defeq-but-distinct* FDRep carriers** (e.g. after `rw [glWeightSpace_twistFDRep_pos]`
  turning `glWeightSpace twistFDRep μ` into `glWeightSpace polyRightDegreeFDRep …`): the
  two `↥(...)` carry mismatched `Module` instances, so the post-`rw` `rfl` silently fails
  and you get "unsolved goals ⊢ ↑A = ↑A". Close it with a `congrArg` term instead:
  `Nat.cast_inj.mpr (congrArg (fun w => Module.finrank k (glWeightSpace k N M w)) hweight)`
  (or prove the `ℕ` equality first to dodge the extra `Nat.cast` layer). Same fix for any
  `finrank`/`glWeightSpace` equality that "should be `rfl`" but isn't.
- **Stars-and-bars count:** `#{f : Fin N → ℕ | ∑ f = m}` is `Finset.piAntidiag univ m`;
  its card is `Nat.multichoose N m` via `Finset.map_sym_eq_piAntidiag` +
  `Finset.sym_univ` + `Sym.card_sym_fin_eq_multichoose`. Then
  `Nat.multichoose_eq`/`Nat.choose_symm` give `= C(m+N-1, N-1)` (needs `N ≥ 1`, which
  `Fin.pos j` supplies inside a `∏ j : Fin N`). For a product of independent column
  counts, biject to `Fintype.piFinset (fun j => piAntidiag …)` and use
  `Fintype.card_piFinset`.

**Workflow note:** `lake build <YourNewLeafModule>` is authoritative for a leaf file
that nothing else imports; building the *chapter aggregator* rebuilds all ~120
project files from source (`lake exe cache get` only fetches Mathlib oleans, not the
project's), which is slow and adds no signal for a leaf addition. After a clean
standalone build, just grep for declaration-name collisions and trust CI for the
full graph rather than waiting on the aggregator locally.
