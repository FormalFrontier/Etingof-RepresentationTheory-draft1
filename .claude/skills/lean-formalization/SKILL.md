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

   **Before recording a "missing from Mathlib" / "needs a helper Mathlib lacks" claim** in a docstring or issue, grep the relevant Mathlib file — pessimistic absent-API notes propagate and block successors who trust them. (#5320: a prior `clength_additive` docstring said the second-isomorphism diagram chase "needs a pseudoelement-membership helper Mathlib does not yet have"; in fact `Abelian.Pseudoelement.sub_of_eq_image`/`pseudo_pullback` and the categorical snake lemma `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` are all present and make the route reachable.) When the section *introduction* blob states a standing assumption (e.g. §9.6 "every object has finite length"), check whether the formalized class actually carries it — dropped standing assumptions are a fidelity gap that makes per-section theorems unprovable as stated (#5320: `IsFiniteAbelianCategory` omits finite length; the §9.6 carrier is `IsFiniteAbelianCategoryOverField.finiteLength`).

2. **Search for existing definitions and infrastructure.** Before defining any concept or building any equivalence/isomorphism, search the codebase:
   ```bash
   grep -r "def.*YourConceptName\|abbrev.*YourConceptName" EtingofRepresentationTheory/
   ```
   Duplicate definitions across chapters create incompatibility bugs that require manual refactoring later (e.g., duplicate `inducedCharacter'` in Ch5, duplicate `IsIndecomposable` in Ch2/Ch6). **Also search for infrastructure you might need** — PRs #1682, #1685, #1690 independently built the same GL₂(𝔽_q) BorelSubgroup equivalence because agents didn't check what already existed. Before building group/subgroup equivalences, coset decompositions, or character computation helpers, search for them first.

   **When verifying Mathlib lemma names/signatures, grep *this project's own* `.lake/packages/mathlib`, never another Mathlib checkout elsewhere on the machine.** This repo pins a recent Mathlib; other local clones (e.g. `lean-training-data`) can be months behind, with renamed or absent API. Confirming against the wrong checkout sends you down dead ends — e.g. hand-rolling a matrix-charpoly-eigenvector argument because the project's cleaner `Module.End.trace_eq_sum_roots_charpoly_of_splits` / `hasEigenvalue_iff_isRoot_charpoly` (and the single-argument `Polynomial.Splits`) weren't visible in the stale checkout (#5129). **The same drift hits `import` module *paths*, not just lemma names** — modules get split and relocated between versions. Before writing a new `import Mathlib.…`, confirm the file exists: `find .lake/packages/mathlib/Mathlib -name 'GeomSum.lean'` (or grep for the lemma and read its file's module path). Guessing from memory wastes a build cycle on `bad import` — e.g. (#5287) `Mathlib.Algebra.GeomSum → Mathlib.Algebra.Ring.GeomSum`, `Mathlib.Algebra.Polynomial.Eval → Mathlib.Algebra.Polynomial.Eval.Defs`.

3. **Verify the statement.** Cross-reference the Lean statement against the book's text. Missing hypotheses (algebraic closure, field characteristic, orientation constraints) are a recurring source of wasted proof attempts. If the proof fails at a fundamental level after 1 attempt, suspect a statement bug before trying alternative tactics.

4. **Estimate your context budget.** Difficulty 3/3 proofs consume 60-80% of a context window on average. If you're already past the midpoint of your session, consider claiming an easier item instead. Partial progress on a hard proof with no commit is worth zero — a completed easy proof is worth one sorry removed.

5. **Check dependency readiness.** Verify that imports compile and key helper lemmas are sorry-free (or that sorry'd helpers won't block your proof). Use `lake build <module>` for the specific file. **A "closed/merged" dependency can still fail to compile.** A `.lean` file absent from its `ChapterN.lean` aggregator is never built by CI, so it rots silently when an upstream lemma it cites changes signature. Before consuming a cited dependency, `grep "ChapterN.Module" EtingofRepresentationTheory/ChapterN.lean` to confirm it is in the build graph, then `lake build` that exact module — do not trust that #closed ⟹ compiles. **And when you create a new file, add it to the `ChapterN.lean` aggregator in the same PR** (otherwise it will not be CI-checked and the next signature change will break it undetected). Concretely (#4695): `KernelLemmaK.lean` (the #4694 kernel-lemma assembly) was never in the aggregator and had stopped compiling against the corrected `kernelLemmaK'`; the fix had to be made before the assembly could even be attempted. Note also: when wiring a low-level file (e.g. a localization stack) back into a higher-level one, watch for `import` cycles — if file `A` imports `B` only for one small lemma, relocate that lemma to a leaf (Mathlib-only) file imported by both, rather than creating the cycle. **A specific recurring trap for "discharge the sorry at `File.lean:L`" issues: the machinery you need may sit *downstream* of the statement file and transitively import it.** This pipeline creates statement files early and proves the machinery in later files, so the engine often imports the very file holding the sorry. Before assuming you can `import` the machinery into the statement file, compute the closure (small Python DFS over `import EtingofRepresentationTheory.…` lines) and check whether the statement file is in it. When it is, the importing edges are frequently **doc-comment-only** (`grep -nE "<defined-ident>" Importer.lean` shows hits only in `/-! … -/`): delete those stale imports to break the cycle (verify the importers still build). Diagnosed in #5478/#5488: `PolynomialGLDecomposition` reached `Theorem5_23_2` only via `CauchyDetQuotient` and `SchurModuleSpecialBlock`, both comment-only.

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

8. **A character table is NOT formalized by asserting orthonormality of hand-typed rows — that is vacuous.** Encoding the table as an explicit `chi : Fin r → Fin r → ℂ` (or `Q5`) and proving the rows are orthonormal + "the group has `r` conjugacy classes" does **not** pin down the table: a continuum of orthonormal `r`-frames satisfy it, and nothing connects the rows to actual representations — the claim "these are the irreducible characters" then lives only in the docstring. This sank Example 4.8.1's first fix (#5418 reopened → decomposed into #5428–#5431). The non-vacuous bar: build each row as the **trace of an honest representation** — construct `V : FDRep ℂ G` (from a real `Representation`/`MonoidHom`), prove `V.character g` equals the tabulated value at each class representative, prove `V` is `Simple` via `FDRep.simple_iff_char_is_norm_one` (`FinGroupCharZero.lean`: `Simple V ↔ ∑ g, χ(g)·χ(g⁻¹) = Nat.card G`, over an alg-closed char-0 field — so work over ℂ, which also carries `√5` etc.), prove the rows are pairwise non-isomorphic (distinct characters / `FDRep.char_orthonormal`), and conclude completeness from "`r` distinct simples + `r` conjugacy classes". The same critique applies to any "tensor multiplicity" or "decomposition" table built on the orthonormality-only certificate (e.g. Example 4.9.1 uses the identical `Q5` + `*_orthonormal` pattern and is a likely repeat flag). Also: the `native_decide` used to discharge those orthonormality sums and the `Fintype.card (ConjClasses G) = r` counts is a **forbidden trust hole** — evaluate character inner-product sums over `G` via a class-function decomposition `∑ g = ∑ class c, |c|·f(rep c)`, not `native_decide`.

**Genuine tensor-multiplicity tables: prove the character identity, don't chase a tensor-product iso (Example 4.9.1 `S₃` — DONE, #5377, `Chapter4/Example4_9_1.lean`).** The non-vacuous form of a Clebsch-Gordan table `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` is the **character identity** `χ_i(g)·χ_j(g) = Σ_k n_{ij}^k χ_k(g)` proved from real reps — you need neither the module iso nor `CharEqIso` (which lives in Ch5, unimportable from Ch4). Recipe: build the irreducibles as `FDRep ℂ G` and get each character as a *closed-form trace* (for `S₃ = Equiv.Perm (Fin 3)`: trivial `= 1`, sign `= (Equiv.Perm.sign g : ℂ)` via `charRep`, standard `= #fix(g) − 1` via the sum-zero subrep of the permutation rep — rebuild the sorry-free Ch5 `Discussion5_11_examples` `permRep`/`stdSub`/`stdRep_character` locally since Ch5 imports Ch4). The whole table then collapses to a polynomial identity in those closed forms, and the *only* group-specific input is one decidable fact `∀ g, (sign g, #fix g) ∈ {finite class values}` proved by `revert g; decide` (do NOT state it for a fixed `g` — that is not decidable). Proof shape: `simp only [irrep_char, Fin.sum_univ_three]; fin_cases i <;> fin_cases j <;> simp only [<matrix-cons lemmas>, Fin.isValue] <;> rcases <class-cases> g <;> rw [<sign-coe>, hs, hf]; push_cast; ring`. Bridge to genuine tensor products with `FDRep.char_tensor (V W) : (V ⊗ W).character = V.character * W.character` + `Pi.mul_apply` (needs `open CategoryTheory MonoidalCategory`). Axiom-clean, no `native_decide`. `S₄`/`A₅` follow the same pattern (#5442/#5443); `A₅` additionally needs the two 3-dim icosahedral reps with golden-ratio values over `ℚ(√5)`.

This saved 2+ sessions in Waves 47-49 by catching false statements early, an entire D̃₄ proof attempt (#4566), a Ch5 Wall 3 R2.b.i attempt against a false pointwise-vanishing residual lemma (#2769 → #4584), and a research-level Cauchy proof attempt against a false multiplicity-one character identity (#4944).

**Worked recipe for genuine small-group character tables (Example 4.8.1 family — #5428 done for Q₈, #5429 S₄, #5430 A₅ triv/ℂ⁴/ℂ⁵).** The `Q₈` table is sorry-free, `native_decide`-free, and axiom-clean (`propext/Classical.choice/Quot.sound` only) in `Chapter4/Example4_8_1.lean` (namespace `Etingof.Example4_8_1.Q8`). The 1-dim, sign, permutation-derived (`stdRepM` deleted-perm), and tensor-twist rows of `Q₈`/`S₄`/`A₅` all follow the identical explicit-construction moves below — **but the remaining #5431 (decomposed into #5449/#5450) does NOT, and the explicit-matrix moves are the wrong tool there:**
- **The two 3-dim `A₅` icosahedral reps `ℂ³₊`/`ℂ³₋` (golden-ratio `χ`) cannot be built as explicit-matrix `MonoidHom`s out of `alternatingGroup (Fin 5)`.** `map_mul` over 60 elements is infeasible by `decide` (even over the `DecidableEq` ring `Q5 = ℚ[√5]`), and the algebraic route would need `PresentedGroup {a⁵,b²,(ab)³} ≃* A₅` (the (2,3,5) von Dyck group has order 60 — Todd–Coxeter), which is **not in Mathlib**. The only feasible rigorous route is the **central-element eigenspace of `Λ²(ℂ⁴)`**: `Λ²(ℂ⁴) ≅ ℂ³₊ ⊕ ℂ³₋`, and `z = Σ_{c∈C} ρ(c)` (one 5-cycle class, 12 elts) acts as `4φ`/`4φ'` (min poly `X²−4X−16`), so each rep is an eigenspace-`Subrepresentation`, with character via the projector `(z−4φ'·id)/(4√5)` and `LinearMap.trace_eq_sum_trace_restrict`. Heavy but uses existing infra (`FDRep.char_tensor` in `Discussion_4_4.lean`, `Subrepresentation`, `Module.End.eigenspace`, `S4.fixCardM`). Do not attempt explicit matrices here. **Phase A landed (#5449 → PR #5454):** `Λ²(ℂ⁴)` is now a genuine `FDRep` `Etingof.Example4_8_1.A5.lam2` (= `range asym ⊆ repC4 ⊗ repC4`, `asym = ½(1−β)` the antisymmetriser), with `lam2_char_formula : lam2.character g = ½(repC4.character g ^2 − repC4.character (g*g))` and `lam2_character : … (classRepA5 j) = ![6,0,-2,1,1] j`, axiom-clean (no `native_decide`). The remaining eigenspace split (`z = Σ_{c∈C} lam2.ρ c` → `ℂ³₊`/`ℂ³₋`) is **#5453**: consume `lam2`/`lam2_character`, do NOT rebuild the exterior square. Two reusable lessons from Phase A: (a) the **swap-trace identity** `trace(swap ∘ map A B) = trace(A∘B)` is copyable from `Chapter5/FrobeniusSchurRealType.lean` (`trace_comm_comp_map`) specialised to ℂ (Ch4 cannot import Ch5); the antisymmetric-subrep character then comes from two `LinearMap.trace_eq_sum_trace_restrict` over the `±1`-eigenspaces of `β` (the `β = ∓1` on `range a`/`ker a` facts close by `linear_combination`/`module` after `LinearMap.smul_apply`+`LinearMap.sub_apply`+`Module.End.one_apply`). (b) **The idempotent-projection lemmas are in `namespace LinearMap`** — write `LinearMap.IsIdempotentElem.isCompl asym_idem` / `LinearMap.IsIdempotentElem.mem_range_iff asym_idem` (bare `asym_idem.isCompl`/`.mem_range_iff` fail: `IsIdempotentElem p` unfolds to the `Eq` `p*p=p`, so dot-notation resolves to `Eq.*`). Feed the `IsCompl (range a) (ker a)` to `DirectSum.isInternal_submodule_iff_isCompl ![range a, ker a] zero_ne_one huniv` for the `IsInternal` the trace lemma needs.
- **The "five simples + five conjugacy classes ⇒ complete table" certificate needs `#(irreducible FDRep ℂ G) = #(ConjClasses G)`, which Mathlib does NOT package** (`RepresentationTheory/` has `simple_iff_char_is_norm_one`, `char_orthonormal`, but no `ConjClasses`-count bridge) — this count theorem is exactly what the rejected `native_decide` orthonormality stood in for, and must be proven as reusable repo infra (or replaced by a decidable `IsCharacterTable` predicate).

**Honest (`native_decide`-free) arithmetic over the `Q5 = ℚ[√5]` character table (#5459 deliverable 4, the retired `A5_orthonormal`, sorry-free axiom-clean in `Chapter4/Example4_8_1.lean`).** Any computation over the book table `chiA5 : Fin 5 → Fin 5 → Q5` (the orthonormality `ip` sum, and the upcoming #5468/#5469 character/norm-one sums) — kernel `decide` **stalls**, but NOT on the `√5`/foldr: it stalls on `ℚ`-normalisation of a `1/N` factor (e.g. `1/60`), getting stuck at the `Rat.num` `Decidable` instance even after the `List.ofFn`/foldr is removed. So do not reach for `decide`; the working pattern is `Q5.ext` + `norm_num`:
  1. **A `sumFin_five`-style explicit-unfold lemma** (`sumFin f = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0))))`, proved by `simp only [sumFin, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]; rfl`). The bare `List.ofFn`/`List.foldr` simp lemmas reduce *inconsistently* in the big file vs a scratch (sometimes leaving an un-reduced `Fin.foldr 5 …`), so pre-unfold the fixed-arity sum into a named lemma rather than relying on `List.ofFn` inside the main proof.
  2. **`Q5` projection simp lemmas** `mk/zero/one/add/neg/mul/ofRat _re/_im` (all `rfl`). The `OfNat` ones MUST use `no_index`: `theorem ofNat_re (n : ℕ) : (no_index (OfNat.ofNat n) : Q5).re = (OfNat.ofNat n : ℚ) := rfl` — without `no_index`, simp's discrimination tree indexes on the literal and the lemma silently makes "no progress" on `(3 : Q5).re` (the custom `OfNat Q5 n` instance, not an `AtLeastTwo` one). Keep them **non-`@[simp]`** and pass explicitly: marking them `@[simp]` does NOT add warnings (the ~21 `unusedSimpArgs` in this file are pre-existing, e.g. `Matrix.toLin'_apply` at the Q₈ `rho_apply`), but explicit-only keeps the blast radius surgical.
  3. **One `norm_num` pass** after `fin_cases i <;> fin_cases j <;> (first | rw [if_pos rfl] | rw [if_neg (by decide)]) <;> apply Q5.ext <;> norm_num [ip, Q5.sumFin_five, sizesA5, chiA5, <all the Q5 _re/_im>, Matrix.cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, head_cons, tail_cons]`. `norm_num` (NOT `simp only`) is what reduces the `OfNat` literals and the `1/60 * (rational) = 0/1` arithmetic; the `cons_val_two/three/four` lemmas (they DO exist in this Mathlib — the existing `repC4_character` uses them) handle matrix indices ≥ 2 that `cons_val_zero/one`+`head_cons` miss. Probe the whole proof in a `/tmp` scratch (`gtimeout 400 lake env lean`) before the 90s file build.

Reusable pieces and the gotchas that each cost a build cycle:
- **The 2-dim quaternion rep already exists** as `Etingof.Q8.rho` in `Chapter5/Example5_1_3.lean` (matrices `A=diag(i,-i)`, `X=![![0,1],![-1,0]]`, `Mhom`, `rho`, plus an `IsSimpleModule` proof). But `Chapter5` *imports* `Chapter4`, so a Ch4 file **cannot** import it — rebuild the construction in a local namespace (no name collision since the namespace differs). Same will hold for any Ch4 rep that duplicates a Ch5 one.
- **Character from a rep:** `(FDRep.of ρ).character g = LinearMap.trace ℂ V (ρ g)` holds **by `rfl`** (`FDRep.of_ρ'` is `rfl`), so `rw [show (FDRep.of ρ).character g = LinearMap.trace ℂ V (ρ g) from rfl]`. For a matrix rep `ρ g = toLinAlgEquiv' (M g)`: rewrite `ρ g = toLin' (M g)` (by `ext; simp [ρ_apply, Matrix.toLin'_apply]`) then `Matrix.trace_toLin'_eq` gives `= (M g).trace`. For a 1-dim rep `ρ g = χ g • LinearMap.id`: `map_smul` + `LinearMap.trace_id` (= `finrank`) gives `χ g`.
- **Simplicity via `FDRep.simple_iff_char_is_norm_one`** (needs `[IsAlgClosed][CharZero][Fintype]`, all hold for ℂ + a finite group): the goal is `∑_{g:G} χ(g)·χ(g⁻¹) = Nat.card G`. **1-dim case is free** — the character *is* the `MonoidHom`, so each summand `χ(g)·χ(g⁻¹) = χ(g·g⁻¹) = 1` (`← map_mul, mul_inv_cancel, map_one`), and `Finset.sum_const` finishes; no enumeration. **2-dim (or higher) case** needs an explicit `∑_{g:G}` enumeration: build `enum : Fin |G| → G`, prove `Function.Bijective enum` by `Fintype.bijective_iff_injective_and_card` + `⟨by decide, by decide⟩`, then `rw [← Equiv.sum_comp (Equiv.ofBijective enum _) f, Fin.sum_univ_eight]; simp only [Equiv.ofBijective_apply, enum]; rfl`. Carry the 8 per-element inverses as `show g⁻¹ = h from by decide`.
- **Pairwise non-iso:** `FDRep.char_iso : (V ≅ W) → V.character = W.character` (forward direction only — no `char_orthonormal` needed). Don't prove distinctness cell-by-cell with `simp`/`norm_num` on the ℂ values (the `fin_cases` Fin-literal problem below bites). Instead lift to a **decidable** structural statement: `Q5toC` (the table→ℂ map) is injective on rational entries (`im = 0`), so character-equality forces `chiQ8 i = chiQ8 j` as `Q5`-vectors, and `Function.Injective chiQ8` closes by **`decide`** (Q5 has `DecidableEq`). `|G|` and `#ConjClasses` likewise: `Fintype.card G` via the group's `card` lemma, `Fintype.card (ConjClasses G) = r` by honest `decide` (kernel-checked, fine).

Three gotchas that each cost a build cycle:
1. **`@[simp] a_zero : (a 0 : QuaternionGroup n) = 1`** (and `DihedralGroup.r_zero`, etc.) silently rewrites the identity element under any `simp`/`norm_num`, so a per-element value lemma keyed on `a 0` stops matching (the term becomes `1`). Use **`norm_num [-QuaternionGroup.a_zero, …]`** (or `simp only` with an explicit list that excludes it). Watch the dual: `FDRep.char_one` (`χ 1 = finrank`) then fires on the `1` and derails a 2-dim trace computation.
2. **`revert i j; decide` for a finite-`ZMod` parity/arithmetic fact reverts *everything* depending on `i,j`** — including a `have e : … = …` whose RHS mentions ℂ-valued vars (α, β), making the reverted goal non-decidable (`decide` errors "expected type must not contain free variables"). **Compute the decidable fact into a `have hp := by revert i j; decide` BEFORE introducing any ℂ-valued `have`.**
3. **`fin_cases i` produces `⟨0, ⋯⟩`, which does *not* reduce `![…] ⟨0,⋯⟩` / table lookups under `simp`/`norm_num`** (the `Matrix.cons_val_*` simp lemmas are keyed on the numeral `0`, not `Fin.mk 0`), but it *does* reduce by **defeq**. So per-cell character-matching proofs should `change <defeq-reduced LHS> = <defeq-reduced RHS>` (e.g. `change chiFun 1 1 (a 0) = Q5toC (1:Q5)`) and then finish — `change` bridges via defeq where `simp` stalls. Assembling the indexed lemma (`irrep i …` for `i:Fin 5`) from per-row lemmas is a clean `fin_cases i` + `exact char_row0 j` (the `exact` matches `⟨0,⋯⟩` to the `0`-literal lemma by defeq).

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
- **`tr(A⁻¹) = conj(tr A)` for a finite-order ℂ-matrix (`χ(g⁻¹)=conj χ(g)`, the real-character / Frobenius–Schur ingredient, #5235).** Do NOT build an eigenbasis or unitarise — the charpoly-roots route is shorter and fully constructive. `tr A = (charpoly A).roots.sum` (`Matrix.trace_eq_sum_roots_charpoly`, alg-closed); each root `μ` is an eigenvalue of `Matrix.toLin' A` (`Module.End.hasEigenvalue_iff_isRoot_charpoly` + `Matrix.charpoly_toLin'`), and `(toLin' A)^n = id` (`← Matrix.toLin'_pow`, `Matrix.toLin'_one`) forces `μ^n = 1`, hence `‖μ‖ = 1` and `conj μ = μ⁻¹` (`Complex.inv_eq_conj`). For `tr(A⁻¹)`: `Matrix.charpoly_inv` + `Matrix.reverse_charpoly` give `charpoly A⁻¹ = C(c) * (charpoly A).reverse` (`c ≠ 0`), so `roots = (charpoly A).reverse.roots`. **Mathlib has NO `Polynomial.roots_reverse`** — prove `(reverse p).roots = p.roots.map (·⁻¹)` for monic split `p` with `0 ∉ p.roots` yourself: factor `p = (p.roots.map (X - C ·)).prod` (`Splits.eq_prod_roots_of_monic`), use that `reverse` is multiplicative over a `Multiset` in a domain (induction + `reverse_mul_of_domain`), and `reverse (X - C a) = C(-a)*X + C 1` has the single root `a⁻¹` (`roots_C_mul_X_add_C_of_IsUnit`). To reduce an *endomorphism* trace/inverse to a matrix, use `LinearMap.toMatrixAlgEquiv b` (the basis-version `AlgEquiv`, defeq to `toMatrix b b`): `E (ρ g⁻¹) = (E (ρ g))⁻¹` via `Matrix.inv_eq_left_inv`, and `E (ρ g) ^ orderOf g = 1` via `map_pow`/`map_one`. Reusable helpers landed in `Chapter5/FrobeniusSchurRealType.lean`: `reverse_multiset_prod`, `roots_reverse_X_sub_C`, `roots_reverse_eq_map_inv`, `matrix_trace_inv_eq_conj`, and `character_inv_eq_conj`.
- **Twisting an `sl(2)` (or any Lie-algebra) representation to make `ρ(e)` a chosen operator — conjugation recipe (#5309, single Jordan block of Jacobson–Morozov part (l), `Chapter2/Problem2_15_1_l.lean`).** To turn the irreducible `rhoLieHom n : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ)` into a rep whose `ρ(e)` is a *specific* nilpotent (here the standard shift `J_{0,n}`, `e_k ↦ e_{k-1}`), conjugate by a `LinearEquiv` `φ`: `(φ.conjAlgEquiv ℂ : _ →ₐ[ℂ] _).toLieHom.comp (rhoLieHom n)` is again a `LieHom` (algebra-equiv conjugation `LinearEquiv.conjAlgEquiv` from `Mathlib.Algebra.Algebra.Equiv` preserves the commutator bracket; `AlgHom.toLieHom` lifts it). `conjAlgEquiv_apply` rewrites it to `φ ∘ₗ f ∘ₗ φ.symm`. Since `rhoLieHom n sl2_e` acts as `e_k ↦ k · e_{k-1}` (a single Jordan block already), the diagonal rescaling `φ : e_k ↦ k! · e_k` normalises the subdiagonal coefficients to `1`. **Crucial API constraint: `Sl2Irrep.lean`'s component maps `rhoH/E/F` and `rhoLieHom_sl2_*_eq` are `private`** — you cannot name them from another file. Compute the conjugation on the standard basis instead via the *public* `lie_eq_rhoLieHom` (`⁅x,v⁆ = rhoLieHom d x v`) + `lie_sl2_e_e_basis`/`lie_sl2_f_e_basis`/`lie_sl2_h_e_basis` + `e_basis`, and prove the endomorphism equality with `(Pi.basisFun ℂ (Fin n)).ext` (`Pi.basisFun_apply : … = Pi.single k 1`, defeq `e_basis n k` — bridge with `change`, not `show`, to dodge the style linter). Nilpotency of the shift: a `jordanShift_pow_apply` induction (`(J^m v) k = if k+m<n then v⟨k+m⟩ else 0`) gives `J^n = 0`. **`omega` gotcha: it does NOT unfold `Fin.val` of an explicit `Fin.mk` (`↑⟨a,h⟩` stays opaque)** — feed the nat-level equality directly, e.g. `congrArg v (Fin.ext (show a = b by omega))`, where `a`,`b` are the *reduced* vals. The general nilpotent case (assemble arbitrary `A` over Jordan blocks) needs a Jordan-basis decomposition that is **not** in Mathlib (`JordanChevalley` is only the semisimple+nilpotent split) — tracked in #5312.

- **A single-operator `k[X]`-rep `V_{λ,n}` as a genuine module, and its indecomposability + non-simplicity (#5358, sorry-free in `Chapter2/Example2_3_14.lean`, namespace `Etingof.Example_2_3_14`).** To realize the representation `(kⁿ, ρ(x)=J_{λ,n})` as a real `k[X]`-module, use `Module.AEval' (jordanBlock lam n)` (NOT a hand-rolled module): `X` acts as the operator, `Module.AEval'.of φ : (Fin n → k) ≃ₗ[k] AEval' φ` is the comparison equiv, and `Module.AEval'.X_smul_of`/`Module.AEval.of_aeval_smul` push the action through `of`. **Indecomposability proof pattern (reusable for any operator whose eigenline is 1-dim):** define module-level `IsIndecomposable R M := Nontrivial M ∧ ∀ N P, IsCompl N P → N = ⊥ ∨ P = ⊥`; pull each `k[X]`-submodule `N` back to the `k`-subspace `W := (N.restrictScalars k).comap of.toLinearMap` (then `m ∈ W ↔ of m ∈ N` is `Iff.rfl`), which is automatically `φ`-invariant via `X_smul_of`; show every nonzero invariant `W` contains the eigenvector `e₀` (the engine `e0_mem_of_invariant`: `shift = J − λ•id` is nilpotent — `isNilpotent.restrict` to `W` — and `Module.End.isNilpotent` restricted to a nontrivial subspace has a nonzero kernel vector, which lands in `ker shift ≤ span{e₀}`); two complementary nonzero submodules then both contain `of e₀`, contradicting `hcompl.inf_eq_bot`. **Non-simplicity (n ≥ 2):** the cyclic submodule `span k[X] {of e₀}` is the 1-dim eigenline — every `p • of e₀ = of (p.eval λ • e₀)` by `Module.End.aeval_apply_of_mem_apply_eq_smul` (the eigenvector-aeval lemma, only needs `J e₀ = λ•e₀`) — so `of e₁ ∉` it; combined with `IsSimpleModule ↔ IsSimpleOrder (Submodule …)` (`eq_bot_or_eq_top`) this gives `¬ IsSimpleModule`. Generic helper `exists_mem_ker_of_isNilpotent` (nilpotent endo on `Nontrivial` module ⟹ nonzero kernel vector) is proved by `g` injective ⟹ `g^m` injective ⟹ `g^m = 0` contradicts `exists_pair_ne`. The JNF *completeness* direction (every f.d. indecomposable is some `V_{λ,n}`) is out of scope — book cites Jordan normal form, doesn't prove it.

- **Frobenius-Schur trace identity `FS(ρ) = |G|⁻¹ ∑ χ(g²) ∈ {±1}` for self-dual simple ρ (#5261).** Work on `V ⊗ V` with `T = tprod ρ ρ` and the swap `cm = TensorProduct.comm`, NOT bilinear forms (the swap is then a clean permutation matrix). The chain (all sorry-free in `Chapter5/FrobeniusSchurTraceIdentity.lean`, reuse before rebuilding): (1) `tr(swap·(A ⊗ₖ A)) = tr(A·A)` — `Matrix.trace` + `Fintype.sum_prod_type` (one diagonal entry is `(A⊗ₖA)(Prod.swap p) p` via `Finset.sum_eq_single` on the `submatrix Prod.swap id` row of `1`); lift to endomorphisms with `TensorProduct.toMatrix_comm` + `TensorProduct.toMatrix_map` + `LinearMap.trace_eq_matrix_trace`/`toMatrix_comp`, giving `trace(cm ∘ map A A) = trace(A ∘ A)`, so `trace(cm ∘ T g) = χ(g²)`. (2) `averageMap T = ⅟|G| • ∑ T g` (`asAlgebraHom_of`); `cm` is equivariant + involutive so it preserves `T.invariants` and `averageMap` is the identity there, so `FS = trace(cm ∘ averageMap) = trace(cm|_invariants)` via `LinearMap.trace_restrict_eq_of_forall_mem`. (3) `dim T.invariants = |G|⁻¹ ∑ χ(g)² = |G|⁻¹ ∑ χ(g)χ(g⁻¹) = 1` (self-duality + `card_inv_mul_sum_char_eq_finrank` + `char_orthonormal`). (4) a linear involution on a 1-dim space has trace `±1` (`trace_fin_one` + `mul_self_eq_one_iff`). The exported theorem is `Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple`. **The twin #5214 (`exists_nonzero_invariant_symmetric_of_FS_eq_one`) landed (sorry-free) in the bilinear-form model** (`Bil = V →ₗ Dual V = linHom ρ ρ.dual`, flip `τ = LinearMap.lflip`) — see the next bullet for its (self-contained) machinery. Gotchas: `⊗ₖ` needs `open scoped Kronecker`; `W.ρ.asModule` dot-notation resolves to `MonoidHom.asModule` — write `Representation.asModule W.ρ`; a `Finset.sum_congr rfl (fun g _ => ?_)` left after `simp [map_sum]` stalls instance synthesis (`AddCommMonoid ?m`) — split the per-term equality into a named `have` and apply it via `congrArg (c * ·) (Finset.sum_congr …)` instead.
- **`FS = 1 ⟹ ∃ nonzero invariant *symmetric* form (#5214, bilinear-form model, sorry-free in `Chapter5/FrobeniusSchurRealType.lean`).** Two reusable pieces. (a) `trace_comm_comp_map`: `trace((comm).toLinearMap ∘ₗ map A B) = trace (A ∘ₗ B)` on `W ⊗ W` for any finite-dim `W` (abstract sibling of #5261's Kronecker version) — proved with `Module.Basis.tensorProduct b b` + `trace_eq_sum_repr_diag` (= `∑ i, b.repr (f (b i)) i`) + `Module.Basis.tensorProduct_repr_tmul_apply`, matching the diagonal sum to `(toMatrix A * toMatrix B).trace` via `Finset.sum_comm`. (b) The projector-counting recipe: averaging projector `P = averageMap Λ` (`isProj_averageMap.trace` = `finrank invariants`), symmetric-part projector `Pₛ = ½(P + τ∘ₗP)` (idempotent via `τ²=1`, `τ` commutes with `P`; `IsProj` via `isProj_range_iff_isIdempotentElem`, trace = `finrank (range Pₛ)`), giving `2·finrank(sym∩Bil^G) = finrank Bil^G + trace(τ∘P)`. The crux `trace(τ∘P) = FS` reduces per-`g` (`trace(τ∘Λg) = χ(g⁻¹g⁻¹)`) by conjugating `τ∘Λg` to `comm∘map(ρ.dual g)(ρ.dual g)` through `E = dualTensorHomEquiv ℂ V (Dual V)` (prove the intertwiner `(τ∘Λg)∘E = E∘(comm∘map…)` on pure tensors, then `LinearMap.trace_comp_comm'` + `trace_comm_comp_map`). `FS=1 ⟹ 2s = d+1 ⟹ s ≥ 1`. **No simplicity needed for existence** — `hρ` is only used by the nondegeneracy half (`nondegenerate_of_invariant_of_simple`). Simp gotchas that cost iterations: (i) after `set Λ := linHom …`, `linHom_apply`/`dual_apply` will NOT fire in `simp` (terms display as `Λ`); prove a pointwise `hΛapp : (Λ g C) v w = C (ρ g⁻¹ v) (ρ g⁻¹ w)` once via `rw [hΛdef, linHom_apply]; simp [comp_apply, dual_apply, Module.Dual.transpose_apply]` and use *that* in later `rw`/`simp`. (ii) `LinearEquiv.coe_coe` in a `rw`/`simp` set unfolds EVERY `↑e` — including a `set`-defined `τ = (lflip).toLinearMap` → `LinearMap.lflip`, silently breaking `τ`-keyed lemmas; apply the operator's own `_apply` lemma (`hτ_apply`) BEFORE `coe_coe`. (iii) `ρ.dual g` is *defeq* but not *syntactically* `Module.Dual.transpose (ρ g⁻¹)` and its display flips unpredictably mid-`rw`-chain — finish the scalar reduction with `simp only [dual_apply, transpose_apply, comp_apply, smul_eq_mul]`, not a fixed `rw` order.

- **Frobenius induced-character formula (Theorem 5.9.1, #5321, sorry-free in `Chapter5/Theorem5_9_1.lean` + `Chapter5/TraceCoinvariants.lean`).** Mathlib's `Representation.ind` is the *tensor/coinvariants* model (`IndV = Coinvariants (tprod (leftRegular ⊗ ρ))`), so do NOT chase coset transversals — prove the **averaged** form via the reusable crux `Etingof.trace_coinvariantsMap σ Φ : trace (Coinvariants.map σ σ Φ) = |Γ|⁻¹ ∑_{h:Γ} trace (σ h ∘ₗ Φ.toLinearMap)` (finite group, char-0, fin-dim). Its proof is the canonical averaging-idempotent argument and is itself reusable for any coinvariants-trace: `e = averageMap σ` projects onto `invariants σ` with `ker e = Coinvariants.ker σ` (`ker_averageMap`, both inclusions via `averageMap_apply` + an `Equiv.mulRight` reindex), so `Submodule.quotientEquivOfIsCompl` gives `Coinvariants σ ≃ invariants σ`; `Φ̄` conjugates to `Φ.restrict` (`LinearEquiv.conj_apply_apply` + `LinearMap.trace_conj'`), then `LinearMap.trace_comp_comm'` moves it to `trace (e ∘ Φ)`, and `averageMap_eq : averageMap σ = |Γ|⁻¹ • ∑ σ h` finishes by linearity. Application wiring: `ind` is `@[simps]` so `rw [Representation.ind_apply]` exposes the shift intertwiner `⟨(lmapDomain (·*g⁻¹)).rTensor V, _⟩` directly — avoid `rfl`-matching a hand-built `IntertwiningMap`, the `Coinvariants.map` defeq check times out at `whnf`. Each twisted trace factors via `LinearMap.trace_tensorProduct'` into a `ℂ[G]`-trace `Etingof.trace_lmapDomain φ = ∑ x, if φ x = x then 1 else 0` (proved with `Finsupp.basisSingleOne` + `trace_eq_matrix_trace`) times `tr_V ρ(h)`; `Finset.sum_comm` + `Etingof.sum_subtype_ite_coe` collapse each fibre `{x : h·x·g⁻¹ = x} = {x : x·g·x⁻¹ = h}`. Gotchas: `⊗[ℂ]` needs `open scoped TensorProduct`; there is no `LinearMap.sum_comp` for `(c•∑ f)∘ₗΦ` — push the sum through with a one-line `ext; simp [LinearMap.sum_apply]`; `congr 1` on `TensorProduct.map A B = map C D` silently closes any *defeq* component (`ρh∘id` vs `ρh`), so normalise with `LinearMap.comp_id`/`id_comp` first rather than writing a second bullet for it.
- **Centre of `ℂ[G]` = class functions, and the renormalised-character recovery formula (Remark 4.5.3, #5336, sorry-free in `Chapter4/Remark4_5_3.lean`).** `classFunctions G := Subalgebra.center ℂ (MonoidAlgebra ℂ G)`. To prove `f ∈ centre ↔ IsClassFunction f` (`∀ x y, f(yxy⁻¹)=f x`): `simp only [classFunctions, Subalgebra.mem_center_iff]` (the `def`-name unfolds the centre membership to `∀ b, b*f = f*b`). **Forward**: test centrality against `single y 1`, evaluate the function equality at `y*x` via `congrArg (fun F => F (y*x)) (h (single y 1))`, then `simp only [single_mul_apply, mul_single_apply, one_mul, mul_one]` (these `MonoidAlgebra` group lemmas give `(single y 1 * f) p = f (y⁻¹*p)` and `(f * single y 1) p = f (p*y⁻¹)`) and clean the group word with `rw [show y⁻¹*(y*x) = x by group]`. **Backward**: `ext z; rw [mul_apply_left, mul_apply_right]` turns `b*f = f*b` into two `b.sum` expansions `∑ r·f(g⁻¹z)` vs `∑ f(zg⁻¹)·r`; `Finsupp.sum_congr` + `mul_comm` reduces to the pointwise conjugation `f(g⁻¹z)=f(zg⁻¹)`, supplied by the class-fn hyp at `(z*g⁻¹, g⁻¹)` after `rw [show g⁻¹*(z*g⁻¹)*g⁻¹⁻¹ = g⁻¹*z by group]`. `renormCharElt_mem_classFunctions` is then one `rw [mem_classFunctions_iff]` + `FDRep.char_conj`. The **recovery formula** `χ_V(g) = √(|G|/χ̃_V(1))·χ̃_V(g)` with normalisation `χ̃_V(z)=(χ_V(1)/|G|)χ_V(z)`: the witness is just `c = |G|/χ_V(1)` (both the `c²=|G|/χ̃_V(1)` and the `χ_V(g)=c·χ̃_V(g)` legs close with bare `field_simp` — no `ring` needed, it over-closes to "no goals"). Need `χ_V(1)=dim V≠0` for simple `V`: a universe-poly clone of `Corollary4_2_4.finrank_pos_of_simple` (`finrank=0 ⇒ Subsingleton V ⇒ Subsingleton (V⟶V)`, contradicting `FDRep.finrank_hom_simple_simple = 1`), then `FDRep.char_one` + `exact_mod_cast …ne'`. **Still open (#5349)**: `renormChar_isPrimitiveIdempotent` (idempotency needs the convolution Schur identity `∑_x χ(x)χ(x⁻¹z)=(|G|/dim)χ(z)` via "`B=∑χ(x⁻¹)ρ(x)` is `G`-equivariant ⇒ scalar by Schur"; primitivity needs the centre's `∏ℂ` Wedderburn structure, not in Mathlib).

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

### Induced rep `Ind_H^G ℂ ≅ k[G]·a` as `Representation.Equiv`, and the MonoidAlgebra/Finsupp instance wall (#5171)

Goal: `Etingof.Definition5_8_1 H (trivial) ≅ ℂ[G]·a` (left ideal). Recipe in
`Chapter5/Introduction5_14.lean` (sorry-free). Source is Mathlib's
`Representation.ind φ ρ` on `Coinvariants (tprod ((leftRegular).comp φ) ρ)` over
`(G →₀ ℂ) ⊗ ℂ`; build the forward map `⟦δ_g ⊗ c⟧ ↦ c·(g⁻¹·a)` via `Coinvariants.lift f0 hinv`
(invariance = `of p * a = a` for `p ∈ H`, proved reindexing the subgroup sum by `Equiv.mulLeft`);
corestrict to `LinearMap.range (mulRight ℂ a)`; bijectivity from a normalised left inverse
(factor `1/|H|`, the `|H|`-fold coinvariant collapse) for injectivity and a section
`Ffull (sMap z) = z·a` for surjectivity; equivariance on `IndV.mk` generators via `ind_mk`.
Package with `Representation.Equiv.mk linEquiv intertwine` (the bundled bare-`Representation` iso —
better target than a `Rep` `≅` here; `(mk e he)` wants `he : ∀ g, ↑e ∘ₗ ρ g = σ g ∘ₗ ↑e`).

**The instance wall** (cost ~5 build cycles — `MonoidAlgebra ℂ G` and `G →₀ ℂ` carry *different*
`AddCommMonoid`/`Module` instances on the same carrier, defeq but not syntactically equal):
- `LinearMap.comp` (`∘ₗ`) and `LinearMap`-equality *types* reject a middle/codomain that is
  `MonoidAlgebra` on one side and `G →₀ ℂ` on the other ("not type-correct under instances
  transparency"). Bridge with an **all-`rfl` identity `LinearEquiv toFinsuppLE : MonoidAlgebra ℂ G ≃ₗ (G →₀ ℂ)`**
  (`toFun := id`, every field `rfl` — it compiles), and compose maps from `Finsupp.lsum`/
  `linearCombination` (which produce `G →₀ ℂ` domains) with `toFinsuppLE.toLinearMap` to retype.
- A bare `Finsupp.single h r * (algebra)` fails to elaborate (`Finsupp` has **no `Mul`**);
  write `MonoidAlgebra.single h r` (an abbrev for `Finsupp.single`, but typed in `MonoidAlgebra`)
  in any multiplied position — *including lemma statements*, where there's no context to coerce.
- A lambda body `MonoidAlgebra.of … h * a` inside `lsum`/`linearCombination` (expected type a
  metavar) gets `of …` whnf'd to `G →₀ ℂ` and loses `Mul` → `HMul (G →₀ ℂ) (MonoidAlgebra) ?`.
  Define such maps as `LinearMap.mulRight ℂ a ∘ₗ (a map landing in MonoidAlgebra)` instead of
  multiplying inside the lambda.
- **Never `rw` a `leftRegular`/`ofMulAction` term (lives on `G →₀ ℂ`) applied to a
  `MonoidAlgebra`-typed argument** — the rewrite motive is heterogeneous and fails. For the
  *target* left-multiplication action, use a `MonoidAlgebra`-native rep
  `leftMulRep g := LinearMap.mulLeft ℂ (of g)` (then `leftMulRep g x = of g * x` is `rfl`), not
  `subrepresentation (leftRegular …)`. Note a def that doesn't *use* `la` won't bind it — call it
  `leftMulRep n`, not `leftMulRep n la`.
- `Representation.IndV.mk` is a **reducible abbrev**, so `simp`/`ext_ring` unfold it to
  `Coinvariants.mk … (TensorProduct.mk … (single h 1) c)` and then `Representation.ind_mk`/
  `Ffull_IndVmk` no longer pattern-match. Re-fold with `change Ffull (… (IndV.mk … h 1)) = …`
  before the `rw` chain.

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

### Scalar extension `ℂ ⊗_ℚ k[S_n]·c_λ ≅ ℂ[S_n]·c_λ` (Specht rational form, #5234)

To prove the base-change compatibility "`SpechtModuleK ℂ` is the complexification of `SpechtModuleK ℚ`"
as an `S_n`-rep iso (`Chapter5/SpechtBaseChangeComplex.lean`), the working recipe — avoiding any
"rational vectors ℚ-indep ⇒ ℂ-indep" linear algebra:
- **Do NOT reach for `MonoidAlgebra.scalarTensorEquiv`/`tensorEquiv`** (`ℂ ⊗_R R[M] ≃ₐ A[M]`): they require
  `[CommMonoid M]`, so they are **unusable for `S_n` = `Equiv.Perm (Fin n)`** (non-commutative for `n ≥ 3`).
- Build the map with `LinearMap.liftBaseChange ℂ (g : ↥V_ℚ →ₗ[ℚ] ℂ[S_n])`, `g v = j v` where
  `j = MonoidAlgebra.mapRingHom (algebraMap ℚ ℂ)`. Get `j` as a `ℚ`-linear map via
  `(jHom).toAddMonoidHom.toRatLinearMap` (every additive map of ℚ-spaces is ℚ-linear).
- **Range** = `V_ℂ`: `LinearMap.range_liftBaseChange` gives `span ℂ (range g)`; finish by span double-inclusion
  using `j c_ℚ = c_ℂ` and `j` multiplicative (⊇ via `Finsupp.induction_linear` on `b`, showing each
  `b * c_ℂ ∈ span`, `of σ * c_ℂ = g ⟨of σ * c_ℚ, _⟩`).
- **Injectivity** via flatness, *not* coordinates: factor `Ψ = TensorProduct.finsuppScalarRight ℚ ℂ ℂ G ∘ lTensor ℂ (incl)`.
  `Module.Flat.lTensor_preserves_injective_linearMap` (ℂ free⇒flat over ℚ) makes `lTensor ℂ` of the injective
  inclusion `V_ℚ ↪ ℚ[S_n]` injective; `finsuppScalarRight` is an equiv. NB `MonoidAlgebra ℚ G` is defeq `G →₀ ℚ`,
  so `finsuppScalarRight` (four explicit args `R S M ι`; `N` is unused) applies even though `S_n` is non-commutative.
- **Equivariance** (intertwines `LinearMap.baseChange ℂ (spechtModuleActionK ℚ …)` with `spechtModuleActionK ℂ …`):
  one line, `j (of σ * x) = of σ * j x` + `mul_smul_comm`.
- Corestrict: `(LinearEquiv.ofInjective Ψ hinj).trans (LinearEquiv.ofEq … range_eq)`; the target
  `↥(p.restrictScalars ℂ)` is defeq to `↥p`, so the equiv lands in `↥(SpechtModuleK ℂ)` directly and
  `(Φ t : ℂ[S_n]) = Ψ t` is `rfl`.

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

### Recursive defs on inductives: use the recursor when you need `rfl` equation lemmas

When you define a function on an inductive (e.g. `Quiver.Path`, recursing on `cons`) with
**equation-compiler syntax** (`| _, nil => …` / `| _, cons p e => …`), the compiled term may use
non-reducing `brecOn`, so the obvious `@[simp] theorem foo_nil … := rfl` / `foo_cons … := rfl`
**fail** ("not definitionally equal" / `rfl : ?m = ?m` against the expected type). This cost a build
cycle on `pathMap` (Ch2 #5222, `Discussion_quiver_rep_bijection.lean`). **Fix:** define it term-mode
via the recursor with an explicit motive, then the equations are genuine `rfl`:
```lean
noncomputable def pathMap (R …) {a b : Q} (p : Quiver.Path a b) : … :=
  Quiver.Path.rec (motive := fun b _ => …) LinearMap.id (fun _ e ih => ih ∘ₗ R.mapLinear e.op) p
@[simp] theorem pathMap_nil  … := rfl   -- now works
@[simp] theorem pathMap_cons … := rfl   -- now works
```
`induction p with | nil | cons …` still works on top of the recursor def (it just uses these simp
lemmas). Separately: when a lemma over a section with `variable [DecidableEq Q]` does not actually
use it (the `pathMap_*` lemmas don't), the `unusedDecidableInType` linter warns — prefix the lemma
with `omit [DecidableEq Q] in` (placed *before* any docstring).

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

#### `IsSimpleModule k[G] ρ.asModule` for a *concrete* representation (Ch5 Example5.1.3 Q₈, #5124)

To prove a hand-built representation `ρ : Representation k G V` is irreducible
(its `asModule` is simple), do **not** reason about `Submodule k[G] ρ.asModule`
directly — work with `ρ`-invariant `k`-subspaces of `V` and transport:

- `Representation.mapSubmodule ρ : ρ.invtSubmodule ≃o Submodule k[G] ρ.asModule`
  is the order iso (in `Mathlib.RepresentationTheory.Submodule`).
- `OrderIso.isSimpleOrder_iff` turns `IsSimpleOrder ρ.invtSubmodule` into
  `IsSimpleOrder (Submodule k[G] ρ.asModule)`. `IsSimpleModule` *extends* that
  `IsSimpleOrder`, but its constructor has **no explicit fields** (the parent is
  instance-implicit): do `suffices hSO : IsSimpleOrder ρ.invtSubmodule by
  haveI := (Representation.mapSubmodule ρ).isSimpleOrder_iff.mp hSO; exact ⟨⟩`.
- Build `IsSimpleOrder ρ.invtSubmodule` via
  `refine { eq_bot_or_eq_top := fun a => ?_ }` (the `Nontrivial` parent comes
  from the existing `[Nontrivial V]` instance). `a : ρ.invtSubmodule`; recover
  the underlying subspace as `(a : Submodule k V)` and its invariance from
  `(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := ρ g)).mp
  ((Representation.mem_invtSubmodule (ρ := ρ)).mp a.2 g)` — both lemmas take the
  endomorphism/representation **explicitly**, so pass `(f := …)`/`(ρ := …)` or
  the bare `name.mp` reads as an unknown constant.
- Then the math: `a ≠ ⊥` ⇒ pick `0 ≠ v ∈ a` (`(Submodule.ne_bot_iff _).mp`),
  apply two generators (as explicit `Matrix.mulVec` evaluations) to manufacture
  the standard basis vectors inside `a` via `smul_mem`/`sub_mem`/`neg_mem`, then
  `eq_top` from "two basis vectors span". For a 2-dim rep this is the "diagonal
  generator and swap share no common eigenline" argument.

**Faithful "completely reducible / semisimple" statement (anti-vacuity, #5384).**
To say a representation `ρ : Representation k G V` is *completely reducible*, write
`IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule` — semisimplicity of the
*`k[G]`-module*. Do **NOT** write `IsSemisimpleModule k V`: over a field every
vector space is semisimple, so that conclusion is **vacuous** and carries zero
representation content (this was the exact bug in `Theorem5_23_2_i`). The `k[G]`
form is genuine content precisely because `k[G]` is not a semisimple ring for
infinite `G` (e.g. `GL_n(k)`). Type `ρ` as `Representation` (not a bare `→*`) so
`.asModule` resolves. Same anti-vacuity smell elsewhere: a Peter-Weyl / decomposition
`X ≅ ⊕ …` stated as a bare `k`-linear (or rank-matching `nonempty_linearEquiv_of_rank_eq`)
iso is vacuous — the real claim is a `G`-(or `G×G`-)*equivariant* iso, which needs
the actual `Representation` structures on both sides.

Build matrix reps as a `MonoidHom G →* Matrix n n k` composed with
`Matrix.toLinAlgEquiv'` (a monoid hom into `End`); `ρ g v = (Mhom g).mulVec v`
via `Matrix.toLinAlgEquiv'_apply`. **`ring` does not work on the noncommutative
matrix ring** — for `A^4 = (A^2)^2` use `pow_mul`; for `(-1)^2` use
`neg_one_sq`; reduce `A^a = A^b` (same base, `A^4=1`) to a `ZMod`-exponent
equality with a `Nat.div_add_mod`/`pow_add`/`pow_mul` helper plus
`ZMod.natCast_eq_natCast_iff`, then close non-`ring` modular facts (e.g.
`3*i ≡ -i [4]`) with `decide`. An `SL₂` rep preserves the wedge form
`B(v,w)=v₀w₁−v₁w₀` automatically: `B(Nv,Nw) = det N · B(v,w)` (a `Fin 2`
`ring` identity), so invariance reduces to `det (ρ g) = 1`.

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

#### `dim V_λ` for a *concrete* partition λ (Ch5 Example5.12.3, #5125)

`Module.finrank ℂ (SpechtModule n la) = n! / ∏ h(i,j)` via
`finrank_spechtModule_eq_card_syt_general` (`dim = |SYT|`,
`CharValueHookFormula.lean`) then `card_standardYoungTableau_eq` (`|SYT| = n!/∏h`,
`FRTHelpers.lean`). The only work left is the hook-length product for the shape —
but **`decide` cannot evaluate it directly**: `YoungDiagram.rowLen`/`colLen` use
`Nat.find` and `Nat.Partition.sortedParts` uses `Multiset.sort` (mergeSort),
both well-founded recursions that the kernel will not reduce. Two-step fix
(worked template in `Chapter5/Example5_12_3.lean`, reuse it verbatim):
1. Rewrite hooks into a `Nat.find`-free product: `colLen c = #{rows longer than
   c}` (`toYoungDiagram_colLen_eq`), giving `hookLengthProduct_eq_compute`.
2. Pin `sortedParts = [explicit list]` with `sortedParts_eq_of` (proof: `μ.parts
   = ↑L` by `rfl` + `L.Pairwise (·≥·)` by `decide`, closed by
   `List.mergeSort_eq_self`), then `hookLengthProduct_eq_of` leaves a product
   over `cellsOfRowLens L` that **is** kernel-reducible, so `by decide` finishes.
The single-row/single-column hook product is `∏_{k<n}(n−k) = n!`
(`prod_range_sub`, via `Finset.prod_range_reflect` +
`Finset.prod_range_add_one_eq_factorial`), giving the general trivial- and
sign-representation dimensions (`dim = 1`). The current Mathlib `Multiset.sort`
API is `Pairwise`-based: there is no `List.Sorted`/`eq_of_perm_of_sorted`; use
`Multiset.sort_cons`/`sort_singleton`/`coe_sort` + `List.mergeSort_eq_self`.

#### Multiplicative character of a finite cyclic subgroup (e.g. `ℂ_ε` on `Z₃ = A₃`, #5248)

To build a character `χ : ↥H →* ℂˣ` of a concrete cyclic subgroup `H ≤ G` sending a chosen
generator `g₀ : ↥H` to a chosen unit `u : ℂˣ`, use `monoidHomOfForallMemZpowers`
(`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`): `monoidHomOfForallMemZpowers (hg : ∀ x, x ∈
Subgroup.zpowers g₀) (hg' : orderOf u ∣ orderOf g₀) : ↥H →* ℂˣ`, with
`monoidHomOfForallMemZpowers_apply_gen` giving `χ g₀ = u`. Worked, sorry-free in
`Chapter5/Discussion5_11_examples.lean` (`epsHom`, the cube-root character `ε(gen) = exp(2πi/3)`).
**`decide` does NOT discharge the three obligations** — each needs a real proof:

- **`g₀ ∈ H`** (here `finRotate 3 ∈ alternatingGroup (Fin 3)`): unfold the subgroup and rewrite to
  the membership predicate first — `rw [Equiv.Perm.mem_alternatingGroup]; decide` (`decide` *does*
  evaluate `sign (finRotate 3) = 1`, but not the bare `∈ alternatingGroup`, which lacks a
  `Decidable` instance).
- **`orderOf g₀ = n`** (`decide` on `orderOf` times out / no instance): use `orderOf_eq_prime`
  (needs `haveI : Fact (Nat.Prime n)`) with `g₀ ^ n = 1` (by `Subtype.ext; decide` on the
  underlying perm) and `g₀ ≠ 1` (`fun h => absurd (congrArg Subtype.val h) (by decide)`).
- **`∀ x, x ∈ Subgroup.zpowers g₀`** (the `∃ k : ℤ` makes `decide` fail): prove `zpowers g₀ = ⊤`
  via `Subgroup.eq_top_of_card_eq` + `rw [Nat.card_zpowers, orderOf_lemma, <subgroup-def>,
  Nat.card_eq_fintype_card]; decide`, then `Subgroup.mem_top`.

For the unit: `zeta3 := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / 3)) (Complex.exp_ne_zero _)`;
`ζ³ = 1` by `Units.ext` then `← Complex.exp_nat_mul` + `Complex.exp_two_pi_mul_I` (push the `(3:ℕ)`
cast through with `push_cast; ring` inside a `show`); `orderOf ζ ∣ orderOf g₀` from
`orderOf_dvd_of_pow_eq_one`. Package `ℂ_ε := FDRep.of (charRep χ)`; simplicity is free from the
existing `charRep_simple`.

#### §5.11 `S₃` induced-rep decompositions — DONE (#5248, all four sorry-free)

All four `Ind_H^G (1-dim char) ≅ ⊞ irreps` are proved in `Discussion5_11_examples.lean` via
Frobenius reciprocity (`Etingof.Theorem5_10_1`), **not** the still-`sorry` `Theorem5_9_1`. The
route fits in one session and the pieces are reusable for any small-group induced-rep decomposition:
- `finrank_hom_symm` (`dim Hom(V,W)=dim Hom(W,V)` via the symmetric scalar product) — lets you flip
  `finrank (S ⟶ Ind_H ρ)` to `finrank (Ind_H ρ ⟶ S)` so the categorical Frobenius (Ind on the left)
  applies, then feed `Etingof.iso_of_forall_finrank_hom_eq` (needs `S ⟶ -`).
- `frobenius_finrank`: the FDRep↔Rep bridge `dim Hom_{S₃}(Ind_H ρ,S)=dim Hom_H(ρ,Res_H S)`. The
  feared plumbing was a non-issue — **all object identifications are `rfl`**:
  `(forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of (Representation.ind H.subtype ρ)) = Rep.ind
  H.subtype (Rep.of ρ) := rfl` (because `Definition5_8_1 = Representation.ind`, `Rep.ind = Rep.of ∘
  .ind`, and `forget₂_ρ`/carrier are defeq). Cross via `FDRep.forget₂HomLinearEquiv`, apply
  `Rep.indResHomEquiv`, return; `Res_H S := (Action.res (FGModuleCat ℂ) H.subtype).obj S` with
  `((Action.res _ f).obj S).ρ h = S.ρ (f h)` (`rfl`).
- completeness `S3_simple_iso` from `exists_simples_sum_finrank_sq_eq_card` + the `1²+1²+2²=6` count.
- `ind_finrank_eq_scalar` = multiplicity as `⅟|H| • ∑_{h:↥H} S.character ↑h * (charRep χ).character h⁻¹`
  (`FDRep.scalar_product_char_eq_finrank_equivariant`), then `sum_cyclic` (enumerate `↥H` via
  `finEquivZPowers`) reduces to a `Fin n` sum you evaluate at the conjugacy-class reps.
Finish each theorem with `iso_of_forall_finrank_hom_eq`, casing `S` over the catalogue:
LHS multiplicity from the scalar product, RHS from `FDRep.finrank_hom_simple_simple` + `finrank_hom_biprod`.

Four gotchas that each cost a build cycle (watch for the analogues in any finite-group character work):
1. **Concrete subgroups you need `Fintype`/`Invertible` instances on must be `abbrev`, not `def`.**
   `def Z2 : Subgroup S3 := …` makes `↥Z2` opaque, so `Fintype ↥Z2` / `Invertible (card:ℂ)` fail to
   synthesize at *statement* elaboration (the lemma won't even state). `abbrev` lets resolution see
   through. (Switching `def`→`abbrev` then breaks any `rw [Z2]` — drop them; the abbrev unfolds
   definitionally so `Nat.card_zpowers`/`mem_alternatingGroup` apply directly.)
2. **`decide` on `Fintype.card ↥(Subgroup.zpowers g)` gets STUCK** (the Fintype routes through a
   noncomputable `Classical.decPred`). Route the card through order instead:
   `rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, <orderOf g = n>]`. (`decide` *does* work for
   `Fintype.card ↥(alternatingGroup (Fin 3))` — only the `zpowers` Fintype is classical.)
3. **Under `open CategoryTheory`, bare `finrank_hom_simple_simple` resolves to the
   `CategoryTheory` version** (which takes `k` as the first *explicit* arg), giving a baffling
   `failed to synthesize Field ↑S.V`. Write `FDRep.finrank_hom_simple_simple S W` explicitly.
4. **`⅟c • x = ↑m` arithmetic**: don't `rw` the card inside `⅟` (the `Invertible` instance is keyed
   on the old term). Use `invOf_smul_eq_iff` (`⅟c • x = y ↔ x = c • y`) to clear the `⅟` first,
   then `rw [<card lemma>, smul_eq_mul]; norm_num` (or `linear_combination` for the cube-root case).
For `ℂ_ε`: `zeta3_primitive : IsPrimitiveRoot (zeta3:ℂ) 3` via `Complex.isPrimitiveRoot_exp 3`
(`rw [show (3:ℂ)=((3:ℕ):ℂ) by norm_num]; exact h` to reconcile `/3` vs `/↑3`), then
`IsPrimitiveRoot.geom_sum_eq_zero` gives `ζ²+ζ+1=0`; `ζ⁻¹=ζ²`, `(ζ²)⁻¹=ζ` via
`inv_eq_of_mul_eq_one_right` + `ζ³=1`. Don't reach for `charEq_iso` here: it needs the induced
character, exactly what the Frobenius route avoids.

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

**Before accepting an import-cycle issue's prescribed heavy refactor, measure exactly which symbols cross the polluted edge — the real fix is often one or two relocations, not the re-routing the issue fears.** An issue framed as "this needs the whole X machinery re-routed through clean files, too big for one session, decompose into (a)+(b)" can collapse once you check *what the consumer actually uses from the polluted import*. For each polluted `import P` in file `F`: list `P`'s declarations (`grep -oE '^(noncomputable def|def|theorem|lemma|abbrev) \w+' P.lean`), then `grep -nowFf` that list against `F.lean` to see the handful of names `F` truly consumes. If those names are clean (their own proofs reach no polluted module — check with the per-symbol trace, not the file's), extract just them into a leaf file and rewire `F` to import it; `P` re-imports the leaf so its other consumers are unaffected (same namespace ⇒ no qualified-name breakage). Then **simulate the whole rewired DAG in Python before editing** (apply the import swaps to the `imports` dict, recompute closures, run a colour-DFS cycle check, and also simulate the eventual downstream assembly's imports) — confirm 0 cycles and `DetInvElim`-free closures up front, so the build is a formality. (#5108: the issue prescribed re-routing the SchurWeyl character machinery [its part (b)]; in fact `CauchyCharDiff` used `Proposition5_22_2` only for `schurPoly_shift` and `CauchyDetQuotientGrading` used `PolynomialGLDecomposition` only for `asModuleHomOfIntertwiner` — two clean-symbol extractions [`SchurPolyShift.lean`, `RepresentationAsModuleHom.lean`] cleared all four ingredient files in one session.)

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
   - **> 1600000**: Refactor the proof. Extract helper lemmas, precompute intermediate results, or split the finite check into smaller pieces. **NEVER reach for `native_decide`** — it is FORBIDDEN in this project (an unverified trust hole outside the kernel; see "FORBIDDEN: `native_decide`" below). If a finite check is too slow for honest `decide`, that is a signal to find a real proof, not a bigger hammer.
   - **Placement:** `set_option ... in` lines must come *before* the `/-- ... -/` docstring (the docstring must sit immediately above `theorem`/`def`). Putting the docstring first gives `unexpected token 'set_option'; expected 'lemma'`. **The same constraint applies to `omit [Inst] in`** (used to silence the `unusedSectionVars` linter when a section instance like `[Fintype ι]`/`[∀ i, Module.Finite ...]` is genuinely unused by a lemma): it must precede the docstring, else `unexpected token 'omit'; expected 'lemma'`. Note the linter reports unused instances *one at a time* — after omitting the flagged ones it may flag a further instance (e.g. `Module.Finite` once `Fintype`/`DecidableEq` are omitted), so expect to extend the `omit` list across a build cycle or two.
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

### Conjugate / restricted-scalars module synonyms (Ch4 #5182)

To build a "twisted scalar action" vector space — e.g. the **conjugate**
representation `V̄` (same `V`, same `G`-action, scalar `z • v = z̄ • v`) — use a
**non-reducible** type synonym so instances don't leak from the original:

```lean
def Conjugate (V : Type u) : Type u := V                       -- NOT abbrev/@[reducible]
instance : AddCommGroup (Conjugate V) := inferInstanceAs (AddCommGroup V)
noncomputable instance : Module ℂ (Conjugate V) := Module.compHom V (starRingEnd ℂ)
```

`Module.compHom M f` (`f : S →+* R`, needs `[Module R M]`) gives `Module S M` with
`s • m = f s • m`. Two gotchas that cost build cycles:

1. **The `smul_def` reduction lemma is `rfl` — but only with `show V from v`, NOT
   `(v : V)`.** `lemma smul_def (z) (v : Conjugate V) : z • v = (starRingEnd ℂ) z •
   (show V from v) := rfl` works. Writing `(v : V)` instead makes the RHS `•`
   re-resolve to the *conjugate* instance (`Conjugate V` is defeq `V`, so the
   ascription doesn't pin the underlying-`V` action), which loops `simp [smul_def]`
   to "maximum recursion depth" and leaves `smul_add _ _ _` unable to synthesize
   `DistribSMul ℂ (Conjugate V)`. `show V from v` (`have this := v; this`) forces the
   underlying-`V` action. (Do NOT hand-roll the `Module` axioms via `SMul` +
   manual fields — `compHom` already discharges them; you only need `smul_def`.)
2. **A `ℂ`-linear map lifts unchanged to the conjugate space.** `ρ g : V →ₗ[ℂ] V`
   is automatically `ℂ`-linear `Conjugate V →ₗ[ℂ] Conjugate V`; prove its
   `map_smul'` by `simp only [RingHom.id_apply, Conjugate.smul_def, map_smul]`.
   Likewise a conjugate-**linear** equiv `V ≃ₛₗ[starRingEnd ℂ] W` becomes a genuine
   `ℂ`-linear equiv `Conjugate V ≃ₗ[ℂ] W`: build the `LinearEquiv` reusing the
   semilinear one's `toFun/invFun/left_inv/right_inv`, and discharge `map_smul'` via
   `rw [Conjugate.smul_def, map_smulₛₗ]; simp` (the `starRingEnd (starRingEnd r) = r`
   collapse). This is how `V̄ ≅ V*` reuses Theorem 4.6.2's nondegenerate
   `innerEquivDual` (de-privatize it rather than duplicating the surjectivity proof).

### Building a custom structure on a `Prod`/`Fin → k` type synonym: `Prod.fst_add` won't fire — add `rfl` projection lemmas (Ch2 #5362)

When constructing a concrete Lie algebra / representation on a non-reducible synonym
`def Heisenberg k := k × k × k` (with `AddCommGroup`/`Module` via `inferInstanceAs`) and adding
your own `Bracket`/`LieRing`, the proofs of the algebra axioms (`add_lie`, `lie_smul`, …) reduce
to component identities — but **the generic `Prod.fst_add`/`Prod.snd_add`/`Prod.smul_fst` simp
lemmas do NOT match**, because the synonym's `+`/`•` resolve through *its own* (defeq but not
syntactic) instance head, not `Prod.instAdd`/`Prod.instSMul`. Symptom: after `simp only [bracket_def,
Prod.fst_add, …]` the goal still shows an un-reduced `((0,0,A) + (0,0,B)).1` (or `(x+y).2.1`), and
the following `ring` fails treating it as an opaque atom. Fix: state the projections as your own
`@[simp]`-`rfl` lemmas over the synonym and use *those* —
```lean
@[simp] theorem add_fst (a b : Heisenberg k) : (a + b).1 = a.1 + b.1 := rfl   -- + snd_fst/snd_snd
@[simp] theorem zero_fst : (0 : Heisenberg k).1 = 0 := rfl                     -- + the others
@[simp] theorem smul_fst (t : k) (a : Heisenberg k) : (t • a).1 = t • a.1 := rfl
```
then `apply <your @[ext] lemma> <;> simp only [bracket_def, add_fst, …, smul_eq_mul] <;> ring`. Two
companions: (i) a non-reducible `def` (not `abbrev`) keeps the `Bracket`/`LieRing` instances from
leaking onto bare `k × k × k` project-wide — worth the extra `rfl` lemmas. (ii) `0 : synonym` is
*not* rewritten to a constructor triple by `simp`, so a goal `(0,0,0) = 0` needs your `@[ext]`
lemma (which splits to the `zero_fst` projections), not bare `simp`. For the genuine content
(e.g. the U(ℋ) Heisenberg relations `YX−XY=C`, …), map the Lie brackets into the enveloping algebra
via `LieHom.map_lie` + `LieRing.of_associative_ring_bracket` (the associative bracket `⁅a,b⁆=a*b−b*a`);
these relations are specific to the presentation and so genuinely non-vacuous. A noncommutative
quotient like the Weyl algebra `U(ℋ)/(c−1)` needs `RingCon` (`TwoSidedIdeal.span {…}.ringCon`,
`RingCon.mk'`, `RingCon.eq`, `TwoSidedIdeal.rel_iff`/`subset_span`), **not** `Ideal.Quotient`
(commutative-only). Worked, axiom-clean in `Chapter2/Example2_9_13.lean`.

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
- **Transporting an existential across a subalgebra equality `h : centralizer A
  = B`: `rw [← h]` the whole goal, do NOT `h ▸` each binder (Ch5, #5383).** When
  the target is `∃ … (Module B Lᵢ) … (IsSimpleModule B Lᵢ) … (Lᵢ ≃ₗ[B] Lⱼ → …) …`
  but every canonical datum lives over `centralizer A` (`centralizerModuleHom`,
  `hL_simp` from `..._bimodule_decomposition_explicit`, `multiplicitySpace_Cdistinct`),
  filling the binders with `h ▸ inferInstance` / `h ▸ hL_simp i` desyncs the
  instances: later `IsSimpleModule`/`≃ₗ` binders expect the *transported* `Module B`
  instance while your term carries the canonical one (type-mismatch on the instance
  argument). Instead `rw [← h]` once at the top so the whole goal is back over
  `centralizer A`, then `refine` with the canonical `inferInstance` / `hL_simp` /
  `multiplicitySpace_Cdistinct … ⟨f⟩` directly. Single-binder `h ▸` (as in
  `Theorem5_18_4_bimodule_decomposition`) is fine; *multiple interdependent
  binders* are what break. See `SchurWeylBimoduleFull.lean`.
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
  **Same fix for a `let`-heavy finite-family dedup/choice proof over a CONCRETE
  `Sum.elim` family** (Ch5 #5100, the clean constituent extractor): assembling
  `{L} ∪ {W j} ∪ {V ν}` as `R := Sum.elim … (Sum.elim …)` and then running the
  dedup-by-character machinery (`Finset.image`/`choose pick`/`Rep := fun w => R
  (pick w)`/engine call) *inline* hit a genuine `(deterministic) timeout at whnf`
  that did **not** clear even at `maxHeartbeats 6400000` — the `isDefEq` checks
  (`Rep w = R (pick w)`, `χ (pick w) = formalCharacter (Rep w)`, the engine's
  unification against the concrete `FDRep` carriers) loop while reducing `R`
  through `Sum.elim` + `FDRep`/`FGModuleCat` coercions. Fix: extract the entire
  dedup step into a standalone lemma quantified over an **abstract** `R : ι →
  FDRep` (conclusion a plain `∑ i ∈ univ.filter (char (R i) = w), a i = 0`); its
  body type-checks once with `R` opaque (no `Sum.elim` to reduce), and the caller
  applies it to the concrete family in one line. After extraction the main theorem
  compiled at the **default** budget. Heuristic: a `whnf` timeout that survives a
  6.4M bump is a defeq *loop*, not a budget shortfall — relocate the offending
  reduction behind an abstract parameter rather than raising heartbeats.

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

### Char-equality ⟹ iso, and FDRep semisimple-classification toolkit (Ch5 #5247)

`Etingof.charEq_iso` (`Chapter5/CharEqIso.lean`) is **done and sorry-free**: for
`V W : FDRep ℂ G` (finite `G`), `V.character = W.character → Nonempty (V ≅ W)`,
the converse of `FDRep.char_iso`. **Use it, don't rebuild it** when a character
identity needs upgrading to an isomorphism (e.g. induced-rep decompositions).

**Permutation- and sub-representation characters (Ch5 §5.11 `stdRep`, #5263).** To
get a permutation rep's character: `permRep g = ((g⁻¹).permMatrix ℂ).toLin'`
(`Matrix.permMatrix_mulVec` + `Matrix.toLin'_apply`), then
`LinearMap.trace … = Matrix.trace … = (Function.fixedPoints g⁻¹).ncard` via
`Matrix.trace_toLin'_eq` + `Matrix.trace_permutation` — i.e. `χ(g) = #fix(g)`. For
the character of an *invariant subspace* (e.g. the standard rep as the sum-zero
`stdSub`), split the trace over an internal direct sum with its complement:
`LinearMap.trace_eq_sum_trace_restrict` (needs `DirectSum.IsInternal N`, obtained for
a two-element family via `DirectSum.isInternal_submodule_iff_isCompl` +
`Submodule.isCompl_iff_disjoint`); the complementary trivial line contributes trace
`1`, giving `χ_std(g) = #fix(g) − 1`. The `Subrepresentation.toRepresentation g`
restriction is *defeq* to the `(permRep g).restrict _` term the trace lemma produces
(proof-irrelevant `MapsTo`), so the sub-character matches by `change`. For simplicity
via `FDRep.simple_iff_char_is_norm_one`, convert `∑_g χ(g)χ(g⁻¹)` to an **integer**
`Finset` sum (`fixCard g := (univ.filter (g · = ·)).card`, `push_cast`) and close with
`decide` — `Set.ncard`/`Function.fixedPoints` are noncomputable, so always bridge to a
`Finset.filter` cardinality first. Pitfall: `linarith` does **not** work over `ℂ`
(unordered) — use `eq_sub_iff_add_eq` / `linear_combination`. Lemmas in
`Chapter5/Discussion5_11_examples.lean`: `permRep_eq_toLin'`, `trace_permRep`,
`stdRep_character`, `stdRep_simple`.

Two lessons that cost ~hours of deliberation here:

1. **For FDRep iso-from-invariants, do the induction *inside* `FDRep`, not via
   `asModule` decomposition.** The categorical route reuses Mathlib's
   `finrank_hom_simple_simple` and `scalar_product_char_eq_finrank_equivariant`
   *directly* with zero `Representation.asModule`/`Rep ≌ ModuleCat k[G]` bridges
   (which the module route needs in both directions, plus a module-level Schur).
   Pattern: strong induction on `finrank ℂ (V : Type)`; peel a simple subobject
   `S₀ ↪ V` via `CategoryTheory.exists_simple_subobject` (needs
   `IsArtinianObject V`); it splits (`IsSplitMono` from `Injective S₀`, the
   `FinGroupCharZero` instance, retraction `Injective.factorThru (𝟙 S₀) ι`); then
   `splitSummand` gives `V ≅ S₀ ⊞ Q` and you match `Q` by induction. The
   character hypothesis enters only once, via `finrank_hom_eq_of_character_eq`
   (`= finrank ℂ (S ⟶ V)` for every `S`).

2. **`IsArtinianObject (FDRep ℂ G)` is the one genuinely-missing Mathlib fact, and
   it is provable in ~30 lines** (`instIsArtinianObjectFDRep`, now an instance):
   give the subobject lattice the strictly-monotone `ℕ`-length `len s = finrank ℂ
   (s : FDRep ℂ G)`, then `WellFoundedLT` via `Subrelation.wf` + `InvImage.wf …
   wellFounded_lt` + `isArtinianObject_iff_not_strictAnti`. Strict monotonicity:
   `a ≤ b` ⟹ `Subobject.ofLE a b h` mono ⟹ underlying linear map injective ⟹
   `finrank ≤`; equality forces the underlying map bijective ⟹ an underlying
   ModuleCat iso that the forgetful functor **reflects**, giving `a = b`. The
   load-bearing forgetful is `Action.forget (FGModuleCat ℂ) G ⋙ forget₂
   (FGModuleCat ℂ) (ModuleCat ℂ)` — it (a) preserves monos, (b) reflects isos, (c)
   has `Fwd.obj X` underlying-defeq to `(X : Type)`, and (d) gives
   `PreservesBinaryBiproduct` via `preservesBinaryBiproduct_of_preservesBinaryProduct`.
   **Gotcha:** `forget₂ (FDRep ℂ G) (FGModuleCat ℂ)` does *not* auto-resolve
   `Mono`/`ReflectsIsomorphisms`/`Subsingleton`-of-obj the way `Action.forget`
   does — use `Action.forget`, not `forget₂`, as the first leg.

Other reusable sorry-free lemmas now in that file: `finrank_biprod_obj`
(`finrank ℂ (A ⊞ B) = finrank A + finrank B`), `finrank_hom_biprod`
(hom-space additivity, via a hand-built `homBiprodEquiv : (S ⟶ A ⊞ B) ≃ₗ[ℂ] (S ⟶
A) × (S ⟶ B)`), `splitSummand` (split mono ⟹ `Y ≅ X ⊞ cokernel`, via
`isBilimitBinaryBiconeOfIsSplitMonoOfCokernel … |>.isLimit.conePointUniqueUpToIso
(BinaryBiproduct.isLimit …)`), `homCongrRight` (post-compose iso ⟹ hom-space
`≃ₗ`), and `isZero_of_finrank_eq_zero`.

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

### Categorical biproducts / progenerators (Ch9 §9.7, #5146)

Building biproduct-based constructions in an abstract abelian category (the §9.7
progenerator classification `multBiproduct P n = ⨁_{p : Σ i, Fin (n i)} P p.1` in
`Introduction_9_7.lean`) hits three non-obvious instance facts:

- **`Projective (⨁ g)` requires the index family in `Type v` (the hom universe), not an
  arbitrary `Type w`.** Mathlib's instance is `{β : Type v} (g : β → C) [HasBiproduct g]
  [∀ b, Projective (g b)] : Projective (⨁ g)`. A family indexed by `ι : Type w` with `w ≠
  v` fails with `failed to synthesize Projective (⨁ ...)` (cost one build cycle). Fix:
  constrain `ι : Type v` (matching `Category.{v}`). The finite-index Fintype `Σ i, Fin
  (n i)` then also lands in `Type v`. `HasBiproduct` itself is fine over any `Finite`
  index, so only the `Projective`/`Injective` biproduct instances force `Type v`.
- **`HasFiniteBiproducts C` is NOT a global instance from `Abelian C`** (it is a
  *theorem* `Abelian.hasFiniteBiproducts`, kept non-instance for performance). A `def`
  whose statement mentions `⨁` needs it; add `[HasFiniteBiproducts C]` as an explicit
  binder (callers in an abelian category discharge it with `haveI :=
  Abelian.hasFiniteBiproducts`). The biproduct of a `Finite`-indexed family then resolves
  via `hasBiproductsOfShape_finite`.
- **The "indecomposable object" predicate is `CategoryTheory.Indecomposable`** (defined in
  `Shapes/BinaryBiproducts.lean` *after* `end Limits`, so it lives in `CategoryTheory`,
  not `CategoryTheory.Limits`): `¬IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z`,
  needs `[HasBinaryBiproducts C]`.

Two reusable helpers landed for the Krull–Schmidt *existence* link
(`KrullSchmidt/Existence.lean`, #5206 — uniqueness/§9.7-assembly links will want both):
- **`clength` is an iso-invariant** (`clength_eq_of_iso (e : X ≅ Y)`): `Subobject.mapIsoToOrderIso
  e : Subobject X ≃o Subobject Y`, then `Order.height_orderIso` + `OrderIso.map_top` give equal
  heights. Needed so a well-founded induction measure descends across a splitting iso `X ≅ Y ⊞ Z`.
- **No Mathlib lemma for a biproduct over a `Sum`** (`⨁ (Sum.elim f₁ f₂) ≅ (⨁ f₁) ⊞ (⨁ f₂)`).
  Build it explicitly: `hom := biprod.desc (biproduct.desc fun a => ι _ (.inl a)) (biproduct.desc
  fun b => ι _ (.inr b))`, `inv := biproduct.desc fun k => match k with | .inl a => ι f₁ a ≫
  biprod.inl | .inr b => ι f₂ b ≫ biprod.inr`; both `*_id` close by `biprod.hom_ext'`/
  `biproduct.hom_ext'` + `rintro (a|b) <;> simp`. This is the step that concatenates two finite
  indecomposable families over `κ₁ ⊕ κ₂`.
- **`∃ (_ : Fintype κ) (f : κ → C), … ⨁ f` elaborates** because a `Sum`/`Exists`-bound hypothesis
  of class type *is* a local instance, so `⨁ f` resolves inside the binder. But after `refine ⟨κ,
  fin, f, …⟩` the supplied `fin` is **not** auto-registered for the remaining goals — add `haveI :=
  fin` before referencing `⨁ f`/`biproduct.ι f` again, or `HasBiproduct f` fails.

**Krull–Schmidt *uniqueness* (`krullSchmidt_unique`, #5480) — the two heavy categorical
ingredients are ALREADY in Mathlib; don't hand-bash them.** Before reimplementing biproduct
matrix algebra, reach for:
- **Cancellation = `CategoryTheory.Biprod.isoElim`** (`Preadditive/Biproducts.lean`): given
  `f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` with `[IsIso (biprod.inl ≫ f.hom ≫ biprod.fst)]` (top-left entry
  invertible), it produces `X₂ ≅ Y₂` by Gaussian elimination. This is the whole Schur-complement
  cancellation — the feared ~hundreds-of-lines step. Sibling `Biprod.gaussian`/`unipotentUpper`/
  `unipotentLower`/`isoElim'` for the component-level forms.
- **Peeling one summand off `⨁ g`** uses `biproduct.toSubtype g p` / `biproduct.fromSubtype g p`
  (`Limits/Shapes/Biproducts.lean`), with `Subtype.restrict p g = fun i' => g i'.val` as the
  sub-biproduct index. They are *definitionally* `biproduct.lift (fun _ => π …)` /
  `biproduct.desc (fun j => ι _ j.val)`, and crucially `biproduct.fromSubtype_toSubtype = 𝟙`,
  `toSubtype_fromSubtype = biproduct.map …`, plus simp lemmas `ι_toSubtype`/`fromSubtype_π`
  (dite on `p j`). So `peelIso g i₀ : ⨁ g ≅ g i₀ ⊞ ⨁ Subtype.restrict (· ≠ i₀) g` is built with
  `hom := biprod.lift (π g i₀) (toSubtype g (·≠i₀))`, `inv := biprod.desc (ι g i₀) (fromSubtype …)`
  and the iso laws close by `biprod.hom_ext'`+`biprod.hom_ext`+`simp` (the inr-snd corner is
  exactly `fromSubtype_toSubtype`). State the codomain with `Subtype.restrict` (NOT
  `fun i' => g i'.val`) so that corner's `𝟙` matches syntactically. Pin the top-left entry of the
  peeled iso to a chosen component with `@[reassoc (attr := simp)]` `peelIso_inv_inl`/`hom_fst`.
- To find the matching `m₀` whose component is *iso* (not just "some iso exists"), reuse the local
  endomorphism-ring sum argument of the exchange lemma but conclude `IsIso (s ≫ biproduct.π Z m₀)`
  (the `⟨⟨rr, hαrr, he1⟩⟩` already proves the component is the iso). Assemble the reindexing
  `κ ≃ μ` from `Equiv.sumCompl (· = k₀)`/`sumCongr`; `sumCompl_symm_apply_of_pos/neg` need the
  predicate pinned (`(p := (· = k))`) — bare `rfl` leaves `p` as `Eq ?m` and the rewrite fails.

Useful idioms from the same file: realise `⨁ P` as a *retract* of `multBiproduct P n`
(when each `n_i ≥ 1`) via a diagonal index inclusion `e i = ⟨i, 0⟩`, `s := biproduct.desc
(fun i => biproduct.ι _ (e i))`, `r := biproduct.lift (fun i => biproduct.π _ (e i))`;
`s ≫ r = 𝟙` by `biproduct.hom_ext'` + `biproduct.hom_ext` then `biproduct.ι_desc`/`lift_π`
and `biproduct.ι_π` (the `dif_pos rfl`/`dif_neg (fun h => …(he h))` dite split, with
`he : Function.Injective e`). A split epi `r` (`IsSplitEpi r := ⟨⟨s, key⟩⟩`) pulls back
generating epis; `biproduct.mapIso (fun _ => e)` transports a progenerator across an iso
of each summand. Krull–Schmidt (the *forward* "every progenerator is `⊕ n_i P_i`"
direction) is not in Mathlib — isolate it as one documented `sorry` (#5153).

**`finrank` of a biproduct Hom space (Ch9 §9.7 Cartan formula, #5144).** To prove
`dim_k Hom(⊕ⱼ fⱼ, ⊕ₖ gₖ) = ∑ⱼ ∑ₖ dim_k Hom(fⱼ, gₖ)` (e.g. `dim B_𝐧 = ∑ c_{ij} n_i n_j`
for `B_𝐧 = (End (multBiproduct P n))ᵐᵒᵖ`): Mathlib's `biproduct.matrixEquiv`
(`(⨁ f ⟶ ⨁ g) ≃ ∀ j k, f j ⟶ g k`) exists but is a bare `Equiv` **restricted to
`Type 0` index types** (`{J K : Type} [Finite J] [Finite K]`), so it does *not* apply when
the biproduct index is `Σ i, Fin (n i) : Type v` (multBiproduct's index lives in the hom
universe). Build your own *universe-polymorphic* `≃ₗ[k]` instead: `toFun m j l :=
biproduct.ι f j ≫ m ≫ biproduct.π g l` (k-linear by `Linear.comp_smul`/`Linear.smul_comp`
and `Preadditive.comp_add`/`add_comp`), `invFun M := biproduct.desc fun j => biproduct.lift
fun l => M j l`; `left_inv`/`right_inv` close by `biproduct.hom_ext'` + `biproduct.hom_ext`
then `simp` (`biproduct.ι_desc`/`lift_π`). Then `e.finrank_eq` + `Module.finrank_pi_fintype k`
(applied twice for the nested Pi) gives additivity — `Module.Free` is free over a field
(`Module.Free.of_divisionRing`, a global instance), `Module.Finite` from the §9.6
Hom-finiteness (`IsFiniteAbelianCategoryOverField.finiteDimensional_hom`). For the
opposite-algebra step `dim (End P)ᵐᵒᵖ = dim End P` use `MulOpposite.opLinearEquiv k`. Collapse
the double sum over `Σ i, Fin (n i)` with `← Finset.univ_sigma_univ` + `Finset.sum_sigma`
(the inner `Fin (n i)` sum is constant, so `Finset.sum_const` + `Fintype.card_fin` gives the
`n_i` weight). **Gotcha:** when re-declaring section instance binders in a `def`/`theorem` to
make one argument explicit (e.g. `def cartanEntry (k) … {C} [Category C] [Linear k C]`),
include `[Preadditive C]` *before* `[Linear k C]` — `Linear` takes `Preadditive` as a
parameter (does not extend it), so omitting it gives `failed to synthesize Preadditive C`.

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
| `p` splits over its field | `p.Splits (RingHom.id k)` | `p.Splits` | **`Polynomial.Splits` is now single-argument** (`Splits (f : k[X]) : Prop`, splits over `k` itself). The ring-hom form is deprecated; `p.Splits (RingHom.id k)` fails to elaborate ("Function expected at p.Splits"). Use `IsAlgClosed.splits p : p.Splits` (not `splits_codomain`), and `Splits.eq_prod_roots_of_monic (hf : p.Splits) hm : p = (p.roots.map (X - C ·)).prod`. (#5235) |
| Integer induction case names | `\| hz \| hp \| hn` | `\| zero \| succ \| pred` | `induction n using Int.induction_on with` alternatives are `zero` (`P 0`), `succ k ih` (`P k → P (k+1)`, `k : ℕ` cast to `ℤ`), `pred k ih` (`P (-k) → P (-k-1)`). Using `hz/hp/hn` gives "Invalid alternative name". (#5365) |

**Combining `↑(q ^ a)` Units.val / zpow scalars in a `↑(q^a) * (↑(q^b) * c) = …` goal (quantum-torus / twisted-cocycle arithmetic, #5365).** Don't guess `rw` order on a mix of `Units.val`, `•`/`*`, and `zpow`. Normalize *both* sides to a single `↑(q ^ E) * c` first with `simp only [smul_eq_mul, ← mul_assoc, ← Units.val_mul]` (collapses each side's two unit factors into one `↑(q^a * q^b)`), then discharge with pre-proved unit-level equalities `have : (q ^ a * q ^ b : kˣ) = q ^ E := by rw [← zpow_add]; congr 1; ring` and `rw [hL, hR]`. `ring` does **not** equate `q ^ A` with `q ^ B` for equal `ℤ`-exponents — you must combine to one `zpow` (`← zpow_add`) and prove the exponent equality separately.

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

**When to use:** The statement involves only `Fin n` for small `n`, concrete matrices, or specific permutations. If `decide` doesn't terminate in reasonable time (< 30s), write a **manual proof** — do NOT fall back to `native_decide` (FORBIDDEN, see below).

## FORBIDDEN: `native_decide`

**`native_decide` is banned in this project.** It compiles the goal to native code and trusts the Lean compiler + runtime — it is *outside the kernel*, so every `native_decide` is an unverified assertion (it has had soundness bugs and is exactly the kind of trust hole a formalization exists to avoid). Do not use it, and do not silence its linter with `set_option linter.style.nativeDecide false`. If a finite computation is too slow for honest `decide`, that means: (a) prove it with real lemmas (`Finset.sum`/`Fintype` API, explicit rewrites), or (b) restructure so the heavy part is a one-off `have` over a `decide`-able sub-statement. "It's just a finite check" is not a license — a slow `decide` is a prompt to think, not to escape the kernel.

**Probe `decide` feasibility in an isolated scratch file, never via a full-module `lake build`.** Kernel `decide` has no internal timeout, so an infeasible one hangs (it ate 15 min / 3.3 GB before I killed it). Put the single goal in `/tmp/Scratch.lean` (import the needed modules + `set_option maxRecDepth …`/`maxHeartbeats …`) and run `gtimeout 300 lake env lean /tmp/Scratch.lean` — a self-contained scratch with explicit `set_option`s does not need the lakefile's `[leanOptions]`, so `lake env lean` is fine here. The OS timeout bounds the experiment and tells you the true cost before you touch the real file. Rough scaling from #5425's E-type root counts (filter over `Fin n → Fin B`): ~4k candidates ≈ 50 s with `maxRecDepth 10000` + `maxHeartbeats 4000000`; ~78k candidates → ~7 GB and climbing (impractical); millions → OOM materializing `univ`. When honest `decide` won't scale, decompose with a real-math plan (e.g. a branch-decomposition convolution that factors the count into small per-component `decide`s) rather than keeping `native_decide`.

**Honest `decide` DOES scale to `S₄`-sized character work — measure before assuming you need a class-function decomposition (#5429).** A predecessor assumed the Example 4.8.1 group-order / conjugacy-class / orthonormality computations *required* `native_decide`. In fact, over `Equiv.Perm (Fin 4)` (24 elements) honest `decide` evaluates in ~10s: norm-one character sums `∑ g : Perm (Fin 4), ((fixCard g : ℤ) - 1)^2 = 24` (for `FDRep.simple_iff_char_is_norm_one`), `Fintype.card (ConjClasses (Perm (Fin 4))) = 5` (needs `set_option maxRecDepth 4000` — the default overflows the quotient enumeration), and a `MulAction` spec like `∀ g a, invol (conjIdx g a) = g * invol a * g⁻¹` (the conjugation `S₄→S₃` action, 24×3 cases, `set_option maxHeartbeats 4000000`). `Fintype.card (Perm (Fin n)) = n!` should go through `Fintype.card_perm`/`Fintype.card_fin` then `decide`, NOT a 24-element enumeration. Calibration: **honest `decide` also scales to the `A₅` regime — measured in #5430, the predicted "too slow, use a class-function decomposition" was wrong, do NOT build a class-sum helper preemptively.** Over `alternatingGroup (Fin 5)` (60 elements, `Fin 5` perms), with `set_option maxRecDepth 8000` + `maxHeartbeats 4000000`, the following all `decide` in well under a minute each: norm-one sums `∑ g : G, ((fixCardM g : ℤ) − 1)^2 = 60` for `ℂ⁴`/`ℂ⁵` simplicity; `Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5` (~34 s); and a 60×6 conjugation-action spec `carrier (conjIdx5 g i) = (carrier i).image (conjPerm g)` (~41 s). For `|A₅|` use `card_alternatingGroup` (`= card α !/2`) + `decide`, NOT a 60-element enumeration. **Always probe the exact goal in a scratch file first** (`gtimeout 300 lake env lean /tmp/Scratch.lean`) — measuring took minutes and saved building an unnecessary conjugacy-class-sum helper. The reusable genuine-rep infrastructure — a generic deleted-permutation representation of any `MulAction G α` (`permRepM`/`stdSubM`/`stdRepM`) with character `#fix(g) − 1` and norm-one simplicity — lives in `Chapter4/Example4_8_1.lean` (namespace `Etingof.Example4_8_1.S4`); it is reused for `A₅`'s `ℂ⁴` (deleted natural action on `Fin 5`) and `ℂ⁵` (deleted permutation rep on the six Sylow-5 subgroups, via a conjugation `MulAction G (Fin 6)` whose closure is certified by honest `decide`) in namespace `Etingof.Example4_8_1.A5` (#5430). For elements of `alternatingGroup (Fin 5)`, build them as `⟨perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩` — bare `⟨perm, by decide⟩` fails to synthesize `Decidable (perm ∈ G)`. When stacking `set_option maxRecDepth … in` with `maxHeartbeats … in`, put `maxHeartbeats` **last** so the linter's required explanatory comment sits immediately under it.

## FORBIDDEN: vacuous "certificate" statements for tables / classifications

A **character table, multiplicity table, or classification claim is NOT formalized by encoding the numbers as a hand-typed matrix and proving an orthonormality / count / `∑dᵢ²=|G|` certificate.** Those properties are *necessary but radically insufficient*: a continuum of orthonormal bases of class functions satisfy them, so the certificate never pins down *the* character table, and it never connects the numbers to any representation. Such a "fix" is vacuous (the real claim survives only in the docstring). The required bar: **exhibit the actual representations and prove each table row is the character (trace) of its representation** — or state a decidable `IsCharacterTable G T` predicate that is provably unique up to row reordering and prove the table satisfies it (which forces the representation connection). If the genuine construction is hard (e.g. A₅'s 3-dim icosahedral reps over ℚ(√5)), land a real partial and decompose the rest — never ship the orthonormality certificate as the whole theorem.

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

## Hand-built codiscrete categories: discharge coherence with `rfl`, not `Subsingleton.elim`

When constructing a small category by hand with singleton hom-sets
(`Hom _ _ := PUnit`, `id _ := ⟨⟩`, `comp _ _ := ⟨⟩` — the codiscrete category, useful for
the toy `C₁`/`C₂` of Ch7 §7.4), every law/naturality/coherence equation is an equality of
`PUnit`-valued morphisms and closes by **`rfl`** via structure eta. Do **not** reach for
`Subsingleton.elim _ _`: `Subsingleton (X ⟶ Y)` fails to synthesize because `⟶` does not
reduce to `PUnit` through the `Category` instance at instance-resolution transparency
(cost one build cycle in #5138). So `NatIso.ofComponents (fun _ => …) (fun _ => rfl)` and
`functor_unitIso_comp _ := rfl` work where the `Subsingleton` forms don't. The `Category`
structure's `id_comp`/`comp_id`/`assoc` fields can simply be omitted (their `by aesop_cat`
defaults close trivially). For an equivalence `C₁ ≌ C₂` of two such categories, build it
with `Equivalence.mk`-style fields and per-object isos `Iso.mk ⟨⟩ ⟨⟩` (or `Iso.refl _`
where the objects are defeq). An equivalence then descends to a bijection of iso-classes
of objects via `Quotient.map e.functor.obj (fun _ _ ⟨f⟩ => ⟨e.functor.mapIso f⟩)` with
`left_inv`/`right_inv` from `e.unitIso`/`e.counitIso` and `Quotient.ind`/`Quotient.sound`
(needs `attribute [local instance] CategoryTheory.isIsomorphicSetoid`); compose with
`Equivalence.congrLeft` to get the iso-class bijection on functor categories `C₁ ⥤ D` vs
`C₂ ⥤ D`.

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
6. **Status tracking lag.** After proving a theorem, update `items.json` immediately in the same commit. Audits have found items marked `scaffolded` that were actually `sorry_free`. Always update proactively — manual tracking in `progress/items.json` is the only status tracking mechanism. **Edit `items.json` surgically (`Edit` on the exact field lines), never rewrite it with `json.dump`/`json.load`+dump** — the reserializer reflows indentation/key-order/unicode and produces a multi-thousand-line diff against the 13k-line shared file (caught only by `git diff --stat`). When changing a `fidelity`/`status` field, `grep -n` the item id, Read those ~15 lines, and `Edit` just the value (and drop any now-stale `fidelity_note`).
7. **FDRep abstraction fighting.** If your proof requires distributing `.hom.hom` over sums or otherwise unwrapping 3+ layers of categorical abstraction, you're fighting the wrong abstraction. See the FDRep Categorical Plumbing patterns above for alternatives.
8. **Universe level mismatches.** Representation theory proofs sometimes need explicit universe annotations (`.{v}`) especially when working with Jacobson radical or maximal ideal APIs. If type unification fails mysteriously, try adding explicit universe parameters.
9. **Sinking entire context windows on known dead-ends.** Before starting a proof, check the "Known Dead-Ends" section above. If the proof requires bridging `ExteriorAlgebra` ↔ `PiTensorProduct` or resolving the `if`-branching diamond, sorry it immediately and move on. Multiple agents have confirmed these are blocked on missing infrastructure.
10. **Opaque placeholder accumulation.** Defining key structures as `sorry : FDRep k G` (e.g., `SchurModule k N lam`) creates downstream dependency chains that block entire proof clusters. When you must sorry a definition, prefer making the carrier type concrete and sorry-ing only specific operations/instances (see "Never sorry a Type" above). Each opaque placeholder blocks all items that depend on it.
11. **Convention mismatch between book and Mathlib.** Sign conventions, ordering conventions, and normalization conventions can silently make statements unprovable. See "Verify Statement Correctness Before Proving" section above. The vandermondePoly sign mismatch wasted multiple agent sessions before being discovered via a concrete n=2 counterexample.
12. **Issue description proof strategies are sometimes wrong.** The proof approach described in an issue body may be mathematically incorrect or only work for special cases. Always spend 10 minutes verifying the described approach before committing to it. See "Issue Description Feasibility Check" section above.
13. **A prior agent's "circular / needs missing theorem" skip can be wrong.** When an issue was already skipped as circular or blocked on a named result "not in the project," do not just re-skip — check whether an existing **off-block / orthogonality / character lemma's diagonal (special) case** already supplies the missing independent input. Concrete example (#2693): the rank-1 Young-symmetrizer fact was twice skipped as "needs primitivity `c_λ k[S_n] c_λ = k·c_λ`, not in project." But the diagonal case of the existing `youngSym_trace_kronecker'` is exactly `trace(c_λ|_S) = α` (an independent `ℂ[S_n]` computation), and `trace(α⁻¹·c_λ|_S) = 1` via `IsProj.trace` gives rank 1 directly — no primitivity, no whole-space trace, no dimension bridge. Pattern: if a proved `..._vanishes_off_block` lemma gives the off-diagonal value (`if h_ne then 0`), its `if_pos rfl` diagonal twin usually gives the special-block value you need. Spend 10 minutes looking for the diagonal twin before re-skipping.
14. **Namespace dot-notation mismatch.** Most Lean files in this project wrap code in `namespace Etingof` (and `noncomputable section`). If you define `def YoungDiagram.foo` inside `namespace Etingof`, the full name is `Etingof.YoungDiagram.foo` — dot notation `μ.foo` (where `μ : YoungDiagram`) will NOT find it. **Symptoms:** The definition silently fails to register (no error reported) and downstream references get "Invalid field" errors. **Fix:** Close the namespace before defining `YoungDiagram.*` declarations that need dot-notation access, then reopen it. Remember to also close/reopen any `noncomputable section`.


### Tactic Gotchas with `rw`, `omega`, and `nsmul`

1. **`rw [← Finset.sum_filter]` fails on lambda matching.** `rw` does strict term matching and often can't unify `fun x => if x ∈ S then f x else 0` with `Finset.sum_filter`'s pattern. Use `simp only [← Finset.sum_filter]` instead — `simp` is more flexible with lambda matching.

2. **`omega` can't see through `Fin` equalities.** After `Fin.val_eq_of_eq`, omega may not recognize the resulting Nat equality. Fix: use `simp only [Fin.mk.injEq] at h` to normalize `⟨a, _⟩ = ⟨b, _⟩` into `a = b` before calling `omega`.

3. **`omega` can't handle `min`/`if` from `List.length_take`.** `List.length_take` gives `(l.take n).length = min n l.length`, and `min` unfolds to `if n ≤ l.length then n else l.length`. omega can't simplify `if`. Fix: extract the bound you need with `lt_of_lt_of_le h (min_le_left a b)` or `min_le_right`.

4. **`nsmul_eq_mul` produces `↑n * x` not `n * x`.** Converting `n • x` (where `n : ℕ`, `x : ℤ`) via `nsmul_eq_mul` gives `↑n * x` with a Nat cast. `linarith` can't equate `↑2 * x` with `(2 : ℤ) * x`. Add `push_cast` after `nsmul_eq_mul` to normalize.

5. **`linarith` requires a linear order — use `linear_combination` over ℂ.** `linarith` only works on linearly ordered types (ℝ, ℤ, ℕ, etc.). For goals over ℂ like `a + b = 0 → a = -b`, use `linear_combination h` instead. The `linear_combination` tactic works over any commutative ring.

6. **sl(2)-triple bracket relations are stated with ℕ-smul — use `nsmul_lie`, not `smul_lie` (Ch2 #5307).** `Sl2Irrep.lie_h_e : ⁅sl2_h, sl2_e⁆ = 2 • sl2_e` and `lie_h_f : ⁅sl2_h, sl2_f⁆ = -(2 • sl2_f)` use **ℕ-smul** (`2 : ℕ`). In a module computation, after `rw [leibniz_lie .., lie_h_f, neg_lie]` you get `-⁅(2:ℕ) • sl2_f, m⁆`; `smul_lie` (the ℂ-scalar lemma) does **not** match the pattern `⁅?t • ?x, ?m⁆`. Use `nsmul_lie : ⁅n • x, m⁆ = n • ⁅x, m⁆`, then `two_nsmul` (or `push_cast`) to turn the resulting `(2:ℕ) • y : M` into something `module` closes. This is the workhorse for the highest-weight ladder (`fIter`/`lie_sl2_h_fIter`/`lie_sl2_e_fIter` in `Problem2_15_1_m_Module.lean`) feeding the #5301 Clebsch–Gordan module-iso assembly.

### Counting solutions / orbits in `ZMod n` where `n` is a *symbolic* modulus (e.g. `q²−1`)

Formalizing a "count the `ν ∈ K^∨` with property P" claim by modelling `K^∨ ≅ ZMod n`
(Ch5 Discussion 5.25.4 / #5169, `Chapter5/Discussion5_25_4.lean`) hits two recurring traps:

1. **`Finset.univ`/`.filter`/`.card` over `ZMod n` needs `Fintype (ZMod n)`, which only
   exists given `[NeZero n]` — and the *statement* elaborates before any in-proof `haveI`.**
   So a `def`/`theorem` whose *type* mentions `Finset.univ : Finset (ZMod (q²−1))` (or any
   `.filter`/`.card` of it) must carry `[NeZero (q ^ 2 - 1)]` as an **instance binder**; you
   cannot derive it inside the proof from a `(hq : 2 ≤ q)` Prop hypothesis (that's too late —
   `Finset.univ` in the signature has already failed to synthesize `Fintype`). Put `[NeZero
   (q ^ 2 - 1)]` on the def and on every theorem referencing it; lower-level lemmas whose
   *statements* avoid `univ` (e.g. an `x.val` divisibility iff) can instead `haveI : NeZero
   … := ⟨by …⟩` internally where they need `ZMod.val_lt`/`natCast_zmod_val`. Callers with a
   concrete `q ≥ 2` discharge the instance trivially; an abstract caller does one `haveI`.

2. **`rw [hfac]` to replace the modulus `n` (e.g. `q²−1 = (q−1)(q+1)`) gives "motive is not
   type correct" whenever a `(x : ZMod n).val` term is in scope** — because `ZMod.val x =
   @ZMod.val n x` has `n` as an *explicit argument*, and `x : ZMod n`, so rewriting `n`
   retypes `x`. **Never rewrite the modulus on a hypothesis/goal containing `.val` of that
   `ZMod`.** Instead rewrite in the *opposite* direction on a term where the product form
   `(q−1)*(q+1)` does **not** overlap the `.val`: e.g. to turn goal `(q+1) ∣ x.val` into
   `(q²−1) ∣ (q−1)*x.val`, do `rw [← mul_dvd_mul_iff_left hq1, ← hfac]` (the `← hfac`
   collapses the freshly-introduced `(q−1)*(q+1)` divisor, leaving `x.val` untouched); to
   prove `(q²−1) ∣ (q−1)*x.val`, build `h2 : (q−1)*(q+1) ∣ (q−1)*x.val` first then `rwa
   [← hfac] at h2`; to bound `x.val < (q−1)*(q+1)`, `rw [← hfac]` then `exact ZMod.val_lt x`.
   The fixed-point count itself is a clean `Finset.card_nbij'` between the fixed set and
   `Finset.range (q−1)` via the multiples-of-`(q+1)` map `k ↦ ((q+1)*k : ZMod n)` (with
   `ZMod.val_natCast_of_lt` for the round-trips); a fixed-point-free involution's orbit count
   is `card/2`, proved by exhibiting a transversal (val-minimal element per pair) and
   `Finset.card_union_of_disjoint` on `moved = reps ∪ reps.image f`.

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

### Degree-bound `Finset.sup` over an `AlgEquiv`-image: two whnf traps (#5486)

When `s` is a uniform degree bound `Finset.univ.sup (… natDegree (E (P …)) …)` for a heavy
algebra-equiv `E` (e.g. `glCoordToPoly : k[Xᵢⱼ,det⁻¹] ≃ₐ Polynomial k[Xᵢⱼ]`), two separate
`(deterministic) timeout at whnf`/`isDefEq` traps appear, *both* because Lean eagerly
whnf-reduces `E` (the AlgEquiv `trans`/FunLike coercion) when a defeq check stalls. Symptom:
the timeout is reported at the **enclosing `theorem`/docstring line** (col 0), not the real
tactic — bisect with `sorry` to find which `have` is at fault. Fixes (`Chapter5/DetClearing.lean`):

1. **`set s := …sup… with hs_def` makes `s` an opaque fvar**, so a term like
   `Finset.le_sup … : f x ≤ Finset.univ.sup f` no longer unifies with the goal `… ≤ s`, and
   Lean whnf-loops trying. **Fix:** `rw [hs_def]` to unfold `s` *before* `exact Finset.le_sup …`.
2. **A pair-indexed `Finset.sup (fun p : ι × κ => … E (P p.1 p.2) …)`** then forces
   `isDefEq` to compare `P (a,c).1 (a,c).2` with the goal's literal `P a c` — and that
   `Prod.fst`/`Prod.snd` projection comparison whnf-reduces `E` into a timeout. **Fix:** use a
   **nested** `sup (fun a => sup (fun c => … E (P a c) …))` so every `P a c` appears literally;
   bound via `le_trans (Finset.le_sup (mem_univ c)) (Finset.le_sup (mem_univ a))`, each `f`
   given explicitly. No projection ⇒ no whnf.

General rule reinforced (see the two bullets above and the abstract-scalar trick): never let
`rw`/`ring`/`exact`/`isDefEq` traverse a heavy `AlgEquiv`/`eval`/`det` term while searching for
a pattern or checking a defeq. Bridge equalities with `congrArg <explicit-motive-λ>` (no
kabstract search), prove per-term field arithmetic over **abstract scalars** `(have key : ∀ A D : k, …)`
then `exact key _ _ _`, and pin a polynomial→`Polynomial` factorization (`evalAtGL = eval₂ … ∘ E`)
once via `MvPolynomial.ringHom_ext` on generators rather than unfolding `E`.

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

## `End X` ring-structure gotchas (endomorphism-ring proofs: Krull–Schmidt, Morita)

`CategoryTheory.End X := X ⟶ X` carries `Monoid`/`Ring` instances (preadditive), but
`End X` is a *semireducible def* over the morphism type, and that bites instance search:

- **`f ^ n` on an *ascribed* morphism fails to synthesize the power.** Writing
  `(biprod.map a b : End (K ⊞ I)) ^ n` errors with `failed to synthesize HPow (K ⊞ I ⟶ K ⊞ I) ℕ`
  — the ascription unfolds `End` to the `⟶` type *before* instance search, and `End.monoid`
  is keyed on head symbol `End`, not `Quiver.Hom`. **Fix:** carry the endomorphism as an
  explicit `End`-typed *variable* (a lemma parameter `(M : End (K ⊞ I))` with a hypothesis
  `hM : (M : K ⊞ I ⟶ K ⊞ I) = biprod.map a b`), then `M ^ n` resolves. Same for `f ^ n` on
  any constructed-then-ascribed morphism: bind it to a variable first.
  - **Corollary (`set`-binding an End power as a bare morphism kills `^`, #5274).** `(f : X ⟶ X) ^ n`
    *does* elaborate (Lean resolves `^` at `End X` because `f : End X` drives it), but
    `set F : X ⟶ X := (f : X ⟶ X)` then `F ^ n` fails with `failed to synthesize HPow (X ⟶ X) ℕ ?` —
    `F` is now a bare `X ⟶ X` fvar with no `End` head to trigger `End.monoid`. **Fix:** don't `set`
    the base morphism; `set` the *whole power* instead — `set g : X ⟶ X := (f : X ⟶ X) ^ n with hg`,
    `set g2 := (f : X ⟶ X) ^ (2 * n)` — and phrase the proof over the plain morphisms `g`, `g2`
    (their type is `X ⟶ X`, no `^` needed downstream). `g ≫ g = g2` then closes by
    `rw [hg, hg2, two_mul, pow_add, End.mul_def]` (the `End.mul_def` turns the `pow_add` `*` back
    into `≫`).
  - **Precedence: `^` binds *looser* than `≫`.** `(f : X ⟶ X) ^ n ≫ (f : X ⟶ X)` parses as
    `(f : X ⟶ X) ^ (n ≫ (f : X ⟶ X))` (→ `CategoryStruct.comp n` type error). Always parenthesise
    the power: `((f : X ⟶ X) ^ n) ≫ (f : X ⟶ X)`.
- **Multiplication is *reversed* composition:** `End.mul_def : x * y = y ≫ x`, `End.one_def :
  (1 : End X) = 𝟙 X`. So `pow_succ` then `End.mul_def` turns `x ^ (n+1)` into `x ≫ x ^ n`. A
  block-power induction `(biprod.map a b) ^ n = biprod.map (a ^ n) (b ^ n)` closes with
  `rw [pow_succ, End.mul_def, ih, hM, biprodMap_comp]; congr 1` (rewrite `ih` *before* `hM` so
  the `M ^ n` subterm is gone before `M` is substituted — otherwise you re-introduce
  `(biprod.map a b) ^ n` and the HPow failure returns).
- **`isUnit_iff_isIso` is in `CategoryTheory`, NOT `End`** (`open CategoryTheory` → bare
  `isUnit_iff_isIso (f : End X) : IsUnit f ↔ IsIso f`). Pair with `End.isUnit_iff_isIso`-style
  guesses being wrong.
- **Transport nilpotence/units along an iso with `Iso.conj`** (`Mathlib/CategoryTheory/Conj.lean`):
  `e.conj : End X ≃* End Y`, `e.conj_apply : e.conj f = e.inv ≫ f ≫ e.hom`. It is only a
  `MulEquiv`, but `conj_apply` lets you compute `e.conj 0 = 0` by `simp`, so it carries
  `IsNilpotent` (via `map_pow` + that zero fact) and `IsUnit` (`IsUnit.map e.conj`) both ways.
  Conjugating `f = e.hom ≫ M ≫ e.inv` is exactly `f = e.symm.conj M` (`e.symm.inv = e.hom`).
- **`ext` may not fire on `𝟙 (X ⊞ Y) = biprod.map …`;** use `apply biprod.hom_ext'` (out of a
  biproduct, post-compose with `inl`/`inr`) or `biprod.hom_ext` (into one, with `fst`/`snd`),
  then `simp`. `biprod.map`-composition (`biprod.map a b ≫ biprod.map c d = biprod.map (a≫c)(b≫d)`)
  and `biprod.map 0 0 = 0` both close by `ext <;> simp` — there is no `biprod.map_id`/`map_map`.
- **`End X` is *noncommutative*, so most of Mathlib's `IsLocalRing` consumer API is unusable** —
  it silently assumes `CommRing`/`CommSemiring` (or `IsDedekindFiniteMonoid`). Specifically
  `IsLocalRing.isUnit_or_isUnit_one_sub_self` (CommRing), `isUnit_or_isUnit_of_isUnit_add` and
  `nonunits_add` (CommSemiring), `isUnit_of_mul_isUnit_right` (comm), and
  `IsIdempotentElem.iff_eq_one_of_isUnit` (`IsDedekindFiniteMonoid`) all fail to synthesize on
  `End X`. **Re-derive from the class field `IsLocalRing.isUnit_or_isUnit_of_add_one {a b} (h : a +
  b = 1) : IsUnit a ∨ IsUnit b`**, which holds for any `Semiring`. From it: `IsUnit a ∨ IsUnit (1 -
  a)` via `(by abel : a + (1 - a) = 1)`; "unit summand of a unit finite sum" via
  `Finset.sum_induction` with `nonunits` closure proved through `isUnit_or_isUnit_of_add_one`; and
  "idempotent unit ⇒ `= 1`" by left-multiplying `a*a = a` by the inverse unit (works in any
  `Monoid`). See `Chapter9/KrullSchmidt/Exchange.lean` for all four helpers.
- **`IsIdempotentElem (g : End Z)` written with a type *ascription* `(g : End Z)` fails** with
  `failed to synthesize Mul (Z ⟶ Z)` (the ascription unfolds `End` before instance search, same
  semireducible-def bite as `^`). **Fix:** pass the type as the named implicit —
  `IsIdempotentElem (M := End Z) g` with `g : Z ⟶ Z` — then feed `hg : g ≫ g = g` *directly*
  (`IsIdempotentElem (M := End Z) g` is defeq to `g * g = g` is defeq to `g ≫ g = g`). For the
  output, an idempotent in a local ring being `0`/`1` (End ring `1 = 𝟙` via `End.one_def`)
  bridges back to morphism `g = 0 ∨ g = 𝟙 Z` cleanly; wrap this once and consume the morphism-level
  result so callers never touch `End`-vs-`Hom` zero/one mismatches.
- **`set_option … in` must precede the doc comment, not sit between `/-- … -/` and the theorem**
  (otherwise: `unexpected token 'set_option'; expected 'lemma'`). To silence
  `linter.unusedFintypeInType` on a theorem whose `[Fintype κ]` is only used to form `⨁` in the
  type, put `set_option linter.unusedFintypeInType false in` on the line *above* the docstring.
- **Round-tripping a functor/decomposition through a *derived* module (e.g. `forwardRep`/
  `vertexSpace` applied to `reverseModule R`) — three frictions that cost many iterations
  (see `Chapter2/Discussion_quiver_rep_bijection.lean`):**
  1. *Instances on the derived carrier.* A `noncomputable def` module structure (`reverseModule R :
     Module (PathAlgebra k Q) (⊕ᵢ …)`) is not an instance. Threading `letI := reverseModule R;
     haveI := …isScalarTower R` through *every* statement is fragile (the `letI` inside
     `…isScalarTower`'s type leaves `k`/the tower stuck with metavariables). Instead
     `attribute [local instance] reverseModule` once, then a clean
     `local instance … : IsScalarTower k (PathAlgebra k Q) (⊕ᵢ …) := reverseModule_isScalarTower R`.
     Even then, generic defs like `vertexProj`/`vertexSpace`/`forwardRep` leave `k` (and sometimes
     `V`) floating → `IsScalarTower ?k …` / `Field ?k` "stuck" errors; pin them explicitly with
     `(k := k) (V := …)` at the call site.
  2. *Family-spelling defeq.* `DirectSum Q F` with `F i = R.obj (op i)` is *definitionally* but not
     *syntactically* `⨁ i, ↥(vertexSpace i)`, so `DirectSum.coeLinearMap_lof` / `component.of` /
     coercion-to-ambient (`(z : V)`) do not fire or even elaborate (the coercion resolver does not
     see `R.obj (op i)` as a `SetLike` subtype). Bridge with a one-line `rfl`/defeq lemma stated in
     the projection spelling (`coeV_lof i z : coeV (lof … i z) = (vertexSpace i).subtype z :=
     DirectSum.coeLinearMap_lof _ i z`) and use `(submodule).subtype z` instead of `(z : V)`.
  3. *Coe-head mismatch in naturality.* `apply Subtype.ext` yields `Subtype.val`, but
     `arrowMap_coe_apply`/your `…_coe` lemmas are stated with the `SetLike`/`↑` coe, and a
     structure field `app := (equiv).toLinearMap` puts a `toLinearMap`-coe between you and the
     equiv-coe `…_coe` lemma — so `rw`/`simp` silently fail to match. Don't fight it lemma-by-lemma:
     `change` the whole goal into a fully *definitionally-equal* computed form (here all the bridging
     coe lemmas — `ofLinear` apply, `codRestrict`/`restrict` `.val`, `reverseModule_smul_def`,
     `…_coe` — are `rfl`), e.g. `change lof Y.unop (R.mapLinear e x) = toEnd R (ofArrow e.unop)
     (lof X.unop x)`, then finish with the *non*-`rfl` rewrites (`toEnd_ofPath`, `pathEnd_mk`, …).
- **A `QuiverRepresentation` `obj` is only `AddCommMonoid`** (it is built over `CommSemiring k`).
  So a module assembled from rep vertex spaces (`⊕ᵢ R.obj (op i)`) is *not* an `AddCommGroup`, and
  any decomposition machinery requiring `[AddCommGroup V]` (e.g.
  `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, which needs subtraction) cannot be
  applied to it. Keep the bulk of the machinery at `[AddCommMonoid V]` and split *only* the
  group-requiring lemma (`isInternal_vertexSpace`) into its own `[AddCommGroup V]` section.
- **There is no `QuiverRepresentation.Iso` reachable from Chapter 2** (it lives in Chapter 6, which
  *imports* Chapter 2 — using it would be circular, and redefining it clashes). For a Chapter-2
  representation isomorphism, use `Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂` (note: `k` and `Q` are
  *explicit*) and expose the per-vertex `LinearEquiv`s separately as the witness that the
  components are isos.

## Pseudoelement diagram chases in an abelian category (Fitting/Krull–Schmidt, #5274)

`Abelian.Pseudoelement` (`Mathlib/CategoryTheory/Abelian/Pseudoelements.lean`) is the clean tool for
"diagram chase" proofs that a categorical map is mono/epi/iso — e.g. that the image restriction
`g' = image.ι (fⁿ) ≫ factorThruImage (fⁿ)` is iso once the `im (fⁿ)` and `ker (fⁿ)` chains stabilise
(`Etingof.exists_pow_stabilizes`, `Chapter9/KrullSchmidt/Length.lean`). Setup and gotchas:

- **Activate the coercions with `attribute [local instance]`, NOT `open scoped`.** The sort coercion
  `objectToSort` (lets `X : C` be the type of pseudoelements), `homToFun` (lets `f a` mean
  pseudo-application), and `overToSort` are `scoped[Pseudoelement] attribute [instance]`, but
  `open scoped Pseudoelement` / `open scoped CategoryTheory.Abelian.Pseudoelement` did **not** turn
  them on (symptoms: `∀ y : X` → "type expected, got (X : C)"; `f a` → `Function expected at ?m`).
  The reliable incantation (also given in the file's own header comment) is
  `attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
  CategoryTheory.Abelian.Pseudoelement.homToFun CategoryTheory.Abelian.Pseudoelement.overToSort`.
  Qualify the lemmas fully (`Abelian.Pseudoelement.comp_apply` / `.apply_zero` / `.zero_apply` /
  `.pseudo_exact_of_exact` / `.pseudo_surjective_of_epi` / `.pseudo_injective_of_mono` /
  `.zero_of_map_zero` / `.mono_of_zero_of_map_zero` / `.epi_of_pseudo_surjective`) — bare
  `comp_apply` collides with `CategoryTheory.comp_apply`.
- **Prove mono/epi/iso the pseudoelement way.** `mono_of_zero_of_map_zero f : (∀ a, f a = 0 → a = 0)
  → Mono f`; `epi_of_pseudo_surjective f : Function.Surjective f → Epi f`; then
  `isIso_of_mono_of_epi f` (abelian is `Balanced`). `comp_apply f g a : (f ≫ g) a = g (f a)`,
  `apply_zero f : f 0 = 0`, `zero_apply Q a : (0 : P ⟶ Q) a = 0` drive the algebra.
- **Bridge subobject equality ⟷ pseudoelement membership via exactness.** To turn
  `kernelSubobject g2 = kernelSubobject g` (a `Subobject` equality from chain stabilisation) into the
  pseudoelement fact `g2 w = 0 → g w = 0`: build the exact short complex
  `ShortComplex.mk (kernelSubobject g).arrow g (kernelSubobject_arrow_comp g)` — exact because
  `imageSubobject (mono).arrow = Subobject.mk (.arrow) = that subobject` (`ShortComplex.exact_iff_image_eq_kernel`
  + `imageSubobject_mono` + `Subobject.mk_arrow`) — then `pseudo_exact_of_exact` gives
  `∃ a, (kernelSubobject g2).arrow a = w`, and `(kernelSubobject g).arrow ≫ g = 0`
  (`kernelSubobject_arrow_comp`) finishes. Dually for images, use `factorThruImageSubobject`
  (epi → `pseudo_surjective_of_epi`) and `imageSubobject_arrow_comp`.
- **Never `rw` a morphism that also appears in a dependent type position.** `rw [← hpi]` to turn
  `g (i a)` into `(p ≫ i)(i a)` fails with `motive is not type correct` because `g` reappears in the
  type of `i = Abelian.image.ι g` (`i : Abelian.image g ⟶ X`). **Fix:** route through an
  *intertwining application lemma* stated once as `∀ y, i (p y) = g y` (from `p ≫ i = g` via
  `← comp_apply`), and rewrite with *that* (`← hint (i a)`) instead of rewriting `g` directly — it
  never abstracts the `g` buried in `i`'s type.
