# Fidelity sweep — Wave 7 (Chapter 7, issue #5344)

Judge: Opus 4.8 (six parallel Opus sub-auditors + Opus adjudication), distinct
from the Sonnet/other authors of the items below.
Scope: all 30 Chapter 7 claim-bearing done items (types theorem / proposition /
lemma / corollary / definition / example / remark).
Method: PLAN.md Stage 3.2 steps 6–7 — anti-vacuity decision test, then
conjunct-by-conjunct fidelity of the Lean statement against the book blob.
Calibrated on confirmed examples #5322, #5323, #5326.

## Context

Issue #5344 was created with all 30 items at `fidelity: unchecked`, but a prior
wave-2 sweep had already assigned verdicts (20 verified, 8 gap, 2 non-standard
`faithful`) and opened repair issues for the gaps — without writing a wave
certificate or reconciling once the repairs merged. All eight gap-repair issues
and both `faithful` resolution issues had since closed via merged PRs. This wave
re-audits every item against the **current** (post-repair) Lean, reconciles the
merged repairs, normalizes the `faithful` label, and (crucially) re-checks the
previously-`verified` items rather than trusting them.

Re-auditing the 20 previously-`verified` items was not a formality: 3 of them
(Example7.5.3, Definition7.8.1, Definition7.8.2) were **refuted to `gap`**.

## Outcome

After this wave every Chapter 7 claim-bearing done item (30 total) is
**`verified` (25)** or **`gap` (5)**; no item remains `unchecked` or `faithful`.
Only `progress/items.json` and this file were touched — no Lean changes.

- **verified: 25**
- **gap: 5** — Example7.3.2 (#5643), Example7.9.6 (#5647), Example7.5.3 (#5838),
  Definition7.8.1 (#5839), Definition7.8.2 (#5840).

### Gap → verified reconciliations (8; merged repairs confirmed faithful)

Six items that were `gap` and two that carried the non-standard `faithful`
label were re-audited against the current Lean; all repairs have merged and all
eight are now genuinely faithful and non-vacuous. Stale `fidelity_issue` /
`fidelity_note` dropped.

- **Example7.1.3** (was gap #5640) — all six category examples present; the
  homotopy category is genuinely constructed via a real `Congruence homotopyRel`
  (actual `ContinuousMap.Homotopic`), not sorried or faked. → **verified**.
- **Example7.2.2** (was gap #5642) — items 1–7 (monoid↔one-object,
  forgetful, dual functor, (co)yoneda, Fun(X,ℤ), path-category reps, Ind/Res) and
  the checkable parts of item 8 (direct sum, tensor, tensor-power, exterior-power
  bifunctors) are all real `where`-clause functors with proven laws. Symmetric
  power SⁿV, Schur functors, and reflection functors are honestly deferred as
  scope notes (genuinely advanced / limited Mathlib API), which the book itself
  flags as advanced. No formalized statement is vacuous or weakened. →
  **verified**.
- **Example7.1.6** (was `faithful` #5641) — `Linear k (ModuleCat A)` faithfully
  captures Rep(A) enriched over Vect_k; non-vacuous (depends on
  `ModuleCat.linearOverField`). → **verified**.
- **Example7.6.3** (was `faithful` #5644) — all five adjunction examples are
  genuine: (1L)/(1R) constructed `Adjunction`s in the rigid category `FDRep k G`;
  (2) the book's exact `Res ⊣ Ind` direction as a real `Adjunction`; (3)/(4)/(5)
  the defining hom-set bijections `UniversalEnvelopingAlgebra.lift`,
  `MonoidAlgebra.lift` (via `G →* Aˣ`, faithfully encoding GL₁),
  `TensorAlgebra.lift`, `SymmetricAlgebra.lift` (commutative-codomain constraint
  faithful to Comm_k). No mere `Nonempty`. → **verified**.
- **Example7.7.2** (was gap #5645) — BOTH `Abelian (ModuleCat A)` and
  `Abelian (FGModuleCat A)` (under `[IsNoetherianRing A]`) present; `Abelian` is a
  genuine structural class. → **verified**.
- **Definition7.9.1** (was gap #5655) — BOTH concepts present as real `abbrev`s:
  `AdditiveFunctor = Functor.Additive` and `LinearFunctor = Functor.Linear k`
  (with the `[Linear k C] [Linear k D]` context matching the book's qualifier).
  → **verified**.
- **Example7.9.2** (was gap #5646) — all six sub-claims (Ind, Res, Hom_G(V,?)
  each additive and k-linear) present on the genuine `Rep k G` functors
  (`indFunctor`, `resFunctor`, `linearCoyoneda`), not merely on `restrictScalars`;
  the two non-`inferInstance` proofs carry real `map_smul` bodies. → **verified**.
- **Example7.9.5** (was gap #5626) — `maschke_isSemisimpleCategory` now asserts
  the full `IsSemisimpleCategory (ModuleCat k[G])` = every short-exact
  `ShortComplex` splits, under `IsUnit (Fintype.card G : k)` (char ∤ |G|). This is
  the genuine Maschke statement, not a special case or trivial existential. →
  **verified**.

### verified → gap (3; prior verdict refuted)

- **Example7.5.3** (→ new issue #5838) — the book states BOTH that the forgetful
  functor A-mod→Vect_k is representable (M = A) AND that for infinite-dimensional
  A restricted to finite-dim modules it is in general NOT representable (witness
  A = c₀₀(ℤ)). Lean formalizes only the positive half (`ringLmapEquivSelf`); the
  non-representability counterexample — the pedagogical point of the example — is
  absent. Silent weakening (Step 7).
- **Definition7.8.1** (→ new issue #5839) — the definition names four notions:
  complex, differentials, cohomology H^i = Ker(d_i)/Im(d_{i-1}), exact-in-i-th-
  term, exact sequence. Lean declares only `CochainComplex'` (the complex
  object); cohomology and exactness are named in the docstring's Mathlib-
  correspondence but have no Lean declaration. Docstring/decl mismatch (Step 7).
- **Definition7.8.2** (→ new issue #5840) — defines a short **exact** sequence
  (0→X→Y→Z→0 exact; X→Y mono, Y→Z epi, Y/X→Z iso), but Lean aliases
  `CategoryTheory.ShortComplex` (a short *complex*, satisfied by the zero
  complex); the defining `ShortExact` predicate is dropped. Vacuity + weakening
  (Steps 6–7).

### Persisting gaps after partial repair (2; repair issues reopened)

- **Example7.3.2** (#5643 reopened) — the prior repair merged sub-items (1a),
  (1b), (2a), (3), (4). **Residual:** sub-item (2)'s non-naturality claim —
  F: V ↦ V* on FVect'_k is pointwise-iso to the identity but NOT naturally iso
  (obstruction: V ≇ V* as GL(V)-reps) — remains absent (only the positive half
  `linearEquiv_dual_iff_finiteDimensional` is present). This is the point of
  sub-item (2). → stays **gap**.
- **Example7.9.6** (#5647 reopened) — the prior repair merged the positive
  exactness claims (Res exact; Ind exact under a documented flatness hypothesis;
  Hom(X,?) left-exact; tensor right-exact). **Residual:** (ii) "Hom(X,?) not
  necessarily right exact" and (iii) "tensor not necessarily left exact" — both
  explicit book claims with the named counterexample 0→ℤ→ℤ→ℤ/2ℤ→0 — are
  unformalized (prose only); and (iii) is stated only for `[CommRing R]` via
  `tensorLeft`, silently narrowing the book's arbitrary-ring A. → stays **gap**.

## Verdicts (all 30)

§7.1: Definition7.1.1 (`Category`, all axioms), Remark7.1.2 (notational, no decl
needed), Example7.1.3, Definition7.1.4 (`FullSubcategory`), Example7.1.5
(full subcategory AbGrp↪Grp: `.Full` is the load-bearing instance and is
asserted; #5594 repair confirmed), Example7.1.6 — all **verified**.

§7.2–7.4: Example7.2.2, Definition7.2.1 (`Functor`, both preservation laws),
Definition7.3.1 (`NatTrans`, components + naturality), Definition7.4.1
(`Equivalence`; Mathlib bundles the coherent/adjoint form — stronger, not
weaker) — all **verified**.

§7.5: Lemma7.5.1 (Yoneda: `∃!` iso inducing φ — existence + uniqueness +
inducing condition), Remark7.5.2 (motivational, no decl), **Example7.5.3 → gap**
(non-representability counterexample missing).

§7.6: Definition7.6.1 (`Adjunction`), Remark7.6.2 (motivational, no decl),
Example7.6.3 — **verified**.

§7.7: Definition7.7.1 (`Abelian`; intrinsic axiomatization equivalent to the
book's embedding form, documented), Example7.7.2, Remark7.7.4 (expository
Morita-equivalence aside — no theorem the formalization must carry; verified as
notational) — **verified**.

§7.8: **Definition7.8.1 → gap** (cohomology + exactness undeclared),
**Definition7.8.2 → gap** (aliases `ShortComplex`, drops `ShortExact`),
Example7.8.3 (split SES built from a real `Splitting.ofHasBinaryBiproduct`),
Definition7.8.6 (connecting hom `δ` + LES exact at all three positions) —
Example7.8.3 and Definition7.8.6 **verified**.

§7.9: Definition7.9.1, Example7.9.2, Definition7.9.3 (left/right exact functors
= preserves finite (co)limits), Definition7.9.4 (`IsSemisimpleCategory` = every
SES splits — genuine, quantifies over all SES with real `Splitting` data),
Example7.9.5, **Example7.9.6 → gap** (negative exactness directions absent;
(iii) narrowed to CommRing) — the rest **verified**.

## Sweep status

Chapter 7 fidelity: 25/30 verified, 5 gap. This is the first Chapter 7 wave
certificate. The five gaps are tracked by open repair issues (#5643, #5647,
#5838, #5839, #5840), all linked to #5344; a future wave should reconcile them
once repaired (as this wave did for the eight merged Chapter 7 repairs), and the
sweep may not be called complete until it reaches two consecutive dry waves.
