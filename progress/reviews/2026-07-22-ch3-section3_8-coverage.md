# Stage 3.7 coverage-arm audit — §3.8 (issue #7373)

Audited the three sorry-free, `fidelity: verified` §3.8 items that lacked a
`coverage` field: **Problem 3.8.3**, **Problem 3.8.4**, **Problem 3.8.5**.
Added `coverage` (with `derived` sub-part arrays for the multi-part 3.8.4/3.8.5),
`lean_decl`, `lean_file`, `last_updated`, reconciled the notes, and fixed the
stale `sorry_free: false` flag on 3.8.5. No re-proving; the prior fidelity
reviews stand.

## Build / axiom verification

`lake build` succeeds sorry-free for `Chapter3.Problem3_8_3`,
`Chapter3.Theorem3_8_1`, `Chapter3.Lemma3_8_2`, `Chapter3.Problem3_8_4_Main`,
`Chapter3.Problem3_8_4_General`, `Chapter3.Problem3_8_5` (full chain, 8592 jobs).
`command grep -c sorry` = 0 for every module. `#print axioms` on all ten
headline decls shows only `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`.

## Coverage classification

### Problem 3.8.3 — Krull-Schmidt without algebraic closure → `covered_full`

Single claim. `Problem3_8_3.lean` names four general-field citation targets, each
assuming only `[Field k]` (no `IsAlgClosed k`):
`endo_iso_or_nilpotent`, `sum_nilpotent_endo`, `krull_schmidt_existence`,
`krull_schmidt_uniqueness`. They cite the `Lemma3_8_2`/`Theorem3_8_1` proofs,
which replace the book's generalized-eigenspace argument with the Fitting
decomposition (`isCompl_iSup_ker_pow_iInf_range_pow`, valid for any
Noetherian+Artinian module). This is exactly the book's claim that Lemma 3.8.2 —
and hence Krull-Schmidt — holds without algebraic closure. `krull_schmidt_uniqueness`
is the referent of Problem 3.8.4's citation "the Krull-Schmidt theorem, valid over
any field by Problem 3.8.3". Added the missing `lean_file`.

### Problem 3.8.4 — scalar extension + Noether-Deuring → `covered_full` (roll-up)

Two parts, both `covered_full`.

- **(i)** `iso_of_baseChange_iso` (`Problem3_8_4_Main.lean:50`).
- **(ii)** Noether-Deuring `directSummand_of_baseChange_directSummand`
  (`Problem3_8_4_General.lean:47`).

**Fidelity spot check (deliverable 3): both hold over a GENERAL field extension
`L/K`, not merely the finite case.** Each theorem's only extension hypotheses are
`[Field L] [Algebra K L]` — no finiteness on `L`. The finite-extension reduction
lives *inside* the proof (the book's Zariski-specialization route: descend the
`L ⊗[K] A`-morphism to a finitely generated `K`-subalgebra `R ⊆ L`, specialize at
a maximal ideal to a residue field `κ` finite over `K` by Zariski's lemma, then
apply the finite case). Lean uses Mathlib's scalar-on-left `L ⊗[K] V` for the
book's `V ⊗_K L` (equivalent); (ii) encodes "direct summand" as a split injection
`p ∘ i = id`. Neither sub-part is weaker than the book claim.

### Problem 3.8.5 — failure of Krull-Schmidt (infinite dim) → `covered_full` (roll-up)

Two parts, both `covered_full`. `A` = `periodicSubalg` (continuous period-1
functions), `M` = `antiperiodicSubmod` (continuous antiperiodic functions).

- **(i)** `periodic_isIndecomposable` (147), `antiperiodic_isIndecomposable` (252)
  — both `Etingof.IsIndecomposable (periodicSubalg) _`, from `A` having no
  nontrivial idempotents (a `{0,1}`-valued continuous function is constant by
  connectedness of `ℝ`).
- **(ii)** `periodic_not_linearEquiv_antiperiodic` (331), `periodic_sq_linearEquiv_antiperiodic_sq` (485).

**Fidelity spot check (deliverable 3):** part (ii)'s `A ≇ M` is a genuine
`IsEmpty (periodicSubalg ≃ₗ[periodicSubalg] antiperiodicSubmod)` — a real
non-isomorphism of `A`-modules (any generator of `M` vanishes somewhere by the
IVT), not a weaker additive/scalar surrogate. `A ⊕ A ≅ M ⊕ M` is a genuine
`A`-linear iso `(periodicSubalg × periodicSubalg) ≃ₗ[periodicSubalg]
(antiperiodicSubmod × antiperiodicSubmod)` via the rotation
`(f,g) ↦ (cos·f − sin·g, sin·f + cos·g)` with transpose inverse (`cos²+sin²=1`).

**Reconciled the stale `sorry_free: false` → `true`**: the file has 0 sorries and
all four headline decls are axiom-clean.

## Follow-up

None. No sub-part's Lean statement is weaker than the book claim, so no follow-up
`feature` issue is opened.
