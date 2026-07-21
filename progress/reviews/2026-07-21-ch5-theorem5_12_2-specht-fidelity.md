# Statement-fidelity & non-vacuity audit — Theorem 5.12.2 (Specht modules classify the irreps of Sₙ)

**Issue:** #7155
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 70ff3fa4)
**Scope:** report-only fidelity + non-vacuity audit of the four headline declarations of Theorem 5.12.2
**Verdict: FAITHFUL — all four declarations axiom-clean, no defect. Nothing filed.**

## Sources compared

- **Book statement** (`blobs/Chapter5/Theorem5.12.2.md`):
  > **Theorem 5.12.2.** *The subspace $V_\lambda := \mathbb{C}[S_n] c_\lambda$ of
  > $\mathbb{C}[S_n]$ is an irreducible representation of $S_n$ under left multiplication.
  > Every irreducible representation of $S_n$ is isomorphic to $V_\lambda$ for a unique
  > $\lambda$.* The modules $V_\lambda$ are called the **Specht modules**.
- **Book definition** (`blobs/Chapter5/Definition5.12.1.md`): a partition $\lambda$ of $n$,
  its Young diagram/tableau $T_\lambda$ (canonical increasing left-to-right, top-to-bottom
  filling), the row subgroup $P_\lambda$ and column subgroup $Q_\lambda$, with
  $P_\lambda \cap Q_\lambda = \{1\}$. (The symmetrizer $c_\lambda = b_\lambda a_\lambda$
  with $a_\lambda = \sum_{g\in P_\lambda} g$, $b_\lambda = \sum_{g\in Q_\lambda}\mathrm{sign}(g)\,g$.)
- **Book proof** (`blobs/Chapter5/Discussion_proof_of_Theorem5.12.2.md`): for
  $\lambda \geq \mu$, `Hom(V_λ, V_μ) = c_λ ℂ[Sₙ] c_μ`, which is `0` for `λ > μ`
  (Lemma 5.13.2) and 1-dimensional for `λ = μ` (Lemmas 5.13.1/5.13.3); hence the `V_λ`
  are irreducible and pairwise non-isomorphic. Since `#partitions(n) = #conjClasses(Sₙ)`,
  the `V_λ` exhaust all irreducibles.
- **Lean declarations** (four headline decls, split across three sub-files):

```lean
-- Theorem5_12_2_Irreducible.lean:26
noncomputable def SpechtModule (n : ℕ) (la : Nat.Partition n) :
    Submodule (SymGroupAlgebra n) (SymGroupAlgebra n) :=
  Submodule.span (SymGroupAlgebra n) {YoungSymmetrizer n la}

-- Theorem5_12_2_Irreducible.lean:204
theorem Theorem5_12_2_irreducible (n : ℕ) (la : Nat.Partition n) :
    IsSimpleModule (SymGroupAlgebra n) (SpechtModule n la)

-- Theorem5_12_2_Distinct.lean:44
theorem Theorem5_12_2_distinct (n : ℕ) (la mu : Nat.Partition n) (h : la ≠ mu) :
    IsEmpty ((SpechtModule n la) ≃ₗ[SymGroupAlgebra n] (SpechtModule n mu))

-- Theorem5_12_2_Classification.lean:482
theorem Theorem5_12_2_classification
    (n : ℕ) (M : Type) [AddCommGroup M] [Module (SymGroupAlgebra n) M]
    [IsSimpleModule (SymGroupAlgebra n) M] :
    ∃ la : Nat.Partition n, Nonempty (M ≃ₗ[SymGroupAlgebra n] (SpechtModule n la))
```

where `SymGroupAlgebra n := MonoidAlgebra ℂ (Equiv.Perm (Fin n))` is `ℂ[Sₙ]`.

## Fidelity checks (per issue deliverable, one block per declaration)

### (a) `SpechtModule` is a genuinely constructed module (not a sorry'd def) — FAITHFUL

- `SpechtModule n la = Submodule.span (SymGroupAlgebra n) {YoungSymmetrizer n la}`. The
  span of a singleton `{c}` in the ring-acting-on-itself left module is exactly the left
  ideal `ℂ[Sₙ]·c = {a·c : a ∈ ℂ[Sₙ]}`. This is precisely the book's
  `V_λ := ℂ[Sₙ] c_λ`. ✓
- The generator is real, not a placeholder. `YoungSymmetrizer n la`
  (`Definition5_12_1.lean:129`) is `ColumnAntisymmetrizer n la * RowSymmetrizer n la`,
  where `RowSymmetrizer = ∑_{g∈P_λ} g` (`:106`) and
  `ColumnAntisymmetrizer = ∑_{g∈Q_λ} sign(g)·g` (`:113`) are honest finite sums over the
  genuinely constructed subgroups `RowSubgroup`/`ColumnSubgroup` (`:64`/`:87`, full
  `Subgroup` structures with `one_mem'`/`mul_mem'`/`inv_mem'` proofs keyed off
  `rowOfPos`/`colOfPos` of the canonical filling). No `def`/`instance` body in the chain
  is sorry'd (confirmed by axiom check below). ✓
- **Convention nuance (not a defect).** The Lean uses `c_λ = b_λ·a_λ` (column × row),
  documented at `Definition5_12_1.lean:119-127` as the Fulton–Harris/Etingof convention.
  The opposite convention `a_λ·b_λ` yields an isomorphic left ideal, so the choice does
  not affect any of the four statements' truth or fidelity. Recorded for transparency. ✓

### (b) Irreducibility is a real irreducible predicate over the correct algebra — FAITHFUL

- `Theorem5_12_2_irreducible : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n la)`.
  A left module over `ℂ[Sₙ]` **is** a representation of `Sₙ`, and `IsSimpleModule` is the
  genuine irreducibility predicate (nonzero, and its only submodules are `⊥` and `⊤`). The
  algebra is `SymGroupAlgebra n = ℂ[Sₙ]`, exactly the book's "under left multiplication". ✓
- This is not a weakened/off-by-triviality form: the proof (`:204-256`) explicitly
  discharges both `SpechtModule ≠ ⊥` (via `young_symmetrizer_sq_ne_zero`) and "every proper
  submodule is `⊥`", the latter via Maschke semisimplicity + the sandwich identity
  `c_λ·x·c_λ = f(x)·c_λ` (from Lemma 5.13.1) and `c_λ² = α·c_λ`, `α ≠ 0` (Lemma 5.13.3) —
  the book's ingredients. ✓

### (c) Distinctness is honest non-isomorphism over all distinct partitions — FAITHFUL

- `Theorem5_12_2_distinct : la ≠ mu → IsEmpty (SpechtModule n la ≃ₗ[ℂ[Sₙ]] SpechtModule n mu)`.
  `IsEmpty (·≃ₗ·)` says there is **no** `ℂ[Sₙ]`-linear equivalence, i.e. `V_λ` and `V_μ` are
  genuinely non-isomorphic as representations. Universally quantified over **all** pairs with
  `la ≠ mu` — no exceptions carved out. ✓
- The proof (`:44-85`) is faithful to the book: for `la ≠ mu`, dominance is total-ish enough
  that either `¬ mu.Dominates la` or `¬ la.Dominates mu`; the corresponding Young symmetrizer
  annihilates the other Specht module (`young_symmetrizer_annihilates_specht`, via
  `Lemma5_13_2_general`), and any iso would then force `c² = 0`, contradicting
  `young_symmetrizer_sq_ne_zero`. This is the book's `c_λ ℂ[Sₙ] c_μ = 0` vanishing. ✓

### (d) Classification genuinely says every irreducible is a Specht module up to iso — FAITHFUL

- `Theorem5_12_2_classification`: for every simple `ℂ[Sₙ]`-module `M`, there exists a
  partition `la` and a `ℂ[Sₙ]`-linear equivalence `M ≃ₗ SpechtModule n la`. This is exactly
  "every irreducible representation of `Sₙ` is isomorphic to some `V_λ`". ✓
- **"Unique λ" is faithfully split, not dropped.** The book's "for a unique `λ`" is the
  conjunction of *existence* (this theorem: some `la` works) and *uniqueness* (that the
  `la` is forced, since distinct partitions give non-isomorphic modules —
  `Theorem5_12_2_distinct`). Together the two declarations render "unique `λ`" completely.
  The internal lemma `blockOf_specht_injective` (`Classification.lean:376`) already uses
  `Theorem5_12_2_distinct` to make the partition→Wedderburn-block map injective, so the
  uniqueness content is genuinely present in the file. ✓
- The proof (`:482-501`) is the book's counting argument, honestly implemented: some
  `c_λ` acts nontrivially on `M` (`exists_young_symmetrizer_nontrivial`, which uses
  `#partitions(n) = #conjClasses(Sₙ) = #Wedderburn-blocks` via `Corollary4_2_2` +
  `irrepDecomp_n_le_card_partition` to show the Specht modules exhaust the blocks), then the
  evaluation map `V_λ → M`, `v ↦ v·m₀` is a nonzero map between simples, so Schur
  (`LinearMap.bijective_of_ne_zero`) makes it an isomorphism. ✓
- **Universe scope nuance (harmless, not a defect).** `M` is quantified at `Type` (universe
  0), not `Type*`. This loses no genuine representation up to isomorphism: every simple
  `ℂ[Sₙ]`-module is finite-dimensional over `ℂ` (`dim ≤ dim ℂ[Sₙ] = n!`), hence isomorphic
  to a `Type`-0 model, so "every irreducible is a `V_λ` up to iso" is fully captured. Noted
  for transparency; consistent with universe-restriction nuances documented in prior audits
  (e.g. the 8.1.1 review). ✓

## Non-vacuity check

**Axioms.** A scratch `#print axioms` on each of the four headline declarations reports
**exactly**:

```
'Etingof.SpechtModule'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.Theorem5_12_2_irreducible'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.Theorem5_12_2_distinct'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.Theorem5_12_2_classification' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` and no custom/unexpected axiom on any of the four — so the **entire transitive
dependency chain** (`YoungSymmetrizer`, `Row/ColumnSymmetrizer`, `Row/ColumnSubgroup`,
`Lemma5_13_1/2/3`, `IrrepDecomp.mk'`, `Corollary4_2_2`, the Wedderburn-block machinery) is
sorry-free. A `grep` for `sorry`/`admit` across the three `Theorem5_12_2_*` files and
`Definition5_12_1.lean` also returns nothing. ✓

**Hypotheses are inhabited (not vacuously-true statements).**
- `SpechtModule`/`irreducible`: `Nat.Partition n` is inhabited for every `n` (e.g. the
  single-part `[n]` for `n ≥ 1`, the empty partition for `n = 0`), so there is always a
  `la` to instantiate and `SpechtModule n la` is a genuine nonzero simple module. ✓
- `distinct`: the `la ≠ mu` hypothesis is satisfiable whenever `#Partition n ≥ 2`, i.e. for
  all `n ≥ 2`. (For `n ∈ {0,1}` there is a single partition and nothing to distinguish —
  correctly, the theorem is then unused, not falsely asserting a distinction.) ✓
- `classification`: the `[IsSimpleModule ℂ[Sₙ] M]` instance is inhabitable — `SpechtModule n la`
  is itself such an `M` (by `Theorem5_12_2_irreducible`) — so the universally-quantified
  statement has genuine instances. ✓

**Concrete non-vacuous instance — `n = 3`.** Partitions of `3` are `[3]`, `[2,1]`, `[1,1,1]`
(three of them), matching the three conjugacy classes of `S₃`. The three Specht modules
`V_[3]` (trivial, dim 1), `V_[1,1,1]` (sign, dim 1) and `V_[2,1]` (standard, dim 2) are the
genuine complete list of irreducibles of `S₃`: each is simple (`irreducible`), pairwise
non-isomorphic (`distinct`, three distinct partitions), and every simple `ℂ[S₃]`-module is
one of them (`classification`). Non-vacuous on all four counts. ✓

## Build & verification

- `lake exe cache get` — cache present (no rebuild).
- `lake build EtingofRepresentationTheory.Chapter5.Theorem5_12_2` — **exit 0**
  ("Build completed successfully (8589 jobs)"). Only non-blocking lint warnings (`show`
  readability notes, `push_neg` deprecation, one 100-char line) in `Definition5_12_1.lean`
  and `Lemma5_13_1.lean`; none affect correctness.
- `#print axioms` on all four headline declarations — clean triple, reported above.

## Verdict

**FAITHFUL.** All four headline declarations of Theorem 5.12.2 faithfully render the book:
`SpechtModule` is the genuinely constructed left ideal `ℂ[Sₙ]·c_λ` (real Young symmetrizer,
no sorry'd defs); `Theorem5_12_2_irreducible` is honest `IsSimpleModule` irreducibility over
`ℂ[Sₙ]`; `Theorem5_12_2_distinct` is honest `IsEmpty`-of-linear-equiv non-isomorphism over
all distinct partitions; and `Theorem5_12_2_classification` genuinely states every simple
`ℂ[Sₙ]`-module is a Specht module up to iso — with the book's "unique `λ`" split faithfully
across `classification` (existence) and `distinct` (uniqueness). All four are axiom-clean
(no `sorryAx`, standard triple only), and the statements are non-vacuous (inhabited
hypotheses; concrete `S₃` witness). The only nuances are the `b_λ a_λ` symmetrizer
convention and the `Type`-0 universe quantifier in `classification`, both harmless and
documented. **No defect; no issue filed.**
