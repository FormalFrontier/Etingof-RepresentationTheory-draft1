# Review — Ch3 Theorem 3.3.1: Irreducible representations of ⊕ᵢ Mat_{dᵢ}(k)

- **Issue:** #7150 (review, report-only)
- **Reviewer session:** `/work` → `/review` worker, branch `agent/c30bcf90`
- **Target:** `EtingofRepresentationTheory/Chapter3/Theorem3_3_1.lean` (249 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter3/Theorem3.3.1.md` (refs `blobs/Chapter3/Theorem3.3.1.refs.md`)
- **Focus areas:** statement fidelity of the three-conjunct classification; typeclass-hypothesis scrutiny on conjunct (2); no-finiteness check on conjunct (3); `MatProd`/`Pi.single` action-model faithfulness; `NeZero`/`dⱼ = 0` non-vacuity handling; distinctness of the `Vⱼ`; axiom cleanliness (report-only, no proof edits)
- **Overall verdict:** **FAITHFUL.** The public theorem
  `Etingof.irreducible_reps_of_matrix_algebra` and all three supporting public
  declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`),
  non-vacuous, and faithfully render the book's classification. The three conjuncts
  correctly encode (1) each `Vⱼ = k^{dⱼ}` is simple, (2) every finite-dimensional simple
  `A`-module is isomorphic to **some** `Vⱼ`, and (3) every `A`-module is semisimple. The
  conjunct-(2) instance list is the natural `k`-algebra-representation setup, **not** a
  vacuity-inducing over-restriction. Conjunct (3) is stated (and proved) for **all**
  `A`-modules with no finiteness hypothesis — a faithful strengthening of the book's
  finite-dimensional claim. The `[∀ i, NeZero (dᵢ)]` hypothesis is the correct, necessary
  rendering of the book's implicit `dᵢ ≥ 1`. **One documented scope nuance** (not a defect):
  the pairwise **non-isomorphism** of the `Vⱼ` is true here but is not separately asserted in
  the statement. **No follow-up issue filed.**

---

## 0. Build and axiom-cleanliness audit

`lake exe cache get` (cache hit, no downloads) then
`lake build EtingofRepresentationTheory.Chapter3.Theorem3_3_1` — **exit 0, 1591 jobs**
(Mathlib cached). `#print axioms` via a scratch importer on the four public declarations:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.irreducible_reps_of_matrix_algebra` | 239 | `[propext, Classical.choice, Quot.sound]` |
| `isSimpleModule_vModuleProd` (Part 1) | 124 | `[propext, Classical.choice, Quot.sound]` |
| `exists_iso_vModuleProd` (Part 2) | 145 | `[propext, Classical.choice, Quot.sound]` |
| `isSemisimpleModule_of_matrixProd` (Part 3) | 139 | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no custom axiom. `grep` for `sorry|admit|proof_wanted` returns nothing. The
two supporting lemmas `matrix_simpleModule_iso_std` (line 70) and
`isSimpleModule_matrix_vecModule` (line 38) are `private` (invisible to the importer), but
they feed the axiom-clean public results, so they are transitively `sorry`-free. `MatProd`
(line 100) is an `abbrev` with a genuine body; `vModuleProd` (line 109) is a real `local
instance` built by `Module.compHom` — no sorried data anywhere. Build emits only three
`show`-should-be-`change` style lints (lines 210/214/227) — cosmetic, no correctness or
fidelity impact.

---

## 1. Book statement and the three-conjunct rendering

**Book (Theorem 3.3.1, verbatim):** *Let `A = ⊕ᵢ₌₁ʳ Mat_{dᵢ}(k)`. Then the irreducible
representations of `A` are `V₁ = k^{d₁}, …, Vᵣ = k^{dᵣ}`, and any finite dimensional
representation of `A` is a direct sum of copies of `V₁, …, Vᵣ`.*

**Lean:**
```lean
theorem Etingof.irreducible_reps_of_matrix_algebra :
    (∀ j, IsSimpleModule (MatProd k d) (Fin (d j) → k)) ∧
    (∀ (W : Type*) [AddCommGroup W] [Module (MatProd k d) W] [Module k W]
        [IsScalarTower k (MatProd k d) W] [FiniteDimensional k W]
        [IsSimpleModule (MatProd k d) W],
        ∃ j, Nonempty (W ≃ₗ[MatProd k d] (Fin (d j) → k))) ∧
    (∀ (X : Type*) [AddCommGroup X] [Module (MatProd k d) X],
        IsSemisimpleModule (MatProd k d) X)
```

The book's single sentence bundles three logically distinct claims, and the conjunction is
the faithful decomposition:

- **"the irreducible representations of `A` are `V₁,…,Vᵣ`"** = *(each `Vⱼ` is irreducible)*
  ∧ *(every irreducible is some `Vⱼ`)* = conjunct (1) ∧ conjunct (2).
- **"any finite dimensional rep is a direct sum of copies of the `Vⱼ`"** = *(every rep is a
  direct sum of simples)* ∧ *(each simple summand is some `Vⱼ`)* = conjunct (3) combined with
  (1)–(2).

The docstring (lines 231–238) states this decomposition explicitly. This is the same
faithful "split the compound claim across named parts" pattern used and accepted in the
sibling review of Theorem 3.6.2 (independence + spanning). **FAITHFUL.**

---

## 2. The action model — `MatProd` and the `Pi.eval` projection action

- `MatProd k d = ∀ i, Matrix (Fin (d i)) (Fin (d i)) k` (line 100), with `d : Fin r → ℕ`.
  A finite product ring over the `r` factors — the canonical model of the finite direct sum
  `⊕ᵢ₌₁ʳ Mat_{dᵢ}(k)` (finite product = finite biproduct of rings). **Faithful.**
- `Vⱼ = k^{dⱼ}` modeled as `Fin (d j) → k`. **Faithful.**
- `A`-action on `Vⱼ`: `vModuleProd j = Module.compHom _ (Pi.evalRingHom … j)` (line 109),
  unfolding (via `vModuleProd_smul`, line 114) to `a • v = a j • v` — i.e. `a ∈ A` acts
  through its **`j`-th matrix component** `a j ∈ Mat_{dⱼ}(k)`, which then acts on `k^{dⱼ}` by
  the standard matrix-on-vector action. This is exactly the book's "`⊕ Mat_{dᵢ}(k)` acting on
  `k^{dⱼ}` through the `j`-th factor". **Faithful, non-vacuous** (a real `Module.compHom`
  instance, not a placeholder).

The `IsScalarTower k (MatProd k d) (Fin (d j) → k)` instance (line 117) is provided and
proved, establishing that the scalar `k`-action and the `A`-action on `Vⱼ` are compatible —
this is what lets the standard representations themselves satisfy conjunct (2)'s hypotheses
(see §4).

---

## 3. Conjunct (1) — each `Vⱼ` is simple; `NeZero`/`dⱼ = 0` handling

`isSimpleModule_vModuleProd (j : Fin r) : IsSimpleModule (MatProd k d) (Fin (d j) → k)`
(line 124), lifted from the single-factor `isSimpleModule_matrix_vecModule` (line 38: any
nonzero vector generates `k^{dⱼ}` under the matrix action) through the surjective projection
`Pi.evalRingHom … j`. This is precisely the book's "each `Vⱼ` is irreducible". **Faithful.**

**`dⱼ = 0` handling (the non-vacuity question).** The entire `section Product` carries
`variable [∀ i, NeZero (d i)]` (line 105), i.e. **every `dᵢ ≥ 1`**. This is load-bearing and
correct:

- If some `dⱼ = 0`, then `Vⱼ = k⁰ = 0`, which is **not** a simple module (a simple module is
  by definition nonzero), so conjunct (1) would be *false*, not merely vacuous. The `NeZero`
  hypothesis is therefore **necessary** for the theorem to be true, not a hidden narrowing.
- It also matches the book's implicit convention: `Mat₀(k)` is the zero ring and `k⁰` is not
  an irreducible representation, so the book's `V₁,…,Vᵣ` implicitly assume `dᵢ ≥ 1`. A factor
  with `dᵢ = 0` is the zero ring, contributes nothing, and would simply be dropped from the
  list — no loss of generality.

So `NeZero` is the faithful rendering of the book's positive-dimension assumption, and it
guarantees each `Vⱼ` is genuinely nonzero (hence conjunct (1) is non-vacuous). **Faithful.**

---

## 4. Conjunct (2) — every fin-dim simple `A`-module is some `Vⱼ`; typeclass scrutiny

`exists_iso_vModuleProd W … : ∃ j, Nonempty (W ≃ₗ[MatProd k d] (Fin (d j) → k))` (line 145).

**Existential shape.** `∃ j, Nonempty (W ≃ₗ[A] (Fin (d j) → k))` is exactly "isomorphic to
**some** `Vⱼ`" — the correct existential over the factor index, with an honest `A`-linear
isomorphism (`≃ₗ[MatProd k d]`, not merely `k`-linear or additive). The proof finds the unique
central idempotent `eᵢ = Pi.single i 1` acting as the identity on `W` (lines 160–190), shows
the `A`-action factors through the `i`-th projection (line 192), transports the single-factor
classification `matrix_simpleModule_iso_std`, and **upgrades the iso to full `A`-linearity**
(lines 225–229). **Faithful.**

**Typeclass-hypothesis scrutiny (the key non-vacuity check).** Conjunct (2) carries
`[Module k W]`, `[IsScalarTower k (MatProd k d) W]`, `[FiniteDimensional k W]`,
`[IsSimpleModule (MatProd k d) W]`. None over-restricts below the book:

- `[Module k W]` + `[IsScalarTower k A W]`: `A = ∏ Mat_{dᵢ}(k)` is a `k`-algebra, so `k`
  embeds via the structure map `k → A` (scalar matrices in each factor). **Every** genuine
  `A`-module `W` therefore acquires a canonical compatible `k`-module structure by restricting
  scalars along `k → A`, and that structure satisfies `IsScalarTower k A W` automatically. So
  these two instances do **not** exclude any `A`-module — they merely pin the (always
  available) `k`-linear structure that makes "finite `k`-dimension" meaningful. This is the
  natural "representation over `k`" setup, exactly the book's ambient framing, **not** an extra
  restriction. `IsScalarTower` is the natural compatibility `c • (a • w) = (c • a) • w`, not a
  strengthening.
- `[FiniteDimensional k W]` = the book's "finite dimensional representation". Correct.
- `[IsSimpleModule (MatProd k d) W]` = "irreducible". Correct.

**Non-vacuity of the hypothesis bundle.** The hypotheses are jointly satisfiable by a genuine
module: each standard representation `Vⱼ = Fin (d j) → k` carries all four instances
(`Module k` from `Pi`; `IsScalarTower` from the instance at line 117; `FiniteDimensional`;
`IsSimpleModule` from conjunct (1)), so conjunct (2) applied to `W = Vⱼ` non-trivially yields
`Vⱼ ≅ Vⱼ`. The premise set is not empty. **Faithful, non-vacuous.**

---

## 5. Conjunct (3) — every `A`-module is semisimple (no finiteness)

`isSemisimpleModule_of_matrixProd (X : Type*) [AddCommGroup X] [Module (MatProd k d) X] :
    IsSemisimpleModule (MatProd k d) X := inferInstance` (line 139).

**Quantifier scope.** Stated for **all** `A`-modules `X` with **no** `FiniteDimensional`
hypothesis, and — crucially — that is genuinely what is *proved*: the body is a bare
`inferInstance`, resolving through Mathlib's instance that a finite product of simple
(matrix-over-field) rings is a semisimple ring, hence *every* module over it is semisimple.
There is **no silent restriction** to finite-dimensional `X`. This is a faithful
**strengthening** of the book (which states the direct-sum claim only for finite-dimensional
reps): the book's conclusion is recovered by combining conjunct (3) with finite length, and
the simple summands are identified with the `Vⱼ` via conjuncts (1)–(2) (a simple `A`-module is
cyclic, hence finite-`k`-dimensional since `A` is, hence some `Vⱼ` by conjunct (2)). The
docstring (lines 136–138) records exactly this combination. **Faithful.**

---

## 6. Documented scope nuance — distinctness of the `Vⱼ` (not a defect)

The book lists `V₁,…,Vᵣ` as the irreducible representations, which carries the implicit
reading that they are **distinct** (pairwise non-isomorphic) iso-classes. The Lean statement
does **not** separately assert `∀ j j', j ≠ j' → IsEmpty (Vⱼ ≃ₗ[A] Vⱼ')`.

- **The fact is true here:** for `j ≠ j'`, the idempotent `eⱼ = Pi.single j 1` acts as the
  identity on `Vⱼ` but as `0` on `Vⱼ'` (the action is through the projection), so no
  `A`-linear isomorphism `Vⱼ ≃ₗ[A] Vⱼ'` can exist. (The proof of conjunct (2) already
  constructs exactly this idempotent machinery, lines 150–194.)
- **Why this is a nuance, not a defect:** conjuncts (1)–(3) fully capture the book's asserted
  content — "the irreducibles are exactly the `Vⱼ`" and "every rep is a direct sum of copies
  of the `Vⱼ`". Distinctness is a *refinement* that would make the enumeration irredundant; its
  omission does not make the statement false, vacuous, or narrower-than-the-book. It is a
  slight *under*-statement (an extra true fact left unstated), not a *mis*-statement. Per the
  issue's filing criterion (file only on "statement infidelity, hidden vacuity, or a
  hypothesis that narrows the theorem below the book"), this does not qualify. Documented here
  for completeness; **no follow-up issue.**

---

## 7. Non-vacuity witness

Concrete instance `r = 1`, `d = ![2]` (so `A = Mat₂(ℚ)`, `V = ℚ²`) verified to typecheck via
a scratch importer (`NeZero (![2] i)` instance supplied by `fin_cases`; exit 0):

```lean
instance : ∀ i : Fin 1, NeZero (![2] i) := fun i => by fin_cases i; exact ⟨by decide⟩
noncomputable example :=
  Etingof.irreducible_reps_of_matrix_algebra (k := ℚ) (r := 1) (d := ![2])
```

All three conjuncts are non-trivially witnessed at this data:

| Conjunct | Witness at `A = Mat₂(ℚ)`, `V = ℚ²` | Non-trivial? |
|---|---|---|
| (1) each `Vⱼ` simple | `ℚ²` is a genuine 2-dimensional simple `Mat₂(ℚ)`-module | yes (`d₀ = 2 ≥ 1`) |
| (2) every fin-dim simple is some `Vⱼ` | any fin-dim simple `Mat₂(ℚ)`-module `≅ ℚ²` | yes (premise met by `ℚ²` itself) |
| (3) every module semisimple | `Mat₂(ℚ)` as a module over itself is semisimple (`= ℚ² ⊕ ℚ²`) | yes (nonzero, decomposes) |

(`vModuleProd` is a `local instance`, so conjunct (1)/(2)'s *types* cannot be re-stated
outside the file; instantiating the whole theorem term, as above, exercises all three
conjuncts and confirms the statement is non-vacuous.)

---

## 8. Verdict summary

| Item | Book | Formalization | Verdict |
|---|---|---|---|
| Action model | `⊕ᵢ Mat_{dᵢ}(k)` on `k^{dⱼ}` via `j`-th factor | `MatProd` + `Pi.evalRingHom` projection action | **FAITHFUL** |
| Conjunct (1) | each `Vⱼ` irreducible | `IsSimpleModule A (Fin dⱼ → k)` | **FAITHFUL** (needs `NeZero dⱼ`, provided) |
| Conjunct (2) content | every irred is some `Vⱼ` | `∃ j, W ≃ₗ[A] (Fin dⱼ → k)` | **FAITHFUL** |
| Conjunct (2) hypotheses | fin-dim rep over `k` | `[Module k W]`+`[IsScalarTower]`+`[FinDim]`+`[Simple]` | **FAITHFUL** (natural setup, non-vacuous) |
| Conjunct (3) | fin-dim rep = ⊕ of `Vⱼ` | every `A`-module semisimple (no finiteness) | **FAITHFUL** (faithful strengthening) |
| `dⱼ = 0` handling | implicit `dᵢ ≥ 1` | `[∀ i, NeZero (dᵢ)]` | **FAITHFUL** (necessary, matches book) |
| Distinctness of `Vⱼ` | listed as distinct `V₁,…,Vᵣ` | not separately asserted (but true) | scope nuance, **not a defect** |

**Axioms:** all four public declarations `⊆ [propext, Classical.choice, Quot.sound]`. No
hidden `sorry`. **Build:** 1591 jobs, exit 0. **Concrete non-vacuous witness:** `r = 1`,
`d = ![2]` (`Mat₂(ℚ)` on `ℚ²`), typechecks.

**Action taken:** none beyond this report. **FAITHFUL** verdict; no defect, no follow-up
issue. No `.lean` edits (report-only review).
