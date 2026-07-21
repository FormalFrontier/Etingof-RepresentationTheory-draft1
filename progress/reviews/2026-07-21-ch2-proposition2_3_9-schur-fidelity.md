# Review — Ch2 Proposition 2.3.9: Schur's Lemma (parts i & ii)

- **Issue:** #7128 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/cb484ae6`
- **Target:** `EtingofRepresentationTheory/Chapter2/Proposition2_3_9.lean` (39 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter2/Proposition2.3.9.md`
- **Focus areas:** statement fidelity of both parts against the book's asymmetric statement;
  the `Ring R` / `Module R Vᵢ` framing vs. the book's "representation of an algebra over a field";
  the hypothesis asymmetry (`[IsSimpleModule R V₁]` on part i, `[IsSimpleModule R V₂]` on part ii);
  the implicit "both irreducible ⇒ iso" corollary; vacuity / hidden-`sorry`-via-axiom check
  (report-only, no `.lean` edits).
- **Overall verdict:** **FAITHFUL.** Both public results
  (`Etingof.Proposition_2_3_9_injective`, `Etingof.Proposition_2_3_9_surjective`) are correct
  transcriptions of Etingof Proposition 2.3.9(i) and (ii). The `Ring R` / `Module R Vᵢ` framing is
  a **faithful generalization** of "representation of an algebra over a field" (it recovers the
  book statement verbatim on `R = A`), the hypothesis asymmetry is exactly right (source simple ⇒
  injective, target simple ⇒ surjective), the file builds (exit 0, 1399 jobs), and both
  declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). **No
  defect filed.** Two benign nuances are recorded and dispositioned below (the implicit iso
  corollary; the "Exact match" docstring wording).

---

## 0. Build and axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter2.Proposition2_3_9` (exit 0, **1399 jobs**).
`#print axioms` on both declarations:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.Proposition_2_3_9_injective` | 21 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Proposition_2_3_9_surjective` | 30 | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no custom axiom. `grep` for `sorry`/`admit`/`proof_wanted` and for `True`/`by trivial`
placeholders returns nothing. Both are `theorem`s (not `def`s), so there is no data body to
construct; the proofs are genuine one-line delegations to Mathlib (see §3).

---

## 1. Statement fidelity

**Book (Proposition 2.3.9, Schur's lemma):** "Let `V₁, V₂` be representations of an algebra `A`
over any field `F` (which need not be algebraically closed). Let `φ : V₁ → V₂` be a nonzero
homomorphism of representations. Then: (i) If `V₁` is irreducible, `φ` is injective. (ii) If `V₂` is
irreducible, `φ` is surjective. Thus, if both `V₁` and `V₂` are irreducible, `φ` is an isomorphism."

**Lean:**
```lean
theorem Etingof.Proposition_2_3_9_injective
    {R : Type*} [Ring R]
    {V₁ : Type*} [AddCommGroup V₁] [Module R V₁] [IsSimpleModule R V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module R V₂]
    (φ : V₁ →ₗ[R] V₂) (hφ : φ ≠ 0) : Function.Injective φ

theorem Etingof.Proposition_2_3_9_surjective
    {R : Type*} [Ring R]
    {V₁ : Type*} [AddCommGroup V₁] [Module R V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module R V₂] [IsSimpleModule R V₂]
    (φ : V₁ →ₗ[R] V₂) (hφ : φ ≠ 0) : Function.Surjective φ
```

Point-by-point against the deliverables in #7128:

1. **Irreducible representation = `IsSimpleModule`.** A representation of an algebra `A` is an
   `A`-module; an *irreducible* representation is precisely a simple `A`-module — one with no proper
   nonzero subrepresentations, i.e. `IsSimpleModule A V`. The book's proof works entirely through
   subrepresentations (kernel is a subrep ≠ V₁ ⇒ 0; image is a subrep ≠ 0 ⇒ V₂), which is exactly
   the submodule-lattice content of `IsSimpleModule`. Faithful. ✔

2. **Hom of representations = `→ₗ[R]`.** A homomorphism of representations of `A` is an `A`-linear
   map, `V₁ →ₗ[A] V₂`. The formalization's `φ : V₁ →ₗ[R] V₂` is exactly this (with `R = A`). "`φ`
   nonzero" is `hφ : φ ≠ 0`. Faithful. ✔

3. **Hypothesis asymmetry — correct.** Part (i) hypothesizes `[IsSimpleModule R V₁]` (the **source**)
   and concludes injectivity; part (ii) hypothesizes `[IsSimpleModule R V₂]` (the **target**) and
   concludes surjectivity. This matches the book's asymmetric statement — (i) needs `V₁` irreducible,
   (ii) needs `V₂` irreducible — and matches the exact instance requirements of the underlying
   Mathlib lemmas (see §3). Neither part carries the other's simplicity hypothesis. ✔

4. **Conclusions.** `Function.Injective φ` / `Function.Surjective φ` are the literal book conclusions
   "φ is injective" / "φ is surjective". No specialization or weakening. ✔

---

## 2. The `Ring R` / `Module R` framing vs. "representation of an algebra over a field"

The one framing question the issue asks to adjudicate explicitly.

**Book setting:** `V₁, V₂` are representations of an `F`-algebra `A`, `F` an arbitrary field. **Lean
setting:** `R` an arbitrary `Ring`, `Vᵢ` arbitrary `R`-modules.

**Disposition: faithful generalization (strictly stronger, recovers the book verbatim).**

- A representation of an `F`-algebra `A` *is* an `A`-module, and the category of representations of
  `A` is exactly the category of `A`-modules with `A`-linear maps. So the book's setting is the
  special case `R = A` of the Lean setting where `R` additionally happens to be an `F`-algebra.
- Schur's lemma in the two forms proved here (nonzero hom out of a simple module is injective;
  nonzero hom into a simple module is surjective) holds for modules over **any** ring — the
  `F`-algebra structure is never used; only the submodule lattice of a simple module matters. The
  generalization from "`A` an `F`-algebra" to "`R` any ring" is therefore sound.
- Instantiating the Lean theorems at `R = A` (any `F`-algebra `A` — e.g. `A = MonoidAlgebra F G`, or
  `A = F` itself) recovers the printed statement with **no loss**. This is the same
  algebra-over-field ⇝ arbitrary-ring generalization pattern accepted as FAITHFUL in the sibling
  flagship audits (Ch3 Theorem 3.5.4, Ch2 Theorem 2.1.1).

Not a defect, and not a mere convention variance: it is a genuine strengthening that is nonetheless
a faithful rendering because it specializes back exactly.

---

## 3. Non-vacuity of the proofs and of the hypotheses

**Proofs are genuine one-line delegations to exactly-matching Mathlib lemmas** (not vacuous or
circular):

```lean
Proposition_2_3_9_injective  := LinearMap.injective_of_ne_zero hφ
Proposition_2_3_9_surjective := LinearMap.surjective_of_ne_zero hφ
```

The Mathlib signatures line up instance-for-instance with the book's asymmetry:

```
@LinearMap.injective_of_ne_zero  : … [IsSimpleModule R M] {f : M →ₗ[R] N}, f ≠ 0 → Injective ⇑f
@LinearMap.surjective_of_ne_zero : … [IsSimpleModule R N] {f : M →ₗ[R] N}, f ≠ 0 → Surjective ⇑f
```

i.e. `injective_of_ne_zero` demands simplicity of the **source** `M` and `surjective_of_ne_zero`
demands simplicity of the **target** `N` — precisely mirroring the file's `[IsSimpleModule R V₁]`
(part i) and `[IsSimpleModule R V₂]` (part ii). These Mathlib lemmas are the direct formal
counterparts of the book's own proof (kernel/image is a subrepresentation, killed by simplicity), so
the delegation is faithful, not a lucky coincidence of a stronger black box.

**Hypotheses are satisfiable (theorems not vacuously true).** `IsSimpleModule` is instantiable: the
witness `example : IsSimpleModule ℚ ℚ := inferInstance` compiles (a field is a simple module over
itself), and more generally every division ring is a simple module over itself and every nonzero
finite-dimensional irreducible representation supplies one. So there exist `R, V₁, V₂, φ ≠ 0`
meeting the premises; the results are not vacuously satisfied by an unsatisfiable hypothesis.

---

## 4. Recorded nuances (both benign)

**(a) The "both irreducible ⇒ iso" corollary is left implicit.** The book appends "Thus, if both
`V₁` and `V₂` are irreducible, `φ` is an isomorphism." The file formalizes only the two parts. This
omission does **not** matter: an injective *and* surjective `R`-linear map is bijective, and a
bijective `R`-linear map is an `R`-linear isomorphism (`LinearEquiv.ofBijective`). The corollary is
a one-line combination of the two formalized parts — the full mathematical content of the
proposition is present; only the trivial packaging into an explicit `≃ₗ` is absent. Not a defect;
noted for completeness. (A future coverage item could add
`Etingof.Proposition_2_3_9_bijective`/`_equiv` under `[IsSimpleModule R V₁] [IsSimpleModule R V₂]`,
but it carries no new content.)

**(b) Module-comment wording "Exact match".** The `## Mathlib correspondence` block says "Exact
match." Strictly, the formalization is a faithful *generalization* (arbitrary ring, not
algebra-over-field) rather than a literal transliteration — §2 shows this is benign and equally
faithful. The docstring is a documentation nicety, not a correctness issue, and the issue scopes
this review to report-only with no `.lean` edits, so the wording is left as-is and the precise
relationship is recorded here.

---

## 5. Verdict

**FAITHFUL.** `Etingof.Proposition_2_3_9_injective` and `Etingof.Proposition_2_3_9_surjective`
correctly formalize Etingof Proposition 2.3.9(i) and (ii): the correct hypothesis asymmetry (source
simple ⇒ injective, target simple ⇒ surjective), genuine `Injective`/`Surjective` conclusions, and
proofs that delegate to the exactly-matching Mathlib lemmas encoding the book's own subrepresentation
argument. The `Ring R` / `Module R` framing is a faithful generalization of "representation of an
algebra over a field" that recovers the book statement verbatim on `R = A`. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorry`), 1399-job build, hypotheses satisfiable (not
vacuous). The two nuances — the implicit iso corollary and the "Exact match" docstring — are benign.
**No defect issue filed.**
