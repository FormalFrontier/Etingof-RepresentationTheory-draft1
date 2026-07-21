# Review — Ch3 Theorem 3.6.2: Linear independence of characters (parts i & ii)

- **Issue:** #7114 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/ea7a12ee`
- **Target:** `EtingofRepresentationTheory/Chapter3/Theorem3_6_2.lean` (306 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter3/Theorem3.6.2.md` (refs `blobs/Chapter3/Theorem3.6.2.refs.md`)
- **Focus areas:** statement fidelity per book part (i)/(ii); character-definition faithfulness; quantifier / hypothesis check; target-space `(A/[A,A])*` correspondence; vacuity / hidden-`sorry` (report-only, no proof edits)
- **Overall verdict:** **Part (i): DEFECT (minor) — filed #7118.** The character definition and
  the mathematical content of both parts are faithful and axiom-clean, but part (i)
  (`characters_linearly_independent`) carries an **unnecessary `[FiniteDimensional k A]`
  hypothesis** that the book's part (i) does not have and the proof does not use, so the
  formalized statement is strictly weaker (a silent specialization of the algebra hypothesis).
  I verified the hypothesis is removable with no other change. **Part (ii): FAITHFUL.** The
  `(A/[A,A])*` target is modeled correctly as the space of tracial functionals and the theorem
  proves the spanning half; combined with part (i) this is the book's basis claim. All three
  named declarations build and are axiom-clean.

---

## 0. Build and axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter3.Theorem3_6_2` — exit 0, **1954 jobs** (Mathlib
cached). Ran `#print axioms` on the three declarations named in the issue via a scratch
importer. **Every** result is exactly `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, no custom axiom:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.character` | 30 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.characters_linearly_independent` | 40 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.characters_basis_semisimple` | 218 | `[propext, Classical.choice, Quot.sound]` |

`grep` for `sorry|admit|proof_wanted` and for `True`/placeholder bodies returns nothing.
`Etingof.character` is a `noncomputable def` with a genuine body (no sorried data). Build
emits only style/deprecation lints (`show`-should-be-`change` at lines 260/269/286,
deprecated `LinearMap.coeFn_sum` at 300, three unused-`simp`-arg hints, and an
"unused `[Fintype ι]` in type" hint on all three declarations) — none affects correctness or
fidelity.

---

## 1. Character definition — `Etingof.character` (line 30)

Book: `χ_V(a) = Tr(ρ_V(a))`, the trace of the action.

Lean:
```
noncomputable def Etingof.character (k A V) [...] [Free k V] [Module.Finite k V] : Dual k A :=
  (LinearMap.trace k V).comp (Algebra.lsmul k k V : A →ₐ[k] End k V).toLinearMap
```

`Algebra.lsmul k k V` sends `a` to the endomorphism `v ↦ a • v`, which is exactly `ρ_V(a)`
(the action of `a` on `V`). Composing with `LinearMap.trace k V` gives `a ↦ Tr(ρ_V(a))`, an
element of `Dual k A = A →ₗ[k] k`. This is a **faithful, non-vacuous** rendering of the book's
character — a real construction of the trace-of-action functional, not a placeholder. The
finiteness/freeness instances (`Module.Finite k V`, `Free k V`) are the correct
"finite-dimensional representation" hypotheses and are genuinely required for the trace to be
well-behaved. **FAITHFUL.**

---

## 2. Part (i) — `characters_linearly_independent` (line 40)

Book, Theorem 3.6.2(i): *Characters of (distinct) irreducible finite-dimensional
representations of `A` are linearly independent.*

Lean: for a finite family `V : ι → Type*`, each `IsSimpleModule A (V i)` and
`FiniteDimensional k (V i)`, pairwise non-isomorphic
(`h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)`), concludes
`LinearIndependent k (fun i => Etingof.character k A (V i))`.

**Faithful aspects.** The conclusion — `LinearIndependent k` of the characters — is the exact
book claim, with the right quantifier shape. The "distinct irreducibles" hypothesis is genuinely
present and load-bearing: `h_noniso` (pairwise non-isomorphism) plus `IsSimpleModule A (V i)`
encode "distinct irreducible", and the proof uses `h_noniso` through the density theorem
(`density_theorem_part2`) to build a target endomorphism tuple that isolates each `V i` — the
density-theorem argument the book gives. `FiniteDimensional k (V i)` correctly encodes "finite
dimensional representations". `IsAlgClosed k` is **not** a silent over-specialization: the whole
Ch3 density-theorem machinery this proof invokes is stated over an algebraically closed field in
the book, so it faithfully matches the book's ambient hypothesis for this theorem.

**DEFECT (minor, filed #7118).** The signature also carries `[FiniteDimensional k A]` (line 41).
The book's part (i) holds for an **arbitrary** algebra `A` — it never assumes `A` finite
dimensional; only the *representations* need be finite dimensional. The proof here does not use it
either: `Etingof.density_theorem_part2` (`Chapter3/Theorem3_2_2.lean:49`) assumes only
`FiniteDimensional k (V i)` and `IsAlgClosed k`, never `FiniteDimensional k A`. I confirmed
empirically that **deleting `[FiniteDimensional k A]` from the signature and rebuilding compiles
cleanly (1954 jobs, exit 0) with no other change** — the hypothesis is genuinely unused. As
stated, the formalized part (i) is therefore **strictly weaker than the book's part (i)** (a
silent specialization of the algebra hypothesis to finite-dimensional `A`). This is the one
checklist item — "no silent specialization of the field or algebra hypotheses" — that fails.

Severity is minor: the statement is true, non-vacuous, and a genuine special case of the book's
claim; the fix is a one-line signature change (drop the instance argument). Filed as **#7118**
with the verification recipe.

---

## 3. Part (ii) — `characters_basis_semisimple` (line 218)

Book, Theorem 3.6.2(ii): *If `A` is a finite-dimensional semisimple algebra, then these
characters form a basis of `(A/[A,A])*`.*

Lean: under `IsSemisimpleRing A`, `FiniteDimensional k A`, `IsAlgClosed k`, `h_noniso`, and
`h_complete` (every finite-dimensional simple `A`-module is isomorphic to some `V i`), proves
```
∀ f : Dual k A, (∀ a b, f (a * b) = f (b * a)) →
  f ∈ Submodule.span k (Set.range (fun i => Etingof.character k A (V i)))
```

**Target space `(A/[A,A])*`.** A functional `f : A →ₗ[k] k` with `f(ab) = f(ba)` is exactly one
that vanishes on every commutator `ab − ba`, i.e. on `[A,A]`, hence descends to `A/[A,A]`; the
space of such tracial functionals is canonically `(A/[A,A])*`. Modeling `(A/[A,A])*` as
`{f : Dual k A | ∀ a b, f(ab) = f(ba)}` is a **faithful, standard reformulation** — it avoids
constructing the quotient and its dual explicitly while capturing precisely the same space.

**"Basis" via spanning + part (i).** Each character `χ_{V i}` is itself tracial
(`Tr(ρ(ab)) = Tr(ρ(a)ρ(b)) = Tr(ρ(b)ρ(a)) = Tr(ρ(ba))`), so the `χ_{V i}` live in this space.
This theorem proves they **span** it (every tracial `f` is in their span, via `ρ` being a
`k`-algebra isomorphism `A ≅ ∏ End(V i)` — surjective by density, injective by
`rep_map_injective_of_semisimple` — and every tracial functional on a matrix-endomorphism factor
being a scalar multiple of the trace, `tracial_of_end_eq_scalar_trace`, the book's matrix-unit
argument). Linear independence is part (i). Spanning + independence = basis, exactly the book's
conclusion. The formalization **splits** the "basis" claim across the two theorems (independence
in part (i), spanning here) rather than bundling a single `Basis` object; the docstring states
this ("Combined with part (i), this gives a basis"). This is a faithful decomposition, not a gap.

**Hypotheses.** `IsSemisimpleRing A` + `FiniteDimensional k A` = "finite-dimensional semisimple
algebra" (book). `h_complete` correctly pins "these characters" to the *complete* set of
irreducibles (the book's "these characters" = characters of all irreducibles). `IsAlgClosed k`
matches the book's ambient setting (the `A ≅ ∏ Mat_{d_i}(k)` decomposition and the
scalar-multiple-of-trace step both use it). No silent specialization here — every hypothesis
corresponds to the book's stated conditions. **FAITHFUL.**

---

## 4. Verdict summary

| Item | Book | Formalization | Verdict |
|---|---|---|---|
| `Etingof.character` | `χ_V(a) = Tr(ρ_V(a))` | `trace ∘ lsmul` | **FAITHFUL** (real, non-vacuous) |
| Part (i) content | lin. indep. of distinct irred. chars | `LinearIndependent k (χ ∘ V)` | faithful content |
| Part (i) hypotheses | arbitrary `A` | extra `[FiniteDimensional k A]` (unused) | **DEFECT (minor) → #7118** |
| Part (ii) target `(A/[A,A])*` | dual of `A/[A,A]` | tracial functionals on `A` | **FAITHFUL** |
| Part (ii) claim | chars form a basis | chars span tracial space (+ part i) | **FAITHFUL** (split, documented) |

**Axioms:** all three declarations `⊆ [propext, Classical.choice, Quot.sound]`. No hidden
`sorry`. **Build:** 1954 jobs, exit 0.

**Action taken:** filed **#7118** (feature) to drop the unnecessary `[FiniteDimensional k A]`
hypothesis on part (i). No `.lean` edits in this report-only review (the experimental removal was
reverted after confirming it compiles).
