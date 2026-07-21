# Review — Ch3 Theorem 3.5.4: Structure of finite dimensional algebras modulo radical

- **Issue:** #7124 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/161bfaa0`
- **Target:** `EtingofRepresentationTheory/Chapter3/Theorem3_5_4.lean` — `Etingof.structure_mod_radical`, sorry-free on `main`
- **Direct dependencies:** `Definition3_5_1.lean` (`Etingof.Radical`), `Theorem3_2_2.lean` (`density_theorem_part2`), `Proposition3_5_3.lean`
- **Fidelity reference:** `blobs/Chapter3/Theorem3.5.4.md` (statement + proof), `blobs/Chapter3/Theorem3.5.4.refs.md`
- **Focus areas (per issue):** finiteness encoding, product-vs-direct-sum, added `IsAlgClosed` hypothesis, `Radical` definition fidelity; non-vacuity; axiom-cleanliness (report-only, no `.lean` proof/statement edits)

- **Overall verdict:** **FAITHFUL (isomorphism), with one documented coverage gap.**
  The isomorphism `A / Rad(A) ≅ ∏ᵢ End_k(Vᵢ)` — the mathematical core of Theorem 3.5.4 —
  is a faithful, non-vacuous, axiom-clean formalization (subset of
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). The one honest shortfall is
  that the book's Theorem 3.5.4 asserts **two** things — (a) *A has only finitely many
  irreducibles up to iso* and (b) the isomorphism — and the Lean declaration formalizes
  **only (b)**, taking clause (a) as a hypothesis (`[Fintype ι]` + `h_complete`) rather than
  proving it. Clause (a) — the book's `r ≤ dim A` bound — is **nowhere** established in the
  repo; the whole 3.5 cluster (this theorem, Corollary 3.5.5, Proposition 3.5.8) consistently
  parameterizes by a finite complete family. This is a coverage gap, **not** a falsehood or a
  vacuity: everything stated is correct and non-vacuous. **No DEFECT filed** (nothing stated
  is wrong). A low-priority `feature` follow-up (§5) is filed to track the missing finiteness
  lemma, since the book explicitly proves it.

---

## 0. Build and axiom-cleanliness audit

`lake build EtingofRepresentationTheory.Chapter3.Theorem3_5_4` — exit 0, **1957 jobs**.

`#print axioms Etingof.structure_mod_radical`:

```
'Etingof.structure_mod_radical' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no custom axiom. The declaration is axiom-clean. (Two style linter warnings on
the file — an unused-`Fintype` note on `density_theorem_part2` and a `show`-vs-`change`
suggestion at `Theorem3_5_4.lean:67` — are cosmetic, not correctness or fidelity issues.)

---

## 1. Finiteness claim — the central concern

**Book (clause a):** *"A finite dimensional algebra A has only finitely many irreducible
representations Vᵢ up to an isomorphism. These representations are finite dimensional."* The
book **proves** this: for pairwise-nonisomorphic irreducibles `V₁,…,V_r`, Theorem 3.2.2 makes
`⊕ρᵢ : A → ⊕ End Vᵢ` surjective, so `r ≤ ∑ dim End Vᵢ ≤ dim A` — finiteness with an explicit
bound.

**Lean encoding.** `structure_mod_radical` takes a family `V : ι → Type u` with `[Fintype ι]`,
`h_noniso` (pairwise non-iso), and `h_complete` (every finite-dimensional simple `A`-module is
`≃ₗ[A]` some `V i`). So the finite index `ι` is a **hypothesis**, not a conclusion.

**Assessment.** Parameterizing by a finite complete family is a faithful and standard encoding
of the *isomorphism* clause (b): "list the finitely many irreducibles as `V i`, then
`A/Rad ≅ ∏ End Vᵢ`." It is a genuine, unconditional statement about `A` in the following sense —
for a fixed `A`, it holds for *every* such family, and (§4) such a family provably exists for
every finite-dimensional `A`. What it does **not** do is discharge clause (a): the theorem
never proves that a finite complete family exists, i.e. that `A` has only finitely many
irreducibles. That finiteness is **genuinely assumed** via `[Fintype ι]`.

I checked whether the finiteness is discharged elsewhere: it is not. `grep` across
`Chapter3/` finds no `r ≤ dim A` / "finitely many irreducibles" existence lemma. Corollary
3.5.5 (`Corollary3_5_5.lean`) and Proposition 3.5.8 (`Proposition3_5_8.lean`) — the downstream
consumers — take the *same* `[Fintype ι]` + `h_complete` package as their own hypothesis. So
the finiteness half of Theorem 3.5.4 is systematically presupposed throughout the 3.5 cluster
and never formalized.

Consequence for fidelity: the isomorphism (the "≅" line of the book statement) is faithful;
the prose clause "has only finitely many irreducible representations up to isomorphism" is
**not** formalized. This is a partial-coverage note, not a misstatement (the Lean theorem does
not *claim* to prove finiteness, so it cannot misstate it). Tracked as a follow-up (§5).

The "finite dimensional" part of clause (a) *is* honored: `[∀ i, FiniteDimensional k (V i)]`
is required, matching "these representations are finite dimensional."

---

## 2. Product vs. direct sum, and `End Vᵢ`

**Book codomain:** `⊕ᵢ End Vᵢ`. **Lean codomain:** `∀ i, Module.End k (V i)` (dependent
product), with `[Fintype ι]`.

- **∏ = ⊕ for finite index.** Over a `Fintype ι`, the finite product and finite direct sum of
  algebras coincide — same underlying `∀ i, ...` carrier, same componentwise ring/algebra
  structure. So `∀ i, Module.End k (V i)` is exactly the book's `⊕ᵢ End Vᵢ` as a `k`-algebra.
  Faithful. (The algebra hom into it is `Pi.algHom`, componentwise, as expected.)
- **`Module.End k (V i)` = `End Vᵢ`.** `Module.End k (V i)` is the `k`-linear endomorphism
  algebra of `Vᵢ`. This matches the book's `End Vᵢ` in this section, where `End` is taken over
  the ground field `k` — consistent with Theorem 3.2.2's codomain `End k V` (all `k`-linear
  maps), which this proof invokes. (By density each `End_k(Vᵢ) ≅ Mat_{dim Vᵢ}(k)`, the matrix
  form named in the refs, but the statement's `Module.End k` form is the faithful literal
  rendering of `End Vᵢ`.) Faithful.

---

## 3. The `IsAlgClosed k` hypothesis

The Lean statement requires `[IsAlgClosed k]`; the one-line book statement of 3.5.4 does not
print it. This is **not** an added-strength fidelity gap:

- **Required by the invoked density theorem.** The proof discharges surjectivity of `φ` via
  `Etingof.density_theorem_part2`, whose signature carries `[IsAlgClosed k]` (Theorem 3.2.2 (ii)).
  Both parts of 3.2.2 need algebraic closure (via
  `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` — Schur over `k̄` giving
  `End_A(Vᵢ) = k`). The book's proof of 3.5.4 *explicitly* cites Theorem 3.2.2, so it inherits
  that theorem's standing hypothesis.
- **Required by the `⊕ End Vᵢ` form itself.** The clean statement `A/Rad ≅ ⊕ End_k Vᵢ` (with
  `End` over `k`, no division rings) is only correct when `End_A(Vᵢ) = k`, i.e. over an
  algebraically closed field. Over a general field the Wedderburn form is
  `⊕ End_{D_i}(Vᵢ)` with division rings `D_i` (refs: Wedderburn–Artin). So `IsAlgClosed` is
  part of the book's *ambient* Chapter 3 setting, silently carried by the `End Vᵢ` notation,
  not an extra restriction the formalization invents.
- **Consistent with 3.2.2.** The density theorem the issue points to for comparison states
  `IsAlgClosed` explicitly; 3.5.4 doing the same is the consistent, honest choice — it surfaces
  a hypothesis the book keeps implicit rather than hiding it.

Verdict: faithful; `IsAlgClosed` is a made-explicit standing assumption, not a strengthening.

---

## 4. `Etingof.Radical` fidelity, and non-vacuity

**`Radical` definition.** `Definition3_5_1.lean`: `Etingof.Radical A := Ideal.jacobson ⊥`
(the Jacobson radical = intersection of maximal left ideals). Book Definition 3.5.1 defines
`Rad(A)` as *the elements acting by 0 in all irreducible representations of A*. For a
finite-dimensional (semiprimary) algebra these coincide, and the proof of 3.5.4 itself
**establishes exactly that coincidence** in the relevant sense:

- `hrad_le_ker`: every `a ∈ Ideal.jacobson ⊥` annihilates each simple `V i`
  (`IsSemisimpleModule.jacobson_le_annihilator`) — i.e. Jacobson ⊆ "acts by 0 on irreducibles."
- `hker_le_rad`: every `a` annihilating all `V i` lies in every maximal left ideal `J` (each
  `A/J` is simple, hence `≅` some `V j` by `h_complete`, on which `a` acts as 0, forcing
  `a ∈ J`) — i.e. "acts by 0 on irreducibles" ⊆ Jacobson.

So `RingHom.ker φ = Radical A` (`hker_eq`), and `ker φ` is precisely "acts by 0 on all the
irreducibles" — Definition 3.5.1's `Rad(A)` verbatim. The Mathlib `Ideal.jacobson ⊥` carrier
is thus a faithful stand-in, and the equivalence to the book's definition is discharged inside
the theorem rather than assumed. Faithful.

**Non-vacuity.** All hypotheses (`FiniteDimensional`, `Fintype ι`, `h_noniso`, `h_complete`,
per-`i` simplicity/finite-dim) are jointly satisfiable with a non-trivial conclusion:

- `A = Mat_d(k)` (`k` algebraically closed): the unique irreducible is the column module
  `k^d`, so `ι = Unit`, `V () = k^d`; `h_noniso` holds trivially and `h_complete` holds (one
  simple class). `Rad(A) = 0`, so the conclusion is `Mat_d(k) ≅ End_k(k^d) = Mat_d(k)` — a
  genuine (non-degenerate) iso onto the full matrix algebra.
- `A = k`: `ι = Unit`, `V () = k`, `Rad = 0`, conclusion `k ≅ End_k(k) = k`.

Both instantiate every hypothesis with the conclusion a non-trivial isomorphism, so the
theorem is not vacuously true. (This also concretely witnesses the existence of a finite
complete family for these `A`, the clause-(a) content that §1/§5 note is not proved in
general.)

---

## 5. Follow-up filed

- **`feature` (low priority) — the finiteness half of Theorem 3.5.4 is unformalized.** The
  book's clause (a), "A has only finitely many irreducibles up to isomorphism"
  (`r ≤ dim A`), is currently a *hypothesis* (`[Fintype ι]` + `h_complete`) everywhere in the
  3.5 cluster and is nowhere proved. A faithful full rendering of 3.5.4 would add a standalone
  lemma establishing existence of a finite complete family for any finite-dimensional `A` over
  algebraically closed `k` — e.g. that the isomorphism classes of finite-dimensional simple
  `A`-modules are finite with cardinality `≤ finrank k A` — from which `[Fintype ι]` +
  `h_complete` are derivable rather than assumed. Filed as **#7127** (`feature`, low priority).
  Not a DEFECT: the existing isomorphism statement is faithful and non-vacuous; this is missing
  coverage, not an error.

## 6. Scope notes

- Report-only: **no `.lean` statement or proof changed.** The scratch `#print axioms` file used
  for §0 was created under `EtingofRepresentationTheory/` and removed; the only tree change is
  this writeup under `progress/reviews/`.
- Downstream `Corollary3_5_5` / `Proposition3_5_8` were read only to confirm the finiteness
  encoding is uniform; their own fidelity was not audited here.
