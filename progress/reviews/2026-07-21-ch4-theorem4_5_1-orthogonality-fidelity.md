# Review — Ch4 Theorem 4.5.1: First orthogonality relation for characters

- **Issue:** #7158 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/80ed00ec`
- **Target:** `EtingofRepresentationTheory/Chapter4/Theorem4_5_1.lean` (47 lines), sorry-free on `main`
- **Underlying Mathlib lemmas:** `FDRep.scalar_product_char_eq_finrank_equivariant`,
  `FDRep.char_orthonormal` (both in `Mathlib/RepresentationTheory/Character.lean`),
  with the fidelity link supplied by `FDRep.char_dual`
  (`(of (dual V.ρ)).character g = V.character g⁻¹`).
- **Fidelity reference:** `blobs/Chapter4/Theorem4.5.1.md` (statement + projector proof).
- **Focus areas:** statement fidelity of part (i) (the `g⁻¹`-vs-conjugate question and the
  `Hom_G` RHS); statement fidelity of part (ii) (Kronecker delta, `[IsAlgClosed k]`);
  non-vacuity; axiom cleanliness; and confirmation that the two cited lemmas prove the
  stated conclusion rather than a weaker restatement.
- **Overall verdict:** **FAITHFUL** (two declarations). No defect; no follow-up issue filed.
  Both `Etingof.Theorem4_5_1_i` and `Etingof.Theorem4_5_1_ii` faithfully render the book's
  first orthogonality relation. The `W.character g⁻¹` factor is the exact field-agnostic
  generalization of the book's complex conjugate `χ_W(g)-bar = χ_{W*}(g)`; the RHS
  `Module.finrank k (W ⟶ V)` is genuinely `dim_k Hom_G(W, V)`; the `if Nonempty (V ≅ W)`
  form is the faithful Kronecker delta; and `[IsAlgClosed k]` is the expected (Schur-driven)
  faithful rendering of the book's "over ℂ" setting, not an unstated strengthening. Both
  declarations build and are axiom-clean (no `sorryAx`).

---

## 0. Build and axiom-cleanliness audit

`lake exe cache get` then `lake build EtingofRepresentationTheory.Chapter4.Theorem4_5_1`
exits 0 (8580 jobs).

`#print axioms` for both declarations:

```
'Etingof.Theorem4_5_1_i'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.Theorem4_5_1_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Clean — the standard classical trio, no `sorryAx`, no custom axioms.

---

## 1. Statement fidelity of part (i)

**Lean (`Etingof.Theorem4_5_1_i`):**

```
{k G : Type u} [Field k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
(V W : FDRep k G) :
  ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ = Module.finrank k (W ⟶ V)
```

proved by `exact scalar_product_char_eq_finrank_equivariant W V`.

**Book:** `(χ_V, χ_W) = dim Hom_G(W, V)` for any representations `V, W`, where
`(χ_V, χ_W) = 1/|G| ∑_g χ_V(g) χ_W(g)-bar`.

### 1a. LHS: `⅟|G| • ∑_g χ_V(g)·χ_W(g⁻¹)` vs `1/|G| ∑_g χ_V(g)·χ_W(g)-bar`

- **Averaging scalar.** `⅟(Fintype.card G : k)` is the two-sided inverse of `|G|` provided by
  the `[Invertible (Fintype.card G : k)]` instance, the field-agnostic form of `1/|G|`. Over ℂ
  (char 0) this is literally `1/|G|`. Faithful.
- **The `g⁻¹` question (key point).** The book's second factor is the complex conjugate
  `χ_W(g)-bar`, and the book *itself* rewrites it as `χ_{W*}(g)` (character of the dual). The
  standard identity is `χ_{W*}(g) = χ_W(g⁻¹)`, which Mathlib records exactly as
  `FDRep.char_dual : (of (dual V.ρ)).character g = V.character g⁻¹`. So Lean's
  `W.character g⁻¹` **is** `χ_{W*}(g)`, i.e. the book's `χ_W(g)-bar` after the book's own first
  rewrite. Over ℂ with a `G`-invariant Hermitian form, `χ_W(g)-bar = χ_W(g⁻¹)` because each
  `ρ_W(g)` is conjugate to a unitary, so its eigenvalues are roots of unity and
  `conj(eigenvalue) = eigenvalue⁻¹`; summing gives `conj(Tr ρ_W(g)) = Tr ρ_W(g⁻¹)`. Thus
  `g⁻¹` is the correct field-agnostic generalization of the conjugate: it makes the statement
  meaningful over any field (where "conjugation" has no meaning) while agreeing with the book
  over ℂ. **Faithful, and this is the mathematically right choice.**

### 1b. RHS: `Module.finrank k (W ⟶ V)` vs `dim Hom_G(W, V)`

- `(W ⟶ V)` is the categorical Hom in `FDRep k G`; morphisms there are exactly the
  `G`-equivariant `k`-linear maps `W → V` (intertwiners). `Module.finrank k (W ⟶ V)` is its
  `k`-dimension. This is precisely the book's `dim Hom_G(W, V)`. Faithful.
- **Direction check.** The book's derivation gives `(χ_V, χ_W) = dim(V ⊗ W*)^G = dim Hom_G(W, V)`
  (note the asymmetry: `χ_V` first, `χ_{W*}` second ⟹ `Hom_G(W, V)`). Lean's LHS has
  `V.character g` as the first factor and `W.character g⁻¹` as the second, and the RHS is
  `(W ⟶ V)` = `Hom_G(W, V)`. The asymmetry matches exactly.

### 1c. The cited lemma proves the stated conclusion (not a weaker restatement)

`scalar_product_char_eq_finrank_equivariant (V W : FDRep k G)` has conclusion
`⅟|G| • ∑_g W.character g * V.character g⁻¹ = finrank k (V ⟶ W)`. Instantiated at `(W, V)`
(the Lean proof term `scalar_product_char_eq_finrank_equivariant W V` swaps the roles), it
becomes `⅟|G| • ∑_g V.character g * W.character g⁻¹ = finrank k (W ⟶ V)` — syntactically the
project's stated goal. The Mathlib proof genuinely runs through `char_linHom` +
`average_char_eq_finrank_invariants` + `invariantsEquivFDRepHom` (the projector/invariants
argument, matching the book's `P = 1/|G| ∑ g` projector onto invariants), so it establishes the
real content, not a definitional shortcut. **No simplicity hypothesis** — part (i) is stated and
proved for arbitrary `V, W`, exactly as the book's "for any representations."

---

## 2. Statement fidelity of part (ii)

**Lean (`Etingof.Theorem4_5_1_ii`):**

```
{k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
(V W : FDRep k G) [Simple V] [Simple W] :
  ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
    if Nonempty (V ≅ W) then (1 : k) else (0 : k)
```

proved by `exact char_orthonormal V W`.

**Book:** for `V, W` irreducible, `(χ_V, χ_W) = 1` if `V ≅ W`, else `0`.

- **`Simple V/W` = irreducible.** In `FDRep k G`, `Simple V` is the categorical simplicity of
  the object, i.e. no nonzero proper subrepresentation — the standard meaning of "irreducible."
  Faithful.
- **Kronecker delta.** `if Nonempty (V ≅ W) then (1 : k) else (0 : k)` is the two-case
  `δ`: value `1` exactly when there exists an isomorphism of representations `V ≅ W`, else `0`.
  `Nonempty (V ≅ W)` is the correct "`V ≅ W`" predicate (existence of a `G`-equivariant iso).
  Faithful.
- **`[IsAlgClosed k]` (assessed).** This is the expected and necessary faithful rendering of the
  book's ℂ setting, **not** an unstated strengthening. The delta form is proved (in
  `char_orthonormal`) by rewriting the RHS of part (i) via `finrank_hom_simple_simple`, which is
  Schur's lemma: over an algebraically closed field `dim Hom_G(W, V)` is `1` (iso) or `0`
  (non-iso). Over a non-closed field the endomorphism algebra of a simple can be a division
  algebra of dimension > 1, so `dim Hom_G(V, V) ≥ 1` may exceed `1` and the clean `0/1`
  dichotomy fails. Algebraic closure is genuinely required; the book obtains it for free by
  working over ℂ. Documented as expected, no defect.
- **The cited lemma proves the stated conclusion.** `char_orthonormal (V W) [Simple V] [Simple W]`
  has conclusion identical to the project statement (`↑1`/`↑0` are `(1 : k)`/`(0 : k)`), and its
  Mathlib proof reduces through part (i) + `finrank_hom_simple_simple` + `Iso.nonempty_iso_symm`.
  Genuine, not a weaker restatement.

---

## 3. Non-vacuity

Both statements were instantiated at `k = ℂ` (algebraically closed, char 0 ⟹ `|G|` invertible)
and an arbitrary nontrivial finite group `G`; the instantiation typechecks (exit 0):

```lean
open scoped Classical
variable {G : Type} [Group G] [Fintype G] [Invertible (Fintype.card G : ℂ)]

example (V W : FDRep ℂ G) :
    ⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g * W.character g⁻¹ =
    Module.finrank ℂ (W ⟶ V) := Etingof.Theorem4_5_1_i V W

example (V W : FDRep ℂ G) [Simple V] [Simple W] :
    ⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g * W.character g⁻¹ =
    if Nonempty (V ≅ W) then (1 : ℂ) else (0 : ℂ) := Etingof.Theorem4_5_1_ii V W
```

- Part (i) has no simplicity hypothesis, so it is non-vacuous for every `V, W`.
- Part (ii)'s `[Simple V] [Simple W]` premise is satisfiable: every finite group has the trivial
  1-dimensional representation, which is simple; and `[IsAlgClosed ℂ]` /
  `[Invertible (Fintype.card G : ℂ)]` both hold. So the hypotheses are jointly satisfiable and the
  statement is non-vacuous. Taking `V = W = trivial` even realizes the `then`-branch (value `1`).

---

## 4. Verdict

**FAITHFUL.** Both declarations faithfully render Etingof Theorem 4.5.1:

- Part (i): `⟨χ_V, χ_W⟩ = dim_k Hom_G(W, V)` for all `V, W`, with `W.character g⁻¹` the exact
  field-agnostic form of the book's conjugate `χ_{W*}` (via `char_dual`), and the RHS the true
  equivariant Hom dimension. Proof runs through the invariants/projector argument matching the
  book.
- Part (ii): the `0/1` Kronecker delta for irreducible `V, W` over an algebraically closed field,
  with `[IsAlgClosed k]` the necessary and faithful rendering of the book's ℂ (Schur's lemma).

No statement defect, no vacuity, axiom-clean (`[propext, Classical.choice, Quot.sound]`). No
`.lean` changes and no follow-up issue.
