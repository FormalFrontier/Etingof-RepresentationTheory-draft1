# Per-claim coverage check (step b)

Verdicts on the 89 gap-likely prose-claim candidates from the deterministic
pre-pass, checked against the actual Lean source by one agent per chapter.

**Caveat:** these are single-agent verdicts, NOT adversarially verified. Expect
some false "covered" (agent matched a related-but-not-identical declaration) and
some false "gap" (claim covered under a name the agent missed). Treat the gap
list as a high-quality candidate defect list, not a confirmed one. Confirming
each gap is the bounded adversarial sweep (Stage 3.7 step 3).

## Totals (of 89)

| verdict | count | meaning |
|---|---|---|
| **gap** | 34 | genuinely not formalized anywhere — real coverage holes |
| covered | 30 | folded into a theorem/def elsewhere (often differently named) |
| trivial_mathlib | 10 | direct Mathlib restatement, not project-worthy |
| nonformal | 15 | motivation / history / notation, not a proposition |

Per chapter (covered / gap / trivial / nonformal):
- Chapter2: 4 / 8 / 4 / 3
- Chapter3: 2 / 4 / 0 / 1
- Chapter4: 2 / 4 / 2 / 2
- Chapter5: 19 / 6 / 1 / 6
- Chapter6: 3 / 0 / 0 / 0
- Chapter7: 0 / 5 / 3 / 3
- Chapter9: 0 / 7 / 0 / 0

## RED FLAGS: vacuous `True` statements (HIGHEST priority — bigger than the prose gaps)

The agents surfaced, and a direct scan confirmed, that **`status: sorry_free` does NOT
mean "formalized."** A statement written as `... : True := by trivial` has no sorry, so
it counts as sorry-free, yet asserts nothing. The project's own rules forbid this
("Never use `True` as a placeholder for propositions").

Direct scan: **16 vacuous `True`-conclusion statements across 13 files**, all marked
`sorry_free` in items.json:

- `Chapter5/Definition5_8_1.lean` — the **induced representation `Ind_H^G V`** is stated
  as `theorem ... : True`. The book's central Ind construction is absent at its definition
  site. It is referenced by `Theorem5_9_1` (also a `True` stub), `5_10_1`, `5_26_1`,
  `5_27_1`. A real `inducedRepV` exists only inside `Theorem5_27_1` (semidirect products).
- `Chapter4/Theorem4_6_2.lean` (existence + uniqueness), `Theorem4_6_3`, `Theorem4_1_1`.
- `Chapter5`: `Corollary5_1_6`, `Example5_1_3`, `Example5_12_3`, `Lemma5_4_7`, `Lemma5_7_2`,
  `Proposition5_3_2`, `Theorem5_3_1`, `Theorem5_6_1`, `Theorem5_9_1`.

Separately, items.json already flags **17 items as `needs_statement`** (acknowledged
incomplete statements) and 1 as `has_true_hypothesis`. The two sets overlap only partially
(e.g. `Corollary5.1.6` is in both; `Definition5.8.1`, `Theorem4.6.2`, `Theorem5.9.1` are
`True`-stubs NOT flagged by `needs_statement`; `Theorem6.5.2` = Gabriel's theorem is flagged
`needs_statement` but is not a plain `True`-stub). So neither tracking field is complete.

**Implication for "are we done?":** the meaningful completeness risk is not sorry-count, it
is *vacuity* — `True` conclusions, `True` hypotheses, and `needs_statement` placeholders, all
currently hiding under `sorry_free`. This deserves its own enforced check (see PLAN
Amendment 6) and is higher priority than the 34 prose-claim gaps.

## The 34 genuine gaps (prioritized clusters)

### Chapter 2 (8) — foundational, high value
- **quiver representations ≃ path-algebra modules** (`Discussion_quiver_rep_bijection`): the
  equivalence and the mutually-inverse maps are not stated; both sides are defined but never linked.
- path algebra `P_Q` is unital for finite Q (`Σ pᵢ = 1`) (`Remark2.8.5`).
- quotient algebra `A/I` multiplication well-defined; `V/W` is a representation (`Discussion_2.5_well_defined`).
- `k[t]` is a faithful Weyl-algebra rep in char 0; `t^a k[a][t,t^{-1}]` faithful in any char (`Discussion_faithful_example`, 2 claims).
- `k[G]` commutative iff `G` commutative; `End V` / free algebra non-commutativity (`Discussion_commutativity_examples`, 2 claims).

### Chapter 3 (4)
- canonical isotypic decomposition `⊕_X Hom(X,V)⊗X → V` is an isomorphism (`Remark3.1.3`).
- free-module evaluation `Aⁿ → X` surjective; f.g. module is a quotient of a free module (`Remark3.3.4`).
- `n` = maximal length of a strict filtration (`Discussion_after_Theorem3.7.1`).
- character is tracial / factors through `A/[A,A]` (`Introduction_to_3.6`).

### Chapter 4 (4)
- **irreducibility criterion: V irreducible ⟺ ⟨χ_V,χ_V⟩ = 1** (`Discussion_after_Theorem4.5.1`) — only the forward direction for already-simple V is proved.
- character recovery from primitive idempotents (Frobenius) (`Remark4.5.3`).
- `V ≅ V*` ⟺ `χ_V` real; dual/conjugate character formulas (`Discussion_4.4`).
- conjugate representation `V̄ ≅ V*` (`Discussion_after_Theorem4.6.2`).

### Chapter 5 (6)
- `Ind_H^G V ≅ Hom_H(k[G],V)` (coinduced) (`Remark5.8.2`).
- worked `Ind` decompositions for S₃ from Z₂, Z₃ (`Discussion_5.11_examples`, 2 claims).
- `U_λ = ℂ[S_n]·a_λ` row-symmetrizer alternative definition (`Introduction_5.14`).
- count `½q(q-1)` complementary-series reps (`Discussion_5.25.4`) — minor, only in comments.
- x-independence isomorphism `V_(O,x,U) ≅ V_(O,y,g(U))` (`Discussion_semidirect_products`).

### Chapter 7 (5) — category theory
- `C₁ ≃ C₂` toy-groupoid equivalence ("check it!") (`Discussion_after_Definition7.4.1`).
- `FSet ≃` skeleton with objects ℕ (`Discussion_after_Definition7.4.1`).
- adjunction as representability of `Y↦Hom(X,G(Y))` (`Discussion_after_Definition7.6.1`).
- iso-classes-of-functors bijection `C₁→D ≃ C₂→D` (`Introduction_7.4`).
- categories in Example 7.7.2 are k-linear (`Discussion_after_Remark7.7.4`).

### Chapter 9 (7) — entire Morita "B_n family" theory missing
All of Section 9.7's introduction + discussion after Def 9.7.1:
- Hom spaces finite-dimensional in finite-length k-linear abelian cat (`Introduction_9.6`).
- projective generators are exactly `P_n = ⊕ nᵢ Pᵢ`, `nᵢ ≥ 1` (`Introduction_9.7`).
- `B_n` with `B/Rad` commutative is unique (`nᵢ=1`) (`Discussion_after_Definition9.7.1`).
- `B_n := End(P_n)^op` are all algebras with module cat ≌ C (`Introduction_9.7`).
- Morita classes are the families `{B_n(C)}` (`Discussion_after_Definition9.7.1`).
- `dim B_n = Σ c_ij nᵢ nⱼ` (Cartan matrix) (`Discussion_after_Definition9.7.1`).
- minimal basic algebra has `dim = Σ c_ij` at `nᵢ=1` (`Discussion_after_Definition9.7.1`).

The Lean development covers Morita only via Corollary 9.7.3's existence/uniqueness/dim-bound
form, not the explicit n-parametrized `B_n` enumeration, the Cartan dimension formula, or
the finite-dimensionality-of-Hom remark.
