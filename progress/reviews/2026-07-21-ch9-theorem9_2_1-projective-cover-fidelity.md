# Statement-fidelity & non-vacuity audit — Theorem 9.2.1 (classification of indecomposable projective modules)

**Issue:** #7157
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 0b806f1f)
**Scope:** report-only fidelity + non-vacuity audit of the three headline declarations of Theorem 9.2.1
**Verdict: FAITHFUL — all three declarations axiom-clean, no defect. Nothing filed.**

## Sources compared

- **Book setup** (`blobs/Chapter9/Introduction_9.2.md`):
  > Let $A$ be a finite dimensional algebra with simple modules $M_1, \ldots, M_n$.
  > […] to understand finitely generated projective modules over $A$, it suffices to
  > classify indecomposable projective modules.

- **Book statement** (`blobs/Chapter9/Theorem9.2.1.md`):
  > **Theorem 9.2.1.** *(i) For each $i = 1, \ldots, n$ there exists a unique
  > indecomposable finitely generated projective module $P_i$ such that
  > $\dim \operatorname{Hom}(P_i, M_j) = \delta_{ij}$.*
  > *(ii)* $A = \bigoplus_{i=1}^n (\dim M_i) P_i$.
  > *(iii) Any indecomposable finitely generated projective module over $A$ is
  > isomorphic to $P_i$ for some $i$.*

- **Book proof** (same blob): lift the rank-1 diagonal projectors
  $e^0_{ij} = E^i_{jj}$ from $A/\operatorname{Rad}(A) = \bigoplus_i \operatorname{End}(M_i)$
  to orthogonal idempotents $e_{ij}$ in $A$ (Corollary 9.1.3), set $P_{ij} = A e_{ij}$;
  then $A = \bigoplus_{i}\bigoplus_{j=1}^{\dim M_i} P_{ij}$, $\operatorname{Hom}(P_{ij}, M_k) = e_{ij} M_k$
  so $\dim \operatorname{Hom}(P_{ij}, M_k) = \delta_{ik}$, and $P_{ij}$ is independent of $j$
  up to iso (idempotents conjugate under $A^\times$, Prop 9.1.1). Indecomposability: a splitting
  $P_i = Q_1 \oplus Q_2$ forces $\operatorname{Hom}(Q_l, M_j) = 0$ for all $j$ for one of $l = 1, 2$,
  hence that $Q_l = 0$. Completeness: any indecomposable projective must occur in the
  decomposition of $A$.

- **Lean declarations** (`EtingofRepresentationTheory/Chapter9/Theorem9_2_1.lean`), shared
  standing context:
  ```lean
  variable {k : Type*} [Field k]
  variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  ```
  and, per theorem, `[IsAlgClosed k]`, a `Fintype`/`DecidableEq` index `ι`, a family
  `M : ι → Type uA` of A-modules that are simple (`IsSimpleModule A (M i)`), pairwise
  non-isomorphic (`hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j`) and exhaustive
  (`hM_exhaustive : ∀ simple S, ∃ i, Nonempty (S ≃ₗ[A] M i)`).

  ```lean
  -- Theorem9_2_1.lean:1468  — part (i)
  theorem Etingof.Theorem_9_2_1_i [IsAlgClosed k] {ι} [Fintype ι] [DecidableEq ι]
      (M : ι → Type uA) [instances…] (hM …) (hM_exhaustive …) :
      ∃ (P : ι → Type uA) (_ : ∀ i, AddCommGroup (P i)) … (_ : ∀ i, Module.Projective A (P i))
        (_ : ∀ i, Module.Finite A (P i)) (_ : ∀ i, Etingof.IsIndecomposable A (P i)),
        (∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) ∧
        (∀ i (Q : Type uA) [instances… incl. Projective, Finite],
          Etingof.IsIndecomposable A Q →
          (∀ j, Module.finrank k (Q →ₗ[A] M j) = if i = j then 1 else 0) →
          Nonempty (Q ≃ₗ[A] P i))

  -- Theorem9_2_1.lean:2334  — part (ii)
  theorem Etingof.Theorem_9_2_1_ii [IsAlgClosed k] {ι} [Fintype ι] [DecidableEq ι]
      (M : ι → Type uA) [instances…] (hM …) (hM_exhaustive …)
      (P : ι → Type*) [instances… incl. Projective, Finite]
      (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
      (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) :
      Nonempty (A ≃ₗ[A] ⨁ (i : ι), Fin (Module.finrank k (M i)) → P i)

  -- Theorem9_2_1.lean:2472  — part (iii)
  theorem Etingof.Theorem_9_2_1_iii [IsAlgClosed k] {ι} [Fintype ι] [DecidableEq ι]
      (M : ι → Type uA) [instances…] (hM …) (hM_exhaustive …)
      (P : ι → Type*) [instances…] (hP_indec …) (hP …)
      (Q : Type uA) [instances… incl. Projective, Finite]
      (hQ_indec : Etingof.IsIndecomposable A Q) :
      ∃ i, Nonempty (Q ≃ₗ[A] P i)
  ```

  Supporting definition:
  ```lean
  def Etingof.IsIndecomposable (A V) [Ring A] [AddCommGroup V] [Module A V] : Prop :=
    Nontrivial V ∧ ∀ (W₁ W₂ : Submodule A V), IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥
  ```

## How the book's objects are encoded

- **"$A$ a finite dimensional algebra"** → `[Ring A] [Algebra k A] [Module.Finite k A]`. Correct.
- **"simple modules $M_1, \ldots, M_n$"** → an indexed family `M : ι → Type uA` (`ι` a `Fintype`)
  that is *simple* (`IsSimpleModule`), *pairwise non-isomorphic* (`hM`) and *exhaustive*
  (`hM_exhaustive`, every simple A-module is iso to some `M i`). This is exactly "a complete list
  of the pairwise-distinct simples", i.e. the book's $M_1,\dots,M_n$ with $n = |\iota|$. Faithful.
- **`[IsAlgClosed k]`** is genuinely load-bearing and matches the book: the proof rests on
  $A/\operatorname{Rad}(A) = \bigoplus_i \operatorname{End}(M_i)$ with $\operatorname{End}(M_i)$ a
  *matrix* algebra over $k$ — this is Schur's lemma over an algebraically closed field
  ($\operatorname{End}_A(M_i) = k$), the standing assumption of Etingof Ch. 9. It is used to pick
  the rank-1 diagonal projectors $E^i_{jj}$. Not a spurious hypothesis.
- **"$\dim \operatorname{Hom}(P_i, M_j) = \delta_{ij}$"** → `Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0`:
  the $k$-dimension of the space of *A-linear* maps. Correct reading of $\dim\operatorname{Hom}_A$.

## Part (i) — `Etingof.Theorem_9_2_1_i` — FAITHFUL

- **Existence.** The `∃ P, …` genuinely produces the family together with its A-module structure and,
  crucially, the properties `Module.Projective`, `Module.Finite`, and `Etingof.IsIndecomposable`.
  The witness is a real construction — `P i = ↥(Submodule.span A {e i})`, the left ideal $A e_i$
  built from idempotents lifted via `exists_orthogonal_idempotents_for_simples` (Wedderburn-Artin +
  Corollary 9.1.3 lifting). Projectivity/finiteness/indecomposability come from genuine lemmas
  (`leftIdeal_projective`, `leftIdeal_finite`, `leftIdeal_indecomposable_of_hom_delta`), none sorried.
- **Delta property.** `∀ i j, finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0` — matches
  $\dim\operatorname{Hom}(P_i,M_j)=\delta_{ij}$ exactly, via `finrank_hom_leftIdeal_eq`
  (the $\operatorname{Hom}(Ae, M) \cong eM$ identity).
- **Uniqueness.** The second conjunct states: any indecomposable f.g. projective `Q` sharing the full
  delta property at index `i` is `Nonempty (Q ≃ₗ[A] P i)`. This is precisely the book's "*unique* such
  module" — "such" being the delta property — proved via Fitting's lemma
  (`indecomposable_projective_iso_of_hom`). Faithful, and the uniqueness is scoped exactly as the book
  intends (indecomposable + f.g. + projective + delta ⇒ iso to `P i`).

**Non-vacuity.** The delta property is self-anti-vacuum: the diagonal case forces
`finrank (P i →ₗ[A] M i) = 1 ≠ 0`, so no `P i` can be the zero module (and `IsIndecomposable`
independently carries `Nontrivial`, see below). `hM_exhaustive` is load-bearing: it forces `ι` to
enumerate *all* simples, so `n = |ι|` is the true simple count rather than an arbitrary subset.
Satisfiable non-degenerately: `A = k` (alg. closed), `ι = Unit`, `M = k` gives one simple with
`P = A = k`.

## Part (ii) — `Etingof.Theorem_9_2_1_ii` — FAITHFUL

- Statement: `Nonempty (A ≃ₗ[A] ⨁ (i : ι), Fin (Module.finrank k (M i)) → P i)`. This is a genuine
  *A-linear* isomorphism of the left regular module `A` with the direct sum over `i` of
  `Fin (dim M_i) → P i`, i.e. `dim M_i` copies of `P_i`. The multiplicity `Module.finrank k (M i)`
  is $\dim M_i$ exactly. This is $A = \bigoplus_{i=1}^n (\dim M_i)\,P_i$. Faithful.
- The proof is a real construction: complete orthogonal idempotents indexed by
  `Σ i, Fin (dim M_i)` (`exists_complete_orthogonal_idempotents_for_simples`), the internal direct-sum
  decomposition `A = ⊕_p A e_p`, componentwise iso `A e_p ≅ P_{p.1}` by part-(i) uniqueness, then
  `sigmaLcurry` + `linearEquivFunOnFintype` regrouping. Not sorried.
- Note (not a defect): part (ii) takes the family `P` and its defining properties (`hP_indec`, `hP`)
  as *hypotheses* rather than re-invoking part (i). This is strictly more general — it holds for any
  family with those properties — and by part (i)'s uniqueness such a family is the projective covers
  up to iso, so no fidelity is lost. Multiplicities are on the correct side (`dim M_i`, not `dim P_i`).

**Non-vacuity.** The hypotheses are simultaneously satisfiable (part (i) produces exactly such a `P`),
so the conclusion is a real isomorphism, not a vacuous implication. The multiplicity would be visibly
wrong if it read `dim P_i` or a constant; it reads `finrank k (M i)`, matching the book.

## Part (iii) — `Etingof.Theorem_9_2_1_iii` — FAITHFUL

- Statement: for any indecomposable f.g. projective `Q`, `∃ i, Nonempty (Q ≃ₗ[A] P i)`. This is the
  honest "every indecomposable f.g. projective is ≅ some `P_i`" — an existence-of-index claim over the
  same `P` family, not a weaker variant. Faithful.
- Proof strategy differs from the book's route (the book argues "must occur in the decomposition of `A`",
  i.e. via Krull-Schmidt) but reaches the same statement: `Q` has a simple quotient `Q/N ≅ M_{j₀}`
  (Artinian ⇒ maximal submodule exists; `hM_exhaustive` identifies the quotient), giving a nonzero
  `Q → M_{j₀}`; `P_{j₀}` also has a nonzero map to `M_{j₀}` (delta gives `finrank = 1`); Fitting's lemma
  (`indecomposable_projective_iso_of_hom`) then yields `Q ≅ P_{j₀}`. The differing proof route does not
  affect statement fidelity.

**Non-vacuity.** `hM_exhaustive` again load-bearing (guarantees the simple quotient `Q/N` is some `M_i`).
The conclusion is a genuine iso witness; `hQ_indec` (with its `Nontrivial` clause) rules out `Q = 0`.

## `IsIndecomposable` is a genuine, correctly-guarded definition

`Etingof.IsIndecomposable A V := Nontrivial V ∧ ∀ W₁ W₂, IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥` is the
standard definition: `V` is nonzero and admits no non-trivial internal direct-sum splitting. The
`Nontrivial V` conjunct is essential and present — without it the zero module would satisfy the
splitting clause vacuously and be spuriously "indecomposable". This matches the book's usage ("if
$P_i = Q_1 \oplus Q_2$ then $Q_1 = 0$ or $Q_2 = 0$", with $P_i \ne 0$).

## Degenerate-case check

The only degeneracy the hypotheses permit is the zero algebra `A = 0` (allowed by `[Algebra k A]`
via the zero map `k → 0`): it has no simple modules, `hM_exhaustive` is vacuously true, `ι` may be
empty, and all three parts hold vacuously/trivially (`A ≅ ⊕_∅ = 0`). This is mathematically correct
(the zero algebra has no indecomposable projectives to classify) and harmless — it does not make any
*non-trivial* instance vacuous. For any nonzero `A`, a simple module exists, so `hM_exhaustive` forces
`ι` non-empty and the statements carry real content.

## Verification performed

- `lake exe cache get` then
  `lake build EtingofRepresentationTheory.Chapter9.Theorem9_2_1` — exit 0.
- No `sorry`/`admit` anywhere in `Theorem9_2_1.lean` (grep clean). All supporting lemmas
  (`leftIdeal_projective`, `leftIdeal_finite`, `finrank_hom_leftIdeal_eq`,
  `leftIdeal_indecomposable_of_hom_delta`, `exists_orthogonal_idempotents_for_simples`,
  `exists_complete_orthogonal_idempotents_for_simples`) are `theorem`/`lemma`, and the two
  `noncomputable def`s (`smulEnd`, `smulRange`) have genuine bodies (no def-body sorry).
- `#print axioms` on all three headline declarations:
  ```
  Etingof.Theorem_9_2_1_i   : [propext, Classical.choice, Quot.sound]
  Etingof.Theorem_9_2_1_ii  : [propext, Classical.choice, Quot.sound]
  Etingof.Theorem_9_2_1_iii : [propext, Classical.choice, Quot.sound]
  ```
  The standard three axioms only — no `sorryAx`, no project-local/custom axiom.

## Conclusion

| Declaration | Verdict |
|---|---|
| `Etingof.Theorem_9_2_1_i` (existence + delta + uniqueness of projective covers) | **FAITHFUL** |
| `Etingof.Theorem_9_2_1_ii` (`A ≅ ⊕ᵢ (dim Mᵢ)·Pᵢ`) | **FAITHFUL** |
| `Etingof.Theorem_9_2_1_iii` (every indecomposable f.g. projective ≅ some `Pᵢ`) | **FAITHFUL** |

All three headline declarations faithfully encode Theorem 9.2.1, are non-vacuous (delta property and
`hM_exhaustive` are load-bearing; `IsIndecomposable` carries `Nontrivial`), and are axiom-clean with no
`sorryAx`. The only permitted degeneracy is the zero algebra, which is mathematically correct and
harmless. No statement or vacuity defect found. **Report-only; no Lean changes, no follow-up `feature`
issue filed.**
