# Fidelity audit: Chapter 5, Theorem 5.26.1 — Artin's theorem (#7193)

**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 44e2bea9)
**Scope:** `EtingofRepresentationTheory/Chapter5/Theorem5_26_1.lean`
(headline decls `Etingof.Theorem5_26_1`, `Etingof.inducedCharacter`).
**Method:** book statement first (`blobs/Chapter5/Theorem5.26.1.md`,
`Discussion_proof_of_Theorem5.26.1.md`, `Remark5.26.2.md`), then
statement-vs-blob fidelity of each headline declaration, then non-vacuity,
then build + axiom-cleanliness. Mirrors the established confidence-phase pattern
(`2026-07-21-ch5-theorem5_22_1-weyl-character-formula-fidelity.md`).

## Overall verdict: **FAITHFUL**

Both headline declarations are genuine, sorry-free, axiom-clean formalizations of
Etingof Theorem 5.26.1. The theorem is the honest equivalence (i) ⟺ (ii); the
ℚ-span (not ℂ-span) is used, which is the whole content of the result; the induced
character `def` has a real body (the standard Frobenius character formula, not a
placeholder); "irreducible" on both G and H is the genuine `CategoryTheory.Simple`
condition; conjugation-invariance `hX` is a real hypothesis used exactly where the
book's proof uses it (the (ii) ⟹ (i) direction). One deviation — the spanning set
ranges over **all** finite-dimensional reps `W` of `H` rather than only irreducible
`W` — is a standard equivalent reformulation (the two ℚ-spans are provably equal),
not a defect. Details below.

---

## Build & axioms

- `lake build EtingofRepresentationTheory.Chapter5.Theorem5_26_1` → exit 0
  (`Build completed successfully (8584 jobs)`); only benign linter warnings
  (`unusedVariables` on `hX`/`hcov` in a private helper — see below —, one
  `push_neg` deprecation, one `show`/`change` style note).
- `#print axioms Etingof.Theorem5_26_1` → `[propext, Classical.choice, Quot.sound]`
- `#print axioms Etingof.inducedCharacter` → `[propext, Classical.choice, Quot.sound]`
- No `sorryAx`. No literal `sorry` in the file. Both decls are public
  (`theorem` / `def` in the `Etingof` namespace); the four supporting lemmas
  (`frobenius_char_reciprocity`, `class_fun_vanishes_on_subgroup_of_orthogonal`,
  `covering_implies_vanishing`, `artin_Q_span_of_induced_chars`) and the
  `trivialFDRep*` witnesses are `private` and fully proved.

---

## Statement fidelity

Book (`blobs/Chapter5/Theorem5.26.1.md`): *Let X be a conjugation-invariant system
of subgroups of a finite group G. Then two conditions are equivalent:*
*(i) Any element of G belongs to a subgroup H ∈ X.*
*(ii) The character of any irreducible representation of G belongs to the ℚ-span of
characters of induced representations Ind_H^G V, where H ∈ X and V is an irreducible
representation of H.*

Lean (`Etingof.Theorem5_26_1`, `:670`):

```
theorem Etingof.Theorem5_26_1 (G : Type) [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X) :
    (∀ g : G, ∃ H ∈ X, g ∈ H) ↔
    (∀ (V : FDRep ℂ G), CategoryTheory.Simple V →
      V.character ∈ Submodule.span ℚ
        {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
          f = Etingof.inducedCharacter H W.character})
```

Item-by-item:

- **Finite group G / system X.** `(G : Type) [Group G] [Fintype G]`,
  `X : Set (Subgroup G)`. Faithful.
- **Conjugation-invariance `hX`.** `∀ H ∈ X, ∀ g, H.map (MulAut.conj g).toMonoidHom ∈ X`.
  `H.map (conj g)` is `gHg⁻¹`, so this is exactly "X is closed under conjugation."
  Genuine hypothesis (not vacuous): used in the (ii) ⟹ (i) direction via `hconj_out`
  (`:694`), precisely where the book's proof invokes "since X is conjugation
  invariant, g cannot be conjugated into such a subgroup." Faithful.
- **(i) covering.** `∀ g : G, ∃ H ∈ X, g ∈ H`. Verbatim. Faithful.
- **(ii) ℚ-span membership.** `V.character ∈ Submodule.span ℚ {…}` over the
  ℚ-module `G → ℂ`. The span is over **ℚ**, not ℂ — this is the substantive point
  of the theorem (Remark 5.26.2 records that ℚ-span and ℂ-span give equivalent
  statements; formalizing the ℚ version captures the real content). Faithful.
- **"irreducible representation of G"** = `CategoryTheory.Simple V` for
  `V : FDRep ℂ G` — the genuine no-nontrivial-subobject simplicity condition in the
  category of finite-dimensional ℂ[G]-modules. Faithful.
- **`V.character`** = `FDRep.character`, the true character (trace of the action).
  Faithful.
- **Direction.** Book "(i) ⟺ (ii)"; Lean `↔`. Both directions proved
  (`artin_forward` for ⟹, an explicit contrapositive for ⟸). Faithful.

### Noted deviation (equivalent reformulation, not a defect)

The book's (ii) restricts the induced representations to `V` **irreducible** reps of
`H`; the Lean spanning set uses `∃ (W : FDRep ℂ ↥H)` with **no** simplicity
constraint — it ranges over all finite-dimensional `W`. This does **not** change the
statement: over ℂ (char 0), Maschke gives `W ≅ ⊕ Uᵢ^{nᵢ}` with `Uᵢ` irreducible, so
`χ_{Ind W} = ∑ nᵢ · χ_{Ind Uᵢ}` lies in the ℤ-span (hence ℚ-span) of
irreducible-induced characters, and conversely irreducible `W` are among all `W`.
Thus `span ℚ {Ind W : all W} = span ℚ {Ind U : irreducible U}`, and the membership
claim is logically identical to the book's. The file's own
`hS_in_ℤspan` (`:262`) proves exactly the forward inclusion (`Ind W` decomposes with
ℕ-multiplicities into the `columnFDRep` irreducibles), so the equivalence is
internally witnessed. Faithful with a standard equivalent encoding; worth a one-line
note only.

## `Etingof.inducedCharacter` fidelity (the key risk flagged in #7193)

```
def Etingof.inducedCharacter (H : Subgroup G) (χ : ↥H → ℂ) : G → ℂ :=
  fun g => (Fintype.card ↥H : ℂ)⁻¹ *
    ∑ x : G, if h : x⁻¹ * g * x ∈ H then χ ⟨x⁻¹ * g * x, h⟩ else 0
```

- **Real body, not a placeholder.** The `def` returns the genuine averaged Frobenius
  character formula `χ_{Ind_H^G W}(g) = (1/|H|) ∑_{x∈G, x⁻¹gx∈H} χ_W(x⁻¹gx)` — the
  standard textbook formula (Etingof §5.26, Serre §7.2). No `sorry`, no `⊥`, no
  `True`-style surrogate.
- **Averaged vs coset-representative form.** The `|H|⁻¹ ∑_{x∈G}` form is the standard
  equivalent of the coset-representative sum `∑_{x∈G/H : x⁻¹gx∈H} χ(x⁻¹gx)`: summing
  over all of `G` instead of coset reps over-counts each contributing coset by exactly
  `|H|` (the `x⁻¹gx ∈ H` condition is `H`-right-invariant modulo the stabilizer), and
  the `|H|⁻¹` prefactor corrects this. Not a redefinition that changes the claim.
- **Faithful use.** In the theorem it is instantiated at `W.character` for
  `W : FDRep ℂ ↥H`, so `inducedCharacter H W.character = χ_{Ind_H^G W}`.
- **Internally validated.** `frobenius_char_reciprocity` (`:45`) proves the def
  satisfies genuine Frobenius reciprocity `∑_g f(g)·Ind(χ)(g⁻¹) = (|G|/|H|)·∑_{h∈H}
  f(h)·χ(h⁻¹)`, and `hS_in_ℤspan` proves `Ind W` decomposes into irreducible
  characters with the correct multiplicities `mᵢ = dim Hom_H(W, Res_H Vᵢ)`. A wrong
  `inducedCharacter` could not satisfy both. Strong evidence the def is the honest
  induced character.

## Non-vacuity

- **Hypotheses simultaneously satisfiable.** `X = {⊤}` (or any conjugation-invariant
  covering system) satisfies `hX` and (i); the trivial group is a concrete witness.
- **Simple reps of `G` exist / the quantifier is not empty.** `trivialFDRep_simple`
  (`:637`) constructs the 1-dimensional trivial representation and proves it
  `Simple`, so the `∀ V, Simple V → …` quantifier ranges over a nonempty class.
- **Span is nontrivial and the backward direction is genuinely exercised.** The
  (ii) ⟹ (i) proof (`:685`) uses `trivialFDRep`, whose character is the constant `1`
  (`trivialFDRep_character`, `:609`), to derive a contradiction from a hypothetical
  uncovered element `g₀`: all induced characters vanish at `g₀` (`hgen_vanish`), so
  the whole span vanishes at `g₀`, but `1 ≠ 0`. This is real content — the theorem is
  not vacuously true, and the span membership carries information.
- The forward direction is not vacuous either: `artin_forward` proves the orthogonal
  complement of the induced characters is trivial (via Frobenius reciprocity + the
  covering hypothesis) and then, via `artin_Q_span_of_induced_chars` (Remark 5.26.2),
  that the ℚ-span contains every irreducible character.

## Minor / cleanup (non-blocking, no fidelity impact)

- `artin_Q_span_of_induced_chars` (`:207`) takes `hX` and `hcov` but uses neither
  (the two `unusedVariables` linter warnings). This is mathematically correct: the
  book's (i) ⟹ (ii) argument needs conjugation-invariance nowhere and uses covering
  only through the supplied `horth_trivial` hypothesis; `artin_forward` discharges
  `horth_trivial` and there consumes `hcov` (via `covering_implies_vanishing`) and
  passes `hX` through unused. The dead parameters could be dropped (or renamed `_`)
  for tidiness. Not worth a PR on its own; fold into any future edit of the file.
- `push_neg` deprecation and one `show`→`change` style note — cosmetic, ignore or
  sweep opportunistically.

## Conclusion

`Etingof.Theorem5_26_1` and `Etingof.inducedCharacter` faithfully and non-vacuously
transcribe Etingof Theorem 5.26.1 (Artin's theorem), are sorry-free and axiom-clean.
The ℚ-span is genuine, the induced-character `def` has a real (standard Frobenius)
body, and irreducibility / conjugation-invariance are the honest conditions used
where the book uses them. The only deviation (spanning set over all `W` vs
irreducible `W`) is a provably-equivalent reformulation. **No defect; report-only.**
No follow-up issue required. The two cleanup notes above are optional and non-blocking.
