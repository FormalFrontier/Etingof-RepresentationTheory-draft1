# Fidelity audit: Chapter 5, Theorem 5.22.1 — Weyl character formula for GL(V) (#7176)

**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 65e2116d)
**Scope:** `EtingofRepresentationTheory/Chapter5/Theorem5_22_1.lean`
(`Etingof.Theorem5_22_1`, `Etingof.schurModule_weight_eq_schurPoly_coeff`), with
supporting `SchurModule`, `glWeightSpace`, `formalCharacter`, and `schurPoly`
(the last in `Proposition5_21_1.lean`).
**Method:** book statement (`blobs/Chapter5/Theorem5.22.1.md`, `.refs.md`) first,
then statement-vs-blob fidelity of each headline declaration, then non-vacuity,
then axiom-cleanliness. Mirrors the established confidence-phase pattern
(`2026-07-21-ch8-theorem8_1_1-projective-fidelity.md`).

## Overall verdict: **FAITHFUL (but partial)**

Both headline declarations are genuine, sorry-free, axiom-clean formalizations of
the **character identity** that is the substantive core of Etingof Theorem 5.22.1
(the book's part 2: "if `N ≥ p`, the character of `L_λ` is the Schur polynomial
`S_λ(x)`"). The formal character `ch(L_λ)` is the true restricted character to the
diagonal torus `(k×)^N`, `L_λ` is the real Schur module `Im(c_λ)`, and `schurPoly`
is the honest alternant ratio `det(x_i^{λ_j+N-j}) / det(x_i^{N-j})` — no side of
the identity is a placeholder or `⊥`.

The formalization is **partial** relative to the book's three-part statement: it
captures part 2 only. Part 1 (the vanishing criterion `L_λ = 0 ↔ N < p`) is
**structurally subsumed** by the parametrization and is not a gap; part 3 (the
explicit dimension product) is a **genuine omission** — a downstream corollary not
derived here. Neither the omission nor the naming constitutes a statement or
vacuity **defect** in the two declarations under audit: their docstrings claim only
"character = Schur polynomial," which is exactly what they prove. Details below.

I file one **feature** follow-up for the missing part 3 (dimension formula) as
*additive* coverage, not a defect fix. See "Follow-up" at the end.

---

## Build & axioms

- `lake build EtingofRepresentationTheory.Chapter5.Theorem5_22_1` → exit 0
  (`Build completed successfully (8604 jobs)`; one benign `unusedTactic` linter
  warning at `:3467`, no errors).
- `#print axioms Etingof.Theorem5_22_1` →
  `[propext, Classical.choice, Quot.sound]`
- `#print axioms Etingof.schurModule_weight_eq_schurPoly_coeff` →
  `[propext, Classical.choice, Quot.sound]`

No `sorryAx`, no custom axioms. `Classical.choice` is expected and benign: it
enters through `schurPoly`, which is built as the `Exists.choose` witness of the
Vandermonde-divides-alternant fact (see §"schurPoly is honest").

---

## Declaration 1 — `Etingof.Theorem5_22_1` (`:3677`): **FAITHFUL** (to part 2)

```
(N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
  formalCharacter k N (SchurModule k N lam) = schurPoly N lam
```
(over `k` with `[Field k] [IsAlgClosed k] [CharZero k]`, from the `variable` at
`:505`.)

This is the book's part 2 verbatim: `ch(L_λ) = S_λ(x)`. Each ingredient is real:

**`SchurModule` is the genuine `L_λ = Im(c_λ)`, not a vacuous/⊥ object.**
`SchurModule k N lam := FDRep.of (schurModuleRep k N lam)` (`:321`), whose carrier
`SchurModuleSubmodule` (`:282`) is `LinearMap.range (youngSymEndomorphism k N lam)`
— the image of the Young symmetrizer `c_λ` acting on the tensor power
`(k^N)^{⊗n}`, `n = ∑ᵢ λᵢ`. The `GL_N(k)`-action (`schurModuleRep`, `:289`) is the
restriction of the diagonal action `g ↦ g^{⊗n}` (`glTensorRep`, `:218`), stable on
the image because the diagonal action commutes with the whole `S_n`-action and
hence with `c_λ` (`glTensor_comm_youngSym` `:246` → `glTensorRep_mem_range` `:271`).
This is exactly the book's construction. Independently, `SchurModuleSimple.lean`
proves this same module is a simple `GL_N`-representation
(`schurModuleSubmodule_isSimple_centralizer`, `schurModule_isSimple`), confirming it
is the irreducible `L_λ`, not merely some module bearing that name.

**`formalCharacter` is the true torus character, not a formal placeholder.**
`formalCharacter k N M` (`:495`) is `∑_μ (finrank_k M_μ) · x^μ`, summed over the
finite set of weights with nonzero weight space, where `M_μ = glWeightSpace k N M μ`
(`:349`) is the joint eigenspace
`⨅_{i,t} ker(M.ρ(diagUnit i t) − t^{μ_i}·id)` — the subspace on which the diagonal
torus generator with `t` in slot `i` acts by the scalar `t^{μ_i}`. `diagUnit`
(`:329`) is a genuine invertible diagonal matrix (its `val`/`inv`/`val_inv`/
`inv_val` are all constructed, not sorried). The sum is well-defined:
`glWeightSpace_finite_support` (`:444`) proves the support finite via simultaneous
generalized-eigenspace independence (`independent_iInf_maxGenEigenspace_of_forall
_mapsTo`) plus Noetherianity, with the eigenvalue map `μ ↦ (t ↦ t^{μ_i})` shown
injective using `exists_unit_pow_ne` (algebraic closure ⇒ infinitely many distinct
torus powers). `formalCharacter_coeff` (`:511`) confirms `coeff_μ = finrank M_μ`.
So this is the honest restricted character to `(k×)^N`, with the correct weight
`t^{μ_i}` reading.

**`schurPoly` is the honest Schur polynomial (see §below).** — FAITHFUL.

## Declaration 2 — `Etingof.schurModule_weight_eq_schurPoly_coeff` (`:3659`): **FAITHFUL**

```
(N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (μ : Fin N →₀ ℕ) :
  (finrank k (glWeightSpace k N (SchurModule k N lam) (fun i => μ i)) : ℚ) =
    (schurPoly N lam).coeff μ
```

This is the coefficient-level (weight-multiplicity) form of the same identity:
`dim (L_λ)_μ = [x^μ] S_λ`. It is a direct consequence of Declaration 1 via
`formalCharacter_coeff`, and the LHS is a genuine `finrank` of a genuine weight
space (same `glWeightSpace` object as above). Faithful.

---

## schurPoly is honest (not an arbitrary `Exists.choose`)

`schurPoly N lam` (`Proposition5_21_1.lean:308`) `:=
(vandermonde_dvd_alternant N (shiftedExps N lam)).choose`. It is **pinned** by
`schurPoly_mul_vandermonde` (`:313`):
`schurPoly N lam * det(alternant vandermondeExps) = det(alternant shiftedExps)`,
i.e. `S_λ · Δ = A_{λ+δ}` with `Δ = det(x_i^{N-1-j})` and
`A_{λ+δ} = det(x_i^{λ_j + N-1-j})`. Because `MvPolynomial (Fin N) ℚ` is an integral
domain and `Δ ≠ 0` (`alternantMatrix_vandermondeExps_det_ne_zero`, and again
`schurPoly_coeff_self_ne_zero`'s `hΔne`), this identity determines `schurPoly`
uniquely — `Exists.choose` is not an arbitrary element. The exponents are the
0-indexed transcription of the book's 1-indexed `N−j`: for `j ∈ {0,…,N−1}`,
`vandermondeExps j = N−1−j` ranges over `N−1,…,0`, matching the book's `x_i^{N-j}`
for `j ∈ {1,…,N}`; `shiftedExps j = λ_j + N−1−j` matches `x_i^{λ_j + N-j}`.
Faithful.

**Coefficient-field choice `ℚ` is benign.** `formalCharacter … : MvPolynomial (Fin N) ℚ`
and `schurPoly … : MvPolynomial (Fin N) ℚ` both live over ℚ regardless of `k`. The
weight multiplicities are natural numbers cast to ℚ; ℚ is the natural home for the
integer character, and the identity is between integer-coefficient polynomials. The
generalization from the book's ℂ to a `[Field k] [IsAlgClosed k] [CharZero k]` `k`
(needed for `SchurModule`/`glWeightSpace`) is a harmless enlargement — algebraic
closure supplies the infinitely many torus scalars that make weight-space support
finite; characteristic 0 is what the Young-symmetrizer scalar `α ≠ 0` needs. No
hidden weakening.

---

## `Antitone lam` vs. the book's `N ≥ p`: FAITHFUL encoding

The book's part-2 hypothesis is `N ≥ p` where `p` = number of parts of `λ`. Here
`λ : Fin N → ℕ` with `Antitone lam` means `λ_0 ≥ λ_1 ≥ ⋯ ≥ λ_{N-1} ≥ 0`
(ℕ-valued ⇒ all `≥ 0`). This is exactly a partition with **at most `N` parts** (the
nonzero entries, padded by trailing zeros), so `p ≤ N` holds automatically — the
parametrization *is* the `N ≥ p` regime. It excludes no genuine `≤ N`-part
partition (any such partition pads to an antitone `Fin N → ℕ`) and admits no
non-partition (antitone + ℕ-valued ⇔ partition with ≤ N parts). `weightToPartition`
(`:30`) converts `lam` to the `Nat.Partition (∑ᵢ λᵢ)` used to build `c_λ`,
confirming the intended reading. Faithful.

---

## Scope: parts 1 and 3 (the one substantive fidelity finding)

The book's Theorem 5.22.1 has three parts:
1. `L_λ = 0 ⇔ N < p`;
2. if `N ≥ p`, `ch(L_λ) = S_λ(x)`;   ← **the formalized content**
3. therefore `dim L_λ = ∏_{1≤i<j≤N} (λ_i − λ_j + j − i)/(j − i)`.

- **Part 1 is structurally subsumed, not a gap.** Under the `λ : Fin N → ℕ`
  encoding, `p ≤ N` always (see previous section), so the "`N < p`" branch — where
  the book's `L_λ` vanishes — is *not expressible*: it corresponds to partitions
  with more than `N` parts, which cannot be written as `Fin N → ℕ`. The
  formalization therefore lives entirely in the non-vanishing regime, and part 1's
  vanishing statement has no faithful instance to omit. This is not overclaiming.
  (Grep of Chapter 5 confirms no separate `L_λ = 0 ↔ N < p` decl exists; none is
  needed for this parametrization.)

- **Part 3 is a genuine omission.** No declaration in this file or elsewhere in
  Chapter 5 computes `dim L_λ` as the explicit product `∏_{i<j}(λ_i−λ_j+j−i)/(j−i)`
  (grep for the product / a `dim`-formula decl returns nothing). Part 3 is a
  corollary of part 2 (evaluate/normalize the character), and it is standard book
  content of the *named* theorem. Its absence makes the formalization
  **faithful-but-partial**.

**Why this is not a DEFECT of the audited declarations.** The two headline decls
state and prove exactly the character identity their docstrings advertise
("`formalCharacter … = schurPoly …`"); nothing in them is weakened, vacuous, or
mislabeled. The gap is *missing additional content*, not a false or empty
statement. Per the issue's framing, I record this as an acceptable partial scope
for the two decls, and file a follow-up (below) to add the missing part 3.

**Naming caveat (advisory, no change made).** `Theorem5_22_1` is named after the
full three-part theorem but proves only part 2. The docstring is honest about what
it proves, so this is not a statement defect — but a reader scanning names could
over-read it. Worth a one-line docstring note that parts 1/3 are subsumed/deferred;
I leave the file untouched per the report-only remit and instead capture it in the
follow-up issue.

---

## Non-vacuity: PASS (formally backed)

The identity is not vacuously true on an empty/⊥ input:

- **RHS nonzero, formally.** `schurPoly_coeff_self_ne_zero`
  (`Proposition5_21_1.lean:782`) proves `(schurPoly N lam).coeff (⟨λ⟩) ≠ 0` for
  antitone `λ` (highest-weight multiplicity one, `K_{λλ} = 1`), and
  `schurPoly_ne_zero` (`Theorem5_23_2Core.lean:96`) gives `schurPoly N lam ≠ 0`.
- **LHS nonzero, hence `L_λ ≠ ⊥`.** Chaining
  `schurModule_weight_eq_schurPoly_coeff` at `μ = λ` with the nonzero highest-weight
  coefficient gives `dim (L_λ)_λ = [x^λ] S_λ ≠ 0` in ℚ, so the weight space at
  weight `λ` is nontrivial and `SchurModule k N lam ≠ ⊥`. Both sides of
  `Theorem5_22_1` are therefore genuinely nonzero.
- **Concrete witness.** `λ = (1,0,…,0)`: `n = 1`, `c_λ` is the trivial (identity)
  symmetrizer, so `L_λ = (k^N)^{⊗1} = k^N`, the standard representation, with
  torus character `x_1 + ⋯ + x_N`; and `S_{(1,0,…,0)} = x_1 + ⋯ + x_N`. Both sides
  are the nonzero degree-1 elementary symmetric polynomial, dimension `N`.

Non-vacuity holds, with the general case backed by proved lemmas rather than only a
single example.

---

## Follow-up

Filed one **feature** issue for the missing **part 3** (explicit dimension product
`dim L_λ = ∏_{1≤i<j≤N}(λ_i − λ_j + j − i)/(j − i)`), which is book content of the
named theorem not yet formalized in Chapter 5. This is additive coverage, not a
defect fix — the two audited declarations are FAITHFUL and non-vacuous as they
stand, and no Lean change is made in this review.
