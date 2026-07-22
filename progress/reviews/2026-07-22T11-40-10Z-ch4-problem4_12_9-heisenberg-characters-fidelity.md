# Stage 3.7 fidelity audit — Problem 4.12.9 (Heisenberg group: characters & tensor products)

- **Issue:** #7272
- **Audited against:** `origin/main` HEAD `100240a8` (≥ required `2b305b75`)
- **Lean file:** `EtingofRepresentationTheory/Chapter4/Problem4_12_9.lean` (175 lines, `status: proved`, sorry-free)
- **Book blob:** `blobs/Chapter4/Problem4.12.9.md`
- **Verdict:** `fidelity: verified`, `coverage: covered_partial`
- **Report-only:** no Lean edits; no genuine gap found, so no follow-up repair issue.

## Book statement

> **Problem 4.12.9.** Find the characters and tensor products of irreducible complex
> representations of the Heisenberg group from Problem 4.12.2.

From Problem 4.12.2, the irreducibles of the order-`p³` Heisenberg group `G` over `𝔽_p` are:
- the `p²` one-dimensional characters `χ : G →* ℂˣ` (trivial on the commutator/center), and
- for each `p`-th root of unity `z ≠ 1`, a `p`-dimensional irreducible `R_z` on
  `V = ZMod p → ℂ` with `(ρ xGen f)(t) = f(t−1)`, `(ρ yGen f)(t) = z^t·f(t)`.

## Headline declarations audited

1. `character_Rz` (line 122)
   `tr ρ⟨a,b,c⟩ = if a = 0 ∧ b = 0 then (p:ℂ)·(z⁻¹)^c.val else 0`.
2. `tensor_character_nonone` (line 133) — generic `z·w ≠ 1`:
   `tr ρz(g) · tr ρw(g) = (p:ℂ) · tr ρzw(g)`.
3. `tensor_character_inv` (line 154) — `z·w = 1`:
   `tr ρz⟨a,b,c⟩ · tr ρw⟨a,b,c⟩ = if a = 0 ∧ b = 0 then (p:ℂ)^2 else 0`.

## 1. Hypothesis faithfulness

- **`[Fact p.Prime]`, `z ^ p = 1`, `z ≠ 1`.** These are the exact hypotheses of the
  Problem 4.12.2 classification. `z^p = 1 ∧ z ≠ 1` picks out a nontrivial `p`-th root of
  unity — precisely the index set of the `p`-dimensional irreducibles `R_z` (by
  4.12.2 `irreducible_iff`, `R_z` is simple iff `z ≠ 1`). Not vacuous (a primitive `p`-th
  root exists for every prime `p ≥ 2`) and not over-strong (it is the minimal condition
  isolating the irreducible family). Confirmed faithful.
- **`IsRz z ρ` + `isRz_eq_rhoHom`.** `IsRz z ρ` (lines 46–48) asserts exactly the book's
  two generator actions: `(ρ xGen f) t = f(t−1)` and `(ρ yGen f) t = z^{t.val}·f t`.
  `isRz_eq_rhoHom` (line 52) discharges `ρ = rhoHom z hz` via the *uniqueness* half of
  4.12.2 `exists_unique_rep` (#6226). So the audited `ρ` is provably **the** irreducible
  `R_z`, not an arbitrary representation with the same character. I checked `rhoLin` (the
  concrete operator, 4.12.2 line 203) against the generators:
  `rhoLin z xGen f t = z^{(0·t−0).val}·f(t−1) = f(t−1)` and
  `rhoLin z yGen f t = z^{(t−0).val}·f t = z^{t.val}·f t` — both match the book. Faithful.
- **`tensor_character_inv` hypotheses `w1 : w ≠ 1`, `hzw : z * w = 1`.** `z·w = 1` forces
  `w = z⁻¹`, whose central character `z^{c}` is the conjugate of `R_z`'s `z^{−c}`; hence
  `R_w = R_{z⁻¹}` is the dual/contragredient of `R_z` — the exact case in which
  `R_z ⊗ R_w` contains the trivial representation and splits into one-dimensionals. The
  extra hypothesis `w ≠ 1` is a (redundant but true) consequence of `z ≠ 1 ∧ z·w = 1`,
  so it neither strengthens nor vacuates the statement; `w^p = 1` is *derived* inside the
  proof (line 162), not assumed. All hypotheses are simultaneously satisfiable for any
  primitive `p`-th root `z`. Correct encoding of "the dual", non-vacuous.

## 2. Conclusion faithfulness (the key check)

- **Character formula (`character_Rz`).** `R_z` acts on `V = ZMod p → ℂ` by
  `rhoLin z g f t = z^{(g.b·t − g.c).val}·f(t − g.a)`, a monomial (permutation × diagonal)
  operator. Its trace picks up only diagonal entries (`g.a = 0`), and on the fibre the
  geometric sum `∑_{t} z^{(g.b·t − g.c).val}` vanishes unless `g.b = 0` as well
  (`sum_zpow_val_eq_zero`, the `(z−1)·S = 0 ⇒ S = 0` argument for `z ≠ 1`). On the center
  `⟨0,0,c⟩` the operator is the scalar `z^{(−c).val} = (z⁻¹)^{c.val}` (`zpow_neg_val`),
  giving trace `p·(z⁻¹)^{c.val} = p·z^{−c}`. This is the correct character of a
  `p`-dimensional representation whose central character is `z^{−c}` and which vanishes
  off the center. Faithful to "find the characters".
- **Tensor products as character identities.** Both `tensor_character_*` are stated as the
  pointwise product of traces `χ_{R_z}(g)·χ_{R_w}(g)`, which is exactly the character of
  `R_z ⊗ R_w`. The RHS targets are the characters of the claimed decompositions:
  - generic (`z·w ≠ 1`): on the center `p·z^{−c}·p·w^{−c} = p·(p·(zw)^{−c})`, i.e.
    `p · χ_{R_{zw}}`, and `0` off-center — the character of `p·R_{zw}` (dimension
    `p² = p·p` matches). Note `R_{zw}` is a genuine irreducible here because `z·w ≠ 1`
    (its `hzw` hypothesis feeds `character_Rz (z*w) …`). Faithful to `R_z ⊗ R_w ≅ p·R_{zw}`.
  - dual (`z·w = 1`): `p²` on the center, `0` off-center — the character of the direct sum
    of all `p²` one-dimensional characters, each once (each `χ` is trivial on the center so
    contributes `1` there; over a fixed non-central `g` the `p²` characters of the
    abelianization `(ZMod p)²` sum to `0`). Faithful to `R_z ⊗ R_{z⁻¹} ≅ ⊕(all p² one-dim)`.
- **Character identity vs. bundled isomorphism — is this a gap?** No. Over `ℂ`, equality of
  characters is equivalent to isomorphism for finite-dimensional representations of a finite
  group. Phrasing the tensor decompositions as character (trace-product) identities is
  therefore a **faithful rendering**, not a weakening — the same convention accepted in the
  precedent Problem 4.12.1 audit (#7268). The one caveat, recorded as an *encoding note* (not
  a gap): the right-hand sides `p·R_{zw}` and `⊕(all p² one-dim)` appear as their characters,
  not as constructed `Representation.Equiv`/`FDRep` isomorphisms; a future strengthening could
  bundle them, but the book only asks to "find" the characters and tensor products, which the
  character identities deliver.

## 3. Non-vacuity

- Hypotheses simultaneously satisfiable: a nontrivial `p`-th root of unity exists for every
  prime `p`, so none of the three theorems is vacuous. In `tensor_character_inv`,
  `z·w = 1 ∧ z ≠ 1` is realized by any primitive root and its inverse.
- Trace targets are non-trivial: `(p:ℂ) ≠ 0` and `(p:ℂ)^2 ≠ 0` since `p` is prime, so the
  central values `p·z^{−c}` and `p²` are genuinely nonzero — the theorems are not the trivial
  `0 = 0`.
- No `True`-typed hypothesis, no trivially-dischargeable premise, no sorry'd data. `IsRz` is a
  genuine conjunction of the two generator equations, discharged only via the real uniqueness
  theorem `exists_unique_rep`.

## Coverage

`covered_partial`. The audited file covers, for the substantive `p`-dimensional family:
the **characters** of every `R_z` (`z ≠ 1`) and the **tensor products** `R_z ⊗ R_w` in both
regimes (`z·w ≠ 1` and `z·w = 1`). It does **not** formalize the tensor products that involve
the `p²` one-dimensional characters — `χ ⊗ χ'` (again one-dimensional) and `χ ⊗ R_z ≅ R_z`
(the character-twist, noted informally in the file's module docstring line 33) — nor state the
characters of the one-dimensional reps as separate declarations (they are their own characters,
`p²` of them, classified in 4.12.2 `one_dim_reps_card`). These omitted pieces are elementary
relative to the `R_z` computations; the mathematically central content of "find the characters
and tensor products" is present. Recorded as `covered_partial` rather than a false
`covered_full`, per the issue's instruction.

## Verification evidence

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_9` — exit `0`
  (`✔ [8588/8588] Built … (2.8s)`).
- `#print axioms` for all three headline theorems:
  ```
  'Etingof.Problem4_12_9.character_Rz'            depends on axioms: [propext, Classical.choice, Quot.sound]
  'Etingof.Problem4_12_9.tensor_character_nonone' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Etingof.Problem4_12_9.tensor_character_inv'    depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  All clean — no `sorryAx`.

## Verdict

**`fidelity: verified`** — all three headline theorems are faithful renderings of the book's
"characters and tensor products of `R_z`" with correct, non-vacuous hypotheses (the `R_z`
family genuinely pinned to the 4.12.2 irreducible via `isRz_eq_rhoHom`), and non-trivial
conclusions. The character-identity phrasing of the tensor decompositions is faithful over `ℂ`
(equal characters ⟺ isomorphic); the un-bundled right-hand sides are an encoding note, not a
gap. **`coverage: covered_partial`** — the one-dimensional characters' own tensor products
(`χ⊗χ'`, `χ⊗R_z`) are outside the formalized scope. No repair issue filed.
