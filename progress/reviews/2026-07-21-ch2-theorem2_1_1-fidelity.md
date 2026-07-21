# Review — Ch2 Theorem 2.1.1: Classification of irreducible sl(2, ℂ)-representations

- **Issue:** #7109 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/7b4e60dc`
- **Target:** `EtingofRepresentationTheory/Chapter2/Theorem2_1_1.lean` (1703 lines), sorry-free on `main`
- **Construction dependency:** `EtingofRepresentationTheory/Chapter2/Sl2Irrep.lean` (the existence witness `V_d`)
- **Fidelity reference:** `blobs/Chapter2/Theorem2.1.1.md`
- **Focus areas:** statement fidelity per book part (i)/(ii); explicit-realization check for (i); non-vacuity / hidden-hypothesis audit; axiom-cleanliness (report-only, no `.lean` edits)
- **Overall verdict:** **FAITHFUL.** Both parts are faithful transcriptions of the book,
  both are non-vacuous (existence in (i) is witnessed by a genuine construction; (ii)'s
  proof is a real strong-recursion argument, not sorry-backed), and both are axiom-clean
  (subset of `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no custom axiom).
  **No DEFECT filed.** One documentation-traceability observation is recorded (§3) and a
  low-priority `doc` follow-up filed for it: the `V_d` construction reproduces the book's
  differential operators `ρ(h)=x∂ₓ−y∂_y, ρ(e)=x∂_y, ρ(f)=y∂ₓ` **exactly** in the monomial
  basis `x^{d−1−k} y^k`, but neither the docstrings nor `Theorem_2_1_1_i` records that
  identification, so the book's *specific realization* claim is present mathematically yet
  not traceable in-repo. This is not a fidelity defect in either statement.

---

## 0. Build and axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter2.Theorem2_1_1` (`lake build`, exit 0, 2924 jobs)
and ran `#print axioms` on both theorems plus the two construction witnesses:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.Theorem_2_1_1_i` | 397 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem_2_1_1_ii` | 1696 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Sl2Irrep.irrep_isIrreducible` | (Sl2Irrep) | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Sl2Irrep.irrep_finrank` | (Sl2Irrep) | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no stray custom axiom anywhere. `grep` for `sorry|admit|proof_wanted` across
`Theorem2_1_1.lean`, `Sl2Irrep.lean`, `Sl2Defs.lean` returns only two prose occurrences of
"sorry-free" in the `Sl2Irrep` docstring — no proof terms.

---

## 1. Part (i) — "exactly one irreducible V_d of each dimension"

**Book (i):** *"The algebra U has exactly one irreducible representation V_d of each dimension,
up to equivalence; this representation is realized in the space of homogeneous polynomials of
two variables x, y of degree d − 1 and is defined by the formulas
ρ(h) = x∂ₓ − y∂_y, ρ(e) = x∂_y, ρ(f) = y∂ₓ."*

**Lean (`Theorem_2_1_1_i (d : ℕ+)`):** a conjunction of

1. **Existence** — `∃ (V : Type) (instances…), finrank ℂ V = d ∧ LieModule.IsIrreducible ℂ sl2 V`,
   discharged with the concrete witness `Fin d → ℂ` carrying `Sl2Irrep.irrepLieRingModule d` /
   `irrepLieModule d`, and the facts `Sl2Irrep.irrep_finrank d`, `Sl2Irrep.irrep_isIrreducible d`;
2. **Uniqueness** — for all `V W` finite-dimensional irreducible sl2-modules with
   `finrank = d`, `Nonempty (V ≃ₗ⁅ℂ, sl2⁆ W)`, discharged via primitive-vector theory
   (`exists_primitiveVector`, `primitiveOrbit_basis`, `primitiveVector_dim`) and the explicit
   iso `sl2_irrep_equiv`.

**Fidelity:** faithful.

- "exactly one … up to equivalence" is correctly split into genuine **existence** AND
  **uniqueness-up-to-Lie-module-isomorphism** (`≃ₗ⁅ℂ, sl2⁆`, the correct category — Lie module
  iso, not mere linear iso). The uniqueness quantifies over *all* modules of dimension `d`, so
  it is the real classification statement, not a statement about a distinguished pair.
- Domain `d : ℕ+` correctly encodes "each dimension" (positive dimension); `finrank ℂ V = d`
  ties the classification to dimension exactly as the book indexes `V_d` by dimension.
- **Non-vacuity:** the existence `∃ V` is witnessed by the honest construction in `Sl2Irrep`
  (`rhoLieHom d : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin d → ℂ)` with the sl(2) triple relations proved,
  `irrep_isIrreducible` showing every nonzero invariant subspace is everything). It is **not**
  a vacuous ∃ discharged by a degenerate/zero object. `irrep_isIrreducible` and `irrep_finrank`
  are both axiom-clean (§0).

**Realization content — the specific concern raised by the issue.** The `Fin d → ℂ` model *is*
the book's polynomial realization, expressed in the monomial basis `x^{d−1−k} y^k`
(`k = 0,…,d−1`). Verified by hand against `rhoH/rhoE/rhoF` in `Sl2Irrep`:

| Book operator on `x^{d−1−k} y^k` | resulting weight / target | Lean component form |
|---|---|---|
| `ρ(h) = x∂ₓ − y∂_y` | eigenvalue `(d−1−k) − k = d−1−2k` | `rhoH`: `(ρ(h)v)_k = (d−1−2k)·v_k` ✓ |
| `ρ(e) = x∂_y` | index `k ↦ k·(index k−1)` | `rhoE`: `(ρ(e)v)_k = (k+1)·v_{k+1}` (i.e. source `m ↦ m·e_{m−1}`) ✓ |
| `ρ(f) = y∂ₓ` | index `k ↦ (d−1−k)·(index k+1)` | `rhoF`: `(ρ(f)v)_k = (d−k)·v_{k−1}` (i.e. source `m ↦ (d−1−m)·e_{m+1}`) ✓ |

So the explicit model is **present and mathematically exact**, and it is **linked to the
statement** (it is `Theorem_2_1_1_i`'s existence witness). What is missing is only the
*documentation* that records this basis identification: the `Sl2Irrep` header lists the
component action but does not state "this is `x∂ₓ − y∂_y` etc. in the basis `x^{d−1−k} y^k`",
and `Theorem_2_1_1_i` uses an anonymous `∃ V`. A reader therefore cannot confirm the book's
*specific realization* clause without re-deriving the correspondence above. This is a
documentation-traceability gap, **not** a statement-fidelity defect (neither statement claims
the realization, so neither can misstate it, and the construction is genuine). Recorded as a
low-priority `doc` follow-up (§4), not a DEFECT.

Bonus: `Problem_2_15_1_f` (line 449) states the same uniqueness against the *named* standard
model `Fin (lam+1) → ℂ`, giving a second, concrete anchor for the classification.

---

## 2. Part (ii) — complete reducibility

**Book (ii):** *"Any indecomposable finite dimensional representation of U is irreducible. That
is, any finite dimensional representation of U is a direct sum of irreducible representations."*

**Lean (`Theorem_2_1_1_ii (V) [finite-dim sl2-module]`):**
`ComplementedLattice (LieSubmodule ℂ sl2 V)`, proved by
`complementedLattice_sl2_aux (finrank ℂ V) V le_rfl`.

**Fidelity:** faithful.

- `ComplementedLattice (LieSubmodule ℂ sl2 V)` — every Lie submodule has a complementary Lie
  submodule — is exactly semisimplicity of the module, i.e. the "direct sum of irreducibles"
  form the book states as the content of (ii). The equivalent "indecomposable ⇒ irreducible"
  phrasing is the standard restatement of the same fact; capturing the direct-sum form is the
  stronger, more directly usable choice and is faithful.
- Hypotheses are exactly "finite-dimensional representation of sl(2, ℂ)": `[AddCommGroup V]`
  `[Module ℂ V]` `[FiniteDimensional ℂ V]` `[LieRingModule sl2 V]` `[LieModule ℂ sl2 V]`. No
  extra side conditions narrow it below the book's generality.
- **Non-vacuity / not sorry-backed:** `complementedLattice_sl2_aux` (line 1668) is a genuine
  proof by `Nat.strongRecOn` on a dimension bound: base cases `N = ⊥` / `N = ⊤`, otherwise
  extract an irreducible sub-Lie-module `W` (`exists_irreducible_lieSubmodule`) and split on
  `W ≤ N` (`complement_case_sub`) vs `W ⊓ N = ⊥` (`complement_case_disjoint`), each recursing
  on a strictly smaller dimension. `Theorem_2_1_1_ii` is axiom-clean (§0), so the whole chain
  is `sorryAx`-free. The lattice is non-trivially complemented (the proof genuinely produces
  complements), not vacuously so.

---

## 3. Documentation-correspondence accuracy

- `Theorem2_1_1.lean` header + the two theorem docstrings match what is proved: part (i) =
  existence + uniqueness up to iso in each positive dimension; part (ii) = complemented
  lattice of Lie submodules = complete reducibility. No drift.
- The "Mathlib correspondence" note ("classification of irreducible sl(2)-representations and
  complete reducibility are not in Mathlib") is accurate: Mathlib has `LieModule.IsIrreducible`,
  `sl`, etc., but not this classification result; the file supplies it.
- The single traceability shortfall is the §1 realization-documentation point: docstrings
  describe the coordinate action of `V_d` but never connect it to the book's polynomial /
  differential-operator picture. Worth a docstring line; filed as a `doc` follow-up.

---

## 4. Follow-up filed

- **`doc` (low priority) — filed as #7111:** add to the `Sl2Irrep` header (and/or `Theorem_2_1_1_i`) the
  identification `V_d = Fin d → ℂ ≅ {homogeneous degree-(d−1) polynomials in x, y}` via the
  monomial basis `x^{d−1−k} y^k`, and note that `rhoH/rhoE/rhoF` are `x∂ₓ − y∂_y`, `x∂_y`,
  `y∂ₓ` in that basis (correspondence table in §1). This makes the book's realization clause
  explicitly traceable. Not a DEFECT — statements are faithful and non-vacuous.

## 5. Scope notes

- Did **not** audit Theorem 2.1.2 (Gabriel finite-type quiver) per the issue; its proof lives
  in Ch6 and is covered by #7106.
- Report-only: no `.lean` file changed. The scratch `#print axioms` file used for §0 was
  removed; the only tree change is this writeup under `progress/reviews/`.
