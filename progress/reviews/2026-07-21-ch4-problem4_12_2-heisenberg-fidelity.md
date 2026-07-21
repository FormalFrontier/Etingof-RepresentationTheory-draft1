# Fidelity audit: Chapter 4, Problem 4.12.2 — Heisenberg group `H_p` (#7204)

**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 974e0738)
**Scope:** `EtingofRepresentationTheory/Chapter4/Problem4_12_2.lean`
(headline decls `exists_unique_rep`, `irreducible_iff`, `one_dim_reps_card`,
`R1_decomposes`, `irreducible_dim`, all in namespace `Etingof.Problem4_12_2`).
**Method:** book statement first (`blobs/Chapter4/Problem4.12.2.md`, parts (a)–(d)),
then statement-vs-blob fidelity of each headline declaration, then non-vacuity, then
build + axiom-cleanliness. Mirrors the established confidence-phase pattern
(`2026-07-21-ch5-theorem5_26_1-artin-fidelity.md`).

## Overall verdict: **gap (part (d) enumeration not exposed as a headline)**

Parts **(a), (b), (c) are faithfully and non-vacuously rendered** as headline results:
the group model is the genuine order-`p³` Heisenberg group, the generators and the two
generator actions match the book's three matrices, existence/uniqueness is a real `∃!`,
irreducibility is the genuine `IsSimpleModule` over `ℂ[G]` with a two-directional
`↔ z ≠ 1`, and the `R_1` decomposition is a genuine internal direct sum of `p` distinct
one-dimensional isotypic lines (`Injective χ` encodes "each occurs exactly once").

Part **(d) is only partially exposed.** The headline `irreducible_dim` states only the
**dimension dichotomy** (`finrank = 1 ∨ finrank = p`), which is faithful and non-vacuous.
The book's part (d) asks to **classify all irreducibles** via the sum-of-squares formula:
exactly `p²` of dimension `1` (the characters) and `p − 1` of dimension `p` (the `R_z`,
`z ≠ 1`), with `p²·1² + (p−1)·p² = p³ = |G|`. That complete enumeration **is fully proved
inside** `irreducible_dim` (the family `E`, its members pairwise non-isomorphic, squared
dims summing to `p³`, and the injection into the complete Wedderburn enumeration forced
surjective by positivity — `hcsurj`), but it is **not surfaced as a named headline
theorem**. Per the issue's explicit instruction, a missing headline enumeration is a
`gap`; a `feature` follow-up is filed to expose it. Details below.

---

## Build & axioms

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_2` → exit 0
  (`Build completed successfully (8587 jobs)`); only benign linter warnings
  (`push_neg` deprecation ×2, two `unusedSimpArgs` on `Pi.single_apply`, two
  `unusedVariables` in `abHom`'s `map_mul'`, one `show`/`change` style note at 943).
- `#print axioms` on all five headline decls →
  `[propext, Classical.choice, Quot.sound]` for each. No `sorryAx`; no literal
  `sorry` in the file. All five are public `theorem`s in the `Etingof.Problem4_12_2`
  namespace.

---

## The group model (`Heisenberg p`)

Book: `G` = `3×3` upper-unitriangular matrices over `𝔽_p`, order `p³`.

Lean models `⟨a,b,c⟩ : (ZMod p)³` as the matrix `[[1,a,c],[0,1,b],[0,0,1]]`, with
`⟨a,b,c⟩ * ⟨a',b',c'⟩ = ⟨a+a', b+b', c+c'+a·b'⟩`. I checked this against the actual
matrix product `M(a,b,c)·M(a',b',c')`: the `(1,2)` entry is `a+a'`, the `(2,3)` entry is
`b+b'`, and the `(1,3)` entry is `c + a·b' + c'` — exactly the encoded law. `One = ⟨0,0,0⟩`
and `Inv = ⟨-a,-b,-c+ab⟩` are the identity and inverse. The full `Group` instance is
proved. `card_eq : Fintype.card (Heisenberg p) = p^3` via `equivProd` to `(ZMod p)³`.
This is a faithful (isomorphic) model of the matrix group. **Faithful.**

Generators (`central_word`, `closure_gens_eq_top` show `{xGen, yGen}` generate):
- `xGen = ⟨1,0,0⟩` ↔ `[[1,1,0],[0,1,0],[0,0,1]]` — the book's first matrix.
- `yGen = ⟨0,1,0⟩` ↔ `[[1,0,0],[0,1,1],[0,0,1]]` — the book's second matrix.
- central `⟨0,0,1⟩ = [xGen, yGen]` (`central_mem_commutator`) — the commutator.
**Faithful.**

---

## Part (a) — `exists_unique_rep`

Book: *such a representation exists and is unique, and compute `ρ(g)` for all `g`.*

```
theorem exists_unique_rep [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) :
    ∃! ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ),
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1)) ∧
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = z ^ t.val * f t)
```

- Genuine `∃!` over an honest `Representation ℂ (Heisenberg p) (ZMod p → ℂ)`.
- The two generator actions are the book's: shift `f ↦ f(·−1)` on `xGen`, and
  multiplication by `z^t` on `yGen` (`z^t.val`, well-defined since `z^p = 1`; matches
  `z^x` for `x ∈ 𝔽_p`). Verified `rhoHom_xGen`/`rhoHom_yGen` deliver exactly these.
- "Compute `ρ(g)` for all `g`" is realized by the explicit `def rhoLin z ⟨a,b,c⟩ f t =
  z^(b·t − c).val · f(t − a)`, whose `map_mul'` I confirmed is proved (genuine rep).
- Uniqueness genuinely uses that `xGen, yGen` generate `G` (`central_word`, `eq_gen_prod`).
- `[Fact p.Prime]` is the book's hypothesis; `NeZero p` is derived from it.

**Faithful, non-vacuous** (`rhoHom` is the explicit witness).

## Part (b) — `irreducible_iff`

Book: *`R_z` is irreducible iff `z ≠ 1`.*

```
theorem irreducible_iff [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hx : … ρ(xGen) f t = f (t-1)) (hy : … ρ(yGen) f t = z^t.val * f t) :
    IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) ρ.asModule ↔ z ≠ 1
```

- "Irreducible" is the genuine `IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) ρ.asModule`
  (no nontrivial subrepresentation), **not** a surrogate.
- Phrased for **any** `ρ` meeting the generator conditions — this is exactly the `R_z`
  of part (a). Both directions are proved: `z = 1` exhibits the constant line as a proper
  nonzero subrep (not simple); `z ≠ 1` shows any nonzero `Y`-invariant subspace contains
  an indicator, then the `X`-orbit sweeps all indicators to `⊤`.
**Faithful, non-vacuous** (`R_z = rhoHom z hz` inhabits the hypotheses).

## Part (c) — `one_dim_reps_card` + `R1_decomposes`

Book: *classify all 1-dim reps; `R_1` decomposes into a direct sum of 1-dim reps, each
occurring exactly once.*

`one_dim_reps_card [Fact p.Prime] : Nat.card (Heisenberg p →* ℂˣ) = p ^ 2`.
- 1-dim complex reps of `G` are precisely the homs `G →* ℂˣ`; the count `p²` is correct
  (they factor through `G^{ab} ≅ (ZMod p)²`, and `|Hom((ZMod p)², ℂˣ)| = p²`). The proof
  builds the explicit bijection `e` with characters of the abelianization
  (`abHom`, `abHom_ker_le_ker`, `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`).
  The classification is rendered as this count-plus-bijection. **Faithful.**

`R1_decomposes` — `∃ S : Fin p → Submodule`, all `G`-invariant, each `finrank = 1`,
`DirectSum.IsInternal S`, and `∃ χ : Fin p → (G →* ℂˣ)`, `Function.Injective χ`, with
`ρ g` acting on `S i` by the scalar `χ i g`.
- `DirectSum.IsInternal S` with `p` lines of `finrank 1` = "`R_1` = direct sum of `p`
  one-dimensional reps."
- Each `S i` is the isotypic line of a character `χ i` (`ρ g w = (χ i g) • w`), and
  `Function.Injective χ` = the `p` characters are pairwise distinct = **"each occurs
  exactly once"** (multiplicity-free). This is the faithful reading of the book's clause
  (the `p` constituents that appear are distinct — not that all `p²` characters appear).
- Stated for the `z = 1` representation (`hy : ρ(yGen) f t = f t`), i.e. `R_1`.
**Faithful, non-vacuous** (`rhoHom 1 …` inhabits the hypotheses).

## Part (d) — `irreducible_dim` (dichotomy only, at headline level)

Book: *use (a)–(c) and the "sum of squares" formula to classify all irreducible reps.*

```
theorem irreducible_dim [Fact p.Prime] {W} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ (Heisenberg p) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = p
```

- The **dimension dichotomy** `{1, p}` is faithful, and non-vacuous in both branches:
  `finrank_rhoHom` shows `R_z` is genuinely `p`-dimensional and `irreducible_iff` makes
  it simple for `z ≠ 1` (so `= p` is realized); characters realize `= 1`.
- **However**, the book's part (d) is the *full classification*: exactly `p²` irreducibles
  of dimension `1` and `p − 1` of dimension `p`, with `p²·1² + (p−1)·p² = p³ = |G|`. That
  complete enumeration **is proved inside the `irreducible_dim` proof** — the family
  `E = (characters) ⊕ (R_z, z ≠ 0)` is built, shown pairwise non-isomorphic
  (`hEinj`, separated by dimension and by the central character `z^{(-1).val}·p`),
  its squared dims sum to `p³` (`hEsum`), and it is injected into the complete Wedderburn
  enumeration `exists_simples_sum_finrank_sq_eq_card`, forced surjective by positivity
  (`hcsurj`, `surj_of_injective_of_sum_eq`). So every simple is `≅` a member of `E`.
- **The gap:** this completeness/enumeration is never surfaced as a *named headline
  result*. The only "count" headlines are `card_eq` (`|G| = p³`) and `one_dim_reps_card`
  (`p²` characters). There is no headline stating "there are exactly `p − 1` irreps of
  dimension `p`" or "every irrep is isomorphic to a character or an `R_z`" (the actual
  classification). Per the issue's explicit instruction, a part-(d) classification that is
  present only as the `{1,p}` dichotomy at the headline level is recorded as a `gap`, with
  a `feature` follow-up naming the missing enumeration.

**Assessment:** faithful dichotomy; classification proven but not exposed → `gap`.

---

## Non-vacuity summary

- `[Fact p.Prime]` inhabitable (`p = 2`). ✓
- `rhoHom z hz` is a genuine `p`-dimensional representation (`finrank_rhoHom = p`), so
  (d)'s `= p` branch and (b)'s "irreducible for `z ≠ 1`" are non-vacuous. ✓
- The `p²` characters of (c) are genuine distinct homomorphisms (`one_dim_reps_card`
  bijection; `charRep` gives a real 1-dim rep). ✓
- `ZMod p → ℂ` is nontrivial; all representations act on nonzero spaces. ✓

---

## Recommendation

- `progress/items.json` `Chapter4/Problem4.12.2` → `fidelity: gap` with a note that
  parts (a)–(c) are faithful and non-vacuous, and part (d) is present only as the
  `{1,p}` dimension dichotomy at the headline level (the full enumeration is proved
  inside `irreducible_dim` but not exposed).
- File a `feature` follow-up: expose the part-(d) classification as a headline theorem —
  e.g. "the irreducibles of `H_p` are exactly the `p²` characters and the `p − 1`
  representations `R_z` (`z ≠ 1`), hence exactly `p²` of dimension `1` and `p − 1` of
  dimension `p`". The mathematical content already exists in `irreducible_dim`'s proof
  (`hcsurj`, `hEsum`, `hEinj`); the follow-up is to lift it into a reusable statement.
- No defect fixed here (report-only review).
