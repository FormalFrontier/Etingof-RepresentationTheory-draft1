# Audit — projection-based reversed-leaf-edge sibling lemmas (PR #2871)

Issue: #2873 (review). Parent (blocked): #2853. Closes: #2868.
Auditor session: `25dd730b`. Date: 2026-05-18 (UTC).
Audit point: current `main` is `a182bbe` (one commit past `a7d3430`;
unrelated K_{1,4}/T(1,2,5) per-(F,Q) API stubs landed in #2878, no
impact on the proj-sibling surface).

Scope: light audit of the four projection-based reversed-leaf-edge
sibling lemmas added by PR #2871 to
`EtingofRepresentationTheory/Chapter6/FieldGenericD5Tilde.lean` in
Section 5e′. No code changes expected; the deliverables are statement
fidelity (D1), half-conclusion design audit (D2), and downstream
readiness assessment for #2853 (D3).

Build status: `lake build EtingofRepresentationTheory.Chapter6` exits
green on `main` at `a182bbe` (8041 jobs). Only two `declaration uses
'sorry'` warnings in `FieldGenericD5Tilde.lean`:

- line 798: `d5tildeRep_kQ_leaf_equalities` (5 raw `sorry`s for the 31
  reversed-orientation sub-cases at lines 926/928/930/932/934).
- line 974: `d5tildeRep_kQ_isIndecomposable` (1 raw `sorry`, line 981).

Total: **6 raw / 2 declarations**. Matches the PR #2871 landing claim.

Line-number drift relative to the issue body: the issue references
`FieldGenericD5Tilde.lean:802/804/806/808/810` for the five
case-split sorries. After the 5e′ insertion (PR #2871 added ~210
lines at the 590–714 range), the sorries are now at lines
`926/928/930/932/934`. Structural meaning (1 / 2 / 4 / 8 / 16
sub-cases respectively) is unchanged.

## Verdict

**PASS.** No follow-up issues filed.

The four proj-siblings are exactly the half-conclusion primitives that
the 31 reversed sub-cases of `d5tildeRep_kQ_leaf_equalities` need. The
half-conclusion design is correct (D2). Downstream readiness for #2853
is high: 30 of the 31 sub-cases have a directly applicable proj-sibling,
and the one outlier (e23 reversed, all leaves canonical) is precisely
the case earmarked for inline `gammaInv_embed*_F` per #2869's closure
analysis. No gaps detected.

---

## 1. Statement fidelity (D1) — PASS

### 1.1 Lemma signatures vs issue body

The four lemmas at `FieldGenericD5Tilde.lean:623-718`:

| Lemma                       | Lines    | Pull direction | Conclusion          |
|-----------------------------|----------|----------------|---------------------|
| `d5tilde_core_F_proj1`      | 623-637  | v=2 → v=0      | `x ∈ W ⟨0⟩`         |
| `d5tilde_core_F_proj2`      | 650-664  | v=2 → v=1      | `z ∈ W ⟨1⟩`         |
| `d5tilde_core3_F_proj1`     | 677-691  | v=3 → v=4      | `x ∈ W ⟨4⟩`         |
| `d5tilde_core3_F_proj2`     | 704-718  | v=3 → v=5      | `z ∈ W ⟨5⟩`         |

Each takes the parameterisation
`(F : Type) [Field F] (Q : Quiver (Fin 6)) [Subsingleton Hom]
  (hOrient : IsOrientationOf Q d5tildeAdj) (m : ℕ)
  (W : ∀ v, Submodule F …) (hW_pull : ∀ w ∈ W ⟨c⟩, P w ∈ W ⟨l⟩)
  (x z : Fin (m+1) → F)
  (hmem : starEmbed1_F x + starEmbed2_F z ∈ W ⟨c⟩)`,
which is the same `(F, Q, hOrient, m, W, hW_*, x, z, hmem)` shape as
the canonical `d5tilde_core_F` / `d5tilde_core3_F` lemmas at
lines 482–590, except:

- **Single submodule `W`**, not the `Wmain Wother` pair (no
  complementarity needed for half-conclusion).
- **Single pull hypothesis `hW_pull`**, not the four push hypotheses
  + complementarity that the canonical `core_F` consumes.

These differences are intrinsic to the proj-sibling design (the
projection identity unilaterally recovers the half tied to the
reversed-direction projection, so no Wother-subtraction is required).
The parameterisation is consistent with the issue body's spec
(`single submodule W such that pull P sends W ⟨c⟩ into W ⟨l⟩`).

Pull-direction correctness:

- `d5tilde_core_F_proj1` consumes `hW_20 : W ⟨2⟩ → W ⟨0⟩` via
  `starFirst_F` — matches "e02 reversed" (pull at v=2 to v=0). ✓
- `d5tilde_core_F_proj2` consumes `hW_21 : W ⟨2⟩ → W ⟨1⟩` via
  `starSecond_F` — matches "e12 reversed" (pull at v=2 to v=1). ✓
- `d5tilde_core3_F_proj1` consumes `hW_34 : W ⟨3⟩ → W ⟨4⟩` via
  `starFirst_F` — matches "e43 reversed" (pull at v=3 to v=4). ✓
- `d5tilde_core3_F_proj2` consumes `hW_35 : W ⟨3⟩ → W ⟨5⟩` via
  `starSecond_F` — matches "e53 reversed" (pull at v=3 to v=5). ✓

### 1.2 Left-inverse projection identities — PASS

All four left-inverse identities consumed in the proj-sibling proofs
exist at `FieldGenericStar.lean:420-450` with closed proofs (no
`sorry`):

| Identity                                                  | Line | Status |
|-----------------------------------------------------------|------|--------|
| `starFirst_F_starEmbed1_F : starFirst_F (starEmbed1_F x) = x` | 420  | closed |
| `starFirst_F_starEmbed2_F : starFirst_F (starEmbed2_F x) = 0` | 426  | closed |
| `starSecond_F_starEmbed1_F : starSecond_F (starEmbed1_F x) = 0` | 434  | closed |
| `starSecond_F_starEmbed2_F : starSecond_F (starEmbed2_F x) = x` | 442  | closed |

Each proof is 3–6 lines using `ext` + `simp only` + `dif_pos`/`dif_neg`.
No proof-level dependency on a `sorry`'d helper.

### 1.3 Proof bodies — PASS

Each proj-sibling proof is the same 3-line pattern:

```lean
have h := hW_pull _ hmem
rw [map_add, ⟨first identity⟩, ⟨second identity⟩, add_zero/zero_add] at h
exact h
```

E.g., `d5tilde_core_F_proj1` rewrites `starFirst_F (starEmbed1_F x +
starEmbed2_F z) = x + 0 = x` then concludes from the pull image. The
proofs are correct and minimal.

---

## 2. Half-conclusion design audit (D2) — AGREE with worker

The worker's progress note (`progress/20260518T070149Z_4141c541.md`,
§"Deviation from spec") argues that the joint conclusion
`x ∈ W ⟨0⟩ ∧ z ∈ W ⟨1⟩` is **not derivable** from a single
reversed-direction pull plus a single canonical-direction push
hypothesis set.

This audit independently verifies that argument.

### 2.1 The structural obstruction

Take e02 reversed, e12 canonical as the prototype mixed sub-case.
Available hypotheses (specialized to `Wmain`):

- Pull `hMain_20 : Wmain ⟨2⟩ → Wmain ⟨0⟩` via `starFirst_F`.
- Pull `hOther_20 : Wother ⟨2⟩ → Wother ⟨0⟩` via `starFirst_F`.
- Push `hMain_12 : Wmain ⟨1⟩ → Wmain ⟨2⟩` via `starEmbed2_F`.
- Push `hOther_12 : Wother ⟨1⟩ → Wother ⟨2⟩` via `starEmbed2_F`.
- Complementarity `∀ v, IsCompl (Wmain v) (Wother v)`.
- `hmem : starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨2⟩`.

Goal: derive `x ∈ Wmain ⟨0⟩ ∧ z ∈ Wmain ⟨1⟩`.

The first conjunct `x ∈ Wmain ⟨0⟩` falls out of `_proj1`.

The second conjunct `z ∈ Wmain ⟨1⟩` cannot be obtained from these
hypotheses. The canonical `core_F` decomposition tries to write
`z = c + d` with `c ∈ Wmain ⟨1⟩`, `d ∈ Wother ⟨1⟩`, then shows
`d = 0`. That argument needs to subtract the Wother-part of
`hmem`; doing so requires a canonical-direction push
`Wmain ⟨0⟩ → Wmain ⟨2⟩` for the first leaf to separate
`starEmbed1_F x = starEmbed1_F a + starEmbed1_F b`
(`a ∈ Wmain ⟨0⟩`, `b ∈ Wother ⟨0⟩`) into Wmain and Wother parts.
With only the reversed 2→0 pull available for that leaf, the
canonical-style decomposition cannot run.

Alternative: apply `starSecond_F` to `hmem`. This recovers `z` as
the second-coordinate projection, but the resulting membership is
`z ∈ starSecond_F (Wmain ⟨2⟩)` — and `starSecond_F (Wmain ⟨2⟩)
⊆ Wmain ⟨1⟩` is exactly the **reversed e12 pull hypothesis**,
which is unavailable in the (e02 reversed, e12 canonical) sub-case.

### 2.2 Verdict

The half-conclusion form is the **right primitive**.

The "joint conclusion" version proposed in the issue body is
recoverable only when:

1. **Both leaves are reversed** — `_proj1` and `_proj2` are
   simultaneously applicable. Composing them gives the full
   conjunction. This is 8 of the 31 sub-cases (e02 ∧ e12 reversed,
   any e23/e43/e53 directions); analogously 8 sub-cases for
   (e43 ∧ e53 reversed) at v=3.
2. **Both leaves are canonical** — `core_F` / `core3_F` directly apply.

In the mixed sub-cases (one leaf canonical, one reversed) the
joint conclusion is genuinely unavailable; the half-conclusion is
all the local hypothesis set affords.

### 2.3 Wrapper recommendation — NOT NEEDED

A "both leaves reversed" convenience wrapper that bundles `_proj1
∧ _proj2` for the 8 sub-cases at v=2 (and analogously at v=3)
would amount to a one-line `⟨_proj1 _ _ _ _ _ _ _ hmem,
_proj2 _ _ _ _ _ _ _ hmem⟩` at the use site. The wrapper saves
roughly one line per call site at the cost of one new top-level
declaration plus its docstring. The audit does not recommend
adding it — the inline application is clear at the call site and
keeps the API surface minimal.

The half-conclusion form is **strictly more flexible** than the
joint conclusion: a sub-case with only one leaf reversed uses
only that side's proj-sibling and derives the other half by
whatever local argument fits (typically the γ-containment chain;
see D3 below). The bundled-conjunction form would force callers
in the mixed sub-cases to do extra unbundling work that the
half-conclusion form avoids.

---

## 3. Downstream readiness for #2853 (D3) — HIGH

### 3.1 The 31 sub-cases — case-split structure

`d5tildeRep_kQ_leaf_equalities` (`FieldGenericD5Tilde.lean:798`)
nests five `rcases` on the directions of edges e02 → e12 → e23 →
e43 → e53. Each `rcases` has two branches; the canonical branch
(`Or.inl`) is descended into, the reversed branch falls out as a
`sorry`:

| Sorry line | Branch (this edge reversed) | Outer edges                    | Sub-cases |
|------------|------------------------------|--------------------------------|-----------|
| 934        | e02 reversed                 | (none)                         | 16        |
| 932        | e12 reversed                 | e02 canon                      | 8         |
| 930        | e23 reversed                 | e02, e12 canon                 | 4         |
| 928        | e43 reversed                 | e02, e12, e23 canon            | 2         |
| 926        | e53 reversed                 | e02, e12, e23, e43 canon       | 1         |

Total: 16 + 8 + 4 + 2 + 1 = **31** sub-cases. Each sorry is the
root of a sub-tree over the inner-edge directions that the
downstream worker must still case-split internally (or hoist via
helper lemmas).

### 3.2 Proj-sibling applicability per sub-case

Within each sub-tree, the four proj-siblings apply to each
reversed-leaf-edge slot:

- **e02 reversed** ⇒ `d5tilde_core_F_proj1` applies to recover
  `x ∈ W ⟨0⟩` (the first half of the v=2 decomposition).
- **e12 reversed** ⇒ `d5tilde_core_F_proj2` recovers
  `z ∈ W ⟨1⟩`.
- **e43 reversed** ⇒ `d5tilde_core3_F_proj1` recovers
  `x ∈ W ⟨4⟩`.
- **e53 reversed** ⇒ `d5tilde_core3_F_proj2` recovers
  `z ∈ W ⟨5⟩`.

For each sorry root, the inner-edge case-split decides which
proj-siblings apply at each leaf:

#### Sorry 934 — e02 reversed (16 sub-cases)

- `d5tilde_core_F_proj1`: **all 16 sub-cases** (the e02-reversed
  hypothesis is fixed in this scope).
- `d5tilde_core_F_proj2`: 8 of 16 (the inner e12-reversed branch).
- `d5tilde_core3_F_proj1`: 8 of 16 (inner e43-reversed).
- `d5tilde_core3_F_proj2`: 8 of 16 (inner e53-reversed).
- Inline `gammaInv_embed*_F`: 8 of 16 (inner e23-reversed).

#### Sorry 932 — e02 canon, e12 reversed (8 sub-cases)

- `d5tilde_core_F_proj2`: **all 8** (e12 reversed fixed).
- The e02-canonical leaf gives a push `Wmain ⟨0⟩ → Wmain ⟨2⟩`,
  i.e., the canonical input for `core_F`'s `hMain_02` slot, but
  `core_F` cannot be applied directly (it needs e12 also canonical
  for the second leaf). The other half (`x ∈ W ⟨0⟩`) of the v=2
  decomposition must be derived from the downstream γ-containment
  chain, not from a local v=2 core call.
- v=3 proj-siblings: applicable per inner e43/e53 split.
- Inline `gammaInv_embed*_F`: 4 of 8 (inner e23-reversed).

#### Sorry 930 — e02, e12 canon, e23 reversed (4 sub-cases)

- **No v=2 proj-sibling applies** (both leaves canonical at v=2).
  Local v=2 reasoning uses canonical `core_F` directly.
- v=3 proj-siblings: applicable per inner e43/e53 split (3 of 4
  sub-cases have ≥1 v=3 leaf reversed).
- **Inline `gammaInv_embed*_F`: all 4** (e23 reversed fixed). The
  central γ-edge is the inv-direction; `d5tilde_gamma_containment_F`
  does not apply unchanged.

#### Sorry 928 — e02, e12, e23 canon, e43 reversed (2 sub-cases)

- `d5tilde_core3_F_proj1`: **both 2** (e43 reversed fixed).
- `d5tilde_core3_F_proj2`: 1 of 2 (inner e53-reversed).
- v=2 reasoning canonical (`core_F` applies).
- γ-containment canonical (`d5tilde_gamma_containment_F` applies
  modulo the v=3 leaf hypothesis swap).

#### Sorry 926 — e02, e12, e23, e43 canon, e53 reversed (1 sub-case)

- `d5tilde_core3_F_proj2`: applies.
- v=2 reasoning canonical; γ-containment canonical except for
  the e53 leaf swap.

### 3.3 The single outlier — e23-reversed-only sub-case

Of the 31 sub-cases, exactly **one** uses no proj-sibling: the
sub-case at sorry 930 where the inner case-split lands on
(e43 canon, e53 canon). All four leaf edges (e02, e12, e43, e53)
are canonical; only the central γ-edge e23 is reversed.

This is the sub-case earmarked for inline `gammaInv_embed1_plus_embed2_F`
and `gammaInv_embed1_plus_embedNshift_F` per #2869's structural
finding (`progress/2026-05-18T09-04-43Z_bcc5a2ad.md`). The local
v=2 / v=3 cores are canonical, so the only inv-direction work is
re-routing the γ-containment chain through the closed-form γ⁻¹
identities (which exist at `FieldGenericD5Tilde.lean:426-459`
with closed proofs).

### 3.4 e23-reversed group at sorry 930 — confirmed inline-only

The issue body asks specifically whether **all 4 sub-cases at
line 930 (e23 reversed) need inline `gammaInv_embed*_F` rather
than a proj-sibling call**.

Answer: **yes**. e23 is the central γ-edge, not a leaf edge; no
proj-sibling targets the v=2 ↔ v=3 bridge (the four proj-siblings
all target leaf vertices 0/1/4/5). Within the e23-reversed group,
three of four sub-cases additionally use a v=3 proj-sibling (when
e43 or e53 is also reversed), but the γ-bridge itself always
requires `gammaInv_embed*_F`.

### 3.5 Quantification vs the wave-60 "24 of 31" claim

The wave-60 audit §3 stated "24 of 31 sub-cases need
direction-reversed sibling lemmas". This figure is the count of
sub-cases with **at least one v=2 leaf reversed** (e02 or e12):

- (e02 ∨ e12 reversed) × (any e23, e43, e53) = (2² − 1) × 2³ = 24
  combinations out of the 2⁵ − 1 = 31 non-canonical combinations.

The wave-60 audit predates the v=3 proj-siblings (`_proj1` /
`_proj2` for `core3_F`). PR #2871 added the v=3 variants on top,
extending coverage:

- v=2 proj-siblings hit (at least one of `_proj1` / `_proj2`):
  **24 of 31** sub-cases (matches wave-60).
- v=3 proj-siblings hit (at least one of `core3_F_proj1` /
  `core3_F_proj2`): **24 of 31** sub-cases (symmetric: e43 ∨ e53
  reversed).
- **Either v=2 or v=3 proj-sibling applies**: **30 of 31**
  sub-cases. The one outlier is the e23-only-reversed case in §3.3.
- **Inline `gammaInv_embed*_F` needed**: **4 of 31** sub-cases
  (all 4 e23-reversed sub-cases at sorry 930).
- **Both a proj-sibling AND inline γ⁻¹ needed**: **3 of 31**
  (e23 reversed AND ≥1 v=3 leaf reversed).

So the wave-60 framing was incomplete; the actually-landed PR
#2871 has strictly broader coverage. **30 of 31 sub-cases have a
proj-sibling that applies; the remaining 1 is the e23-only-reversed
case where inline γ⁻¹ is the entire story.**

### 3.6 No gaps detected

Every reversed sub-case has the primitive it needs:

- ≥1 reversed leaf edge: ≥1 proj-sibling applies (30 sub-cases).
- e23 reversed: inline `gammaInv_embed*_F` (4 sub-cases, overlap
  with above in 3).
- Pure e23-reversed sub-case: pure inline γ⁻¹ (1 sub-case).

No sub-case lacks a primitive. The 4 proj-siblings + the 2
closed-form γ⁻¹ identities (`gammaInv_embed1_plus_embed2_F`,
`gammaInv_embed1_plus_embedNshift_F`) form a complete primitive
set for #2853.

### 3.7 Open scope-shape question for #2853 (not a blocker)

The leaf-equality conclusion is
`W₁ ⟨0⟩ = W₁ ⟨1⟩ ∧ W₁ ⟨0⟩ = W₁ ⟨4⟩ ∧ W₁ ⟨0⟩ = W₁ ⟨5⟩` —
three equalities chained via the four leaf vertices `{0, 1, 4, 5}`.
The canonical-direction branch (lines 843–924) derives these from
`compl_le_forces_eq` applied to four containment facts coming out
of `d5tilde_gamma_containment_F`:

- `W₁ ⟨0⟩ ⊆ W₁ ⟨4⟩` ⇒ via `compl_le_forces_eq` ⇒ `=`.
- `W₁ ⟨0⟩ ⊆ W₁ ⟨5⟩` ⇒ `=`.
- `W₁ ⟨1⟩ ⊆ W₁ ⟨4⟩` ⇒ `=`.
- Then chains 01 via 14.

In the reversed sub-cases, the proj-siblings give containments
**from the v=2/v=3 centers outward to the leaves** (e.g.,
e02 reversed gives `Wmain ⟨2⟩ → Wmain ⟨0⟩` membership info),
not the leaf-to-leaf chains `compl_le_forces_eq` consumes. The
downstream worker must compose the proj-sibling outputs with the
canonical pushes (where available) and/or the inv-direction γ⁻¹
identities to recover the leaf-to-leaf containments.

This is a **scope-shape question for #2853's eventual /replan**,
not a primitive-level gap. The proj-siblings provide the
per-(F, Q) replacement for the canonical pushes that
`d5tilde_gamma_containment_F` consumes; the worker needs to thread
them through analogous γ-containment chains for each reversed
sub-case. The recommended decomposition for #2853 is the
4-sub-issue split by reversed-edge group suggested in
`progress/2026-05-18T09-04-43Z_bcc5a2ad.md` (next step item 1):
e02-reversed group (16), e12-reversed (8), e23-reversed (4), and
the v=3-only-reversed group (2 + 1 = 3).

---

## 4. Summary

PR #2871's four proj-sibling lemmas are correctly stated, soundly
proved, and consume well-formed left-inverse identities. The
half-conclusion form is the right primitive (per §2). Downstream
coverage for #2853 is high: 30 of 31 reversed sub-cases have a
directly applicable proj-sibling, and the one outlier matches the
pre-identified inline-γ⁻¹ strategy from #2869's closure analysis.

No follow-up issues filed. The proj-sibling design + inline γ⁻¹
strategy are jointly sufficient for the 31 reversed sub-cases.

Verdict: **PASS**.
