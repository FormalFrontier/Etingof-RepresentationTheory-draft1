# Review — Ch7 Lemma 7.5.1: The Yoneda Lemma

- **Issue:** #7117 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/50c30438`
- **Target:** `EtingofRepresentationTheory/Chapter7/Lemma7_5_1.lean` (34 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter7/Lemma7.5.1.md` (the `.refs.md` companion named in the
  issue does not exist in the tree — no external refs to cross-check; not a defect)
- **Focus areas:** statement fidelity against the book's representing-object-uniqueness form;
  genuine `∃!` (uniqueness, not merely existence); arbitrary category, genuine iso conclusion;
  vacuity / hidden-`sorry`-via-axiom check (report-only, no `.lean` edits)
- **Overall verdict:** **FAITHFUL.** The single public result `Etingof.yoneda_lemma` is a correct
  transcription of the book's Lemma 7.5.1 in its *representing-object-uniqueness* form (not the
  general Yoneda bijection), with genuine `∃!`, an arbitrary category, and a genuine isomorphism
  conclusion. It builds (exit 0, 608 jobs) and is axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no custom axiom). **No defect filed.**
  One fidelity nuance is recorded and dispositioned below: the formalization represents the book's
  `Hom(X, ?)` (covariant) by `yoneda.obj X = Hom(?, X)` (contravariant). This is the *dual*
  representable functor, equally strong and equally true because `yoneda` is fully faithful exactly
  as `coyoneda` is; the uniqueness-of-representing-object content is identical, so it is a benign
  convention variance, not a weakening.

---

## 0. Build and axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter7.Lemma7_5_1` (exit 0, **608 jobs**). The file has a
single public declaration; `#print axioms` on it:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.yoneda_lemma` | 25 | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no custom axiom. `grep` for `sorry`/`admit`/`proof_wanted` and for
`True`/`by trivial` placeholders returns nothing. The declaration is a `theorem` (not a `def`), so
there is no data body to construct; the proof is genuine (see §3).

---

## 1. Statement fidelity

**Book (Lemma 7.5.1):** "If a functor `F` is represented by an object `X`, then `X` is unique up to
a unique isomorphism. I.e., if `X, Y` are two objects in `𝒞`, then for any isomorphism of functors
`φ : Hom(X, ?) → Hom(Y, ?)` there is a unique isomorphism `a_φ : X → Y` inducing `φ`."

**Lean:**
```lean
theorem Etingof.yoneda_lemma {C : Type*} [Category C]
    (X Y : C) (φ : yoneda.obj X ≅ yoneda.obj Y) :
    ∃! (a : X ≅ Y), yoneda.map a.hom = φ.hom
```

Point-by-point against the deliverables in #7117:

1. **"Representing-object-uniqueness" form vs. general Yoneda bijection.** The book states the
   *corollary* form — a representable functor determines its representing object up to a unique
   isomorphism — **not** the general Yoneda bijection `Nat(Hom(X,-), F) ≅ F(X)`. The Lean statement
   matches the form the book actually asserts: it takes an iso of the two representable functors and
   returns a unique iso of the representing objects. It is **not** a hidden weakening to the general
   bijection, nor a strengthening to it. ✔

2. **"Isomorphism of functors."** `φ : yoneda.obj X ≅ yoneda.obj Y` is an iso in the functor
   category `Cᵒᵖ ⥤ Type`, i.e. a natural isomorphism of the representable functors — exactly the
   book's "isomorphism of functors". ✔

3. **Genuine uniqueness.** The conclusion is `∃!` over `a : X ≅ Y`, i.e. existence **and**
   uniqueness — the book's "unique isomorphism `a_φ`". It is not the weaker `∃`. ✔

4. **"Inducing `φ`."** The pinning condition is `yoneda.map a.hom = φ.hom`. `yoneda.map a.hom` is
   the natural transformation induced by the underlying morphism `a.hom : X → Y`, so requiring it to
   equal `φ.hom` is precisely "`a_φ` induces `φ`". Pinning the `.hom` component is sufficient:
   a natural iso is determined by its `hom`, and `yoneda.map` of an iso is the iso whose `hom` is
   `yoneda.map a.hom`, so this correctly singles out `a`. ✔

5. **Arbitrary category, genuine iso conclusion.** `C : Type*` with `[Category C]` and arbitrary
   objects `X Y : C` — no silent specialization to a concrete category. The output `a : X ≅ Y` is a
   genuine `CategoryTheory` isomorphism (`X ≅ Y`), not a placeholder or a bare morphism. ✔

---

## 2. Fidelity nuance — covariant `Hom(X, ?)` vs. Mathlib's contravariant `yoneda.obj X`

The one point that deserves explicit attention. In Mathlib
(`Mathlib/CategoryTheory/Yoneda.lean:43`):

```lean
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X := { obj Y := (unop Y) ⟶ X, map f := ↾fun g ↦ f.unop ≫ g }
  ...
```

so `yoneda.obj X` is the **contravariant** representable `Hom(?, X)` (the functor `Y ↦ (Y ⟶ X)`),
whereas the book writes the **covariant** `Hom(X, ?)` (which in Mathlib is `coyoneda.obj (op X)`,
the functor `Y ↦ (X ⟶ Y)`).

**Disposition: benign, not a defect.** The formalized statement is the *dual* of the printed one,
obtained by reversing every arrow in `𝒞`. It is neither weaker nor stronger:

- Both `yoneda : C ⥤ (Cᵒᵖ ⥤ Type)` and `coyoneda : Cᵒᵖ ⥤ (C ⥤ Type)` are fully faithful, so the
  uniqueness-of-representing-object conclusion holds verbatim for either. The proof here rests only
  on `Yoneda.fullyFaithful` — the identical fact holds via `Coyoneda.fullyFaithful`.
- The lemma's mathematical content — "a representable functor determines its representing object up
  to a unique isomorphism" — is direction-agnostic; the book's `Hom(X, ?)` is merely Chapter 7's
  running convention for the representable functor.
- Instantiating the Lean theorem on `Cᵒᵖ` recovers the book's covariant statement on `C` verbatim
  (since `coyoneda`-representability on `C` is `yoneda`-representability on `Cᵒᵖ`), so the two are
  interderivable with no loss.

The file's docstring/module comment reproduces the book's `Hom(X, ?)` wording while the code uses
`yoneda.obj X`; a reader comparing the two should understand this is the dual representable. This is
a documentation nicety, not a correctness issue, and the issue scopes edits to "minimal" — I have
left the proof untouched and recorded the variance here rather than reword the docstring, since the
existing text is faithful to the book it quotes.

---

## 3. Non-vacuity of the proof

The proof is genuine, not a vacuous or circular discharge:

```lean
refine ⟨Yoneda.fullyFaithful.preimageIso φ, ?_, ?_⟩
· exact Yoneda.fullyFaithful.map_preimage φ.hom          -- the witness induces φ
· intro b hb                                             -- uniqueness
  apply Yoneda.fullyFaithful.isoEquiv.injective
  ext1
  exact hb.trans (Yoneda.fullyFaithful.map_preimage φ.hom).symm
```

- **Existence witness:** `Yoneda.fullyFaithful.preimageIso φ : X ≅ Y` — the actual preimage
  isomorphism under the fully-faithful Yoneda embedding, matching the book's construction
  `a_φ = φ_Y⁻¹(1_Y)` (full faithfulness packages the same content).
- **Induces `φ`:** `map_preimage` gives `yoneda.map (preimageIso φ).hom = φ.hom`.
- **Uniqueness:** any `b` with `yoneda.map b.hom = φ.hom` is pushed through injectivity of the
  fully-faithful `isoEquiv`, so `b = preimageIso φ`.

This is the standard, non-circular proof of the corollary via full faithfulness of the Yoneda
embedding. The `∃!` is real on both halves.

---

## 4. Verdict

**FAITHFUL.** `Etingof.yoneda_lemma` correctly formalizes Etingof Lemma 7.5.1 in its
representing-object-uniqueness form: genuine `∃!`, arbitrary category, genuine `X ≅ Y` conclusion,
correct "inducing `φ`" pinning. Axiom-clean (`[propext, Classical.choice, Quot.sound]`), 608-job
build, no `sorry`. The only nuance — Mathlib's `yoneda.obj X` is the contravariant `Hom(?, X)` dual
of the book's covariant `Hom(X, ?)` — is a benign convention variance (equal strength, same content,
interderivable on `Cᵒᵖ`), not a weakening or strengthening. **No defect issue filed.**
