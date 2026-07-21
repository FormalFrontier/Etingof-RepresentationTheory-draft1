# Statement-fidelity & non-vacuity audit — Ch8 Theorem 8.1.5 (characterizations of injective modules)

**Issue:** #7168
**File:** `EtingofRepresentationTheory/Chapter8/Theorem8_1_5.lean` (166 lines, sorry-free)
**Book source:** `blobs/Chapter8/Theorem8.1.5.md`
**Date:** 2026-07-21
**Verdict:** All three headline declarations **FAITHFUL**. No defect. Report-only; no feature follow-up filed.

---

## The book's theorem

Theorem 8.1.5 states the equivalence of three properties of a module `I`:

- **(i)** *Extension property*: for an injective `α : N → M` and any `ν : N → I`, there is `μ : M → I`
  with `μ ∘ α = ν`.
- **(ii)** *Splitting*: any injective `α : I → M` splits, i.e. there is `μ : M → I` with `μ ∘ α = id`.
- **(iii)** *Exactness*: the contravariant functor `Hom_A(?, I)` is exact.

The book proves "(i)⟹(ii)" and "(iii)⟹(i)" by analogy with Theorem 8.1.1, then "(ii)⟹(iii)" via the
pushout `E = (M ⊕ I)/N`. Note the book's Theorem 8.1.5 is *purely* the three-way equivalence — there is
no separate part 1/2/3 numbered content beyond conditions (i)/(ii)/(iii). Capturing (i)⇔(ii) and
(i)⇔(iii) therefore yields the **complete** theorem by transitivity; this is not a partial audit scope.

---

## Declaration 1 — `Etingof.Theorem_8_1_5_i_iff_ii` (`:44`) — FAITHFUL

```
Module.Injective R I ↔
  (∀ {M} [AddCommGroup M] [Module R M] (f : I →ₗ[R] M), Function.Injective f →
     ∃ g : M →ₗ[R] I, g.comp f = LinearMap.id)
```

- **LHS = condition (i).** `Module.Injective R I` is Mathlib's extension property. Its class field
  (`Mathlib/Algebra/Module/Injective.lean:61`) is
  `out : ∀ ⦃X Y : Type v⦄ … (f : X →ₗ Y), Injective f → (g : X →ₗ Q) → ∃ h : Y →ₗ Q, ∀ x, h (f x) = g x`,
  i.e. exactly "injective `f`, arbitrary `g` into `I`, extend `g` along `f`" — a verbatim match for the
  book's (i). Confirmed the forward proof uses `hI.out f hf LinearMap.id`, consuming the genuine field.
- **RHS = condition (ii), correct direction.** `f : I →ₗ M` is the injection *out of* `I`; the witness
  `g : M →ₗ I` satisfies `g.comp f = LinearMap.id`, i.e. `g ∘ f = id_I`. This is a genuine **retraction /
  left inverse** of `f` (so `I` is a direct summand of `M`) — matching the book's `μ ∘ α = id`, **not**
  the reversed "section" statement `f ∘ g = id`. Correct.
- **Proof content is real** (not `trivial`/`sorry`-adjacent). Forward: `hI.out`. Backward: the honest
  pushout construction `P = (I × Y)/K`, `K = range (g.prod (-α))`, with an explicit injectivity proof of
  `j = mkQ ∘ inl` and the extension `r ∘ k`. This is the book's `E = (M ⊕ I)/N` argument.

## Declaration 2 — `Etingof.Theorem_8_1_5_i_iff_iii` (`:109`) — FAITHFUL

```
Module.Injective R I ↔
  (∀ {K M N} … (ι : K →ₗ M) (π : M →ₗ N),
     Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π →
       Function.Injective (fun g : N →ₗ I => g ∘ₗ π) ∧
       (∀ h : M →ₗ I, h ∘ₗ ι = 0 ↔ ∃ g : N →ₗ I, g ∘ₗ π = h) ∧
       Function.Surjective (fun h : M →ₗ I => h ∘ₗ ι))
```

- **Hypotheses = short exact sequence `0 → K →[ι] M →[π] N → 0`.** `Function.Injective ι`
  (exactness at `K`), `Function.Surjective π` (exactness at `N`), `range ι = ker π` (exactness at `M`).
  Correct SES encoding. (The book labels its sequence `0 → N → M → K → 0`; the formalization's `K,M,N`
  is a pure relabeling with identical mathematical content.)
- **Conclusion = honest exactness of `Hom(-, I)`** applied to that SES, giving
  `0 → Hom(N,I) →[·∘π] Hom(M,I) →[·∘ι] Hom(K,I) → 0`:
  1. `Injective (·∘π)` — left exactness at `Hom(N,I)`;
  2. `∀ h, h∘ι = 0 ↔ ∃ g, g∘π = h` — exactness at the middle, i.e. `ker(·∘ι) = range(·∘π)` as a
     two-directional iff (both inclusions), not a one-sided weakening;
  3. `Surjective (·∘ι)` — right exactness onto `Hom(K,I)`.
  Conjunct 3 is precisely the extension property along the injection `ι : K → M`, hence the only conjunct
  carrying the injectivity content — accurately described in the docstring ("first two conjuncts hold for
  every module `I`"). No vacuous restatement.
- **Proof content is real.** Forward `(i)⟹(iii)`: conjunct 2's nontrivial direction is discharged by
  `(ker π).liftQ h hkh ∘ₗ (π.quotKerEquivOfSurjective hπ).symm`, and conjunct 3 by `hI.out`. Backward
  `(iii)⟹(i)`: instantiates the SES with `ι := α`, `π := (range α).mkQ`, extracting the surjectivity
  conjunct. The formalization proves the equivalence directly (a valid route) rather than the book's
  `(ii)⟹(iii)` cycle — not a fidelity concern.

## Declaration 3 — `Etingof.Theorem_8_1_5_Baer` (`:162`) — FAITHFUL (supplementary, correctly labeled)

```
Module.Injective R I ↔ Module.Baer R I
```

- `Module.Baer R I` is Mathlib's ideal-extension criterion (`Injective.lean:68`: every `g : I' →ₗ I`
  from an ideal `I' : Ideal R` extends to `R →ₗ I`). The proof is `Module.Baer.iff_injective.symm`.
- The docstring **explicitly** flags this as "a supplementary characterization, not one of the book's
  three conditions." No overclaim that Baer is condition (i)/(ii)/(iii). Faithful bookkeeping.

---

## Cross-cutting checks

- **`[Small.{v} R]` / universe setup — benign.** `Module.Injective` and its RHS quantify modules over
  `Type v` (same universe as `I : Type v`), the standard Mathlib phrasing. `Small.{v} R` is the ordinary
  universe-management hypothesis (used by `Baer.iff_injective`, `Injective.of_injective`). Setting
  `v := u` makes `Small.{u} (R : Type u)` automatic and lets modules range over `Type u`, recovering the
  book's arbitrary-module statement. Not a hidden restriction; no weakening of mathematical content.
- **Non-vacuity — confirmed.** `Module.Injective` genuinely discriminates: over a field every module is
  injective, whereas over `ℤ` the module `ℚ` (and `ℚ/ℤ`) is injective while `ℤ` itself is not — so the
  predicate is neither always-true nor always-false. Each iff's two directions carry real proof content
  (pushout quotient; `liftQ`/`quotKerEquivOfSurjective`), none reducible to `trivial`. The statement is
  not confined to `I = 0` or a semisimple ring.
- **Axiom cleanliness — PASS.** `#print axioms` on all three decls yields exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no custom axiom. (`Classical.choice` is
  expected from the Mathlib injective/quotient infrastructure.)
- **Build — PASS.** `lake build EtingofRepresentationTheory.Chapter8.Theorem8_1_5` → exit 0
  (1340 jobs). No `sorry`/`admit` in the file.

## Minor, non-blocking observation (not a defect)

Line 87 emits a `linter.style.show` warning: the `show (g x, (0:Y)) - ((0:I), α x) ∈ K` changes the goal
and should be `change`. Cosmetic style only — no bearing on statement fidelity or correctness. Not worth
a feature issue on its own.

---

## Conclusion

All three headline declarations of Theorem 8.1.5 are **FAITHFUL** to the book, axiom-clean, and
non-vacuous. Conditions (i)⇔(ii) and (i)⇔(iii) together capture the complete three-way equivalence; the
Baer equivalence is correctly labeled supplementary. **No genuine statement or vacuity defect found — no
feature follow-up issue filed.**
