# Review — Ch3 Theorem 3.10.2: Irreducible representations of tensor products of algebras

- **Issue:** #7192 (review, report-only)
- **Reviewer session:** `/work` → `/review` worker, branch `agent/b0171c30`
- **Target:** `EtingofRepresentationTheory/Chapter3/Theorem3_10_2.lean` (734 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter3/Theorem3.10.2.md`, `blobs/Chapter3/Discussion_before_Theorem3.10.2.md`, `blobs/Chapter3/Discussion_proof_of_Theorem3.10.2.md`
- **Focus areas:** statement fidelity of part (i) irreducibility / part (ii) existence / part (ii) uniqueness; genuineness of "irreducible" (no-nontrivial-invariant-submodule, quantified over **all** `a•` and `b•`); faithfulness of the `(a⊗b)•(v⊗w) = (a•v)⊗(b•w)` action; `≃ₗ`-level (not dimension-only) uniqueness; `[IsAlgClosed k]` faithfulness; non-vacuity witness; axiom cleanliness (report-only, no proof edits)
- **Overall verdict:** **FAITHFUL.** All four headline declarations build (`lake build` exit 0, 1950 jobs) and are axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). Part (i) (`tensor_product_irreducible`), part (ii)-existence (`tensor_product_irreducible_classification`), and part (ii)-uniqueness (`tensor_left_factor_unique` / `tensor_product_irreducible_classification_unique`) each faithfully transcribe the book. "Irreducible" is the genuine only-`⊥`-or-`⊤` invariant-submodule condition, quantified over **all** `a` (both `A`) and `b` (both `B`); the action is the real `(a⊗b)•(v⊗w)=(a•v)⊗(b•w)` via `Algebra.lsmul` and `SMulCommClass A B M`, not a surrogate; uniqueness is a genuine `V ≃ₗ[A] V'` / `W ≃ₗ[B] W'` isomorphism of the matched factors, not dimension-only. `[IsAlgClosed k]` is a faithful (not weakening) hypothesis, load-bearing in part (i)/existence via the density theorem. Non-vacuity confirmed with a **compiled** witness. **Two documented scope nuances** (neither a defect): part (i) states the only-trivial-invariant-submodule half and leaves nontriviality of `V ⊗ W` implicit (automatic from simplicity of `V`, `W`); the two uniqueness theorems do **not** require `[IsAlgClosed k]` (a faithful strengthening, since Schur's lemma needs only simplicity). The `items.json` `fidelity: verified` marker is confirmed correct. **No follow-up issue filed.**

---

## 0. Build and axiom-cleanliness audit

`lake exe cache get` (cache hit, no downloads) then
`lake build EtingofRepresentationTheory.Chapter3.Theorem3_10_2` — **exit 0, 1950 jobs**
(Mathlib cached). `#print axioms` via a scratch importer on the four headline declarations:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.tensor_product_irreducible` | 127 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.tensor_product_irreducible_classification` | 250 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.tensor_left_factor_unique` | 632 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.tensor_product_irreducible_classification_unique` | 705 | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no custom axiom. `grep` for `sorry|admit|proof_wanted` in the file returns
nothing. The supporting private lemmas (`map_smulRight_smulRight_eq`,
`pure_tensors_mem_of_stable`, `exists_functional_ne_zero`, `tmul_ne_zero`,
`exists_contraction_ne_zero`, `lid_map_eq_apply_rid`, `rid_mapψ_lsmul`, `comm_map_apply`)
and the `Part2Helpers` data (`homBSMul`, `homBModule`, `evalMap`) feed the axiom-clean
headline results, so they are transitively `sorry`-free. `evalMap` (line 220) and `homBSMul`
(line 197) are real `def`s with genuine bodies (no sorried data); `homBModule` (line 205) is
a real `Module B` instance. The load-bearing dependency
`Etingof.density_theorem_part1` (`Chapter3/Theorem3_2_2.lean:19`, Jacobson/Burnside
surjectivity `A → End_k V` for simple fin-dim `V` over alg-closed `k`) is transitively
`sorry`-free (the axiom check would surface any `sorryAx` otherwise). Build emits only
cosmetic lints (a `show`→`change` suggestion at line 413, two long-line warnings at 273/655,
a `push_neg` deprecation at 661) — no correctness or fidelity impact.

---

## 1. Book statement and the Lean rendering

**Book (Theorem 3.10.2, verbatim):**
> *(i) Let `V` be an irreducible finite dimensional representation of `A` and let `W` be an
> irreducible finite dimensional representation of `B`. Then `V ⊗ W` is an irreducible
> representation of `A ⊗ B`.*
>
> *(ii) Any irreducible finite dimensional representation `M` of `A ⊗ B` has the form (i) for
> unique `V` and `W`.*

The book assumes throughout Chapter 3 that `k` is algebraically closed, and the proof of (i)
explicitly invokes the density theorem ("the maps `A → End V` and `B → End W` are
surjective"). The Lean file carries `[IsAlgClosed k]` accordingly.

---

## 2. Part (i) — `Etingof.tensor_product_irreducible` (FAITHFUL)

```lean
theorem Etingof.tensor_product_irreducible (k A B V W : Type*)
    [Field k] [IsAlgClosed k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule B W] :
    ∀ (U : Submodule k (V ⊗[k] W)),
      (∀ (a : A) (b : B) (x : V ⊗[k] W), x ∈ U →
        TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a)
          ((Algebra.lsmul k k W : B →ₐ[k] Module.End k W) b) x ∈ U) →
      U = ⊥ ∨ U = ⊤
```

Fidelity checks:

- **"Irreducible" is genuine.** `IsSimpleModule A V` / `IsSimpleModule B W` are the real
  no-nontrivial-submodule-plus-nontrivial conditions on the hypotheses. The conclusion
  `U = ⊥ ∨ U = ⊤` is the genuine only-trivial-invariant-submodule statement for `V ⊗ W`.
- **Invariance quantifies over ALL `a•` and `b•`, both factors.** The stability hypothesis is
  `∀ (a : A) (b : B) …`, i.e. over every pure-tensor action `(a⊗b)•`, not just one factor or
  one element. Because a `k`-submodule stable under the `k`-spanning set `{a⊗b}` of `A ⊗ B`
  is, by `k`-linearity and additivity of the action, stable under **all** of `A ⊗ B`, this is
  exactly "`U` is an `A ⊗ B`-submodule". So the theorem is the genuine irreducibility of
  `V ⊗ W` over `A ⊗ B`.
- **The action is the real `(a⊗b)•(v⊗w) = (a•v)⊗(b•w)`.** `Algebra.lsmul k k V a` is the
  endomorphism `v ↦ a • v`; `TensorProduct.map (lsmul a) (lsmul b)` on a pure tensor gives
  `(a•v) ⊗ (b•w)`. This is the honest `A ⊗ B`-action, not a weaker surrogate.
- The proof faithfully follows the book: `density_theorem_part1` gives surjectivity of
  `A → End_k V` and `B → End_k W`, so `U` is stable under all `TensorProduct.map f g`
  (`f ∈ End_k V`, `g ∈ End_k W`); a rank-one contraction then extracts an arbitrary pure
  tensor from any nonzero `u ∈ U`, forcing `U = ⊤`.

**Scope nuance (not a defect):** the statement provides the only-`⊥`-or-`⊤` half of
"irreducible" and leaves the nontriviality `V ⊗ W ≠ 0` (i.e. `⊥ ≠ ⊤`) implicit. This is
automatic — `V`, `W` are simple hence nonzero, so `V ⊗ W ≠ 0` over a field — and matches the
project's standard rendering of irreducibility as `eq_bot_or_eq_top` (identical convention in
part (ii)'s `hM` hypothesis). No content is lost.

---

## 3. Part (ii) existence — `Etingof.tensor_product_irreducible_classification` (FAITHFUL)

```lean
theorem …classification (k A B : Type*) (M : Type u)
    [Field k] [IsAlgClosed k] … [FiniteDimensional k M]
    [Module A M] [IsScalarTower k A M] [Module B M] [IsScalarTower k B M]
    [SMulCommClass A B M] [Nontrivial M]
    (hM : ∀ (U : Submodule k M),
      (∀ (a : A) (x : M), x ∈ U → a • x ∈ U) →
      (∀ (b : B) (x : M), x ∈ U → b • x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ V W … (_ : IsSimpleModule A V) … (_ : IsSimpleModule B W) (e : M ≃ₗ[k] V ⊗[k] W),
      (∀ a m, e (a • m) = TensorProduct.map ((Algebra.lsmul k k V) a) LinearMap.id (e m)) ∧
      (∀ b m, e (b • m) = TensorProduct.map LinearMap.id ((Algebra.lsmul k k W) b) (e m))
```

Fidelity checks:

- **"Irreducible `M` of `A ⊗ B`" is faithfully encoded.** `M` carries commuting `A`- and
  `B`-actions (`SMulCommClass A B M`) with a shared `k`-scalar structure
  (`IsScalarTower k A M`, `IsScalarTower k B M`) — this is precisely an `A ⊗ B`-module
  structure. `hM` is the genuine irreducibility condition: a `k`-submodule invariant under
  **both** the `A`- and the `B`-action is exactly an `A ⊗ B`-submodule, and `hM` says the
  only such are `⊥` and `⊤`. `[Nontrivial M]` supplies `M ≠ 0`.
- **"`M` has the form `V ⊗ W`" is a genuine `A ⊗ B`-module isomorphism.** The witness `e` is
  a `k`-linear equivalence `M ≃ₗ[k] V ⊗ W` that is simultaneously `A`-equivariant (`A` on the
  left factor) and `B`-equivariant (`B` on the right factor) — together, `A ⊗ B`-equivariant.
  So `M ≅ V ⊗ W` as `A ⊗ B`-modules, exactly the book's "has the form (i)".
- **`V`, `W` are genuinely irreducible:** `IsSimpleModule A V` and `IsSimpleModule B W` are
  produced as part of the existential, matching "irreducible `V` … irreducible `W`".
- The proof faithfully follows the book's existence argument (extract a simple `A`-submodule
  `V₀ ⊆ M` via Artinian/atomic, set `W₀ = Hom_A(V₀, M)` with the `(b·f)(v) = b·(f v)`
  `B`-action, prove the evaluation map `V₀ ⊗ W₀ → M`, `v ⊗ f ↦ f v`, bijective — surjective
  by `A`-`B`-invariance of its image + irreducibility, injective by the density theorem — and
  a `finrank` argument gives simplicity of `W₀`). `evalMap` and `homBSMul` are real `def`s.

---

## 4. Part (ii) uniqueness — `tensor_left_factor_unique` / `…_classification_unique` (FAITHFUL)

```lean
theorem Etingof.tensor_left_factor_unique
    {k A V W V' W' : Type*} [Field k] [Ring A] [Algebra k A] …
    [FiniteDimensional k W] [Nontrivial W] …
    [IsSimpleModule A V] [IsSimpleModule A V']
    (e : V ⊗[k] W ≃ₗ[k] V' ⊗[k] W')
    (hA : ∀ a x, e (map (lsmul a) id x) = map (lsmul a) id (e x)) :
    Nonempty (V ≃ₗ[A] V')

theorem Etingof.tensor_product_irreducible_classification_unique
    {k A B V W V' W' : Type*} … [IsSimpleModule A V] [IsSimpleModule A V']
    [IsSimpleModule B W] [IsSimpleModule B W']
    (e : V ⊗[k] W ≃ₗ[k] V' ⊗[k] W')
    (hA : …left-factor A-equivariance…) (hB : …right-factor B-equivariance…) :
    Nonempty (V ≃ₗ[A] V') ∧ Nonempty (W ≃ₗ[B] W')
```

Fidelity checks:

- **Uniqueness is a genuine module isomorphism, not dimension-only.** The conclusions are
  `Nonempty (V ≃ₗ[A] V')` and `Nonempty (W ≃ₗ[B] W')` — honest `A`-linear and `B`-linear
  equivalences of the matched factors. This is strictly stronger than "same dimension".
- **The hypothesis is genuine `A ⊗ B`-equivariance.** `e` is assumed both `A`-equivariant on
  the left factor (`hA`) and `B`-equivariant on the right factor (`hB`); together this is an
  `A ⊗ B`-module isomorphism `V ⊗ W ≃ V' ⊗ W'`.
- **This is the book's "for unique `V` and `W`".** As the docstring notes, given two
  factorizations `M ≅ V ⊗ W` and `M ≅ V' ⊗ W'` (both from part (ii)-existence), composing the
  two equivalences yields exactly such an `A`-`B`-equivariant `e`, so `V ≅ V'` and `W ≅ W'`.
- The proof is genuine Schur's lemma: a suitable contraction
  `v ↦ rid (map id ψ (e (v ⊗ w₀)))` is an `A`-linear map `V → V'`, nonzero for a suitable
  `ψ`, hence bijective (`LinearMap.bijective_of_ne_zero` on simple modules). The `W`-factor
  follows by the factor-swap `comm` equivalence.

**Scope nuance (not a defect):** the two uniqueness theorems carry **no** `[IsAlgClosed k]`
hypothesis. This is correct and a faithful strengthening — Schur's lemma between simple
modules needs only simplicity, not algebraic closure — so the uniqueness half holds more
generally than the (density-theorem-bound) existence half.

---

## 5. `[IsAlgClosed k]` faithfulness

`[IsAlgClosed k]` faithfully renders Etingof's standing Chapter 3 hypothesis. It is
load-bearing (not decorative) in part (i) and part (ii)-existence: both route through
`Etingof.density_theorem_part1`, whose surjectivity conclusion requires an algebraically
closed field (it is the Burnside/Jacobson density theorem). The module docstring correctly
records the sharpness: without algebraic closure, `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` is a counterexample to
(i) (this is the content of the file's companion `Remark3_10_3`, which formalizes the
infinite-dimensional obstruction `¬ IsField (ℂ(x) ⊗ ℂ(x))`). No hidden weakening: `k` is a
genuine algebraically closed field, and the finite-dimensionality hypotheses on `A`, `B`,
`V`, `W`, `M` match the book's "finite dimensional".

---

## 6. Non-vacuity

The hypotheses are simultaneously satisfiable. Concrete witness `A = B = k`, `V = W = k`
(`k` any algebraically closed field), verified by a **compiling** scratch check:

```lean
variable (k : Type*) [Field k] [IsAlgClosed k]

example : ∀ (U : Submodule k (k ⊗[k] k)),
    (∀ (a b : k) (x : k ⊗[k] k), x ∈ U →
      TensorProduct.map ((Algebra.lsmul k k k) a) ((Algebra.lsmul k k k) b) x ∈ U) →
    U = ⊥ ∨ U = ⊤ :=
  Etingof.tensor_product_irreducible k k k k k          -- typechecks: all instances resolve

example : IsSimpleModule k k := inferInstance            -- the witness's simplicity hypothesis
```

Every required instance (`FiniteDimensional k k`, `IsSimpleModule k k` for both factors)
resolves, so `Etingof.tensor_product_irreducible k k k k k` is a well-typed application to a
genuinely inhabited hypothesis set — the theorem is **not** vacuously true. (`k ⊗ k ≅ k` is
one-dimensional, so its only submodules are indeed `⊥` and `⊤`, consistent with the
conclusion.) The same `A = B = k`, `M = k` instantiation witnesses part (ii)-existence
(`M = k` nontrivial and irreducible), and `V = V' = W = W' = k` witnesses uniqueness.

---

## 7. Verdict and disposition

**FAITHFUL.** All four headline declarations build, are axiom-clean (no `sorryAx`),
non-vacuous, and faithfully render Theorem 3.10.2 parts (i) / (ii)-existence /
(ii)-uniqueness: genuine irreducibility quantified over both factors, the real
`(a⊗b)•(v⊗w)=(a•v)⊗(b•w)` action, `≃ₗ`-level uniqueness of the matched factors, and a
faithful load-bearing `[IsAlgClosed k]`. The two documented scope nuances (implicit
nontriviality in part (i); `[IsAlgClosed k]`-free uniqueness) are faithful conventions /
strengthenings, not defects. The existing `progress/items.json` `fidelity: verified` marker
for `Chapter3/Theorem3.10.2` is confirmed correct; no change to `items.json` is required.
**No follow-up issue filed.**
