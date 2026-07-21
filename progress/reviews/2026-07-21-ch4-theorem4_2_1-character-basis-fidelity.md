# Review — Ch4 Theorem 4.2.1: Irreducible characters form a basis of class functions

- **Issue:** #7141 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/78168514`
- **Target:** `EtingofRepresentationTheory/Chapter4/Theorem4_2_1.lean` (338 lines), sorry-free on `main`
- **Supporting infrastructure (all sorry-free):**
  `EtingofRepresentationTheory/Infrastructure/IrreducibleEnumeration.lean` (supplies
  `IrrepDecomp`, `columnFDRep`, `columnFDRep_simple/_injective/_surjective`, the
  Wedderburn-Artin `iso`), `Infrastructure/ColumnRepSimple.lean`,
  `Infrastructure/RegularCharacter.lean` (`d_cast_ne_zero`).
- **Fidelity reference:** `blobs/Chapter4/Theorem4.2.1.md` (+ `.refs.md`),
  `blobs/Chapter4/Introduction_4.2.md` (section standing definitions).
- **Focus areas:** statement fidelity of the spanning + independence pair against the
  book's "basis of `F_c(G,k)`"; whether the proof genuinely establishes completeness
  (not a short-circuit); the `[IsAlgClosed k]` hypothesis; de-duplication of the
  irreducible-character index set; non-vacuity; axiom cleanliness.
- **Overall verdict:** **FAITHFUL** (three declarations). No defect; no follow-up issue filed.
  The pair (`Etingof.Theorem4_2_1` spanning + `Etingof.Theorem4_2_1_linearIndependent`
  independence) faithfully renders "the characters of the irreducible representations form a
  basis of `F_c(G, k)`." The class-function condition, the index set, and the hypotheses all
  match the book. The proof route **differs from the book** (direct Wedderburn/orthogonality
  argument rather than Theorem 3.6.2 + the `(A/[A,A])*` identification) but is a valid,
  non-circular alternative proof of the same theorem. All three declarations build and are
  axiom-clean (no `sorryAx`).

---

## 0. Build and axiom-cleanliness audit

`lake exe cache get` then `lake build EtingofRepresentationTheory.Chapter4.Theorem4_2_1`
exits 0. `#print axioms` on all three declarations (via a scratch importer, since removed)
returns exactly the standard trio — **no `sorryAx`, no custom axiom**:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.classFunction_eq_zero_of_orthogonal_simples` | 184 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem4_2_1` | 197 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem4_2_1_linearIndependent` | 286 | `[propext, Classical.choice, Quot.sound]` |

A `sorry` grep over the target file and its three project infrastructure dependencies
(`IrreducibleEnumeration.lean`, `ColumnRepSimple.lean`, `RegularCharacter.lean`) returns 0
hits. The `IrrepDecomp` datum and every field/lemma the proofs project out (`n`, `d`,
`d_pos`, the Wedderburn-Artin algebra `iso`, `projRingHom`, `columnRep`, `columnFDRep`,
`columnFDRep_simple`, `columnFDRep_injective`, `columnFDRep_surjective`, `d_cast_ne_zero`)
are genuinely constructed on top of Mathlib's `MonoidAlgebra.wedderburnArtin`, never
`sorry`/`True`. The theorems therefore are **not vacuous by construction**.

---

## 1. Statement fidelity, per declaration

### Book statement

> **Theorem 4.2.1.** *If the characteristic of `k` does not divide `|G|`, characters of
> irreducible representations of `G` form a basis in the space `F_c(G, k)`.*

The book's proof: by Maschke `k[G]` is semisimple, so by **Theorem 3.6.2** the characters are
linearly independent and form a basis of `(A/[A,A])*` (`A = k[G]`); then it identifies
`(A/[A,A])* ≅ F_c(G,k)` as vector spaces. So "form a basis" = **spanning** + **linear
independence** over the space of class functions.

Section 4.2's introduction (`Introduction_4.2.md`) fixes the definitions used here:
`χ_V(g) = Tr|_V(ρ(g))`; `χ_V` is a **class function**, defined there via the *conjugation*
form `χ_V(hgh⁻¹) = χ_V(g)`; and `F_c(G,k) ⊂ F(G,k)` is the subspace of class functions.

### 1a. `Etingof.Theorem4_2_1` — spanning — **FAITHFUL**

```
(f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span k (FDRep.character '' { V : FDRep k G | Simple V })
```

- **Class-function hypothesis.** `∀ g h, f (h*g*h⁻¹) = f g` is *verbatim* the class-function
  definition given in `Introduction_4.2.md` (`χ_V(hgh⁻¹) = χ_V(g)`). It is also equivalent to
  the `f(gh) = f(hg)` form written in the Theorem-4.2.1 blob: given conjugation invariance,
  `f(hg) = f(h(gh)h⁻¹) = f(gh)`; conversely from `f(ab)=f(ba)` take `a=h, b=gh⁻¹` to get
  `f(h·gh⁻¹) = f(gh⁻¹·h) = f(g)`, i.e. `f(hgh⁻¹)=f(g)`. So the hypothesis is exactly
  `f ∈ F_c(G,k)`. **Faithful.**
- **Conclusion = spanning.** `f ∈ span_k (character '' {V | Simple V})` says every class
  function is a `k`-linear combination of irreducible characters — the spanning half of
  "basis". **Faithful.**
- **`character` semantics.** `FDRep.character V g = LinearMap.trace k V (V.ρ g)` (Mathlib) is
  the book's `χ_V(g) = Tr(ρ(g))`. **Faithful.**

### 1b. `Etingof.Theorem4_2_1_linearIndependent` — independence — **FAITHFUL**

```
LinearIndependent k
  (Subtype.val : ↥(FDRep.character '' { V : FDRep k G | Simple V }) → (G → k))
```

The `k`-linear independence of the (distinct) irreducible characters, viewed inside
`F(G,k) = G → k`. This is the independence half of "basis". **Faithful.**

### 1c. Together = "form a basis of `F_c(G,k)`"

Spanning (1a) shows `F_c ⊆ span(irr. characters)`; independence (1b) shows those characters
are `k`-linearly independent; and each irreducible character is itself a class function
(`FDRep.char_conj`), so the spanning set lives inside `F_c`. Hence the set of irreducible
characters is a **basis of `F_c(G,k)`** — exactly the book's claim. The "characters are
class functions" direction is standard (`char_conj`) and is not broken out as a separate
declaration; this is a presentational choice, not a gap.

### 1d. `Etingof.classFunction_eq_zero_of_orthogonal_simples` — completeness core — **FAITHFUL**

```
(f : G → k) (hf_class : ∀ g h, f (h*g*h⁻¹) = f g)
(hf_orth : ∀ (V : FDRep k G) [Simple V], ∑ g : G, f g * V.character g⁻¹ = 0) :
    f = 0
```

This is genuine **character completeness**: a class function orthogonal (w.r.t. the book's
pairing `⟨f,χ⟩ = 1/|G| ∑ f(x)χ(x⁻¹)`, up to the harmless `|G|` scale) to *every* irreducible
character is zero. It is the substantive input to spanning (§2). **Faithful** as an internal
completeness statement.

---

## 2. Does the proof genuinely establish the theorem? (no short-circuit)

Confirmed non-trivial and non-circular:

1. **Completeness (`classFunction_eq_zero_of_orthogonal_simples`)** implements a real
   Wedderburn argument, not a triviality:
   - `toGroupAlgebra f = ∑_g f(g)·g⁻¹ ∈ k[G]` is **injective** in `f`
     (`toGroupAlgebra_injective`), so proving `f = 0` reduces to `α := toGroupAlgebra f = 0`.
   - When `f` is a class function, `α` is **central** in `k[G]`
     (`toGroupAlgebra_central`, via `MulAut.conj` reindexing) — a genuine use of the
     hypothesis.
   - Under the Wedderburn iso `k[G] ≅ ∏_i Mat_{d_i}(k)` (`IrrepDecomp.mk'`), each block
     `projRingHom i α` commutes with everything, so by `matrix_central_eq_scalar` it is a
     **scalar matrix** `c·1`.
   - Its trace equals `∑_g f(g)·χ_i(g⁻¹)` (`trace_toGroupAlgebra_action`), which the
     orthogonality hypothesis forces to `0`; since `(d_i : k) ≠ 0` (`d_cast_ne_zero`, from
     `d_i | |G|` and `|G|` invertible), the scalar `c = 0`, so every block vanishes and
     `α = 0`.
   This is the standard "class functions ↔ center of `k[G]`, trace-zero scalar ⇒ zero"
   completeness argument — substantive, not a short-circuit.

2. **Spanning (`Theorem4_2_1`)** builds the explicit Fourier projection
   `f' = ∑_i c_i·χ_i`, `c_i = 1/|G| ∑_g f(g)·χ_i(g⁻¹)`, over the finite family
   `columnFDRep`, then applies completeness to `f - f'`. Orthogonality of `f - f'` to an
   *arbitrary* simple `V` is reduced to a column rep via
   `columnFDRep_surjective` (**every simple is isomorphic to some `columnFDRep j`**) and
   `FDRep.char_iso`, and evaluated with the orthonormality relation
   `FDRep.char_orthonormal` (`⟨χ_i,χ_j⟩ = δ_{ij}`, this project's Theorem 4.5.1(ii)). The
   `columnFDRep_surjective` step is essential: it is what makes the finite Fourier expansion
   cover **all** irreducible characters, so the argument is genuinely complete, not a claim
   over a proper subfamily.

3. **Independence (`Theorem4_2_1_linearIndependent`)** applies the orthogonality functional
   `f ↦ ∑_x f(x)·χ_{V i₀}(x⁻¹)` to a vanishing combination; only the diagonal term survives
   (again `FDRep.char_orthonormal`, `if i=j then |G| else 0`), giving
   `g_{i₀}·|G| = 0`, hence `g_{i₀} = 0` since `|G|` is invertible. This rests on **genuine
   character orthonormality**, not a triviality.

**De-duplication (basis vs multiset).** The index set is the *image*
`FDRep.character '' {V | Simple V}` — a `Set (G → k)`. Because isomorphic simples have equal
characters (`char_iso`), the image automatically collapses isomorphic copies: it is the set
of **distinct** irreducible characters. `LinearIndependent` is taken over the subtype of this
image, so distinctness is handled correctly and the object is precisely a candidate basis
(not an over-counted multiset). This is the mathematically correct rendering.

**Proof route vs book (adjudication).** The book routes through Theorem 3.6.2 and the
`(A/[A,A])* ≅ F_c(G,k)` identification. The Lean file instead proves completeness directly
via the group-algebra center / Wedderburn blocks and uses `FDRep.char_orthonormal`
(Theorem 4.5.1(ii)) for both halves. Two things make this legitimate rather than a
divergence:
- **Same theorem.** The end statements (spanning + independence over `F_c`) are exactly the
  book's basis claim; only the internal argument differs.
- **No circularity.** `FDRep.char_orthonormal` is a Mathlib lemma proved independently (via
  the averaging/Reynolds operator and Schur's lemma — see this project's `Theorem4_5_1.lean`,
  `exact char_orthonormal V W`), **not** derived from Theorem 4.2.1. Although 4.5.1 appears
  *after* 4.2.1 in the book's page order, the Lean/Mathlib development does not make 4.5.1
  depend on 4.2.1, so there is no logical loop.
Verdict: **FAITHFUL** (a valid alternative proof), not a defect.

---

## 3. The `[IsAlgClosed k]` hypothesis — **FAITHFUL** (narrowing that matches the book's real assumption; also mathematically necessary)

The book's Theorem 4.2.1 as printed says only "if `char k ∤ |G|`", without restating
algebraic closure at that line. The Lean statements add `[IsAlgClosed k]`. This is **not** a
spurious strengthening:

- **The section's algebra-theoretic backbone assumes algebraic closure.** The book proves
  4.2.1 through Theorem 3.6.2, and Chapter 3's development is stated "over an algebraically
  closed field `k`" (`blobs/Chapter3/Introduction.md`: *"Let `A` be an algebra over an
  algebraically closed field `k`."*). The `A/rad A ≅ ⊕ Mat_{d_i}(k)` split-semisimple
  structure that 3.6.2 and the character-basis count rely on requires `k` to be a splitting
  field. So `[IsAlgClosed k]` is the book's **ambient** assumption inherited into 4.2.1, not
  an extra restriction the formalizer invented.
- **It is necessary for the statement to be true.** Over a non-algebraically-closed field
  the irreducible characters need **not** span the class functions. Concretely, `G = ℤ/3`,
  `k = ℚ` (`char ℚ = 0 ∤ 3`): `F_c(G,ℚ)` has dimension 3 (three conjugacy classes), but there
  are only **two** irreducible `ℚ`-representations (trivial, and a 2-dimensional one since
  `x²+x+1` is irreducible over `ℚ`), giving only two characters `(1,1,1)` and `(2,-1,-1)` —
  which cannot span a 3-dimensional space. The literal "`char k ∤ |G|`"-only statement is
  therefore **false** without a splitting/algebraically-closed hypothesis. The Lean statement
  is the *correct* one.

So `[IsAlgClosed k]` is a faithful specialization to the book's true intended setting, and
arguably a *correction* of an under-stated hypothesis rather than a narrowing of a valid
claim. **FAITHFUL.**

`[Invertible (Fintype.card G : k)]` renders "`char k ∤ |G|`" correctly: over a field,
`|G|` invertible ⟺ `|G| ≠ 0` in `k` ⟺ `char k ∤ |G|`.

---

## 4. Non-vacuity witness

Take `k = ℂ`, `G` any nontrivial finite group (e.g. `ℤ/2`):
- `[Field ℂ]`, `[IsAlgClosed ℂ]` are Mathlib instances.
- `[Group G]`, `[Fintype G]` hold for `ℤ/2`.
- `[Invertible (Fintype.card G : ℂ)]`: `Fintype.card (ℤ/2) = 2 ≠ 0` in `ℂ` (char 0), so the
  cardinality is invertible — the hypotheses are jointly satisfiable, so the theorems are
  **not vacuously true**.
- The index set `{V : FDRep ℂ G | Simple V}` is **non-empty**: the trivial 1-dimensional
  representation is simple, so `FDRep.character '' {V | Simple V}` contains at least the
  constant character `g ↦ 1`. Thus "the irreducible characters form a basis" is a claim about
  a non-empty family. For `ℤ/2` the class-function space is 2-dimensional and there are
  exactly two irreducible characters, so the basis claim has real content in the witness.

The `∃`-free statements (spanning is a membership claim, independence a `LinearIndependent`
claim) are witnessed by genuine constructions (`IrrepDecomp.mk'`, `columnFDRep`), never
`sorry` or `True` — consistent with the clean `#print axioms`.

---

## 5. Verdict summary

| Declaration | Verdict |
|---|---|
| `Etingof.classFunction_eq_zero_of_orthogonal_simples` | **FAITHFUL** (genuine completeness core, axiom-clean) |
| `Etingof.Theorem4_2_1` (spanning) | **FAITHFUL** |
| `Etingof.Theorem4_2_1_linearIndependent` (independence) | **FAITHFUL** |

**No defect found; no follow-up issue filed.** The spanning + independence pair faithfully
renders Etingof Theorem 4.2.1 ("irreducible characters form a basis of `F_c(G,k)`"). The
class-function hypothesis is the book's own definition, the character index set is the
correctly de-duplicated set of distinct irreducible characters, and `[IsAlgClosed k]` matches
the book's ambient split-semisimple assumption (and is in fact necessary for the statement to
hold). The proof takes a different but non-circular route from the book (direct
Wedderburn/orthogonality rather than 3.6.2 + `(A/[A,A])*`), which is a valid alternative
proof of the same theorem. All three declarations build and are axiom-clean.
