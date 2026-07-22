# Stage 3.7 fidelity & non-vacuity audit — Problem 4.12.6 (affine group `x ↦ ax+b` over `𝔽_q`)

- **Issue:** #7293 (report-only)
- **Lean file:** `EtingofRepresentationTheory/Chapter4/Problem4_12_6.lean` (685 lines, `grep -c sorry` = 0)
- **Book:** `blobs/Chapter4/Problem4.12.6.md`
- **Audited against:** `origin/main` @ `c8e8520a`
- **Build:** `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_6` exits 0 (only `linter.style` longLine/`show` warnings, no errors).
- **Verdict:** `verified` / **`covered_partial`**

## Book statement

> **Problem 4.12.6.** Let `𝔽_q` be a finite field with `q` elements, and let `G` be the group
> of nonconstant inhomogeneous linear transformations, `x ↦ ax + b`, over `𝔽_q`
> (i.e. `a ∈ 𝔽_q^×`, `b ∈ 𝔽_q`). Find all irreducible complex representations of `G`, **and
> compute their characters. Compute the tensor products of irreducible representations.**
>
> Hint: Let `V` be the representation of `G` on the space of functions on `𝔽_q` with sum of
> all values equal to zero. Show that `V` is an irreducible representation of `G`.

Three deliverables: (1) classify all irreducibles, (2) compute their characters, (3) compute
tensor products of irreducibles.

## Statement-fidelity

### Group encoding — faithful

`Affine K` is the pair `⟨a, b⟩` with `a : Kˣ`, `b : K`, so `a ≠ 0` (the "nonconstant"
constraint) and `b` arbitrary. The action `act g x = g.a * x + g.b` (line 87) is exactly
`x ↦ ax + b`. Multiplication `⟨a,b⟩ * ⟨a',b'⟩ = ⟨a·a', a·b' + b⟩` (line 60) is the composition
order of `x ↦ ax+b`: `(g ∘ h)(x) = a(a'x + b') + b = (aa')x + (ab'+b)`, verified by
`act_mul : act (g*h) x = act g (act h x)` (line 91). The `Group (Affine K)` instance is fully
proved (associativity, units, inverses; lines 74–84). `card_eq` (line 124):
`|Affine K| = q(q-1)`. Faithful in every respect.

### (1) Classification — faithful and complete (within the proof)

- `one_dim_reps_card` (line 140): `Nat.card (Affine K →* ℂˣ) = q - 1` for `3 ≤ q`. One-dimensional
  complex reps are, up to isomorphism, the monoid homs `G → GL₁(ℂ) = ℂˣ` (`GL₁` abelian, so no
  conjugation collapse), so this correctly counts the one-dimensional irreducibles. The proof
  factors characters through `G^{ab} ≅ Kˣ` (every translation `⟨1,c⟩` is a commutator
  `[⟨a,0⟩,⟨1,c'⟩] = ⟨1,(a-1)c'⟩`) and applies Pontryagin duality
  `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` giving `|Kˣ →* ℂˣ| = |Kˣ| = q-1`. Faithful.
- `zeroSum K` (line 204) `= {f : K → ℂ | ∑ x, f x = 0}` is exactly the book's "functions on `𝔽_q`
  with sum of all values zero." `zeroSum_finrank` (line 229): `dim = q-1` (kernel of the
  summation functional, correct codimension 1). `zeroSum_invariant` (line 216): `G`-invariant
  under `(ρ g f)(x) = f(g⁻¹·x)`.
- `zeroSum_irreducible` (line 303): every `G`-invariant subspace `U ≤ zeroSum K` is `⊥` or all of
  `zeroSum K` — genuine irreducibility of the book's `V`. `Vrep_isSimpleModule` (line 479)
  repackages this as `IsSimpleModule (MonoidAlgebra ℂ G) V.asModule`, the correct group-algebra
  notion of simplicity.
- `irreducible_dim` (line 560): every irreducible complex rep of `G` has `dim ∈ {1, q-1}`. The
  proof is a genuine complete classification: it exhibits the explicit family `E` (the `q-1`
  characters `charRep χ`, each dim 1 and `Simple`; and `V`, dim `q-1` and `Simple`), proves the
  members pairwise non-isomorphic (`hEinj`: characters by `FDRep.char_iso`, `V` by dimension since
  `q-1 > 1`), computes `∑ dim² = (q-1)·1 + (q-1)² = q(q-1) = |G|` (`harith`, `hEsum`), injects the
  family into the Wedderburn enumeration `exists_simples_sum_finrank_sq_eq_card`, and forces
  surjectivity by pigeonhole (`surj_of_injective_of_sum_eq`, every `dim² > 0`) — so every simple
  is isomorphic to one of the `q` explicit reps. The `q = 2` edge (`G` abelian) is dispatched via
  `Example4_3_FiniteAbelianGroups`. Thus "find all irreducibles" is fully and faithfully covered:
  the exposed statement is the dimension dichotomy, and the exhaustiveness/irredundancy of the
  explicit `{q-1 characters} ∪ {V}` list is established inside the proof.

### (2) Characters — PARTIAL

Only the **one-dimensional** characters are computed: `charRep_character` (line 428) gives
`(FDRep.of (charRep χ)).character g = χ g`, i.e. the character of a one-dimensional rep is its
defining homomorphism. The character of the `(q-1)`-dimensional irreducible `V` is **not**
formalized (expected: fixed-point count of `g` on `𝔽_q` minus one — `q-1` at `1`, `-1` on
fixed-point-free translations, `0` when `a ≠ 1`). Gap.

### (3) Tensor products — ABSENT

No tensor-product decomposition (`χ ⊗ χ'`, `χ ⊗ V`, `V ⊗ V`) appears anywhere in the file. Gap.

## Non-vacuity

- The irreducibility/classification theorems are phrased for "any `ρ` with
  `(ρ g f)(x) = f(g⁻¹·x)`" and "any simple `σ`". Such objects genuinely exist and are
  constructed here, so the universally-quantified statements are not vacuous: `permRep` (line 458)
  is a concrete representation, `permRep_apply` (line 468) discharges the `hρ` hypothesis by `rfl`,
  `Vsub` (line 472) builds `V` as an actual subrepresentation, `charRep` (line 419) builds the
  one-dimensional reps, and `exists_simpleFDRep` (line 520) transports any simple module to a
  genuine `FDRep` object (via `transportModule`/`repOfModule`).
- `IsSimpleModule (MonoidAlgebra ℂ (Affine K)) …` is the genuine group-algebra simplicity, not a
  weakened placeholder; `zeroSum_finrank` fixes the dimension at the correct `q-1`.
- The `3 ≤ q` hypothesis on `one_dim_reps_card` is a real, non-degenerate constraint: for `q = 2`,
  `Kˣ` is trivial, `G ≅ ℤ/2` is abelian of order 2 with `2 ≠ q-1 = 1` characters. Documented at the
  declaration (lines 134–139) and exercised in the `q=2` branch of `irreducible_dim`.
- No hypothesis is contradictory or self-defeating; `V` is nontrivial exactly because `q ≥ 2`
  (`Vrep_isSimpleModule` takes `2 ≤ q`).

## `#print axioms`

All deliverable and supporting declarations depend only on `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`:

- `one_dim_reps_card`, `zeroSum_irreducible`, `irreducible_dim` (the three required)
- `zeroSum_finrank`, `Vrep_isSimpleModule`, `exists_simpleFDRep`, `charRep_simple`,
  `Affine.card_eq` (supporting)

## Coverage verdict

`covered_partial`. The book's **classification** ("find all irreducible complex representations")
is fully and faithfully formalized and non-vacuous. The book's other two explicit requests are
partial/absent:

- character of the `(q-1)`-dimensional `V`: **missing** (only one-dimensional characters via
  `charRep_character`);
- tensor products of irreducibles: **absent**.

Follow-up feature issue **#7294** filed for the character-of-`V` and tensor-product deliverables.
No `.lean` edits made (report-only). The file's `## Formalization` docstring (lines 24–39)
already scopes its claims to the classification and does not over-claim characters or tensor
products.
