---
name: lean-formalization
description: Use when working on Phase 3 formalization — translating mathematical text into Lean 4 statements and proofs, or filling sorry placeholders.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Lean Formalization Skill

Patterns for formalizing mathematics textbooks into Lean 4 with Mathlib. Derived from Phase 2 analysis of 583 items across 10 chapters of Etingof's Representation Theory.

## Writing Style: reflect the mathematics, not the process

Every comment and docstring you write into a `.lean` file must read as if it belonged to
a mathematics research paper. The repository records the mathematics of the book, never
the story of how the formalization was carried out.

**No war stories.** Do not write PR, issue, or directive numbers (`#4947`, `issue #2483`,
`directive #4777`), nor any narrative of the formalization process: no `redirect`,
`relocated`, `is now in`, `hosts`, `This file is part of ...`, `Why this lives here`, no
refactor codenames, and no progress or status narration (`sorry-free`, `route B`,
`retired`, `Spec resolution`, `the one remaining sorry`, `## Status`). That history lives
in git and GitHub, not in the source. If a sentence carried a real structural fact (an
import ordering, a re-export), state it plainly without the process narrative. A
re-export note reads `X is re-exported from Y via the import above.`, not `X is now in Y
(#5075), re-exported ...`.

**Speak like a mathematician.** Write plain, precise mathematical prose. Avoid the
AI-slop register: `genuine`/`genuinely`, `crux`, `payoff`, `seam`, `glue`, `assembly`
(as a noun for a proof or theorem — say "the proof"/"the theorem"/"the construction"),
`notch stronger`, `iso-strength`, `ghost` (name the object, e.g. "a summand with zero
multiplicity space"), `would-be`, `routes through`, `threaded in`, `manufactured from`,
`feeding`, `driven by`. Do not force awkward verb-object pairs ("closes the input", "the
field turns X into Y"); use plain mathematical verbs: proves, establishes, gives, yields,
follows from, reduces to. Do not use bold or italics for mid-sentence emphasis (a bold
run-in title at the start of a docstring is fine as structure).

**Banned marks and words** (Kim's standing bans, in all technical writing): em-dashes
`—` (use a comma, colon, semicolon, or parentheses), and the words `bridge`, `gate`,
`smoke`.

For calibration, `EtingofRepresentationTheory/Chapter6/Problem6_1_5_OrbitInjective.lean`
is written to this standard.

## Session Setup

Before the first `lake build` or `lake env lean` in any session:
```bash
lake exe cache get
```
This downloads pre-built Mathlib oleans. Skipping it triggers a full Mathlib rebuild (1800+ jobs).

**To read a Mathlib lemma's exact signature, don't assume `.lake/packages/mathlib` is under
your own worktree** — a per-agent worktree often has none, and the shared checkouts under
*sibling* worktrees get garbage-collected mid-session (a path that grepped fine minutes ago
vanishes). Re-resolve each time with
`find <project-root> -path '*/packages/mathlib/Mathlib/<Dir>/<File>.lean' | head -1`, or just
verify signatures against the compiler (`example : <sig> := by exact?` / a scratch `#check`)
rather than trusting a cached source path.

**When you do grep Mathlib source, use `rg` or `command grep` — not bare `grep`.** The
shell's `grep` is wrapped (ugrep with `--ignore-files`) and honors `.gitignore`; since
`.lake/` is gitignored, `grep pattern .lake/packages/mathlib/...` silently returns nothing
(no error, empty output) and reads as "the lemma doesn't exist." `rg -n pattern <path>` and
`command grep -n pattern <path>` both bypass the wrapper and search the file directly.

**In this Mathlib version `Basis` lives in the `Module` namespace.** The type is
`Module.Basis ι R M` and explicit lemma references need the prefix: `Module.Basis.ext`,
`Module.Basis.constr_basis`, `Module.finBasis` (returns a `Module.Basis`). A bare identifier
`Basis` / `Basis.ext` fails with "Unknown identifier" (easy to miss — `grep 'namespace Basis'`
shows it, but only a wider look reveals it nested under `namespace Module`). Dot notation on a
basis term (`b.constr`, `b.repr`, `b.sum_repr`, `b.ne_zero`) resolves fine unprefixed; only
explicit `Module.Basis.*` references and type annotations `Module.Basis …` need the `Module.`.

**Never `cd` into `.lake/packages/mathlib` (or any subdir) — read absolute paths from the
worktree root instead.** The shell's cwd persists across Bash calls, and
`.lake/packages/mathlib` is itself a lake project: once cwd is inside it,
`lake build EtingofRepresentationTheory.<Module>` fails with a confusing "unknown target", and
a bare `lake build` **silently builds Mathlib and reports success** — a green build that never
touched your project. If builds report "unknown target" or an unexpected job count, run `pwd`
and `cd` back to the worktree root before trusting any result.

**Typecheck with `lake build EtingofRepresentationTheory.<Module>`, NOT `lake env lean
<file>`.** `lake env lean` does **not** apply the lakefile's `[leanOptions]` — in
particular `maxSynthPendingDepth = 3` (lakefile.toml; the Lean default is 2). Deep
instance chains in this project (e.g. the `Subalgebra → Module.End` centralizer-module
instances: `Module ↥(centralizer A) (V →ₗ[A] E)` from `centralizerModuleHom`) need depth
3, so under `lake env lean` they throw **spurious** `synthInstanceFailed` errors that do
not occur under `lake build`. If a file fails `lake env lean` with instance-synthesis
errors on centralizer/Subalgebra hom-spaces but you suspect the proof is fine, re-check
with `lake build <Module>` before debugging — the on-`main` file fails `lake env lean`
too. (Some places below still say `lake env lean`; prefer `lake build` when the file uses
these instances.)

**Two Mathlib lemmas can produce the *same* `1`/`0`/`Pi.single i 1` through *different*
typeclass paths — `rw` then fails syntactically, `exact` succeeds by defeq.** Classic case
(cost real iterations in #6597, `Chapter9/Problem9_5_3_PrimitiveIdempotents.lean`):
`CompleteOrthogonalIdempotents.single K` builds `Pi.single i 1` with the `Semiring`/quotient
`One`, while a `[Field (K i)]`-requiring lemma builds it with `Field`'s `One`; the two `1`s are
defeq but NOT syntactically equal, so `rw [← lemmaEq]` reports "did not find pattern". **Fixes:**
(a) provide the locally-needed instance with **`letI` (transparent), not `haveI` (opaque)** — a
`haveI hK : ∀ i, Field (K i) := …` cannot be unfolded by defeq, so `exact`/`congrArg` across the
two `One` paths fail; `letI` lets them unify. (b) Compute along ONE path (via your equation
hypotheses) and cross to the other with **defeq-tolerant** `exact`/`congrArg f h`/`Subtype.ext h`
instead of `rw`. For subalgebra/subtype coercions specifically, the `Subalgebra.coe_mul`/`coe_add`
/`coe_zero` lemmas are `rfl`, so `rw` on them is brittle — prefer `Subtype.ext (R-level eq)` to
prove a `↥S`-level equation and `congrArg S.val (↥S-level eq)` to prove an `R`-level one.

**`set`/`let`-abbreviating a *type* hides its instances from synthesis.** `set O :=
MulAction.orbit ↥G b` then writing `↥O` makes `MulAction ↥G ↥O` (and `Finite`/`Fintype ↥O`)
**unfindable** — typeclass search will not unfold a local `set`/`let` definition, so you get
`failed to synthesize HSMul ↥G ↥O ?` or a `synthInstance` timeout. Write the type out
(`↥(MulAction.orbit ↥G b)`) everywhere an instance must resolve; accept the verbosity (wrap long
lines). Relatedly, a lambda whose **output** type is still a metavariable sends instance search
into a loop — e.g. `Quotient.map' (fun w => g • w) h` before `Quotient.map'`'s codomain is pinned
gives the same `HSMul … ?` timeout. Ascribe it: `fun w : T => (g • w : T)`. Both bit during the
octahedral four-diagonal quotient action (#6972).

**`letI : AddCommGroup P := addCommGroupOfRing …` on a parent type `P` SHADOWS and breaks
`Module R P` synthesis** (v4.31/v4.32 regression; cost ~10 iterations in #7509,
`Chapter6/CoxeterInfrastructure.lean`). The old trick of adding a ring-induced `AddCommGroup`
to a `DirectSum`/`QuiverRepresentation.obj` so submodule-of-`P` lemmas fire now makes
`Module R P` (and thus `Module R ↥(submodule of P)`) **unfindable** — the local `AddCommGroup`
shadows the canonical `AddCommMonoid` and the discrimination tree no longer matches
`DirectSum.instModule`. **Fix:** capture the module instance *first*
(`letI mP : Module R P := inferInstance`), build the group from it
(`@Etingof.addCommGroupOfRing R _ P inferInstance mP`), and pass both explicitly to the
consuming lemma (`@Module.Free.of_divisionRing R P _ acg mP`,
`@isNoetherian_of_isNoetherianRing_of_finite R P _ acg mP …`) so nothing re-synthesizes under
the shadow. Note `Module.Free.of_divisionRing` is a priority-100 *instance* (every vector space
is free) — once a clean `AddCommGroup` is in scope it fires on its own. Relatedly: **`LinearMap.ker f`
is a submodule of `f`'s DOMAIN, not its codomain** — check the map's direction before deciding
which module the kernel lives in (I lost several iterations assuming `(ρ.sinkMap i).ker ⊆ ρ.obj i`
when `sinkMap : ⊕ⱼVⱼ →ₗ Vᵢ` makes it a submodule of the direct sum). For finrank-zero
contradictions on `Module.Free` carriers, `Module.finrank_eq_zero_iff_of_free` avoids needing any
`AddCommGroup` upgrade at all.

**`LinearMap.ofIsCompl hC W₁.subtype 0` (and sibling complement/projection constructors) can
stop elaborating** when the ring/module are only inferrable from a coerced-subtype argument
(regression seen fixing Ch3 `Problem3_8_5.lean`, #7533). The non-`@` application fails to infer
`R`/`E` from `W₁`, so `hC : IsCompl W₁ W₂` reports `Application type mismatch … expected
IsCompl ?m ?m` (the `p q` stay metavariables). **Fix:** switch to `Submodule.projection` (the
along-a-complement self-map) and pin the types with the fully explicit form
`@Submodule.projection R _ E _ _ W₁ W₂ hC`; its `_apply_of_mem_left/_right`/`_apply_mem` lemmas
replace the `ofIsCompl_apply_left/right` route. Feed those lemmas (also `@`-explicit) through
`simpa [hπ] using (@…)`, **not** `exact` — a bare `exact @Submodule.projection… ` forces whnf of
the projection term plus instance synthesis and blows 200k heartbeats, whereas `simpa`'s
simplified goal guides synthesis and closes cheaply.

**A bespoke `Module`/`IsScalarTower` instance on a `LinearMap`/`Hom` space collides with
Mathlib's generic ones and breaks synthesis.** Mathlib already gives `Module S (M →ₗ[R] N)`
(`LinearMap.module`, needs `SMulCommClass R S N`) and `IsScalarTower S T (M →ₗ[R] N)` for free.
A hand-written `instance homBModule : Module B (V₀ →ₗ[A] M)` then competes with the generic
`Module B`; synthesis picks the generic one but a custom `IsScalarTower k B (V₀ →ₗ[A] M)` built
on the bespoke `Module B` no longer matches, so `Algebra.lsmul`/`Module.End`/`Submodule.module'`
goals fail with `failed to synthesize IsScalarTower …`/`Algebra k (Module.End k …)` (#7520,
`Chapter3/Theorem3_10_2.lean`, originally sorry-free in #705). **Fix: delete the bespoke
instances and rely on the library generics** (replace any explicit `homBSMul V₀ b f` with `b • f`,
which is defeq). **Diagnostic:** if the *same* synthesis error survives changing `set`→`let`→a
fully written-out concrete type, the type-abbreviation is NOT the cause — look for a duplicate/
bespoke instance on that type shape instead.

**A regressed file with a burst of `failed to synthesize Module k …` / `HasQuotient …`
errors is usually a non-`@[reducible]` class-type helper `def`.** Under the v4.30 toolchain,
a `def`/`noncomputable def` whose *return type is a class* (`AddCommGroup`, `AddCommMonoid`,
`Module`, …) that is used as a local instance now emits `Definition … of class type must be
marked @[reducible] or @[implicit_reducible]` — and, critically, instance search can no
longer unfold it, so a `letI : AddCommGroup T := myHelper …` blocks synthesis of
`Module k T` / `HasQuotient T (Submodule k T)` built on top of it (the natural instance is
w.r.t. a *defeq-but-not-syntactic* `AddCommMonoid`). **Fix: mark the helper `@[reducible]`**
(`@[reducible] noncomputable def` is fine), which lets `.toAddCommMonoid` reduce back to the
ambient monoid. Diagnosed on `Etingof.addCommGroupOfRing` in `Chapter6/Definition6_6_4.lean`
(#7524), which had cascaded into `Module`/`HasQuotient` failures across the whole cokernel
construction of the reflection functor `F⁻`. Same knob as the `@[implicit_reducible]` note on
`Module.IsTorsionBySet.module` at #6090. Whenever "restore fresh-buildable" work turns up
mass `Module`/`HasQuotient` synthesis failures, grep the warnings for "class type must be
marked" first — it points straight at the culprit.

**For a `def Foo := Bar` wrapper (e.g. `def PathAlgebra := _ →₀ k`) with re-exposed
`inferInstanceAs` instances, two more traps beyond the `rw`/`exact` split — both hit while
restoring `Definition2_8_4.lean` (#7499), cost ~15 iterations:**
- **A type ascription `(e : Foo)` is *erased* during elaboration**, so a `Finset.sum`/`∑`
  over `(summand : Foo)` still takes the summand's *native* `Bar` `AddCommMonoid`, not `Foo`'s
  (confirmed with `set_option pp.all`). `Finset.sum_mul`/`mul_sum` then "make no progress"
  because they expect the ambient semiring's monoid. **Fix: build the summand from a function
  whose *declared return type* is `Foo`** (here `ofPath x : PathAlgebra := single x 1`), so the
  sum genuinely lives in `Foo`'s structure. Keep the public `Finsupp.single`-form lemma for
  downstream clients and add a definitionally-equal `foo_eq_sum` (`:= rfl`) in the `Foo` form
  for the internal proof.
- **After `Finset.sum_mul` fires, the result sum is in the *semiring-derived* `AddCommMonoid`,
  but `Finset.sum_ite_eq'`/`simp` re-synthesize the *group-derived* one** → the two are defeq
  but `rw`/`simp` won't match ("did not find pattern" on syntactically-identical goals).
  **Fix: evaluate the sum with `Finset.sum_eq_single_of_mem`**, which consumes the goal's sum
  as-is (no instance re-synthesis); discharge its `∀ b ≠ a, f b = 0` side goal with a term-mode
  `(hterm b).trans (if_neg …)` (a bare `rw` leaves an unclosed `0 = 0` across the same diamond).
- **Ring-law instance fields (`left_distrib`, `zero_mul`, `smul_mul`, …) whose old `change …;
  rw [map_add]` broke: rewrite them term-mode** as `map_add (mulLinear a) b c` /
  `(LinearMap.congr_fun (map_add …) c).trans (LinearMap.add_apply …)`. And for
  `Finsupp.induction_linear` leaking `Bar`-typed pieces into `Foo` multiplication, wrap a
  `Foo`-native `induction_linear` (`:= Finsupp.induction_linear …`) whose step binders are `Foo`.
  Small `Finsupp`-typed helpers (`c • single x 1 = single x c`, `c • 0 = 0`) proved by `rw` then
  applied to `Foo` goals by `exact` cover the `SMulZeroClass k Foo`-not-synthesizable gaps.

**`TensorProduct.finsuppScalarRight`/`finsuppScalarLeft` rewrites that stop matching on a
`MonoidAlgebra ℚ G` factor (#7522, `Chapter5/Corollary5_12_4.lean`).** These lemmas
(`finsuppScalarRight_apply_tmul_apply`, …) are stated over `ι →₀ R`, but `MonoidAlgebra R G`
is `G →₀ R` with `MonoidAlgebra.addCommMonoid` *overriding the `AddCommMonoid.nsmul` field*
(the "abuses definitional equality" TODO in Mathlib's `MonoidAlgebra/Defs.lean`). The two
instances are defeq at `default` (so the `def` composing `finsuppScalarRight` with a
base-changed submodule inclusion still elaborates) but not reducibly equal, so `rw`/`simp`
report "did not find pattern" and even leave the goal "not type-correct under `instances`
transparency". **Fix: don't fight the rewrite — build the value term with explicit `Finsupp`
typing** (`have h := finsuppScalarRight_apply_tmul_apply (R := …) … (↑w) g`, passing the
`MonoidAlgebra`-typed coercion where `ι →₀ R` is expected; it unifies by defeq) **then
transport with `refine h.trans ?_`** (`Eq.trans`'s first argument unifies up to defeq, unlike
`rw`). Close the residual scalar goal with `Algebra.smul_def`, `mul_comm`, `rfl`. Only the
one coefficient lemma broke; the surrounding `def`s and other proofs were untouched.

**A `neg_smul`/cast rewrite tail that breaks under a Mathlib bump: close it with `push_cast;
module` instead of chasing the rewrite (#7530, `Chapter2/Problem2_7_4.lean`).** A proof ending
`rw […, ← Nat.cast_smul_eq_nsmul (R := k) (n + 1), neg_smul]; congr 1; push_cast; ring` regressed
with `rw [neg_smul]` reporting `Did not find an occurrence of the pattern -?r • ?x` — even though
the goal visibly had `(-(↑n + 1)) • m` on the RHS. The cause is a smul instance diamond: after the
earlier `zero_sub` one side is `-((↑n + 1) • m)` (neg *outside* the smul) while the stated side is
`(-(↑n + 1)) • m` (neg *inside*), and the two smul paths are defeq but not syntactically matchable,
so `neg_smul` fires on neither. **Fix: drop the `neg_smul`/`congr`/`ring` tail and finish with
`push_cast` (to fold `↑(n + 1)` to `↑n + 1`) then `module`.** The `module` tactic normalizes both
`r • m` and `-` uniformly and ignores the neg-inside/neg-outside distinction, so it closes goals
that a positional `rw [neg_smul]` can't. General rule for "restore fresh-buildable" work: when a
`smul`/cast `rw` step fails with "did not find pattern" on a goal that looks right, reach for
`module` (module-linear goals) before hand-massaging the negation.

**Same failure for `AddCommGrpCat`/`ModuleCat` homology goals in `ConcreteCategory.hom` form**
(cost ~5 iterations in #6952, `Chapter8/HomComplexHomologyK.lean`). After
`AddCommGrpCat.comp_apply`, terms read `ConcreteCategory.hom f (ConcreteCategory.hom g x)`; the
element `x` often has type `CohomologyClass …` while a lemma expects `↑(AddCommGrpCat.of …)`. These
are defeq but `AddCommGrpCat.of`/carrier is not reducible, so `rw [hcancel]` and even
`simp only [Iso.inv_hom_id_apply]` **silently do not fire** (reported "unused"/"pattern not found").
Fixes: (a) don't expand-and-cancel isos elementwise — prove the *forward* naturality square via
`ShortComplex.LeftHomologyMapData.homologyMap_comm` + `ConcreteCategory.congr_hom … y` +
`AddCommGrpCat.comp_apply`, then close with **`exact h`** (full-transparency defeq bridges the
`homology n` vs `(sc n).homology` and carrier-coe gaps that `rw` cannot); (b) derive the `.symm`
form from the forward square by pure `AddEquiv` algebra (`AddEquiv.symm_apply_eq`,
`apply_symm_apply`) rather than unfolding `homologyAddEquiv` (which retypes to `(sc n).homology`
and breaks surrounding applications).

**Cast lifted out of a `Multiset`/`Finset` map inside a hypothesis.** A statement summand like
`(m.map (fun x => 1 - (x : ℚ)⁻¹)).sum` (with `m : Multiset ℕ`) elaborates with the coercion
lifted OFF the function and ONTO `m`: the hypothesis becomes
`(Multiset.map (fun x : ℚ => 1 - x⁻¹) (Nat.cast <$> m)).sum` — a `do`-block / `<$>` over `m`
coerced to `Multiset ℚ`. A cleanly-defined `f : ℕ → ℚ := fun x => 1 - (x:ℚ)⁻¹` then does NOT
match, so `rw [← heq]` reports "did not find pattern". Bridge it once at the top with
`simp only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map, Function.comp_def] at heq`
(this rewrites `x >>= pure ∘ ↑` → `↑ <$> m` → `m.map ↑` → `m.map (g ∘ ↑)`), after which the
hypothesis is `(m.map (fun a => 1 - (↑a)⁻¹)).sum` and folds to your `f`. Do this before building
any per-element case analysis on the sum. **If instead you just need the NUMERIC value of a
concrete literal sum** (e.g. `(({2,3,3} : Multiset ℕ).map (fun x => 1 - (x:ℚ)⁻¹)).sum = 11/6`,
as when deriving `|G|` from the SO(3) pole-counting identity for the `{2,3,3}`/`{2,3,4}`/`{2,3,5}`
families in `Problem4_12_8.lean`), skip the fold: `simp only [Multiset.insert_eq_cons]; norm_num`
proves it outright — `norm_num` evaluates through the `do`-block/`<$>` on its own. Then
`rw [that_sum] at heq; field_simp [hcard_ne_zero] at heq; linarith` closes `(Nat.card G : ℚ) = N`.

**When composing a chain of `LinearEquiv`s between principal ideals, parametrize each generic
equiv by the *boundary submodule* plus a `hp : p = Submodule.span R {w}` proof — don't lean on
defeq between a named ideal (`SpechtModule`, `rowColIdeal`) and its `Submodule.span` unfolding.**
Cost real iterations in #6775 (`Chapter5/Problem5_24_1_b.lean`): a `def signTwistSpanEquiv (w) :
↥(span{w}) ≃ₗ ↥(span{φ w})` applied to `x : ↥(SpechtModule n la)` type-checks (domains are defeq),
but the SMul instance on `↥(SpechtModule)` is *syntactically* different from the one on
`↥(span{w})`, so the equivariance `rw [signTwistSpanEquiv_equiv]` cannot match, and `erw` blows
`whnf` past 1.6M heartbeats unifying the huge `MonoidAlgebra`/`Submodule` SMul instances. **Fix:**
give the equiv signature explicit `(p q : Submodule R M) (hp : p = span{v}) (hq : q = span{w})` and
instantiate `p := SpechtModule n la` (`hp := rfl`), `q := rowColIdeal n la*`, so the composite's
endpoints are the *named* ideals and every equivariance `rw` matches syntactically; membership
obligations inside then open with `rw [hp]`/`rw [hq]` to expose the span.

**`Representation.asModule` is a non-reducible `def` wrapping the vector space `V`, so its
elements do NOT auto-coerce (no `↑m : Fin 3 → k`, no `m.val`, no `m.2`) and instances like
`Nontrivial`/`CharP` won't be found on it.** Cost real iterations in #6852
(`Chapter9/Problem9_5_3_S3Char2.lean`, `eStd_smul_triv`/`eStd_smul_std`). Fixes: (a) to reach the
underlying value/membership, type-ascribe to the concrete carrier — `set v : (subrep).toSubmodule
:= m` (defeq via `set`), then `↑v`/`v.2` work; (b) note that `ρ g m` already has the *transparent*
codomain type (the submodule, not `asModule`), so `(ρ g m : Fin 3 → k)` coerces fine — push the
action through first; (c) for char-2 `m + m = 0` on an `asModule`, do it on the **scalar** side
(`rw [← two_smul k m, CharTwo.two_eq_zero, zero_smul]`) rather than invoking
`CharTwo.add_self_eq_zero` (which needs an `AddMonoidWithOne`/`CharP` instance on the opaque
`asModule`); (d) `Representation.asModuleEquiv` is `LinearEquiv.refl`, so `asModuleEquiv m` is defeq
`m` — a `have key : single g 1 • m = ρ g m := by rw [Representation.single_smul, one_smul]; rfl`
bridges `single_smul` to the plain action.

**A `map_smul'`/`asModule` proof that used to close by `rw`/`simp` but now leaves a
trivially-true goal (`0 = 0`, `X = X`, `f 0 = 0`) is the reducible-transparency
regression, not a math error.** `rw`/`simp` run their terminal reflexivity at
reducible transparency, which no longer unfolds `Representation.asModule` (a
`def := V` whose `AddCommMonoid`/`Module`/`Zero` instances are defeq to, but
syntactically distinct from, `V`'s). Fixes for the `MonoidAlgebra.induction_linear`
`zero`/`add` cases: (a) after `simp only [zero_smul]` close with **`exact rfl`** (or
`exact map_zero f`) at default transparency, not by relying on `simp`/`rw`'s own
close; (b) a bare `rw [map_add]` / `rw [map_zero]` will *not* match `asModule`'s add
instance — split the map with a **pinned** `show f (a•x + b•x) = f (a•x) + f (b•x)
from map_add f _ _` (the `show` elaborates the add in the goal's `asModule` instance,
`from` fills it by defeq), then `rw [ha, hb]; exact rfl`. (c) When an inline
`≃ₗ[k[G]]` structure's `single_smul` rewrite fails because a helper equiv's *concrete*
codomain (`DirectSum β W`) leaks past the `asModule` action, don't fight it — if the
helper intertwines the two representations, **reuse the generic
`asModuleEquivOfIntertwiner`/`asModuleHomOfIntertwiner` lift** (proved once at the
type-variable level where `f x : W` matches `asModule σ` syntactically) instead of
re-deriving. Worked example: #7554 (`Chapter5/RepresentationAsModuleHom.lean`, all
four `map_smul'` proofs).

**`is_simple_module_of_finrank_eq_one (Module.finrank_self k)` on a `Representation.asModule`
no longer synthesizes `IsScalarTower k k[G] ρ.asModule`** — a current Mathlib regression that
bites when the representation's carrier `V` is the base field `k` itself (e.g. `Representation.trivial
ℂ G ℂ`). Passing `Module.finrank_self k` pins the lemma's `V := k` to the self-module `k.instModule`,
selecting the ℂ[G]→ℂ restriction branch of the `Module k ρ.asModule` diamond, which
`Representation.instIsScalarTowerMonoidAlgebraAsModule` (stated over `asModule`'s *transferred/derived*
`Module k`, with `backward.isDefEq.respectTransparency false`) cannot unify against under reduced
transparency (even with the tower instance explicitly in local context). **Fix: route the finrank
through the derived branch.** Either the one-line form
`is_simple_module_of_finrank_eq_one (ρ.asModuleEquiv.finrank_eq.trans (Module.finrank_self k))`, or
the explicit-pin form `refine is_simple_module_of_finrank_eq_one (K := k) (A := k[G]) (V := ρ.asModule)
?_; rw [ρ.asModuleEquiv.finrank_eq, Module.finrank_self]`. Worked examples: #7513
(`Chapter5/Theorem5_26_1.lean`, `trivialFDRep_simple`) and #7515 (`Chapter5/Theorem5_4_6.lean`,
`trivialFDRep_simple`). The same idiom (`(Module.finrank_self ℂ)`) may still be live in
`Theorem5_25_2.lean:1506` (#7516), `Lemma5_4_7.lean:95`, and `Problem6_1_6.lean:760` — apply the
same fix there.

**`MonoidAlgebra.single g 1` elaborates the coefficient `1` as `ℕ` (giving `ℕ[G]`) unless
pinned** — the module/action can't back-propagate the base ring during elaboration, so
`single g 1 • m` fails with `HSMul ℕ[G] M M`. Always write `single g (1 : k)`. Cost a full build
cycle in #6859. Relatedly, a whole-group case split like `∀ g : Perm (Fin 3), P g` is
`decide`-able, but only when stated with `g` universally quantified: `have : ∀ g, g = 1 ∨ … := by
decide; … rcases this g` — `decide` on a hypothesis mentioning a *free* `g` errors with "expected
type must not contain free variables".

**`ext x` over-recurses on a `LinearMap`/`Representation` equation whose domain is
`MonoidAlgebra k G`** — because `MonoidAlgebra k G` reduces to `G →₀ k`, `ext` peels past the
LinearMap into the `Finsupp` and hands you `x : G` (or a `Finsupp` index), not `x : MonoidAlgebra k G`,
so a follow-up `exact map_mul f (of g) x` fails with "argument x has type G". Fix: force one level
with `refine LinearMap.ext fun x => ?_` (x is then the algebra element). Same idiom for the `comm`
obligation of `Action.mkIso`: use `ext : 1` (not bare `ext`) to stop at the linear-map equation
`f.hom ∘ₗ M.ρ g = N.ρ g ∘ₗ f.hom`.

**To get `Module k ↥S` on an abstract `S : ModuleCat (k[G])` object** (needed for `k`-linear maps,
`Basis`, `LinearMap.toSpanSingleton`, char-2 `x+x=0` via `two_smul`), install it locally:
`letI : Module k ↥S := Module.compHom ↥S (algebraMap k (k[G]))`, then hand-prove
`IsScalarTower k (k[G]) ↥S` and `SMulCommClass k (k[G]) ↥S` (both one-liners via `Algebra.smul_def`
/ `Algebra.commutes` — the `k`-smul is defeq `algebraMap _ • ·`). With that, a nonzero `k`-linear
`S₃`-intertwiner between two simple `asModule`s promotes to `k[G]`-linear by `MonoidAlgebra.induction_on`
(base `of g` = generator equivariance, `hsmul` case closes by `smul_assoc` + the map's `map_smul`), then
`LinearMap.bijective_of_ne_zero` (Schur) + `LinearEquiv.toModuleIso` gives the `ModuleCat` iso. Worked
example: `simple_iff_triv_or_std` / `nonempty_iso_of_genEquivariant` (#6859, `Chapter9/Problem9_5_3_S3Char2.lean`).

**`fin_cases i` (and `Fin.cases`) emit the literal as `⟨0, ⋯⟩` (`Fin.mk`), which `rw`/`simp` keyed
on `(0 : Fin 3)` (an `OfNat`) cannot match** — "did not find pattern" even though they're defeq.
Same #6852. Fix: open each branch with `change <goal with (0 : Fin 3)/(1 : Fin 3)/(2 : Fin 3)>` to
restate at the `OfNat` literals (defeq, so `change` accepts), *then* `rw`/`decide`-facts match.
Prefer `change` over `show` here (the linter flags `show` for non-readability goal changes).

**`omega` treats `(⟨c, _⟩ : Fin n).val` as an *opaque* atom (it does NOT reduce `Fin.mk`'s value to
`c`), so a goal `x = ⟨c, _⟩` — or `x.val = (⟨c, _⟩).val` after `apply Fin.ext` — is unprovable by
`omega` even when `x.val = c` is derivable.** Tell-tale: the omega counterexample lists a variable
like `h := ↑↑⟨1, ⋯⟩` (the literal appears as an opaque unknown, unconstrained to `1`). Fix: prove the
plain `ℕ` goal `x.val = c` first (with the literal `c`, e.g. `1`), then `exact Fin.ext h`. Cost two
build cycles in `affine_two_branch_deleted_isD` (#6940, `Chapter6/Problem6_1_3_continued_tildeE.lean`)
where the target was `σ.symm v' = ⟨1, _⟩` over a variable-rank `Dₖ`. Relatedly, when `subst h` with
`h : n' = k` could eliminate either variable, name the one to drop (`subst n'`) so the kept variable
(here `k`, used in the goal type) survives.

**`omega` treats `Nat.card {x // p x}` and `Nat.card {x // q x}` as *distinct atoms* even when `p`
and `q` are definitionally equal (classic case: a `≠` goal vs a `¬ =` hypothesis).** In a counting
proof, `Equiv.sumCompl (fun g => orderOf g = 5)` gives a hypothesis mentioning
`Nat.card {g // ¬ orderOf g = 5}`, but a goal stated with `{g // orderOf g ≠ 5}` will not close by
`omega` — the counterexample lists the goal's card as an unconstrained variable. Fix: bridge with an
`rfl` cast first, `have he : Nat.card {g // orderOf g ≠ 5} = Nat.card {g // ¬ orderOf g = 5} := rfl;
rw [he]`, so both sides share one atom. Cost one build cycle in `simpleGroup_card60_exists_index_five`
(#6982, `Chapter4/Problem4_12_8.lean`).

**Adding a heavy import to a foundational *definition* file can break a *downstream* file by
slowing generic typeclass search past its heartbeat budget.** Hit in #7443: adding
`import Mathlib.Algebra.Category.ModuleCat.Projective` to `Chapter9/Definition9_6_2.lean` (to state
a `ModuleCat` example) pulled its `Projective` instances transitively into `Theorem9_6_4.lean`,
where a pre-existing `inferInstance`-style `Projective P` search on a *generic* object then
timed out at 20000 heartbeats — even though nothing in that file changed. Diagnose by rebuilding
the failing file on a clean baseline (`git stash` your edits, `lake build <Module>`); if it passes,
your import is the cause. **Fix:** keep foundational definition files' imports minimal and put the
heavy-import example/instance in its own separate file that imports both the definition and the
heavy module. Where a proof already holds the structure, grab the parent field directly
(`hp.toProjective`) instead of `inferInstance` to sidestep the slow search entirely.

**Heavy category-theory objects (total complexes / coproducts) make `isDefEq`, `whnf`, and
typeclass search blow up — unfold *one step short* and finish by hand.** Cost real iterations in
#6683 (`Chapter8/ExternalTensorResolution.lean`, `Projective ((mapBifunctor …).total.X n)`). Two
compounding traps: (a) forcing the goal defeq all the way to the coproduct — e.g.
`show Projective (∐ g)` or `exact inferInstanceAs (Projective (∐ g))` against a total-complex
`.X n` — times out `whnf`/`isDefEq` even at 1–2M heartbeats, because normalizing `∐` over the
bifunctor summands explodes. **Fix:** stop at the `mapObj` level with a cheap `rfl` helper
(`(K.total c).X n = K.toGradedObject.mapObj p n := rfl`; note `@[simps -isSimp d]` on `total`
generates only `total_d`, *not* `total_X`), `rw` it, then `show Projective (∐ g)` — now a single
`mapObj` unfold, cheap. (b) Even with the goal literally `∐ g` and `∀ b, Projective (g b)` in
context, the coproduct-`Projective` instance (`Preadditive/Projective/Basic.lean`) is declared
`set_option backward.isDefEq.respectTransparency false`, so its full-transparency defeq does **not
terminate** on heavy summands. **Fix:** build the lifting property by hand —
`refine ⟨fun {E X} f e he => ⟨Sigma.desc fun b => Projective.factorThru (Sigma.ι g b ≫ f) e, ?_⟩⟩;
apply Sigma.hom_ext; intro b; rw [Sigma.ι_desc_assoc]; exact Projective.factorThru_comp _ e`. General
lesson: when a Mathlib instance/lemma quietly uses full transparency, bypass it with an explicit
term rather than fighting heartbeats.

**Applying a hypothesis/lemma whose implicit *type* arguments are still metavariables postpones
its explicit args as synthetic-opaque metavariables — a later premise then either whnf-loops or
fails with a spurious "Application type mismatch: … expected LinearMap.range ?m = …".** Hit in
#7504 (`Chapter8/Theorem8_1_1.lean`, reverse direction of `Theorem_8_1_1_i_iff_iv`): applying
`hex : ∀ {K M N : Type v} … (ι) (π), Injective ι → … → range ι = ker π → _` as
`hex (ker f).subtype f _ hfsurj (Submodule.range_subtype _)` left `K`/`M`/`N` unsolved, so `ι`
became a postponed `?m` and the exactness premise `range ?m = ker π` had to `whnf`-reduce the heavy
`f := p ∘ₗ e.toLinearMap` term to unify — timing out at 200k heartbeats (making the file
non-importable). Passing a concrete `ι` or ascribing its type does **not** help; the postponement is
driven by the unsolved implicit *type* args. **Fix:** pin them by name at the call site —
`hex (K := ↥(ker f)) (M := P →₀ Shrink.{v} R) (N := P) ι f hι hfsurj hexact` — so every explicit arg
elaborates eagerly against a concrete expected type and the premises unify syntactically. Hoist
`ι`/`hι`/`hexact` into `let`/`have` bindings first to keep the call readable.

**When an inline proof over huge *concrete* terms times out heartbeats, lift the heavy structural
argument into a standalone helper `def`/lemma whose hypotheses are the *abstract* objects.** Hit in
#6767 (`Chapter8/ExternalTensorResolution.lean`): the degree-0 `quasiIso` goal assembled a cokernel
of `(tensorObj (res₁Complex P₁) (res₂Complex P₂)).d 1 0` via `Cofork.IsColimit.mk` +
`mapBifunctor.hom_ext` + `Cofork.IsColimit.π_desc`; inline these tactics run their `isDefEq`/`whnf`
on the enormous restricted-external-tensor complexes and blow 200k heartbeats. **Fix:** extract
`isColimitCokernelCofork_tensorObj_augmentation {C₁ C₂ : ChainComplex (ModuleCat k) ℕ} … : IsColimit
(CokernelCofork.ofπ q _)` taking `C₁ C₂ q p₁ p₂` and the cofork/`ιTensorObj`-identity hypotheses as
*variables* — the colimit bookkeeping now elaborates on symbols (fast), and the concrete call site
is a single `exact`. (`IsColimit` is `Type`, not `Prop`, so the helper is a `noncomputable def`, not
a `theorem`.) Two `Cofork` gotchas from that proof: `CokernelCofork.tensor c₁ c₂` is *definitionally*
a `CokernelCofork.ofπ`, so a bare `rw [CokernelCofork.π_ofπ]` will collapse `Cofork.π (tensor …)` —
rewrite it via your own `hππ : Cofork.π (tensor …) = p₁ ⊗ₘ p₂` *before* any `π_ofπ` fires; and
`s.condition` on a `CokernelCofork s` resolves to the general `Cofork.condition` (`f ≫ π = 0 ≫ π`,
leaving a `0 ≫ π`), so use `CokernelCofork.condition s` (`f ≫ π = 0`) instead. For a functor-category
iso `α : F ≅ G`, the simp lemma for `(α.app X).hom` is `Iso.app_hom` (not `NatIso.app_hom`).

**The Chapter 8 `Tor` rearrangement stack carries a *second* `Module k` action on the same
carrier — restriction-through-`Aᵐᵒᵖ` vs `TensorProduct`-diagonal — that is defeq-*false*.** Hit in
#6742 (`Chapter8/RearrangeBifunctorNatIso.lean`). `tensorRightFunctorₖ.obj` equips `tensorOver A N M`
with the `k`-action *restricted through* `algebraMap k Aᵐᵒᵖ` (its file's `instModuleKObj`), whereas
`rearrangeBidegree`/`TensorOverModule` use the `TensorProduct`-diagonal `k`-action on `M`. On simple
tensors both give `c • ⟦(x⊗y)⊗n⟧ = ⟦(c•x)⊗y⊗n⟧`, so they agree **propositionally but not
definitionally** — `ModuleCat.of k (tensorOver …)` built the two ways are *not* `rfl`-equal, so
`(…).toModuleIso` will not typecheck against `(F.obj X).obj Y`. Note the `(A₁⊗A₂)ᵐᵒᵖ`-*module* half
of the diamond **is** dissolvable by defining your local `Module (A₁⊗A₂)ᵐᵒᵖ (X⊗Y)` as
`inferInstanceAs (Module _ (extTensorFunctorObj … X Y))` (reuse the very instance the functor object
carries); only the `k`-action still differs, and only on the `(A₁⊗A₂)` side (the `Aᵢ` factor sides
match because `rearrangeBidegree` takes `Module k (Pᵢ)` from those same restriction instances).
**Fix (what actually worked, #6742 completed):** you do *not* need `Module.ext`/`eqToIso` on the
instances. Build an identity-carrier `LinearEquiv` `((F.obj X).obj Y) ≃ₗ[k] ModuleCat.of k (tensorOver …)`
(`toFun := fun z => z`); the two `ModuleCat` objects each pin their own `Module k`, so `map_smul'`
becomes the honest `c •_restr z = c •_diag z`, dischargeable over `QuotientAddGroup.mk_surjective` +
`TensorProduct.induction_on` + `smul_mk` + `TensorProduct.smul_tmul'`, bottoming out at
`extModule_algebraMap_smul` (`algebraMap k (A₁⊗A₂)ᵐᵒᵖ c • z = c • z`, via `AlgHom.commutes`). Then
`LinearEquiv.trans` with `rearrangeBidegree` and `.toModuleIso`. Assemble the bifunctor `NatIso` as
two **nested** `NatIso.ofComponents`, and make the inner (per-`X`) NatIso a **separate named `def`**
with a `@[simp]` `_hom_app` lemma — otherwise the outer naturality `simp` tries to unfold the inner
NatIso's large baked-in proof and hits `(deterministic) timeout at whnf`.

**`Ext`-side mirror: the `k`-module on a Hom object `(Z ⟶ N)` differs between `linearYoneda` and
`ModuleCat.of` when `N`'s carrier has an *external* `Module k`.** Hit in #6867
(`Chapter8/RearrangeHomComplexX.lean`, the cohomological twin of the `Tor` carrier diamond above).
The cochain-complex `.X` objects are `((linearYoneda k _).obj N).obj (op Z)`, whose `Module k (Z ⟶ N)`
is the categorical `Linear.homModule`; the per-summand `summandIso` and the target tensor factors are
spelled `ModuleCat.of k (Z ⟶ N)`, whose `Module k` is `ModuleCat.Hom.instModule` picking the *external*
`Module k N` (`TensorProduct.instModule` on `N₁⊗N₂`, ambient `Module k Nᵢ` on each factor) — **not** the
algebra-restricted one. So `(linearYoneda…).obj (op Z)` is **not defeq** to `ModuleCat.of k (Z ⟶ N)`,
`ChainComplex.linearYonedaObj_X` is a non-`rfl` simp lemma, and `LY.map … ≫ summandIso.hom` won't
typecheck. **Fix that worked (sorry-free):** prove the object equality as an `eqToIso`-able lemma —
`by rw [ChainComplex.linearYonedaObj_X]; dsimp only [linearYoneda]; congr 1; refine Module.ext' _ _
(fun r f => ?_); apply ModuleCat.hom_ext; apply LinearMap.ext; intro z; exact algebraMap_smul A r
(f.hom z)` (the `congr 1` peels `ModuleCat.of`, `Module.ext'` reduces to smul equality, and
`algebraMap_smul` is the scalar-tower reconciliation — one per algebra `A`/`A₁⊗A₂`). Then
`fullSummandIso := eqToIso srcEq ≪≫ summandIso ≪≫ tensorIso (eqToIso …) (eqToIso …)` and the complex
iso is `eqToIso (linearYonedaObj_X …) ≪≫ coreIso`. Cheaper than the `Tor` note's identity-carrier
`LinearEquiv` when the two objects are literally `ModuleCat.of k (same carrier)` with different
`Module k` args. Also: `Hom(-,N)` (`(linearYoneda k _).obj N`) is `Additive` (`linearYoneda_obj_additive`),
so it sends the degreewise `mapBifunctor` coproduct to a biproduct — assemble the degreewise iso as a
finite `∑` over `Finset.univ`/`Fintype` of the fiber with per-summand `ι`/`π` from `mapBifunctorDesc`
(delta) and `ι_mapBifunctorDesc`, discharging the two composites via `Functor.map_sum` +
`CategoryTheory.op_sum`. Beware `Functor.map_id`/`map_sum` name-clash with Lean's monad `Functor`: use
`CategoryTheory.Functor.map_id`.

**`⨁` notation clash under `open CategoryTheory`.** In a file with `open CategoryTheory` (common in
Chapter 4 files using `FDRep`/`Simple`), the `⨁` big-operator resolves to the *categorical biproduct*,
not `DirectSum` — writing `⨁ (_ : ι), M` for a `DirectSum` then fails with a baffling
`failed to synthesize Category ι`. Fix: write the type explicitly as `DirectSum ι (fun _ => M)`
(or `open DirectSum` after the section). `Representation.directSum`/`.prod` and the
character-additivity lemmas `char_prod`/`char_directSum` (Problem 4.12.6) are the usual companions.

**Distinct-but-defeq local `Module k` instances break `rw`/`simp` on imported lemmas — use `erw`
or a `rfl`-restatement.** This file's own `instModuleK`/`instModuleKObj` and `ExternalTensorFunctor`'s
*private* `restrictModule₁` are all `Module.compHom X (algebraMap k Bᵐᵒᵖ)` — defeq but **syntactically
distinct** (the private ones aren't importable, so you must redeclare). An imported `@[simp]` lemma
like `extTensorFunctorMapHom_tmul` (whose `m₁ ⊗ₜ[k] m₂` is baked in `restrictModule₁`) then silently
fails to fire on a goal whose `x ⊗ₜ[k] y` came from *your* induction context (`instModuleK`) — `rw`
reports "did not find pattern", `simp only` lists it as "unused". Two robust escapes: (a) `erw [lemma]`
(matches up to reducible defeq), or (b) restate the lemma with a `rfl` proof in your own instance
context (`theorem extMapHom_tmul … := rfl`) so its LHS matches syntactically. Do **not** chain many
`erw`s in one call — each does an expensive defeq search and the combined term blows up `whnf`; keep
them on separate lines.

**A stale `simp only [...]` in a helper that mirrors a Mathlib sibling lemma: re-copy the
sibling's *current* proof instead of debugging the old argument list (#7526).** In
`Chapter7/Example7_9_2.lean`, `left_adjoint_linear` (the `Functor.Linear` companion of
`Adjunction.left_adjoint_additive`) had a hand-tuned `simp only [homEquiv_unit,
Functor.map_smul, ← Functor.comp_map, ← adj.unit.naturality, …]` that left an unsolved goal
against current Mathlib (the `←`-naturality/`comp_smul`/`id_map` args reported "unused" and
never fired). The fix was not to repair the chain but to open Mathlib's present proof of the
sibling (`left_adjoint_additive`: `set_option backward.defeqAttrib.useBackward true in … :=
(adj.homEquiv _ _).injective (by simp [homEquiv_unit])`) and mirror it verbatim for `map_smul`.
When a stale-proof regression is on a lemma that names a Mathlib analogue in its docstring,
grep Mathlib for that analogue and copy its proof style first — it is usually a one-liner and
tracks the API drift you are fighting. (Also: `set_option … in` must sit *before* the
docstring, not between docstring and `lemma`.)

**Discharging an `↔`/membership goal over a `Prop` def with `omega`: use `unfold theDef; omega`, not
`simp only [theDef]; omega`.** For a decidable `Prop` def built from `∨`/`∧`/`=`/`≤` over `ℕ` (e.g. an
explicit graph adjacency pattern like `armAdjIdx` in `Chapter6/Problem6_1_3_continued_tildeE.lean`),
`simp only [theDef]` may partially rewrite the unfolded body (collapsing a clause, reordering) into a
shape `omega` no longer recognizes — it then reports a bogus counterexample (tell-tale sign: the
counterexample omits variables that appear in the def, e.g. no `q` when the def mentions `p+q+1`). A
plain `unfold theDef; omega` hands `omega` the raw disjunction and closes it. Also prefer explicit
`i ≤ p+q ∧ j ≤ p+q` over `max i j ≤ p+q` in such defs — equivalent, and cheaper for `omega`.

**When `erw` *itself* times out (`whnf` heartbeat blow-up on a big `ModuleCat`/iso term), close by
explicit-term `refine`, not a rewrite.** For a two-sided goal `LHS = RHS` where a pointwise helper
`h : … = …` applies to each side but `rw`/`simp` "did not find pattern" and `erw` blows `whnf` even
at `maxHeartbeats 1000000`: apply the helper as a *fully-applied term* (all section args explicit,
no metavars) inside `refine (h_left …).trans (Eq.trans ?_ (h_right …).symm)` and let `refine`'s
defeq unification match each side; discharge the residual middle goal (the two helpers' RHS, equal
by definitional differential/whisker reductions) with `rfl`. This sidesteps both syntactic `rw`
matching and `erw`'s runaway `whnf`. Pointwise `ModuleCat` helpers also need the *inner*
application spelled in the same coercion form as the goal (state the LHS as
`ModuleCat.Hom.hom (ModuleCat.Hom.hom f.inv (a ⊗ₜ b)) (y ⊗ₜ z)`, not the bare-coe
`f.inv (a ⊗ₜ b)`, which elaborates to `ConcreteCategory.hom` and won't match a `hom_comp`-reduced
goal). The `eqToHom`-on-elements bridge between same-carrier `ModuleCat` objects (different
`Module k` instance) is `HEq (ModuleCat.Hom.hom (eqToHom h) w) w := by subst h; rfl`, upgraded per
site with `eq_of_heq`.

**Exposing a value proved-inside an iff-of-existentials (`exists_congr`): extract the pointwise
iff first.** The recurring "compute this scalar / classify these reps" fidelity task (#7204,
#7211, #7231) needs the concrete witness, but a lemma stated as `(∃ c, P c) ↔ (∃ c, Q c)` and
proved by `apply exists_congr; intro c; …` severs the witness under `obtain` — both `.mp` and
`.mpr` hand back a *fresh* existential whose value you cannot recover, so you can never pin `c` to
your target. **Fix:** split the lemma — pull the per-`c` body out as `…_of (c) : P c ↔ Q c`, then
define the original existential lemma as `exists_congr (…_of …)` (one line, same signature, no
call-site churn). Now `(…_of _ target).mpr hproof` gives the pointwise action *at your concrete
scalar* directly. Worked example: `sumTranspositionsStab_acts_scalar_iff_content_const_of` in
`Chapter5/Problem5_16_3.lean` (#7231, exposing that `E=(12)+⋯+(1n)` acts on a rectangular `V_λ` by
`c − r`).

**Reading background-build results: grep the teed log for `error:`, do not trust a
wrapper's exit code or `tail`.** `lake build` prints Lean errors *before* the final
`Build completed` / `✖` summary, so `... | tee log | tail -40` can hide them, and a
separate poller/`sleep`-loop you spawn to wait has its own exit status unrelated to
the build's. Always confirm success by `grep -nE "error:|✖|Build completed" log`
on the full teed file (and check `#print axioms` for `sorryAx`) — never infer "build
passed" from a poller returning exit 0.

**Build-environment recovery (shared `.lake/packages` across pod worktrees):**
- `Lean exited with code 139` (SIGSEGV) on *dependency* files you did not touch has
  two distinct causes. (a) Corrupted Mathlib oleans from a concurrent `lake exe cache
  get` writing the shared dir — fix with `lake exe cache get!`, then rebuild. (b)
  **Memory pressure from build parallelism** — if the SAME heavy file builds fine in
  isolation (`lake build EtingofRepresentationTheory.Chapter5.<File>`) but segfaults
  during a big parallel build, it is OOM, not corruption. Build the heavy files one
  at a time, then the target.
- `failed to read file '...olean', incompatible header` means `main` bumped the Lean
  toolchain mid-session. `lake exe cache get` only fetches **Mathlib** oleans, NOT
  the upstream deps (batteries/aesop/Qq/importGraph/Cli/plausible) — those keep
  old-toolchain oleans and keep throwing `incompatible header`. Recovery order:
  1. `git fetch origin main`; if `origin/main:lean-toolchain` changed, rebase onto
     `origin/main`.
  2. The shared `.lake/packages/mathlib` checkout itself can lag the manifest
     (`lake update` may not move it): `grep -A2 '"name": "mathlib"' lake-manifest.json`
     for the pinned `rev`, then `git -C .lake/packages/mathlib checkout <rev>` so its
     `lean-toolchain` matches the project.
  3. `lake exe cache get`, then rebuild the stale upstream deps (`lake build Batteries
     Aesop ...`, or just build your target and let lake regenerate them).
- A **stale session in another worktree** still on the pre-bump toolchain can rebuild
  the shared dep oleans back to the old version, re-corrupting your build in a loop.
  Check `pgrep -fl 'v4.28'` (the old version); if a `lake`/`lean` from an obsolete
  worktree is running, terminate that specific PID (targeted, not `pkill`).
- **Never run two `lake build` invocations against the same worktree at once.** The
  harness auto-backgrounds slow builds, so re-issuing `lake build` (or launching an
  aggregate build while a single-file one is in flight) stacks concurrent lake
  instances that race on the shared build dir and lock, yielding **spurious `build
  failed` / `✖` for modules you never touched**. Symptom: a sibling file "fails" in
  the aggregate build but compiles fine standalone. Fix: wait for the running build
  (`while pgrep -x lake >/dev/null; do sleep 5; done`) before starting another, and
  trust the single-file result — a module that builds in isolation is not broken.

**A prerequisite the issue says "landed" may still be in an unmerged PR, not `main`.** In parallel
formalization, issues are often written against a dependency that is only *open as a PR* (its file
is absent from your fresh `main` checkout). Don't skip/block — instead: (a) find the PR
(`gh pr list --search "<File>"` or by the issue# it closes), (b) read its API from the branch
without checking it out (`git show origin/<branch>:<path>`), (c) drop a **temporary untracked** dev
copy of that file into your worktree so you can `lake build` your new work against it, and (d) when
the prerequisite PR's CI is green, merge it (`gh pr merge <N> --squash --delete-branch`), then
`git merge origin/main`, delete your dev copy, and add your file to the chapter aggregator. Only
commit *your* file — never the dev copy (it arrives via `main`). This turned a "blocked on #6688"
situation into a same-session completion (#6684).

## Pre-Flight Checklist (Before Starting Any Proof)

Run this checklist before writing a single tactic. Skipping it has caused agents to waste entire context windows on dead-ends.

1. **Check Known Dead-Ends.** Scan the "Known Dead-Ends" section below. If your proof requires any of these patterns, sorry it immediately and move on:
   - ExteriorAlgebra ↔ PiTensorProduct bridging
   - ~~`if`-branching `obj` fields in QuiverRepresentation-like structures~~ — **NOT a dead-end for reasoning about a *single* fibre** (#6160, `simpleRep_isIrreducible` in `Chapter3/Problem3_9_3.lean`). Gotcha: for `simpleRep i` whose `obj v := Fin (if v = i then 1 else 0) → k`, the fibre `(simpleRep i).obj i` is defeq to `Fin (if i = i then 1 else 0) → k` but **NOT** to `Fin 1 → k` — the `if` is stuck because the `Decidable (i = i)` from an abstract `[DecidableEq Q]` never reduces to `isTrue`. Consequences: (a) instance search cannot find `AddCommGroup ((simpleRep i).obj i)` / `finrank`-lemmas since `.obj i` is not *syntactically* a `Pi`; (b) `is_simple_module_of_finrank_eq_one` `apply` fails to unify the bundled `instAddCommMonoid` against `AddCommGroup.toAddCommMonoid`. **Fix:** keep the honest stuck-`if` type — build an identity `LinearEquiv` `e : (simpleRep i).obj i ≃ₗ[k] (Fin (if i = i then 1 else 0) → k)` (all fields `fun _ => rfl`; target is *syntactically* a `Pi`, so TC finds `AddCommGroup`/`Pi.module`), get `IsSimpleOrder (Submodule k (Fin (if i = i then 1 else 0) → k))` from `is_simple_module_of_finrank_eq_one (by simp [Module.finrank_fin_fun])`, then transport the `eq_bot_or_eq_top` dichotomy back with `Submodule.orderIsoMapComap e` (`f.injective (by rw [h, map_bot])`). Off-vertex fibres `Fin 0 → k` are `Subsingleton` (submodules are `⊥`/`⊤` via `Submodule.eq_bot_iff`/`eq_top_iff'` + `Subsingleton.elim`). The full *round-trip* (`reflectionFunctor` compositions) below remains a dead-end.
   - **Abstract `ρ : QuiverRepresentation k Q` (not `simpleRep`): `finrank`/simple-module API needs `AddCommGroup` on every carrier — install it once with `acg`.** The `obj` carriers bundle only `AddCommMonoid`, so `isSimpleModule_iff_finrank_eq_one`, `Module.Free.of_divisionRing`, and `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq` (all require `[AddCommGroup M]`) don't fire on `ρ.obj v`. **Fix (mirrors `extDiff`):** `letI : ∀ v, AddCommGroup (ρ.obj v) := fun _ => Etingof.Problem6_9_3.acg (k := k)` as the first proof line — `acg = { inst with neg := (-1)•·, … }` keeps `toAddCommMonoid` defeq to the bundled instance, so `Module k (ρ.obj v)` stays compatible and TC now finds `Free`/finrank lemmas. Worked example: `irreducible_isSimpleRep` (#6166) proves an abstract irreducible `ρ` over a finite acyclic quiver is `≃` a vertex simple — all arrows vanish (well-founded induction on `fun a b => Nonempty (a ⟶ b)`, whose `Relation.TransGen` is irreflexive by `NoOrientedCycles`→positive `Quiver.Path i i`, hence WF via `Finite.wellFoundedOn`+`Subrelation.wf`), then `IsSimpleModule k (ρ.obj v₀)` gives `finrank=1` and `nonempty_linearEquiv_of_finrank_eq` builds the vertexwise iso (`commutes` is free since both sides' arrow maps are `0`). **Two tactic gotchas there:** (a) a `⊥=⊤ → Subsingleton` helper written as a local `have ∀ {M : Type*}` triggers `AddConstAsyncResult.commitConst: constant has level params […]` — a universe-polymorphic `have` breaks async elaboration; make it a **top-level** `private theorem` instead. (b) to read off `Function.update f v₀ U v₀ = U` from a `let F := Function.update …`, `rw [Function.update_self]` fails (can't see through the `let`); use `simpa only [F, Function.update_self]` (`simp only [F]` DOES unfold a `let`-bound local).
   - `Decidable.casesOn` **composition** (double round-trip) in `reflectionFunctorPlus`/`Minus` proofs — the composition F⁻(F⁺(V)) creates types Lean can't reduce through. **Note:** Individual arrow-level helper lemmas (e.g., `reversedArrow_ne_ne_is_cast`, `reversedArrow_ne_ne_twice`) ARE provable using `eqRec_heq_self` and `Subsingleton.elim` patterns (see HEq section below). The dead-end is the full Sigma-level round-trip, not individual components.
   - ~~`reflFunctorPlus_mapLinear_ne_ne` / `reflFunctorMinus_mapLinear_ne_ne` API (missing)~~ — **RESOLVED**: both now exist in `Chapter6/Definition6_6_3.lean` / `Definition6_6_4.lean` (plus `_eq_ne`, `_equivAt_ne`, `_equivAt_eq`); use them directly for reflection-functor naturality (ne/ne and eq/ne cases).
   - **Representation `W` over a *non-ambient* `Quiver` instance (e.g. `reversedAtVertex Q i`): dot-notation resolves the WRONG quiver.** `W.obj`/`W.sinkMap`/`W.instAddCommMonoid`/`W.mapLinear` synthesize the ambient `[Quiver Q]` for their instance arg, not `reversedAtVertex Q i`, giving "synthesized `inst✝` / inferred `reversedAtVertex Q i`" or "failed to synthesize `AddCommMonoid (W.obj v)`". **Fix:** write everything with explicit `@` pinning the quiver (`@Etingof.QuiverRepresentation.sinkMap k _ Q (Etingof.reversedAtVertex Q i) W i`), and provide the per-component `DirectSum`/`lof`/`component` instances via `letI acmW : ∀ b, AddCommMonoid (@…obj … (reversedAtVertex Q i) W b.fst) := fun b => @…instAddCommMonoid k Q _ (reversedAtVertex Q i) W b.fst` (and `modW` for `Module`). To *transport* such a rep back to the ambient quiver, package the vertex-space transport as a `LinearEquiv` via `match I₂, h with | _, rfl => LinearEquiv.refl` (turns the accessor `HEq`s into plain equations — see `objTransportEquiv`/`transportReversedTwiceEquiv` in `Chapter7/Exercise7_9_8.lean`).
   - ~~Definition-level `sorry : Type` for `AlgIrrepGL`~~ — **RESOLVED** (Wave 35): SchurModule constructed in PR #1740, AlgIrrepGL instances via `show ... from inferInstance` in PR #1752. Some downstream definition sorrys remain (`formalCharacter`, `kostkaNumber`).
   - ~~Nilpotent operator structure theorem (cyclic decomposition / Jordan chains) — not in Mathlib, blocks Problem6_9_1.~~ — **RESOLVED** (Wave 47): Problem6_9_1 proved without cyclic decomposition via direct IsCompl argument (#2215).
   - ~~Clifford theory (semidirect product orbit method) — blocks Mackey machine (Theorem5_27_1)~~ — **RESOLVED** (Wave 47): All Mackey machine sorries proved. PRs #2034, #2047, #2049 all merged after CI fix (#2240). The original 500-line estimate was too pessimistic — bypass approaches proved sufficient.
   - ~~`Submodule.map` of complementary submodules through non-injective maps — does NOT preserve complementarity. Problem6_9_1 IsCompl conditions hit this fundamental gap.~~ — **RESOLVED** (Wave 47): Bypassed via 7-step IsCompl proof that avoids map_of_complementary entirely (#2215).
   - `Lemma5_13_3` (Young symmetrizer idempotency) over general fields — currently only works over ℂ. Blocks the trace-based approach to Weyl character formula.
   - Corner ring Morita equivalence (`eAe` Morita equivalent to `A` for full idempotent `e`) — not in Mathlib, ~200-300 lines. Blocks BasicAlgebraExistence.
   - `basic_morita_algEquiv` (basic + Morita equivalent ⟹ isomorphic) — fundamental circularity: all non-circular approaches require Krull-Schmidt theorem or progenerator theory, neither in Mathlib.
   - ~~Right-multiplication dominance for polytabloids~~ — **RESOLVED** (Wave 46): The tabloid module approach (`TabloidModule.lean`) bypasses the right-multiplication issue entirely. Linear independence uses tabloid projections + unitriangularity, not direct dominance comparison. The remaining bottleneck is `polytabloid_syt_dominance` which needs a cross-column entry comparison argument (issue #2124).
   - `columnInvCount'` as straightening WF order — **PROVEN FALSE** (counterexample in #2104): for partition (2,2), σ = swap(1,2) has columnInvCount' = 1, but Garnir terms can also have columnInvCount' = 1. The correct WF order is tabloid dominance (multiset-based), not pointwise column inversion count. PR #2119 was closed as stale; straightening needs a fresh implementation using `tabloidDominance` from TabloidModule.lean.
   - Non-commutative `TensorProduct` — Mathlib requires `CommSemiring`. Balanced tensor product `A ⊗_{eAe} N` (or `M ⊗_A N`, `M` right / `N` left over a noncommutative `A`) must be built as a manual quotient. **Worked sorry-free template: `Chapter8/Definition8_2_3.lean` (Tor, #5628).** Recipe: right `A`-modules are `ModuleCat Aᵐᵒᵖ` (right action `m*a = MulOpposite.op a • m`); `M ⊗_A N := TensorProduct ℤ M N ⧸ S`, `S = AddSubgroup.closure {(op a • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (a • n)}`; the induced map for `f : M ⟶ M'` is `QuotientAddGroup.map S S' (TensorProduct.map f.hom.toAddMonoidHom.toIntLinearMap LinearMap.id).toAddMonoidHom h` (containment `h`: `AddSubgroup.closure_le` + `rintro ⟨a,m,n,rfl⟩` + `subset_closure ⟨a, f.hom m, n, by simp [map_smul,…]⟩`); then `Functor.leftDerived` over `AddCommGrpCat` gives the derived functor (`#print axioms` shows only `propext/choice/Quot.sound`, no `sorryAx`). **Functor-law proof pattern (cost me several iterations):** (a) extract the induced morphism as a *named* `def … : tensorOver M →+ tensorOver M'` plus a `@[simp]` `_mk` lemma (`f ↑(m ⊗ₜ n) = ↑(f.hom m ⊗ₜ n) := rfl`) — you cannot `simp [theFunctor]` inside the functor's own `where` block (self-reference error), and `ext` drills to *different* depths (bare tensor for single-morphism goals like `map_id`; only to the quotient for sum goals like `Additive.map_add`, where you then need `obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x`); (b) `induction x` (TensorProduct): `tmul` by `simp`, `add a b ha hb` by `simp only [map_add, ha, hb]`; coercion-additivity `↑(p+q) = ↑p + ↑q` is `map_add (QuotientAddGroup.mk' _) p q`. Unblocks corner ring Morita equivalence and BasicAlgebraExistence. **Feeding a commutative-ring module to this right-module `Etingof.Tor` (statement pass for Problem 8.2.7, `Chapter8/Problem8_2_7.lean`):** the argument is `ModuleCat Aᵐᵒᵖ`, but for commutative `A` (`ℤ`, `k[X]`) a left module has no automatic `Module Aᵐᵒᵖ`; supply it as a `noncomputable local instance … : Module Aᵐᵒᵖ M := Module.compHom M ((RingHom.id A).fromOpposite fun x y => mul_comm x y)` (do NOT make it a global instance — for `M = A` it diamonds with `Semiring.toOppositeModule`). To write a cyclic-module answer `A/gcd` without any `GCDMonoid`/`DecidableEq A` instance (unavailable for a general field's `k[X]`), use `A ⧸ Ideal.span {f, g}` — in a PID `(f)+(g) = (gcd)`. **Proof pass — higher `Tor`/`Ext` vanishing for cyclic `R/(a)` over a PID (#6263, `Problem8_2_7.lean`, all four `_vanish`; the content is projective dimension `≤ 1` via the length-`1` resolution `0 → R →(·a) R → R/(a) → 0`).** **Ext:** build the resolution in `ModuleCat R` (`ModuleCat.shortComplexOfCompEqZero f g eq0` + `ModuleCat.shortComplex_shortExact` from `Function.Exact f g`/inj/surj proved on the *bare* `LinearMap`s — `f := (a:R) • LinearMap.id`, `g := Algebra.linearMap`/`(Ideal.span {p}).mkQ`), then `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃ 1` (both free terms projective; `import Mathlib.CategoryTheory.Abelian.Projective.Dimension`) gives `HasProjectiveDimensionLT (R/(a)) 2`, and `HasProjectiveDimensionLT.subsingleton _ 2 (n+2) (by omega) _` kills `Extⁱ` for `i≥2`. **Tor** (right module lives in `ModuleCat Rᵐᵒᵖ`): build the *same* resolution over `Rᵐᵒᵖ` — the `·a` map's `map_smul'` closes by `simp only [RingHom.id_apply, MulOpposite.smul_eq_mul_unop]; ring` (the `Semiring.toOppositeModule` action is `r•x = x*r.unop`), and the quotient map's `map_smul'` by `rw [MulOpposite.smul_eq_mul_unop]; change …; rw [← map_smul]; …mul_comm` (the `Module.compHom` action `r•z` is **defeq** `r.unop•z`, so `change`/`rfl` bridge the two) — then squeeze the middle `Tor` between the two vanishing free-term `Tor` (`Functor.isZero_leftDerived_obj_projective_succ`) inside `Etingof.Functor.leftDerived_sixTerm_exact F hS (n+1) (n+2) rfl`, extracting the `ShortComplex.Exact` at the middle with `hExact.exact' 1 2 3` then `Exact.isZero_X₂ (h1.eq_of_src _ _) (h3.eq_of_tgt _ _)`. **`a=0`/`f=0` edge:** `R/(0) ≅ R` is free; do NOT rely on `Projective (ModuleCat.of Rᵐᵒᵖ (R/(0)))` instance search (it heartbeat-loops on `ZMod 0`) — transport `IsZero` along an explicit `Rᵐᵒᵖ`-linear equiv to the free module (`{ e0.toAddEquiv with map_smul' := fun r z => by change …; rw [smul_eq_mul, mul_comm] }`, `e0 := Submodule.quotEquivOfEqBot`; keep `x : R` on the *domain* side of the equiv so `HMul` doesn't get stuck on the `ZMod 0`/quotient carrier). The degree-`0`/`1` `Tor`/`Ext ≅ R/gcd` identifications are still `sorry` (out of scope of #6263). **When the module structure is the *external* tensor product over a *noncommutative* `A₁ ⊗[k] A₂` (Künneth, Problem 8.2.8, `Chapter8/Problem8_2_8.lean`)** the `compHom` shortcut no longer applies and `TensorProduct.Algebra.module` only builds `Module (A⊗B) M` from commuting actions on a *single* `M` — the external structure (`A₁` on the first factor, `A₂` on the second; plus `Algebra.TensorProduct.opAlgEquiv : (A₁⊗A₂)ᵐᵒᵖ ≃ₐ A₁ᵐᵒᵖ⊗A₂ᵐᵒᵖ` on the right-module `Tor` side) is not a defeq-safe instance. For a *statement* pass, don't construct it: take `Module (A₁⊗[k]A₂) …` / `Module (A₁⊗[k]A₂)ᵐᵒᵖ …` as instance-implicit theorem parameters **pinned** by a hypothesis fixing the action on simple tensors (`(a₁⊗ₜa₂) • (x₁⊗ₜx₂) = (a₁•x₁)⊗ₜ(a₂•x₂)`; wrap the right side in `MulOpposite.op` for the `ᵐᵒᵖ` case). Simple tensors generate and `•` is additive, so the pin determines the structure uniquely — faithful, and sidesteps statement-irrelevant instance plumbing. RHS `⨁_{j+m=i}` is `DirectSum` over `{p : ℕ × ℕ // p.1 + p.2 = i}` with `TensorProduct ℤ` summands (group-level shadow of the book's `⊗ₖ`, matching Problem 8.2.7). **`HasExt (ModuleCat.{v} R)`:** resolves from `Small.{v} R` (free when `R : Type v`), but synthesis heartbeat-times-out unless you `import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences` alongside `…ModuleCat.Ext.HasExt`. **Degree-`0`/`1` `Tor ≅ R/gcd` identifications (#6524, `Problem8_2_7.lean`, both `_tor_zero`/`_tor_one` sorry-free):** the glue `Etingof.tensorOverEquivTensor` (in `Definition8_2_3_RightExact.lean`) now converts the balanced `tensorOver A N M` into Mathlib's `TensorProduct A M N` for **commutative** `A`, given `hcompat : ∀ a m, op a • m = a • m` — reuse it (`(tensorOverEquivTensor hcompat).trans (PolyGcd.tensorEquiv f g).toAddEquiv` for `Tor₀`; and `polyTensorOverEquiv N := (tensorOverEquivTensor …).trans (TensorProduct.lid …).toAddEquiv` as the `intTensorOverEquiv` analogue for the `Tor₁` six-term window). **`hcompat` has two instance-dependent proofs, and picking wrong wastes iterations:** for the *free* module `M = A` (or when TC lands on the global `Submodule.Quotient.module'`), `op_smul_eq_smul a m` closes it (that instance carries `IsCentralScalar`); but when `tensorOverEquivTensor`'s `[Module Aᵐᵒᵖ M]` unifies to the `mopPolyQuot`/`ModuleCat.of`-pinned instance (`M = k[x]/f`), `op_smul_eq_smul` synthesizes the *wrong* SMul and mismatches — instead feed the proof through a `?_` hole (`refine … (tensorOverEquivTensor ?_).trans …`, so Lean pins the expected instance) then `intro a m; change (op a).unop • m = a • m; rw [MulOpposite.unop_op]` (the `compHom` action is defeq to the unop action). The `Tor₁` proof is a line-for-line port of the part-(i) `i_tor_one` with `ZMod ↝ k[x]/·`, `mulByCast ↝ PolyGcd.mulBy`, `zmodKerEquiv ↝ PolyGcd.kerEquiv`. **Proving a bespoke tensor/derived functor preserves `ShortExact` — flatness of projectives (#6587, `Chapter8/TensorProjectiveExact.lean`, all sorry-free except the free/coproduct case #6600).** Reusable Mathlib names that took real reconnaissance: `ShortComplex.shortExact_of_iso (e : S₁ ≅ S₂) (h : S₁.ShortExact)` transfers along an iso; `S.mapNatIso (τ : F ≅ G) : S.map F ≅ S.map G` (needs `PreservesZeroMorphisms`, free from `Functor.Additive`); `ShortComplex.ShortExact.map_of_exact` needs **both** `[PreservesFiniteLimits F] [PreservesFiniteColimits F]` — and `forget₂ (ModuleCat R) AddCommGrpCat` HAS both (bare `inferInstance`), as does any composite of exact functors; `AB4 AddCommGrpCat` / `AB5` (`Mathlib.Algebra.Category.Grp.AB`) give coproduct exactness. **`ShortExact` is NOT in Mathlib as "stable under retracts" — build it** (`shortExact_of_retract`, general `[Abelian D]`): mono/epi via `MorphismProperty.of_retract (P := monomorphisms/epimorphisms _)` (feed `RetractArrow T.f U.f` built from the ShortComplex retract `h` by `{ i := Arrow.homMk h.i.τ₁ h.i.τ₂ h.i.comm₁₂, r := …, retract := Arrow.hom_ext _ _ e₁ e₂ }` where `eⱼ : h.i.τⱼ ≫ h.r.τⱼ = 𝟙` comes from `rw [← ShortComplex.comp_τⱼ, h.retract, ShortComplex.id_τⱼ]` — feed `e₁ e₂` to `Arrow.hom_ext` **by defeq**, since `(Arrow.mk T.f).left` does not `simp`-reduce to `T.X₁`); exactness via `Retract T.homology U.homology := h.map (ShortComplex.homologyFunctor D)` + `IsZero.iff_id_eq_zero` + `hz.eq_of_tgt hr.i 0` (retract of a zero homology is zero). **Functoriality of the tensor in the module argument** is a bifunctor `ModuleCat Aᵐᵒᵖ ⥤ (ModuleCat A ⥤ AddCommGrpCat)` (obj `M ↦ tensorLeftFunctor A M`, map via `tensorRightMap`); its `map_id`/`map_comp` close by `refine NatTrans.ext (funext fun N => ?_); apply AddCommGrpCat.hom_ext; apply tensorOver_hom_ext; intro m n; rfl` (a bare `ext N` descends all the way to elements and then `AddCommGrpCat.hom_ext` fails — stop at the component with `NatTrans.ext (funext …)`). Then `Retract.map (bifunctor)` + `S.mapNatTrans` builds the short-complex retract `mapRetract`. **Projective ⇒ retract of free** is free: `Projective.factorThru (𝟙 P) ε` / `Projective.factorThru_comp` where `ε := (ModuleCat.adj Aᵐᵒᵖ).counit.app P` is epi via the instance `Adjunction.counit_epi_of_R_faithful` (`forget` is faithful); the free cover is `(ModuleCat.free Aᵐᵒᵖ).obj ↑P = of Aᵐᵒᵖ (↑P →₀ Aᵐᵒᵖ)`. The unit iso `Aᵐᵒᵖ ⊗_A N ≅ N` (`x ⊗ n ↦ x.unop • n`, inverse `n ↦ 1 ⊗ n`) is `homEquivInvFun` of `Φ x := DistribSMul.toAddMonoidHom N x.unop`, packaged into a `NatIso` to `forget₂` — its naturality square closes by `exact (map_smul g.hom x.unop n).symm` after `rw [AddEquiv.coe_toAddMonoidHom, tensorSndMap_mk]` (the `unitorEquiv_apply` `rw` won't fire through the `⇑.toAddMonoidHom` coe, so finish by defeq `exact`). **Packaging a *pointwise* module construction as a `ModuleCat` bi/functor (#6679, `Chapter8/ExternalTensorFunctor.lean`, `extTensorFunctor : ModuleCat A₁ᵐᵒᵖ ⥤ ModuleCat A₂ᵐᵒᵖ ⥤ ModuleCat (A₁⊗A₂)ᵐᵒᵖ` on `extTensorModule`, sorry-free) — three gotchas each cost real iterations:** (i) **`ModuleCat` must be imported** (`import Mathlib.Algebra.Category.ModuleCat.Basic`) — a granular-import file that doesn't have it fails with the baffling `invalid use of explicit universe parameters, 'ModuleCat' is a local variable` (autoImplicit bound `ModuleCat`). (ii) The restricted `Module k X` / `IsScalarTower k Aᵐᵒᵖ X` / external-action instances that the pointwise construction needs on each `ModuleCat Aᵐᵒᵖ` *object* cannot be `letI`-in-body when they must appear in a *return type* (e.g. stating `extTensorFunctorMapHom : (X ⊗[k] Y) →ₗ[(A₁⊗A₂)ᵐᵒᵖ] …`) — provide them as **`local instance (X : ModuleCat Aᵐᵒᵖ) : …`** keyed on the `ModuleCat` carrier (`Module k X := Module.compHom X (algebraMap k Aᵐᵒᵖ)`; the tower by `rw [Algebra.smul_def]; exact mul_smul _ _ _`). Keyed on `↥X` they don't diamond onto the algebras. But then any lemma about `extTensorModule` stated via `(extTensorModule …).toSMul.smul` **won't `rw`/`simp`-match** the ambient `•` (which now resolves to your differently-named `local instance`) — **restate it with the ambient `•`** (`op(a₁⊗a₂) • (m₁⊗m₂) = …`, proof = the original lemma, defeq) and use *that*. (iii) **Functor-law proofs (`map_id`/`map_comp`/naturality) do NOT go through an abstract `φ.hom` extensionality** — because `extTensorFunctorObj = ModuleCat.of _ (X⊗Y)`, its carrier coercion `↑(obj)` is defeq-but-not-syntactic to `X ⊗ Y`, so after `LinearMap.ext fun z` + `TensorProduct.induction_on` the element `z` lands at `↑X⊗↑Y` while `φ.hom`'s FunLike is at `↑(obj)`, and `map_add`/`map_zero`/`rw [ha]` all silently fail to fire (nor does `TensorProduct.ext'`). Instead prove the id/comp laws at the **`mapHom` level** (domain literally `X ⊗ Y`, transparent coercion — `extTensorFunctorMapHom_id = LinearMap.id`, `extTensorFunctorMapHom_comp = _ ∘ₗ _`, each by `LinearMap.ext`+`induction`+`rfl`/`map_add`), then lift to `ModuleCat` via `ModuleCat.hom_ext` + `rw [extTensorFunctorMap_hom, …_id/comp, ModuleCat.hom_id/hom_comp]`, and assemble the functor (`map_comp`/`naturality` fields discharged by feeding `𝟙` to `extTensorFunctorMap_comp` + `Category.id_comp`/`comp_id`). The `map_smul'` of the morphism map (op-linearity of `TensorProduct.map`) is a double `TensorProduct.induction_on` inside `induction r using MulOpposite.rec'` — reduce `op(a₁⊗a₂)•(m₁⊗m₂)` on both sides with the restated `smul_tmul` lemma. **Reusing that infra in a *new* file (#6717, `Chapter8/ExternalTensorProjective.lean`, `extTensorFunctorObj_projective_of_free` sorry-free): the `restrictModule₁/₂ tower₁/₂ extModule` `local instance`s leak their *names* but not their instance-ness — re-activate with `attribute [local instance] restrictModule₁ restrictModule₂ tower₁ tower₂ extModule` (do NOT redeclare — "already declared").** **Proving the external tensor of two *free* modules is free over `(A₁⊗A₂)ᵐᵒᵖ`:** `finsuppTensorFinsupp` does NOT apply — the free carrier's `Module k` is the restricted `compHom` one, which is *not* defeq to the standard `Finsupp` `k`-module (`rfl` fails to identify the two `⊗[k]` types; they are literally different quotients). Bridge with an identity-function `k`-linear equiv `freeCastEquiv₁ : ↑((free A₁ᵐᵒᵖ).obj I₁) ≃ₗ[k] (I₁ →₀ A₁ᵐᵒᵖ)` (`toFun := id`, `map_smul' c x := algebraMap_smul A₁ᵐᵒᵖ c (id x : _ →₀ _)` — the two `k`-actions agree), then `TensorProduct.congr freeCastEquiv₁ freeCastEquiv₂ ≪≫ₗ finsuppTensorFinsupp k k A₁ᵐᵒᵖ A₂ᵐᵒᵖ I₁ I₂ ≪≫ₗ Finsupp.mapRange.linearEquiv (Algebra.TensorProduct.opAlgEquiv k k A₁ A₂).toLinearEquiv` is a `k`-linear equiv to `I₁×I₂ →₀ (A₁⊗A₂)ᵐᵒᵖ`. **Promote it to `(A₁⊗A₂)ᵐᵒᵖ`-linear** by supplying `map_smul'` via `induction r using MulOpposite.rec'` → `induction s using TensorProduct.induction_on` → on the `tmul a₁ a₂ / tmul x y` generator, `rw [extTensorFunctor_op_smul_tmul, RingHom.id_apply, <generator lemma>]` where the generator lemma `freeExtTensorEquivK ((op a₁•x)⊗(op a₂•y)) = op(a₁⊗ₜa₂) • freeExtTensorEquivK (x⊗y)` is proved coordinatewise (`Finsupp.ext`, `finsuppTensorFinsupp_apply`, `← Algebra.TensorProduct.tmul_mul_tmul`, `map_mul`, `opAlgEquiv_tmul`). Finish `ModuleCat.projective_of_free (Module.Basis.ofRepr thatEquiv)` (note: `Basis` is now `Module.Basis`). **Two traps:** (a) state the promoted equiv over the *raw* `↑F₁ ⊗[k] ↑F₂` carrier, NOT `↑(extTensorFunctorObj …)` — under the `ModuleCat.of` coercion `rw`/`simp` silently fail on `smul_zero`/`add_tmul`/`map_zero` (`Basis.ofRepr` re-coerces to the object by defeq at the end anyway); (b) coordinate access `x i` on a `↑(ModuleCat…)`-typed Finsupp does NOT elaborate ("function expected") — route through `freeCastEquiv₁ … x i`. **Transporting a coproduct-preserving additive functor `G` (e.g. `restrictScalars`) through a `mapBifunctor`/total complex when Mathlib has NO "functor commutes with total" lemma (#6738, `Chapter8/ExternalTensorRestriction.lean`, `extTensorComplex_restrictIso` sorry-free) — don't search for the lemma, build the chain iso degreewise via `isoOfComponents`:** (a) **degree-`n` object iso** `= PreservesCoproduct.iso G (bicomplex.toGradedObject.mapObjFun π n) ≪≫ Limits.Sigma.mapIso (fun i => pointwiseObjIso …)` — `(mapBifunctor …).X n` is *defeq* `∐ (bicomplex.toGradedObject.mapObjFun π n)`, `G` preserves it (here `preservesColimit_restrictScalars`; `PreservesCoproduct.iso` needs `[HasCoproduct fun i => G.obj (f i)]` + the `PreservesColimit` instance, both auto), and `Sigma.mapIso` swaps summands via the pointwise bifunctor iso; the whole thing type-checks by defeq (`(curriedTensor C).obj X |>.obj Y = X ⊗ Y`, `((F.mapBifunctorHC c c).obj K₁).obj K₂` = the bicomplex). (b) **summand-compat lemmas** `ι… ≫ iso.inv`/`.hom`: `simp only [iso_def, Iso.trans_inv, PreservesCoproduct.inv_hom, HomologicalComplex.ιMapBifunctor, HomologicalComplex₂.ιTotal, CategoryTheory.GradedObject.ιMapObj, Limits.Sigma.ι_mapIso_inv_assoc, Limits.ι_comp_sigmaComparison]` — you MUST unfold `ιMapBifunctor→ιTotal→ιMapObj→Sigma.ι` **by name** (they're `def`s, not simp-normal, so `Sigma.ι_mapIso_*`/`ι_comp_sigmaComparison` won't match otherwise); derive the hom-direction from the inv one by `rw [← cancel_mono iso.inv, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, inv_lemma, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]`. (c) **differential compat** (the `isoOfComponents` `comm`): `rw [← cancel_epi iso.inv, Iso.inv_hom_id_assoc]; apply HomologicalComplex.mapBifunctor.hom_ext; intro i₁ i₂ h`, expand both `d = D₁+D₂` (`mapBifunctor.d_eq`, `ι_D₁`, `ι_D₂`), pull each `dₖ` with `mapBifunctor.dₖ_eq`/`dₖ_eq_zero'` (case-split `rcases iᵣ with _ | i'`; `by simp [ComplexShape.down_Rel]` proves `Rel (i'+1) i'` and `ChainComplex.next_nat_zero` the `i=0` no-`Rel` branch), and land each surviving term on the **pointwise bifunctor naturality** (`extRestrictObjIso_naturality`). The Koszul sign `ε : ℤˣ` is the SAME on both sides ⇒ cancel it with `Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul` then `congr 1` (do NOT reach for `Functor.map_zsmul`/`Preadditive.zsmul_comp` — `ComplexShape.ε₁/ε₂` are `ℤˣ`, not `ℤ`; and `Linear ℤ C` is a free instance for any preadditive `C`, so the `Linear.*` lemmas apply). Expose the restricted differential `((F.mapHomologicalComplex c).obj K).d n m = F.map (K.d n m)` via `Functor.mapHomologicalComplex_obj_d` before merging two `F.map`s with `← Functor.map_comp_assoc`. Match the RHS `(curriedTensor C).map f |>.app Y = f ▷ Y`/`(curriedTensor C).obj X |>.map g = X ◁ g` with the naturality's `tensorHom (res₁.map f) (res₂.map g)` by `CategoryTheory.Functor.map_id` (qualify it — bare `Functor.map_id` is the *applicative* `<$>` one) + `MonoidalCategory.tensorHom_id`/`id_tensorHom`, finishing by `rfl`/`congr 2`. **π/augmentation degree-0 compat** (`ι_extRestrictComplexXIso_aug₀`, the map-level `i=0` square the quasiIso assembly consumes) is even shorter: `← Functor.map_comp_assoc, HomologicalComplex.ι_mapBifunctorDesc`, collapse the two half-maps `(F.map a₁).app _ ≫ (F.obj _).map a₂` to `extTensorFunctorMap a₁ a₂` via `← extTensorFunctorMap_comp` + `comp_id`/`id_comp`, then one `extRestrictObjIso_naturality`.
   - **Noncommutative *induction* functor `A ⊗_S - : ModuleCat S ⥤ ModuleCat A` and its tensor–hom adjunction, for a ring hom `f : S →+* A` with `S` commutative but `f`'s image not central (#6433, `Chapter9/PathAlgebraInduction.lean`, sorry-free — the left adjoint of `restrictScalars` that Mathlib's `extendScalars` can't supply because it needs `CommRing A`).** Recipe: (a) **right-mult `S`-module on `A`**, `s•a = a*f s` — build via the opposite embedding `f.toOpposite hcomm : S →+* Aᵐᵒᵖ` (needs `hcomm : ∀ s t, Commute (f s) (f t)`, true here since `f`'s image is the commutative vertex subalgebra) then `Module.compHom A (f.toOpposite …)`; this is a *global* `noncomputable instance` (no diamond — `S ≠ A` as types). It gives `SMulCommClass S A A` (`smul_comm` by `mul_assoc`), so **`TensorProduct.leftModule` supplies the left `A`-action on `A ⊗[S] M` for free** (`a•(b⊗ₜm)=(a*b)⊗ₜm`). (b) Functor morphism map = `TensorProduct.map (LinearMap.id (R:=S) (M:=A)) l.hom` (S-linear) *upgraded* to `A`-linear: `{ __ := TensorProduct.map … , map_smul' := … }` (the `__ :=` inherits `toAddHom`; prove `map_smul'` at the coe level with a leading `change … (a•x) = a• …`, then `TensorProduct.smul_tmul'`/`map_tmul`). Add a `@[simp] _tmul := rfl` lemma so `map_id`/`map_comp` close by `TensorProduct.induction_on` + `simp`. (c) **Adjunction via `Adjunction.mkOfHomEquiv`.** Backward map `a⊗m ↦ a•h m` is **`S`-balanced but NOT `S`-bilinear** (S acts by right-mult on `A`, through `f` on `N`), so `TensorProduct.lift` does *not* apply — use **`TensorProduct.liftAddHom (bilin : A →+ M →+ N) (balanced)`**, then re-add `A`-linearity via `map_smul'`. Factor `bilin` and the `balanced` proof into **named defs** (`symmBilin`/`symmBilin_balanced`) — inlining them into the anonymous constructor caused `isDefEq`/`whnf` **heartbeat timeouts** from the two-`Module`-structure coercion churn on `↑((restrictScalars f).obj N)` vs `↑N`. Naturality squares mostly close by `rfl` after `apply ModuleCat.hom_ext; ext`. (d) **Projectivity:** `Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms adj` (supply `restrictScalars`'s `PreservesEpimorphisms` inline: `constructor; intro …; rw [ModuleCat.epi_iff_surjective] at *; exact hφ`) + `S` semisimple (`Module.projective_of_isSemisimpleRing` → `M.projective_of_categoryTheory_projective`). **Two traps that cost real iterations:** (i) **`PathAlgebra k Q : Type (u+1)` not `Type u`** — `Quiver.Path` lands in `Type (max u v)` and the standard setup uses `Quiver.{u+1}`, so `A ⊗_S M` lives at carrier universe `u+1`; state the whole functor/adjunction at **`ModuleCat.{u+1}`** on both sides (matching `S`- and `A`-module carriers), and force the `M`-coercion in `ModuleCat.of A (TensorProduct S A (M : Type (u+1)))` or it reads `M` as the `Type (u+2)` object. (ii) a **`LinearMap` INTO a `restrictScalars` object** needs `ModuleCat.ofHom (X := M) (Y := (restrictScalars f).obj N) {…}` with *explicit* `(X:=)(Y:=)` (mirrors Mathlib's own `RestrictScalars.map'`) — otherwise the codomain is read as bare `↑N` and `Module S ↑N` fails to synthesize. **Building the *inner* bimodule tensor `V ⊗_S M` where a NON-canonical `S`-action must survive (#6480, `Chapter9/PathAlgebraStandardComplex.lean`, the standard short complex `A ⊗_S (V ⊗_S M) →ᵈ A ⊗_S M →ᵉ M`, sorry-free):** `V = ArrowIndex Q →₀ k` carries two commuting `S`-actions (source/target); the tensor is *balanced* over the target action but the *surviving* left `S`-action is the source one — and `TensorProduct S V M` ALSO has its own canonical (target) `Module S`. Three distinct `Module S` on one defeq carrier ⇒ diamond. **Break it with a `def` (NOT `abbrev`) type synonym per action:** `def ArrowTgt := ArrowIndex Q →₀ k` with the target action as its registered `Module (Q→k)` (used to *form* the tensor), and `def VtensCarrier M := TensorProduct (Q→k) ArrowTgt (restrict M)` with the **source** action registered by hand as `TensorProduct.map (srcHom s) LinearMap.id` (`srcHom s` = the source-scaling endo, `(Q→k)`-linear w.r.t. the *target* action via the bimodule `smul_comm`). Consequences that cost real iterations: **(a)** because `VtensCarrier` is a non-reducible `def`, `induction x` fails with "major premise not inductive" — use `induction x using TensorProduct.induction_on with | zero | tmul | add`. **(b)** a lemma stated about `s • (v ⊗ₜ m : VtensCarrier M)` resolves the smul to the *canonical* tensor instance, not yours (the `⊗ₜ` term's head is `TensorProduct`, and the type ascription does NOT reroute instance search) — state the helper about `TensorProduct.map (srcHom s) id (v ⊗ₜ m)` instead, and in proofs convert `s • x` (x a variable of type `VtensCarrier`, correct instance baked in) via `vtens_smul_def` *before* `TensorProduct.induction_on` substitutes a raw `⊗ₜ`. **(c)** build `d` as `homEquivSymm δ` where `δ : VtensObj ⟶ restrictScalars (A ⊗_S M)` is source-`S`-linear (its `map_smul'` uses `arrowInclusion (s ·_src v) = f s · arrowInclusion v`); the counit `ε` is `homEquivSymm (𝟙 _)`, equal to `inducedRestrictAdj.counit.app M` by `← Adjunction.homEquiv_symm_id` then `simp [theAdj, Adjunction.mkOfHomEquiv_homEquiv]; rfl`. **(d)** `congr 1` on a subtraction goal `a-b = c-d` can present the two subgoals in *reversed* order — use `refine congr_arg₂ (· - ·) ?_ ?_` for deterministic (a=c, then b=d) order. **Transporting a length/degree grading of `A` to an injective coordinate map on `A ⊗_S M` (#6514, `Chapter9/PathAlgebraInducedGrading.lean`, the noncommutative `coordMapCH` analogue for `koszulSES`-style `Mono d`/exactness):** given `lengthGrading : A →ₗ[k] (ℕ →₀ A)` with left inverse `lengthTotalize` (sum of graded pieces), (i) upgrade both to **`(Q→k)`-linear** for the *right* action `s•a = a*f s` — it is length-preserving because right-mult by `f s = vertexEmbedding s` scales each basis path by its *target* coordinate (prove `lengthProj_mul_vertexEmbedding` per-coordinate by `Finsupp.induction_linear`, then assemble `map_smul` by `Finsupp.ext`; do the single-case product as `@HMul.hMul (PathAlgebra k Q) …` per the def-opacity note above, and prove `single p c * f s = s(tgt) • single p c` via `c • ofPath` + `smul_mul`/`ofPath_mul_vertexEmbedding`/`smul_comm`); (ii) `inducedCoordMap := (TensorProduct.finsuppLeft (Q→k) (Q→k) A (restrictObj M) ℕ).toLinearMap ∘ₗ TensorProduct.map lengthGradingS LinearMap.id` gives `A ⊗_S M →ₗ (ℕ →₀ A ⊗_S M)` with `_tmul (a⊗ₜm) n = lengthProj n a ⊗ₜ m` (by `finsuppLeft_apply_tmul_apply`); **injectivity for free** from the `TensorProduct.map` left inverse (`← map_comp`, `lengthTotalizeS_comp_lengthGradingS`, `map_id`) composed with `finsuppLeft.injective`. **Trap:** the `ModuleCat A` coercion `↑(inducedRestrictObj M)` does NOT carry the `Module (Q→k)` the tensor needs for `→ₗ[Q→k]` — expose it with an `abbrev inducedCarrier M := TensorProduct (Q→k) A (restrictObj M)` (defeq to the coercion, but instance search finds the canonical tensor `Module (Q→k)`). **Splitting `d = stdd M` into half-maps `Φ,Ψ` + the `hshift_gen` coordinate-shift relation (#6535, same file `PathAlgebraConsSplittingIso.lean`, sorry-free):** `Φ (a⊗v⊗m) = (a·v)⊗m`, `Ψ (a⊗v⊗m) = a⊗(v·m)` are built exactly like `stdd` — `homEquivSymm` of the two `S`-linear halves `stdδΦ,stdδΨ` of `stdδ` (each with its own `liftAddHom (bilin) (balanced)` scaffold, the balanced/`map_smul'` proofs are literally the first/second `refine congr_arg₂ (·-·)` branch of `stdδ`'s proof: `arrowInclusion_wSMul_tgt` for `balanced`, `arrowInclusion_wSMul_src` + `TensorProduct.smul_tmul'` (Φ) / `one_tmul_smul` (Ψ) for `map_smul'`). Then `inducedCoordMap M (d ξ) (n+1) = Φ (ξ_n) − Ψ (ξ_{n+1})` (with `ξ_j := inducedCoordMapGen (V⊗_S M) ξ j`) by double `TensorProduct.induction_on ξ` (outer `a⊗y`, inner `y = v⊗m`) reducing to the landed generator lemma `inducedCoordMap_stdd_tmul_succ`. **Gotcha that cost a build cycle:** in the `add` cases, a Finsupp is evaluated at the index `n + 1`, and bare `rw [map_add]` UNIFIES `?f (?a+?b)` with that index application `F (n+1)` — it then fails synthesizing `AddHomClass (ℕ→₀_) ℕ _`. Use `simp only [map_add, Finsupp.add_apply]` (respects instance resolution, skips the index) plus `TensorProduct.tmul_add` for the inner split, then `abel`; never `rw [map_add]` when a `ℕ →₀` sits applied at `n+1`. **Assembling middle exactness `standardComplex_exact` via the downward degree telescoping (#6512, `Chapter9/PathAlgebraStandardResolution.lean`, sorry-free):** strong induction `standardComplex_exact_aux N` — coords vanish above `N` ⟹ `ξ ∈ im d`; the step subtracts `d η` for `η` the degree-`N` cons-preimage (`exists_stdΦ_preimage_topDegree`), lowering the top degree; base `N=0` needs `ε` injective on the length-`0` component (`A_0 ⊗_S M ≅ M`), proved by `ξ = (its coord 0)` (`inducedCoordMap_coord_zero` + `inducedCoordMapGen`/`_injective`) then `coord0 = 1 ⊗ ε(coord0)` (`lengthProj_zero_tmul`: the degree-`0` part is a `vertexEmbedding (Pi.single i c)`, moved across by `one_tmul_smul`; extract the length-`0` basis path via `cases p with | nil | cons` on the `Quiver.Path`). **Statement-level tensor-carrier trap that cost ~3 build cycles:** writing a balanced tmul `x ⊗ₜ[Q → k] (m : M)` in a *theorem statement* fails `failed to synthesize Module (Q → k) ↑M` — the `A`-module carrier `↑M` has no `(Q→k)`-module (only `restrictObj M` does), and standalone the `⊗ₜ` can't infer it. Fix: give the whole tmul an expected type — ascribe `(… ⊗ₜ[Q → k] (m : M) : inducedCarrier M)` (propagates `restrictObj M` to the factor), or wrap the factor `show restrictObj M from (stdε M).hom …` / drop to the bound `m : restrictObj M` directly. The `←`-rewrite trick `have key := inducedCoordMap_zero_eq M ξ; rw [← hξ, hε, TensorProduct.tmul_zero] at key` (with `hξ : ξ = inducedCoordMap M ξ 0`) turns `coord0 = 1⊗ε(coord0)` into `ξ = 0` without re-deriving the ascription.

   - **`Function.Injective (stdΦ M).hom` (whole-map cons-splitting injectivity) is NOT among the landed #6541 seeds — it needs a genuine left inverse (retraction) of `stdΦ`, the `A_n ⊗_S V ≅ A_{n+1}` inverse = #6545's deliverable.** `exists_stdΦ_preimage_topDegree` gives only *surjectivity* of `Φ` (enough for middle exactness). `Mono (stdd M)` (#6561) additionally needs `Φ`-injectivity (applied to the top graded component `ξ_N` after `Φ(ξ_N) = Ψ(0) = 0`): build `R := TensorProduct.liftAddHom Rbilin Rbilin_balanced` sending a basis path `q` (length `n+1`) to `(coeff • ofPath p) ⊗ (single e 1 ⊗ m)` via `exists_cons_decomp`, `0` on vertices, and prove `R ∘ Φ = id` using cons-uniqueness `ofPath_mul_arrowElt_inj` (composable) / source-action balancing vanishing (non-composable). Don't expect the `finsupp_shift_eq_zero` analogy alone to close `Mono` — that lemma needs no injectivity of `g` only because polynomial `Φ = X•𝟙` is coordinate-identity; here `Φ` genuinely transforms coordinates.
   - **Tensor of an acyclic complex is acyclic, over a field (Problem 7.8.7(ii), #6304, `Chapter7/Problem7_8_7.lean`).** Route: (a) helper `acyclic_of_homotopy_id_zero : Homotopy (𝟙 X) 0 → X.Acyclic` — `Homotopy.homologyMap_eq` gives `𝟙 (Hⁱ X) = homologyMap (𝟙 X) i = homologyMap 0 i = 0`, then `exactAt_iff_isZero_homology` + `IsZero.iff_id_eq_zero`. (b) `Etingof.Exercise7_8_4 K hK : Nonempty (Homotopy (𝟙 K) 0)` (over a field an acyclic complex is contractible). (c) Whisker that homotopy through the tensor bifunctor with **`HomologicalComplex.mapBifunctorMapHomotopy₁`** (homotopy in the *first* arg — use for the `C`-acyclic case) / **`mapBifunctorMapHomotopy₂`** (second arg — `D`-acyclic case), from `Mathlib/Algebra/Homology/BifunctorHomotopy.lean`. `tensorObj`/`tensorHom` on `HomologicalComplex` are defeq to `mapBifunctor`/`mapBifunctorMap` for `F := curriedTensor (ModuleCat k)`, `c := ComplexShape.up ℤ`. Bridge the homotopy's endpoints to `𝟙`/`0` with `Homotopy.ofEq`: `mapBifunctorMap (𝟙)(𝟙) = 𝟙` by `rw [mapBifunctorMap, CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, HomologicalComplex₂.total.map_id]; rfl`, and `mapBifunctorMap 0 g = 0` (and `f 0 = 0`) by `apply HomologicalComplex.hom_ext; intro j; apply HomologicalComplex.mapBifunctor.hom_ext; intro i₁ i₂ hji; simp` (the `ι_mapBifunctorMap` simp lemma + the bifunctor killing `0`). **Two gotchas:** (i) `Functor.map_id`/`Functor.map_zero` resolve to the *applicative* `_root_.Functor` (`id <$> x`) and silently mismatch — always qualify `CategoryTheory.Functor.map_id`. (ii) `Acyclic` is a `Prop` but `Homotopy` is data (`Type`): `rcases`/split the `C.Acyclic ∨ D.Acyclic` disjunction *first* (while the goal is still the `Prop` `Acyclic`), then build the homotopy inside each branch — you cannot eliminate an `Or` into a `Homotopy`.
   - `garnir_reduction'` algebraic approach — The standard approach using `a_λ · G = 0` (Garnir element annihilated by row symmetrizer) and Lemma 5.13.1 collapses to a tautology when trying to extract the linear combination. The algebraic identity only shows the existing tabloid is in the span — it doesn't produce the *smaller* tabloids needed for the inductive step. Needs tabloid-level reasoning (James' approach: work with equivalence classes of fillings under row permutations) instead.
   - Polytabloid transfer map `tabloidProjection(polytabloid T) = polytabloidTab T` — **PROVEN FALSE** (Wave 46-49): For partition (3,2), two distinct SYTs can map to the same inverse-tabloid. The dominance property (`swap_column_dominance`) fails for σ_T⁻¹. 4+ agent sessions were wasted on this approach across issues #2189, #2212. The correct approach uses tabloid-level unitriangularity (Track 2 in TabloidModule.lean), not direct transfer.
   - ~~`iso_of_formalCharacter_eq_schurPoly` — Requires GL_N complete reducibility (Schur-Weyl duality), which is NOT in Mathlib.~~ — **RESOLVED**: now sorry-free at `SchurWeylFormalCharacterIso.lean:992`, built on `decompose_polynomial_gl_rep` (GL_N-equivariant complete reducibility, `PolynomialGLDecomposition`) + `schurPoly_linearIndependent` + the highest-weight identification. The ~300-line infrastructure was built. **Use it** as the GL char→iso keystone: it takes `halg : IsAlgebraicRepresentation`, `h_span` (ℕ-weight spaces span ⊤), and `h : formalCharacter = schurPoly N lam`, and returns `Nonempty (M ≅ SchurModule k N lam)`. Do NOT treat highest-weight / character→iso work (e.g. the §5.23 contragredient identity) as blocked on this.

   **Before recording a "missing from Mathlib" / "needs a helper Mathlib lacks" claim** in a docstring or issue, grep the relevant Mathlib file — pessimistic absent-API notes propagate and block successors who trust them. (#5320: a prior `clength_additive` docstring said the second-isomorphism diagram chase "needs a pseudoelement-membership helper Mathlib does not yet have"; in fact `Abelian.Pseudoelement.sub_of_eq_image`/`pseudo_pullback` and the categorical snake lemma `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` are all present and make the route reachable.) When the section *introduction* blob states a standing assumption (e.g. §9.6 "every object has finite length"), check whether the formalized class actually carries it — dropped standing assumptions are a fidelity gap that makes per-section theorems unprovable as stated (#5320: `IsFiniteAbelianCategory` omits finite length; the §9.6 carrier is `IsFiniteAbelianCategoryOverField.finiteLength`). **The flip side — discharging an over-hypothesis:** when a Ch9 theorem carries a `[IsNoetherianRing …]` / `[FiniteDimensional …]` / `[Module.Finite …]` side condition on an `End`/`Hom` object that the book never states, it is almost always auto-satisfied via the over-field carrier — `Etingof.IsFiniteAbelianCategoryOverField.finiteDimensional_hom : FiniteDimensional k (X ⟶ Y)` (`Introduction_9_6.lean`) proves every Hom-space is finite-dim over `k`. From there `(End P)ᵐᵒᵖ` Noetherian is a 3-liner (`finiteDimensional_hom P P` → `Module.Finite k (End P)ᵐᵒᵖ` via the Mathlib opposite instance → `isNoetherian_of_tower k inferInstance`; the algebra/opposite `Module k` diamond is defeq, so `inferInstance` chains cleanly). #5665 removed exactly such a `[IsNoetherianRing (End P)ᵐᵒᵖ]` from `Theorem_9_6_4` this way. **Do NOT reach for the abstract subobject↔submodule (Galois) correspondence to derive these** — it needs arbitrary sups the finite-length subobject lattice doesn't carry in Mathlib; the over-field `finiteDimensional_hom` route is the intended lever. Pattern for keeping ring-level consumers (§9.7 `Introduction_9_7_Morita.lean` is deliberately `k`-free) working: keep the Noetherian-hypothesis proof as a general `_of_isNoetherian` engine and make the book-faithful theorem a thin over-field wrapper that derives the instance and delegates.

   **Forming `Fin n`- (or `ι`-)indexed biproducts in an abstract abelian category `[Category.{v} C]` — two instance traps (#6206, `Exercise9_6_3.lean`, progenerator characterization).** (a) `Abelian.hasFiniteBiproducts` is only an `attribute [local instance]` in Mathlib, so `HasFiniteBiproducts C` is **not** found by global TC search — `HasBiproduct (fun _ : Fin n => P)` fails to synthesize until you add `haveI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts` (then the global `hasBiproductsOfShape_finite` instance fires for any `[Finite J]`). (b) Mathlib's `Projective (⨁ g)` instance is declared `{β : Type v}` sharing the *morphism* universe `v`, so it does **not** apply to `g : Fin n → C` (`Fin n : Type 0`) when `v` is an arbitrary universe variable. Restate it universe-polymorphically: `theorem projective_biproduct {β : Type*} (g : β → C) [HasZeroMorphisms C] [HasBiproduct g] [∀ b, Projective (g b)] : Projective (biproduct g) where factors f e _ := ⟨biproduct.desc fun b => Projective.factorThru (biproduct.ι g b ≫ f) e, by refine biproduct.hom_ext' _ _ (fun b => ?_); simp [Projective.factorThru_comp]⟩`, and also supply `[∀ b, Projective (g b)]` explicitly (`haveI : ∀ b, Projective (g b) := fun _ => inferInstance` — the Pi-instance is not auto-derived from `[Projective P]`). Note `Etingof.wellFoundedLT_subobject` (Length.lean) gives `IsArtinianObject X` via `isArtinianObject.is_of_prop`, unlocking Mathlib's `exists_simple_subobject` for simple-quotient/subobject peeling inductions on `Etingof.clength` (`clength_additive`/`clength_strictMono` are the length arithmetic).

2. **Search for existing definitions and infrastructure.** Before defining any concept or building any equivalence/isomorphism, search the codebase:
   ```bash
   grep -r "def.*YourConceptName\|abbrev.*YourConceptName" EtingofRepresentationTheory/
   ```
   Duplicate definitions across chapters create incompatibility bugs that require manual refactoring later (e.g., duplicate `inducedCharacter'` in Ch5, duplicate `IsIndecomposable` in Ch2/Ch6). **Also search for infrastructure you might need** — PRs #1682, #1685, #1690 independently built the same GL₂(𝔽_q) BorelSubgroup equivalence because agents didn't check what already existed. Before building group/subgroup equivalences, coset decompositions, or character computation helpers, search for them first.

   **The same trap applies to whole *theorems*, not just helpers: a headline result is often already proven sorry-free under a different book-item name than the issue you claimed.** Book theorems and later problem-set problems frequently establish the *same* mathematical fact (a theorem states it; an exercise re-derives it via a guided route). Before starting — or accepting a multi-session decomposition of — a proof of a headline result, grep for an existing proof of the *same statement* under any name and just read your conclusion off it (per CLAUDE.md "use earlier results in the project"). #5311 (Problem 2.15.1(h)–(k), `sl₂` complete reducibility) was decomposed into a multi-session build (#5316/#5317/#5318), but `ComplementedLattice (LieSubmodule ℂ sl2 V)` was already proven sorry-free as `Theorem_2_1_1_ii` (Theorem 2.1.1(ii)) via the *same* Casimir argument; the final `complete_reducibility` sorry was a one-line `exists_isCompl` away. Grep by the mathematical content (`ComplementedLattice`, `IsCompl`, the target conclusion), not just the item id. **A sharper version of the same trap: when the formalized statement is a weaker *existential* rendering of a book problem whose prose describes a heavy explicit construction, that existential often follows in a few lines from a *stronger* already-proven neighbor — do not build the construction.** #6567 (Problem 9.6.5) asks in prose to construct the tensor functor `G = P ⊗_B −` and prove it quasi-inverse to `F = preadditiveCoyonedaObjFG`, but the formalized goal is only `∃ G ξ, (G ⋙ F ≅ 𝟭) ∧ (∀ X, Epi (ξ.app X)) ∧ IsIso ξ`. Theorem 9.6.4 already proves `F.IsEquivalence` (via ess-surj + fully-faithful, no circularity — 9.6.5 imports it), and any equivalence yields a genuine quasi-inverse for free: `G := F.asEquivalence.inverse`, `ξ := F.asEquivalence.unitIso.inv`, with (i) = `counitIso`, (ii) from `NatIso.isIso_app_of_isIso` + `IsIso → Epi`, (iii) from `Iso.isIso_inv`. The book's construction is one *route* to a quasi-inverse; an existential only needs *some* witness, so a stronger equivalence result discharges it directly. Before decomposing a "construct X and prove property P" issue, read the actual Lean goal: if it is `∃`-quantified, look for a neighboring theorem that already gives more than P.

   **When verifying Mathlib lemma names/signatures, grep *this project's own* `.lake/packages/mathlib`, never another Mathlib checkout elsewhere on the machine.** This repo pins a recent Mathlib; other local clones (e.g. `lean-training-data`) can be months behind, with renamed or absent API. Confirming against the wrong checkout sends you down dead ends — e.g. hand-rolling a matrix-charpoly-eigenvector argument because the project's cleaner `Module.End.trace_eq_sum_roots_charpoly_of_splits` / `hasEigenvalue_iff_isRoot_charpoly` (and the single-argument `Polynomial.Splits`) weren't visible in the stale checkout (#5129). **The same drift hits `import` module *paths*, not just lemma names** — modules get split and relocated between versions. Before writing a new `import Mathlib.…`, confirm the file exists: `find .lake/packages/mathlib/Mathlib -name 'GeomSum.lean'` (or grep for the lemma and read its file's module path). Guessing from memory wastes a build cycle on `bad import` — e.g. (#5287) `Mathlib.Algebra.GeomSum → Mathlib.Algebra.Ring.GeomSum`, `Mathlib.Algebra.Polynomial.Eval → Mathlib.Algebra.Polynomial.Eval.Defs`. **For a *new* file, just `import Mathlib`** (every project file does). The pinned Mathlib uses the `module`/`public import` system, so granular `import Mathlib.Foo.Bar` lines silently fail to expose public declarations — symptom is a baffling `Unknown identifier 'Basis'` at the `variable` line even though the import "succeeded". Also note `Basis` is now `Module.Basis`: a fresh file needs `open Module` for bare `Basis`/`End`/`finrank`/`finBasis` to resolve (#5638). These two cost ~4 build cycles when writing `Chapter5/DiagonalCoordinate.lean` from scratch. **The same granular-import gap can hit individual `Basis.*` lemmas even when the `Basis` type itself resolves**: in a pre-existing granular-import file, `apply Basis.ext …` / `rw [Basis.constr_basis]` reported `Unknown identifier` while `Pi.basisFun` worked fine. Fix: use **dot notation** — `b.ext fun i => …`, `b.constr_basis …` — which resolves through the term's type even when the fully-qualified name doesn't (#5301). (Adding a granular `import Mathlib.LinearAlgebra.Basis.Basic` did *not* help.) **In a pre-existing granular-import file (no `open Module`) the basis *constructor* and finrank-from-basis lemma need the `Module.` prefix**: `Module.Basis.mk hli hsp` (bare `Basis.mk` is `Unknown identifier`) and `Module.finrank_eq_card_basis` (bare `finrank_eq_card_basis` is unknown), provided by `import Mathlib.LinearAlgebra.Dimension.Finrank` + `…Dimension.Finite`. Eigenvalue theory over `IsAlgClosed` (`Module.End.exists_eigenvalue`, `HasEigenvalue.exists_hasEigenvector`, `Module.End.mem_eigenspace_iff`) needs `import Mathlib.LinearAlgebra.Eigenspace.Triangularizable`; `IsAlgClosed` needs `import Mathlib.FieldTheory.IsAlgClosed.Basic` (#6189). A clean "central element acts as a scalar on a simple f.d. module over `IsAlgClosed k`" (Schur) is: take an eigenvalue of `Algebra.lsmul k k V z`, its eigenspace is a nonzero `WeylAlgebra`-invariant `k`-submodule (`z` central), hence `⊤` by `IsSimpleModule` — no need for the `Module.End`-is-a-division-ring machinery. **Reusing a lemma from a `section` under a *different* typeclass regime — a `section variable [CharZero k]` gets stamped onto *every* declaration in that section, even ones that never use it** (the `unusedSectionVars` linter confirms this by warning), so calling such a lemma under `[CharP k p]` fails with `failed to synthesize CharZero k`. Symptom while proving `center_charP` (#6188): the char-free `adx`/`ady` monomial lemmas lived inside `section CharZeroSimple` and would not apply in characteristic `p`. Fix: hoist genuinely hypothesis-free infrastructure into its own `section` with only the minimal `variable (k) [Field k]`, *above* the char-specific sections, so both a `[CharZero k]` and a `[CharP k p]` consumer can use it. Cheaper than re-proving the lemmas per characteristic.

3. **Verify the statement.** Cross-reference the Lean statement against the book's text. Missing hypotheses (algebraic closure, field characteristic, orientation constraints, **finiteness/Artinian**) are a recurring source of wasted proof attempts. If the proof fails at a fundamental level after 1 attempt, suspect a statement bug before trying alternative tactics. **Missing-finiteness is the classic trap for statement-pass items that assert a *bijection/equivalence between two structures* (`Nonempty (X ≃ Y)`, `card X = card Y`) over a general `[Ring R]`** — Chapter 9's book results silently assume a finite-dimensional algebra over a field, but the pipeline's statement-pass often drops that to `[Ring R] [Small.{v} R]`, and the correspondence then fails on an infinite-dimensional witness. Concretely (#6581 part (i) → #6590): `blocks_equiv_indecomposableCentralIdempotents : Nonempty (Etingof.Block R ≃ {e // IsIndecomposableCentralIdempotent R e})` is **false for `R = ℤ`** — the simple ℤ-modules ℤ/p are pairwise unlinked (`Ext¹_ℤ(ℤ/p,ℤ/q)=0`, p≠q), so `Etingof.Block ℤ` is infinite (one block per prime), while `1` is the only indecomposable central idempotent of ℤ, giving `Nonempty (infinite ≃ singleton) = False`. Before proving any block/idempotent/Wedderburn-flavored equivalence, test `ℤ` (or `k[x]`) as an infinite-dimensional counterexample; if it breaks, the fix is `[IsArtinianRing R]` / `[Field k] [Algebra k A] [FiniteDimensional k A]`, and you report + decompose (per "Definition seems wrong: don't silently work around bad definitions") rather than grinding.

4. **Estimate your context budget.** Difficulty 3/3 proofs consume 60-80% of a context window on average. If you're already past the midpoint of your session, consider claiming an easier item instead. Partial progress on a hard proof with no commit is worth zero — a completed easy proof is worth one sorry removed.

5. **Check dependency readiness.** Verify that imports compile and key helper lemmas are sorry-free (or that sorry'd helpers won't block your proof). Use `lake build <module>` for the specific file. **A "closed/merged" dependency can still fail to compile.** A `.lean` file absent from its `ChapterN.lean` aggregator is never built by CI, so it rots silently when an upstream lemma it cites changes signature. Before consuming a cited dependency, `grep "ChapterN.Module" EtingofRepresentationTheory/ChapterN.lean` to confirm it is in the build graph, then `lake build` that exact module — do not trust that #closed ⟹ compiles. **And when you create a new file, add it to the `ChapterN.lean` aggregator in the same PR** (otherwise it will not be CI-checked and the next signature change will break it undetected). Concretely (#4695): `KernelLemmaK.lean` (the #4694 kernel-lemma assembly) was never in the aggregator and had stopped compiling against the corrected `kernelLemmaK'`; the fix had to be made before the assembly could even be attempted. Note also: when wiring a low-level file (e.g. a localization stack) back into a higher-level one, watch for `import` cycles — if file `A` imports `B` only for one small lemma, relocate that lemma to a leaf (Mathlib-only) file imported by both, rather than creating the cycle. **A specific recurring trap for "discharge the sorry at `File.lean:L`" issues: the machinery you need may sit *downstream* of the statement file and transitively import it.** This pipeline creates statement files early and proves the machinery in later files, so the engine often imports the very file holding the sorry. Before assuming you can `import` the machinery into the statement file, compute the closure (small Python DFS over `import EtingofRepresentationTheory.…` lines) and check whether the statement file is in it. When it is, the importing edges are frequently **doc-comment-only** (`grep -nE "<defined-ident>" Importer.lean` shows hits only in `/-! … -/`): delete those stale imports to break the cycle (verify the importers still build). Diagnosed in #5478/#5488: `PolynomialGLDecomposition` reached `Theorem5_23_2` only via `CauchyDetQuotient` and `SchurModuleSpecialBlock`, both comment-only. **But when the downstream file genuinely *uses* the statement file (a real import edge, not comment-only), you cannot break the cycle — instead relocate the theorem itself into the downstream file, keeping its fully-qualified name unchanged (nothing outside its own file references it, so the name is all that matters), and leave a one-line pointer comment where it was.** Diagnosed in #7290: `Problem4_12_10_symmetric`'s proof needs `exists_orbitEval_surjection` from `Problem4_12_10_OrbitEval.lean`, which really imports `Problem4_12_10_Symmetric.lean` for `symPowRep`; the theorem moved into OrbitEval. The issue's "file field" naming the statement file is then just wrong about placement — the `#print axioms <FQN>` check still passes after the move, so don't fight to keep it in the named file.

   Use `set -o pipefail` when piping `lake build` through `tee`/`tail` — otherwise the pipeline's exit code is `tee`'s `0` and a real build failure reads as success. **For "mechanical glue"/aggregation issues, also audit that the *generality* of every input lemma matches the goal — closed/merged ≠ usable.** An issue can have all its named dependencies merged yet still be unwritable because the inputs are proved at a narrower generality than the target. Concretely (#2708, Schur-Weyl C-4a): the goal `schurModuleSubmodule_isSimple_centralizer` is over a generic alg-closed CharZero field `k`, but every per-block input it must feed (`trace_symGroupAction_eq_spechtModuleCharacter`:1029, `youngSym_action_vanishes_off_block`:2158, `youngSym_action_on_special_block_rank_one_scaled_proj`:2279) is hardcoded to `ℂ`, and generic `k` does not base-change from `ℂ`. `grep` the input lemmas' signatures for the field type before claiming. If they are `ℂ`-only while the goal is generic, the issue is mis-scoped: `coordination skip` to `replan` with the two paths (specialize the goal to `ℂ` — usually correct when the rest of that chapter's backbone is `ℂ`-only and nothing consumes the generic statement; or first generalize the inputs to generic `k`). Do not rewrite the goal's generality unilaterally.

6. **Code the framework before deep analysis.** When a proof has an obvious high-level structure (e.g., "use Schur's lemma + nonvanishing"), code that framework with sorry placeholders within the first 15 minutes. Don't spend the majority of your session analyzing whether the hard step is provable before writing any Lean. The framework commit has value even if the hard sorry remains — it reduces the problem for future agents. Deep mathematical analysis should happen AFTER the framework compiles, focused on the specific sorry goals.

## Endgame Protocol (≥99% Sorry-Free)

When the project is near completion (581/583 items sorry-free as of Wave 49), the remaining sorries are qualitatively different — they're the hardest problems, not low-hanging fruit. Agents must adjust their approach.

### Definition Audit Before Proof Attempts

**When a proof is stuck after 2 attempts, audit the definition against the textbook BEFORE trying more proof approaches.**

The polytabloid definition was non-standard (T-dependent form `κ_T · of(τ) · a_λ` instead of standard `of(τ) · c_λ`). This caused **4+ agent sessions** of wasted work across multiple waves. Once the definition was refactored to match the textbook, 3 sorries were eliminated trivially.

**Checklist when stuck:**
1. Read the blob file for the relevant definition
2. Compare the Lean definition's structure against the book's mathematical definition
3. Check: does the Lean definition use the same decomposition/factoring as the book?
4. If not, consider whether a definition refactoring would simplify the proof
5. A definition refactoring that makes proofs trivial is MORE valuable than a clever proof of a bad definition

### Counterexample-First Verification

Before investing a full session in a hard proof, spend 5-10 minutes checking the statement is correct:

1. **Instantiate with concrete examples.** If the theorem is about all graphs with property P, check P for the simplest non-trivial case.
1b. **A *fixed* signature handed down by a planner can itself be under-hypothesized — test it before proving.** Instantiate the degenerate case (set the algebras/rings to the base field, modules to trivial or free) and compare both sides by hand; a missing finiteness hypothesis often only shows up there. Worked example (#6803, Problem 8.2.8 Ext Künneth): the signature required only `Nᵢ` finite-dimensional, but at `A₁=A₂=k`, `Nᵢ=k`, `Mᵢ` infinite-dimensional the natural map `M₁*⊗M₂* → (M₁⊗M₂)*` is a proper injection, so the *mandated* proof route (finite-dim Hom-tensor iso + field Künneth, which yields a **natural** iso) cannot prove it — `Mᵢ` must be finite-dimensional (or FP∞ / f.g. over Noetherian `A`) too. **Watch the conclusion's strength:** a `Nonempty (_ ≃+ _)` / `Nonempty (_ ≅ _)` *existential* iso is much weaker than a natural one — it can be true by cardinality/dimension coincidence even when the natural map is not an iso, so a counterexample to naturality does NOT strictly refute it, yet it is still unprovable by the intended route and weaker than the book. When the fixed statement is ill-posed this way, `coordination skip … "reason"` to `replan` with the counterexample + the finiteness fix + a strengthened (k-linear/natural) conclusion — do not silently change a fixed signature or grind on an unprovable statement (matches the "definition/statement seems wrong" escalation).
2. **Check boundary cases.** The hypothesis `h_dim : Module.finrank k M = Module.finrank k (SchurModule k N lam)` was added to `iso_of_formalCharacter_eq_schurPoly` after discovering a counterexample: `M = SchurModule ⊕ det⁻¹`. **`formalCharacter` is a *truncated* invariant — it records only `ℕ`-valued weight spaces and is blind to `det`-twists — so it is NOT a complete invariant, and SIMPLICITY does not rescue it.** Any lemma deriving "`M` is polynomial" (`⨆ μ, glWeightSpace = ⊤`) or "`M ≅ L_λ`" from `IsSimpleModule` + `formalCharacter M = schurPoly N lam` *alone* is **false** (#4948): counterexample `M = det⁻¹ ⊗ Sym³(std)`, `N=2` — simple, 4-dim, `formalCharacter = x₁+x₂ = schurPoly 2 (1,0)` (the `(-1,-1)` shift sends `(3,0),(2,1),(1,2),(0,3) ↦ (2,-1),(1,0),(0,1),(-1,2)`, only `(1,0),(0,1) ∈ ℕ²` survive) yet ℕ-weight spaces span only 2 of 4 dims and `M ≇ std`. Polynomiality must be a **threaded hypothesis** (`hLtop : ⨆ μ, glWeightSpace = ⊤`), discharged from the rep's actual polynomial source (e.g. transport `M`'s `h_span` to a simple summand `L` across the equivariant iso via `glWeightSpace_map_eq_of_rep_iso` + `Submodule.map_iSup`), never manufactured from simplicity. When a planner decomposes a hard theorem into "isolated `sorry` ingredients", an ingredient can itself be *unsound* — verify each ingredient is TRUE (seek a counterexample) before grinding on its proof. **Tactic gotcha (weight-space dim work):** `rw` of a submodule-valued subterm sitting *under* `Module.finrank` (e.g. `rw [glWeightSpace_eq_glWeightSpaceℤ …]` or `glWeightSpaceℤ_charTwist_shift` inside `finrank k (glWeightSpace …)`) fails with **`motive is not type correct`** — the `[Module k ↥S]` instance can't be abstracted over the rewritten `S`. Fix: prove the *submodule* equality `S = T` first (rewrites there are fine), then bridge to the ℕ-level finrank equation with a `congrArg` helper `congrArg (fun U : Submodule k V => Module.finrank k U) (h : S = T) : finrank k S = finrank k T` (and `rw` *that*). The `p`-fold det-twist character formula `formalCharacter_charTwist_detChar_pow` (`AlgIrrepGLNonIso.lean`, induction via `formalCharacter_shift_of_weightSpace_finrank`) is a worked example.
3. **If two "different" accounts/objects produce suspiciously similar data, investigate.**
4. **Indecomposability of explicit affine-Dynkin reps: build a small decomposition first.** The Ch6 `*Rep_kQ_isIndecomposable` family (D̃/Ẽ/T(p,q,r), orientation-generic) is built from a single nilpotent twist `N`, which is **too weakly coupled** and yields *decomposable* reps. Already refuted for the sporadic cases (Ẽ₆/Ẽ₇/T(1,2,5), #4548, `progress/indecomposability-framework-investigation.md`) and for the D̃ family in **reversed-leaf** orientations (D̃₄ #4523 → #4566: explicit `m=1` complementary pair). The needed fix is the homogeneous-tube redesign, not a cleverer proof. Before claiming any open `d5/d6/d7/d8/dTilde/etilde/t125 *_kQ_isIndecomposable` issue, check #4566/#4548 — most are likely still false. A reversed leaf removes the coupling its forward edge supplied, so test a reversed orientation at `m=1` for `span`-level decompositions. (Note: the canonical all-sink D̃₄ `starRepGen_isIndecomposable` is genuinely indecomposable — only the orientation-generic statements are at risk.) **This also refutes the `*_kQ_leaf_equalities` sub-lemmas** (e.g. #2853, and the d6/d7/d8 analogs) that feed those `_isIndecomposable` theorems: the *mixed* orientations (one leaf pushed, one pulled at a shared center) force only an M-twisted relation `M(W⟨leaf⟩) = W⟨other⟩` with `M = (I−N)⁻¹` (derivable via `linearEquiv_invariant_isCompl_symm_mem` + `gammaInv_embed_general_F` + the v=2 `core_F`), and no edge supplies the leaf N-invariance needed to untwist it — so leaf equality is *false* there (D̃₅ m=1: `W⟨0⟩=span{(1,1)}`, forced `W⟨5⟩=(I−N)W⟨0⟩=span{(0,1)}`). Don't grind on a `_leaf_equalities` issue over arbitrary orientations; only the all-canonical and all-leaves-reversed branches are provable. **To land a sorry-free `_leaf_equalities`, restrict the statement rather than leaving bare sorries (#4743 for D̃₅):** add explicit Hom-direction hypotheses to the signature (`hc02/hc12/hc23 : Nonempty (@Quiver.Hom (Fin n) Q ⟨a⟩ ⟨b⟩)` pinning each canonical edge, plus a same-direction `Iff` for the two shared-center leaves, e.g. `hv3 : Nonempty (Hom 4 3) ↔ Nonempty (Hom 5 3)`), then discharge every off-restriction `rcases hOrient_edge` branch with `(hOrient.2.2 i j h_canonical h_reversed).elim` — `IsOrientationOf`'s third conjunct (`OrientationDefs.lean:41`) is exactly the antisymmetry "no arrows both ways". This keeps the existing case tree intact; only the previously-`sorry` leaves change to one-line contradictions (minimal diff). If the lemma is consumed generically (e.g. by `_isIndecomposable`, which only uses it in its all-canonical branch), **move the call into the branch that can supply the hypotheses** — there the canonical arrows give `⟨a02⟩ ⟨a12⟩ ⟨a23⟩` and same-direction `v3` leaves give `iff_of_true ⟨a43⟩ ⟨a53⟩`. Reusable across the open D̃₆/₇ leaf_equalities (#4722/#4689). **Construction tip for the homogeneous-tube `def` (sub-A of each shape, e.g. `t125Rep_kQ` #4559 mirroring `etilde7Rep_kQ` #4568):** the `*RepMap_kQ` match must produce `(Fin (*Dim m a) → F) →ₗ (Fin (*Dim m b) → F)`, and the leaf vertex has dimension `m+1` (not `1*(m+1)`) in `*Dim`. Since `1*(m+1)` is **not** defeq to `m+1`, the `a=1` block maps (`suffixBlockEmbed_F F 1 2`, `prefixBlockEmbed_F F 1 _`) fail to typecheck at the leaf — use `starEmbed2_F`/`starSecond_F` (suffix) or `starEmbed1_F`/`starFirst_F` (prefix), which produce the bare `Fin (m+1)` shape. The `2…6`-coefficient block maps are fine. To extract `>2` input blocks for a wide eigenvalue arm (T(1,2,5)'s arm 1 is `F^{3(m+1)}`), the fixed-`N` `blockEmbedAt_F` won't fit; use the general `blockEmbedAtN_F`/`blockProjAtN_F` (`FieldGenericT125.lean`, target dim a raw `ℕ`). **3-arm tube caveat (Ẽ₆/T(p,q,r), #4638): even the *all-canonical* "three leaf subspaces equal `W⟨leaf_i⟩` all equal" collapse is circular and NOT a usable stepping stone** — unlike D̃₄ where each arm's diagonal embed hits *both* center blocks (so `compl_le_forces_eq` gives `W⟨leaf⟩=W⟨1⟩=W⟨2⟩` for any pair), each tube arm embeds its leaf line into only 2 of the ≥3 center blocks. The proven membership criteria (`etilde6_arm{A,B,C}_criterion`, `FieldGenericETilde6.lean`) give `x∈W₁⟨2⟩ ↔ (0,x,x)∈W₁⟨0⟩`, `x∈W₁⟨4⟩ ↔ (x,0,x)∈W₁⟨0⟩`; the inclusion `W₁⟨2⟩≤W₁⟨4⟩` that `compl_le_forces_eq` needs is `(0,x,x)∈W₁⟨0⟩ ⟹ (x,0,x)∈W₁⟨0⟩`, **false** for general `W₁⟨0⟩` (e.g. `⟨(0,1,1)⟩`). Leaf-equality holds only because the surviving pairs are trivial — i.e. it is a *corollary* of indecomposability, not a route to it. The correct route (sub-C assembly) is the §3 **brick contradiction** consuming the criteria + `etilde6_arm*_plane_split` (each plane `π_i=(W₁⟨0⟩⊓π_i)⊕(W₂⟨0⟩⊓π_i)`) + the eigenvalue site, concluding `W₁⟨0⟩∈{⊥,⊤}` directly. **Once a shape's corrected homogeneous-tube `def` lands, its `_isIndecomposable` flips from false to TRUE — stop trying to refute it.** Scope construction and proof as *separate* deliverables (the ETilde6/7 + D̃₄ pattern): the `*Rep_kQ` def gains an explicit `(lam : F)` parameter with the fourth/eigenvalue arm = `starEmbedTube_F F lam m` (`λ•id + J`, a *square* Jordan block — relocated into `FieldGenericStar.lean`, #4648), the `*_not_finite_type_per_kQ` consumer fixes `lam = 1`, and the orientation-generic `_isIndecomposable` proof is sorried "for every lam", **deferred to a shared family-wide center-crux wall** (open across D̃₄ #4674 / D̃₅–D̃₈ / Ẽ₆ `etilde6Rep_kQ_isIndecomposable` / Ẽ₇). The worked canonical-orientation proof `starTubeRepGen_isIndecomposable` (`FieldGenericTube.lean`) + the leaf reductions `forward_leaf_subspace_eq`/`reversed_leaf_subspace_eq` + the center lemma `eigenvalue_jordan_invariant_compl_trivial_gen` are the assembly pieces. So: don't re-investigate whether these are tractable as one unit, and don't refute a shape whose corrected tube already landed — check the construction's arm map first.

5. **"Follows via Schur's lemma / character matching" can be circular — check the nonzero-hom prerequisite.** When an issue claims a decomposition/iso "follows by Schur's lemma" from two reps being simple, remember Schur's lemma (`finrank_hom_simple_simple`) only gives `Hom ∈ {0,1}`-dim; concluding *iso* needs a **nonzero** equivariant map, which usually presupposes the very character/highest-weight match being sought. Example (#2493): identifying the abstract Schur-Weyl summand `Lᵢ` with `SchurModule k N λ` was claimed to follow from `Lᵢ` simple (C-3) + `SchurModule` simple (C-4) + Schur's lemma, but that route is circular — it needs `char(Lᵢ) = schurPoly N λ` (the highest-weight classification, downstream #2482/#2483) to produce the nonzero map. The character-level assembly (`formalCharacter(V^⊗n) = ∑_λ dim(Sλ)·sλ`) is reachable from C-1∘C-2; the concrete-module iso is not. Land the reachable character identity and route the classification gap to the downstream issue rather than forcing a circular "Schur's lemma" proof. Also: do not "rescue" such an iso with a pure `finrank`-equality `≃ₗ[k]` — it type-checks but is mathematically vacuous (any equal-dimension spaces are k-linearly isomorphic), violating the no-vacuous-theorems principle.
6. **"Vanishes pointwise" lemmas about an element already known to lie in a span are usually false — refute by direct computation.** A lemma claiming an explicit element has *zero coefficient* at certain basis points (e.g. a residual `Δ`'s coefficient at tabloids with no column-standard rep, Ch5 Wall 3 R2.b.i #2769) is suspicious whenever the true reason `Δ` sits in the target span `V` is **global** rather than pointwise. If `Δ` equals a single polytabloid `±ψ_τ` (τ col-standard), it carries `±1` at *every* column-class of τ — including non-standardizable ones — so pointwise vanishing fails even though `Δ ∈ V` holds. Brute-force the smallest example by replicating the Lean definitional conventions exactly (`toTabloid` = entry→row map, `ColumnSubgroup`, `tabloidStrictDominates`, signed-polytabloid form of the construction), and **validate your model reproduces a known ground truth** (e.g. the design note's hand-computed values) before trusting a refutation. This refuted #2769 in minutes (`progress/r2bi-counterexample-check.py`, redesign tracked in #4584). **A hand-checked *confirmation* is no safer than a hand-checked refutation — brute-force both directions.** A prior meditate note (#2776, `progress/r3-bis-residual-cancellation.md` §3) claimed the *same* statement was TRUE via a cross-region involution, "validated on the running example; sign reversal verified" — the faithful brute force refuted it on that very example. When you assert a tricky combinatorial identity *holds*, run the script; never ship "verified by hand". And refuting the lemma does not refute the goal: the global span-membership a dead pointwise route was serving is often still true by a *direct* identification (here `Δ = ±ψ_τ`, discharged by the existing `(srRank, rowInvCount')` induction — see `progress/r2b-redesign-direct-polytabloid.md`). Also beware the inverse circularity trap: a "straightening" lemma that *consumes* `v ∈ V` as a hypothesis (e.g. `tabloidSupport_straightening`) cannot be the route that *establishes* `v ∈ V`; and a design note claiming a proof is "just re-packaging the internals of lemma X" is circular whenever X takes the goal as a hypothesis — check before adopting the plan. **When your validation script tests a *measure/ordering* condition (e.g. `srRank τ' < srRank σ`, IH-availability, dominance), pin the measure's DIRECTION to the codebase definition before trusting PASS/FAIL.** A flipped sign silently inverts the verdict: here `srRank σ = #{τ : σ strictly dominates τ}` counts tabloids *below* σ, so a tabloid dominated by σ has *smaller* srRank (IH-available) — an early script that counted tabloids *above* spuriously reported every constituent "above σ" and nearly condemned a sound route (Ch5 R2.b #4593, validated route → #4604/#4605). Re-derive one row by hand against the Lean `def` before reading the table.

7. **Character / multiplicity identities: dimension-count both sides (evaluate at all-ones) before attempting.** Any claimed `formalCharacter M = ∑_λ (coeff_λ)·S_λ` must match in *total dimension*: setting every torus variable to `1` makes each `S_λ` evaluate to `dim V_λ = s_λ(1,…,1)` and the LHS to `dim M`. This is a 30-second check that catches multiplicity errors instantly. It refuted #4944: `polyRightDegreeFDRep_formalCharacter` claimed the degree-`d` part `A_d` of `k[Xᵢⱼ]` had a *multiplicity-one* decomposition `formalCharacter k N A_d = ∑_{ν : BoundedPartition N d} schurPoly N ν.parts`, but for `N=2, d=1`, `dim A_1 = 4` (the four `Xᵢⱼ`) while `∑_ν dim V_ν = dim V_{(1,0)} = 2` — unequal, so false. The actual right-`GL_N` multiplicity is `dim S_ν(k^N) = s_ν(1,…,1)` (the left Schur-factor of the GL×GL Cauchy bi-rep `Sym^d(V⊗W) = ⊕_ν S_ν(V)⊗S_ν(W)`), **not** one. The fix is to correct the statement to the multiplicity-bearing form `∑_ν (eval 1 (schurPoly N ν.parts)) • schurPoly N ν.parts` (Cauchy at `x=1^N`) — and since a sorried *false* theorem is a landmine even unused, correct it openly (per "Definition seems wrong: don't silently work around bad definitions") rather than leaving it. Watch for "multiplicity one" / "each ν exactly once" claims about a *forgetful restriction* of a bi-representation: forgetting one factor of `V_λ ⊠ V_λ` leaves `dim V_λ` copies, never one (except `dim V_λ = 1`, i.e. powers of `det`). The qualitative *support* conclusion a consumer wants (e.g. "constituents of `A/det` have `ν_N = 0`") usually survives the multiplicity correction (the `dim V_{ν-(1,…,1)} = dim V_ν` factors cancel termwise), so re-spec the proof, don't abandon the consumer.

8. **A character table is NOT formalized by asserting orthonormality of hand-typed rows — that is vacuous.** Encoding the table as an explicit `chi : Fin r → Fin r → ℂ` (or `Q5`) and proving the rows are orthonormal + "the group has `r` conjugacy classes" does **not** pin down the table: a continuum of orthonormal `r`-frames satisfy it, and nothing connects the rows to actual representations — the claim "these are the irreducible characters" then lives only in the docstring. This sank Example 4.8.1's first fix (#5418 reopened → decomposed into #5428–#5431). The non-vacuous bar: build each row as the **trace of an honest representation** — construct `V : FDRep ℂ G` (from a real `Representation`/`MonoidHom`), prove `V.character g` equals the tabulated value at each class representative, prove `V` is `Simple` via `FDRep.simple_iff_char_is_norm_one` (`FinGroupCharZero.lean`: `Simple V ↔ ∑ g, χ(g)·χ(g⁻¹) = Nat.card G`, over an alg-closed char-0 field — so work over ℂ, which also carries `√5` etc.), prove the rows are pairwise non-isomorphic (distinct characters / `FDRep.char_orthonormal`), and conclude completeness from "`r` distinct simples + `r` conjugacy classes". The same critique applies to any "tensor multiplicity" or "decomposition" table built on the orthonormality-only certificate (e.g. Example 4.9.1 uses the identical `Q5` + `*_orthonormal` pattern and is a likely repeat flag). Also: the `native_decide` used to discharge those orthonormality sums and the `Fintype.card (ConjClasses G) = r` counts is a **forbidden trust hole** — evaluate character inner-product sums over `G` via a class-function decomposition `∑ g = ∑ class c, |c|·f(rep c)`, not `native_decide`.

9. **A book formula ported verbatim into `ℕ` is silently FALSE at a boundary when it contains subtraction — plug in the degenerate case before proving.** Truncated `ℕ`-subtraction makes `a - b` collapse to `0` (or the formula to a wrong constant) exactly where the mathematics wants a negative/zero index. Problem 2.8.11(a) #6267: the stated coefficient `C(n + m - 1, m - 1)` (dimension of the degree-`n` piece of `k[x₁..x_m]`) is correct for `m ≥ 1` but at `m = 0` becomes `C(n - 1, 0) = 1` for *every* `n`, whereas `k[]` ≅ `k` is concentrated in degree `0` (dim `1` at `n=0`, else `0`) — so both the finrank theorem and the power-series identity `(1-X)^m·h = 1` are false at `m=0`. Fix: use the equal-for-`m≥1`, boundary-correct form `C(n + m - 1, n)` (= `Nat.multichoose m n`), which is exactly what `Finset.card_finsuppAntidiag_nat_eq_choose` (`#(univ.finsuppAntidiag n) = (#s + n - 1).choose n`) produces and what makes the identity hold for all `m` including `0`. Correct the statement openly (docstring the choice) rather than adding an `m ≥ 1` hypothesis that silently drops the degenerate case. **Reusable API for "dim of degree-`n` homogeneous piece = # monomials":** `homogeneousSubmodule = restrictSupport {d | d.degree = n}` (`homogeneousSubmodule_eq_finsupp_supported`), which has monomial basis `MvPolynomial.basisRestrictSupport`; then `Module.finrank_eq_nat_card_basis` + `Nat.card_coe_set_eq` + `Set.ncard_coe_finset` reduces `finrank` to the antidiag `Finset.card`. **Power-series `(1-X)^m·(∑ C(n+m-1,n) tⁿ) = 1`:** it *is* `PowerSeries.invOneSubPow k m` — use `.inv_val` + `invOneSubPow_inv_eq_one_sub_pow` + `invOneSubPow_val_succ_eq_mk_add_choose`, match coefficients `C(d+n,d)=C(n+(d+1)-1,n)` via `Nat.choose_symm`, and handle `m=0` directly with `PowerSeries.ext`. Worked example: `Chapter2/Problem2_8_11.lean` (`finrank_homogeneous_mvPolynomial`, `hilbertSeries_mvPolynomial`).

**Genuine tensor-multiplicity tables: prove the character identity, don't chase a tensor-product iso (Example 4.9.1 `S₃` — DONE, #5377, `Chapter4/Example4_9_1.lean`).** The non-vacuous form of a Clebsch-Gordan table `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` is the **character identity** `χ_i(g)·χ_j(g) = Σ_k n_{ij}^k χ_k(g)` proved from real reps — you need neither the module iso nor `CharEqIso` (which lives in Ch5, unimportable from Ch4). Recipe: build the irreducibles as `FDRep ℂ G` and get each character as a *closed-form trace* (for `S₃ = Equiv.Perm (Fin 3)`: trivial `= 1`, sign `= (Equiv.Perm.sign g : ℂ)` via `charRep`, standard `= #fix(g) − 1` via the sum-zero subrep of the permutation rep — rebuild the sorry-free Ch5 `Discussion5_11_examples` `permRep`/`stdSub`/`stdRep_character` locally since Ch5 imports Ch4). The whole table then collapses to a polynomial identity in those closed forms, and the *only* group-specific input is one decidable fact `∀ g, (sign g, #fix g) ∈ {finite class values}` proved by `revert g; decide` (do NOT state it for a fixed `g` — that is not decidable). Proof shape: `simp only [irrep_char, Fin.sum_univ_three]; fin_cases i <;> fin_cases j <;> simp only [<matrix-cons lemmas>, Fin.isValue] <;> rcases <class-cases> g <;> rw [<sign-coe>, hs, hf]; push_cast; ring`. Bridge to genuine tensor products with `FDRep.char_tensor (V W) : (V ⊗ W).character = V.character * W.character` + `Pi.mul_apply` (needs `open CategoryTheory MonoidalCategory`). Axiom-clean, no `native_decide`. `S₄`/`A₅` follow the same pattern (#5442/#5443); `A₅` additionally needs the two 3-dim icosahedral reps with golden-ratio values over `ℚ(√5)`. **`A₅` DONE (#5776, PR #5846, same file):** reuse the genuine catalogue `Etingof.Example4_8_1.A5.irrepA5` (= `![repTriv, repC3plus, repC3minus, repC4, repC5]`) + its class-rep character values `irrepA5_character_book` (over `Q5 = ℚ(√5)`) verbatim — `import EtingofRepresentationTheory.Chapter4.Example4_8_1` (no cycle; 4_8_1 imports only Mathlib). Two lessons that cost real time:
  - **Do the golden-ratio arithmetic in `Q5`, NOT `ℂ`.** `A₅`'s characters are class functions, so `χ_i(g) = Q5toC (chiA5 i (classIdxA5 g))` (via `classIdxA5_spec` + `FDRep.char_conj`); the tensor identity then reduces to a `5·5·5` case split over the classes. Closing that split directly over `ℂ` with `push_cast <;> (first | ring | linear_combination …·sqrt5_sq)` ran **44 minutes then crashed** — the `first` backtracking runs `ring` over `ℂ`-with-`√5` under a bumped heartbeat budget, ×125. Instead prove the identity in `Q5` (`chiA5 i j * chiA5 i' j = Σ q5Nat(n)·chiA5 k j`), where `√5²=5` is baked into `Q5.mul`, so each case is pure rational `norm_num` on `re`/`im` (no `√5`, no `ℂ`); then transport to `ℂ` once via a hand-proved ring-hom lemma `Q5toC_mul (a b) : Q5toC (a*b) = Q5toC a * Q5toC b` (`simp [Q5.mul_re, Q5.mul_im]; push_cast; linear_combination (-(a.im*b.im))*sqrt5_sq`) plus the existing `Q5toC_add`. Whole file drops to ~4 min. `Q5` has `Mul/Add/Neg/Zero/One/OfNat` but **no `CommRing`/`NatCast`/`AddCommMonoid`** — so no `Finset.sum`/`•`/`map_sum` over `Q5`; write the RHS as an explicit `Fin.sum_univ_five` of `q5Nat n * chiA5 k j` with `q5Nat n := ⟨(n:ℚ),0⟩`.
  - **`FDRep.char_conj V g h : V.character (h*g*h⁻¹) = V.character g` — rewrite the character *argument* only.** To turn `χ(g)` into `χ(classRep (classIdx g))` given `hc : c * classRep (classIdx g) * c⁻¹ = g`, a bare `rw [← hc]` **also rewrites the `g` inside `classIdx g`** on the RHS, corrupting the goal. Localise it: `have key : χ g = χ (classRep (classIdx g)) := by rw [← FDRep.char_conj V (classRep (classIdx g)) c, hc]` (the `←` targets the standalone `χ (classRep …)`, then `hc` collapses `c*·*c⁻¹` to `g`).
  - **Kernel `decide` memory OOMs CI — reduce group sums to class sums BEFORE deciding, and split big files (#5852, PR #5854).** A single `decide` of a 60×60 = 3600-term character double sum under `maxHeartbeats 2000000000` cost ~12 GB of kernel memory and OOM-killed the 16 GB CI runner for two days (`zEnd_cube_trace`); heartbeats bound *time*, not *memory*, so a "just raise the budget" decide can pass locally and still kill CI. If you find yourself raising `maxHeartbeats` past ~4·10⁶ for a `decide`, restructure instead: (a) any conjugation-invariant summand (characters, `fixCardM`, `tr(z·ρ(·))` for central `z`) collapses `∑ g : A₅` to the 5 class representatives weighted by `classIdxA5_card` sizes — the abstract pieces are `S4.fixCardM_conj`, `A5.sum_fixCard_classfn`, and the centrality+trace-cyclicity argument in `zEnd_cube_trace`; the kernel then only ever evaluates 5 (not 60, not 3600) terms. (b) Elaboration memory **ratchets across a file** (~13 GB cumulative for the old 2755-line `Example4_8_1.lean` even after (a)) — split into chained modules so each lean process peaks lower (now `Example4_8_1/{Q8,S4,A5Classes,A5Reps,A5Lambda2,A5Golden}.lean` + umbrella, peaks 5.6–9.7 GB; measure with `ps -o rss=` sampling during `lake build`). Chained imports also serialize the heavy modules in CI, so their peaks never stack. Micro-splitting one `decide` via `fin_cases i <;> (revert g; decide)` does NOT reduce peak (the elaborator still evaluates every column in one declaration) — don't bother.

This saved 2+ sessions in Waves 47-49 by catching false statements early, an entire D̃₄ proof attempt (#4566), a Ch5 Wall 3 R2.b.i attempt against a false pointwise-vanishing residual lemma (#2769 → #4584), and a research-level Cauchy proof attempt against a false multiplicity-one character identity (#4944).

**Worked recipe for genuine small-group character tables (Example 4.8.1 family — #5428 done for Q₈, #5429 S₄, #5430 A₅ triv/ℂ⁴/ℂ⁵).** The `Q₈` table is sorry-free, `native_decide`-free, and axiom-clean (`propext/Classical.choice/Quot.sound` only) in `Chapter4/Example4_8_1.lean` (namespace `Etingof.Example4_8_1.Q8`). The 1-dim, sign, permutation-derived (`stdRepM` deleted-perm), and tensor-twist rows of `Q₈`/`S₄`/`A₅` all follow the identical explicit-construction moves below — **but the remaining #5431 (decomposed into #5449/#5450) does NOT, and the explicit-matrix moves are the wrong tool there:**
- **The two 3-dim `A₅` icosahedral reps `ℂ³₊`/`ℂ³₋` (golden-ratio `χ`) cannot be built as explicit-matrix `MonoidHom`s out of `alternatingGroup (Fin 5)`.** `map_mul` over 60 elements is infeasible by `decide` (even over the `DecidableEq` ring `Q5 = ℚ[√5]`), and the algebraic route would need `PresentedGroup {a⁵,b²,(ab)³} ≃* A₅` (the (2,3,5) von Dyck group has order 60 — Todd–Coxeter), which is **not in Mathlib**. The only feasible rigorous route is the **central-element eigenspace of `Λ²(ℂ⁴)`**: `Λ²(ℂ⁴) ≅ ℂ³₊ ⊕ ℂ³₋`, and `z = Σ_{c∈C} ρ(c)` (one 5-cycle class, 12 elts) acts as `4φ`/`4φ'` (min poly `X²−4X−16`), so each rep is an eigenspace-`Subrepresentation`, with character via the projector `(z−4φ'·id)/(4√5)` and `LinearMap.trace_eq_sum_trace_restrict`. Heavy but uses existing infra (`FDRep.char_tensor` in `Discussion_4_4.lean`, `Subrepresentation`, `Module.End.eigenspace`, `S4.fixCardM`). Do not attempt explicit matrices here. **Phase A landed (#5449 → PR #5454):** `Λ²(ℂ⁴)` is now a genuine `FDRep` `Etingof.Example4_8_1.A5.lam2` (= `range asym ⊆ repC4 ⊗ repC4`, `asym = ½(1−β)` the antisymmetriser), with `lam2_char_formula : lam2.character g = ½(repC4.character g ^2 − repC4.character (g*g))` and `lam2_character : … (classRepA5 j) = ![6,0,-2,1,1] j`, axiom-clean (no `native_decide`). The remaining eigenspace split (`z = Σ_{c∈C} lam2.ρ c` → `ℂ³₊`/`ℂ³₋`) is **#5453**: consume `lam2`/`lam2_character`, do NOT rebuild the exterior square. Two reusable lessons from Phase A: (a) the **swap-trace identity** `trace(swap ∘ map A B) = trace(A∘B)` is copyable from `Chapter5/FrobeniusSchurRealType.lean` (`trace_comm_comp_map`) specialised to ℂ (Ch4 cannot import Ch5); the antisymmetric-subrep character then comes from two `LinearMap.trace_eq_sum_trace_restrict` over the `±1`-eigenspaces of `β` (the `β = ∓1` on `range a`/`ker a` facts close by `linear_combination`/`module` after `LinearMap.smul_apply`+`LinearMap.sub_apply`+`Module.End.one_apply`). (b) **The idempotent-projection lemmas are in `namespace LinearMap`** — write `LinearMap.IsIdempotentElem.isCompl asym_idem` / `LinearMap.IsIdempotentElem.mem_range_iff asym_idem` (bare `asym_idem.isCompl`/`.mem_range_iff` fail: `IsIdempotentElem p` unfolds to the `Eq` `p*p=p`, so dot-notation resolves to `Eq.*`). Feed the `IsCompl (range a) (ker a)` to `DirectSum.isInternal_submodule_iff_isCompl ![range a, ker a] zero_ne_one huniv` for the `IsInternal` the trace lemma needs.
- **The "five simples + five conjugacy classes ⇒ complete table" certificate needs `#(irreducible FDRep ℂ G) = #(ConjClasses G)`, which Mathlib does NOT package** (`RepresentationTheory/` has `simple_iff_char_is_norm_one`, `char_orthonormal`, but no `ConjClasses`-count bridge) — this count theorem is exactly what the rejected `native_decide` orthonormality stood in for, and must be proven as reusable repo infra (or replaced by a decidable `IsCharacterTable` predicate).
- **Finiteness of the set of simple modules over a finite-dimensional algebra IS provable from Mathlib primitives — do NOT defer it as "missing infra" (#6090, landed as `Etingof.finite_simpleModuleClasses` in `Chapter4/Exercise4_2_3.lean`, sorry-free).** Goal shape: `Finite (SimpleModuleClasses.{u} R)` (iso classes of simple `R`-modules) for `R` finite-dim over a field `k`. Route, all from Mathlib: (a) `rad = Ring.jacobson R` annihilates every simple module — `IsSemisimpleModule.jacobson_le_annihilator R M` (a simple module is semisimple), giving `Module.IsTorsionBySet R M (Ring.jacobson R)`; (b) descend to the semisimple quotient `A = R ⧸ Ring.jacobson R` via `Module.IsTorsionBySet.module` (mark the descended `Module A M` `@[implicit_reducible]`, else "class type must be marked reducible"), and transfer simplicity with `LinearMap.isSimpleModule_iff_of_bijective` applied to the **identity semilinear map** `hM.semilinearMap` (its `map_smul'` is `rfl`, so `mk r • x = r • x` is definitional — this makes R-linear ⇄ A-linear equiv promotion/demotion trivial `{ e with map_smul' := fun a x => by obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a; exact e.map_smul r x }`); (c) `A` semisimple: `isArtinian_of_tower k inferInstance` → `IsArtinianRing R` → `IsSemiprimaryRing R` (Mathlib instance) whose `IsSemiprimaryRing.isSemisimpleRing` field gives `IsSemisimpleRing A` (no need to import `Chapter8/SemiprimaryAlgebra`); (d) over semisimple `A`, `Finite (isotypicComponents A A)` is a Mathlib instance (`Mathlib/RingTheory/SimpleModule/Isotypic.lean`, needs `IsNoetherian`), every simple embeds as an ideal (`IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`), and `⟦X⟧ ↦ isotypicComponent A A (descent of X)` is a **choice-free, injective** map into that finite type (well-defined & injective via `LinearEquiv.isotypicComponent_eq` + `IsIsotypicOfType.isotypicComponent` + `isIsotypicOfType_submodule_iff`). `Finite.of_injective` finishes — no `Shrink`/universe juggling. Reuse this for any Ch4/Ch9 count that first needs "finitely many simples". To lift a categorical `Iso` in `(simpleProp _).FullSubcategory` to/from a `LinearEquiv`: `(ObjectProperty.ι _).mapIso iso |>.toLinearEquiv` one way, `P.fullyFaithfulι.preimageIso e.toModuleIso` the other; and `attribute [local instance] CategoryTheory.isIsomorphicSetoid` is needed for `≈`/`Quotient.lift` since the setoid is passed explicitly in `SimpleModuleClasses`.
- **Jacobson-radical membership over a NONcommutative ring — do NOT reach for `Ideal.mem_jacobson_bot` (#6568, `Chapter3/Problem3_9_5.lean`, `not_isSemisimpleRing_of_degenerate`, sorry-free).** `Ideal.mem_jacobson_bot` (`x ∈ jacobson ⊥ ↔ ∀ y, IsUnit (x*y+1)`) and its siblings live in a `[CommRing R]` section; applying them to a noncommutative algebra (Clifford, path algebra, `U_q`) fails with a **misleading `failed to synthesize CommRing ?m` + `whnf` heartbeat timeout** that hides the real cause. Prove `a ∈ Ring.jacobson R` directly via the maximal-left-ideal characterization: `rw [Ring.jacobson_eq_sInf_isMaximal]; refine Ideal.mem_sInf.mpr (fun {M} hM => ?_); rw [Set.mem_setOf_eq] at hM; by_contra haM`. For a maximal `M` with `a ∉ M`, maximality gives `M ⊔ Ideal.span {a} = ⊤` (`(Ideal.isMaximal_def.1 hM).2 _ (lt_of_le_of_ne le_sup_left …)`, strictness from `Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)`), so `1 = m + r*a` with `m ∈ M` (`Submodule.mem_sup` + `Ideal.mem_span_singleton'` for the *left* multiple `r*a`; `m = 1 - r*a` by `eq_sub_of_add_eq`). When `(r*a)² = 0`, `m` is a unit (inverse `1 + r*a`) — build it as an **explicit `Units` `⟨⟨1-r*a, 1+r*a, hval, hinv⟩, rfl⟩`** since `isUnit_of_mul_eq_one` needs commutativity, and prove `hval`/`hinv` with `noncomm_ring` (NOT `ring`) reducing to `1 - r*a*r*a` then `sub_zero`. Unit in `M` contradicts `hM.ne_top` via `Ideal.eq_top_of_isUnit_mem`. Pair with `IsSemisimpleRing.jacobson_eq_bot` (semisimple ⇒ radical `⊥`, `import Mathlib.RingTheory.Jacobson.Semiprimary`) for a "degenerate/non-separable ⇒ NOT semisimple" obstruction. Two supporting facts from the same proof: (a) the grade-involution intertwiner `a * r = involute r * a` for `a = ι v` (when `polar Q v · = 0`) is a clean `CliffordAlgebra.induction` (algebraMap: `AlgHom.commutes`+`Algebra.commutes`; ι: `eq_neg_of_add_eq_zero_left (ι_mul_ι_add_swap …)`; mul/add: `map_mul`/`map_add` + assoc), giving `a*r*a = 0` for free; (b) **`CliffordAlgebra.ι` injectivity in char ≠ 2** (no general Mathlib lemma) via `CliffordAlgebra.equivExterior` (needs `haveI : Invertible (2:ℂ) := invertibleOfNonzero (by norm_num)`): `(equivExterior Q) (ι Q v) = ExteriorAlgebra.ι ℂ v` is exactly `CliffordAlgebra.changeForm_ι CliffordAlgebra.changeForm.associated_neg_proof v`, then `ExteriorAlgebra.ι_eq_zero_iff`.
- **The minimal polynomial `z²−20z−400=0` splitting `Λ²(ℂ⁴)` into `ℂ³₊`/`ℂ³₋` (#5459 crux) does NOT need an explicit 16×16 matrix `decide` — get it from multiplicity-freeness for free (landed as `lam2_hom_finrank`, `zEnd_trace`, PR #5741).** `FDRep.scalar_product_char_eq_finrank_equivariant V V : ⅟(card G) • ∑_g χ(g)χ(g⁻¹) = finrank ℂ (V ⟶ V)` (in `RepresentationTheory/Character.lean`; needs `[Fintype G] [Invertible (card G : ℂ)]` — supply the invertible instance by `rw [show Fintype.card G = 60 from …]; exact invertibleOfNonzero (by norm_num)`) turns `⟨χ_{Λ²},χ_{Λ²}⟩ = 2` into `dim_ℂ End_G(Λ²) = 2`. Evaluate the sum honestly by writing `χ_{Λ²}(g)=½·P(g)` with the **integer** `P(g)=(fix₅(g)−1)²−(fix₅(g·g)−1)` (from `lam2_char_formula`+`repC4_char`; the character is real so `χ(g⁻¹)=χ(g)` via `fixCardM_inv` and `g⁻¹g⁻¹=(gg)⁻¹`), factor out `¼`, and `∑_g P(g)²=480` by `decide` (integer sum, no ℚ/native_decide). Then `dim End=2` means the **three** endos `{1, z, z²}` are linearly dependent (3 vectors in a 2-dim `Hom`-space), forcing a degree-≤2 minimal polynomial; the two trace identities pin it exactly: `tr z=60` (each `ρ(g·r·g⁻¹)` is conjugate to a 5-cycle so `χ_{Λ²}=1`, sum of `1` over 60 elts — via `FDRep.char_conj`+`lam2_character 3`; note `LinearMap.trace ℂ ↥lam2Sub.toSubmodule (lam2Sub.toRepresentation x) = lam2.character x` holds **by `rfl`**) and `tr z²=3600`, giving `μ⁺+μ⁻=20`, `μ⁺μ⁻=−400` (`μ±=10±10√5`). **Note the eigenvalue scaling differs from the earlier bullet**: this uses `z = Zamb = Σ_{g∈A₅} ρ(g·r·g⁻¹)` (all 60 elts = 5·class-sum, chosen so centrality is a one-line reindex), so `μ±=20φ/20φ'`, min poly `z²−20z−400` — NOT the class-sum-only `X²−4X−16`. Remaining after PR #5741: package `zEnd` as a categorical `φ : lam2 ⟶ lam2` (equivariant via `zEnd_central`), extract the degree-2 relation, then projector `P⁺=(z−μ⁻)/(20√5)` gives `finrank=3`; characters via the two-eigenspace `LinearMap.trace_eq_sum_trace_restrict` system. **Trace-moment lemmas `tr(zⁿ)` (`zEnd_sq_trace` `=3600`, `zEnd_cube_trace` `=96000`, #5778): mirror the sibling one level up, and never `rw [map_mul]` on a `trace(a*b*c)=…` goal.** `map_mul` sees `LinearMap.trace` (a `→ₗ[ℂ] ℂ` functional) and tries to synthesize `MulHomClass` for it, silently mangling the goal into `trace a * trace b * trace c` before failing — the tell is `failed to synthesize instance … MulHomClass (… →ₗ[ℂ] ℂ)`. Do the `map_mul`/associativity rewrite inside a **separate endomorphism-level `have hrw : z*…*ρ(g·r·g⁻¹) = ρ g * (…) * ρ g⁻¹`** (there `map_mul` correctly targets `lam2Sub.toRepresentation`), then `rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]`. For `tr(zⁿ)`: centrality of the product `zⁿ⁻¹` (`(zEnd_central g).mul_right (zEnd_central g)` builds `Commute (ρ g) (z*z)` for the cube) makes every conjugate summand's trace equal, so `tr(zⁿ)=60·tr(zⁿ⁻¹·ρ(r))`; unfold one more `z` and hit `zEnd_comp_char` to land on an honest `∑_h ∑_{h'} χ`-style group sum by `decide`. That decide scales ~60× per extra `z` factor (cube = 3600 terms, ~4 min build, `maxHeartbeats 2000000000`/`maxRecDepth 100000`); a `classIdxA5` class-index reduction (sub-issue #5) would cut it to 60 terms but `fixCardM` alone can't separate the two 5-cycle classes, so that fallback needs the dedicated work. When copying the sibling's `key : (∑ …) = N := by decide`, replicate its parenthesis nesting exactly — an extra `(` around the summand leaves the outer `(∑…)` unclosed and the parser dies on `:=` with "unexpected token ':='; expected ')'".
- **`rw` gotchas hit while landing PR #5741 (both cost a rebuild):** (1) rewriting a hypothesis of the form `⅟(card G) • S = …` with `card G = 60` fails **`motive is not type correct`** — the `⅟` carries an `Invertible (card G)` instance that can't be abstracted; fix by `rw [invOf_eq_inv, smul_eq_mul]` FIRST (drops the instance-dependence), then rewrite the cast freely. (2) A `rw [… , lam2_character 3]` chain can silently close the goal via its trailing `rfl` (the `![6,0,-2,1,1] 3` matrix index reduces to `1` definitionally), so a following `norm_num`/`rfl` throws **"no goals to be solved"** — either drop the trailing tactic, or make the closing step robust with `simpa using lam2_character 3` (simp's `Matrix.cons_val_*` evaluate the index either way).
- **`motive is not type correct` in `Fin n`/`Nat.Partition`/`List`-index proofs (#6076, Problem 5.16.2; two variants, each cost a rebuild).** (1) With `hsum : la.sortedParts.sum = n`, doing `rw [← hsum]` to turn a goal `m < n` into `m < …sum` fails — `n` is the *type parameter* of `la : n.Partition`, so abstracting it breaks `la`'s type. Fix: never `rw [← hsum]`; use a term (`lt_of_lt_of_eq hmlt hsum : m < n`) or forward `rw [hsum]` in a goal that mentions only `…sum`. (2) `set r := rowOfPos … with hr` *before* establishing a `getElem` fact, then `rw [hr]` into the index of `la.sortedParts[r]`, fails (the `r < length` membership proof depends on `r`). Fix: state the raw `have`s (`rowOfPos_lt_length`, `colOfPos_lt_getElem`, `pos_decomp_list`) *first*, then `set r`/`set c` — `set` folds them automatically and no `rw`-into-`getElem` is needed. Also: `List.sum_take_succ l i h : (l.take (i+1)).sum = (l.take i).sum + l[i]` is cleaner than `take_succ_eq_append_getElem` + `simp`.
- **Reusing earlier-chapter helpers that are `private` (#6076).** Much of the Young-tableau coefficient/counting machinery (`youngSymmetrizer_pq_coeff`, `youngSymmetrizer_support` in `PolytabloidBasis.lean`; `rowOfPos_lt_iff`, `rowOfPos_colOfPos_canonical`, `card_filter_val_lt`, `swap_mem_RowSubgroup`, … in `Lemma5_13_2.lean`) is `private`. `grep -n "private (theorem|lemma) <name>"` and remove the `private` keyword rather than reproving — de-privatizing is a one-word, regression-free change (verified by a full `lake build`), far cheaper than re-deriving ~80 lines of `MonoidAlgebra`/positional-induction proofs.
- **`MonoidAlgebra.algHom_ext` hands you the goal on `single g 1`, not `of g` (#6750, `Chapter5/Problem5_24_1_b.lean`).** So `of`-based rewrite lemmas (e.g. a project `signTwist_of : φ (of g) = …`) silently fail to fire (`rw` "did not find pattern"; `simp only` leaves the goal unsolved and flags every downstream arg unused). `MonoidAlgebra.of ℂ G g` is *defeq* to `single g 1` but not syntactically equal — insert a `show φ (φ (MonoidAlgebra.of ℂ G g)) = MonoidAlgebra.of ℂ G g` (`show`/`change` uses defeq, unfolding `AlgHom.comp`/`AlgHom.id` too) *before* the `of`-lemma rewrites. For involution proofs (`sign(g)²=1`, group-algebra automorphisms), prove `(sign g : ℤˣ)` squares to `1` via `Int.units_mul_self` after `← Int.cast_mul, ← Units.val_mul` (the ℤ-level `↑u * ↑u` is NOT the ℤˣ `u * u` the lemma expects), then `DFunLike.congr_fun hcomp` + `Function.Involutive.bijective`. Also: no Mathlib lemma sums `YoungDiagram.rowLens` — `μ.rowLens.sum = μ.card` is `Finset.card_eq_sum_card_fiberwise` on `Prod.fst` (fibers are `row i`, `rowLen_eq_card`); `card_transpose` is `Equiv.finsetCongr`; the `(List.range n).map f).sum = ∑ i ∈ Finset.range n, f i` bridge is a 2-line `List.range_succ`/`Finset.sum_range_succ` induction.
- **Extracting the golden-ratio characters `χ₊`/`χ₋` from the eigenspace split (#5781, PR #5843, landed as `repC3plus_character`/`repC3minus_character`).** Solve the 2×2 trace system `χ₊+χ₋ = χ_{Λ²}` and `μ⁺χ₊+μ⁻χ₋ = tr(z·ρ(g))` per class `j`: `LinearMap.trace_eq_sum_trace_restrict` over the `IsCompl` eigenspace pair `E±` of `zEnd` gives both equations (on `E±`, `z·ρ(g)` restricts to `μ±·(ρ(g)|E±)` — prove via `Module.End.mem_eigenspace_iff.mp (hf i x.2)`), then `mul_left_cancel₀ (muPlus_sub_muMinus ≠ 0)` + `linear_combination (±10)*sqrt5_sq`. **Two traps that cost ~7 rebuilds:**
  - **The trace-transport `repC3plus.character g = tr(ρ(g)|E⁺)` hits an `AddCommGroup` instance diamond.** `LinearMap.trace_conj'` (needed to move the trace across the intertwiner `e : E⁺ ≃ repC3plusSub.toSubmodule`) requires `[AddCommGroup ↥E⁺]`, but a **doubly-nested** subtype `↥E⁺` (`E⁺ : Submodule ℂ ↥lam2Sub.toSubmodule`) defaults to `Submodule.addCommMonoid`, so `e` records `E⁺.addCommMonoid` and you get *"Application type mismatch: argument `e` … `E.addCommMonoid` vs `AddCommGroup.toAddCommMonoid`"*. **Fix: `letI : AddCommGroup (↥E) := E.addCommGroup` as the first line of the proof** — the local high-priority instance makes every `↥E` (the equiv, both traces) resolve the `AddCommGroup`-derived `AddCommMonoid`, matching `trace_conj'`. Build the intertwiner with `LinearEquiv.ofBijective` of a corestricted `(lam2Sub.subtype ∘ₗ E.subtype).codRestrict …` (mirrors `Theorem5_25_2.lean`'s `evalMap`); `Submodule.equivMapOfInjective` hits the same diamond. The whole transport lemma needs `set_option synthInstance.maxHeartbeats 400000` + `maxHeartbeats 800000` (the nested subtype makes defeq slow, not wrong).
  - **`Q5toC` arithmetic: use `norm_num`, not `simp only`.** `simp only [Q5.ofNat_re, Q5.neg_re, …]` does **not** reduce `(3 : Q5).re`/`(-1 : Q5).im` (leaves opaque `re 3` in the goal); `norm_num [Q5toC, muPlus, muMinus, chiA5, Matrix.cons_val_*, Q5.mk_re, Q5.ofNat_re, …]` does, and outright closes the all-rational classes (incl. the all-zero class `1`) — leaving only the two 5-cycle classes for `linear_combination`. Never `decide` on `Q5` (the `1/60`/`ℚ`-normalisation stalls the kernel).

**Honest (`native_decide`-free) arithmetic over the `Q5 = ℚ[√5]` character table (#5459 deliverable 4, the retired `A5_orthonormal`, sorry-free axiom-clean in `Chapter4/Example4_8_1.lean`).** Any computation over the book table `chiA5 : Fin 5 → Fin 5 → Q5` (the orthonormality `ip` sum, and the upcoming #5468/#5469 character/norm-one sums) — kernel `decide` **stalls**, but NOT on the `√5`/foldr: it stalls on `ℚ`-normalisation, getting stuck at the `Rat.num` `Decidable` instance even after the `List.ofFn`/foldr is removed. This triggers on **any non-integer `ℚ`** in the entries, not only a `1/N` prefactor (e.g. `1/60`): a bare `(chiA5 1 j + chiA5 2 j).re = …` `decide` over the `⟨1/2, ±1/2⟩` golden-ratio entries of rows 1/2 also stalls. So do not reach for `decide` on anything touching the `1/2` entries; the working pattern is `Q5.ext`/`norm_num` (the `Q5.*_re/_im` projection set below closes `.re`/`.im` of `Q5` sums directly — e.g. `lam2_character_eq_sum : lam2.character (classRepA5 j) = Q5toC (chiA5 1 j) + Q5toC (chiA5 2 j)`, the `χ_Λ² = χ₊+χ₋` identity, via `← Q5toC_add` then `fin_cases j <;> simp only [chiA5, cons_val…] <;> norm_num [Q5.add_re, …]`):
  1. **A `sumFin_five`-style explicit-unfold lemma** (`sumFin f = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0))))`, proved by `simp only [sumFin, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]; rfl`). The bare `List.ofFn`/`List.foldr` simp lemmas reduce *inconsistently* in the big file vs a scratch (sometimes leaving an un-reduced `Fin.foldr 5 …`), so pre-unfold the fixed-arity sum into a named lemma rather than relying on `List.ofFn` inside the main proof.
  2. **`Q5` projection simp lemmas** `mk/zero/one/add/neg/mul/ofRat _re/_im` (all `rfl`). The `OfNat` ones MUST use `no_index`: `theorem ofNat_re (n : ℕ) : (no_index (OfNat.ofNat n) : Q5).re = (OfNat.ofNat n : ℚ) := rfl` — without `no_index`, simp's discrimination tree indexes on the literal and the lemma silently makes "no progress" on `(3 : Q5).re` (the custom `OfNat Q5 n` instance, not an `AtLeastTwo` one). Keep them **non-`@[simp]`** and pass explicitly: marking them `@[simp]` does NOT add warnings (the ~21 `unusedSimpArgs` in this file are pre-existing, e.g. `Matrix.toLin'_apply` at the Q₈ `rho_apply`), but explicit-only keeps the blast radius surgical.
  3. **One `norm_num` pass** after `fin_cases i <;> fin_cases j <;> (first | rw [if_pos rfl] | rw [if_neg (by decide)]) <;> apply Q5.ext <;> norm_num [ip, Q5.sumFin_five, sizesA5, chiA5, <all the Q5 _re/_im>, Matrix.cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, head_cons, tail_cons]`. `norm_num` (NOT `simp only`) is what reduces the `OfNat` literals and the `1/60 * (rational) = 0/1` arithmetic; the `cons_val_two/three/four` lemmas (they DO exist in this Mathlib — the existing `repC4_character` uses them) handle matrix indices ≥ 2 that `cons_val_zero/one`+`head_cons` miss. Probe the whole proof in a `/tmp` scratch (`gtimeout 400 lake env lean`) before the 90s file build.

Reusable pieces and the gotchas that each cost a build cycle:
- **The 2-dim quaternion rep already exists** as `Etingof.Q8.rho` in `Chapter5/Example5_1_3.lean` (matrices `A=diag(i,-i)`, `X=![![0,1],![-1,0]]`, `Mhom`, `rho`, plus an `IsSimpleModule` proof). But `Chapter5` *imports* `Chapter4`, so a Ch4 file **cannot** import it — rebuild the construction in a local namespace (no name collision since the namespace differs). Same will hold for any Ch4 rep that duplicates a Ch5 one. **A second, sorry-free template over Mathlib's *abstract* `QuaternionGroup 2`** (the Pauli rep of Example 4.3) lives at `Chapter4/Example4_3_Q8.lean` (`Etingof.Example4_3_Q8.rep : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ`, plus a `Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ)` wrapper `repLin`). Building a `MonoidHom` out of `QuaternionGroup n` (rather than a custom `Q8`) means `map_mul'` must handle the four `a/xa` cases with `ZMod (2*n)` exponents: define `repFun (a i) = A^i.val`, `repFun (xa i) = X*A^i.val`; reduce powers mod the order with a `A^m = A^(m % 4)` helper (`Nat.div_add_mod` + `pow_add`+`pow_mul`+`A^4=1`); and discharge each exponent congruence `A^p = A^q` via a `rhoI_pow_congr` lemma whose `(p:ZMod 4)=(q:ZMod 4)` hypothesis is closed by `revert i j; decide` (the `ZMod (2*n)` arithmetic is a finite decidable check — no `linear_combination`/`push_cast` fights with the characteristic). The driving group relations are matrix identities proved by `simp only [..., Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two, Complex.I_mul_I]`. Note `Matrix.neg_fin_two` does NOT exist (use `ext`+`Matrix.neg_apply`), and `ring` will NOT prove `A^4=(A^2)^2` on noncommutative matrices (use `pow_mul`/`pow_succ`).
- **Unit quaternions ≅ SU(2) — DONE (Problem 4.12.7(e), #6271, `Chapter4/Problem4_12_7.lean`), a reusable template for any quaternion↔2×2-matrix group iso.** Define the raw embedding `qmat q = !![re+imI·I, imJ+imK·I; -imJ+imK·I, re-imI·I] : ℍ[ℝ] → M₂(ℂ)` as a plain `noncomputable def` (NOT a bundled RingHom — avoids the AlgHom obligations), give it four `@[simp]` entry lemmas at literal indices (`qmat q 0 0 = …`, proved `rfl`), then prove `qmat_one`/`qmat_mul` (`ext i j; fin_cases i <;> fin_cases j <;> simp only [qmat, Matrix.mul_apply, Fin.sum_univ_two, Fin.mk_zero, Fin.mk_one, <cons lemmas>, Quaternion.{re,imI,imJ,imK}_mul] <;> apply Complex.ext <;> simp only [Complex.{add,mul,sub,neg,ofReal,I}_{re,im}, …] <;> ring` — `ring` can't see `I*I=-1`, so you MUST split to `re`/`im` via `Complex.ext` first), `qmat_conjTranspose : qmat (star q) = (qmat q)ᴴ` (star↔conjTranspose), and `qmat_det q = ↑(normSq q)`. Unitarity of the image is then *free*: `star (qmat q) * qmat q = qmat (star q) * qmat q = qmat (star q * q) = qmat ↑(normSq q) = qmat 1 = 1`. Assemble `qmatHom : unitary ℍ[ℝ] →* specialUnitaryGroup (Fin 2) ℂ` (membership via `Matrix.mem_specialUnitaryGroup_iff` = unitary ∧ det 1; `map_one'`/`map_mul'` are `Subtype.ext (by simpa using qmat_{one,mul} …)`), then `MulEquiv.ofBijective`. **Surjectivity is the crux:** for `M ∈ SU(2)`, get the explicit anti-diagonal form `M 1 1 = star (M 0 0)`, `M 1 0 = -star (M 0 1)` from `Mᴴ = adjugate M` (both equal `M⁻¹`: `Matrix.inv_eq_left_inv huc` from unitary, `Matrix.inv_eq_right_inv` from `mul_adjugate`+`det=1`; then `Matrix.adjugate_fin_two`), reconstruct the preimage quaternion `⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩`, get `normSq = 1` from `det M = M00·star M00 + M01·star M01 = ↑(Complex.normSq M00 + normSq M01)` (`Complex.mul_conj` matches `z * star z` by defeq — `starRingEnd_apply` is `rfl`), and finish `qmat q = M` with `Matrix.eta_fin_two M` + `rw [h11,h10]` + `ext i j; fin_cases … <;> simp [qmat, hq, Complex.ext_iff]`. **Gotcha that cost a build cycle:** `(Quaternion.normSq q : ℂ)` mis-elaborates — the `: ℂ` is taken as the *expected output type* of the polymorphic `normSq : ℍ[R] →*₀ R`, forcing `R = ℂ` hence `q : ℍ[ℂ]` (error "expected ℍ[ℂ]" / "failed to synthesize CommRing ℍ"). Always double-annotate the natural output first: `((Quaternion.normSq q : ℝ) : ℂ)`. Same trap for any `(polyFn x : T)` where `T` isn't the natural codomain.
- **Dimension of a matrix subspace + internal direct sum `End(V) = ⊕ Wᵢ` (SO(3)-decomposition, #6353, sorry-free in `Chapter4/Problem4_12_11.lean`).** For a `Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)` cut out by transpose/trace conditions (scalars `ℝ·1`, skew `Mᵀ=-M`, symmetric, traceless-symmetric): **finrank via explicit `!!` basis** — `set v : Fin d → EndV := ![!![…], …]`, prove `LinearIndependent ℝ v` with `rw [Fintype.linearIndependent_iff]; intro g hg; have eIJ := congr_fun (congr_fun hg I) J; simp [hv, Fin.sum_univ_{three,five}, Matrix.add_apply] at eIJ ⊢; intro i; fin_cases i <;> simp_all` (read off `g I` from the basis entry that is `1` there and `0` elsewhere), prove the `Submodule = Submodule.span ℝ (Set.range v)` by `le_antisymm` (⊇: `Submodule.span_le` + `rintro _ ⟨i,rfl⟩; fin_cases i <;> · ext a b; fin_cases a <;> fin_cases b <;> simp [hv]`; ⊆: matrix `ext i j; fin_cases i <;> fin_cases j <;> simp [hv, Matrix.add_apply] <;> linarith [<entry relations>]` where the relations `M j i = ±M i j`, `M i i = 0`, `M22 = -M00-M11` come from `congr_fun (congr_fun hMᵀ i) j` on the defining transpose eq and `Matrix.trace_fin_three`), then `rw [hspan, finrank_span_eq_card hindep, Fintype.card_fin]`. Scalar line: `finrank_span_singleton one_ne_zero`. **`DirectSum.IsInternal ![W₀,W₁,W₂]`** via `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`: independence from `iSupIndep_fin_three` (three `Disjoint` goals; `change Disjoint W₀ (W₁ ⊔ W₂)` — NOT `show`, style linter — then `Submodule.disjoint_def`; the transpose/trace *functionals* kill the cross terms, e.g. a symmetric skew matrix is `0` via `(2:ℝ)•M=0` from `rw [two_smul ℝ]; nth_rewrite 2 [hMM]; rw [add_neg_cancel]` then `smul_eq_zero`); `iSup = ⊤` from the projection decomposition `M = (tr M/3)•1 + ½(M−Mᵀ) + (½(M+Mᵀ)−(tr M/3)•1)` (membership summed with `Submodule.mem_sup`, the algebraic identity `by module`, transpose obligations by `simp only [Matrix.transpose_*]; module`, trace by `simp only [Matrix.trace_*, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]; ring`). Two gotchas: **chained `rw [Matrix.transpose_mul/transpose_transpose,…]` fails** (`transpose_transpose` needs a syntactic `Mᵀᵀ` that the previous step didn't produce, or a nested `((c•1)ᵀ)` a single `transpose_smul` won't reach) — use **`simp only [Matrix.transpose_*]`** which applies repeatedly; **`le_iSup _ i` leaves the family a metavariable** so a `: Wᵢ ≤ _` ascription can't reduce `![…] i` — pass the family explicitly `le_iSup ![W₀,W₁,W₂] i`. Membership `iff`s (`M ∈ skewSub ↔ Mᵀ = -M`) are `Iff.rfl`.
- **Irreducibility of the same SO(3) summands by orbit-of-rotations (#6539, `skewSub_irreducible` landed sorry-free; `tracelessSymSub_irreducible` #6547 / `hooke_law` #6548 planned).** To show a `conjRep`-invariant `U ≤ W` is `⊥` or `W` (`conjRep A M = A M Aᵀ`), build concrete rotation elements of `SO3` and read off their conjugation action on the explicit `!!`-basis, then chase the orbit. Membership: `⟨mat, by rw [mem_specialOrthogonalGroup_iff]; refine ⟨?_,?_⟩; · rw [mem_orthogonalGroup_iff]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]; · simp [Matrix.det_fin_three]⟩ : SO3`. Conjugation-on-basis: `conjRep R (basis i) = ±basis j` by `ext i j; fin_cases i <;> fin_cases j <;> simp [conjRep_apply, R, basis, Matrix.mul_apply, Fin.sum_univ_three]` (simp handles `star` = transpose over ℝ on its own — do NOT add `star_coe_eq_transpose`, it's unused). **Standard 3-dim rep (skew):** the three diagonal sign rotations `diag(±1)` (det 1, i.e. even # of `−1`s) isolate each coordinate via `M ± conjRep D M` (the entry `(Dz M Dz)ᵢⱼ = dᵢdⱼ Mᵢⱼ` flips exactly the off-axis entries); the cyclic-permutation rotation `!![0,0,1;1,0,0;0,1,0]` spreads one coordinate to all three; a nonzero coordinate then forces every basis vector into `U` (`extract` via `inv_mul_cancel₀`). **Key gotcha for the 5-dim spin-2 rep W (traceless symmetric):** the finite octahedral rotation subgroup (sign + permutation matrices, order 24) splits W as `2 ⊕ 3`, so finite rotations do **NOT** prove W irreducible — you need exactly ONE continuous rotation. The mechanically-verified route: the V4 sign group `{I,Dx,Dy,Dz}` acts on the 5 basis vectors by distinct `±1` characters, so `¼∑ χ(g) conjRep g M` projects `M` onto each basis component (all in `U`); then one 45° rotation `Rz45 = !![c,-c,0;c,c,0;0,0,1]`, `c = Real.sqrt 2 / 2`, converts off-diagonal ↔ diagonal (`conjRep Rz45 w0 = -w3`). Membership/conjugation for the 45° rotation close after `simp` with `ring_nf; rw [c45, div_pow, Real.sq_sqrt (by norm_num)]; norm_num` (keep `c45_sq : c45*c45 = 1/2` handy). For an equivariant-endo-is-scalar step (`hooke_law`): a matrix invariant under `Dz,Dy,Dc` is scalar (finite entrywise); and `f|_W` scalar follows from Schur (`ℝ[f|_W]` is a field, `= ℝ` or `ℂ`) plus `dim_ℝ W = 5` **odd** ruling out the `ℂ` complex-structure case — this needs only *real* irreducibility, no absolute irreducibility. **`hooke_law` DONE (#6548, sorry-free modulo the `tracelessSymSub_irreducible` dep).** The realized proof is *simpler* than the `ℝ[f|_W]`-field-classification plan — use these three reusable pieces: **(1) dimension-form Schur** `equivMap_eq_zero_of_finrank_lt`: an equivariant `φ` mapping an irreducible invariant `W` into a strictly-smaller invariant `Wsmall` (`finrank Wsmall < finrank W`) is `0` on `W` — proof is `W ⊓ ker φ` is invariant so `⊥` or `W` by irreducibility; the `⊥` case makes `φ.restrict` injective (`LinearMap.finrank_le_finrank_of_injective`), contradicting the dimension gap. This needs ONLY source-irreducibility + a `finrank` count, avoiding the non-iso-target Schur argument. Apply it with `φ = scalarProj ∘ₗ f` (`1 < 5`) and `φ = skewProj ∘ₗ f` (`3 < 5`) to kill the scalar/skew components of `f(W)`, giving `f(W) ⊆ W`. `scalarProj`/`skewProj` are genuine equivariant `def`s (`M ↦ (tr M/3)•1`, `M ↦ ½(M−Mᵀ)`; equivariance from `conjRep_trace`/`conjRep_transpose`; `map_add'`/`map_smul'` close by `module`). **(2) `f|_W = μ•id` via a real eigenvalue** — NOT the field classification: restrict `f` to `g : Module.End ℝ ↥W` (`f.restrict hmapsW`), then `g` has a real eigenvalue because `g.charpoly.natDegree = finrank = 5` is ODD (`LinearMap.charpoly_natDegree`, `Module.End.hasEigenvalue_iff_isRoot_charpoly`); the μ-eigenspace pulled back to `W ⊓ ker(f − μ•id) ≤ EndV` is a nonzero (`HasEigenvalue.exists_hasEigenvector` gives the witness) invariant submodule, hence `= W` by irreducibility ⟹ `f y = μ•y` on all of `W`. **(3) odd-degree real root helper** `exists_isRoot_of_odd_natDegree` — **Mathlib has NO `IsRealClosed ℝ` instance** (`FieldTheory/IsRealClosed` exists but no ℝ instance), so prove it inline via IVT: normalise to `leadingCoeff = 1` (`C lc⁻¹ * p`), get a positive value from `tendsto_atTop_of_leadingCoeff_nonneg` and a negative one from `(p.comp (-X))` + `tendsto_atBot_of_leadingCoeff_nonpos` (leadingCoeff `−1` by `Odd.neg_one_pow`), then `intermediate_value_Icc`/`Icc'`. **Gotcha (cost a build cycle):** computing `conjRep A M` entrywise by `simp only [conjRep_apply, <def>, Matrix.mul_apply, Fin.sum_univ_three, star, Matrix.conjTranspose, Matrix.transpose, Matrix.map_apply, …]` leaves the real `star` as `id (entry)` (e.g. `id 1`, `id (-1)`) — you MUST add `id_eq` to the simp set or `linarith` sees opaque terms; and specialise the `congr_fun (congr_fun h i) j` entry equations at CONCRETE `i j` before simp (a `∀ i j` form never evaluates the `vecCons` indices).
- **Character from a rep:** `(FDRep.of ρ).character g = LinearMap.trace ℂ V (ρ g)` holds **by `rfl`** (`FDRep.of_ρ'` is `rfl`), so `rw [show (FDRep.of ρ).character g = LinearMap.trace ℂ V (ρ g) from rfl]`. For a matrix rep `ρ g = toLinAlgEquiv' (M g)`: rewrite `ρ g = toLin' (M g)` (by `ext; simp [ρ_apply, Matrix.toLin'_apply]`) then `Matrix.trace_toLin'_eq` gives `= (M g).trace`. For a 1-dim rep `ρ g = χ g • LinearMap.id`: `map_smul` + `LinearMap.trace_id` (= `finrank`) gives `χ g`.
- **Schur scalar from a commuting endomorphism: extract the underlying `LinearMap` from the category equation with THREE `.hom`s (`Chapter6/DimDvdCard.lean`, #6723).** To turn "`f : Module.End ℂ V` commutes with `V.ρ g` for all `g`, `V` simple" into `f = c • LinearMap.id`: (1) package `f` as `φ : V ⟶ V := { hom := FGModuleCat.ofHom f, comm := fun g => by ext v; exact LinearMap.congr_fun (hf g) v }` where `hf g : f ∘ₗ V.ρ g = V.ρ g ∘ₗ f` (the `comm` field wants exactly this orientation — an `End` `*`-equation `a * b = b * a` is defeq to the `∘ₗ` form, so `(hcomm g).symm` slots in); (2) `obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ φ` (needs `[Simple V]`; `FiniteDimensional ℂ (V ⟶ V)` is automatic for `FDRep`). Then the underlying `LinearMap` of an `FDRep`/`Action` morphism is `ψ.hom.hom.hom : V.V →ₗ V.V` (**three** `.hom`s: Action.Hom → FGModuleCat/Induced → ModuleCat.Hom → LinearMap — NOT two; `congr_fun`/`DFunLike.congr_fun` on `f.hom.hom` fails because it is a `ModuleCat.Hom`, not a function). Close `f = c • LinearMap.id` by: `have key : (FGModuleCat.ofHom f).hom.hom = (c • 𝟙 V).hom.hom.hom := congrArg (fun ψ : V ⟶ V => ψ.hom.hom.hom) hc.symm; rw [show (FGModuleCat.ofHom f).hom.hom = f from rfl] at key; rw [key, Action.smul_hom, Action.id_hom]; rfl`. The three defeq facts that make the tail `rfl`-close: `(FGModuleCat.ofHom f).hom.hom = f`, `(c • g).hom.hom = c • g.hom.hom` (FGModuleCat smul), and `FGModuleCat.hom_hom_id : (𝟙 A).hom.hom = LinearMap.id` — all `rfl`. Then `LinearMap.trace ℂ V (c • LinearMap.id) = c * finrank` (`map_smul` + `LinearMap.trace_id`) pins `c`. Do NOT go through the `MonoidAlgebra ℂ G`-module `Corollary_2_3_10` route unless you already have `IsScalarTower`/`IsSimpleModule A V` set up — the category route above needs only the bare commuting `LinearMap`.
- **Every element of `ℤ[G]` (`G` finite) is integral over `ℤ` — for free, no center machinery.** `MonoidAlgebra ℤ G` is `Module.Finite ℤ` via `Module.Finite.of_basis Finsupp.basisSingleOne` (`haveI : Fintype G := Fintype.ofFinite G` first), so `IsIntegral.of_finite ℤ z` gives integrality of any `z` directly. The central-character integrality (#6723) needs only this + Schur (above): a class sum `z = ∑_{x ∼ g₀} single x 1` need NOT be shown central in `ℤ[G]` for its scalar `ω` to be integral — map it through `Φ = MonoidAlgebra.lift ℤ (End ℂ V) G V.ρ`, get `Φ z = c • id` by Schur, and descend `IsIntegral ℤ (Φ z) = IsIntegral ℤ (algebraMap ℂ (End ℂ V) ω)` to `IsIntegral ℤ ω` via `isIntegral_algebraMap_iff` (`algebraMap ℂ (End ℂ V)` injective on nonzero `V`: `injective_iff_map_eq_zero`, then `Module.ker_algebraMap_end` + `top_ne_bot`). Conjugation-permutes-the-class reindexing is `Finset.sum_nbij' (fun x => g*x*g⁻¹) (fun x => g⁻¹*x*g)` with membership by `isConj_iff.mpr ⟨g, …⟩` + `IsConj.trans`, summand equality by `simp only [← MonoidHom.map_mul]; congr 1; group`.
- **Simplicity via `FDRep.simple_iff_char_is_norm_one`** (needs `[IsAlgClosed][CharZero][Fintype]`, all hold for ℂ + a finite group): the goal is `∑_{g:G} χ(g)·χ(g⁻¹) = Nat.card G`. **1-dim case is free** — the character *is* the `MonoidHom`, so each summand `χ(g)·χ(g⁻¹) = χ(g·g⁻¹) = 1` (`← map_mul, mul_inv_cancel, map_one`), and `Finset.sum_const` finishes; no enumeration. **2-dim (or higher) case** needs an explicit `∑_{g:G}` enumeration: build `enum : Fin |G| → G`, prove `Function.Bijective enum` by `Fintype.bijective_iff_injective_and_card` + `⟨by decide, by decide⟩`, then `rw [← Equiv.sum_comp (Equiv.ofBijective enum _) f, Fin.sum_univ_eight]; simp only [Equiv.ofBijective_apply, enum]; rfl`. Carry the 8 per-element inverses as `show g⁻¹ = h from by decide`.
- **Universe trap: `FDRep.simple_iff_char_is_norm_one` forces `k` and `G` into the *same* universe (#6306, `Chapter4/Problem4_12_6.lean`).** It unifies `Simple.{u,u+1}`, so it fires only for a `Type 0` group (`QuaternionGroup 2`, `Equiv.Perm (Fin n)`, `Heisenberg p`). For an **abstract** group `G : Type u₁` (e.g. `Affine K` with `K : Type*`) it fails with `Simple.{0, max u₁ 1} … =?= Simple.{?u, ?u+1}`. Don't reach for the character criterion there — prove simplicity of the 1-dim `charRep χ` as a **`ℂ[G]`-module** instead: `IsSimpleModule ℂ[G] (charRep χ).asModule` via `isSimpleModule_iff` + the `Subrepresentation.subrepresentationSubmoduleOrderIso ▸ IsSimpleOrder` reduction (every `ℂ`-subspace of `ℂ` is `⊥`/`⊤` and invariant), then feed the universe-general bridge `Etingof.simple_fdRepOf_of_isSimpleModule (charRep χ) : Simple (FDRep.of (charRep χ))` (Exercise4_2_3, `{k : Type u} {G : Type v}` — different universes OK). Same trap applies to feeding an arbitrary-universe `W` (or a subrep on `↥(zeroSum K)`) into the `Type 0` Wedderburn enumeration `exists_simples_sum_finrank_sq_eq_card`: **universe-transport** it with the `Problem4_12_2`/`Problem4_12_6` idiom `exists_simpleFDRep` (`transportModule`/`repOfModule`/`transportLinearEquiv` from `Infrastructure/SimpleModuleCount.lean` → `FDRep.of (repOfModule (Fin dM → ℂ))`, dim preserved). The whole "classify irreps of `K ⋊ Kˣ` / abstract `G` over ℂ" pattern is a near-verbatim clone of `Problem4_12_2` (Heisenberg) — mirror it rather than re-deriving; `FDRep.char_iso` for non-iso and `simple_fdRepOf_of_isSimpleModule` are the universe-safe tools.
- **Pairwise non-iso:** `FDRep.char_iso : (V ≅ W) → V.character = W.character` (forward direction only — no `char_orthonormal` needed). Don't prove distinctness cell-by-cell with `simp`/`norm_num` on the ℂ values (the `fin_cases` Fin-literal problem below bites). Instead lift to a **decidable** structural statement: `Q5toC` (the table→ℂ map) is injective on rational entries (`im = 0`), so character-equality forces `chiQ8 i = chiQ8 j` as `Q5`-vectors, and `Function.Injective chiQ8` closes by **`decide`** (Q5 has `DecidableEq`). `|G|` and `#ConjClasses` likewise: `Fintype.card G` via the group's `card` lemma, `Fintype.card (ConjClasses G) = r` by honest `decide` (kernel-checked, fine). **The *converse* — character injectivity `V.character = W.character → Nonempty (V ≅ W)` for `FDRep ℂ G` — is NOT in Mathlib** (only the forward `char_iso`), and is a recurring blocker for "equal characters ⟹ isomorphic reps" steps (e.g. producing the `U₂ ≅ g(U₁)` iso in the Exercise 5.27.3 orbit classification). It follows from Maschke semisimplicity + multiplicity = `⟨χ_S, χ_V⟩` (via `scalar_product_char_eq_finrank_equivariant`), but the isotypic-uniqueness assembly must be built as reusable repo infra — tracked in #6425. Don't hand-roll it inline per item.
- **Iso-level classification from a k[G]-module iso (affine-group template, #7307, `Chapter4/Problem4_12_6.lean`).** The forward bridge `Etingof.equivOfAsModuleLinearEquiv ρ σ (f : ρ.asModule ≃ₗ[k[G]] σ.asModule) : ρ.Equiv σ` (Infrastructure/`SimpleModuleCount.lean`) turns a group-ring-module isomorphism back into a `Representation.Equiv` — it's just `(IntertwiningMap.equivLinearMapAsModule ρ σ).symm f.toLinearMap |>.ofBijective f.bijective` (both `IntertwiningMap.ofBijective` and `equivLinearMapAsModule` are already in Mathlib; don't rebuild `LinearEquiv.ofBijective` + the intertwining proof by hand). `exists_simpleFDRep'` uses it to return `Nonempty (ρ.Equiv U.ρ)` alongside the transported `Type 0` FDRep, so `Representation.char_iso` transfers `ρ`'s character to the concrete model. **Character dot-notation trap on a plain FDRep:** `U.ρ.character` misresolves to `MonoidHom.character` (`FDRep.ρ` is declared `G →* (V →ₗ V)`, a raw MonoidHom, not `Representation`) — write `Representation.character U.ρ`; and `FDRep.character U = Representation.character U.ρ` is `rfl`, so `FDRep.char_iso α` retypes directly to a `Representation.character U.ρ = Representation.character U'.ρ` equality. **Uniqueness pattern:** build the complete family `E = (q-1 characters) ⊕ (one q-1-dim member)` (`Sum.elim`), prove pairwise-non-iso (`FDRep.char_iso`) + `∑ dim² = |G|`, then completeness gives every simple `≅` some `E i`; dimension picks the slot. `FDRep.complete_of_sum_finrank_sq_eq_card` forces same-universe `{k G : Type u}` so it's **unusable for abstract `K : Type*`** — reuse the universe-polymorphic `exists_simples_sum_finrank_sq_eq_card` + `surj_of_injective_of_sum_eq` instead (as `irreducible_dim` does). Worked capstone: `irreducible_classification` (every irreducible `≅` some `charRep χ` or `V`), assembled from `simple_FDRep_iso_enum` + `Vrep_unique` + `charRep_exists` + `equiv_of_character_eq`.
- **Complete-reducibility dimension count for `FDRep ℂ G` — landed reusable infra (`Chapter6/Problem6_1_6.lean`, #6625, sorry-free).** Given a complete irreducible list `W : Fin m → FDRep ℂ G` (`IsCompleteIrreps`: each simple, pairwise non-iso, exhaustive), `char_eq_sum_mult` proves `S.character = ∑ⱼ (finrank ℂ (Wⱼ ⟶ S) : ℂ) • (Wⱼ).character` and `finrank_eq_sum_mult` gives the dimension count `(finrank ℂ S : ℤ) = ∑ⱼ finrank(Wⱼ ⟶ S)·finrank(Wⱼ)`. Recipe (a lightweight version of the #6425 isotypic assembly, done per-file): the difference `χ_S − ∑ⱼ mⱼ χ_{Wⱼ}` is a class function orthogonal to every simple char, so it vanishes by `Etingof.classFunction_eq_zero_of_orthogonal_simples` (in `Chapter4/Theorem4_2_1.lean` — **remember the import**); orthogonality per simple `V'` uses `exhaustive` to get `V' ≅ Wₖ`, then `scalar_product_char_eq_finrank_equivariant` (LHS `∑_g χ_S χ_{Wₖ}(·⁻¹) = |G|·mₖ`) and `char_orthonormal` (`∑_g χ_{Wⱼ} χ_{Wₖ}(·⁻¹) = |G|·[j=k]`). Collapse `char_orthonormal`'s `if Nonempty (Wⱼ ≅ Wₖ)` to `if j=k` via `hW.distinct`/`⟨eqToIso (congrArg W hjk)⟩` — do **not** `subst hjk` (it eliminates the `obtain`-bound `k`, breaking every later `W k`). `finrank_eq_sum_mult` follows by `congrFun … (1:G)` + `FDRep.char_one`. **Parse trap that cost a rebuild:** standalone `finrank ℂ (V G ⊗ W i)` elaborates `⊗` as module `TensorProduct` (→ `failed to synthesize AddCommMonoid (↑(V G).V ⊗ ↑(W i).V)`) because the coercion-to-Type fires before the FDRep monoidal `⊗`; inside a `⟶` it's fine. Fix: `set S : FDRep ℂ G := V G ⊗ W i` and write `finrank ℂ S`. `dim(V ⊗ Wᵢ) = 2·dim Wᵢ` comes from `FDRep.char_tensor` + `char_one` at `1` (avoids a module-tensor `finrank_tensorProduct` lemma entirely); `finrank ℂ (V G) = 2` from `charV_eq` at `1` = `Matrix.trace 1 = Fintype.card (Fin 2)`. To get `m ≥ 1`, the trivial rep `FDRep.of (Representation.trivial ℂ G ℂ)` is `Simple` (via `is_simple_module_of_finrank_eq_one (Module.finrank_self ℂ)` + `NeZero (Nat.card G : ℂ)`), so `exhaustive` yields some `Wᵢ₀` with `dim = 1`.
- **Induced-character norm / Mackey collapse (Exercise 5.27.3 Part (i), `Chapter5/Exercise5_27_3.lean`, sorry-free).** To prove an *abstractly-specified* induced rep `V(χ,U)` is `Simple` from *only* its character formula (iv) — no structural handle on `V` — go through `FDRep.simple_iff_char_is_norm_one`: reduce `∑_{x∈A⋊G} χ_{V}(x)χ_{V}(x⁻¹) = |A⋊G|`. Reusable moves worth mirroring: (a) extend the little-group character `χ_U` to a class function `Uc : G → ℂ` zero off the stabilizer, so the formula's `dite` becomes `χ(φh a)·Uc(hgh⁻¹)` with no proof-dependent subgroup element; (b) the `A`-sum is character orthogonality on the finite abelian `A` — package `∑_a (ψ a : ℂ) = if ψ = 1 then |A| else 0` for `ψ : A →* ℂˣ` via `sum_hom_units_eq_zero` composed with `Units.coeHom ℂ`; (c) collapse the internal triple `G`-sum by two conjugation change-of-variables (`g ↦ hgh⁻¹`, `h' ↦ hh'⁻¹`) written as ONE explicit `(G×G) ≃ (G×G)` bijection fed to `Fintype.sum_equiv` after `← Fintype.sum_prod_type'` — cleaner than nested `Equiv.sum_comp`; each pointwise `if`/`Uc`-argument equality closes by `group`. Gotchas that cost cycles: `Finset.sum_subtype` needs `(p := …)` given explicitly (else the predicate is a metavariable); `positivity` does NOT prove `(n : ℂ) ≠ 0` (ℂ unordered) — use `exact_mod_cast Fintype.card_ne_zero`; `SemidirectProduct.equivProd.symm (a,g)` is defeq `⟨a,g⟩` (close the `∑`-conversion with `rfl`, no `equivProd_symm_apply` simp lemma).

Induced-representation / coset-model gotchas (`Chapter5/Theorem5_27_1.lean`, `inducedRepV` on `(G ⧸ stab) → U`), each cost a build cycle:
- **`set P := (Π i : Fin k, Matrix …)` makes the Pi ring structure opaque to `simp`/`rw` (Wedderburn/matrix-product-algebra proofs — #6652, `Chapter3/Problem3_9_5.lean` `odd_isSumMatrixAlgebra`, sorry-free).** After `set P := … with hPdef`, `P` is a *local `let`-constant*, so (a) `simp [Pi.add_apply, Pi.mul_apply, Pi.single_apply, …]` on a goal like `(e0 + e1) i = (1 : P) i` fires **nothing** — the `+`/`*`/`1` live at the opaque type `P`, not the literal Pi type — until you unfold the let with **`simp +zetaDelta [Pi.mul_apply, …]`** (zetaDelta unfolds `let`-bound fvars; then default `Pi.single_eq_same`/`one_mul` close it, so the extra `Pi.*` args are usually redundant — the linter flags them). (b) `rw [hPdef]` to turn `Module.finrank ℂ P` into the Pi type **fails with "motive is not type correct"** (finrank's `Module`/`AddCommMonoid` instance argument depends on `P`); instead `change Module.finrank ℂ (∀ i : Fin k, Matrix (Fin (d i)) (Fin (d i)) ℂ) = _` (defeq, no instance abstraction) then `rw [Module.finrank_pi_fintype, Fin.sum_univ_two]`. Style linter: use `change`, not `show`, for these defeq goal restatements. For the `dᵢ = dⱼ` step, transport an algebra automorphism `ψ : P ≃ₐ P` (e.g. from the grade involution) with `ψ e0 = e1`, then `Submodule.map (ψ.toLinearEquiv : P →ₗ P) (range (mulLeft e0)) = range (mulLeft e1)` gives `finrank` equality via `LinearEquiv.finrank_map_eq` (rewrite it *in the hypothesis*, `rw [hmap] at hfm`, to dodge the same motive trap); each coordinate ideal `range (mulLeft (Pi.single i 1))` has `finrank = dᵢ²` (`= range (LinearMap.single ℂ _ i)`, `finrank_range_of_inj` + `ker_single` needs explicit `(R := ℂ) (φ := …)`, then `Module.finrank_matrix`). Assemble the final product with `RingEquiv.piFinTwo` (→ `AlgEquiv.ofRingEquiv … (fun _ => rfl)`), `Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)`, `LinearMap.toMatrixAlgEquiv'.symm`, `AlgEquiv.prodCongr`. Linear identities over two algebra generators (`1`, `e univ`) close with the `module` tactic (needs `import Mathlib.Tactic.Module`) after `smul_mul_smul_comm` eliminates the products.
- **Carrier-vs-function-type friction.** `inducedRepV φ χ U := FDRep.of (V := (G ⧸ H) → U) …`, so its carrier `↑(inducedRepV φ χ U).V` is *defeq* but not *syntactically* equal to `(G ⧸ H) → U`. Mixing the two breaks `rw`/`simp`: feeding a literal `Pi.single q₀ u` into `weightSpace`'s `LinearMap.id`/`LinearMap.sub_apply` machinery (carrier instances) clashes with `A_action_scalar`/`inducedRepV_A_apply` (which type `f : (G ⧸ H) → U`), giving `AddCommMonoid` mismatch / "target not type-correct under instances". Fixes: (a) **prefer the function-level A-eigenvalue equation** `ρ⟨a,1⟩ f = χ(a) • f` over `weightSpace` membership — the proven idiom (see `inducedRepV_orbit_injectivity`'s `haction_f`); (b) keep the eigenvector as a `set f₀ : (G ⧸ H) → U := Pi.single q₀ u` **function-typed local**, not a bare literal in a carrier slot; (c) an *opaque* carrier term `T f₀` (output of a `LinearEquiv`) feeds `A_action_scalar φ χ U a (T f₀) q` fine — only literal `Pi.single` with baked instances bites.
- **`ShortComplex.moduleCatMk f g h` projections don't reduce syntactically (#6012, Ch7 Ex 7.8.4).** `(moduleCatMk f g h).X₂`, `.f`, `.g` are *defeq* to `ModuleCat.of R …` / `ModuleCat.ofHom f` but not syntactic, so any `rw`/`simp`/literal on them stalls: a bound `x₂ : ↑(moduleCatMk …).X₂` makes `omega` bail (not seen as `ℤ`) and a numeral in that type throws `failed to synthesize OfNat (↑… .X₂) 2`; `rw [ShortComplex.moduleCatMk]` fails ("no equation lemmas" — it's a plain `def`). Working recipe: (a) prove short-exactness via the **`.hom`/LinearMap-level** lemmas `moduleCat_exact_iff_ker_sub_range`, `mono_iff_injective`, `epi_iff_surjective`, and open each with **`change` to the honest goal** (`change LinearMap.ker g ≤ LinearMap.range f`, `change Mono (ModuleCat.ofHom f)`) so everything downstream is stated on the real `ℤ`/`ZMod n` maps; (b) prove the arithmetic core as a plain `Function.Injective f`/`Surjective g` on genuine-typed inputs, then transfer (`exact fun a b hab => hinj hab` — `⇑(ofHom f) a` is defeq `f a`); (c) to use a splitting/retraction morphism as a real map, bind `let ρ : ℤ →ₗ[ℤ] ℤ := sp.r.hom` (defeq accepts it) and feed `ModuleCat.hom_ext_iff.mp sp.f_r` (rewritten by `hom_comp`/`hom_id`) to `DFunLike.congr_fun` — all subsequent linearity/omega then lives in honest `ℤ`. For part (i) "SES of vector spaces splits", `ShortComplex.ShortExact.splittingOfProjective` closes it outright (`Module.Free.of_divisionRing` → `Projective.of_free` → the ModuleCat projective instance are all found automatically).
- **`MulAction G (G ⧸ stab)` instance fails on `⟦1⟧` literals.** `g • (⟦(1:G)⟧ : G ⧸ stab)` errors `failed to synthesize HSMul G (Quotient (QuotientGroup.leftRel …))` — the instance is keyed on `HasQuotient.Quotient`, and the `⟦·⟧`/`Quotient.mk` head doesn't match. Use **`QuotientGroup.mk (1 : G)`** (its result type *is* the `HasQuotient` form) everywhere the base coset is smul'd. (A variable `q : G ⧸ stab` smul's fine; only the literal is poisoned. `set q₀ := ⟦1⟧` dodges the smul error, but a `set` fvar then won't `rw`-match a lemma stated with raw `mk`, so for cross-lemma `rw` keep `QuotientGroup.mk (1:G)` raw, no `set`.)

Gotchas that each cost a build cycle:
1. **`@[simp] a_zero : (a 0 : QuaternionGroup n) = 1`** (and `DihedralGroup.r_zero`, etc.) silently rewrites the identity element under any `simp`/`norm_num`, so a per-element value lemma keyed on `a 0` stops matching (the term becomes `1`). Use **`norm_num [-QuaternionGroup.a_zero, …]`** (or `simp only` with an explicit list that excludes it). Watch the dual: `FDRep.char_one` (`χ 1 = finrank`) then fires on the `1` and derails a 2-dim trace computation.
2. **`revert i j; decide` for a finite-`ZMod` parity/arithmetic fact reverts *everything* depending on `i,j`** — including a `have e : … = …` whose RHS mentions ℂ-valued vars (α, β), making the reverted goal non-decidable (`decide` errors "expected type must not contain free variables"). **Compute the decidable fact into a `have hp := by revert i j; decide` BEFORE introducing any ℂ-valued `have`.**
3. **`fin_cases i` produces `⟨0, ⋯⟩`, which does *not* reduce `![…] ⟨0,⋯⟩` / table lookups under `simp`/`norm_num`** (the `Matrix.cons_val_*` simp lemmas are keyed on the numeral `0`, not `Fin.mk 0`), but it *does* reduce by **defeq**. So per-cell character-matching proofs should `change <defeq-reduced LHS> = <defeq-reduced RHS>` (e.g. `change chiFun 1 1 (a 0) = Q5toC (1:Q5)`) and then finish — `change` bridges via defeq where `simp` stalls. Assembling the indexed lemma (`irrep i …` for `i:Fin 5`) from per-row lemmas is a clean `fin_cases i` + `exact char_row0 j` (the `exact` matches `⟨0,⋯⟩` to the `0`-literal lemma by defeq).
4. **A bare `Matrix.single 0 0 1` defaults its *index* type to `ℕ`** (giving `Matrix ℕ ℕ …`), so a lemma such as `⁅Matrix.single 0 0 1, Matrix.single 0 1 1⁆ = …` errors with `failed to synthesize Bracket (Matrix (Fin 2) …) (Matrix ℕ …)` unless *every* occurrence is ascribed. Fix once with a reducible `private abbrev e11 : Matrix (Fin 2) (Fin 2) k := Matrix.single 0 0 1` (the ascription pins the indices) and use `e11 k` everywhere. Follow-up gotcha: `rw [Matrix.single_mul_single_*]` will **not** match through the abbrev (the term stays folded as `e11 k * e12 k`), so prove the matrix-unit bracket facts with `simp [e11, e12, LieRing.of_associative_ring_bracket, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h]` (those single-mul lemmas are `@[simp]`; pass the `(1 : Fin 2) ≠ 0` side fact `h` explicitly). Worked example: `Chapter2/Problem2_16_2.lean` (`bracket_e11_e12`, `bracket_expand`, `instIsSolvable` for the matrix Lie algebra `⟨X,Y | [X,Y]=Y⟩`). Note `LieAlgebra.ofAssociativeAlgebra` is a *global* instance that fires off the local `attribute [local instance 100] LieRing.ofAssociativeRing`, so `smul_lie`/`lie_smul` (k-bilinearity) and the `module` tactic are available on matrices with no extra setup.
5. **`Finsupp` multi-index work over `ℕ` (MvPolynomial coefficient / Frobenius-character-formula proofs — `Chapter5/Problem5_16_1.lean` `res_charValue_sum`) has four recurring traps, each cost a build cycle:** (a) **`(f - g) a` for `ℕ`-valued Finsupps is `Finsupp.tsub_apply`, not `Finsupp.sub_apply`** (ℕ is not a group; subtraction is truncated) — `sub_apply` fails with "did not find pattern". (b) **`Finsupp.single i 1` with a bare `1` leaves the value-type a metavariable**, so `(D - Finsupp.single i 1) j` errors `Function expected at D - fun₀ | i => 1 … type ?m` (the Finsupp coe can't fire on an unresolved type) — always write **`Finsupp.single i (1 : ℕ)`**. (c) **`set foo := fun i h => …` (a function-valued `set`) does NOT beta-reduce under `rw [hfoo]`**, so a downstream `rw`/simp-lemma keyed on the unfolded head (e.g. `bpDecr_parts` matching `(bpDecr …).parts`) won't fire — use **`simp only [hfoo]`** (simp beta-reduces) to unfold, or add a `have foo_parts : ∀ …, (foo i h).parts j = … := by simp only [hfoo, …]` helper and rewrite with *that*. (d) **`Finsupp.coe_equivFunOnFinite_symm` will unfold a `set`-bound Finsupp variable** (`D := equivFunOnFinite.symm …`) mid-`rw`-chain because `⇑D` reduces to `⇑(equivFunOnFinite.symm …)`, breaking a later `rw [hDval]` (`hDval : D i = …`) — prove per-side value lemmas (`hL`/`hR`) with the coe applied *once* and `rw [hL, hR]` instead of a long shared chain. Also: **`subst h` where `h : x = c` and `c` is a lemma/def *parameter* silently eliminates the parameter** (replacing it by `x`), then `c` is `Unknown identifier` downstream — avoid `subst` when either side is a fixed binder; use `rw [h]` / explicit `if_pos`/`if_neg`.
6. **Computing an explicit `n×n` sparse integer determinant (`!![…]`, e.g. E-type Cartan matrices, `Chapter6/Problem6_1_3_continued_E7_E8.lean` `det_cartan_E6/E7/E8`) — the naive `simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]` expands to all `n!` cofactor terms (E₈ = 40320) and either blows `maxSteps` after minutes or leaves un-evaluated `Fin.succAbove k j`; `norm_num [Fin.succAbove, Fin.lt_def]` in the same pass then times out at `isDefEq`.** The fix is a **two-stage prune-then-clean** tactic (write it once as a `macro`, apply per matrix): **Stage 1** `simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const, mul_zero, zero_mul, add_zero, zero_add, neg_zero, mul_neg, neg_neg, mul_one, one_mul, pow_zero, pow_succ]` — the point is `Fin.succ_succAbove_succ`/`Fin.succ_succAbove_zero`/`Fin.zero_succAbove` reduce `succAbove` *symbolically* in `0`/`.succ` form (no `if`/`Fin.lt_def` `isDefEq` cost), so `Matrix.cons_val_succ` evaluates each entry and the `zero_mul`/`mul_zero` lemmas **prune the zero cofactors before the tree reaches `n!`** (E₈ collapses to a handful of nonzero paths). **Stage 2** `<;> norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.head_fin_const, Matrix.vecHead, Matrix.vecTail]` — the *now-small* residual has a few `succAbove` indices that Lean's `Fin` numeral simproc left as literals; unfolding `Fin.succAbove`/`Fin.lt_def` here is cheap and finishes the ℤ arithmetic. Get the `!![…]` literal for `2•1 - adj` first via `have hC : cartan t = !![…] := by ext i j; fin_cases i <;> fin_cases j <;> decide`. Whole E₆/E₇/E₈ set runs in ~15 s each at **default heartbeats** — no `set_option maxHeartbeats` needed. Do **not** try `decide` on `Matrix.det` (hits `maxRecDepth`/kernel blowup) or a single combined `simp` with `Fin.succAbove` unfold (the `isDefEq` blowup returns).
7. **Stating a fresh lemma/`have` equating dependent `Fin`-tuple builders of a *composite* — `Fin.init (Fin.cons a g) = Fin.cons a (Fin.init g)`, `Fin.tail (Fin.snoc B x) = …` — fails to even elaborate** with a motive mismatch like `Fin.cons … has type Fin (n+1) → A but is expected to have type (i : Fin ?) → ?α i.castSucc`. `Fin.init`/`Fin.tail` return the *dependent* type `α i.castSucc`/`α i.succ`, and Lean won't unify the two (defeq-equal, syntactically-different) constant-family motives at the `Eq` layer; a `(… : Fin n → A)` ascription on one side does **not** fix it. **Do not state these as standalone equations.** Instead (a) prove a *generic* helper over an opaque tuple variable `u` (e.g. `contractNth_castSucc_eq_snoc (u : Fin (m+2) → A) : … Fin.init u …` — `Fin.init u` of a *variable* elaborates fine), then apply it inside a `rw` where the goal is already well-typed; or (b) do the rewrite *within* the well-typed goal via `rw`/`conv` (subterms coming from applied `@[simp]` lemmas carry a concrete type), reducing tail-of-snoc etc. with `Fin.tail_init_eq_init_tail`, `Fin.init_snoc`, `Fin.snoc_castSucc`/`snoc_last`, `Fin.snoc_apply_zero`; or (c) when you must name the value, restrict to a plain-function `have` (`(fun i => cons a g i.castSucc) = …`) proved pointwise by `funext`+`Fin.cases`. Worked example: `Chapter8/BarResolution.lean` (`barFace_comp_barFace`, its snoc helpers, and cases B/E). Mathlib has **no** `Fin.init_cons`/`tail_snoc`.
8. **Extracting a single entry of the Cartan matrix `2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj` (pervasive in Chapter 6, `Problem6_1_3_continued_tildeE.lean`)** — do **not** put `two_nsmul` in the simp set alongside `Matrix.smul_apply`/`Matrix.one_apply`: `two_nsmul : 2•a = a+a` fires on the matrix-level `2 • 1` *before* the entry is extracted, leaving an unsolvable `(1 + 1) i j` (matrix addition, not scalar `2`). Extract first, scalarize last: `rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul]; split_ifs <;> norm_num` gives the clean `M i j = (if i = j then 2 else 0) - adj i j`. **Reusable affine-Dynkin proof pattern** (`affineNullVector_pos`, step 1 of the affine classification #6785): the positive kernel generator (discrete Perron–Frobenius) is (a) fold `w = |x|` from the degeneracy null vector — termwise `wᵢ Mᵢⱼ wⱼ ≤ xᵢ Mᵢⱼ xⱼ` (via `abs_mul_abs_self` on the diagonal, `nlinarith [mul_nonneg ha (sub_nonneg.mpr hb)]` off-diagonal) gives `A(w) ≤ A(x) = 0`, and `hpos w` pins `A(w)=0`; (b) **integer** polarization at `Pi.single k 1`: `A(t•w + eₖ) = 2t(A·ᵥw)ₖ + 2 ≥ 0` for all `t:ℤ` — the `t²` term vanishes because `A(w)=0`, so evaluating at `t = ±2` and `omega` forces `(A·ᵥw)ₖ = 0` (no need to go to ℚ); (c) strict positivity from irreducibility — the zero-set of `w` is adjacency-closed (`2wₚ = ∑ⱼ adjₚⱼ wⱼ`, all terms `≥ 0`), and the `SimpleGraph`/`Relation.ReflTransGen` connectivity block (copy verbatim from `isDynkinDiagram_isTree` in `Problem6_1_3_continued_E7_E8.lean`) propagates `w=0` to the `x≠0` witness. Bilinear symmetry `uᵀMv = vᵀMu` is a 3-line `Bform`+`Finset.sum_comm`+`hMsym_ij` (needs only `adj` symmetric), avoiding `Matrix.IsSymm` transpose gymnastics.

### Sorry Decomposition as Primary Strategy

In endgame, **decomposing a hard sorry into 2-4 smaller sorries is often more valuable than attempting the hard sorry directly.**

**When to decompose (not attempt directly):**
- Difficulty ≥ 7 and no clear single-session proof strategy
- The proof has independent sub-cases or sub-lemmas
- Multiple agents could work on different sub-sorries in parallel

**How to decompose well:**
1. Code the proof framework with `sorry` placeholders for each independent step
2. Each sorry should have a clear mathematical description in a comment
3. Each sorry should be independently attackable (no circular dependencies between sub-sorries)
4. Create issues for each sub-sorry with proper `depends-on` relationships

**Evidence:** Problem6_1_5_theorem (1→0), Theorem2_1_2 (1→2 smaller), InfiniteTypeConstructions (0→4 targeted), PolytabloidBasis (3→0 via restructure) — all used decomposition as the winning strategy.

### "Discharge the sorry in file X" can require a Core split (import-cycle trap, #6501)

An *assembly* issue whose verification demands `file X` be sorry-free often needs lemmas that live in a **downstream** file — one that `import`s `X`. You cannot `import` that file back into `X` (cycle), so the sorry in `X` looks un-fillable in place. Before writing any proof, check the import direction of every ingredient the reduction consumes: `grep -rln "import .*X" EtingofRepresentationTheory/` and read the sorried helper file's `import` lines. If a needed helper file imports `X`, the fix is a **Core split**, not a heroic inline proof:

1. Move `X`'s *upstream* definitions (the ones the downstream/helper file actually uses — the coordinate ring, the action, the invariant object, the grading lemmas) into a new `X_Core.lean` (imports only `Mathlib`).
2. Repoint the downstream/helper file's `import …X` → `import …X_Core`.
3. Rebuild `X.lean` as the *assembly*: `import X_Core` + the (now-non-cyclic) helper files, keeping the headline theorems there so the problem's named result still lives in `X.lean`.
4. Add `X_Core` (and any newly-imported helper) to the `Chapter?.lean` aggregator.

Deliberately keep the deep *sorried* dependency (e.g. a range-identification/surjectivity lemma) **out** of `X.lean` — it stays in the downstream file so `X.lean` is genuinely sorry-free while still consuming it (a sorried dependency is not a blocker). Worked example: `Chapter5/Problem5_24_2.lean` (#6501) — extracted `Problem5_24_2_Core.lean`, repointed `Problem5_24_2_Bridge.lean` to Core, and assembled the First Fundamental Theorem sorry-free on top of two sorried upstream lemmas.

**Step 2 (repointing) silently drops transitive imports the downstream file relied on.** When the downstream file `import`ed the *full* `X`, it inherited everything `X` transitively imported (other `Definition*`/`RightExact` project files and Mathlib instance modules). Repointing to a *narrow* `X_Core` (which imports far less) removes those, and the downstream file fails on the FIRST rebuild with `Unknown identifier`/`failed to synthesize instance` errors for lemmas/instances it never named a direct import for. The fix is mechanical: read each error, add the missing `import` directly to the downstream file (or to `X_Core` if several downstream files need it). Concretely (#6588, splitting `Problem8_2_6_Core` out of `Problem8_2_6` so `TensorProjectiveExact` could import Core): `TensorProjectiveExact` had silently relied on `Problem8_2_6`'s chain for `Definition8_2_3_RightExact` (the `tensorOver_hom_ext`/`homEquivInvFun` helpers) and for `Mathlib.Algebra.Category.ModuleCat.Colimits` (`PreservesFiniteColimits (forget₂ (ModuleCat R) AddCommGrpCat)`, needed by `ShortExact.map_of_exact`) — both had to be added explicitly. Budget one or two build cycles for this; `grep -oE '^import ' | wc -l` before/after to sanity-check you didn't over-narrow. Worked example: `Chapter8/Problem8_2_6_Core.lean` (#6588) — the second-argument tensor functoriality (`tensorSndMap`/`tensorRightNatTrans`/`torSndMap`/`tensorLeftFunctor`) extracted so the flatness lemma (in downstream `TensorProjectiveExact`) could feed the (iii)-Tor long exact sequence proof back in `Problem8_2_6`.

### Recording an out-of-reach claim when sorry is disallowed (fidelity sweeps)

Fidelity-review issues (epic #5338) often say "prove conjunct X, no sorry/nd; if out of reach, add an explicit scope note rather than silently dropping it." That bans both a sorried theorem *and* pure prose. The lever that satisfies both: **record the precise claim as a `Prop`-valued `def` against the real objects already in the file** — e.g. `def Foo_irreducible (n) : Prop := ∀ W : Submodule …, (∀ g : V ≃ₗ[k] V, … stable under the actual GL(V)-action …) → W = ⊥ ∨ W = ⊤`. A `Prop`-def *asserts nothing* (it names a statement, can't be `exact`ed as a proof), so it is not a vacuous/false claim and not a sorry; it pins the exact formulation the tracking issue must discharge, against the concrete action maps (no drift). Pair it with a one-paragraph section docstring stating the book's proof strategy + the concrete obstruction + the tracking issue. Also land any genuinely-provable *sub*-conjunct in the same PR (e.g. the parenthetical `∧ⁿV = 0` for `n > dim V` via `exteriorPower.finrank_eq` + `Module.finrank_zero_iff`) so the PR carries real proved content, not just a recorded statement. Worked example: `Chapter5/Example5_19_3.lean` (#5638 → statements `Example5_19_3_symmetric_irreducible`/`_exterior_irreducible` pinned, vanishing proved; full proof tracked in #5715).

### When to Accept a Long-Term Sorry

Some sorries may represent genuinely hard formalization work beyond current Mathlib infrastructure. Accept them when:
- The sorry requires 200+ lines of new mathematical infrastructure not in Mathlib
- 3+ agents have attempted different approaches and all failed
- The sorry is not blocking other items (leaf node in dependency graph)

**Before accepting "needs Mathlib infra X" — check whether the *statement* was generalized past the book's standing conventions, manufacturing the blocker.** A repeatedly-skipped sorry whose deferral cites missing heavy infrastructure (Bass/perfect rings, Krull–Schmidt, Schur–Weyl, …) is often an artifact of a prior "fidelity"/generalization edit that dropped the book's running hypotheses. Etingof Ch8 assumes **finite-dimensional** algebras and modules throughout; under that hypothesis the proof is usually elementary and *more* faithful than the general statement. Concretely (#5474, Example 8.1.7): four sessions skipped the converse `P*` injective ⟹ `P` projective as blocked on Bass (flat ⟹ projective over a perfect ring) + Lambek for the k-dual — both absent from Mathlib — because the statement had been generalized to *arbitrary* `P`. Restricting to finite-dimensional `P` (the book's actual setting) collapses it to: split the dual of a finite free cover using injectivity of `P*`, then transport the section back through the finite-dimensional evaluation iso `P ≃ P**` (`Module.evalEquiv`) — no Bass, no flatness. This *narrowing* toward the book's conventions is the opposite of the line-103 "don't widen the goal unilaterally" trap, and it is the correct move, not the owner's-call deferral the skip comments assumed: re-add the dropped standing hypothesis (`[FiniteDimensional k A]`, `[FiniteDimensional k P]`), prove it, and note in the docstring why dropping it would need the absent infra. (Watch the universe side-condition the restriction can expose: `Module.Injective.extension_property`'s `[Small.{uM} R]` is free once `k A P : Type u` share one universe.)

**Current long-term candidates (Wave 49):**
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (difficulty 8)
- `basic_morita_algEquiv` — requires Krull-Schmidt theorem (not in Mathlib)
- 3× `*_isIndecomposable` proofs — may require explicit matrix computation

**Never accept a sorry silently.** Document it in an issue with: what's needed, why it's hard, and what would unblock it.

## Translation Pipeline

Formalizing an item follows three stages: **translate**, **scaffold**, **prove**.

### 1. Translate: Natural Language to Formal Statement

Read the item's blob text and its `.refs.md` file (Mathlib coverage + external sources). Then:

1. **Identify the Mathlib types.** Check `.refs.md` for exact/partial matches. For exact matches, use the Mathlib declaration directly. For partial matches, read the Mathlib source to understand the gap.
2. **State the theorem/definition.** Write the Lean signature with `sorry` as body. Include a docstring with the book's natural language statement.
3. **Check it compiles.** Run `lake env lean <file>` — fix import and type errors before proceeding.

**Common pitfalls:**
- **No `-/` inside doc-comments.** A stray `-/` sequence in prose (e.g. writing `one-/two-sided`, or `f⁻¹/g`) closes the `/-! … -/` or `/-- … -/` block early, and the remaining text is parsed as commands — producing baffling "unexpected identifier; expected command" errors far from the real spot. Reword to `one- or two-sided`. Likewise avoid an accidental `/-` opening a nested comment.
- **Never use `λ` as a bound-variable name.** In Lean 4 `λ` is the reserved lambda keyword, so `fun λ => …`, `∑ λ ∈ s, …`, or `(λ : Nat.Partition n)` all produce cryptic parse errors (`unexpected token '=>'`, `unexpected token 'λ'`). This bites constantly in the partition/Young-diagram chapters where `λ` is the natural mathematical name — use `la` (the codebase convention) or `lam`. The book's `λ` in prose inside doc-comments is fine.
- **No combining-diacritic identifiers.** A name whose diacritic is a *combining* Unicode codepoint — e.g. `g̃` (`g` + U+0303 combining tilde), `x̄`, `f̂` — does not tokenize as an identifier: Lean reports `expected token` / `Missing cases` at the `let`/`have`, far from the real cause. Use a plain ASCII suffix (`glift`, `xbar`, `fhat`) for locally-introduced names.
- Don't invent type classes. If Mathlib doesn't have a concept, use a `structure` or `def` with explicit fields.
- Don't use `True` as a placeholder for propositions — it compiles but hides the real requirement.
- Check that universe levels are consistent. Representation theory often needs `Type*` not `Type`.
  - **The `Sₙ`-classification comes in a `Type 0` and a universe-polymorphic flavour — pick by the deliverable's universe (#6284).** `Etingof.Theorem5_12_2_classification` is stated for `M : Type` (Type 0) over ℂ and lands in `SpechtModule n la`. A deliverable/consumer with `{V : Type*}` (e.g. anything about `ρ.asModule` for `ρ : Representation ℂ (Equiv.Perm (Fin n)) V`, `V : Type*`) **cannot** use it — its simple submodules `↥W` inherit `V`'s universe. Use `Etingof.classification_general_u ℂ n (W : Type _)` (in `Theorem5_12_2_ClassificationGeneral.lean`; `M : Type w`, needs `[IsAlgClosed k] [CharZero k]`, ℂ qualifies) which lands in `SpechtModuleK ℂ n la`. Bridge to the ℂ Specht API with `SpechtModuleK ℂ n la = SpechtModule n la` via `unfold SpechtModuleK SpechtModule; rw [YoungSymmetrizerK_eq_mapRange ℂ n la, YoungSymmetrizer_eq_mapRange n la]` (both public in `Theorem5_22_1.lean`), so ℂ-only lemmas like `sumTranspositions_mul_eq_content_smul` still apply. Maschke's `IsSemisimpleModule (SymGroupAlgebra n) ρ.asModule` is then `inferInstance` (the `Etingof.neZero_card_perm` instance discharges `NeZero (Nat.card Sₙ : ℂ)`). Worked example: `Chapter5/SumTranspositionsEigenvalues.lean`.
- **WF-recursive definitions** (`termination_by`): Don't use `rw [f]` or `simp [f]` to unfold — they fail on WF-recursive functions. Instead, prove a separate `have` using `unfold f` (works inside `conv` blocks), or extract a standalone unfolding lemma.
- **`Finset.prod`/`∏`-style products need `CommMonoid`.** `GL_N k`, `Matrix n n k`, and `Module.End` are non-commutative, so `∏ i, g i` over them does **not** typecheck (`failed to synthesize CommMonoid (GL …)`). For diagonal/torus elements that *do* commute, don't fight the typeclass: induct over the `Finset` with a partial helper (e.g. `diagTorusOn s` = the partial product over `s`, with `_empty`/`_insert`/`_univ` lemmas) and assemble one factor at a time via `map_mul`. See `Chapter5/FormalCharacterTorusTrace.lean`.
- **Diagonalizing a distinct-eigenvalue matrix (conjugate to a diagonal) — full recipe.** Mathlib has no "distinct eigenvalues ⟹ diagonalizable" shortcut; build the eigenbasis. The chain (over an alg-closed field, here `ℂ`): roots of `A.charpoly` ↔ eigenvalues via `Matrix.mem_spectrum_iff_isRoot_charpoly` + `Matrix.spectrum_toLin'` + `Module.End.hasEigenvalue_iff_mem_spectrum`; `0` is not an eigenvalue of a unit via `spectrum.zero_mem_iff` (**`R` is an explicit arg — write `(spectrum.zero_mem_iff ℂ).mp`, not `spectrum.zero_mem_iff.mp`**, else "unknown constant `…mp`"); one eigenvector per eigenvalue is linearly independent via `Module.End.eigenvectors_linearIndependent'` (needs an *injective* eigenvalue family); `N` independent vectors in `Fin N → ℂ` give a basis via `basisOfLinearIndependentOfCardEqFinrank` (**needs `[Nonempty (Fin N)]` — handle `N = 0` separately; `GL_0` is a `Subsingleton`, close with `Subsingleton.elim`**); the column matrix `V := (Pi.basisFun ℂ (Fin N)).toMatrix ⇑b` is invertible via `Basis.invertibleToMatrix`, and `A * V = V * diagonal eigenvalues` follows columnwise from the eigenvector equation (`A *ᵥ vⱼ = tⱼ • vⱼ`), giving `A = V * D * V⁻¹` (`Matrix.mul_inv_of_invertible`). Package `h := unitOfInvertible V` (GL is `abbrev … := (Matrix …)ˣ`, so `unitOfInvertible` *is* a GL element), prove the GL equation via `Units.ext` + `Matrix.GeneralLinearGroup.coe_mul`/`coe_inv`. **Dot-notation gotcha: `f.HasEigenvalue` fails (`LinearMap.HasEigenvalue` does not exist) when `f : … →ₗ[R] …`; annotate `f : Module.End R M` so dot notation resolves to the `Module.End.*` API.** Full worked proof: `Chapter5/DiagonalizableConj.lean` (`gl_conj_diagTorus_of_distinct_eigenvalues`).
- **`tr(A⁻¹) = conj(tr A)` for a finite-order ℂ-matrix (`χ(g⁻¹)=conj χ(g)`, the real-character / Frobenius–Schur ingredient, #5235).** Do NOT build an eigenbasis or unitarise — the charpoly-roots route is shorter and fully constructive. `tr A = (charpoly A).roots.sum` (`Matrix.trace_eq_sum_roots_charpoly`, alg-closed); each root `μ` is an eigenvalue of `Matrix.toLin' A` (`Module.End.hasEigenvalue_iff_isRoot_charpoly` + `Matrix.charpoly_toLin'`), and `(toLin' A)^n = id` (`← Matrix.toLin'_pow`, `Matrix.toLin'_one`) forces `μ^n = 1`, hence `‖μ‖ = 1` and `conj μ = μ⁻¹` (`Complex.inv_eq_conj`). For `tr(A⁻¹)`: `Matrix.charpoly_inv` + `Matrix.reverse_charpoly` give `charpoly A⁻¹ = C(c) * (charpoly A).reverse` (`c ≠ 0`), so `roots = (charpoly A).reverse.roots`. **Mathlib has NO `Polynomial.roots_reverse`** — prove `(reverse p).roots = p.roots.map (·⁻¹)` for monic split `p` with `0 ∉ p.roots` yourself: factor `p = (p.roots.map (X - C ·)).prod` (`Splits.eq_prod_roots_of_monic`), use that `reverse` is multiplicative over a `Multiset` in a domain (induction + `reverse_mul_of_domain`), and `reverse (X - C a) = C(-a)*X + C 1` has the single root `a⁻¹` (`roots_C_mul_X_add_C_of_IsUnit`). To reduce an *endomorphism* trace/inverse to a matrix, use `LinearMap.toMatrixAlgEquiv b` (the basis-version `AlgEquiv`, defeq to `toMatrix b b`): `E (ρ g⁻¹) = (E (ρ g))⁻¹` via `Matrix.inv_eq_left_inv`, and `E (ρ g) ^ orderOf g = 1` via `map_pow`/`map_one`. Reusable helpers landed in `Chapter5/FrobeniusSchurRealType.lean`: `reverse_multiset_prod`, `roots_reverse_X_sub_C`, `roots_reverse_eq_map_inv`, `matrix_trace_inv_eq_conj`, and `character_inv_eq_conj`.
- **Twisting an `sl(2)` (or any Lie-algebra) representation to make `ρ(e)` a chosen operator — conjugation recipe (#5309, single Jordan block of Jacobson–Morozov part (l), `Chapter2/Problem2_15_1_l.lean`).** To turn the irreducible `rhoLieHom n : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ)` into a rep whose `ρ(e)` is a *specific* nilpotent (here the standard shift `J_{0,n}`, `e_k ↦ e_{k-1}`), conjugate by a `LinearEquiv` `φ`: `(φ.conjAlgEquiv ℂ : _ →ₐ[ℂ] _).toLieHom.comp (rhoLieHom n)` is again a `LieHom` (algebra-equiv conjugation `LinearEquiv.conjAlgEquiv` from `Mathlib.Algebra.Algebra.Equiv` preserves the commutator bracket; `AlgHom.toLieHom` lifts it). `conjAlgEquiv_apply` rewrites it to `φ ∘ₗ f ∘ₗ φ.symm`. Since `rhoLieHom n sl2_e` acts as `e_k ↦ k · e_{k-1}` (a single Jordan block already), the diagonal rescaling `φ : e_k ↦ k! · e_k` normalises the subdiagonal coefficients to `1`. **Crucial API constraint: `Sl2Irrep.lean`'s component maps `rhoH/E/F` and `rhoLieHom_sl2_*_eq` are `private`** — you cannot name them from another file. Compute the conjugation on the standard basis instead via the *public* `lie_eq_rhoLieHom` (`⁅x,v⁆ = rhoLieHom d x v`) + `lie_sl2_e_e_basis`/`lie_sl2_f_e_basis`/`lie_sl2_h_e_basis` + `e_basis`, and prove the endomorphism equality with `(Pi.basisFun ℂ (Fin n)).ext` (`Pi.basisFun_apply : … = Pi.single k 1`, defeq `e_basis n k` — bridge with `change`, not `show`, to dodge the style linter). Nilpotency of the shift: a `jordanShift_pow_apply` induction (`(J^m v) k = if k+m<n then v⟨k+m⟩ else 0`) gives `J^n = 0`. **`omega` gotcha: it does NOT unfold `Fin.val` of an explicit `Fin.mk` (`↑⟨a,h⟩` stays opaque)** — feed the nat-level equality directly, e.g. `congrArg v (Fin.ext (show a = b by omega))`, where `a`,`b` are the *reduced* vals. The general nilpotent case (assemble arbitrary `A` over Jordan blocks) needs a Jordan-basis decomposition that is **not** in Mathlib (`JordanChevalley` is only the semisimple+nilpotent split) — tracked in #5312.

- **A single-operator `k[X]`-rep `V_{λ,n}` as a genuine module, and its indecomposability + non-simplicity (#5358, sorry-free in `Chapter2/Example2_3_14.lean`, namespace `Etingof.Example_2_3_14`).** To realize the representation `(kⁿ, ρ(x)=J_{λ,n})` as a real `k[X]`-module, use `Module.AEval' (jordanBlock lam n)` (NOT a hand-rolled module): `X` acts as the operator, `Module.AEval'.of φ : (Fin n → k) ≃ₗ[k] AEval' φ` is the comparison equiv, and `Module.AEval'.X_smul_of`/`Module.AEval.of_aeval_smul` push the action through `of`. **Indecomposability proof pattern (reusable for any operator whose eigenline is 1-dim):** define module-level `IsIndecomposable R M := Nontrivial M ∧ ∀ N P, IsCompl N P → N = ⊥ ∨ P = ⊥`; pull each `k[X]`-submodule `N` back to the `k`-subspace `W := (N.restrictScalars k).comap of.toLinearMap` (then `m ∈ W ↔ of m ∈ N` is `Iff.rfl`), which is automatically `φ`-invariant via `X_smul_of`; show every nonzero invariant `W` contains the eigenvector `e₀` (the engine `e0_mem_of_invariant`: `shift = J − λ•id` is nilpotent — `isNilpotent.restrict` to `W` — and `Module.End.isNilpotent` restricted to a nontrivial subspace has a nonzero kernel vector, which lands in `ker shift ≤ span{e₀}`); two complementary nonzero submodules then both contain `of e₀`, contradicting `hcompl.inf_eq_bot`. **Non-simplicity (n ≥ 2):** the cyclic submodule `span k[X] {of e₀}` is the 1-dim eigenline — every `p • of e₀ = of (p.eval λ • e₀)` by `Module.End.aeval_apply_of_mem_apply_eq_smul` (the eigenvector-aeval lemma, only needs `J e₀ = λ•e₀`) — so `of e₁ ∉` it; combined with `IsSimpleModule ↔ IsSimpleOrder (Submodule …)` (`eq_bot_or_eq_top`) this gives `¬ IsSimpleModule`. Generic helper `exists_mem_ker_of_isNilpotent` (nilpotent endo on `Nontrivial` module ⟹ nonzero kernel vector) is proved by `g` injective ⟹ `g^m` injective ⟹ `g^m = 0` contradicts `exists_pair_ne`. The JNF *completeness* direction (every f.d. indecomposable is some `V_{λ,n}`) is out of scope — book cites Jordan normal form, doesn't prove it.

- **Decomposing an `sl(2)`-module into an internal/external direct sum of irreducibles via Casimir eigenvalues + a dimension count (#5301, sorry-free in `Chapter2/Problem2_15_1_m_Module.lean`; the Clebsch–Gordan iso `V_λ ⊗ V_μ ≅ ⨁_k V_{λ+μ−2k}`).** The generic Casimir infrastructure is **already built in `Chapter2/Problem2_15_1_complete_reducibility.lean`** — do NOT rebuild it: `casimir M : Module.End ℂ M` (`= EF+FE+H²/2` via `toEnd`), `casimir_apply`, `casimir_highest_weight` (value `μ(μ+2)/2` on an `E`-killed `H`-eigenvector), `casimir_central`/`commute_casimir_toEnd`, and `casimirGenEigenspace a : LieSubmodule ℂ sl2 M` with `casimirGenEigenspace_iSupIndep`. **Assembly recipe** (indexing summands by `k : Fin (min λ μ + 1)`): (1) each summand `N k := LieSubmodule.map (cgLieHom k) ⊤` sits in a distinct Casimir eigenspace — for `w = cgLieHom v`, `casimir M w = cgLieHom (casimir V_ν v) = s_k • w` via a one-line `casimir_comp_lieHom` (`casimir` is natural in Lie-module homs: `simp only [casimir_apply, map_add, map_smul, LieModuleHom.map_lie]`) plus `casimir` on the irrep is a scalar (`casimir (Fin (n+1)→ℂ) = n(n+2)/2 • 1`, got by rewriting `toEnd → rhoLieHom` — proved by `LinearMap.ext`+`toEnd_apply_apply`+`rfl` — and applying `casimir_eq_scalar_lambda`); (2) **independence** `iSupIndep N` = `(casimirGenEigenspace_iSupIndep.comp hginj).mono hle`, where `hginj` is injectivity of `k ↦ s_k` (from the project's `casimir_scalar_inj`) and `hle : N k ≤ casimirGenEigenspace s_k`; (3) **exhaustion** `⨆ N k = ⊤` by finrank: `LinearEquiv.ofInjective (DirectSum.coeLinearMap P) (hindep.dfinsupp_lsum_injective)` composed with `LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap)` gives `⨁ P ≃ₗ ↥(⨆ P)`, so `finrank ↥(⨆ P) = Module.finrank_directSum = Σ finrank (N k) = (λ+1)(μ+1) = finrank M`, then `Submodule.eq_top_of_finrank_eq`; (4) `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` for the internal form, or assemble the **external** `≃ₗ⁅ℂ,sl2⁆ ⨁` by `Φ := DirectSum.toModule ℂ _ M (fun k => (cgLieHom k).toLinearMap)`, prove it's a Lie hom with the project-local `lieHomOfGens`/`map_lie_of_gens` (reduce to `h,e,f` and each generator via `DirectSum.linearMap_ext` → the componentwise bracket `⁅x, lof k w⁆ = lof k ⁅x,w⁆`), surjective (`range ⊇ each N k`, and `⨆ N k = ⊤`), hence bijective by finrank (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`), packaged as a `LieModuleEquiv` via `{ LinearEquiv.ofBijective … with map_lie' := … }`. **Gotchas:** `⨁` needs `open scoped DirectSum`; the direct-sum Lie-module *instance* needs `import Mathlib.Algebra.Lie.DirectSum`; `DirectSum.ext` can't infer its family under `refine` — use `apply DirectSum.ext; intro j` (unifies the conclusion first); `FiniteDimensional ℂ (⨁ …)` is not automatic — supply `Module.Finite.equiv (DirectSum.linearEquivFunOnFintype ℂ _ _).symm`; and importing `complete_reducibility` brings in a generic `sl2_decomp`, so delete any local copy to avoid a duplicate-declaration clash.

- **A generators-and-relations algebra `A = k⟨g,x⟩/(rels)`, its finite-dim modules, and `Ext¹≠0`/one-block (#5722, sorry-free in `Chapter9/Problem9_3_2.lean`).** Full reusable recipe for "construct a specific f.d. algebra and study its modules/blocks". **Algebra:** `A := RingQuot Rel` over `FreeAlgebra ℂ (Fin n)`; give `Rel` as an **inductive** Prop (one constructor per relation, e.g. `| anticomm : Rel (fg*fx + fx*fg) 0`) so multiple relations coexist; each relation lemma is `have h := RingQuot.mkAlgHom_rel ℂ Rel.<ctor>; simp only [map_add, map_mul, map_zero/one] at h; exact h` (do NOT `simpa using`, it over-simps the goal — `g`,`x` are `def`s, close by defeq `exact`). **Representation→module:** `repHom (G X : Module.End ℂ V) (hrels) := RingQuot.liftAlgHom ℂ ⟨FreeAlgebra.lift ℂ ![G,X], by intro a b r; induction r with | … => simp only [map_*, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero, Matrix.cons_val_one] ; exact h…⟩`; then `Module A V := Module.compHom V ρ.toRingHom` (the instance `Module (Module.End ℂ V) V` exists; `a • v = ρ a v` holds **by `rfl`** — expose it as `smul_def`). `repHom_g`/`repHom_x` (`repHom … g = G`) close by `simp only [repHom, g, mk, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply, Matrix.cons_val_*]`. **A-linear maps from a `ℂ`-linear `φ` intertwining only `g`,`x`:** generators generate `A`, so prove `∀ a v, φ (ρV a v) = ρW a (φ v)` by `obtain ⟨w,rfl⟩ : ∃ w, mk w = a := RingQuot.mkAlgHom_surjective ℂ Rel a; induction w with` `grade0` (use `mk.commutes`/`ρ.commutes` + `Module.algebraMap_end_apply` + `map_smul`), `grade1` (`fin_cases i` → the two hyps), `mul`/`add` (`simp only [map_mul/add, Module.End.mul_apply/LinearMap.add_apply] at *; rw [ha, hb]`); package as `mkAlgLinear` building `V →ₗ[A] W` with that as `map_smul'`. **Type-synonym carriers (CRUCIAL gotcha):** when two modules share an underlying type (e.g. both `≅ ℂ`), make them distinct `def Splus := ℂ` (NOT `abbrev`, else the two `Module A` instances clash) and supply EVERY instance via `inferInstanceAs` (`AddCommGroup`, `Module ℂ`, **and** `Nontrivial`, `NoZeroSMulDivisors` if used downstream); the synonym has NO `One`/`OfNat`, so never write `(1 : Splus)` — use a generic `obtain ⟨a, ha⟩ := exists_ne (0 : Splus)`; prove apply-lemmas by `rfl`, never `rw` through the synonym (coercion mismatch). For a carrier used only once (e.g. `ℂ²`), just use `abbrev Pplus := Fin 2 → ℂ` and `Matrix.toLinAlgEquiv'` for the operators (relations close by `simp only [← map_mul, ← map_add]; rw [<matrix identity via ext;fin_cases;simp [Matrix.mul_apply, Fin.sum_univ_two]>, map_zero/one]`). **1-dim simplicity:** `IsSimpleModule A V` from `hsimp : IsSimpleModule ℂ V := isSimpleModule_iff_finrank_eq_one.mpr (Module.finrank_self ℂ)` (import `RingTheory.SimpleModule.Rank`) via `refine { exists_pair_ne := ⟨⊥,⊤,bot_ne_top⟩, eq_bot_or_eq_top := fun N => ?_ }; rcases hsimp.eq_bot_or_eq_top (N.restrictScalars ℂ) …` then `Submodule.restrictScalars_injective ℂ A V` + `restrictScalars_bot/top` (needs an `IsScalarTower ℂ A V` instance, one-liner: `⟨fun c a v => by show ρ (c•a) v = c • ρ a v; rw [map_smul]; rfl⟩`). **Ext¹(S₃,S₁)≠0 from a nonsplit SES** `0→S₁→S₂→S₃→0`: build `ses := ModuleCat.shortComplexOfCompEqZero f g hcomp` + `ses_shortExact := ModuleCat.shortComplex_shortExact ses <Function.Exact f g> <inj f> <surj g>` (prove these as pure `LinearMap` facts, NOT through the ModuleCat coercion); then `ses_shortExact.extClass ≠ 0` because a vanishing class lifts `𝟙 S₃` through `g`: `obtain ⟨x₂,hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ ses.X₃ ses_shortExact (Abelian.Ext.mk₀ (𝟙 _)) (n₁:=1) rfl (by rw [heq, Abelian.Ext.comp_zero])`, `obtain ⟨h,rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).surjective x₂`, `rw [Abelian.Ext.mk₀_comp_mk₀] at hx₂`, `mk₀`-injective gives the section `h ≫ ses.g = 𝟙`, contradicted by module-level `A`-linearity (apply `.hom` to an element via `congrArg (fun φ => φ.hom s) hsec; simpa [ses, ModuleCat.shortComplexOfCompEqZero, ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_ofHom]`). `DirectlyExtLinked` = `nontrivial_of_ne _ _ extClass_ne_zero`; `AreLinked` = `Relation.EqvGen.rel _ _ (Or.inl (Or.inl …))`.
- **Frobenius-Schur trace identity `FS(ρ) = |G|⁻¹ ∑ χ(g²) ∈ {±1}` for self-dual simple ρ (#5261).** Work on `V ⊗ V` with `T = tprod ρ ρ` and the swap `cm = TensorProduct.comm`, NOT bilinear forms (the swap is then a clean permutation matrix). The chain (all sorry-free in `Chapter5/FrobeniusSchurTraceIdentity.lean`, reuse before rebuilding): (1) `tr(swap·(A ⊗ₖ A)) = tr(A·A)` — `Matrix.trace` + `Fintype.sum_prod_type` (one diagonal entry is `(A⊗ₖA)(Prod.swap p) p` via `Finset.sum_eq_single` on the `submatrix Prod.swap id` row of `1`); lift to endomorphisms with `TensorProduct.toMatrix_comm` + `TensorProduct.toMatrix_map` + `LinearMap.trace_eq_matrix_trace`/`toMatrix_comp`, giving `trace(cm ∘ map A A) = trace(A ∘ A)`, so `trace(cm ∘ T g) = χ(g²)`. (2) `averageMap T = ⅟|G| • ∑ T g` (`asAlgebraHom_of`); `cm` is equivariant + involutive so it preserves `T.invariants` and `averageMap` is the identity there, so `FS = trace(cm ∘ averageMap) = trace(cm|_invariants)` via `LinearMap.trace_restrict_eq_of_forall_mem`. (3) `dim T.invariants = |G|⁻¹ ∑ χ(g)² = |G|⁻¹ ∑ χ(g)χ(g⁻¹) = 1` (self-duality + `card_inv_mul_sum_char_eq_finrank` + `char_orthonormal`). (4) a linear involution on a 1-dim space has trace `±1` (`trace_fin_one` + `mul_self_eq_one_iff`). The exported theorem is `Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple`. **The twin #5214 (`exists_nonzero_invariant_symmetric_of_FS_eq_one`) landed (sorry-free) in the bilinear-form model** (`Bil = V →ₗ Dual V = linHom ρ ρ.dual`, flip `τ = LinearMap.lflip`) — see the next bullet for its (self-contained) machinery. Gotchas: `⊗ₖ` needs `open scoped Kronecker`; `W.ρ.asModule` dot-notation resolves to `MonoidHom.asModule` — write `Representation.asModule W.ρ`; a `Finset.sum_congr rfl (fun g _ => ?_)` left after `simp [map_sum]` stalls instance synthesis (`AddCommMonoid ?m`) — split the per-term equality into a named `have` and apply it via `congrArg (c * ·) (Finset.sum_congr …)` instead.
- **`FS = 1 ⟹ ∃ nonzero invariant *symmetric* form (#5214, bilinear-form model, sorry-free in `Chapter5/FrobeniusSchurRealType.lean`).** Two reusable pieces. (a) `trace_comm_comp_map`: `trace((comm).toLinearMap ∘ₗ map A B) = trace (A ∘ₗ B)` on `W ⊗ W` for any finite-dim `W` (abstract sibling of #5261's Kronecker version) — proved with `Module.Basis.tensorProduct b b` + `trace_eq_sum_repr_diag` (= `∑ i, b.repr (f (b i)) i`) + `Module.Basis.tensorProduct_repr_tmul_apply`, matching the diagonal sum to `(toMatrix A * toMatrix B).trace` via `Finset.sum_comm`. (b) The projector-counting recipe: averaging projector `P = averageMap Λ` (`isProj_averageMap.trace` = `finrank invariants`), symmetric-part projector `Pₛ = ½(P + τ∘ₗP)` (idempotent via `τ²=1`, `τ` commutes with `P`; `IsProj` via `isProj_range_iff_isIdempotentElem`, trace = `finrank (range Pₛ)`), giving `2·finrank(sym∩Bil^G) = finrank Bil^G + trace(τ∘P)`. The crux `trace(τ∘P) = FS` reduces per-`g` (`trace(τ∘Λg) = χ(g⁻¹g⁻¹)`) by conjugating `τ∘Λg` to `comm∘map(ρ.dual g)(ρ.dual g)` through `E = dualTensorHomEquiv ℂ V (Dual V)` (prove the intertwiner `(τ∘Λg)∘E = E∘(comm∘map…)` on pure tensors, then `LinearMap.trace_comp_comm'` + `trace_comm_comp_map`). `FS=1 ⟹ 2s = d+1 ⟹ s ≥ 1`. **No simplicity needed for existence** — `hρ` is only used by the nondegeneracy half (`nondegenerate_of_invariant_of_simple`). Simp gotchas that cost iterations: (i) after `set Λ := linHom …`, `linHom_apply`/`dual_apply` will NOT fire in `simp` (terms display as `Λ`); prove a pointwise `hΛapp : (Λ g C) v w = C (ρ g⁻¹ v) (ρ g⁻¹ w)` once via `rw [hΛdef, linHom_apply]; simp [comp_apply, dual_apply, Module.Dual.transpose_apply]` and use *that* in later `rw`/`simp`. (ii) `LinearEquiv.coe_coe` in a `rw`/`simp` set unfolds EVERY `↑e` — including a `set`-defined `τ = (lflip).toLinearMap` → `LinearMap.lflip`, silently breaking `τ`-keyed lemmas; apply the operator's own `_apply` lemma (`hτ_apply`) BEFORE `coe_coe`. (iii) `ρ.dual g` is *defeq* but not *syntactically* `Module.Dual.transpose (ρ g⁻¹)` and its display flips unpredictably mid-`rw`-chain — finish the scalar reduction with `simp only [dual_apply, transpose_apply, comp_apply, smul_eq_mul]`, not a fixed `rw` order.

- **Frobenius induced-character formula (Theorem 5.9.1, #5321, sorry-free in `Chapter5/Theorem5_9_1.lean` + `Chapter5/TraceCoinvariants.lean`).** Mathlib's `Representation.ind` is the *tensor/coinvariants* model (`IndV = Coinvariants (tprod (leftRegular ⊗ ρ))`), so do NOT chase coset transversals — prove the **averaged** form via the reusable crux `Etingof.trace_coinvariantsMap σ Φ : trace (Coinvariants.map σ σ Φ) = |Γ|⁻¹ ∑_{h:Γ} trace (σ h ∘ₗ Φ.toLinearMap)` (finite group, char-0, fin-dim). Its proof is the canonical averaging-idempotent argument and is itself reusable for any coinvariants-trace: `e = averageMap σ` projects onto `invariants σ` with `ker e = Coinvariants.ker σ` (`ker_averageMap`, both inclusions via `averageMap_apply` + an `Equiv.mulRight` reindex), so `Submodule.quotientEquivOfIsCompl` gives `Coinvariants σ ≃ invariants σ`; `Φ̄` conjugates to `Φ.restrict` (`LinearEquiv.conj_apply_apply` + `LinearMap.trace_conj'`), then `LinearMap.trace_comp_comm'` moves it to `trace (e ∘ Φ)`, and `averageMap_eq : averageMap σ = |Γ|⁻¹ • ∑ σ h` finishes by linearity. Application wiring: `ind` is `@[simps]` so `rw [Representation.ind_apply]` exposes the shift intertwiner `⟨(lmapDomain (·*g⁻¹)).rTensor V, _⟩` directly — avoid `rfl`-matching a hand-built `IntertwiningMap`, the `Coinvariants.map` defeq check times out at `whnf`. Each twisted trace factors via `LinearMap.trace_tensorProduct'` into a `ℂ[G]`-trace `Etingof.trace_lmapDomain φ = ∑ x, if φ x = x then 1 else 0` (proved with `Finsupp.basisSingleOne` + `trace_eq_matrix_trace`) times `tr_V ρ(h)`; `Finset.sum_comm` + `Etingof.sum_subtype_ite_coe` collapse each fibre `{x : h·x·g⁻¹ = x} = {x : x·g·x⁻¹ = h}`. Gotchas: `⊗[ℂ]` needs `open scoped TensorProduct`; there is no `LinearMap.sum_comp` for `(c•∑ f)∘ₗΦ` — push the sum through with a one-line `ext; simp [LinearMap.sum_apply]`; `congr 1` on `TensorProduct.map A B = map C D` silently closes any *defeq* component (`ρh∘id` vs `ρh`), so normalise with `LinearMap.comp_id`/`id_comp` first rather than writing a second bullet for it.
- **Centre of `ℂ[G]` = class functions, and the renormalised-character recovery formula (Remark 4.5.3, #5336, sorry-free in `Chapter4/Remark4_5_3.lean`).** `classFunctions G := Subalgebra.center ℂ (MonoidAlgebra ℂ G)`. To prove `f ∈ centre ↔ IsClassFunction f` (`∀ x y, f(yxy⁻¹)=f x`): `simp only [classFunctions, Subalgebra.mem_center_iff]` (the `def`-name unfolds the centre membership to `∀ b, b*f = f*b`). **Forward**: test centrality against `single y 1`, evaluate the function equality at `y*x` via `congrArg (fun F => F (y*x)) (h (single y 1))`, then `simp only [single_mul_apply, mul_single_apply, one_mul, mul_one]` (these `MonoidAlgebra` group lemmas give `(single y 1 * f) p = f (y⁻¹*p)` and `(f * single y 1) p = f (p*y⁻¹)`) and clean the group word with `rw [show y⁻¹*(y*x) = x by group]`. **Backward**: `ext z; rw [mul_apply_left, mul_apply_right]` turns `b*f = f*b` into two `b.sum` expansions `∑ r·f(g⁻¹z)` vs `∑ f(zg⁻¹)·r`; `Finsupp.sum_congr` + `mul_comm` reduces to the pointwise conjugation `f(g⁻¹z)=f(zg⁻¹)`, supplied by the class-fn hyp at `(z*g⁻¹, g⁻¹)` after `rw [show g⁻¹*(z*g⁻¹)*g⁻¹⁻¹ = g⁻¹*z by group]`. `renormCharElt_mem_classFunctions` is then one `rw [mem_classFunctions_iff]` + `FDRep.char_conj`. The **recovery formula** `χ_V(g) = √(|G|/χ̃_V(1))·χ̃_V(g)` with normalisation `χ̃_V(z)=(χ_V(1)/|G|)χ_V(z)`: the witness is just `c = |G|/χ_V(1)` (both the `c²=|G|/χ̃_V(1)` and the `χ_V(g)=c·χ̃_V(g)` legs close with bare `field_simp` — no `ring` needed, it over-closes to "no goals"). Need `χ_V(1)=dim V≠0` for simple `V`: a universe-poly clone of `Corollary4_2_4.finrank_pos_of_simple` (`finrank=0 ⇒ Subsingleton V ⇒ Subsingleton (V⟶V)`, contradicting `FDRep.finrank_hom_simple_simple = 1`), then `FDRep.char_one` + `exact_mod_cast …ne'`. **Still open (#5349)**: `renormChar_isPrimitiveIdempotent` (idempotency needs the convolution Schur identity `∑_x χ(x)χ(x⁻¹z)=(|G|/dim)χ(z)` via "`B=∑χ(x⁻¹)ρ(x)` is `G`-equivariant ⇒ scalar by Schur"; primitivity needs the centre's `∏ℂ` Wedderburn structure, not in Mathlib).

### 2. Scaffold: Set Up the Proof Structure

Before attempting the proof:

1. **Read the book's proof sketch.** Identify the key steps and what facts they use.
2. **Check dependencies.** All items this proof depends on should be sorry-free (or admitted for now). If not, either work on those first or use `admit` temporarily.
3. **Outline the proof.** Use `sorry` for each major step:

```lean
theorem foo : statement := by
  -- Step 1: reduce to case X
  sorry
  -- Step 2: apply theorem Y
  sorry
  -- Step 3: algebraic manipulation
  sorry
```

### 3. Prove: Fill In Sorries One at a Time

Follow the global CLAUDE.md proof rules strictly:

1. **One tactic at a time.** Write one tactic, check diagnostics.
2. **Use `done` to see remaining goals.** Don't guess what the goal state is.
3. **Error priority:** syntax > type > unsolved goals > warnings.
4. **Stop at first error.** Don't continue writing tactics after an error.
5. **Hardest case first.** For case splits, sorry the easy cases and focus on the hard one.

### Private Abbreviation Gotcha

Multiple files define `private abbrev GL2 = ...` / `private abbrev GL2' = ...` for the same underlying type. When using lemmas across files, `rw`/`simp`/`show` may fail because the elaborator sees different abbreviation names. Workarounds:
- Use `have h := lemma_from_other_file ...` then `rw [h]` (let unification handle it)
- Use `change` instead of `show` when the target uses a different abbreviation
- For sorry'd lemmas that need `[Fintype F] [DecidableEq F]` instances (needed by callers and the sorry body): wrap in a `section` with `set_option linter.unusedFintypeInType false` / `set_option linter.unusedDecidableInType false`. The `set_option ... in` syntax doesn't work before `private`.

### Greek-capital notation chars (`Π`, `Σ`, `λ`) can't be identifiers

Greek *lowercase* (`σ`, `τ`, `π`) work fine as identifiers, but the capitals `Π`/`Σ` are reserved notation (Pi/Sigma types), so `set Π := …`, `let Σ := …`, or even embedding them in a name like `hΠ`/`hΣ` fails to tokenize (`unexpected token 'Π'; expected '_' or identifier`, sometimes cascading into confusing downstream parse errors). Use ASCII names for permutation/projection matrices etc. (`PL`, `PR`, `permMat`), and `hperm…` not `hΠ`. Cost two build cycles in #6807.

### `open MvPolynomial` inside `namespace Etingof` opens the wrong namespace

Several Ch5 files declare `namespace MvPolynomial` *inside* `namespace Etingof`
(e.g. `EvalEqOnGL.lean`, `PolynomialWeightSaturation.lean`), so `Etingof.MvPolynomial`
exists. A bare `open MvPolynomial` from inside `namespace Etingof` resolves to that
(near-empty) `Etingof.MvPolynomial` and silently shadows root Mathlib `MvPolynomial`
— `monomial`, `X`, `degreeOf_sum_le`, `smul_eq_C_mul`, etc. then all read as
"Unknown identifier" even though `open MvPolynomial` is right there. **Fix:** write
`open _root_.MvPolynomial`. (Cost one build cycle in #5565.) Same pattern applies to
any namespace the repo redeclares under `Etingof`.

### Stuck `Module ?m (M i)` Metavariable Errors

When working over a *family* `(M : ι → Type*) [∀ i, Module A (M i)] [∀ i, Module 𝕜 (M i)] [∀ i, IsScalarTower 𝕜 A (M i)]` (common for representation families), `lake build` errors like `typeclass instance problem is stuck … (i : ι) → Module ?m (M i)` mean a ring/field implicit was left undetermined. Three concrete causes, each with a one-line fix (diagnosed across ~5 build cycles in #4885, `CharacterIndependence.lean`):

1. **An `abbrev`/`def` over the section `M` silently absorbs `M`'s instances.** `abbrev Pim : Type _ := ∀ i, M i` carries `[∀ i, Module A (M i)]` into its signature, so `Pim M` needs `A` — which `∀ i, M i` does not determine → stuck `Module ?A (M i)`. **Fix:** take a *fresh* type-family argument: `abbrev Pim (N : ι → Type*) : Type _ := ∀ i, N i`, then use `Pim M`.
2. **A helper `def proj … : Pim M →ₗ[A] Pim M` has an implicit `A` invisible at use sites.** When applied (`proj M j x`), neither the argument nor result type mentions `A`, so `A` is a free metavariable. **Fix:** pin it with a named argument everywhere — `proj (A := A) M j x`.
3. **A lemma statement / `LinearIndependent 𝕜 (fun i => f M i)` whose body doesn't pin `𝕜` or `A`.** Restating `Algebra.lsmul 𝕜 𝕜 (M i)` or `traceChar M i` standalone leaves the acting algebra/base field ambiguous. **Fix:** ascribe the codomain — `(traceChar M i : A →ₗ[𝕜] 𝕜)` — or route through a named `def repEnd (i) : A →ₐ[𝕜] End 𝕜 (M i)`.
4. **In-proof `set M := fun i => asModule (L i).ρ` blocks instance search.** Abbreviating a type family with `set`/`let` inside a proof makes `M i` an opaque local fvar, so `Module A (M i)` / `IsScalarTower` / defeq like `asModule (L i).ρ = ↥(L i).V` no longer resolve (instances are registered on the *unfolded* `asModule (L i).ρ`). Symptoms: `failed to synthesize Ring (G →₀ ℂ)` and unsolved `trace ℂ (M i) … = trace ℂ ↑(L i).V …` defeq goals. **Fix:** don't abbreviate — inline `(fun i => Representation.asModule (L i).ρ)` at every call site (a literal lambda beta-reduces during instance search; an fvar does not). This is how the existing `hLsimp`-style hypotheses are written. Diagnosed across 2 build cycles in #4908.

5. **Proving a `Subrepresentation` is algebraic via a monomial basis: thread ONE named linear map, never bare `↑`.** When mirroring `polyRightDegreeFDRep_isAlgebraic` (or building any `IsAlgebraicRepresentation`/basis-coordinate proof on a submodule carrier `W`), `let val : W →ₗ[k] _ := W.subtype` and state every fact (`hvval`, `hbv`, `hrepr`) about `val x`, not the coercion `↑x`. Reason: `map_sum`/`map_smul` emit `W.subtype (…)` while `↑x` elaborates to `Subtype.val`; they are defeq but **`rw` is syntactic and will not fire** across the two forms, stalling mid-proof. Bridge to a standalone `…_toRepresentation_coe` lemma (which is stated with `↑`) by giving the local `val`-form lemma `:= LinearMap.restrict_coe_apply …` (defeq). Two adjacent gotchas in the same proof shape: (a) `set W := restrictTotalDegree …` makes the basis type mismatch the rep's carrier `(theSubrep …).toSubmodule` — instead `set W := (theSubrep …).toSubmodule` (the *actual* carrier) so basis/`map_smul` types line up, and discharge membership with `(MvPolynomial.mem_restrictTotalDegree _ _ _).mpr` (this version takes **3** explicit args; supplying *one* `_` leaves a Pi and `.mpr` fails with `Function.mpr`). (b) `Module.Finite k (theSubrep …).toSubmodule` is NOT found from `Module.Finite k (rightHull …)` automatically (projection isn't unfolded by instance search) — provide `inferInstanceAs (Module.Finite k (rightHull …))`. Cost ~3 build cycles in #5577 (`Chapter5/RightTranslationHullDecomp.lean`, `boundedRightRep_isAlgebraic`).

General rule: if an implicit type/ring/field appears only *inside* a definition's body (not in any argument or result type visible at the call site), pin it explicitly. Test a suspect term in isolation in `/tmp/foo.lean` — it compiles there when the surrounding context determines the implicit, which localizes the bug fast.

### A *family* of module structures on ONE underlying type breaks `map_smul` — give each index its own carrier type (#6240, Problem 3.9.2b)

Building `∃ M : ℕ → Type, … ∀ k l, Nonempty (M k ≃ₗ[A] M l) → k = l` (pairwise-nonisomorphic family): the natural move is `M k := Fin d → 𝕜` for all `k` with a `k`-dependent `Module A (Fin d → 𝕜)` provided as an existential witness (via `Module.compHom` of a per-`k` `AlgHom`). **This wedges two different `Module A (Fin d → 𝕜)` structures onto the same type.** Consequences, each a real failure:
- `map_smul φ r x` (for `φ : M k ≃ₗ[A] M l`) fails with `failed to synthesize SMul A (Fin d → 𝕜)` / "synthesized i2, inferred i1" — TC cannot pick between the two instances (they live only inside `φ`'s type, and `map_smul`'s `[Module A M]` arg is synthesized independently). `φ.map_smul`, `φ.toLinearMap.map_smul`, and the `.map_smul'` field all hit the same wall.
- Proving `IsIndecomposable A (Fin d → 𝕜)` needs `haveI := <the witness>` for `Submodule`/`•` to resolve, but `haveI` makes the instance an opaque fvar, so a follow-up `show IsIndecomposable A (Fin d → 𝕜)` reports "not definitionally equal" against the goal's `(fun k => …) k` instance.

**Fix: distinct carriers.** `def Cyc (n k : ℕ) : Type := Fin d → 𝕜` (index by *everything* the action depends on), with `instance … : AddCommGroup (Cyc n k) := inferInstanceAs …`, same for `Module 𝕜`, `Nontrivial`, and a **registered** `noncomputable instance : Module A (Cyc n k) := Module.compHom (Cyc n k) (rep n k).toRingHom`. Now every `Cyc n k` has a canonical instance: `map_smul φ` works across the distinct types `Cyc n k`/`Cyc n l`, and `Submodule`/`IsIndecomposable` resolve with no `letI`/`show`. Bonus: `Module.compHom`'s smul is defeq to the underlying hom application, so `r • x = rep n k r x` holds by `rfl` (state action lemmas via `rep`, then `r • x` in `map_smul` output rewrites to them for free). Costs: (a) `Pi.smul_apply`/`Pi.add_apply` do NOT fire under the `Cyc` head — per-component goals need `show w j = c • v j` (defeq via Pi's pointwise smul) before `simp`; (b) reuse raw operators on `Fin d → 𝕜` (e.g. `nilOpR : End 𝕜 (Fin d → 𝕜)`) and define `nilOp n k : End 𝕜 (Cyc n k) := nilOpR` — the End types are defeq so lemmas like `nilOp_sq := nilOpR_sq` transfer by defeq. Diagnosed across ~6 build/probe cycles.

### `rw [lie_smul]` (and other `Module`-keyed lemmas) fails on a `TensorProduct` goal — restate with the concrete carrier type (#7529)

`rw [lie_smul]` / `simp only [lie_smul]` (Mathlib's `⁅x, c • m⁆ = c • ⁅x, m⁆`) fails with `Did not find an occurrence of the pattern ⁅?x, ?t • ?m⁆` on a goal `⁅x, c • m⁆` where `m : M ⊗[𝕜] N` — even though the goal literally has that shape. Cause: a scalar written **inside a `def` returning a tensor** (e.g. `cgHW := ∑ i, cᵢ • (eᵢ ⊗ₜ eⱼ)`) elaborates its `•` with `TensorProduct.instSMul`, whereas `lie_smul` is stated over an abstract `[Module R M]` so its `•` is the `Module`-derived `SMulZeroClass.toSMul` instance. The two are **definitionally equal but different instance terms**, and `rw`/`simp` match on the discrimination-tree key, so neither fires. (Diagnose by dumping the goal with `set_option pp.all true in` before the `rw` — the inner smul shows `TensorProduct.instSMul` while the outer/statement smul shows `…Module….toSMul`. The outer one often comes from `Finset.smul_sum`, so the *same* goal carries both instances.)

**Fix: restate the lemma with the concrete tensor type, prove it by the abstract lemma (defeq), and `rw` through the restatement.** In a section with `variable (lam mu : ℕ)`:
```lean
theorem lie_smul_cg (x : sl2) (c : ℂ) (m : (Fin (lam+1) → ℂ) ⊗[ℂ] (Fin (mu+1) → ℂ)) :
    ⁅x, c • m⁆ = c • ⁅x, m⁆ := lie_smul c x m
```
Now `lie_smul_cg`'s statement `c • m` elaborates with the *same* `TensorProduct.instSMul` the goals use (concrete carrier ⇒ same instance search), so `rw [lie_smul_cg]` fires; the body still typechecks because `lie_smul` proves it up to defeq. This pattern generalizes to any `Module`-keyed rewrite (`map_smul`, `smul_comm`, …) that stalls on a concrete-tensor goal. It is a recurring cause of "no longer elaborates" regressions across the tensor-product/Lie-module files after a Mathlib bump.

### `MonoidAlgebra` Ext: Don't Use `Finsupp.lhom_ext`

`MonoidAlgebra k G` is `def`-equal to `G →₀ k`, so `Finsupp.lhom_ext` *applies* to a goal `F = 0` for `F : MonoidAlgebra k G →ₗ[k] N` — but it unifies the domain with the bare `G →₀ k`, which pries the type open and breaks instance search for everything registered on `MonoidAlgebra` (`failed to synthesize Ring (G →₀ ℂ)` / `Algebra ℂ (G →₀ ℂ)` / `Module (G →₀ ℂ) (M i)`). **To show a linear functional on `MonoidAlgebra k G` vanishes**, keep the type intact: prove `∀ a, F a = 0` by `induction a using MonoidAlgebra.induction_on` (base case `of k G g` — exactly the group-element evaluation you have a bridge lemma for; `hadd`/`hsmul` close by `simp only [map_add, …]` / `simp only [map_smul, …]`), then package via `LinearMap.ext`. (#4908)

### A `→₀`-based algebra must be a `def`, never an `abbrev` — `abbrev` leaks `Finsupp.instMul` (pointwise) (#5987)

`MonoidAlgebra k G` is a `def` (semireducible) *on purpose*: it hides that the carrier is
`G →₀ k`, so Mathlib's pointwise `Finsupp` instances (`Finsupp.instMul` from
`Mathlib.Data.Finsupp.Pointwise`, etc.) do **not** apply and the convolution ring
structure is the unique one. If you instead declare your algebra as a **reducible
`abbrev`** (as `Chapter2/Definition2_8_4.lean` did: `abbrev PathAlgebra k Q :=
QuiverPathIndex Q →₀ k`), then under `import Mathlib` the pointwise `Finsupp.instMul`
becomes a valid `Mul` on your type and **outranks your intended (convolution/
concatenation) multiplication** (disjoint-support basis paths multiply to `0`).

The file that *defines* `Foo` compiles because it imports a *narrow* Mathlib slice
excluding `Finsupp.Pointwise`; every downstream file that `import Mathlib` silently gets
**pointwise** `*` instead. Symptoms: a `single_mul_single`-style lemma refuses to
`rw`/`simp` in a downstream goal ("did not find pattern" though the term looks identical),
and statements like `p_source * arrow = arrow` become **false** as elaborated. **Diagnose**
with `set_option pp.all true in #check (a * b)` — the `HMul` head should be your ring's
`instHMul`, not `Finsupp.instMul`. **Fix = make it a semireducible `def`** (Mathlib's
`MonoidAlgebra` pattern), so instance search (reducible-only) can no longer see the
`Finsupp` instances. The conversion triggers a predictable cascade (cost ~10 build cycles
in #5987, `Chapter2/Definition2_8_4.lean`):
- **Re-expose module-level instances** via `inferInstanceAs` — `AddCommGroup`, `Module k`,
  `Inhabited`, … (the `Finsupp`-derived ones are `noncomputable`). Elaboration still unfolds the
  `def` at default transparency, so `Finsupp.single x c : Foo` etc. keep typechecking.
- **`binop%` leak on `Finsupp.single` products.** `(Finsupp.single x a * Finsupp.single y b : Foo)`
  fails (`failed to synthesize HMul (ι →₀ k) (ι →₀ k) ?`) — and *operand* ascriptions
  `(Finsupp.single x a : Foo)` don't help, because `binop%` compares operand vs expected type at
  *reducible* transparency, treats them as uncomparable, and defaults to the raw Finsupp type.
  **Fix:** write the product with explicit `@HMul.hMul Foo Foo Foo _ (Finsupp.single …) (…)`. Keep the
  atoms literal `Finsupp.single` (not a new wrapper `def`) so downstream `rw`/`simp` on goals holding
  `Finsupp.single` (from `Finsupp.induction_linear`, unfolded `ofX := Finsupp.single …`) still match.
- **Reading a coefficient `a x` does NOT elaborate for `a : Foo`.** The semireducible `def` has no
  `FunLike`, so `a ⟨…⟩` fails ("Function expected … but this term has type `Foo`"); it only works
  when `a` is a *bare fvar* the elaborator can unfold, never on a compound `(p * q : Foo)` or an
  ascribed term. **Fix:** route coefficient access through a `LinearMap` — `def coeffAt x : Foo →ₗ[k] k
  := Finsupp.lapply x`; `coeffAt x a` is defeq to `a x` but applies cleanly to products
  (`#6616`, `Chapter9/PathAlgebraLowerBound.lean`). Two follow-ons there: (a) a `coeffAt`/`single_apply`
  lemma whose statement has `if … then … else 0` needs `Decidable` on `QuiverPathIndex` equality — no
  `DecidableEq` on arrows, so put `open Classical in` on that single lemma (NOT file-scoped
  `open scoped Classical`, which the style linter rejects); (b) rewriting a `Prop` *inside* such an
  `if` (e.g. `comp_eq_some_nil_iff`) fails `rw` with "motive is not type correct" because the `Decidable`
  instance depends on the rewritten term — use `simp only [the_iff]` (or `by_cases … <;> simp [h, the_iff]`).
- **`Finsupp.lsum`-based defs leak their LinearMap type.** A `def mul' : Foo →ₗ[k] Foo →ₗ[k] Foo :=
  Finsupp.lsum …` compiles but any tactic that unfolds it hits "target not type-correct under
  instances transparency", and `Finsupp.lsum_single` won't fire. **Fix:** type the internal
  machinery on the *raw* `ι →₀ k` (`compSingle`, `mulLinear`) so it is leak-free, and bridge to `Foo`
  only at the ring instance (`mul := fun f g => mulLinear f g`, `mul_def := rfl`). When a def *must*
  stay `Foo`-domained (needed by `AlgHom.ofLinearMap` — the raw type has no algebra instance), prove
  its apply-lemma by `change`-ing the goal to the raw-coercion form first, then `simp [Finsupp.lsum_single]`.
- **simp can't match `Finsupp.smul_single`** on the `instModule`-typed smul that a `Foo`-ascribed RHS
  produces (defeq but keyed on a different `SMul` head). **Fix:** use `rw [Finsupp.smul_single]` (rw
  unifies instance args up to defeq) instead of `simp only [Finsupp.smul_single]`. **Corollary
  (#6510, length grading `A →ₗ[k] (ℕ →₀ A)`):** when the whole *term* is instance-ambiguous — e.g.
  `(Finsupp.single n (Finsupp.single p c)) n'` where the inner single's `Zero` reverts to the raw
  `ι →₀ k` while the outer expects `Foo` ("target not type-correct under instances transparency") —
  even `rw [Finsupp.single_apply]` fails to match. Discharge the apply-lemma with **term-mode
  `exact Finsupp.single_apply`** (unifies up to defeq), not `rw`. Also avoid `congr 1` on such a
  goal: it re-elaborates the inner `Finsupp.single` and reintroduces the wrong `Zero` instance —
  keep the whole computation in one `rw […]` chain (`Finsupp.smul_single, ofPath, Finsupp.smul_single,
  smul_eq_mul, mul_one`) so instances stay consistent.
- **`•` on a submodule of `Foo` stalls on `Field ?m` when the scalar's implicit `k` is unpinned**
  (#6975, `Chapter9/PathAlgebraProjectiveCover.lean`). Writing a bare `eIdem i • v` where
  `eIdem : {k Q} … → Q → Foo` leaves `k` a metavar (nothing in `i : Q` determines it), and `binop%`
  smul elaboration then trips the `Field ?k` instance search and aborts with "typeclass instance
  problem is stuck / `Field ?m`" — even though `inferInstance : SMul Foo (submodule)` resolves fine on
  its own. **Fix:** pin the scalar's implicit, `eIdem (k := k) i • v` (also inside `f.map_smul (eIdem i) v`
  and any `have`/type-ascription mentioning the smul). Same trap for any polymorphic constant whose
  ground universe/field can't be inferred from its explicit args.
- **`Foo = ι →₀ k` with `Quiver.{u+1}` lands in `Type (u+1)`, not `Type u`** — `Quiver.Path`, hence
  `QuiverPathIndex`, hence `PathAlgebra k Q`, are one universe above `Q : Type u`. A principal submodule
  `A · eᵢ` therefore lives in `Type (u+1)`; a theorem quantifying its projective family as `P : Q → Type u`
  cannot be instantiated with it. Relax such a hypothesis to `P : Q → Type*` (the finrank/equiv proof is
  universe-agnostic) rather than fighting the universe (#6975).

### Induced rep `Ind_H^G ℂ ≅ k[G]·a` as `Representation.Equiv`, and the MonoidAlgebra/Finsupp instance wall (#5171)

Goal: `Etingof.Definition5_8_1 H (trivial) ≅ ℂ[G]·a` (left ideal). Recipe in
`Chapter5/Introduction5_14.lean` (sorry-free). Source is Mathlib's
`Representation.ind φ ρ` on `Coinvariants (tprod ((leftRegular).comp φ) ρ)` over
`(G →₀ ℂ) ⊗ ℂ`; build the forward map `⟦δ_g ⊗ c⟧ ↦ c·(g⁻¹·a)` via `Coinvariants.lift f0 hinv`
(invariance = `of p * a = a` for `p ∈ H`, proved reindexing the subgroup sum by `Equiv.mulLeft`);
corestrict to `LinearMap.range (mulRight ℂ a)`; bijectivity from a normalised left inverse
(factor `1/|H|`, the `|H|`-fold coinvariant collapse) for injectivity and a section
`Ffull (sMap z) = z·a` for surjectivity; equivariance on `IndV.mk` generators via `ind_mk`.
Package with `Representation.Equiv.mk linEquiv intertwine` (the bundled bare-`Representation` iso —
better target than a `Rep` `≅` here; `(mk e he)` wants `he : ∀ g, ↑e ∘ₗ ρ g = σ g ∘ₗ ↑e`).

**The instance wall** (cost ~5 build cycles — `MonoidAlgebra ℂ G` and `G →₀ ℂ` carry *different*
`AddCommMonoid`/`Module` instances on the same carrier, defeq but not syntactically equal):
- `LinearMap.comp` (`∘ₗ`) and `LinearMap`-equality *types* reject a middle/codomain that is
  `MonoidAlgebra` on one side and `G →₀ ℂ` on the other ("not type-correct under instances
  transparency"). Bridge with an **all-`rfl` identity `LinearEquiv toFinsuppLE : MonoidAlgebra ℂ G ≃ₗ (G →₀ ℂ)`**
  (`toFun := id`, every field `rfl` — it compiles), and compose maps from `Finsupp.lsum`/
  `linearCombination` (which produce `G →₀ ℂ` domains) with `toFinsuppLE.toLinearMap` to retype.
- A bare `Finsupp.single h r * (algebra)` fails to elaborate (`Finsupp` has **no `Mul`**);
  write `MonoidAlgebra.single h r` (an abbrev for `Finsupp.single`, but typed in `MonoidAlgebra`)
  in any multiplied position — *including lemma statements*, where there's no context to coerce.
- A lambda body `MonoidAlgebra.of … h * a` inside `lsum`/`linearCombination` (expected type a
  metavar) gets `of …` whnf'd to `G →₀ ℂ` and loses `Mul` → `HMul (G →₀ ℂ) (MonoidAlgebra) ?`.
  Define such maps as `LinearMap.mulRight ℂ a ∘ₗ (a map landing in MonoidAlgebra)` instead of
  multiplying inside the lambda.
- **Never `rw` a `leftRegular`/`ofMulAction` term (lives on `G →₀ ℂ`) applied to a
  `MonoidAlgebra`-typed argument** — the rewrite motive is heterogeneous and fails. For the
  *target* left-multiplication action, use a `MonoidAlgebra`-native rep
  `leftMulRep g := LinearMap.mulLeft ℂ (of g)` (then `leftMulRep g x = of g * x` is `rfl`), not
  `subrepresentation (leftRegular …)`. Note a def that doesn't *use* `la` won't bind it — call it
  `leftMulRep n`, not `leftMulRep n la`.
- `Representation.IndV.mk` is a **reducible abbrev**, so `simp`/`ext_ring` unfold it to
  `Coinvariants.mk … (TensorProduct.mk … (single h 1) c)` and then `Representation.ind_mk`/
  `Ffull_IndVmk` no longer pattern-match. Re-fold with `change Ffull (… (IndV.mk … h 1)) = …`
  before the `rw` chain.

### `k`-trace lemmas on a group-algebra submodule need `restrictScalars k`

When generalizing a character/trace from `ℂ` to general `k` (the #4946 chain), the Specht-type
modules are left ideals `SpechtModuleK k n la = k[S_n]·c_λ` — i.e. a `Submodule (MonoidAlgebra k G) (MonoidAlgebra k G)`
(over the *algebra*), not a `Submodule k _`. Mathlib's `k`-trace lemmas (`LinearMap.trace_restrict_eq_of_forall_mem`,
`LinearMap.trace_baseChange`) require a `Submodule k M`, so passing the algebra-submodule leaves `p`/`q` stuck as
metavars. **Fix:** phrase the hypothesis and the `.restrict` over `(SpechtModuleK k n la).restrictScalars k` (same
carrier, so the action `→ₗ[k]` on `↥(SpechtModuleK …)` is defeq to the one on `↥(… .restrictScalars k)`); close the
final step with `exact` (which uses defeq) rather than `rw` (syntactic). Field-independence of such a trace then comes
cheaply: the idempotent `α⁻¹·c_λ` makes `χ(σ) = trace(L_σ ∘ R_{α⁻¹c}) = (N₀:k)⁻¹·(M₀:k)` with `N₀,M₀ ∈ ℤ` from the
ℤ-coefficients of `c_λ` (`YoungSymmetrizerZ` + `mapRangeRingHom`), so `χ_k = algebraMap ℚ k (χ_ℚ)` and ℂ injectivity
transfers. Worked example: `Chapter5/SpechtCharacterGeneral.lean` (#4991). Also: `set G := Equiv.Perm (Fin n)` where
`G` is *also* a binder's type duplicates the variable (`σ✝` vs `σ`) — write the type literally instead of `set`.

### `restrictScalars`/`of_restrictScalars_finite` re-synthesise `IsScalarTower`/`CompatibleSMul` with a metavar codomain and don't find the local instance (#7512)

Fresh-buildability regression pattern in the "isotypic component of a group-algebra module, take ℂ-trace" idiom
(`letI : Module ℂ ↥C_R := (C_R.restrictScalars ℂ).module; haveI : IsScalarTower ℂ A ↥C_R := ⟨…⟩`). A direct
`inferInstance : IsScalarTower ℂ A ↥C_R` (or `… : CompatibleSMul …`) **succeeds**, but the same obligation raised
*inside* `Module.Finite.of_restrictScalars_finite ℂ A ↥C_R` or `e'.restrictScalars ℂ` **fails to synthesize** — the
consumer resolves the obligation while the `Module ℂ`/codomain is still a metavariable, so it never matches the local
`haveI`. **Fixes** (all keep the underlying maps unchanged): (a) pass the tower instance explicitly,
`@Module.Finite.of_restrictScalars_finite ℂ A ↥C_R _ _ _ _ _ _ iST _`; (b) build the ℂ-linear equiv by hand instead of
`e'.restrictScalars ℂ` — `{ toFun := e', invFun := e'.symm, map_add' := e'.map_add, left_inv := …, right_inv := …,
map_smul' := fun c x => e'.toLinearMap.map_smul_of_tower c x }` (the structure type pins the codomain, so
`map_smul_of_tower`'s `CompatibleSMul` resolves; `e'_ℂ x = e' x` and `e'_ℂ.symm = e'.symm` stay `rfl`); (c) pin
`(M := …) (N := …)` on `LinearMap.trace_conj'` when the endomorphism is typed over a defeq-but-syntactically-different
carrier. Worked example: `Chapter5/Theorem5_15_1.lean` `trace_isotypic_eq_mult_trace`. `CharacterMultiplicityBridge.lean`
has the identical pattern and the same regression.

### `bijective_or_eq_zero`/`of_injective` on a group-algebra submodule hit the `Ring.toSemiring` vs `MonoidAlgebra.semiring` diamond (#7512)

`isotypicComponent`/Schur API carry `[Ring R]` and so bake `Ring.toSemiring` (and `AddCommGroup.toAddCommMonoid`) into
their submodules, whereas a `→ₗ[SymGroupAlgebra n]` map from a theorem signature picks the *direct* `MonoidAlgebra.semiring`
(and `Submodule.addCommMonoid`). These are **defeq but not syntactic** (`… .toSemiring = MonoidAlgebra.semiring` is `rfl`),
so `f.comp S.subtype` / `IsSemisimpleModule.of_injective (Submodule.inclusion h)` fail to unify or leave the map a metavar.
**Fixes:** (a) for Schur, drop `f.comp S.subtype` and hand the *unascribed* restriction literal
`{ toFun := fun t => f t.val, map_add' := …, map_smul' := … }` straight to `LinearMap.bijective_or_eq_zero (R := R) (M := …) (N := …)`
so its `[Ring]`/`[AddCommGroup]` context drives the instances (an ascribed `↥S →ₗ[R] V` re-picks the wrong ones); recover the
map in the bijective branch via `LinearEquiv.ofBijective _ h_bij`; (b) for "submodule of a semisimple module is semisimple",
skip `of_injective` entirely — if the ambient is semisimple (e.g. `PermutationModule` over `ℂ[Sₙ]`, which is
`IsSemisimpleRing`), `haveI : IsSemisimpleModule R I := inferInstance` works via `IsSemisimpleModule.submodule`.

### `Module.Free ℂ ↥(submodule)` no longer resolves by `inferInstance` — use `Module.Free.of_divisionRing ℂ <explicit type>` (#7512)

The `Submodule.addCommMonoid` vs `AddCommGroup.toAddCommMonoid` diamond blocks `inferInstance` for `Module.Free ℂ ↥p`
(and for `Module.finrank_pi_fintype`, which wants `Module.Free ℂ (V →ₗ[R] V)`). Supply it explicitly with the type argument:
`Module.Free.of_divisionRing ℂ (↥(permModuleIsotypicComponent …))` / `Module.Free.of_divisionRing ℂ (V →ₗ[R] V)`.

### `MvPolynomial.coeff_smul` won't match a `zsmul` — convert with `Int.cast_smul_eq_zsmul (R := ℂ)` (#7512)

A `(sign π : ℤ) • p` from a determinant/Vandermonde expansion is the `AddCommGroup` `zsmul`, not the `SMulZeroClass ℤ`
action `coeff_smul` expects, so `rw [MvPolynomial.coeff_smul]` reports "did not find pattern". Convert both directions:
`rw [← Int.cast_smul_eq_zsmul (R := ℂ) z, MvPolynomial.coeff_smul, …, Int.cast_smul_eq_zsmul (R := ℂ)]`.

### `restrictScalars k` map equalities over `A ⊗[k] X` modules are prohibitively slow for symbolic degree — state the identity pointwise (Ch8 bar resolution, #6414)

When a map is `A`-linear (e.g. the bar differential `barDiff n : (A ⊗[k] Xₙ₊₁) →ₗ[A] (A ⊗[k] Xₙ)`) and
you want to compose it with a `k`-linear map, the natural statement `(barDiff n).restrictScalars k |>.comp …
= …` forces `LinearMap.CompatibleSMul (A ⊗[k] Xₙ₊₁) (A ⊗[k] Xₙ) k A` synthesis. For a *concrete* degree
(`n = 0`) this resolves; for *symbolic* `n` it **times out past 1M heartbeats** — even elaborating the
statement (before any proof) hangs at `synthesize pending MVars`. **Fix:** state the identity **pointwise**
`∀ x, f (g x) + … = x` (application of an `A`-linear map to an element needs no `CompatibleSMul`), prove it
on generators, and extend to all `x` by a `TensorProduct.induction_on` / `PiTensorProduct.induction_on`
wrapper (`map_add`/`add_add_add_comm` for the add cases; for the `smul_tprod r v` case use
`TensorProduct.smul_tmul` to move `r` onto `w` and reuse the generator lemma with `r • w`). The pointwise
form is equivalent and directly usable downstream. Prefer it for any barModule-style map with symbolic degree.

### A tensor RHS with `(m : M)` silently becomes `sorry` when the equation LHS is a `ModuleCat`-hom application (Ch9 induced modules `A ⊗_S M`, #6541)

Writing a lemma `(someHom M).hom η = a ⊗ₜ[Q → k] (m : M)` where the RHS is a `TensorProduct` and
`m : restrictObj M` **elaborates the whole RHS to `sorry`** — the error then surfaces later as a
mysterious `⊢ … = sorry` in the *proof* goal, not as a statement error. Cause: `(someHom M).hom η`
has type `↑(inducedRestrictObj M)` (a `ModuleCat` carrier), which is **not syntactically** a
`TensorProduct`, so the elaborator can't propagate the second-factor module instance to the RHS
`⊗ₜ` and gives up. This is why `inducedCoordMap_tmul`-style lemmas work (their LHS type *is*
`inducedCarrier M = TensorProduct …`) but a hom-application LHS does not. **Fix:** annotate the RHS
tensor with the concrete carrier: `= (a ⊗ₜ[Q → k] (m : M) : inducedCarrier M)`. Two related pins in
the same file: `map_add` on `f (a + b)` where the argument is a `Nat` sum `n + 1` rewrites the
`n + 1` instead of the `a + b` — use `LinearMap.map_add` to force the module map; and a lemma whose
implicit `k` is fixed only by pure quiver/`Nat` data (`exists_ofPath_mul_arrowElt q hx`) leaves
`Field ?k` stuck — pass `(k := k)`.

**Two more pins when building a retraction / injectivity of `Φ = stdΦ M` on `A ⊗_S (V ⊗_S M)` by hand (#6545, `Chapter9/PathAlgebraConsSplittingRetraction.lean`, sorry-free `stdΦ_injective`):** **(i) the field `k` does NOT act on `A ⊗_S -` tensors — only `S = Q → k` does.** `Module k (TensorProduct (Q→k) A X)` does not synthesize (nor does it on the `↑(inducedVtensObj M)` `ModuleCat` carrier — a `Module A` does not auto-give `Module k`), so `c • (tensor)` for `c : k` is ill-typed. Keep every coefficient **inside a `Finsupp` factor** and move it across a tensor only with base-ring (`Q→k`) `TensorProduct.smul_tmul`, realizing `c` as a vertex indicator `Pi.single v c` acting through the right/source `S`-action. Corollary: `Finsupp.single q c : PathAlgebra k Q` as a `⊗ₜ` factor **fails** `Module (Q→k)` synthesis (the ascription unfolds it to the raw `QuiverPathIndex →₀ k`, losing `instModuleVertex`) — write the factor as `c • ofPath q` (or bare `ofPath q`) and convert with a `single q c = c • ofPath q` lemma when needed. **(ii) the concrete-carrier annotation is also what selects the *source* `Module` instance on `VtensObj`.** Complementing gotcha (b) of the #6480 entry: a bare `(v ⊗ₜ[Q→k] m : VtensObj M)` resolves its smul to the *canonical* (target) tensor instance, so `vtens_smul_def`/`change` to the source `TensorProduct.map (srcHom s) id` form both fail. **Fix:** ascribe the *whole outer expression* to the abbrev — `(a ⊗ₜ (v ⊗ₜ m : VtensObj M) : inducedVtensObj M)` — which propagates `inducedVtensObj`'s source instance inward; then `TensorProduct.smul_tmul` on the outer produces a genuine source-action `s • (v ⊗ₜ m)` that `vtens_smul_def`/`vtens_smul_tmul` rewrite (it is even defeq to `srcHom s v ⊗ₜ m`, so `congr 1` can close it). State every helper lemma and `def` return type in terms of the `inducedVtensObj M` / `inducedRestrictObj M` abbrevs (not spelled-out `TensorProduct (Q→k) …`, which reintroduces the wrong instance and the `QuiverPathIndex →₀ k` unfold).

### Assembling a `ProjectiveResolution` / quasi-iso to `single₀` from a (k-linear) contracting homotopy (Ch8 bar resolution, #6415)

To turn a chain complex `C : ChainComplex (ModuleCat A) ℕ` with augmentation
`π : C ⟶ (ChainComplex.single₀ _).obj (ModuleCat.of A W)` into a `ProjectiveResolution`, the only
real work is `QuasiIso π`; the rest is `complex := C`, `π := π`, `projective n := <your instance>`,
`quasiIso := <the proof>` (the `hasHomology` field is auto — `ModuleCat A` is abelian). **Do not**
reach for the restriction-of-scalars *functor-reflection* route (`quasiIso_map_iff_of_preservesHomology`);
it needs a hand-built `HomotopyEquiv` over `ModuleCat k` and fights the `k`-module-structure defeq.
Go **degreewise**, mirroring Mathlib's `CategoryTheory.ProjectiveResolution.of`:

- `rw [quasiIso_iff]; rintro (_ | n)`.
- **Degree `n+1`:** `rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]`
  leaves `C.ExactAt (n+1)`. Then `rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp),
  ShortComplex.moduleCat_exact_iff]` gives the elementwise goal `∀ x, (d n) x = 0 → ∃ y, (d (n+1)) y = x`.
  The k-linear contracting homotopy `d(n+1)(s(n+1) x) + s n (d n x) = x` supplies `y := s (n+1) x`.
  The `sc'.f`/`sc'.g` are `C.d (n+2)(n+1)` / `C.d (n+1) n` but wrapped; peel them with
  `have hf : (C.sc' (n+2)(n+1) n).f = ModuleCat.ofHom (d (n+1)) := ChainComplex.of_d <X-family> <d-family> (n+1)`
  (give both families *explicitly* — metavars won't infer), `rw [hf]`, then `change`/`ModuleCat.ofHom_apply`
  to drop `⇑(ofHom ·)` (the coercion prints as `ConcreteCategory.hom`, not `ModuleCat.Hom.hom`).
- **Degree `0`:** `rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']` (the three
  `S.g/f = 0` side goals close with `all_goals rfl`) leaves `(mk S₁.f φ.τ₂ _).Exact ∧ Epi φ.τ₂`.
  The `.f`/`.τ₂` are buried projections, so **transport to a clean short complex** built by
  `ShortComplex.moduleCatMk (barDiff 0) ε ε_comp_barDiff_zero` (whose `.f`/`.g` are defeq `ofHom …`):
  `refine (ShortComplex.exact_and_epi_g_iff_of_iso (ShortComplex.isoMk (.refl _) (.refl _) (.refl _) ?_ ?_)).2 ⟨hTexact, hTepi⟩`,
  and the two comm squares close with just `simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]`
  (simp already knows `ChainComplex.of_d` and `barπChainMap_f_zero`). Prove `hTexact` via
  `moduleCat_exact_iff` + the degree-0 homotopy `d₀ s₀ + s₋₁ ε = id`, and `hTepi` via
  `ModuleCat.epi_iff_surjective` + surjectivity of `ε`.

The `restrictScalars` functor *does* have `Additive`/`ReflectsIsomorphisms`/`PreservesFiniteLimits`+
`Colimits` (⟹ `preservesHomologyOfExact`), so the reflection route is *possible* — it is just more
code than the degreewise one here. Exactness of a `ModuleCat A` complex is an underlying-abelian-group
fact, so a `k`-linear homotopy discharges it directly with no functor machinery.

### `Fin.cons`/`Fin.init` on an empty or symbolic domain leaves the family `α` a metavariable — pin `(α := fun _ => A)` (#6414)

`Fin.cons`/`Fin.init` are dependent (`{α : Fin (n+1) → Sort*}`). For an *empty* tail (`v : Fin 0 → A`) or a
subterm whose expected type doesn't constrain `α` (the `Fin.init` output type `∀ i, α i.castSucc` is vacuous
when the domain is `Fin 0`), elaboration leaves `α` — and hence the explicit args a₀/v — as unsolved
metavars: `rw`/`show`/`funext` with a bare `Fin.cons a₀ v` fails with "type mismatch `?m i` vs `A`" or
"did not find pattern `Fin.cons ?m ?m`". **Fix:** write `Fin.cons (α := fun _ : Fin (n+2) => A) a₀ v`
explicitly (match the family the *goal* uses — a const `fun _ => A` if it came from `tprod k (Fin.cons …)`).
Also `Fin.last 0 = (0 : Fin 1)` needs `Fin.ext rfl`, not `Subsingleton.elim` (`Subsingleton (Fin (0+1))`
doesn't synthesize). Separately, `tprod k (Fin.cons …)` is ambiguous with `_root_.tprod` (infinite products) —
qualify as `PiTensorProduct.tprod k (Fin.cons …)`.

### Total complex of two resolutions via `HomologicalComplex.mapBifunctor` + `toSingle₀Equiv` augmentation (Ch8 external tensor complex, #6680, `Chapter8/ExternalTensorComplex.lean`)

To build `⨁_{j+m=i} (P₁)ⱼ ⊗ (P₂)ₘ` with Koszul-signed differential for a general bifunctor
`F : ModuleCat A₁ᵐᵒᵖ ⥤ ModuleCat A₂ᵐᵒᵖ ⥤ ModuleCat (A₁⊗A₂)ᵐᵒᵖ`, use
`HomologicalComplex.mapBifunctor P₁.complex P₂.complex F (ComplexShape.down ℕ)` — Mathlib supplies
`d`, signs (`ε₂ (i₁,i₂) = c.ε i₁ = (-1)^{i₁}` from the diagonal `TotalComplexShape c c c`), `d_comp_d`,
and the summand API. Four gotchas, each cost multiple iterations:
- **`mapBifunctor` needs `[F.PreservesZeroMorphisms]` and `[∀ X, (F.obj X).PreservesZeroMorphisms]`.**
  Not automatic. If `F`'s action is defined with `local instance`s in another file (e.g. `extModule`
  in `ExternalTensorFunctor.lean`), **re-declare those same `local instance`s in your file** or a
  `Module (A₁⊗A₂)ᵐᵒᵖ (X⊗Y)` diamond (`instSemiring` vs `instRing.toSemiring`) blocks LinearMap-level
  rewrites against `F`'s map lemma. Prove `F.map 0 = 0` at the *LinearMap* level (native carriers, no
  ModuleCat coercion), then lift via `ModuleCat.ofHom_zero`.
- **`HasMapBifunctor`/`HasTotal` over `down ℕ` needs `Finite (ComplexShape.π (down ℕ)³ ⁻¹' {n})`.**
  Mathlib's fiber-finiteness instance is keyed on `fun i => i.1+i.2`, which does *not* match
  `ComplexShape.π` syntactically — add your own `instance (n) : Finite (…π… ⁻¹' {n})` (copy the
  `Finite.of_injective … Fin (n+1) × Fin (n+1)` proof). Then coproducts resolve via
  `hasColimitsOfShape_discrete`.
- **Make the complex (and any `mapBifunctorDesc`-based map) an `abbrev`, not `def`.** A `def` wrapper
  is defeq-but-not-syntactic to `mapBifunctor`, so `ι_mapBifunctorDesc`/`d_eq`/`ι_D₁`/`ι_D₂` silently
  fail to fire through it.
- **Dependent descent (`mapBifunctorDesc (fun i₁ i₂ h => …)`): use a structural `match`, never
  `obtain ⟨rfl,rfl⟩`.** `obtain` on the opaque proof `h : π(i₁,i₂)=0` leaves a stuck `Eq.ndrec`
  (no iota on a non-`rfl` proof) so `ι_mapBifunctorDesc` reduces to un-usable cruft. Instead
  `match i₁,i₂,h with | 0,0,_ => aug00 | (_+1),_,h => absurd h (by simp) | 0,(_+1),h => absurd h (by simp)`.
- **Augmentation to `single₀`:** build via `(ChainComplex.toSingle₀Equiv C M).symm ⟨f₀, hf⟩`. Extract
  each resolution's degree-0 map as `((ChainComplex.toSingle₀Equiv Pᵢ.complex Mᵢ) Pᵢ.π).1` — this has
  clean codomain `Mᵢ` (not `((single₀).obj Mᵢ).X 0`, which blocks `← Functor.map_comp` from combining
  two `(F.obj Mᵢ).map` calls), and its `.2` field *is* the `d 1 0 ≫ π₀ = 0` fact you need for `hf`.
  The `hf` proof: `mapBifunctor.hom_ext`, then `d_eq`+`ι_D₁/₂`, `obtain` the `(1,0)|(0,1)` summands,
  kill the dead one with `d₁/₂_eq_zero (by simp : ¬ Rel 0 (next 0))`, evaluate the live one with
  `d₁/₂_eq` (fully **named** args `(K₁:=…)(K₂:=…)(F:=…)(c:=…)(i₁:=…)…(h:=by simp)(h':=by simp)` — positional is unusable), sign `= 1` by `rfl`/`simp`, then naturality of `F.map πᵢ` + `← Functor.map_comp` + the `d≫π=0` fact + `F.map 0 = 0`.

### `restrictScalars` homology/limit preservation FAILS to synthesize for noncommutative target rings — the `ChangeOfRingsExact` instances require *both* rings commutative (Ch8 external tensor resolution, #6735, `Chapter8/ExternalTensorResolution.lean`)

`(ModuleCat.restrictScalars f).PreservesHomology` / `PreservesFiniteLimits` / `PreservesFiniteColimits` do **not** `inferInstance` when the target ring is noncommutative (e.g. `f = algebraMap k A₁ᵐᵒᵖ`, which is everywhere in this book). The `Mathlib/…/ChangeOfRingsExact.lean` exactness instances are declared under `variable {R} [CommRing R] {R'} [CommRing R']` — they only fire for commutative targets. Likewise `extendRestrictScalarsAdj` (which would make `restrictScalars` a *right* adjoint) needs `[CommRing R] [CommRing S]`. **Build it via the left adjoint instead** (`restrictScalars ⊣ coextendScalars`, general rings): `restrictScalars` preserves colimits, and it already has `PreservesMonomorphisms` + (via `Additive`) `PreservesZeroMorphisms`, so `preservesHomology_of_preservesMonos_and_cokernels` applies:
```lean
theorem restrictScalars_preservesHomology {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology := by
  haveI : Limits.PreservesColimits (ModuleCat.restrictScalars.{u} f) :=
    (ModuleCat.restrictCoextendScalarsAdj f).leftAdjoint_preservesColimits
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _
```
Then `homology (F(Q.complex)) (n+1)` for a `ProjectiveResolution Q` is zero via the mapped quasi-iso `(F.mapHomologicalComplex _).map Q.π` (`QuasiIsoAt` instance, auto from `[F.PreservesHomology]`) + `HomologicalComplex.singleMapHomologicalComplex F _ 0 |>.app N` + `isZero_single_obj_homology (down ℕ) 0 (F.obj N) (n+1) (by simp)` (note: `c`, `j` are **explicit** leading args of `isZero_single_obj_homology`). Two more snags: `ChainComplex.single₀` is an `abbrev` for `HomologicalComplex.single _ (down ℕ) 0`, so the `single`-lemmas apply directly; and a `res₁Complex`-style `abbrev` whose only `k`-dependence is in its return type leaves `k` a stuck `Algebra ?k A₁` metavariable — pin it with `res₁Complex (k := k) P₁`.

**Also (definition-audit):** `extTensorProjectiveResolution` was declared over `[CommRing k]`, but its `quasiIso` field (tensor of resolutions is a resolution of the tensor) is *false* over a general `CommRing` — it is `Tor_{>0}^k(M₁,M₂)=0`, which fails for `k=ℤ`, `M₁=M₂=ℤ/2`. It needs `[Field k]`. Confirm a homological-algebra `quasiIso`/acyclicity obligation actually holds under the stated ring hypotheses (flatness ⟹ field) *before* attempting to fill it.

### An additive functor commutes with `mapBifunctor`/`total` — it's `PreservesCoproduct.iso`, not a hand-built descent (Ch8 #6743, `Chapter8/MapBifunctorPostcomp.lean`)

To move an additive `G : D ⥤ D'` through the total complex — `(G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c) ≅ mapBifunctor K₁ K₂ (F ⋙ (Functor.whiskeringRight _ _ _).obj G) c` (the shape #6727/#6738 need) — do **not** hand-build the colimit descent. Each degree is *definitionally* `∐ (…mapObjFun π j)` (`total.X j := toGradedObject.mapObj π j := ∐ …`, all `rfl`), and `((F ⋙ whiskG).obj X₁).obj X₂ = G.obj ((F.obj X₁).obj X₂)` is defeq, so:
- **Degreewise iso is literally `Limits.PreservesCoproduct.iso G (postcompFam …)`** — the `G.obj (∐ f) ≅ ∐ (G ∘ f)` iso lands with the target complex's degree type accepted by defeq, no transport. Instance needs: `[G.Additive]` (⇒ `preservesFiniteCoproductsOfAdditive`) + `[Finite (π ⁻¹' {j})]` (⇒ `PreservesColimit`), plus the RHS `HasCoproduct (fun i => G.obj (f i))` — supply it from `‹HasMapBifunctor K₁ K₂ (F ⋙ whiskG) c›` as a genuine `instance` so the *same* coproduct is used everywhere (else `PreservesCoproduct.inv_hom`'s `.inv = sigmaComparison` `rfl` fails across two subsingleton `HasColimit` instances).
- **Summand compat** from `Limits.ι_comp_sigmaComparison` (inv form) + `PreservesCoproduct.inv_hom`; then the differential square via `HomologicalComplex.Hom.isoOfComponents`, reducing on each summand with `mapBifunctor.d_eq`/`ι_D₁`/`ι_D₂` and `d₁_eq'`/`d₂_eq'`. `G` passes the Koszul sign `ε₁/ε₂ : ℤˣ` by `Functor.map_units_smul` (additive ⇒ `Functor.intLinear : G.Linear ℤ`) + `Linear.units_smul_comp`; `d₁ = F.map d`, `d₂` pass through `G` by `rfl` (defeq).
- **Pin the `ComplexShape` explicitly with `(c := c)` at every call site** of a helper whose `c` is inferable *only* from its return type (`postcompX`/`postcompFam`). TC resolution for the coproduct/`Finite`-fiber args fires before `c` unifies and dies with `typeclass instance problem is stuck … TotalComplexShape c₁ c₂ ?m`. Same fix as the `proj (A := A)` / `le_iSup ![…]` metavariable traps above.
- `whiskeringRight` lives in `CategoryTheory.Functor`, so write **`Functor.whiskeringRight`** under `open CategoryTheory` (unqualified is `Unknown identifier`).

### Cochain-complex `Ext` crux: keep ℤ indices in ONE cast form, and hand-build the noncommutative tensor–hom adjunction (Ch8 Problem 8.2.6 ii, #6464)

Computing `Ext¹` as `CohomologyClass (R.cochainComplex) (single V 0) 1` (via
`ProjectiveResolution.extAddEquivCohomologyClass`) and matching it to a cocycle/coboundary group:

- **`-↑2` vs `-2` will silently break every `rw`.** `R.cochainComplex.X`, `cochainComplexXIso`,
  `toSingleEquiv`, and `homEquivDeg`-style defs index by `-(n : ℤ) = -↑n` (a `Nat.cast`), while
  `δ_toSingleMk` / `toSingleMk` / `cochainComplex_d` take **literal** `ℤ` args. `-↑2` and `-2` are
  defeq but **not syntactically equal**, so `rw [key]`, `rw [toSingleEquiv_toSingleMk]`, and
  `Iso.inv_hom_id_assoc` all fail to fire (and `simp only [Nat.cast_ofNat]` often does *not*
  normalize `-↑1` when the `1` is `One.one`). **Fix:** pick the cast form your `homEquivDeg_apply`
  produces (`-((n:ℕ):ℤ)`) and pass *that exact form* to `Cochain.δ_toSingleMk`, `cochainComplex_d`,
  and `Cochain.toSingleMk_surjective`, so isos/differentials cancel syntactically. Prove the
  degree-`k` `d`-fact as `have : R.complex.d k (k-1) = ofHom (barDiff …) := barResolution_complex_d …`
  (`2` ascribed to `1+1` is accepted by defeq) to sidestep `ChainComplex.of_d`'s `(j+1)` matching.
- **`LinearMap.liftBaseChangeEquiv A` needs `[CommSemiring A]`** — useless for a path/group algebra.
  The adjunction `(A ⊗[k] X →ₗ[A] V) ≃+ (X →ₗ[k] V)`, `f ↦ (x ↦ f (1 ⊗ x))`, must be built by hand:
  `toFun f := (f.restrictScalars k).comp (TensorProduct.mk k A X 1)`,
  `invFun g := AlgebraTensorModule.lift (LinearMap.toSpanSingleton A _ g)` (both need only
  `Semiring A`); `left_inv` via `AlgebraTensorModule.ext` + `f.map_smul` + `smul_tmul'`.
- **Assemble the two quotients with `QuotientAddGroup.congr G' H' e he`**: `CohomologyClass = Cocycle ⧸
  coboundaries` and `Problem3_9_1.Ext1 = ↥cocycles ⧸ (coboundaries.submoduleOf cocycles)` are both
  `QuotientAddGroup` quotients (submodule quotient is defeq `⧸ ·.toAddSubgroup`). Build
  `e := (Ψ1.addSubgroupMap (cocycle …)).trans (AddEquiv.addSubgroupCongr hcocy)` (its coercion to the
  ambient hom is `Ψ1` on the underlying cochain, `rfl`); `he` uses `AddSubgroup.mem_map` +
  `Submodule.mem_comap` (for `submoduleOf`) + the coboundary equality `Ψ1 (δ 0 1 β) = coboundaryOf (-(Ψ0 β))`.

### Scalar extension `ℂ ⊗_ℚ k[S_n]·c_λ ≅ ℂ[S_n]·c_λ` (Specht rational form, #5234)

To prove the base-change compatibility "`SpechtModuleK ℂ` is the complexification of `SpechtModuleK ℚ`"
as an `S_n`-rep iso (`Chapter5/SpechtBaseChangeComplex.lean`), the working recipe — avoiding any
"rational vectors ℚ-indep ⇒ ℂ-indep" linear algebra:
- **Do NOT reach for `MonoidAlgebra.scalarTensorEquiv`/`tensorEquiv`** (`ℂ ⊗_R R[M] ≃ₐ A[M]`): they require
  `[CommMonoid M]`, so they are **unusable for `S_n` = `Equiv.Perm (Fin n)`** (non-commutative for `n ≥ 3`).
- Build the map with `LinearMap.liftBaseChange ℂ (g : ↥V_ℚ →ₗ[ℚ] ℂ[S_n])`, `g v = j v` where
  `j = MonoidAlgebra.mapRingHom (algebraMap ℚ ℂ)`. Get `j` as a `ℚ`-linear map via
  `(jHom).toAddMonoidHom.toRatLinearMap` (every additive map of ℚ-spaces is ℚ-linear).
- **Range** = `V_ℂ`: `LinearMap.range_liftBaseChange` gives `span ℂ (range g)`; finish by span double-inclusion
  using `j c_ℚ = c_ℂ` and `j` multiplicative (⊇ via `Finsupp.induction_linear` on `b`, showing each
  `b * c_ℂ ∈ span`, `of σ * c_ℂ = g ⟨of σ * c_ℚ, _⟩`).
- **Injectivity** via flatness, *not* coordinates: factor `Ψ = TensorProduct.finsuppScalarRight ℚ ℂ ℂ G ∘ lTensor ℂ (incl)`.
  `Module.Flat.lTensor_preserves_injective_linearMap` (ℂ free⇒flat over ℚ) makes `lTensor ℂ` of the injective
  inclusion `V_ℚ ↪ ℚ[S_n]` injective; `finsuppScalarRight` is an equiv. NB `MonoidAlgebra ℚ G` is defeq `G →₀ ℚ`,
  so `finsuppScalarRight` (four explicit args `R S M ι`; `N` is unused) applies even though `S_n` is non-commutative.
- **Equivariance** (intertwines `LinearMap.baseChange ℂ (spechtModuleActionK ℚ …)` with `spechtModuleActionK ℂ …`):
  one line, `j (of σ * x) = of σ * j x` + `mul_smul_comm`.
- Corestrict: `(LinearEquiv.ofInjective Ψ hinj).trans (LinearEquiv.ofEq … range_eq)`; the target
  `↥(p.restrictScalars ℂ)` is defeq to `↥p`, so the equiv lands in `↥(SpechtModuleK ℂ)` directly and
  `(Φ t : ℂ[S_n]) = Ψ t` is `rfl`.

### Base-change module `L ⊗[K] V` over `L ⊗[K] A` — build it, `TensorProduct.Algebra.module` fails (#5896/#5923, Problem 3.8.4)

To state anything about "`V ⊗_K L` as an `A ⊗_K L`-module" (scalar extension of a
representation to a field extension `L/K`), you need `Module (L ⊗[K] A) (L ⊗[K] V)` — and
**Mathlib has no such instance**. Two traps that cost real time:
- **Use Mathlib's scalar-on-left `L ⊗[K] V`, not the book's `V ⊗_K L`.** The `L`-on-right
  factor of `V ⊗[K] L` has no `Module L` instance; `TensorProduct.leftModule` only acts on the
  left factor. `L ⊗[K] V ≅ V ⊗_K L` canonically — note the swap in a docstring and move on.
- **`TensorProduct.Algebra.module` does not elaborate here** (it is a deliberate non-instance;
  the planner's suggestion to use it is a dead end). Even after supplying `Module A (L⊗V)` on
  the right factor + `SMulCommClass`/`IsScalarTower` by hand, `TensorProduct.Algebra.module`
  still fails to find `IsScalarTower K L (L⊗V)` *inside* its own elaboration (the same goal
  resolves standalone — a fragile diamond on the two scalar actions).

**Working recipe** (all real `def`s, no data-sorry; `Chapter3/Problem3_8_4.lean`,
`rep`/`repTensor`/`bcMod`): base-change the representation through `End`, then use the
universal property of the tensor algebra, then `compHom`:
```
rep       : A →ₐ[K] Module.End L (L ⊗[K] V) := (Module.End.baseChangeHom K L V).comp (Algebra.lsmul K K V)
repTensor : (L ⊗[K] A) →ₐ[L] Module.End L (L ⊗[K] V) := AlgHom.liftEquiv K L A (Module.End L (L ⊗[K] V)) rep
bcMod     : Module (L ⊗[K] A) (L ⊗[K] V) := Module.compHom (L ⊗[K] V) (R := Module.End L (L ⊗[K] V)) repTensor.toRingHom
```
Key lemmas: `Algebra.lsmul K K V : A →ₐ[K] End K V` (the `A`-action, needs `IsScalarTower K A V`);
`Module.End.baseChangeHom K L V : End K V →ₐ[K] End L (L ⊗[K] V)` (base change of endos, from
`LinearMap.baseChange`); `AlgHom.liftEquiv R S A B : (A →ₐ[R] B) ≃ (S ⊗[R] A →ₐ[S] B)` (needs
`IsScalarTower R S B`). Pin `R := Module.End …` explicitly in `compHom` or `V` stays a metavar.
Once `bcMod` is a (file-scoped) instance, `Module L (L⊗A)`, `Algebra L (L⊗A)` and
`FiniteDimensional L (L ⊗[K] V)` all resolve, and `≃ₗ[L ⊗[K] A]` statements typecheck.
Encode "`X` is a direct summand of `Y`" as a split injection `∃ i p, p ∘ₗ i = id` (avoids
quantifying over a complement type/universe).

### Base change distributes over a Wedderburn `∏ Matrix(D i)` — compose three `Algebra.TensorProduct` isos (#6147)

For "scalar extension commutes with a product of matrix algebras" (the semisimple base-change
count #6136 → field-general monotonicity #6127), `K ⊗[k] A ≃ₐ[K] ∏ᵢ Matrix (K ⊗[k] D i)` from
`A ≃ₐ[k] ∏ᵢ Matrix (D i)` is a clean three-step compose (all sorry-free, axiom-clean in
`Chapter4/Exercise4_2_3_BaseChangePiMatrix.lean`):
1. `Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) e` base-changes `e` along `k→K`
   (`congr (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : A ⊗[R] B ≃ₐ[S] C ⊗[R] D` — put `refl K` in the `f`/`S`
   slot, `e` in the `g`/`R=k` slot).
2. `Algebra.TensorProduct.piRight k K K (fun i => Matrix … (D i))` moves `K ⊗[k] -` inside the
   finite product (needs `[Fintype ι] [DecidableEq ι]`; `Fin n` has both).
3. `AlgEquiv.piCongrRight` glues a per-factor `matrixBaseChange`.

The per-factor `K ⊗[k] Matrix n n D ≃ₐ[K] Matrix n n (K ⊗[k] D)` is the only fiddly piece:
`congr refl (matrixEquivTensor n k D)` → `(Algebra.TensorProduct.assoc k k K K D (Matrix n n k)).symm`
→ **the `k`→`K` upgrade of `(matrixEquivTensor n k (K ⊗[k] D)).symm`**. `matrixEquivTensor` is only
stated `≃ₐ[k]`, but it *is* `K`-linear, so upgrade with a tiny helper:
```
def upgradeToK (f : X ≃ₐ[k] Y) (h : ∀ (c : K) x, f (c • x) = c • f x) : X ≃ₐ[K] Y :=
  { f with commutes' := fun r => by
      have hh := h r 1; rw [map_one] at hh
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]; exact hh }
```
(needs `[Algebra K X] [Algebra K Y] [IsScalarTower k K X] [IsScalarTower k K Y]`). The `map_smul`
hypothesis `h` for `(matrixEquivTensor …).symm` is a `TensorProduct` induction: `tmul` case is
`rw [TensorProduct.smul_tmul']; simp only [matrixEquivTensor_apply_symm]; exact smul_assoc c b _`.
`Algebra.TensorProduct.assoc`'s explicit args are `(T C D)` (here `T=K`); the `commRight`/
`cancelBaseChange` detour is unnecessary once you have `upgradeToK`.

### An `Algebra.adjoin`/`Submodule.span` object must be introduced *opaquely*, not as a `let` (#6158)

When a long proof needs a finitely generated subalgebra `R := Algebra.adjoin K {entries}`
(descent of a base-change iso to an f.g. subextension, Problem 3.8.4 `Problem3_8_4_Descent.lean`),
binding it with `let R := Algebra.adjoin K …` makes **every** downstream `isDefEq`/`whnf` try to
unfold the adjoin. The result is `(deterministic) timeout at whnf`/`isDefEq` scattered across the
proof — even in tactics that have nothing to do with `R`'s definition. Instead introduce it as an
opaque hypothesis via an existential:
```
obtain ⟨R, hFG, hmem₁, hmem₂⟩ :
    ∃ R : Subalgebra K L, R.FG ∧ (∀ i j, c i j ∈ R) ∧ (∀ j i, d j i ∈ R) := by
  refine ⟨Algebra.adjoin K (↑entries : Set L), Subalgebra.fg_adjoin_finset entries, ?_, ?_⟩
  …  -- Algebra.subset_adjoin + Finset.mem_union_left/right + Finset.mem_image
```
Now `R` is a bare fvar: unification never unfolds it, and only the membership facts you named are
available. Package the coordinates you need as `⟨c i j, hmem₁ i j⟩ : ↥R` with a
`have hval : ∀ i j, R.val ⟨c i j, _⟩ = c i j := fun _ _ => rfl` so `rw`s close by `rfl`.
Two more levers for these large tensor/descent proofs: (1) push all the arithmetic onto the given
`L`-iso `e` by going through the **injective** coefficient-inclusion maps
`incV := LinearMap.rTensor V R.val.toLinearMap` (injective by `Module.Flat.rTensor_preserves_
injective_linearMap`, `V` free over the field `K`), proving `incW ∘ φ = e ∘ incV` on the `↥R`-basis
and extending by `Basis.sum_repr` — this yields the inverse relations and `A`-equivariance without
ever computing `φ` on non-basis vectors; (2) expect to need `set_option maxHeartbeats 800000 in`
(with the required explanatory comment on the line *after* the `in`, not before).

### Upgrading `dim V_λ = 1` to the book's representation-iso claim (trivial/sign, #5637)

A recurring Chapter 5 fidelity-gap shape: the book says "`V_{(n)}` is the *trivial*
representation" / "`V_{(1ⁿ)}` is the *sign* representation", but the Lean only proves
`Module.finrank ℂ (SpechtModule n …) = 1`. Dimension `1` is necessary but **not**
sufficient — `Sₙ` has two one-dimensional reps, so the count cannot distinguish them.
State the genuine `ℂ[Sₙ]`-module claim instead: every `σ` acts as the identity (trivial)
resp. as `sign σ` (sign). Worked end-to-end in `Chapter5/Example5_12_3.lean`
(`Example5_12_3_trivial_rep`, `Example5_12_3_sign_rep`), sorry-free. The recipe, in two
cheap pieces:
- **Generator transformation** `of(σ) · c_λ = χ • c_λ` (χ = 1 resp. `sign σ`). For the two
  extremes one of the row/column subgroups is everything and the other is trivial: for
  `(n)`, `Q_λ = {1}` so `ColumnAntisymmetrizer = 1` and `c_λ = a_λ`, and `P_λ = Sₙ` so
  `of_row_mul_RowSymmetrizer` (Lemma5_13_1) gives `of(σ)·c_λ = c_λ`; dually for `(1ⁿ)`,
  `of_col_mul_ColumnAntisymmetrizer` gives the `sign σ` scaling. The subgroup
  characterizations are direct `rowOfPos`/`colOfPos` computations on the literal
  `[n]` / `List.replicate n 1` (no `Nat.find`), and "`b_λ = 1`" comes from a `Unique`
  instance on the trivial subgroup + `simp [ColumnAntisymmetrizer, …, Fintype.card_unique]`.
- **Collapse the module to `ℂ·c_λ`** so the action on *every* `v ∈ V` is forced by its
  action on the generator. `span ℂ {c_λ} ≤ V.restrictScalars ℂ` (since `c_λ ∈ V`), both
  have `finrank ℂ = 1` (`finrank_span_singleton hc_ne` and the already-proved `dim = 1`,
  which holds by `rfl` over `restrictScalars` — `↥(V.restrictScalars ℂ)` is defeq `↥V`),
  so `Submodule.eq_of_le_of_finrank_le` gives equality. Then any `v` is `z • c_λ`
  (`mem_span_singleton`) and `↑(of σ • v) = of σ * (z • c_λ) = z • (χ • c_λ) = χ • ↑v`
  via `Algebra.mul_smul_comm` + the generator lemma + `smul_comm`; `Subtype.ext` closes it.
  Get `c_λ ≠ 0` for free from `dim = 1` (if `c_λ = 0`, `V = ⊥`, `finrank = 0` by
  `Module.finrank_zero_of_subsingleton`). The collapse step is packaged as the reusable
  `spechtModule_smul_eq` — feed it `dim = 1` + the generator transformation. Note `↑(χ • v)`
  needs `Submodule.coe_smul_of_tower` (ℂ in the tower), while `↑(of σ • v)` uses
  `Submodule.coe_smul` (the algebra ring); `smul_eq_mul` turns the latter into `*`.

### Matrix Lie bracket (`𝔰𝔬(n)`, `𝔰𝔩`, §2.9 examples) is a *local* instance

**`LieRing (Matrix n n R)` from `LieRing.ofAssociativeRing` (`⁅a,b⁆ = ab − ba`) is NOT a global instance** — Mathlib declares it `attribute [local instance 100]`, active only inside `Mathlib/Algebra/Lie/OfAssociative.lean`. A `LieSubalgebra` like `LieAlgebra.Orthogonal.so n R` still works (its subtype's `LieRing`/`LieAlgebra` are baked in), but the moment you write the *ambient* matrix bracket `⁅A, B⁆` (e.g. in a `map_lie'` obligation, or via `LieSubalgebra.coe_bracket : ↑⁅x,y⁆ = ⁅↑x,↑y⁆`) you get `failed to synthesize LieRing (Matrix …)`. **Fix: re-enable it in your file with `attribute [local instance 100] LieRing.ofAssociativeRing`.** The priority `100` is deliberate: `Fin n → R` is also a ring, so this instance *would* diamond with `Cross.lieRing` (the cross-product bracket, itself a Mathlib non-instance you enable at default priority ~1000) — but the higher default priority of `Cross.lieRing` wins, so the vector bracket stays `⨯₃` and `bracket_eq_cross : ⁅u,v⁆ = u ⨯₃ v := rfl` is unaffected. **Worked sorry-free template: `Chapter2/Exercise2_9_5.lean` (#5965), the hat-map `LieEquiv (Fin 3 → ℝ) ≃ₗ⁅ℝ⁆ so(3)`.** Recipe: `hatFun v := !![0,-v 2,v 1; v 2,0,-v 0; -v 1,v 0,0]`; membership/linearity/`map_lie'`/`left_inv`/`right_inv` all discharge entrywise by `ext i j; fin_cases i <;> fin_cases j <;> simp [hatFun, cross_apply] <;> ring` (matrix `*` evaluates via default `!!`/`Fin 3` simp lemmas — `Matrix.mul_apply`/`Fin.sum_univ_three` are *unused* here); `right_inv` (reading entries off a skew matrix) needs the skew relations `A j i = -A i j` from `A.property` via `congrFun (congrFun ((mem_so _).1 A.property) i) j`, fed to `linarith`. Inside a `LieEquiv … where` block, unfold the subtype-`toFun` goal with `apply Subtype.ext` then `change` (not `show` — the style linter flags `show` for defeq goal changes).

### Matrix-conjugation reps `conjRep A N = A·N·star A` on a *variable* `N` — go through basis characters + `module`, NOT entrywise `simp` (Ch4 SO(3), #6547)

**Entrywise `simp [conjRep_apply, Matrix.mul_apply, Fin.sum_univ_three, …]` reduces `A·N·star A` at a fixed `(i,j)` only when `N` is a *concrete* `!!`-literal.** When `N` is a free variable (e.g. proving a V4 sign-averaging projection identity `N i j • wᵢⱼ = ¼(N − D₁·N − D₂·N + D₃·N)` for arbitrary `N ∈ U`), `simp` leaves `star !![…]` and a partial `![…] ᵥ* (N * …)` (`vecMul`/`dotProduct`) **un-evaluated** — the middle free factor blocks the `!!`-multiplication simprocs — and the closing `linarith`/`ring`/`linear_combination` then fails on the stuck goal. Adding `Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial` only helps partially (leaves `of fun i ↦ vecCons …ᵀ`). **Fix: never expand `conjRep g` on a variable entrywise. Instead (i) prove the 15 concrete character lemmas `conjRep g (wⱼ) = ± wₖ` on the fixed basis vectors `wⱼ` — those ARE `!!`-literals, so `ext i j; fin_cases … <;> simp [conjRep_apply, g, wbasis, Matrix.mul_apply, Fin.sum_univ_three]` closes them; (ii) rewrite the variable by its basis decomposition (`conv_rhs => rw [decomp N]` — use `conv_rhs`/`conv_lhs`, a bare `rw [decomp]` corrupts the `N i j` *coefficients* since `N i j` contains the pattern `N`); (iii) `simp only [map_add, map_smul, <the character lemmas>]` to push `conjRep` through linearity onto the basis; (iv) close with `module`.** Reading one entry off a `module`-proved wbasis form: `rw [that_form]; simp [wbasis, Matrix.add_apply]`. For `SO(3)` membership of a `45°`-rotation (`c45 = √2/2`, `c45_sq : c45*c45 = 1/2`): `mem_specialOrthogonalGroup_iff` → `⟨orthogonal, det⟩`; the orthogonal `ext i j; fin_cases <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [c45_sq]` (multi-goal, `<;>` correct), det on its own line `simp [Matrix.det_fin_three]` then `nlinarith [c45_sq]` (single goal — a `<;>` here trips the style linter). Worked sorry-free: `Chapter4/Problem4_12_11.lean` `tracelessSymSub_irreducible` (5-dim `W`) and `skewSub_irreducible` (#6539).

### `finrank` of a `FreeLieAlgebra`-quotient by presented relations (Ch2 2.16.3, #6324)

**Computing `finrank (FreeLieAlgebra k (Fin m) ⧸ relIdeal) = d` for a nilpotent presented Lie algebra** (worked sorry-free for `n=1`, dim 3 Heisenberg, in `Chapter2/Problem2_16_3.lean`; the `n=2`/`n=3` cases #6339/#6340 reuse the same scaffold). The recipe splits into a lower and an upper bound plus reusable infrastructure:

- **Generation of the free algebra** — `lieSpan k Free (Set.range (of k)) = ⊤`. Not in Mathlib; prove by *corestriction*: `let ι i : ↥H := ⟨of k i, subset_lieSpan ⟨i, rfl⟩⟩` where `H := lieSpan …`, `φ := FreeLieAlgebra.lift k ι : Free →ₗ⁅k⁆ H`, then `H.incl.comp φ = LieHom.id` by `FreeLieAlgebra.hom_ext` (agree on generators) + `rfl`; so `a = H.incl (φ a) = ↑(φ a) ∈ H`.
- **Projection as a `LieHom`** — the LieIdeal quotient's `mk` is only packaged as a `LieModuleHom` (`LieSubmodule.Quotient.mk'`). Wrap it: `{ (LieSubmodule.Quotient.mk' I).toLinearMap with map_lie' := fun {_ _} => rfl }`. Surjectivity is `LieSubmodule.Quotient.surjective_mk'`; `proj a = 0 ↔ a ∈ I` is `LieSubmodule.Quotient.mk_eq_zero`.
- **Generation of the quotient** — `lieSpan {x̄, ȳ} = ⊤` in the quotient: `rintro a -; obtain ⟨b, rfl⟩ := proj_surjective …`, prove `b ∈ lieSpan (range of)` from the free-generation lemma, then `induction … using LieSubalgebra.lieSpan_induction` — each case uses `proj`'s `map_add`/`map_smul`/`LieHom.map_lie` to push through.
- **Lower bound (independence)** — map into `gl_d(k) = Matrix (Fin d) (Fin d) k` (enable `attribute [local instance] LieRing.ofAssociativeRing`, see the note above) via `matHom := FreeLieAlgebra.lift k ![X, Y]` for explicit nilpotent matrices realizing the target algebra; show both relators `↦ 0` (so `relIdeal ≤ (matHom).ker` via `LieSubmodule.lieSpan_le` + `LieHom.mem_ker`), then a vanishing combination `∑ cᵢ • v̄ᵢ = 0` pulls back through `proj_eq_zero_iff` into `relIdeal ⊆ ker matHom`, giving `∑ cᵢ • matHom(gen) = 0` in `gl_d`; read off `cᵢ = 0` entrywise (`congrFun (congrFun h i) j` + `simp [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]`). Matrix commutators: `LieRing.of_associative_ring_bracket` (`⁅A,B⁆ = AB−BA`, is `rfl`) + `Matrix.single_mul_single_same`/`single_mul_single_of_ne` (simp discharges the `Fin` index `≠`). **Define elementary matrices as named `Matrix (Fin d) (Fin d) k` `def`s** — bare `Matrix.single 0 1 1` lets the index literals default to `ℕ` and the `⁅⁆`/`*` fail to synthesize. Note `Bracket` is *heterogeneous* (`Bracket L M`), so each argument's type is elaborated independently — a numeral-index `single` in the **second** bracket argument still defaults to `Matrix ℕ ℕ` even when the first arg is pinned to `Fin d`; pin *both* args (named `def`s, or one type-ascription per bracket arg).
- **Entrywise proofs over `Polynomial k` (loop-algebra / `gl_d(k[t])` work, e.g. `matHom₄` in `Chapter2/Problem2_16_3.lean`)** — plain `ext i j` **over-extends**: for scalar-`k` entries it stops at the entry equation, but when entries are themselves `ext`-able (`Polynomial k`) it keeps applying `Polynomial.ext`, leaving unsolvable `(…).coeff n✝ = …` goals that `ring` cannot touch. **Fix: bound extensionality to the matrix with `refine Matrix.ext fun i j => ?_`** (not `ext i j`), then `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply] <;> ring` closes each entry as a polynomial identity. Worked sorry-free template: `Chapter2/Problem2_16_3.lean` `range_matHom₄_not_finite_of_three_ne_zero` (#6387) — a period-2 ladder `Ψ(v) = ⁅⁅v,G₃⁆,G₁⁆` with `Ψ(p·r) = -9X²p·r` proving `range matHom₄` infinite-dimensional for `char k ≠ 3` (all obstructing scalars are powers of 3). Infinitude of a submodule: build an infinite `LinearIndependent` family (distinct `t`-degrees, pulled back along a single entry functional `entry21` to the monomial basis `Polynomial.basisMonomials` + `LinearIndependent.units_smul`), then `Module.Finite.not_linearIndependent_of_infinite`.
- **Upper bound (spanning)** — `Submodule.span {basis} = ⊤`. Build a `LieSubalgebra` whose carrier is that submodule (`{ Submodule.span … with lie_mem' := hclosed }`), proving closure `hclosed` by `Submodule.span_induction₂` (base case = every bracket of two basis elements lands in the span, using the relation lemmas; the linearity cases are `add_lie`/`lie_add`/`smul_lie`/`lie_smul` + `Submodule.add_mem`/`smul_mem`). Then `lieSpan {x̄,ȳ} = ⊤ ≤ W` (via `lieSpan_le` + `{x̄,ȳ} ⊆ span`) forces `W = ⊤`, hence the submodule is `⊤`.
- **Assemble** — `Module.Basis.mk hindep hspan` then `Module.finrank_eq_card_basis`, `Fintype.card_fin`. **`Basis` is `Module.Basis` in this Mathlib** (v4.32.0-rc1); import `Mathlib.LinearAlgebra.Basis.Basic`. Convert `Set.range ![a,b,c]` to `{a,b,c}` with `Matrix.range_cons`/`range_cons_empty` + `Set.singleton_union`.

**Infinite-dimensional (affine) case — `¬ Module.Finite k (Free ⧸ relIdeal)` (Ch2 2.16.3(b) `𝔤₄`, #6388, worked sorry-free in `Problem2_16_3.lean`).** Map into `gl_d(k[t]) = Matrix (Fin d) (Fin d) (Polynomial k)` with `x ↦ t·A`, `y ↦ B` (`matHom₄c := lift k ![NXc, NYc]`), so bracket words with `j` factors of `x` land in `t^j·gl_d(k)`. Exhibit a **climbing tower** `S₀` (a fixed low-degree bracket) with `Sₙ₊₁ = ⁅⁅y,x⁆, Sₙ⁆` and prove `matHom (Sₙ) = tⁿ⁺ᶜ • E` for a fixed nonzero matrix `E` by induction (base + a one-step lemma `⁅⁅y,x⁆, tᵐ•E⁆ = tᵐ⁺¹•E`). Then `LinearIndependent k (fun n => proj (Sₙ))` via `LinearIndependent.of_comp η` where `η : g →ₗ[k] k[t]` is the `(i,j)`-entry functional built with `Submodule.liftQ (relIdeal).toSubmodule ((Matrix.entryLinearMap k _ i j).comp matHom.toLinearMap) (…relIdeal ≤ ker…)` (the LieSubmodule quotient `M ⧸ N` is *defeq* to `M ⧸ N.toSubmodule`, so `liftQ` typechecks against `g` and `η (proj a) = (matHom a) i j` is `rfl`); `η (proj Sₙ) = tⁿ⁺ᶜ` are distinct monomials (`Polynomial.basisMonomials` + `LinearIndependent.comp (·+c)`). Close with `Module.Finite.not_linearIndependent_of_infinite` (needs `import Mathlib.LinearAlgebra.Dimension.Finite`).
  - **Finding the witness matrices is a search, not a recall.** The natural `𝔰𝔩₃`-loop realization (`x ↦ E₂₀·t`, `y ↦ E₀₁−E₁₂`) **collapses mod `p`** for the affine node's characteristic (`𝔤₄` dies to 4 dims over `𝔽₃`: every `𝔰𝔩₃` root vector has `ad`-weight divisible by 3, so the collapse is representation-independent). Search over `𝔽ₚ` for `A,B ∈ gl_d(𝔽ₚ)` with both relators `↦ 0` and the height-graded image climbing (a pure-Python mod-`p` bracket/BFS search over sparse `A,B` found a clean 4×4 witness in minutes; prefer sparse `{0,1,2}` entries for cheap `simp`). **Both relators may hold only mod `p`** — check which are ℤ-clean (here `ad(y)⁵x=0` over ℤ, `ad(x)²y=0` only mod 3) to know where `h3 : (3:k)=0` is needed.
  - **Char-`p` matrix-identity tactic recipe** (the relator/step/base lemmas): (1) collapse products with **full `simp`** (not `simp only` — the `Fin` `≠` side-goal of `single_mul_single_of_ne` needs the default simproc `Fin.reduceEq`) `[defs, LieRing.of_associative_ring_bracket, mul_add, add_mul, mul_sub, sub_mul, single_mul_single_same, single_mul_single_of_ne]`; (2) **`apply Matrix.ext; intro i j`**, NOT `ext i j` — over `Polynomial k` a bare `ext` keeps going into `Polynomial.coeff`, breaking `ring`; (3) fold all char-`p` content into a single `(p : Polynomial k) • (junk)` summand so the closing `Matrix.ext … <;> ring` is a **ℤ-clean identity** (uniform `ring`, no per-entry `linear_combination`), then `rw [key, three_eq_zero_poly k h3, zero_smul, add_zero]` where `three_eq_zero_poly : (3:k)=0 → (3:Polynomial k)=0` is `rw [← map_ofNat (Polynomial.C) 3, h3, map_zero]`; (4) **stage deep `ad`-strings** (`ad(y)⁵x`, a 4-fold nested `⁅x,ad(y)³x⁆`) as a chain of collapsed-single `have e1,e2,e3` — a single `simp` on the fully-nested bracket hits the `whnf` heartbeat **timeout**.

### Heavy Instance Resolves Abstractly but Fails Concretely

**A heavy instance (e.g. `centralizerModuleHom : Module ↥(centralizer …) (V →ₗ[A] E)`) that resolves for an *abstract* carrier `V` can fail fresh typeclass search for a *concrete* one (`V = Fin N → k`), at the same `synthInstance.maxHeartbeats` — it is structural, not a heartbeat shortfall (diagnosed across ~7 build cycles in #4860, `SchurWeylLDistinct.lean`).** Symptom: `failed to synthesize HSMul … ?m` (an `outParam` output stuck as a metavar) on a `•`/instance you wrote *freshly* in the concrete proof, while the *same* `•` typechecks when it comes from *specializing* a polymorphic lemma's signature. Two non-fixes and the fix:
- `haveI hI : Module … := …` registers the instance but makes it **opaque** — the `•` no longer reduces (`show (c • f) v = c.val (f v)` fails defeq), and it **shadows** the canonical instance so APIs expecting the canonical one mismatch.
- `letI hI := …` keeps it transparent (reduces) but **still shadows** — passing your term to a lemma whose signature used the canonical instance gives an "application type mismatch" unless your `letI` body is syntactically the canonical instance.
- **Fix:** never write the offending notation freshly in the concrete proof. (a) Obtain the goal *by specialization* — `refine polymorphicLemma … ?_` so the `•` in the `?_` goal is substituted from the lemma's signature, not searched. (b) Add an **abstract** `:= rfl` rewrite lemma over a general `V` (where the instance resolves), e.g. `theorem c_smul_eq (f) : c • f = (centralizerToEndA … c).comp f := rfl`, and `simp only [c_smul_eq]` in the concrete proof to eliminate the `•` entirely. The concrete proof then stays instance-notation-free.

### Tensor-Hom adjunction for Lie modules, and the `.toFun`-blocks-`simp` gotcha in structure-spread `map_lie'` (#6217)

**`Hom_𝔤(V ⊗ W, U) ≅ Hom_𝔤(V, U ⊗ W*)` (Problem 2.14.3, sorry-free in `Chapter2/Problem2_14_3.lean`).** Don't re-derive the adjunction — assemble Mathlib pieces at the *Lie-equivariant* level: (1) `TensorProduct.LieModule.liftLie k L V W U : (V →ₗ⁅k,L⁆ W →ₗ[k] U) ≃ₗ[k] (V ⊗ W →ₗ⁅k,L⁆ U)` is the already-equivariant tensor-Hom adjunction (its `.symm` peels `V ⊗ W` off the source); the middle `W →ₗ[k] U` carries `LinearMap.instLieRingModule` (bracket `⁅x,f⁆ m = ⁅x,f m⁆ − f⁅x,m⁆`), the *same* instance `liftLie` uses, so no defeq friction. (2) A Lie-module equiv `(W →ₗ[k] U) ≃ₗ⁅k,L⁆ U ⊗ W*` built from `dualTensorHomEquiv k W U` (an equiv because `W` is finite dim over a field — `Module.Free`/`Module.Finite` fire automatically) composed with `TensorProduct.comm k U (Module.Dual k W)`; the only real content is `map_lie'` (the map `u ⊗ φ ↦ (w ↦ φ(w)•u)` is 𝔤-equivariant, checked by `induction … using TensorProduct.induction_on` + `ext w`, using `TensorProduct.LieModule.lie_tmul_right`, `Module.Dual.lie_apply` (`⁅x,φ⁆ m = −φ⁅x,m⁆`), `LieHom.lie_apply`, `lie_smul`, `neg_smul`, then `abel`). (3) Postcompose a fixed source against a Lie-module equiv `d : B ≃ₗ⁅k,L⁆ C` to get the `k`-linear `(V →ₗ⁅k,L⁆ B) ≃ₗ[k] (V →ₗ⁅k,L⁆ C)` — hand-build the `LinearEquiv` with `toFun f := (d : B →ₗ⁅k,L⁆ C).comp f`, `invFun g := (d.symm : …).comp g`; all four `map_add'/map_smul'/left_inv/right_inv` are `by ext v; simp [LieModuleHom.comp_apply]`. Final term: `(liftLie …).symm.trans (congrHomRight d)`. There is **no** `LieModuleEquiv.ofBijective` (only the Lie-*algebra* `LieEquiv.ofBijective` at `Algebra/Lie/Basic.lean:652`); build the `LieModuleEquiv` by structure-spread `{ someLinearEquiv with map_lie' := … }` or via `.symm` of a bijective one.

**The gotcha that cost a build cycle:** when you construct a bundled morphism by spreading a `LinearEquiv`/`LieModuleEquiv` — `{ e with map_lie' := by … }` — the `map_lie'` goal is phrased with the *structure field* `toFun`, i.e. `(↑e).toFun x`, **not** the funlike coercion `e x`. So `simp only [LinearEquiv.trans_apply, TensorProduct.comm_tmul, dualTensorHom_apply, …]` (all stated about `⇑e`) **does not fire** and you get bare `unsolved goals` with an un-reduced `(↑(… ≪≫ₗ …)).toFun (…)`. **Fix: prepend `LinearMap.toFun_eq_coe, LinearEquiv.coe_coe` to the `simp only` set** (`toFun_eq_coe` rewrites `(↑e).toFun` → `⇑(↑e)`, `coe_coe` → `⇑e`); only then do the apply-lemmas match. Include them in the `add` induction case too (`simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe] at ha hb ⊢` before `simp only [lie_add, map_add, ha, hb]`).

### Destructuring an existential with chained instance fields → `letI`, not `haveI`

When you `obtain ⟨ι, _, S, acgS, modkS, …⟩` from a `∃ … (S) (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module k (S i)) …` and re-register the fields as instances, **`haveI : ∀ i, AddCommGroup (S i) := acgS` makes a *fresh opaque copy* `this`**, but the next field `modkS : ∀ i, @Module k (S i) _ (acgS i)` still mentions the *original* `acgS`. TC then has two incompatible `AddCommMonoid (S i)` paths (`this i` vs `acgS i`) and every downstream `Module`/`DirectSum`/`IsSimpleModule.congr` fails with `Type mismatch … (acgS i) vs (this i)`. **Fix:** use `letI := acgS` (transparent, no type annotation) for the *data* instances (`AddCommGroup`, `Module`, …) so `this i` reduces to `acgS i`; `haveI` is fine for `Prop` instances (`IsSimpleModule`, `IsScalarTower` — proof-irrelevant). Diagnosed in one cycle in #5405 (`SchurWeylPartition.lean`). To expose such a tower for a *submodule* carrier `S i = ↥(S' i)` from the producing theorem, just add `(_ : ∀ i, IsScalarTower k A (S i))` to its existential and discharge with `fun _ => inferInstance`.

### Reading a degree-`n` Tor/Ext group off a length-`1` resolution (Ch8, #6307)

To compute `Tor₁`/`Ext¹` of cyclic modules from a resolution `0 → P₁ → P₀ → M → 0`, feed the
short exact sequence to the repo's `Etingof.Functor.leftDerived_sixTerm_exact` (Tor) or
Mathlib's `Abelian.Ext.contravariantSequence`/`covariantSequence` (Ext). The window is an
exact `ComposableArrows _ 5`; extract facts with `hExact.exact' i j k` (gives
`(sc' i j k).Exact`) then `.ab_range_eq_ker` (in `AddCommGrp`: `f.hom.range = g.hom.ker`) and
`ShortComplex.exact_iff_mono`/`AddMonoidHom.range_eq_top`. `map'` of an `mk₅` reduces by
`dsimp`/defeq to the constructor arg. Then `Tor₁ ≅ ker(·a)`, `Ext¹ ≅ coker(·a)` on the
degree-`0` group, transported to the concrete model via naturality of
`Functor.leftDerivedZeroIsoSelf` (Tor) or `Abelian.Ext.addEquiv₀` + `mk₀_comp_mk₀` (Ext), and
closed with the number-theory isos. **Gotcha:** do **not** `set CS := <the sequence> with h` —
`set` makes `CS.obj i`/`CS.map' i j` opaque, so later `Submodule.map`/instance unification that
needs those to reduce definitionally fails (cost a cycle in #6307). Instead keep the sequence
inline (only `have hExact := …_exact …`) and name the connecting/functoriality maps as
*concrete-typed* `let`s (e.g. `let dhom : Ext S.X₁ Y 0 →+ Ext S.X₃ Y 1 := hS.extClass.precomp Y _`);
the exactness facts then unify against them by defeq. Also: `ℤ ⊗_ℤ N ≅ N` (`tensorOver ℤ N ℤ`)
needs `TensorProduct.lid` — the `Semiring.toModule ℤ` vs `AddCommGroup.toIntModule ℤ` diamond is
actually defeq here, so `lid` composes fine (don't over-engineer a bridge).

### Categorical `Projective (ModuleCat.of R P)` from `Module.Projective R P` — build the term, don't `inferInstance` (Ch9, #6382)

Proving infinite homological dimension (`homologicalDimension A = ⊤`) needs a projective
middle term for each syzygy SES. Two traps, both cost cycles in #6382:

- **Synthesis loop.** `ModuleCat.projective_of_categoryTheory_projective [Module.Projective R P] :
  Projective (of R P)` and `ModuleCat.projective_of_module_projective [Small R] [Projective P] :
  Module.Projective R P` are mutually recursive, so a bare `inferInstance`/`inferInstanceAs
  (Projective (of A P))` blows the **`synthInstance.maxHeartbeats` (20000)** budget (bumping
  `maxHeartbeats` does nothing — it's the *separate* synthInstance cap). Build the term directly:
  `@ModuleCat.projective_of_categoryTheory_projective A _ <object> <the Module.Projective witness>`.
- **Shared-carrier `Module` collision.** If two distinct modules share an `abbrev` carrier (e.g.
  `abbrev Pplus := Fin 2 → ℂ` *and* `abbrev Pminus := Fin 2 → ℂ`), their `Module A` instances have
  the same discrimination key `Module A (Fin 2 → ℂ)`; a *fresh* `ModuleCat.of A Pplus` written
  after both exist silently grabs the most-recently-declared one (wrong ρ). Reference the object
  that already baked in the right instance at its definition (`ses.X₂`, not a fresh `of A Pplus`),
  and pass the `Module.Projective` witness positionally so its bundled `AddCommGroup`/`Module`
  fields unify by defeq. (Cleaner long-term: give each module its own carrier — see the #6240 note
  above — but that is invasive once the concrete `Fin n → ℂ` block already compiles.)

Then the 2-periodic Ext-nonvanishing is a short induction: `ext_extClass_comp_ne_zero` (nonzero
`Extⁱ(X₁,Y)` maps to nonzero `Extⁱ⁺¹(X₃,Y)` for `i≥1` via `contravariant_sequence_exact₁` +
`eq_zero_of_hasProjectiveDimensionLT` on the projective middle) composes the two SES extension
classes; `homologicalDimension R = ⊤` follows from `∀ d, ¬ HasHomologicalDimensionLE R d` by
`le_antisymm le_top (le_iInf₂ (fun d hd => absurd hd (h d)))`.

### `finrank k (M →ₗ[A] N)` and Hom-into-product additivity (Cartan/multiplicity counting, Ch9 #6439)

Dimension-counting over a `k`-algebra `A` (Cartan matrices, `[N : Mᵢ]` multiplicities,
Euler characteristics) repeatedly needs `finrank k (M →ₗ[A] N)`. Useful facts:

- **Finiteness is automatic.** `LinearMap.finiteDimensional'` is an instance:
  `FiniteDimensional k (M →ₗ[A] N)` given `[FiniteDimensional k M] [FiniteDimensional k N]`
  and `[IsScalarTower k A M] [IsScalarTower k A N]` (it embeds `M →ₗ[A] N ↪ M →ₗ[k] N` via
  `restrictScalarsₗ`). So carry `IsScalarTower k A ·` on every module and `Module.Finite k ·`
  falls out — no manual subspace argument.
- **Freeness is NOT automatic.** `Module.Free.of_divisionRing` is not a global instance; if you
  need `Module.Free k ·` (e.g. for `Module.finrank_pi_fintype`), add
  `attribute [local instance] Module.Free.of_divisionRing` in your section.
- **Hom commutes with finite products in the 2nd arg**, always (no projectivity needed):
  build `(M →ₗ[A] ∀ s, Q s) ≃ₗ[k] ∀ s, (M →ₗ[A] Q s)` by hand
  (`toFun f s := (LinearMap.proj s).comp f`, `invFun := LinearMap.pi`), then
  `finrank_pi_fintype` gives `finrank (Hom into ⨁/∏) = ∑ finrank`. Convert `⨁`→`∏` with
  `DirectSum.linearEquivFunOnFintype`.
- **k-linearity of a postcomposition** `f ↦ e.comp f` for `e : M ≃ₗ[A] N`: the `map_smul'`
  goal reduces to `e (c • x) = c • e x` (`c : k`), closed by
  `LinearMapClass.map_smul_of_tower e c x` (the `CompatibleSMul` instance comes from the two
  `IsScalarTower k A ·`). `simp` will NOT fire the plain `LinearMap.map_smul_of_tower` on a
  bundled `≃ₗ`.
- **`Hom`-additivity on a SES with projective source** (`0→N'→N→N/N'→0`,
  `finrank_hom_additive_of_projective`, needs `[Module.Projective A M]`) is the tool when the
  sequence is not split; for an *explicit* finite direct sum the product-additivity above is
  cleaner (no projectivity, no submodule identification).

### Tactic Selection Guide

| Goal Shape | Try First | Then Try |
|-----------|-----------|----------|
| `⊢ a = b` (algebraic) | `ring`, `field_simp; ring` | `simp`, manual `rw` |
| `⊢ a = b` (categorical) | `simp [CategoryTheory...]` | `ext`, `aesop_cat` |
| `⊢ P ∧ Q` | `exact ⟨..., ...⟩` or `constructor` | split into subgoals |
| `⊢ ∃ x, P x` | `exact ⟨witness, proof⟩` | `use witness` |
| `⊢ P → Q` | `intro h` | `fun h => ...` |
| `⊢ ∀ x, P x` | `intro x` | lambda |
| Finite group theory | `decide` (small groups) | case analysis |
| Linear algebra | `ext`, `simp [LinearMap...]` | `apply LinearMap.ext` |
| Module homomorphisms | `ext`, `simp` | manual composition |

### `rw [ZMod.natCast_self]` fails to match `↑n` in `ZMod n` — use `CharP.cast_eq_zero` (#7508)

Proving `q² ≡ 1 (mod q²−1)` (Discussion 5.25.4), the step `rw […, ZMod.natCast_self, …]`
regressed with `Tactic rewrite failed: Did not find an occurrence of the pattern ↑?n` on the
goal `↑(q²−1) + 1 = 1` — even though `↑(q²−1) : ZMod (q²−1)` is visibly a nat-cast of the
modulus. `ZMod.natCast_self`'s `↑?n` LHS no longer unifies against the `ZMod` `NatCast`
instance during `rw`. **Fix: rewrite with `CharP.cast_eq_zero` instead** (`(↑p : R) = 0`
given `[CharP R p]`), which matches through the `CharP (ZMod n) n` instance. One-token swap;
watch for this across the ZMod/modular-arithmetic "restore fresh-buildable" issues.

### Enumerating a concrete finite group over `ZMod n` (`QuaternionGroup`, `DihedralGroup`, …) — #6068

Case-splitting a `ZMod n` index (e.g. proving a per-element fact for all of `QuaternionGroup 2`)
has two traps that each cost several build cycles:
- **`fin_cases i` on `i : ZMod n` yields anonymous `⟨k, ⋯⟩` constructor terms, NOT the literals
  `0,1,2,3`** — so `rw`/`exact` with lemmas stated at `a 3`, `xa 1`, … silently fail to match,
  and `simp` may also rewrite `a 0 ↝ 1` (via `a_zero`), hiding the constructor from your
  evaluation lemmas. Instead prove `zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide` once, then `rcases g with i | i <;> rcases zmod4_cases i with rfl|rfl|rfl|rfl`
  substitutes genuine literals that match literal-stated lemmas. (`decide` needs a closed prop:
  `revert i` first — `by decide` on the open `i` fails with "must not contain free variables".)
- **Group products (`a 1 * xa 0 = xa 3`) close by `decide`, but hoist each into a named `have`
  with explicit `(… : QuaternionGroup n)` ascription** before the `<;>` chain. An inline
  `simp only [show a 1 * xa 0 = xa 3 from by decide, …]` under `<;>` fails elaboration with
  "expected type must not contain metavariables". A bare `a 1` on a RHS also needs the ascription
  (its `n` is otherwise an unresolved metavariable).
- Concrete `ℂ` identities with `Complex.I` left after evaluation (e.g. `-s = I * (I * s)`) close
  uniformly with `norm_num [Complex.ext_iff]` (`ring`/`Complex.I_sq` are fiddlier because
  `ring_nf` leaves `I^2`, not `I*I`).
- Finite-dimensionality/basis of such a subspace: build an explicit `≃ₗ[ℂ] (Fin d → ℂ)` (forward
  = evaluate at coset reps, inverse = an explicit `liftFun` whose values the covariance forces),
  then `e.finrank_eq ▸ Module.finrank_fin_fun`. For irreducibility of a `d`-dim rep, exhibit two
  independent members of any nonzero invariant `U` (a nonzero `f` and a well-chosen `ρ(g) f`, via
  a `2×2` coordinate determinant `≠ 0`), then `Submodule.eq_of_le_of_finrank_le`.

### `rw [← h]` on an order/cardinality numeral that equals the `Fin n` size corrupts the motive (#6639, Ch5 A₅)

Working in `A5 = ↥(alternatingGroup (Fin 5))`, an order-`5` element `a` has `orderOf a = 5` — the
same numeral `5` as in `Fin 5`, which is baked into `a`'s *type*. So `rw [← horda]` (rewriting
`5 ↦ orderOf a` in a goal like `a ^ 5 = 1`) or `rw [ha_def, ← horda₀]` (in `orderOf a = 5`)
tries to generalize *every* `5`, including the one inside `Fin 5`, and fails with
`motive is not type correct` plus a spurious `Fintype (ToType {len := 4})` mismatch. The
identical proof shape for order-`3`/order-`2` elements works precisely because `3`/`2 ≠ 5`.
**Caveat — `4` collides too:** `Fin 5` normalizes to `Fin (4 + 1)`, so `rw [← h]` on a `4`
numeral (e.g. `rw [← kleinV_card…]` turning the target cardinality `4` back into
`Fintype.card ↥(kleinV …)` in a goal set over `A5 = alternatingGroup (Fin 5)`) hits the *same*
`motive is not type correct` / `Fintype (ToType {len := 4})` failure — the `4` unifies with the
one inside `Fin (4+1)`. So "safe because `≠ 5`" is wrong for `4`. **Fix:** rewrite *forward* only.
Prove the chain of plain equalities as separate `have`s
(`h1 : S.card = Fintype.card {g // p g}`, `h2 : Fintype.card {g // p g} = Fintype.card ↥K`,
`hK : Fintype.card ↥K = 4`) and close with `rw [h1, h2, hK]` (each step rewrites an `Fintype.card`
term forward, never the bare `4`). Relate `{g // p g}` to `↥K` with
`Fintype.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))` when `K`'s carrier is `{g | p g}`.
Worked example: `charval_A4_threeDim` in `Chapter5/Problem5_11_1.lean` (`hS1card`, #6707).
**Fix:** never rewrite the numeral. Rewrite the `orderOf`/order term instead:
- `have horda : orderOf a = 5 := by rw [ha_def]; exact (orderOf_injective H.subtype (Subgroup.subtype_injective H) a₀).trans horda₀` (compose, don't `← horda₀`).
- `have ha5 : a ^ 5 = 1 := by have h := pow_orderOf_eq_one a; rwa [horda] at h` (rewrite `orderOf a ↦ 5`, forward, not the numeral).

Same trap bites `Real.sqrt 5` vector literals: `![12, 0, 0, (-1 + Real.sqrt 5)/2, …]` compared to a
`: ℂ` character elaborates the vector as `Fin 5 → ℝ` and inserts a `↑(…)` coercion, so it won't
`rfl`-match a `ℂ`-side value with `↑√5`. Force `ℂ` by writing `(Real.sqrt 5 : ℂ)` inside the entries.

### Three cheap `rw`/`congr` traps when averaging/reindexing over `Fin n → Fin N` (#6829, Ch5 `Problem5_24_2_Bridge.lean`)

Proving `reynolds_injective` (block-symmetrization Reynolds operator on `End(V^{⊗n})`) surfaced three
recurring, easily-fixed pitfalls:

- **`congr 1` on `c • (big sum) = c • (big sum)` blows 200k heartbeats.** Stripping the scalar off a
  `((…).card : ℂ)⁻¹ • ∑ τ ∈ blockPerms, toMatrix M (a∘τ) (b∘τ)` equality via `congr 1` runs
  `isDefEq` on the full sums (index type `Fin n → Fin N`) and times out — *nondeterministically*, so
  it may pass one build and fail the next. **Fix:** prove the inner `∑ = ∑` as its own `have hsum`
  (e.g. by `Finset.sum_nbij'` reindexing) and finish with `rw [toMatrix_reynolds, toMatrix_reynolds,
  hsum]`. Never `congr 1` across a large `Finset.sum`.
- **`rw [← h]` with `h : BIG = 0` rewrites the *first* `0`, usually an inner `else 0`.** In a goal
  `∑ f, ∑ g, (if P then W f₀ g₀ else 0) = 0`, `rw [← h]` (meaning to expand the RHS `0`) instead
  hits the `else 0` inside the summand and corrupts the term. **Fix:** never `rw [← h]` to touch a
  bare `0`; rewrite *forward* with an explicit `rw [show LHS = LHS' from Finset.sum_congr …]` then
  `exact h`.
- **`congrFun hσ j` on `hσ : f ∘ g = f` yields `(f ∘ g) j`, which won't `rw` into a goal written as
  `f (g j)`.** `rw [congrFun hσ.2 j]` fails with "did not find `(slot ∘ ⇑σ) j`" against a target
  `slot (σ j) = slot j` (defeq but not syntactic). **Fix:** bind an explicitly-typed intermediate
  `have h2 : slot (σ j) = slot j := congrFun hσ.2 j` (defeq-tolerant `:=`), then `rw [h2]`. Same for
  `ρ (ρ⁻¹ j) = j`: use `Equiv.apply_symm_apply ρ j` (there is no `Equiv.Perm.apply_inv_self`; `ρ⁻¹`
  is defeq `ρ.symm`).

### Graph connectivity ("∃ edge-path" clauses) via `Relation.ReflTransGen`, and Fin-bound `omega` gotchas (#6762, Ch6 affine Dynkin `Problem6_1_3_continued_tildeE.lean`)

Connectivity clauses of the shape `∀ i j, ∃ path : List (Fin n), path.head? = some i ∧ path.getLast? = some j ∧ ∀ k (h : k+1 < path.length), adj (path.get ⟨k,_⟩) (path.get ⟨k+1,h⟩) = 1` are painful to build as raw lists. **Recipe:** work with `Relation.ReflTransGen (fun a b => adj a b = 1)` (built-in `.refl`/`.single`/`.head`/`.tail`/`.trans`), and convert *once* with a helper: `obtain ⟨l, hne, hchain, hhead, hlast⟩ := List.exists_isChain_ne_nil_of_relationReflTransGen h; refine ⟨l, ?_, ?_, ?_⟩` closing head/last by `rw [List.head?_eq_some_head hne, hhead]` / `List.getLast?_eq_some_getLast`, and the `get`-condition by `simpa [List.get_eq_getElem] using List.isChain_iff_getElem.mp hchain k hk`. Reduce full connectivity to reach-from-a-base: `symm` of `ReflTransGen` holds when `adj.IsSymm` (induct, flipping each edge via `hsymm.apply`), so `(reach i).symm.trans (reach j)`. For variable-rank families (cycle `Ãₙ`, chain `D̃ₙ`) prove `reach` by `induction` on the vertex index; for finite exceptional diagrams enumerate with `fin_cases`.
- **Edge chains and the `by decide` metavariable trap:** nested `Relation.ReflTransGen.head (b := ⟨1,by decide⟩) (by decide) (…)` fails with `Expected type must not contain metavariables` — the inner `by decide` for an edge fires before its endpoints are unified. **Fix:** make the edges `?_` goals in a skeleton and discharge them all afterwards: `refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_ (.single ?_)) <;> decide`. Needs the edge relation `abbrev` (not `def`) so `decide` sees through it to `adj a b = 1`.
- **`by omega` on a `Fin t.rank` bound can't see `rank`:** `⟨2, by omega⟩ : Fin (Dtilde n hn).rank` fails because omega treats `.rank` as opaque. Add `have hrank : (…).rank = n + 1 := rfl` in scope. Also, in a `∀ m, 2 ≤ m → m ≤ n-2 → … ⟨m, by omega⟩` statement the *unnamed* `→` hypotheses are NOT in scope for the bound's `by omega`; **name them** (`∀ m (_ : 2 ≤ m) (hmn : m ≤ n-2), …`) so omega can use them.
- **`subst h` picks the wrong variable:** with `h : v = n` and both `v`, `n` local, `subst h` may eliminate `n` (breaking every later `n`). Use `rw` with a `Fin.ext` equality instead: `have : (⟨v,hv⟩ : Fin _) = ⟨n, by omega⟩ := Fin.ext (by omega); rw [this]`.
- **`vertexDegree adj x = 3` is NOT defeq to your raw `(univ.filter (fun j => adj x j = 1)).card = 3` under `classical` (#6941):** `classical` in scope makes your inline `univ.filter (fun j => adj x j = 1)` synthesize a *different* `DecidablePred` instance than the one baked into the `vertexDegree` def, so `filterYours ≠ filterDef` as terms — `rfl`, `simpa [vertexDegree]`, and `unfold; congr 1` all fail, and `omega` treats the two `.card` terms as unrelated opaque nats. **Fix (bridge once, reuse):** `have hVD : ∀ x, vertexDegree adj x = (univ.filter (fun j => adj x j = 1)).card := by intro x; unfold vertexDegree; congr 1; ext j; simp only [Finset.mem_filter]` — the `ext`+`mem_filter` route is instance-agnostic. Then `rw [← hVD]` to feed a `vertexDegree = k` hypothesis into filter-card reasoning (and keep every inline filter written identically so they share the classical instance). This project has two `vertexDegree` spellings (`Etingof.vertexDegree` in `DynkinForward`, `Etingof.Problem6_1_3_E7E8.vertexDegree`); bridge each separately.

### Plugging a concrete `Type 0` group (`ZMod`, `Fin`, …) into a `∀ Q : Type u` hypothesis → `ULift` (#6101)

A theorem like `Exercise_8_2_9_i_finAb` quantifies its lifting hypothesis over `Q₁ Q₂ : Type u`
(the universe of the ambient `P`), but the natural witnesses (`ZMod (q^N)`, `ZMod q`) live in
`Type 0`. Applying `hP (ZMod (q^N)) …` then fails with "type mismatch: `ZMod (q^N) : Type` but
expected `Type u`". **Fix:** transport via `AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n`
(`import Mathlib.Algebra.Group.ULift`; `Finite (ULift _)` and `AddCommGroup (ULift _)` are
instances). Feed `ULift.{u} (ZMod …)` as `Q`, conjugate the reduction map and character by
`e := AddEquiv.ulift` / `e.symm`, and recover facts through `e.symm.injective`. This is *not*
needed when the target type is already built from a `Type u` parameter (e.g. the fin-dim
`k[x]`-module case with `k : Type u` makes `k[x]/(p^N) : Type u` directly). To prove
`Surjective (e2.symm ∘ f0 ∘ e1)`, take `y`, `obtain ⟨z, hz⟩ := hf0surj (e2 y)`, use `e1.symm z`,
and close with `rw [e1.apply_symm_apply, hz, e2.symm_apply_apply]`.

### Nonzero functional out of a finite/torsion group → killed-quotient + basis coordinate, not `Projective.exists_dual_ne_zero` (#6101)

To build a nonzero hom `P →+ ZMod q` from a finite abelian `P` with `q ∣ |P|` (the "character"
that a subgroup inclusion cannot give — a prime-order subgroup of `ZMod q²` is not a summand):
take `H = (q • AddMonoidHom.id P).range` (`q•` is non-injective by Cauchy's order-`q` element,
hence non-surjective as `P` is finite, so `H ≠ ⊤`), make `P ⧸ H` a `ZMod q`-vector space via
`QuotientAddGroup.zmodModule hHmem`, and extract a coordinate functional from
`Module.Basis.ofVectorSpace (ZMod q) (P ⧸ H)` + the contrapositive of
`Module.Basis.forall_coord_eq_zero_iff`. Two traps: (a) `Module.Projective.exists_dual_ne_zero`
gets its `[Projective]`/`[Free]` instance search **stuck over the `letI` module** — avoid it,
the `forall_coord_eq_zero_iff` route needs no `Projective` instance; (b) the bare `LinearMap`
coercion `⇑(b.coord i) x` fails to elaborate here — route through `(b.coord i).toAddMonoidHom`
and let defeq bridge to the Mathlib lemma's `b.coord i x`. Import surprises: `Field (ZMod p)` is
in `Mathlib.Algebra.Field.ZMod` (not `Data.ZMod.Basic`); `Module.Basis.ofVectorSpace` lives under
namespace `Module.Basis`; the order→dimension endgame uses `ZMod.addOrderOf_coe` +
`ZMod.natCast_eq_zero_iff` + `addOrderOf_dvd_natCard`.

### The `k[x]`-module analog (#6113): `fast_instance% Field` diamonds the torsion `Module`, so pass instances explicitly to `ofVectorSpace`

The fin-dim `k[x]`-module case of Exercise 8.2.9 (`Exercise_8_2_9_i_polynomial`) mirrors the
finAb proof over the PID `k[x]`: a monic irreducible factor `p` of the annihilator of a nonzero
`v` (via `LinearMap.toSpanSingleton`, `ker` a proper nonzero ideal — nonzero because
`Polynomial.not_finite`, proper because `1 ∉ ker`; monic factor from
`Polynomial.exists_monic_irreducible_factor`, NOT `normalize` which needs an unavailable
`DecidableEq k`) gives `p • ⊤ ≠ ⊤`; the `K = k[x]/(p)`-vector space `P/(p•⊤)`
(`Module.isTorsionBy_quotient_element_smul`, `Submodule.Quotient.nontrivial_iff`) yields a nonzero
functional; lift through `Ideal.Quotient.factorₐ : k[x]/(p^N) → k[x]/(p)` (surjective,
`factor_surjective`) with `N = dim_k P + 1`; coprimality `IsCoprime a (p^N)`
(`Irreducible.coprime_iff_not_dvd` + `.pow_right`) makes the lift a **unit**, so it is surjective and
`dim_k P ≥ dim_k k[x]/(p^N) = N·deg p > dim_k P` (`finrank_quotient_span_eq_natDegree`,
`natDegree_pow`, `LinearMap.finrank_le_finrank_of_surjective`, `Irreducible.natDegree_pos`).

**The one real trap (cost ~5 build cycles):** `Ideal.Quotient.field` is built with `fast_instance%`,
whose derived `Semiring (k[x]/(p))` is defeq to — but *syntactically different from* — the canonical
`Ideal.Quotient.commRing`-derived semiring that the `Module (k[x]/(p)) (P/p•⊤)` torsion instance is
registered over. So a `haveI : Field (k[x]/(p))` makes instance **search** for the module fail at
`Module.Basis.ofVectorSpace` (even with the module also provided via `letI` — search wants a
syntactic match). **Fix:** don't add a separate `Field` haveI; feed both instances explicitly, where
Lean unifies up to defeq:
`@Module.Basis.ofVectorSpace (k[x]/(p)) (P/p•⊤) (Ideal.Quotient.field _).toDivisionRing _
(Module.isTorsionBy_quotient_element_smul P p).module`. The `k[x]`-linear functional `φ : P → K` is
then built by hand (a `LinearMap` literal); its `map_smul'` bridges the `k[x]`- and `K`-actions with
`Module.IsTorsionBy.mk_smul` (turns `a • x` on `P/p•⊤` into `(mk a) • x`, matching the same torsion
instance fed to the basis) then `map_smul`, `smul_eq_mul`, `Algebra.smul_def`,
`Ideal.Quotient.algebraMap_eq`. No `ULift` is needed here (unlike finAb): `k : Type u` makes
`k[x]/(p^N) : Type u` directly.

### Structure/instance fields with interleaved implicit/explicit binders → `:= by intro <all>; exact …`

When a class field's type interleaves implicit and explicit binders (e.g.
`CategoryTheory.Congruence`'s `comp_left {X Y Z} (f) {g g'} : r g g' → …`),
both named-argument (`comp_left f h := …`) and `:= fun f h => …` forms mis-bind
— Lean's implicit-lambda insertion assigns your names to the wrong positions and
you get baffling "argument has type `Y ⟶ Z`" errors. This bites hardest when the
relation `r` is a *pullback* (`fun f g => Homotopic f.hom g.hom`) so the
hypothesis type doesn't reduce as written. Fix: use tactic mode and `intro`
**every** binder explicitly, `:= by intro X Y Z f g g' h; exact …`. Cost 4
build cycles on `Chapter7/Example7_1_3.lean` (#5640, homotopy category of spaces
as `CategoryTheory.Quotient TopCat homotopyRel`). That file is also the reusable
template for "build a quotient category": give `r : HomRel C`, prove
`Congruence r` (`equivalence` from the relation's `Equivalence`; `comp_left`/
`comp_right` from its composition-compatibility lemma), then
`abbrev Q := CategoryTheory.Quotient r` gets its `Category` instance for free.

### `rw`/`simp` fail to match Finsupp applications over `Tabloid` (Ch5 TabloidModule)

`Tabloid n la` is a `def` for `Quotient (TabloidSetoid n la)` (semireducible, NOT
reducible). `rw` and `simp only` match at *reducible* transparency, so when an
element `t` comes from `ext`/`Finset.ext` (typed `Quotient (TabloidSetoid …)`) a
Finsupp value `ψ t` produced by `Finsupp.smul_apply`/`sub_apply` is **not
syntactically equal** to a hand-written `ψ t` (or to a `ψ t = 0` from a lemma
whose binder is `: Tabloid n la`), even though they are defeq. Symptom: `rw [h]`
/`simp only [h]` reports "did not find pattern `ψ t`" or "unused" on a term that
visibly contains `ψ t`. This cost ~7 build iterations in #4998. Workarounds, in
order of preference:

1. **Introduce an explicit representative.** After `apply Finset.ext; intro t`,
   do `obtain ⟨a, rfl⟩ : ∃ a, toTabloid n la a = t := ⟨Quotient.out t, toTabloid_out t⟩`.
   Now every Finsupp application is over `toTabloid n la a`, which `rw` matches
   (this is why proofs like `twistedPolytabloid_per_q_decomp` that apply Finsupps
   to `toTabloid n la α` never hit the gremlin).
2. **Prefer `exact`/function application over `rw`.** Application typechecks up to
   defeq, so `exact h₁ h₂`, `hEq ▸ h`, and `Finsupp.support_smul hmem` work where
   `rw` fails. Reserve `rw` for terms you constructed yourself in the same goal.
3. **`show` to a hand-written / defeq form.** `Finsupp.smul_apply` is `rfl`, so
   `show c • ψ (toTabloid n la a) = 0` reaches a defeq goal whose hand-written
   `ψ (…)` then matches a `rw [hψ0]`; `show … ≠ 0` likewise re-normalizes a
   simp-mangled goal back so the next `rw` finds its pattern.

Separately: `Finset.le_sup`/`Finset.exists_mem_eq_sup` over a `ℕ`-valued
`f` need the `(f := fun t => …)` named argument, else instance resolution stalls
on `OrderBot ?m`.

### Assembling short exact sequences of `FDRep`s (Ch5 Cauchy det-quotient)

Feeding `formalCharacter_add_of_shortExact` (or any map between FDReps built as
`FDRep.of ρ`) hits three recurring defeq gremlins. Cost 4 build cycles in #5003
(`CauchyDetQuotientDegree.lean`, `quotDetDegreeFDRep_formalCharacter`); the
working pattern:

1. **The carrier `↑(FDRep.of ρ).V` does NOT accept a `(u : MvPolynomial …)`
   coercion.** SetLike isn't seen through the `FGModuleCat` wrapper, so
   `(u : MvPolynomial …)` fails with "type mismatch: ↑(twistFDRep …).V". Extract
   the underlying element with an explicit subtype map, like the existing
   `polyOf d := (homogeneousSubmodule …).subtype` (its `polyOf_rho` is `rfl`).
   Define one such `eU/eV/eW` per FDRep (ascribe its type `FDRep →ₗ[k] (ambient)`;
   the domain unifies by defeq) and state the action/inclusion facts as
   `rfl`-backed `have`s: `eU (M.ρ g u) = (ambient ρ) g (eU u)` and
   `eV (ι u) = mulDet (eU u)` are all `fun _ _ => rfl`, since `FDRep.of_ρ'`,
   `Subrepresentation.toRepresentation`, and `LinearMap.restrict` are definitional.
2. **`let`-bound maps hide `LinearMap.restrict` from `rw`.** `rw
   [LinearMap.restrict_coe_apply]` fails ("did not find pattern") when the map is a
   local `let ι := … .restrict …`, because the goal shows the opaque `ι`, not
   `restrict`. Don't rewrite with `restrict_coe_apply`; use the `rfl`-backed
   per-`let` `have`s from (1), and prove injectivity via
   `eU_inj := Subtype.coe_injective` then `apply mulDet_injective`.
3. **A term-mode `calc … := (lemma …).symm` over `glWeightSpace` of an FDRep can
   hang `isDefEq` (still timed out at 3.2M heartbeats).** Matching the calc's
   stated endpoint against the lemma's type triggers whnf of the FDRep carriers;
   if the weight-function arguments differ only by a beta-redex, Lean still unfolds
   the whole rep. Replace the `calc` with `rw [glWeightSpace_twistFDRep_pos …
   (fun i => …)]` supplying the weight **explicitly** (syntactic keyed matching, no
   whnf), then `congr 1; funext i; simp only [Finsupp.add_apply, …]; omega`. The
   SES assembly still needs `set_option maxHeartbeats` raised (~3200000) for the
   rank-nullity character argument even after these fixes.

### `evalGLAway` / `IsLocalization.Away.lift` rewrites blow up out of context (Ch5 det-localization)

`evalGLAway : Localization.Away (detPoly k N) →+* (GL → k)` is `IsLocalization.Away.lift …`.
Stating a *fresh* identity about it (e.g. `evalGLAway (localRightRep g φ) 1 = evalGLAway φ g`)
and proving it by `rw [evalGLAway_localRightRep]` or by `have h := evalGLAway_localRightRep g 1 φ`
**fails both ways**: `rw` reports "pattern not found" on a pattern that is *visually identical* to
the goal (the hidden `IsLocalization` instance arg won't unify), and the term application hits a
`whnf`/`isDefEq` timeout even at `maxHeartbeats 2000000`. The very same lemma rewrites fine
*inside* the file that proved it (e.g. `DetInvElim`), because there the goal already carries the
instance in the right shape. **Guidance:** don't repackage `evalGLAway` identities as standalone
lemmas in a new file; invoke `evalGLAway_localRightRep` (and friends) directly within a proof
context that already produced the localization term by rewriting, so the instance shape matches.
If you must state one fresh, expect to reproduce the original lemma's proof (the
`IsLocalization.ringHom_ext` localization-extension route), not to reuse it by `rw`/application.

### Dependent Pi Types and Pi.single

When working with `Pi.single` for dependent function types (e.g., `∀ i, Matrix (Fin (d i)) (Fin (d i)) k`), standard lemmas like `Pi.single_eq_same`, `Pi.single_add` do NOT work with `simp` because types differ across indices.

**Working pattern** — unfold to `Function.update` and manipulate `dite`:
```lean
ext t r s  -- go all the way to scalar level
simp only [Pi.single, Function.update, dite_apply, Pi.zero_apply, ...]
split
· next h => subst h; rfl  -- or simp
· simp  -- the ¬(i = t) case gives 0
```

Key insight: `ext t` alone leaves dependent casts (`⋯ ▸ x`). Go deeper with `ext t r s` to reach scalar goals where `subst` eliminates the cast.

### Recursive defs on inductives: use the recursor when you need `rfl` equation lemmas

When you define a function on an inductive (e.g. `Quiver.Path`, recursing on `cons`) with
**equation-compiler syntax** (`| _, nil => …` / `| _, cons p e => …`), the compiled term may use
non-reducing `brecOn`, so the obvious `@[simp] theorem foo_nil … := rfl` / `foo_cons … := rfl`
**fail** ("not definitionally equal" / `rfl : ?m = ?m` against the expected type). This cost a build
cycle on `pathMap` (Ch2 #5222, `Discussion_quiver_rep_bijection.lean`). **Fix:** define it term-mode
via the recursor with an explicit motive, then the equations are genuine `rfl`:
```lean
noncomputable def pathMap (R …) {a b : Q} (p : Quiver.Path a b) : … :=
  Quiver.Path.rec (motive := fun b _ => …) LinearMap.id (fun _ e ih => ih ∘ₗ R.mapLinear e.op) p
@[simp] theorem pathMap_nil  … := rfl   -- now works
@[simp] theorem pathMap_cons … := rfl   -- now works
```
`induction p with | nil | cons …` still works on top of the recursor def (it just uses these simp
lemmas). Separately: when a lemma over a section with `variable [DecidableEq Q]` does not actually
use it (the `pathMap_*` lemmas don't), the `unusedDecidableInType` linter warns — prefix the lemma
with `omit [DecidableEq Q] in` (placed *before* any docstring).

### Representation Theory Patterns

This book covers:
- **Chapters 1-3:** Basic algebra (associative algebras, quivers, Lie algebras)
- **Chapters 4-6:** Representation theory fundamentals (representations, characters, tensor products)
- **Chapters 7-10:** Advanced topics (structure theorems, categories, Hopf algebras)

**Key Mathlib imports for this book:**
```
Mathlib.Algebra.Algebra.Basic
Mathlib.RingTheory.TensorProduct.Basic
Mathlib.Representation.Basic
Mathlib.Algebra.Lie.Basic
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.LinearAlgebra.TensorProduct.Basic
Mathlib.GroupTheory.GroupAction.Basic
```

**When Mathlib doesn't have it:** This is the most important work in the project — prove it here. Check the `.refs.md` file for the item. If coverage is "gap", build the definition and proof from scratch. These are the highest-priority items, not items to defer. If the book proves the result (or assigns it as an exercise with hints), follow the book's approach. If it's genuinely external mathematics, prove it anyway — that's what this project is for.

#### "Central element / equivariant endo acts as a scalar" on a simple `FDRep` — stay categorical, skip the `Simple`↔`IsSimpleModule` bridge (Ch4 #6072, Problem 4.5.2)

When you need "operator `T` on a simple `FDRep ℂ G` commutes with the action ⟹ `T = c • id`"
(the Schur-scalar step of central-character / idempotent computations), **do not** try to
turn categorical `[Simple V]` into `IsSimpleModule ℂ[G] V.ρ.asModule` to feed
`Etingof.Corollary_2_3_10` — that forward bridge is a real rabbit hole (essential-image
closure under subobjects). Instead work in the invariants of `linHom` exactly like
`Chapter4/Proposition4_7_1.lean`:

```lean
-- T ∈ (Representation.linHom V.ρ V.ρ).invariants  ⟺  ∀ g, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T
-- via Representation.linHom_apply and V.ρ g ∘ₗ V.ρ g⁻¹ = id (← map_mul, mul_inv_cancel, map_one)
have h1dim : finrank ℂ (Representation.linHom V.ρ V.ρ).invariants = 1 := by
  rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
  exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ V
-- id is a nonzero invariant (trace id = finrank ≠ 0), so finrank_eq_one_iff_of_nonzero'
-- gives every invariant = c • id.  Pin c by trace: trace (c • id) = c * finrank.
```

`finrank_endomorphism_simple_eq_one` and `invariantsEquivFDRepHom` both take categorical
`[Simple V]` directly. The scalar is then read off from `LinearMap.trace`, and for
group-algebra elements the trace is a character sum closed by `FDRep.char_orthonormal`
(`= |G|` on the diagonal via `if_pos ⟨Iso.refl V⟩`, `0` off-diagonal). Centrality of the
element (needed for the commuting hypothesis) is cleanest proved once at the `ℂ[G]` level
(`ψ * single h 1 = single h 1 * ψ` by a `Fintype.sum_equiv` conjugation reindex `g ↦ h⁻¹gh`
+ `char_conj`), then transported through `asAlgebraHom` (an `AlgHom`, so `map_mul`) with
`Module.End.mul_eq_comp`. See `Etingof.endo_scalar` in `Chapter4/Problem4_5_2.lean`.

#### The *reverse* bridge `IsSimpleModule ℂ[G] ρ.asModule ⟹ Simple (FDRep.of ρ)` IS tractable — but mind the `asSubmodule` vs `toRepresentation.asModule` non-defeq (Ch4 #6247)

Opposite to the rabbit hole above: when you *have* module simplicity and *want* categorical
`Simple`, use `Etingof.simple_fdRepOf_of_isSimpleModule ρ` (`Chapter4/Exercise4_2_3.lean`,
field-general, no `NeZero`/`IsAlgClosed` needed). This is exactly how an `IsIrredSub`/atom
subrepresentation summand becomes a `Simple (FDRep.of σ.toRepresentation)` you can feed to
completeness (`simple_iso_irrepA5`) and `FDRep.char_orthonormal`. **Gotcha that cost a build
cycle:** the two `ℂ[G]`-module structures `σ.asSubmodule` (submodule of `ρ.asModule`, what
`isIrredSub_iff_isSimpleModule`/`Subrepresentation.asSubmodule` gives you) and
`σ.toRepresentation.asModule` (what `simple_fdRepOf_of_isSimpleModule` wants) are **NOT defeq** —
`haveI : IsSimpleModule … σ.toRepresentation.asModule := hAsSubmodule` fails with a module-instance
type mismatch. Transport with `IsSimpleModule.congr (toRepAsModuleEquiv σ)` (the identity map on
the shared carrier `↥σ.toSubmodule`, `ℂ[G]`-linear by `MonoidAlgebra.induction_linear` +
`Representation.single_smul`). The ready-made `Etingof.isSimpleModule_toRepresentation_asModule`
+ `toRepAsModuleEquiv` live in `Chapter5/SimpleSubrepExtraction.lean`; a **Chapter 4** consumer must
**inline** the ~12-line `toRepAsModuleEquiv` def (importing Ch5 into Ch4 is a backwards dependency).
See `subFDRep_simple` in `Chapter4/Problem4_12_5.lean`.

#### Dual / contragredient representation as a genuine opposite-module instance (#5593, twins #5355/#5356)

A recurring fidelity-gap family: a "dual representation `V*`" definition aliased to
the bare dual carrier (`abbrev DualRep k V := Module.Dual k V`) drops its *defining
data* — the contragredient action — and is flagged as a `gap`. The fix is to
**construct the action as a real instance**, not just keep the carrier. For an
algebra rep (`V` an `A`-module over base ring `k`, `[SMulCommClass A k V]`), the
dual `Module.Dual k V` is a left `Aᵐᵒᵖ`-module via `(op a • f)(v) = f(a • v)`:

```lean
instance : SMul Aᵐᵒᵖ (Module.Dual k V) where
  smul a f := f.comp (DistribSMul.toLinearMap k V a.unop)   -- (a • f) v = f (a.unop • v), rfl
instance : Module Aᵐᵒᵖ (Module.Dual k V) where
  one_smul f := by ext v; simp
  mul_smul a b f := by ext v; simp [mul_smul]               -- unop reverses: (a*b).unop = b.unop*a.unop
  add_smul a b f := by ext v; simp [add_smul]
  …                                                          -- smul_zero/smul_add/zero_smul: ext v; simp
```

Then a `@[simp]` lemma `(a • f) v = f (a.unop • v)` (proof `rfl`) records the book's
defining equation, and an `example : Module Aᵐᵒᵖ (DualRep …) := inferInstance`
witnesses it. The Lie-algebra twin (#5356, `Definition2_14_2.lean`) instead reuses
Mathlib's prebuilt `Module.Dual.instLieRingModule`. Worked example:
`Chapter3/Definition3_3_2.lean`. Two general syntax traps that each cost a build cycle:

- **`Aᵒᵖ` is `Opposite` (category theory); the multiplicative opposite is `Aᵐᵒᵖ`
  (`MulOpposite`).** Using `ᵒᵖ` for an algebra gives a bare `expected token` parse
  error. Import `Mathlib.Algebra.Module.Opposite` for the notation and `Module Aᵐᵒᵖ`
  prerequisites, and `Mathlib.Algebra.Algebra.Defs` if you reference `Algebra k A`.
- **`omit [Inst] in` must precede the docstring AND the attributes**, i.e.
  `omit [Algebra k A] in` / `/-- … -/` / `@[simp]` / `theorem …`, in that order.
  Placing it after the docstring (or after `@[simp]`) is a parse error. Use it to
  silence the "automatically included section variable unused" warning for a lemma
  (e.g. the `rfl` defining-equation lemma) that doesn't touch every section variable.

#### Adjunction / universal-property examples — Mathlib usually has both directions (#5644, Example7.6.3)

Lists of "adjoint functor" examples (Etingof 7.6.3: `V⊗ ⊣ V*⊗`, `Res ⊣ Ind`, UEA,
group algebra, tensor/symmetric algebra) almost all reduce to a Mathlib universal
property or a packaged adjunction — formalize each as the relevant equivalence,
not by hand-building counits:
- Algebra free-object adjunctions → the `.lift` hom-set `≃`: `UniversalEnvelopingAlgebra.lift`,
  `MonoidAlgebra.lift` (`(G →* A) ≃ (k[G] →ₐ[k] A)`), `TensorAlgebra.lift`,
  `SymmetricAlgebra.lift`. For the book's `GL₁(A) = Aˣ` phrasing, pre-compose with
  the units bijection `(G →* Aˣ) ≃ (G →* A)` (`MonoidHom.toHomUnits` / `Units.coeHom`);
  note `MonoidHom.toHomUnitsMulEquiv` needs `CommMonoid`, so for noncommutative `A`
  build the plain `Equiv` by hand (`left_inv`/`right_inv` by `ext; simp`). These `.lift`
  defs are `noncomputable` — mark the wrapper `noncomputable def`.
- Tensor/dual biadjunction → in the rigid category `FDRep k G` (rigid for `[Field k]
  [Group G]`), `CategoryTheory.tensorLeftAdjunction Y Y' : tensorLeft Y' ⊣ tensorLeft Y`
  from the exact pairing. With `V`'s right dual `Vᘁ` (`= V*`): `tensorLeftAdjunction V Vᘁ`
  gives `V*⊗ ⊣ V⊗`; for the reverse, `tensorLeft V ⊣ tensorLeft Vᘁ`, supply
  `haveI : ExactPairing Vᘁ V := BraidedCategory.exactPairing_swap V Vᘁ` (FDRep is braided)
  then `tensorLeftAdjunction Vᘁ V`. Together they witness "V*⊗ is left *and* right adjoint".
- **A fidelity finding of "Lean states the OPPOSITE adjoint direction from the book"
  is often a non-issue: Mathlib ships both directions.** Frobenius reciprocity has
  `Rep.indResAdjunction` (`Ind ⊣ Res`) *and* `Rep.resIndAdjunction`/`Rep.resCoindAdjunction`
  (`Res ⊣ Ind`/`Res ⊣ Coind`, finite index, since `Ind ≅ Coind`). Before treating an
  adjoint-direction discrepancy as a real gap, grep for the other-direction adjunction;
  record both with docstrings explaining the biadjointness rather than "fixing" one.
- **A fidelity finding of "the bridge linking the computed shadow to the real
  object is assumed implicitly" — check whether that bridge is already a proved
  Proposition in the project before treating it as a doc-only caveat or a big new
  theorem.** (#5639, Example 6.8.5: the example computed the reflection-functor
  action via an ad-hoc combinatorial `D₄_simpleReflection` on `Fin 4 → ℤ`,
  disconnected from the functors F⁻ᵢ. But `Etingof.Proposition6_6_8_source` already
  proves the BGP bridge `d(F⁻ᵢ V) = sᵢ(d(V))` sorry-free.) The fix is neither
  documentation-only nor a new bridge theorem: **re-express the example with the
  genuine infrastructure** the proved Proposition is stated over — here
  `Etingof.simpleReflection`/`Etingof.cartanMatrix`/`Etingof.simpleRoot` (Defs
  6.4.10/6.4.1/6.4.5) in place of the ad-hoc copies — and cite the Proposition in
  the docstring. The numerics stay `decide`-able and the functor↔shadow identification
  stops being implicit. Grep the relevant Proposition/Corollary files (e.g. the
  `_source`/`_sink` dimension-vector lemmas) before assuming the connection is missing.

#### `IsSimpleModule k[G] ρ.asModule` for a *concrete* representation (Ch5 Example5.1.3 Q₈, #5124)

To prove a hand-built representation `ρ : Representation k G V` is irreducible
(its `asModule` is simple), do **not** reason about `Submodule k[G] ρ.asModule`
directly — work with `ρ`-invariant `k`-subspaces of `V` and transport:

- `Representation.mapSubmodule ρ : ρ.invtSubmodule ≃o Submodule k[G] ρ.asModule`
  is the order iso (in `Mathlib.RepresentationTheory.Submodule`).
- `OrderIso.isSimpleOrder_iff` turns `IsSimpleOrder ρ.invtSubmodule` into
  `IsSimpleOrder (Submodule k[G] ρ.asModule)`. `IsSimpleModule` *extends* that
  `IsSimpleOrder`, but its constructor has **no explicit fields** (the parent is
  instance-implicit): do `suffices hSO : IsSimpleOrder ρ.invtSubmodule by
  haveI := (Representation.mapSubmodule ρ).isSimpleOrder_iff.mp hSO; exact ⟨⟩`.
- Build `IsSimpleOrder ρ.invtSubmodule` via
  `refine { eq_bot_or_eq_top := fun a => ?_ }` (the `Nontrivial` parent comes
  from the existing `[Nontrivial V]` instance). `a : ρ.invtSubmodule`; recover
  the underlying subspace as `(a : Submodule k V)` and its invariance from
  `(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := ρ g)).mp
  ((Representation.mem_invtSubmodule (ρ := ρ)).mp a.2 g)` — both lemmas take the
  endomorphism/representation **explicitly**, so pass `(f := …)`/`(ρ := …)` or
  the bare `name.mp` reads as an unknown constant.
- Then the math: `a ≠ ⊥` ⇒ pick `0 ≠ v ∈ a` (`(Submodule.ne_bot_iff _).mp`),
  apply two generators (as explicit `Matrix.mulVec` evaluations) to manufacture
  the standard basis vectors inside `a` via `smul_mem`/`sub_mem`/`neg_mem`, then
  `eq_top` from "two basis vectors span". For a 2-dim rep this is the "diagonal
  generator and swap share no common eigenline" argument.

#### *Consuming* `IsSimpleModule k[G] ρ.asModule` to bound `finrank` (Ch4 Problem4.12.1, #5997)

The reverse direction — given `hρ : IsSimpleModule k[G] ρ.asModule` as a hypothesis,
deduce a *dimension bound* by exhibiting a concrete spanning invariant subspace — is
cleanest via the **`Subrepresentation` structure** (root namespace, from
`Mathlib.RepresentationTheory.Subrepresentation`), not `invtSubmodule`:
- `Representation.IsIrreducible ρ` is `abbrev`-defined as `IsSimpleOrder (Subrepresentation ρ)`;
  `haveI hirr : Representation.IsIrreducible ρ :=
  (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ` registers the instance
  (and first `haveI := hρ` so `IsSimpleModule.nontrivial (R := k[G]) (M := ρ.asModule)` gives
  `Nontrivial V` — `ρ.asModule` is *definitionally* `V`, so ascribe `Nontrivial V` directly).
- Build the invariant subspace as a `Subrepresentation ρ` literal:
  `{ toSubmodule := Submodule.span k S, apply_mem_toSubmodule := … }`. Prove invariance by
  `intro g x hx; induction hx using Submodule.span_induction with | mem … | zero => simp
  | add … => rw [map_add]; exact add_mem … | smul … => rw [map_smul]; exact smul_mem …`; the
  `mem` case reduces to showing `ρ g` sends each generator into the span (case-split `g` on
  the group's constructors).
- `IsSimpleOrder.eq_bot_or_eq_top Sub : Sub = ⊥ ∨ Sub = ⊤`. `(⊥/⊤ : Subrepresentation ρ).toSubmodule`
  is `⊥`/`⊤` **by `rfl`** but `rw [h]` won't auto-close it — append `; rfl`. Rule out `⊥` from a
  nonzero member; then `Sub.toSubmodule = ⊤` gives `Submodule.span k S = ⊤` (defeq), and
  `finrank_le_of_span_eq_top (v := ![…])` + `Module.finrank_pos` pin `finrank ∈ {1,…,#S}` (`omega`).
- Gotchas: endomorphism-composition application is `Module.End.mul_apply` (**not**
  `LinearMap.mul_apply`, which does not exist); eigenvector power law `f^n v = μ^n • v` is
  `Module.End.HasEigenvector.pow_apply`; `Module.End.exists_eigenvalue` needs
  `[IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]`. For `DihedralGroup N`,
  `r j = (r 1)^j.val` via `DihedralGroup.r_one_pow` + `ZMod.natCast_zmod_val` (needs `[NeZero N]`),
  and the relations are `r_mul_r`/`r_mul_sr`/`sr_mul_r`/`sr_mul_sr`.

**Faithful "completely reducible / semisimple" statement (anti-vacuity, #5384).**
To say a representation `ρ : Representation k G V` is *completely reducible*, write
`IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule` — semisimplicity of the
*`k[G]`-module*. Do **NOT** write `IsSemisimpleModule k V`: over a field every
vector space is semisimple, so that conclusion is **vacuous** and carries zero
representation content (this was the exact bug in `Theorem5_23_2_i`). The `k[G]`
form is genuine content precisely because `k[G]` is not a semisimple ring for
infinite `G` (e.g. `GL_n(k)`). Type `ρ` as `Representation` (not a bare `→*`) so
`.asModule` resolves. Same anti-vacuity smell elsewhere: a Peter-Weyl / decomposition
`X ≅ ⊕ …` stated as a bare `k`-linear (or rank-matching `nonempty_linearEquiv_of_rank_eq`)
iso is vacuous — the real claim is a `G`-(or `G×G`-)*equivariant* iso, which needs
the actual `Representation` structures on both sides.

Build matrix reps as a `MonoidHom G →* Matrix n n k` composed with
`Matrix.toLinAlgEquiv'` (a monoid hom into `End`); `ρ g v = (Mhom g).mulVec v`
via `Matrix.toLinAlgEquiv'_apply`. **`ring` does not work on the noncommutative
matrix ring** — for `A^4 = (A^2)^2` use `pow_mul`; for `(-1)^2` use
`neg_one_sq`; reduce `A^a = A^b` (same base, `A^4=1`) to a `ZMod`-exponent
equality with a `Nat.div_add_mod`/`pow_add`/`pow_mul` helper plus
`ZMod.natCast_eq_natCast_iff`, then close non-`ring` modular facts (e.g.
`3*i ≡ -i [4]`) with `decide`. An `SL₂` rep preserves the wedge form
`B(v,w)=v₀w₁−v₁w₀` automatically: `B(Nv,Nw) = det N · B(v,w)` (a `Fin 2`
`ring` identity), so invariance reduces to `det (ρ g) = 1`.

#### FDRep of a homogeneous polynomial component (Ch5 Cauchy/Schur-Weyl, #4934)

To state a `formalCharacter` identity on a degree-`d` piece of `A = k[Xᵢⱼ]` you
need that piece as an `FDRep`. Recipe (sorry-free):
- finite-dimensionality of `MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d`:
  it sits inside `MvPolynomial.restrictTotalDegree _ _ d` (a degree-`d`
  homogeneous poly has total degree `≤ d` via `IsHomogeneous.totalDegree_le` +
  `mem_restrictTotalDegree`), which is `Module.Finite` for finitely many vars —
  conclude with `Submodule.finiteDimensional_of_le`.
- package: take the existing `Subrepresentation` of the homogeneous component
  (e.g. `polyRightHomogeneousSubrep`, `PolyRightGrading.lean`), then
  `FDRep.of (subrep.toRepresentation)`. `FDRep.of` needs `[Module.Finite k V]`,
  which the `FiniteDimensional` instance supplies (defeq over a field).
- Gotcha: `open MvPolynomial` did **not** expose `homogeneousSubmodule` /
  `restrictTotalDegree` / `mem_restrictTotalDegree` in an `instance` signature
  under `relaxedAutoImplicit false` — fully qualify with `MvPolynomial.`.

#### Universe 0 + explicit `(k : Type)` in the GL-rep decomposition cluster (#5478)

The polynomial-decomposition machinery (`decompose_polynomial_gl_rep`,
`polynomialRep_isSemisimple`, anything built on `FDRep.of` of a GL-rep) is pinned
to **universe 0**: their files open with `variable (k : Type) ... (N : ℕ)`, not
`Type*`. Two consequences when *consuming* these from an upstream theorem (e.g.
discharging `Theorem5_23_2_i`, and the same will hit part (ii)):
- **Specialize the carrier too.** It is not enough to set `k : Type`; the
  representation carrier `Y` must also be `Type` (universe 0), because `FDRep.of`
  forces it. Symptom if you forget: `Representation.{0,0,u} … but expected
  Representation.{0,0,0}`. (Contrast the general advice elsewhere that reps
  "often need `Type*`" — this cluster is the exception.)
- **`k` and `N` are explicit positional args.** `polynomialRep_isSemisimple` etc.
  take `k` then `N` *before* the `FDRep`/hypothesis args, since the section
  `variable (k : Type) (N : ℕ)` uses `()`. Call as
  `polynomialRep_isSemisimple k n (FDRep.of …) (…)`. Symptom if you omit them:
  the `FDRep` binds to `k`, giving nonsense like `failed to synthesize Field ↑(…).V`
  and a stray hypothesis of type `ℕ`.
- Assembly chain that works: `IsAlgebraicRepresentation.exists_detPow_twist_isPolynomial`
  (det-clearing) → `charTwistRep (detChar k n ^ s) ρ` (its `⇑` is `fun g =>
  det(g)^s • ρ g` via `MonoidHom.pow_apply` + `Units.val_pow_eq_pow_val`) →
  `polynomialRep_isSemisimple` → untwist by `(detChar k n ^ s)⁻¹` with
  `isSemisimpleModule_charTwistRep` (`charTwistRep c⁻¹ (charTwistRep c ρ) = ρ`
  closes by `rw [charTwistRep_apply, charTwistRep_apply, smul_smul, ← Units.val_mul,
  ← MonoidHom.mul_apply, inv_mul_cancel, MonoidHom.one_apply, Units.val_one,
  one_smul]`). `charTwistRep`/`detChar` live in `Etingof.KernelLemmaKPrime`.
- **Weight-spanning (`⨆ glWeightSpace = ⊤`) of a `det`-twist needs the twist to be genuinely
  *polynomial*, not just algebraic — clear at a LARGE enough exponent (#5606).** Algebraicity
  (k[X,D] coefficients) does NOT give weight-spanning (the `det⁻¹` counterexample), and
  `IsAlgebraicRepresentation` has no transport (`.restrict`/`.of_linearEquiv`) to
  `IsPolynomialRepresentation`. The clean route: get the `det^{r₀}`-twist algebraic (e.g. via the
  basis det-clearing mirroring `rightHull_isSemisimple`, `detTwist_clearing` in
  `RealizationCoreAnalytic.lean`), then `IsAlgebraicRepresentation.exists_detPow_twist_isPolynomial`
  (`DetClearing.lean`) gives an `s` with the *further* `det^s`-twist polynomial. Clear instead at
  `r := r₀ + s`: the `det^{r₀+s}`-twist is `fun g => det(g)^s • (det^{r₀}·ρ) g`, which equals
  `charTwistRep (detChar^{r₀+s}) ρ` (prove by `funext g; ext x; rw [LinearMap.smul_apply,
  charTwistRep_apply, charTwistRep_apply, smul_smul]; congr 1; rw [show det g = detChar g from rfl,
  MonoidHom.pow_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
  pow_add]; ring`), so `hfun ▸ hPoly₀ : IsPolynomialRepresentation …`, and weight-spanning then
  comes free from `polynomial_rep_iSup_glWeightSpace_eq_top` (`PolynomialWeightSaturation.lean`).
  The det-clearing `φ` (basis denominators) also works at `r₀+s ≥ r₀`, so factor the clearing into a
  parameterised lemma and call it twice (at `r₀` for algebraicity→`s`, at `r₀+s` for the output).

The canonical Fintype indexing set for "dominant weights `ν ∈ ℕ^N` of size `d`"
is `BoundedPartition N d` (`Proposition5_21_1.lean`: antitone `ν : Fin N → ℕ`
with `∑ ν = d`; has `Fintype` + `DecidableEq`). Use it to write a
multiplicity-one decomposition as a single `Finset.sum`
(`∑ ν : BoundedPartition N d, schurPoly N ν.parts`) — each `ν` once = mult one,
no ad-hoc partition bookkeeping.

#### `dim V_λ` for a *concrete* partition λ (Ch5 Example5.12.3, #5125)

`Module.finrank ℂ (SpechtModule n la) = n! / ∏ h(i,j)` via
`finrank_spechtModule_eq_card_syt_general` (`dim = |SYT|`,
`CharValueHookFormula.lean`) then `card_standardYoungTableau_eq` (`|SYT| = n!/∏h`,
`FRTHelpers.lean`). The only work left is the hook-length product for the shape —
but **`decide` cannot evaluate it directly**: `YoungDiagram.rowLen`/`colLen` use
`Nat.find` and `Nat.Partition.sortedParts` uses `Multiset.sort` (mergeSort),
both well-founded recursions that the kernel will not reduce. Two-step fix
(worked template in `Chapter5/Example5_12_3.lean`, reuse it verbatim):
1. Rewrite hooks into a `Nat.find`-free product: `colLen c = #{rows longer than
   c}` (`toYoungDiagram_colLen_eq`), giving `hookLengthProduct_eq_compute`.
2. Pin `sortedParts = [explicit list]` with `sortedParts_eq_of` (proof: `μ.parts
   = ↑L` by `rfl` + `L.Pairwise (·≥·)` by `decide`, closed by
   `List.mergeSort_eq_self`), then `hookLengthProduct_eq_of` leaves a product
   over `cellsOfRowLens L` that **is** kernel-reducible, so `by decide` finishes.
The single-row/single-column hook product is `∏_{k<n}(n−k) = n!`
(`prod_range_sub`, via `Finset.prod_range_reflect` +
`Finset.prod_range_add_one_eq_factorial`), giving the general trivial- and
sign-representation dimensions (`dim = 1`). The current Mathlib `Multiset.sort`
API is `Pairwise`-based: there is no `List.Sorted`/`eq_of_perm_of_sorted`; use
`Multiset.sort_cons`/`sort_singleton`/`coe_sort` + `List.mergeSort_eq_self`.

#### Multiplicative character of a finite cyclic subgroup (e.g. `ℂ_ε` on `Z₃ = A₃`, #5248)

To build a character `χ : ↥H →* ℂˣ` of a concrete cyclic subgroup `H ≤ G` sending a chosen
generator `g₀ : ↥H` to a chosen unit `u : ℂˣ`, use `monoidHomOfForallMemZpowers`
(`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`): `monoidHomOfForallMemZpowers (hg : ∀ x, x ∈
Subgroup.zpowers g₀) (hg' : orderOf u ∣ orderOf g₀) : ↥H →* ℂˣ`, with
`monoidHomOfForallMemZpowers_apply_gen` giving `χ g₀ = u`. Worked, sorry-free in
`Chapter5/Discussion5_11_examples.lean` (`epsHom`, the cube-root character `ε(gen) = exp(2πi/3)`).
**`decide` does NOT discharge the three obligations** — each needs a real proof:

- **`g₀ ∈ H`** (here `finRotate 3 ∈ alternatingGroup (Fin 3)`): unfold the subgroup and rewrite to
  the membership predicate first — `rw [Equiv.Perm.mem_alternatingGroup]; decide` (`decide` *does*
  evaluate `sign (finRotate 3) = 1`, but not the bare `∈ alternatingGroup`, which lacks a
  `Decidable` instance).
- **`orderOf g₀ = n`** (`decide` on `orderOf` times out / no instance): use `orderOf_eq_prime`
  (needs `haveI : Fact (Nat.Prime n)`) with `g₀ ^ n = 1` (by `Subtype.ext; decide` on the
  underlying perm) and `g₀ ≠ 1` (`fun h => absurd (congrArg Subtype.val h) (by decide)`).
- **`∀ x, x ∈ Subgroup.zpowers g₀`** (the `∃ k : ℤ` makes `decide` fail): prove `zpowers g₀ = ⊤`
  via `Subgroup.eq_top_of_card_eq` + `rw [Nat.card_zpowers, orderOf_lemma, <subgroup-def>,
  Nat.card_eq_fintype_card]; decide`, then `Subgroup.mem_top`.

For the unit: `zeta3 := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / 3)) (Complex.exp_ne_zero _)`;
`ζ³ = 1` by `Units.ext` then `← Complex.exp_nat_mul` + `Complex.exp_two_pi_mul_I` (push the `(3:ℕ)`
cast through with `push_cast; ring` inside a `show`); `orderOf ζ ∣ orderOf g₀` from
`orderOf_dvd_of_pow_eq_one`. Package `ℂ_ε := FDRep.of (charRep χ)`; simplicity is free from the
existing `charRep_simple`.

#### Building `MulAut (Multiplicative A)` from a coordinate formula (semidirect-product `φ`, #5920)

To apply `Etingof.Theorem5_27_1` you must exhibit the group as `A ⋊[φ] G` with `A` a `CommGroup`,
so `φ : G →* MulAut A`. For `A = Multiplicative (ZMod n)` (dihedral, inversion) or `A = Multiplicative
(ZMod p × ZMod p)` (Heisenberg, the shear `(b,c) ↦ (b, c+a·b)`), build each automorphism as a `MulAut
(Multiplicative …) where` giving `toFun/invFun` in `ofAdd (… toAdd x …)` coordinates. Gotchas that cost
several build cycles (`Chapter5/Exercise5_27_2_Heisenberg.lean`, sorry-free defs):
- **The lemma names `Multiplicative.toAdd_mul` / `Multiplicative.toAdd_ofAdd` do NOT exist.** Both facts
  hold **by `rfl`** (`Multiplicative` is a type synonym), so don't `simp [those]` — instead `apply
  Multiplicative.toAdd.injective` and work with the underlying `ZMod …` (Prod) goal directly.
- Inside the `MulAut … where` block, prove `left_inv`/`right_inv`/`map_mul'` by `apply
  Multiplicative.toAdd.injective; apply Prod.ext; · rfl · show <snd-component eqn>; ring`.
- For *standalone* `@[simp] lemma φ_zero : shear 0 = 1` and `φ_add : shear (a+a') = shear a * shear a'`
  (needed for `map_one'`/`map_mul'` of the `G →* MulAut A` hom), start `refine MulEquiv.ext fun x => ?_`
  then `rw [MulAut.one_apply]` (resp. `MulAut.mul_apply`) to reduce `(1) x`/`(f*g) x` — **without this rw
  the RHS is stuck and `apply Prod.ext` fails to unify** — then `apply Multiplicative.toAdd.injective`,
  `show <reduced Prod pair> = <reduced Prod pair>` (both sides fully spelled out; defeq closes the
  `show`), and finish `apply Prod.ext; · rfl · show …; ring`.
- The `G →* MulAut A` hom's `map_one'`/`map_mul'`: `toAdd (1 : Multiplicative _) = 0` and `toAdd (a*a')
  = toAdd a + toAdd a'` are `rfl`, so discharge by `show shear 0 = 1; exact shear_zero` / `show shear
  (toAdd a + toAdd a') = _; exact shear_add …` (a `show` to the defeq-reduced form, not a named rewrite).

The classification theorem itself is a statement-pass `sorry` with an **existential** shape (`∃ n (W :
Fin n → FDRep ℂ G), simple ∧ pairwise-noniso ∧ complete ∧ dimension-profile`) — mirror
`Exercise5_27_2_Affine.lean`; you do NOT need to construct the individual irreps to state the
classification. (Or, when Mathlib already has the group, e.g. `DihedralGroup N`, state it on that
directly and record the semidirect structure only in the docstring — `Exercise5_27_2_Dihedral.lean`.)

#### §5.11 `S₃` induced-rep decompositions — DONE (#5248, all four sorry-free)

All four `Ind_H^G (1-dim char) ≅ ⊞ irreps` are proved in `Discussion5_11_examples.lean` via
Frobenius reciprocity (`Etingof.Theorem5_10_1`), **not** the still-`sorry` `Theorem5_9_1`. The
route fits in one session and the pieces are reusable for any small-group induced-rep decomposition:
- `finrank_hom_symm` (`dim Hom(V,W)=dim Hom(W,V)` via the symmetric scalar product) — lets you flip
  `finrank (S ⟶ Ind_H ρ)` to `finrank (Ind_H ρ ⟶ S)` so the categorical Frobenius (Ind on the left)
  applies, then feed `Etingof.iso_of_forall_finrank_hom_eq` (needs `S ⟶ -`).
- `frobenius_finrank`: the FDRep↔Rep bridge `dim Hom_{S₃}(Ind_H ρ,S)=dim Hom_H(ρ,Res_H S)`. The
  feared plumbing was a non-issue — **all object identifications are `rfl`**:
  `(forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of (Representation.ind H.subtype ρ)) = Rep.ind
  H.subtype (Rep.of ρ) := rfl` (because `Definition5_8_1 = Representation.ind`, `Rep.ind = Rep.of ∘
  .ind`, and `forget₂_ρ`/carrier are defeq). Cross via `FDRep.forget₂HomLinearEquiv`, apply
  `Rep.indResHomEquiv`, return; `Res_H S := (Action.res (FGModuleCat ℂ) H.subtype).obj S` with
  `((Action.res _ f).obj S).ρ h = S.ρ (f h)` (`rfl`).
  - **Dot-notation trap on a restricted rep (`FDRep = Action`): write `FDRep.ρ`/`FDRep.character` explicitly (#6706).** `((Action.res …).obj σ).ρ` resolves to `Action.ρ` (a `G →* CategoryTheory.End …`, the *categorical* automorphism), NOT `FDRep.ρ` (`G →* (V →ₗ V)`), so `Representation.invariants (…).ρ` fails with "argument has type `↥K →* CategoryTheory.End …`" and `(…).character` fails with "environment does not contain `Action.character`". Fix: `Representation.invariants (FDRep.ρ ((Action.res …).obj σ))` and `FDRep.character ((Action.res …).obj σ) g`. The averaging bridge `⅟(card ↥K) • ∑_{g:↥K} σ.character (g:↥H) = finrank (invariants (FDRep.ρ (Res σ)))` is just `FDRep.average_char_eq_finrank_invariants` after rewriting the summand `FDRep.character (Res σ) g = σ.character (g:↥H)` (`rfl`). To read off `FDRep.ρ (Res σ) ⟨w,hwV⟩ = σ.ρ w` from a `mem_invariants` fact, `simpa` won't unify the two `.ρ` spellings — use `show (σ.ρ w) x = x; exact hfix`.
- completeness `S3_simple_iso` from `exists_simples_sum_finrank_sq_eq_card` + the `1²+1²+2²=6` count.
- `ind_finrank_eq_scalar` = multiplicity as `⅟|H| • ∑_{h:↥H} S.character ↑h * (charRep χ).character h⁻¹`
  (`FDRep.scalar_product_char_eq_finrank_equivariant`), then `sum_cyclic` (enumerate `↥H` via
  `finEquivZPowers`) reduces to a `Fin n` sum you evaluate at the conjugacy-class reps.
Finish each theorem with `iso_of_forall_finrank_hom_eq`, casing `S` over the catalogue:
LHS multiplicity from the scalar product, RHS from `FDRep.finrank_hom_simple_simple` + `finrank_hom_biprod`.

Four gotchas that each cost a build cycle (watch for the analogues in any finite-group character work):
1. **Concrete subgroups you need `Fintype`/`Invertible` instances on must be `abbrev`, not `def`.**
   `def Z2 : Subgroup S3 := …` makes `↥Z2` opaque, so `Fintype ↥Z2` / `Invertible (card:ℂ)` fail to
   synthesize at *statement* elaboration (the lemma won't even state). `abbrev` lets resolution see
   through. (Switching `def`→`abbrev` then breaks any `rw [Z2]` — drop them; the abbrev unfolds
   definitionally so `Nat.card_zpowers`/`mem_alternatingGroup` apply directly.)
2. **`decide` on `Fintype.card ↥(Subgroup.zpowers g)` gets STUCK** (the Fintype routes through a
   noncomputable `Classical.decPred`). Route the card through order instead:
   `rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, <orderOf g = n>]`. (`decide` *does* work for
   `Fintype.card ↥(alternatingGroup (Fin 3))` — only the `zpowers` Fintype is classical.)
3. **Under `open CategoryTheory`, bare `finrank_hom_simple_simple` resolves to the
   `CategoryTheory` version** (which takes `k` as the first *explicit* arg), giving a baffling
   `failed to synthesize Field ↑S.V`. Write `FDRep.finrank_hom_simple_simple S W` explicitly.
4. **`⅟c • x = ↑m` arithmetic**: don't `rw` the card inside `⅟` (the `Invertible` instance is keyed
   on the old term). Use `invOf_smul_eq_iff` (`⅟c • x = y ↔ x = c • y`) to clear the `⅟` first,
   then `rw [<card lemma>, smul_eq_mul]; norm_num` (or `linear_combination` for the cube-root case).
For `ℂ_ε`: `zeta3_primitive : IsPrimitiveRoot (zeta3:ℂ) 3` via `Complex.isPrimitiveRoot_exp 3`
(`rw [show (3:ℂ)=((3:ℕ):ℂ) by norm_num]; exact h` to reconcile `/3` vs `/↑3`), then
`IsPrimitiveRoot.geom_sum_eq_zero` gives `ζ²+ζ+1=0`; `ζ⁻¹=ζ²`, `(ζ²)⁻¹=ζ` via
`inv_eq_of_mul_eq_one_right` + `ζ³=1`. Don't reach for `charEq_iso` here: it needs the induced
character, exactly what the Frobenius route avoids.

### `_kQ` rep `obj` projection does not reduce in signatures (sporadic tube family)

The per-(field, orientation) reps `<X>Rep_kQ` (`FieldGeneric{Star,D5/6/7Tilde,ETilde6/7,T125,Tube}.lean`) are built tactically: `noncomputable def … := by letI := Q; exact { obj := fun v => Fin (<X>Dim m v) → F, … }`. The structure projection `(<X>Rep_kQ …).obj ⟨v, _⟩` does **not** reduce to `Fin (k·(m+1)) → F` under the transparency that `Membership`-instance synthesis uses. Consequences when stating lemmas over the rep family `W : ∀ v, Submodule F ((<X>Rep_kQ …).obj v)`:

- A **top-level signature** with a concrete-element membership — `∀ (x : Fin (k·(m+1)) → F), x ∈ W ⟨v, _⟩ → …` — fails to elaborate (`failed to synthesize Membership (Fin … → F) (Submodule F ((…).obj ⟨v, ?⟩))`). Equalities/`≤` between two `W ⟨v⟩` only typecheck when the two vertices share a dim (e.g. the four dim-`(m+1)` leaves of the D̃ family); for distinct-dim vertices (e.g. T(1,2,5)) they don't.
- `(…).obj ⟨v,_⟩ = (Fin (<X>Dim m ⟨v,_⟩) → F) := rfl` ✓ (projection reduces with `<X>Dim` symbolic), but `… = (Fin (k·(m+1)) → F) := rfl` ✗ (the `<X>Dim` match won't reduce in the same step).

**Workarounds.** (1) State reusable arm/flag helpers over **explicit `Fin (k·(m+1)) → F` carriers** plus per-edge hypotheses (as `t125_prefix_sub` / `t125_canonical_collapse` do) — these elaborate cleanly. (2) Do the `W ⟨v⟩` → explicit-carrier bridge **inside a proof body**, where `simp only [<X>Rep_kQ, <X>RepMap_kQ]` unfolds the rep and concrete memberships elaborate at default transparency (this is why the local `core`/`leaf*_sub` haves inside `starTubeRepGen_isIndecomposable` work). Do not try to expose a rep-level `…_leaf_equalities` theorem whose *conclusion* carries concrete memberships; assemble that content in the consuming indecomposability proof instead.

### Direct sums / decompositions of `QuiverRepresentation` (Ch6, #4781)

Two gotchas bite anyone building iterated direct sums or decomposition results
(`DecompositionExistence.lean` is the reference; `exists_decomposition` is the
existence-of-decomposition-into-indecomposables workhorse).

**Rewriting a `DirectSum.component ⟨w, arr⟩ z` Sigma index fails with "motive is not type
correct" (Ch7 #6085, the reflection-functor adjunction bijection).** The component's *value*
type is `M idx.fst`, a dependent position, so `rw [heq]` on the whole index `idx : Σ j, (j ⟶ i)`
(e.g. `sourceArrowReindexEquiv hi ⟨w,e⟩ = ⟨w, β⟩`) is rejected. Fix: rewrite only the *arrow*
second component, keeping `fst = w` fixed — extract `hsnd : revOut hi ⟨w,e⟩ = β` and
`rw [← hsnd]`, whose motive `fun arr => … = component ⟨w, arr⟩ z` has constant value type
`M w`. To turn a whole direct-sum equality into a per-index check over a reindexing bijection,
use `DirectSum.ext_component R (fun b => ?_)` then `obtain ⟨a, rfl⟩ := e.surjective b`
(reduces `component b` to `component (reindex a)`, where a `Finset.sum_eq_single`-based
component read-off lemma applies). Package the `κ.symm ∘ codRestrict` round-trip and the
per-arrow component identity as reusable `have`s before the `Equiv` assembly, and reduce the
`if hv : v = i then hv ▸ appAtI r else …` app field with `simp only [reduceDIte]` (at `i`)
/ `simp only [dif_neg hv, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]` (off `i`).

1. **`obj` carries only `AddCommMonoid` — `FiniteDimensional` is ill-typed.**
   `Etingof.QuiverRepresentation.obj` bundles `AddCommMonoid` + `Module`, not
   `AddCommGroup`. So a hypothesis `[∀ v, FiniteDimensional k (V.obj v)]` does
   **not** elaborate (`FiniteDimensional` needs `AddCommGroup`). Use
   `[∀ v, Module.Finite k (V.obj v)]` instead (works over `AddCommMonoid`;
   `Module.finrank` is fine too). Where you genuinely need group structure
   (complements, `IsCompl`, `prodEquivOfIsCompl`, `finrank` additivity), add it
   locally and *only there*:
   `letI : ∀ v, AddCommGroup (V.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)`
   (it extends the bundled `AddCommMonoid`, no diamond). Under that `letI`,
   `FiniteDimensional k (V.obj v)` becomes defeq-derivable from `Module.Finite`,
   so `Submodule.finrank_add_eq_of_isCompl`, `Submodule.finrank_eq_zero`, and the
   submodule-`Module.Finite` instance all resolve.

2. **`directSum` returns obj-universe `max u₁ u₂` — pin the fold base to `Type 0`.**
   `Etingof.QuiverRepresentation.directSum.{…}` has `ρ₁ : QR.{…,u₄,…}`,
   `ρ₂ : QR.{…,u₅,…}`, result `QR.{…,max u₅ u₄,…}`. A `foldr`-based `directSumList`
   with a *universe-polymorphic* zero base (`obj := fun _ => PUnit`) therefore
   leaks a **free universe** (the base's `PUnit` universe stays an independent
   param, and unification fails with `directSumList.{…,?u}` mismatches). Fix: make
   the zero rep `obj := fun _ => PUnit.{1}` (concretely `Type 0`) and state the
   decomposition theorem at obj-universe `0`
   (`QuiverRepresentation.{uk, 0, 0, uh} k (Fin n)`). Then `max u 0 = u` collapses
   cleanly and `directSumList` is monomorphic. Obj-universe `0` is exactly what the
   orbit-counting application needs (`V.obj v ≃ Fin (d v) → k`). Tie `V` and the
   existential summand list to the **same** explicit universes, or the witness
   `[V]`/`L₁ ++ L₂` fails with a `List.cons` universe mismatch.

   Defeq-but-not-syntactic `(subRep …).obj v` ↦ `↥(W v)`: `rw [subRep_obj]` in a
   `finrank` goal triggers a "motive is not type correct" (the `AddCommMonoid`
   instance depends on the rewritten term). Use `change`/`show` to the reduced
   form (defeq) or `simp only [subRep_obj]` instead of `rw`.

## Scaffolding Anti-Patterns

These patterns were discovered during Chapter 2 and 7-8 reviews. Avoid them in all scaffolding work.

### Never sorry a Type

```lean
-- BAD: sorry'd type breaks all downstream usage
noncomputable def Etingof.PathAlgebra ... : Type* := sorry

-- GOOD: define carrier concretely, sorry the algebraic instances
def Etingof.PathAlgebra ... := FreeModule k (Quiver.Path ...)
instance : Algebra k (Etingof.PathAlgebra ...) := sorry
```

A sorry producing `Type*` gives `sorryAx Type*` — no instances can be built on it. Define the carrier type concretely and sorry the structure instances.

### Don't alias only the carrier type

```lean
-- BAD: misses the Lie module structure (the actual content of the definition)
abbrev Etingof.LieTensorProduct ... := TensorProduct k V W

-- GOOD: alias and import the relevant instance
import Mathlib.Algebra.Lie.TensorProduct
abbrev Etingof.LieTensorProduct ... := TensorProduct k V W
-- The Lie module instance is provided by the import
```

When a definition is about *structure on a type*, the alias must capture the structure, not just the carrier.

### Don't scaffold definitions as theorems

```lean
-- BAD: book definition scaffolded as theorem
theorem Etingof.Definition_8_2_3 : (sorry : Prop) := sorry

-- GOOD: use def/abbrev for definitions
noncomputable def Etingof.TorFunctor ... := sorry
```

Use `def`/`abbrev`/`noncomputable def` for definitions, `theorem`/`lemma` for propositions.

### Don't write tautological examples

```lean
-- BAD: proves nothing
example (A : Type*) [Ring A] : (1 : A) = 1 := rfl

-- GOOD: demonstrate actual properties
example (A : Type*) [Ring A] (a : A) : 1 * a = a := one_mul a
```

### Verify blob content before scaffolding

If a blob file is empty, flag it rather than scaffolding from the title alone. Title-only scaffolding produces low-quality formalizations.

**Blob filenames can be off-by-one / mislabeled — confirm the actual statement, don't trust the filename.** Blob extraction sometimes shifts numbered items across files, especially where a Problem's text is split by a page break or interleaved with the preceding discussion. Before formalizing item `X.Y.Z`, grep the book prose for the literal `X.Y.Z` label (it appears in the text, e.g. `**Problem X.Y.Z.**`) and read the statement there, rather than assuming `blobs/<Chapter>/<Item X.Y.Z>.md` holds it. (#5727: `Problem3.8.3.md` actually contained Problem 3.8.4(i)'s text; the real Problem 3.8.3 — "prove Lemma 3.8.2 without algebraic closure" — lived inside `Discussion_proof_of_Theorem3.8.1.md`.)

### Use minimal imports

Prefer the most specific Mathlib module. Don't import `Mathlib.LinearAlgebra.DirectSum.Finite` when `Mathlib.Algebra.Module.Prod` suffices.

### Verify "import-cleanliness" with a real transitive trace, never a grep or an agent claim

When a task requires a file to avoid some module (e.g. the Chapter 5 `DetInvElim`-clean work for #5072/#5075/#5078: a file must NOT transitively import `DetInvElim`, else it creates a build cycle), do not trust a direct-import grep or a subagent's pollution claim — both miss/invent transitive edges. An Explore agent confidently mis-reported `FormalCharacterTorusTrace` as importing `DetInvElim` when it does not; a real trace caught it. Compute the transitive closure yourself before relying on it:

```bash
python3 - <<'PY'
import os, re
root="EtingofRepresentationTheory"; imports={}
for dp,_,fs in os.walk(root):
    for f in fs:
        if f.endswith(".lean"):
            mod="EtingofRepresentationTheory"+dp[len(root):].replace("/",".")+"."+f[:-5]
            imports[mod.replace("..",".")]=[m.group(1) for line in open(os.path.join(dp,f))
                if (m:=re.match(r'^import (EtingofRepresentationTheory\.[\w.]+)',line))]
def trans(s,seen=None):
    seen=seen or set()
    for d in imports.get(s,[]):
        if d not in seen: seen.add(d); trans(d,seen)
    return seen
target="EtingofRepresentationTheory.Chapter5.<File>"
print([x for x in trans(target) if "DetInvElim" in x] or "CLEAN")
PY
```

The lemma you need may live in a *polluted* file even though its own proof is clean (this is common — additivity/weight-space helpers stranded in files that import `DetInvElim` for unrelated reasons). The fix is to **relocate the clean statement+proof into a new file importing only clean ancestors**, leaving the polluted original in place; verify the new file with the trace above.

**Before accepting an import-cycle issue's prescribed heavy refactor, measure exactly which symbols cross the polluted edge — the real fix is often one or two relocations, not the re-routing the issue fears.** An issue framed as "this needs the whole X machinery re-routed through clean files, too big for one session, decompose into (a)+(b)" can collapse once you check *what the consumer actually uses from the polluted import*. For each polluted `import P` in file `F`: list `P`'s declarations (`grep -oE '^(noncomputable def|def|theorem|lemma|abbrev) \w+' P.lean`), then `grep -nowFf` that list against `F.lean` to see the handful of names `F` truly consumes. If those names are clean (their own proofs reach no polluted module — check with the per-symbol trace, not the file's), extract just them into a leaf file and rewire `F` to import it; `P` re-imports the leaf so its other consumers are unaffected (same namespace ⇒ no qualified-name breakage). Then **simulate the whole rewired DAG in Python before editing** (apply the import swaps to the `imports` dict, recompute closures, run a colour-DFS cycle check, and also simulate the eventual downstream assembly's imports) — confirm 0 cycles and `DetInvElim`-free closures up front, so the build is a formality. (#5108: the issue prescribed re-routing the SchurWeyl character machinery [its part (b)]; in fact `CauchyCharDiff` used `Proposition5_22_2` only for `schurPoly_shift` and `CauchyDetQuotientGrading` used `PolynomialGLDecomposition` only for `asModuleHomOfIntertwiner` — two clean-symbol extractions [`SchurPolyShift.lean`, `RepresentationAsModuleHom.lean`] cleared all four ingredient files in one session.)

### Match Mathlib's generality for type class assumptions

If Mathlib uses `[Semiring R]`, don't restrict to `[CommRing R]`. Use the same or a compatible assumption. Within a chapter, be consistent — don't use `[CommRing R]` in one definition and `[Ring R]` in the adjacent one.

## Scaffolding Review Checklist

When reviewing scaffolded files, check each item against this list:

1. **Compilation**: `lake build <module>` passes with only expected sorry warnings
2. **Lean↔Blob↔items.json alignment**: every items.json entry has a .lean file and a blob file, no orphans
3. **Mathlib alias correctness**: `#check` the referenced declaration, verify it exists and is non-deprecated
4. **Type class consistency**: assumptions match Mathlib's (or are intentionally more specific with documented rationale)
5. **Anti-pattern scan**: no sorry'd types, no carrier-only aliases, no definitions-as-theorems, no tautological examples
6. **Import minimality**: imports are the most specific Mathlib module needed
7. **Doc-string quality**: matches the blob text, identifies Mathlib correspondence
8. **Gap definitions**: carrier type is concrete (not sorry'd), instances are sorry'd

Write findings to `reviews/<chapter>-scaffolding-review.md` with per-file scores and systematic pattern analysis.

## Quality Checks

Before submitting a PR for a formalized item:

1. **`lake env lean <file>` passes** — no errors
2. **No `sorry` remaining** in the target item (sorry in dependencies is OK)
3. **No `admit`** anywhere in committed code
4. **Docstring present** with book's natural language statement
5. **Imports are minimal** — only import what's actually used
6. **No duplicate declarations** — search for the declaration name across all files before adding. Duplicate names (even private ones) cause CI failures when files are compiled together. PRs #1655, #1657 were CI fixes for this exact issue.
7. **Heartbeat budget** — if your proof uses heavy `decide`, `omega`, or trace computations, test with the CI heartbeat limit. Use `set_option maxHeartbeats N in` to increase locally if needed. Guidelines:
   - **≤ 400000**: Normal, no annotation needed
   - **400000–800000**: Acceptable for trace/character computations over finite groups. Add a comment explaining why.
   - **800000–1600000**: Borderline. Acceptable only for GL₂(𝔽_q) trace computations or similar unavoidable large finite sums. Must have a comment. Consider whether `simp` can be replaced with targeted `rw` to reduce heartbeats.
   - **> 1600000**: Refactor the proof. Extract helper lemmas, precompute intermediate results, or split the finite check into smaller pieces. **NEVER reach for `native_decide`** — it is FORBIDDEN in this project (an unverified trust hole outside the kernel; see "FORBIDDEN: `native_decide`" below). If a finite check is too slow for honest `decide`, that is a signal to find a real proof, not a bigger hammer.
   - **Placement:** `set_option ... in` lines must come *before* the `/-- ... -/` docstring (the docstring must sit immediately above `theorem`/`def`). Putting the docstring first gives `unexpected token 'set_option'; expected 'lemma'`. **The same constraint applies to `omit [Inst] in`** (used to silence the `unusedSectionVars` linter when a section instance like `[Fintype ι]`/`[∀ i, Module.Finite ...]` is genuinely unused by a lemma): it must precede the docstring, else `unexpected token 'omit'; expected 'lemma'`. Note the linter reports unused instances *one at a time* — after omitting the flagged ones it may flag a further instance (e.g. `Module.Finite` once `Fintype`/`DecidableEq` are omitted), so expect to extend the `omit` list across a build cycle or two. **Section-wide vs per-lemma:** if an earlier `def` in the section *captured* the instance (Lean auto-includes an instance-implicit section var whenever its type mentions an already-used var, even if the def's body never touches it), then a per-lemma `omit [Inst] in` on a *downstream* lemma that calls that def fails with `failed to synthesize instance … Inst` — the def now demands it. Fix by putting a bare `omit [Inst]` command (no `in`, no docstring) *right after the section's `variable` line, before the defs*, so nothing in the section captures `Inst` in the first place; keep per-lemma `omit … in` only for instances (like `Module.Finite`) that some later lemma genuinely needs but others don't.
   - **`whnf` timeout despite a high budget** usually means Lean is eagerly reducing through a *non-reducible* coercion (e.g. an `FDRep`/`FGModuleCat` carrier identified with a hom-space, re-typed mid-proof via `let e' := e`). Fix it by paying that coercion *once* in a helper theorem whose output is already stated in the target type, then consume the result opaquely — do not re-coerce inside the heavy proof.
   - **`whnf` timeout through a `Quotient.liftOn'` definition** (e.g. `MulAction.orbitRel.Quotient.orbit`, relevant to the Ch6 orbit-counting chain #4777). Proving a membership like `a ∈ (Quotient.mk'' a).orbit` via `orbitRel.Quotient.mem_orbit.mpr rfl` forces Lean to whnf-unfold the `liftOn'` and blows the heartbeat budget for a one-line goal. Fix: don't lean on defeq — rewrite with the `_mk` simp lemma first (`rw [orbitRel.Quotient.orbit_mk]`, turning the quotient orbit into `MulAction.orbit G a`), then close with the plain-orbit API (`mem_orbit_self`). Also pin the quotient index explicitly (`Set.mem_biUnion (Set.mem_univ (Quotient.mk'' a)) …`) rather than letting unification infer it through the `liftOn'`. With both, the proof drops back under the default 200000 budget.
   - **Pushing an `AlgEquiv`/`RingEquiv` through `Polynomial.eval₂`/`aeval`** (e.g. the scaling-action transcendence argument in `Problem6_1_5_StrictDimBound`, #4828). To rewrite `(e : K ≃ₐ[k] K) (eval₂ f x p)` with `Polynomial.hom_eval₂` (which is stated for a bare `RingHom`), first bridge the coercion: `rw [show (e) (eval₂ f x p) = e.toRingHom (eval₂ f x p) from rfl]`, then `rw [Polynomial.hom_eval₂]`. The `⇑e` vs `⇑e.toRingHom` coercions are defeq, so `show … from rfl` matches — but an ascribed `(rfl : … = …)` does **not** match under `rw` (it fails to find the pattern). Express `aeval` as `eval₂` first via `Polynomial.aeval_def`. CI runs only `lake build` (no separate linter), so the `show`-tactic style warning on the `from rfl` term is harmless.

## Issue Sizing for Formalization

Based on Phase 2 experience with issue sizing:

- **Definitions:** 1-3 per issue (fast, low risk)
- **Easy theorems** (direct application of Mathlib): 2-5 per issue
- **Medium theorems** (multi-step proofs): 1-2 per issue
- **Hard theorems**: 1 per issue
- **Never mix difficulty levels** in one issue — a hard theorem blocks the easy ones

### Verify cited "model" files actually close the analogous case

When an issue says "mirror the proven branch in sibling file X" or "models: Y, Z",
**grep the cited file for `sorry` at the analogous declaration before assuming the
branch is tractable**. In the D̃-family tube work (#4692) the issue cited D̃₆
(`FieldGenericD6Tilde.lean`) and T(2,2,2) as models for the mixed-direction
(combo C/C′) and central-reversed leaf-equality branches — but D̃₆ carries the
**same five branches still `sorry`**, and no tube member had closed a mixed
combo-C branch anywhere. A branch that is unsolved across *every* sibling is
frontier-difficulty regardless of how the issue frames it. In that case prefer
landing reusable infrastructure plus a documented reduction (e.g. combo C′
reduces exactly to leaf `Λ`-invariance, the indecomposability crux) over a
heroic full-closure attempt, and partial-PR. Confirm the tractability premise
early — it sets scope and avoids rediscovering the obstruction from scratch.

### Before creating a NEW named file, re-fetch main — concurrent sessions land it too

Skill #4853 ("verify cited 'already-landed' deps exist") has a twin failure mode:
the artifact you are about to **create** may already exist on `main`, landed by a
**concurrent** session while you worked. If your branch base is several commits
behind, `git fetch origin main` and check before you write `Chapter5/Foo.lean` —
especially for a planned/obvious filename the whole pod is converging on. In
#4695's kernel-lemma (K) assembly, a worker built `Chapter5/KernelLemmaK.lean`
from scratch, then on rebase found `main` already had a complete sorry-free
`KernelLemmaK.lean` from a sibling session; the entire branch (plus a follow-up
issue resting on a gap the landed version sidestepped) was redundant and got
closed. Cheap guard: `git fetch origin main && git show origin/main:<intended
path>` (or `git log origin/main --oneline -15` for the area) right before the
first `Write` of a new file. If it exists, build *on* it, not beside it. Bonus:
the landed version often reveals a cleaner formulation — there, stating (K) over
explicit **weight-vector generators** (each in a single `glWeightSpaceℤ`) made the
descent need no torus-semisimplicity of `O`, which the abstract-submodule framing
had wrongly demanded.

### "Residual sorry" issue whose file isn't on main yet — prove the lemma in its home, don't skip

A `... residual` issue often quotes a sorry'd theorem "in `Chapter5/FooAssembly.lean`"
and gives a `lake build ...FooAssembly` verification — but that file ships with a
**sibling PR still in progress** (claimed, no PR), so it does not exist on `main`.
Do **not** `coordination skip` as "stale": the *deliverable* is the lemma's proof, and
the lemma is almost always a standalone, reusable fact. Prove it in its natural
building-block home (the file where its subject and ingredients live — e.g.
`schurPoly_coeff_self_ne_zero` belongs in `Proposition5_21_1.lean` beside `schurPoly`,
`schurPoly_mul_vandermonde`, `alternant_coeff_kronecker`), with the **exact signature**
the issue quotes. The eventual assembly imports that home transitively
(`KernelLemmaKPrime` → `Theorem5_22_1` → `Proposition5_21_1`), so when the sibling PR
lands it deletes its sorry'd copy and calls your lemma. Note this hand-off in the PR
body and progress file. (#4949: proved sorry-free in `Proposition5_21_1.lean` while the
consuming `KernelLemmaKPrimeAssembly.lean` from #4923 was unlanded.) Watch for name
collision: use the issue's exact theorem name so the sibling references rather than
re-declares it.

### Adding a hypothesis the consumer must supply: check the import direction first

When an issue says "add hypothesis `h` to lemma `L`, the consumer supplies it",
verify *before* editing `L`'s signature that the term the consumer will pass is
reachable **without an import cycle**. A *property* lemma (`X_isAlgebraic`,
`X_isSimple`, `X_isPolynomial`, …) is usually defined **downstream** of the object
`X` it describes — but the consumer of `L` often lives in the same upstream file
where `X` itself is defined, so it cannot import the downstream property. The plan
will read as if `h := X_property` is a one-liner; it is an import cycle. Fix by
extracting the *general* infrastructure the property is built from into an upstream
file and proving the consumer's instance **inline**; leave only the concrete
packaging downstream. (#4882: `iso_of_formalCharacter_eq_schurPoly` gained `halg`,
but `detTwistedSchurModuleRep_isAlgebraic` lives in `DetTwistAlgebraic`, which
imports `Proposition5_22_2` — where both the consumer *and* `detTwistedSchurModuleRep`
live — a cycle. Resolved by extracting `GLRepAlgebraic.lean` with the reusable
`glTensorRep_isAlgebraic` / `.restrict` / `.detTwist` and building `halg` inline.)
A second, related trap in the same issue: a plan step asserted "the simple summand
`≅ L_λ` at the asModule level" as if free, but the existing classification exposes
only *characters*, not the iso — that step needed a strictly stronger (deferred)
lemma. Treat every "obviously follows" step in a plan as a claim to check against
an actual existing declaration before committing to a sorry-free target.

**Generalizing a ℂ lemma "in place" when its general-`k` support is downstream:
put the general version in a NEW downstream file, don't edit the ℂ file.** A plan
that says "lift `foo` (ℂ) to general `k` in `FooFile.lean`" is mis-scoped whenever
`foo`'s proof needs general-`k` infrastructure (`SpechtModuleK_isSimpleModule_general`,
`Theorem5_12_2_distinct_general`, `youngSymmetrizerK_annihilates_specht`, …) that
lives in files which *import* `FooFile.lean` — editing in place is an import cycle.
When the generalized lemma is **not itself consumed upstream** (only by a still-later
assembly), the cleanest fix is a new *downstream* file importing both `FooFile.lean`
and the general-`k` machinery; leave the ℂ original untouched. The "already generic"
helpers in `FooFile.lean` (e.g. `trace_youngSymEndomorphism_restrict_eq_sum`,
`youngSymEndomorphism_restrict_sq_scalar`) still apply by proof-irrelevance even when
your `.restrict` supplies a different (defeq) membership proof, so you can re-state the
theorems verbatim. Working over `k` throughout often *removes* ℂ-specific helpers (the
ℚ→ℂ base-change `youngSym_sq_ℂ'` / `youngSymmetrizerK_complex_eq` vanish — the scalar
comes straight from `YoungSymmetrizerK_sq_scalar k`). To stay independent of a sibling
"general-`k` character" PR you can't import yet, define a local Specht character
(`spechtBlockCharacterK := trace of left-mult-by-`of σ` on `SpechtModuleK`) that is
*definitionally equal* to the bridge's `spechtModuleCharacterK`, so the eventual
consumer reconciles `h_label` by `rfl`. (#5004: `SchurWeylSpecialBlockGeneral.lean`,
the two `youngSym_action_*_general` lemmas — built first try this way.) **Check the
import DAG of the support lemmas before writing any code; don't discover the cycle
after editing the ℂ file.**

**Multi-block tubes: don't fix the `_leaf_equalities` *statement shape* ahead of
the center-collapse design.** For the ≥3-arm / >2-block-center tubes (Ẽ₆ #4638,
Ẽ₇ #4746, and the entangled D̃₅ #4743) the eigenvalue site is a **separate
vertex** (not a leaf) mapping to *all* center blocks, while the deep flag leaves
reach only the edge blocks (Ẽ₇: leaf-4→block 0, leaf-7→block 3; interior blocks
1,2 come only from the flag *intermediate* vertices). So N-invariance on the
common `F^{m+1}` cannot be read off one leaf — it must be derived **jointly** with
the flag collapse, and a center-core decomposition needs the intermediate
vertices' W-spans. Stating `…_leaf_equalities` with a guessed conclusion first
risks an *un-derivable* statement (the d5tilde #4743 outcome). Build the concrete
center-core primitive first, fix the conclusion shape from it, then prove
leaf-equalities and `_isIndecomposable` jointly. The mechanical eigenvalue
readout (e.g. `etilde7_arm1Tube_blockProj_F`: the four block projections of the
arm-1 tube = `(p+q, p+Λq, p+Λ²q, p+Λ³q)`) is the reusable piece to land first.

**Star `_leaf_equalities`: the non-canonical *orientation* branches fold too —
they are not the mechanical d5/d6tilde reversed-leaf pattern.** For a *star*
(Ẽ₆ #4701, Ẽ₇ #4769) the conclusion `W₁⟨leafᵢ⟩` all-equal couples every arm
through the single shared center, whose composite planes pairwise overlap.
Reversing an arm edge only swaps an embed criterion for a projection criterion;
it does **not** decouple the arms, so every orientation branch hits the *same*
overlapping-plane center-collapse wall as the canonical branch and folds into
`…Rep_kQ_isIndecomposable`. The d5/d6tilde reversed-leaf branches close only
because those are *chains* with one central γ-tube (combo-D reads reversed leaves
off one shared block) — no analog exists for the star. So an issue framed as
"close the non-canonical branches by mirroring d6tilde" is mis-scoped: grep the
canonical branch first; if its center collapse is already re-scoped to the
indecomposability fold (e.g. #4750/#4765 left `hcenter` as a documented `sorry`),
the reversed branches inherit it. Re-scope via a doc PR (`--partial`) rather than
attempting closure.

## Proven Proof Strategies

Patterns that have succeeded in this project, derived from 110+ merged proof PRs (through wave 20).

### Mathlib Alias Pattern (Chapter 2)

When a book definition matches a Mathlib concept exactly, use a simple alias:

```lean
/-- Definition 2.1.1: An associative algebra over k. -/
abbrev Etingof.Algebra (k : Type*) [CommRing k] (A : Type*) := Algebra k A
```

This pattern covered 19/25 Chapter 2 definitions. Check `.refs.md` — if coverage is "exact match", alias first, prove later. Don't build custom definitions when Mathlib already has the concept.

### Conjugate / restricted-scalars module synonyms (Ch4 #5182)

To build a "twisted scalar action" vector space — e.g. the **conjugate**
representation `V̄` (same `V`, same `G`-action, scalar `z • v = z̄ • v`) — use a
**non-reducible** type synonym so instances don't leak from the original:

```lean
def Conjugate (V : Type u) : Type u := V                       -- NOT abbrev/@[reducible]
instance : AddCommGroup (Conjugate V) := inferInstanceAs (AddCommGroup V)
noncomputable instance : Module ℂ (Conjugate V) := Module.compHom V (starRingEnd ℂ)
```

`Module.compHom M f` (`f : S →+* R`, needs `[Module R M]`) gives `Module S M` with
`s • m = f s • m`. Two gotchas that cost build cycles:

1. **The `smul_def` reduction lemma is `rfl` — but only with `show V from v`, NOT
   `(v : V)`.** `lemma smul_def (z) (v : Conjugate V) : z • v = (starRingEnd ℂ) z •
   (show V from v) := rfl` works. Writing `(v : V)` instead makes the RHS `•`
   re-resolve to the *conjugate* instance (`Conjugate V` is defeq `V`, so the
   ascription doesn't pin the underlying-`V` action), which loops `simp [smul_def]`
   to "maximum recursion depth" and leaves `smul_add _ _ _` unable to synthesize
   `DistribSMul ℂ (Conjugate V)`. `show V from v` (`have this := v; this`) forces the
   underlying-`V` action. (Do NOT hand-roll the `Module` axioms via `SMul` +
   manual fields — `compHom` already discharges them; you only need `smul_def`.)
2. **A `ℂ`-linear map lifts unchanged to the conjugate space.** `ρ g : V →ₗ[ℂ] V`
   is automatically `ℂ`-linear `Conjugate V →ₗ[ℂ] Conjugate V`; prove its
   `map_smul'` by `simp only [RingHom.id_apply, Conjugate.smul_def, map_smul]`.
   Likewise a conjugate-**linear** equiv `V ≃ₛₗ[starRingEnd ℂ] W` becomes a genuine
   `ℂ`-linear equiv `Conjugate V ≃ₗ[ℂ] W`: build the `LinearEquiv` reusing the
   semilinear one's `toFun/invFun/left_inv/right_inv`, and discharge `map_smul'` via
   `rw [Conjugate.smul_def, map_smulₛₗ]; simp` (the `starRingEnd (starRingEnd r) = r`
   collapse). This is how `V̄ ≅ V*` reuses Theorem 4.6.2's nondegenerate
   `innerEquivDual` (de-privatize it rather than duplicating the surjectivity proof).

### Building a custom structure on a `Prod`/`Fin → k` type synonym: `Prod.fst_add` won't fire — add `rfl` projection lemmas (Ch2 #5362)

When constructing a concrete Lie algebra / representation on a non-reducible synonym
`def Heisenberg k := k × k × k` (with `AddCommGroup`/`Module` via `inferInstanceAs`) and adding
your own `Bracket`/`LieRing`, the proofs of the algebra axioms (`add_lie`, `lie_smul`, …) reduce
to component identities — but **the generic `Prod.fst_add`/`Prod.snd_add`/`Prod.smul_fst` simp
lemmas do NOT match**, because the synonym's `+`/`•` resolve through *its own* (defeq but not
syntactic) instance head, not `Prod.instAdd`/`Prod.instSMul`. Symptom: after `simp only [bracket_def,
Prod.fst_add, …]` the goal still shows an un-reduced `((0,0,A) + (0,0,B)).1` (or `(x+y).2.1`), and
the following `ring` fails treating it as an opaque atom. Fix: state the projections as your own
`@[simp]`-`rfl` lemmas over the synonym and use *those* —
```lean
@[simp] theorem add_fst (a b : Heisenberg k) : (a + b).1 = a.1 + b.1 := rfl   -- + snd_fst/snd_snd
@[simp] theorem zero_fst : (0 : Heisenberg k).1 = 0 := rfl                     -- + the others
@[simp] theorem smul_fst (t : k) (a : Heisenberg k) : (t • a).1 = t • a.1 := rfl
```
then `apply <your @[ext] lemma> <;> simp only [bracket_def, add_fst, …, smul_eq_mul] <;> ring`. Two
companions: (i) a non-reducible `def` (not `abbrev`) keeps the `Bracket`/`LieRing` instances from
leaking onto bare `k × k × k` project-wide — worth the extra `rfl` lemmas. (ii) `0 : synonym` is
*not* rewritten to a constructor triple by `simp`, so a goal `(0,0,0) = 0` needs your `@[ext]`
lemma (which splits to the `zero_fst` projections), not bare `simp`. For the genuine content
(e.g. the U(ℋ) Heisenberg relations `YX−XY=C`, …), map the Lie brackets into the enveloping algebra
via `LieHom.map_lie` + `LieRing.of_associative_ring_bracket` (the associative bracket `⁅a,b⁆=a*b−b*a`);
these relations are specific to the presentation and so genuinely non-vacuous. A noncommutative
quotient like the Weyl algebra `U(ℋ)/(c−1)` needs `RingCon` (`TwoSidedIdeal.span {…}.ringCon`,
`RingCon.mk'`, `RingCon.eq`, `TwoSidedIdeal.rel_iff`/`subset_span`), **not** `Ideal.Quotient`
(commutative-only). Worked, axiom-clean in `Chapter2/Example2_9_13.lean`.

### Type Class Instance Examples

For "example" items that demonstrate a type satisfies a definition, use `inferInstance`:

```lean
/-- Example 2.2.1: M_n(k) is an algebra. -/
instance : Algebra k (Matrix (Fin n) (Fin n) k) := inferInstance
```

This compiles cleanly when Mathlib already provides the instance. Check with `#check` first.

### Module-theory instance gotchas (semisimple / submodule work)

Two traps recur when using Mathlib's `IsSemisimpleModule` / `IsSimpleModule` API:

- **`List.TFAE.out` chokes on named type args.** Writing
  `(IsSemisimpleModule.finite_tfae (R := R) (M := X)).out 0 1` fails with
  "type class instance expected". Instead let the *goal type* drive inference
  exactly as Mathlib does internally:
  `haveI : IsNoetherian R X := (IsSemisimpleModule.finite_tfae.out 0 1).mp ‹_›`
  (TFAE order is `[Module.Finite, IsNoetherian, IsArtinian, IsFiniteLength, …]`).
  The `‹_›` finds the source instance; the `M` is unified from the goal.

- **AddCommGroup vs AddCommMonoid diamond on `↥(submodule)`.** Transferring
  simplicity along an equiv with `IsSimpleModule.congr e` can fail with an
  AddCommMonoid mismatch (`p.addCommGroup.toAddCommMonoid` vs `p.addCommMonoid`)
  when one side is a submodule type. Use `(LinearEquiv.isSimpleModule_iff e).mp`
  instead — it sidesteps the re-synthesis that triggers the diamond.

- **`sub_mem` fails on `QuiverRepresentation` submodules.** The `obj v` carriers
  of `Etingof.QuiverRepresentation` (Chapter 6 indecomposability proofs) are
  wired with `instAddCommMonoid` only, so `Submodule.sub_mem` on a `W v` errors
  with an opaque application-type-mismatch (the `p` metavar never unifies). Mirror
  the established `core` pattern in `FieldGenericStar.lean`: build subtractions as
  `(W v).add_mem h ((W v).smul_mem (-1 : F) h')` and discharge the algebraic
  identity pointwise (`ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring`).
  Relatedly, when introducing a center vector for `eq_bot_iff`, annotate its type
  (`intro (w : Fin (2*(m+1)) → F) hw`) — an under-determined `w` cascades into
  spurious "No goals"/type-mismatch errors downstream. Keep `⟨i, by omega⟩` Fin
  literals (not `(i : Fin 5)`) so the `mapLinear`/`starRepMap_kQ` match reduces
  definitionally for `change`/defeq steps.

- **`Module.End` predicate dot-notation resolves to the nonexistent `LinearMap.*` (Ch5 §5.22 torus semisimplicity, #7210).** A value `glTensorRep … g` / `M.ρ g` has type `Module.End k V`, which elaborates as `LinearMap`, so `(M.ρ g).IsSemisimple` / `.invtSubmodule` / `.IsFinitelySemisimple` fail with "environment does not contain `LinearMap.IsSemisimple`". Write the predicate head explicitly: `Module.End.IsSemisimple (M.ρ g)`, `Module.End.invtSubmodule (…)`. (Dot-notation *does* work on `Module.End`-valued fields like `.maxGenEigenspace`, and on terms whose type head is already `Module.End.IsSemisimple`/`IsFinitelySemisimple` — e.g. `hss.restrict`, `hss.isFinitelySemisimple`, `hfss.maxGenEigenspace_eq_eigenspace`.) To prove a torus operator semisimple: it is diagonal in `tensorStdBasis`, so `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` with `p = ∏ s ∈ S, (X − C s)` (`S = (range (n+1)).image (u^·)`; squarefree via `separable_prod_X_sub_C_iff'` + `Separable.squarefree`; `aeval p = 0` on the basis via `Module.End.aeval_apply_of_mem_apply_eq_smul`).

- **Coercing an `FDRep` carrier element to the underlying module, and transferring `IsSemisimple.restrict` onto `(FDRep.of ρ).ρ` (Ch5 §5.22, #7210).** `(SchurModule k N lam).V` is `FGModuleCat.of k ↥(SchurModuleSubmodule …)`, so `(v : TensorPower …)` on a carrier element does **not** fire (type is `↑(…).V`, not `↥(submodule)`). Route through the subtype: `set ι := Submodule.subtype (SchurModuleSubmodule …)` — its domain is defeq to the FDRep carrier, so `ι v : TensorPower` type-checks. The intertwining `ι (M.ρ g w) = glTensorRep … g (ι w)` closes by `simp only [SchurModule, FDRep.of_ρ']; rfl` (the `restrict`-coe identity is definitional). To transfer semisimplicity of the tensor-power operator to the restriction on the FDRep, `exact ((glTensorRep_…_isSemisimple …).restrict hinvt)` works by defeq **through** `FDRep.of_ρ'`; `simpa only [SchurModule, FDRep.of_ρ'] using hss` does **not** — it rewrites `M.ρ`→`schurModuleRep` but then leaves an `FGModuleCat.of`-vs-native-submodule module-instance mismatch it cannot close.

- **Upgrading a `k`-linear bijection to an `A`-linear equiv: prove `map_smul`
  on the composite, do NOT transport the `A`-module (Ch5, #4926 biduality).**
  When the target is `↥S ≃ₗ[A] ↥T` but the natural maps factor through a
  hom-of-hom space `D := (↥S →ₗ[A] E) →ₗ[C] E` whose only canonical action is by
  `↥(centralizer C)` (= `A` by double-centralizer), resist putting an
  `A`-module on `D` via `Module.compHom`/scalar transport — the `map_smul`
  obligations then force you to unfold `compHom` everywhere and the elaboration
  is brutal. Instead: build *all* intermediate equivs `k`-linearly (the
  curried-evaluation `↥S ≃ₗ[k] D` via `LinearEquiv.ofInjectiveOfFinrankEq`, the
  precomposition via the already-`k`-linear `homCongrLeftOverSubring`), thread
  them to a `Φ : ↥S ≃ₗ[k] ↥T`, then package the *final* `↥S ≃ₗ[A] ↥T` with the
  explicit constructor `{ toFun := Φ, map_add' := Φ.map_add, invFun := Φ.symm,
  left_inv := Φ.left_inv, right_inv := Φ.right_inv, map_smul' := fun a v => ... }`
  and prove the lone `A`-`map_smul'` by hand (`apply (last equiv).injective; ext;
  rewrite the definitional apply-formulas`). The double-hom space never needs an
  `A`-module structure at all. Bonus: isolate the genuine content as a *pure
  `k`-finrank* lemma (`finrank k ↥S = finrank k D`) whose statement mentions no
  exotic module — clean to state and to attack separately.
- **Transporting an existential across a subalgebra equality `h : centralizer A
  = B`: `rw [← h]` the whole goal, do NOT `h ▸` each binder (Ch5, #5383).** When
  the target is `∃ … (Module B Lᵢ) … (IsSimpleModule B Lᵢ) … (Lᵢ ≃ₗ[B] Lⱼ → …) …`
  but every canonical datum lives over `centralizer A` (`centralizerModuleHom`,
  `hL_simp` from `..._bimodule_decomposition_explicit`, `multiplicitySpace_Cdistinct`),
  filling the binders with `h ▸ inferInstance` / `h ▸ hL_simp i` desyncs the
  instances: later `IsSimpleModule`/`≃ₗ` binders expect the *transported* `Module B`
  instance while your term carries the canonical one (type-mismatch on the instance
  argument). Instead `rw [← h]` once at the top so the whole goal is back over
  `centralizer A`, then `refine` with the canonical `inferInstance` / `hL_simp` /
  `multiplicitySpace_Cdistinct … ⟨f⟩` directly. Single-binder `h ▸` (as in
  `Theorem5_18_4_bimodule_decomposition`) is fine; *multiple interdependent
  binders* are what break. See `SchurWeylBimoduleFull.lean`.
- **`centralizerModuleHom` firing twice needs an `IsScalarTower` companion
  (Ch5, #4926).** To get `Module ↥(centralizer C) ((V →ₗ[A] E) →ₗ[C] E)` you
  re-apply `Theorem5_18_1.centralizerModuleHom` with `C` in the `A`-slot; this
  requires `IsScalarTower k ↥C (V →ₗ[A] E)`, which is NOT automatic. Provide it
  (`smul_assoc r b f := LinearMap.ext fun v => by change (r•b).val (f v) = …;
  rw [Subalgebra.coe_smul, LinearMap.smul_apply]`). Note: even *stating* this
  instance (its `SMul` in the signature) overruns the default 20000 synth
  heartbeats — bump `synthInstance.maxHeartbeats` on the instance itself.
- **Bundled instances from a destructured existential are already usable — do
  NOT re-`haveI` them (Ch5, #4716).** Decomposition theorems
  (`glTensorRep_..._decomposition...`) return `∃ (S : ι → Type u)
  (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module k (S i)) …`. After
  `obtain ⟨…, S, hSacg, hSmod, hSfin, …⟩`, those hypotheses are automatically
  local instances: `Module k (S i)`, `S i ⊗[k] (L i)`, `trivial k G (S i)`
  all resolve with no `haveI`. Pitfalls that cost real debugging time:
  - The anonymous form `haveI := hSmod` for a *Pi-quantified* instance can fail
    to register a usable instance. Always use the type-ascribed form
    `haveI iSmod : ∀ i, Module k (S i) := hSmod` — or, better, just rely on the
    `obtain` hypotheses directly and add nothing.
  - Re-introducing an instance that already exists (e.g. `haveI iSacg : ∀ i,
    AddCommGroup (S i) := hSacg` when `hSacg` is in scope) creates a *competing*
    instance term; later `Module k (S i)` picks the new one while the source
    hypothesis still carries the old one, producing `AddCommGroup`-diamond
    type-mismatches.
  - Symptom of getting this wrong: a cascade of misleading
    `failed to synthesize Module k (S i)` errors plus a `(deterministic)
    timeout at whnf` (the fallback global instance search is what blows the
    heartbeats — bumping `maxHeartbeats` does NOT fix it, fixing the instance
    setup does). Only `haveI` instances that are genuinely *missing*, e.g.
    `Module.Free` over a field: `haveI : ∀ i, Module.Free k (S i) :=
    fun i => Module.Free.of_divisionRing k (S i)`. For a `Type 0` basis index
    (needed when the result type demands `Type`, not `Type u`), use
    `Fin (Module.finrank k (S i))` with `Module.finBasis k (S i)`.

### Proving `IsAlgebraicRepresentation` (Ch5 §5.23, #4756)

`detTwistedSchurModuleRep_isAlgebraic` (`Chapter5/DetTwistAlgebraic.lean`) is the
first algebraicity proof for a concrete rep, and ships **three reusable lemmas** —
reach for these before re-deriving for any other `GL_N` rep (e.g. bare
`schurModuleRep`, `glTensorRep`, further twists):

- `glTensorRep_isAlgebraic` — the diagonal action is algebraic; matrix coefficient
  in `tBasisAlg` is the monomial `∏ₘ X_{(h m, f m)}`.
- `IsAlgebraicRepresentation.restrict (W) (hW)` — restrict to a `ρ`-invariant
  submodule. (`schurModuleRep` algebraicity falls out as the intermediate step.)
- `IsAlgebraicRepresentation.detTwist` — twist by the `det` character.

Plus `evalAtGL_{mul,sum,prod,C,X_inl}`: `evalAtGL g` is `MvPolynomial.eval σ`, a
ring hom, so it commutes with `*`/`∑`/`∏`/`C`; prove each by
`simp only [Etingof.evalAtGL, map_mul]` etc. The det polynomial is `detPolyGL`
(det of the generic `(Xᵢⱼ)` matrix); `evalAtGL g detPolyGL = det g` via
`RingHom.map_det`.

Three API gotchas that cost build cycles here:
- **Tensor-basis coefficients:** `Basis.piTensorProduct_repr_tprod_apply` gives
  `(piTensorProduct b).repr (⨂ₜ x) p = ∏ i, (b i).repr (x i) (p i)` — the clean way
  to read a coefficient of `PiTensorProduct.map f (tprod …)`.
- **`Matrix.col` has no `col_apply`.** `M.col j = Mᵀ`, so `(M.col j) i` is
  *definitionally* `M i j` (via `transpose`/`of_apply`). After
  `rw [Matrix.mulVec_single_one]` just close the entry goal with `rfl`, not a
  `col_apply` simp (which does not exist).
- **`Basis.repr_reindex_apply` needs full qualification** as
  `Module.Basis.repr_reindex_apply` (and `Module.Basis.reindex_apply`); the bare
  `Basis.`-prefixed forms fail to resolve. Use these to fit a non-`Fin`-indexed
  basis (e.g. `tBasisAlg : Basis (Fin n → Fin N)`) into the `Fin m`-indexed
  `IsAlgebraicRepresentation` predicate by reindexing through `Fintype.equivFin`.
- **`let` not `set` for locals whose *defeq* you rely on** (here a projection `π`
  and the functional `φ y = b'.repr (π y) a`): `set` introduces an *opaque* local,
  so terms like `linearProjOfIsCompl_apply_left` (which mention the unfolded
  expression) no longer typecheck against it, and `fun _ => rfl` proofs break.

- **GL-element inverse coercion to `Matrix` is ambiguous — annotate, or use `.val`.**
  Writing `((g i)⁻¹ : Matrix _ _ k)` for `g i : GL (Fin p) k` (e.g. the base-change
  action `g j · M · (g i)⁻¹` in `Problem6_1_5_OrbitSpace.lean`) elaborates with
  unresolved metavariables and times out typeclass synthesis: Lean cannot decide
  between *GL-inverse-then-coerce* and *coerce-then-`Matrix.inv`*, and the `_ _`
  dimensions never pin down. Write `(↑(g i)⁻¹ : Matrix (Fin p) (Fin p) k)` with the
  coercion arrow **and** explicit dimensions, or `(g i)⁻¹.val`. Then the GL coe lemmas
  (`Matrix.GeneralLinearGroup.coe_mul/coe_inv/coe_one`) drive the proofs, and
  `(↑g)⁻¹ * ↑g = 1` comes via `← coe_mul; (mul_inv_cancel/inv_mul_cancel); coe_one`.
  To turn a vertex `≃ₗ` into a `GL` element, build the `Units` directly
  (`⟨toMatrix' e, toMatrix' e.symm, _, _⟩`, val/inv discharged by `← toMatrix'_comp`,
  `e ∘ₗ e.symm = id` via `ext; simp`, `toMatrix'_id`) — its coe to `Matrix` is then
  `rfl`-equal to `toMatrix' e`, which makes the orbit↔iso intertwining a clean
  `toMatrix'`/`toLin'` round-trip. Rectangular matrices need `Matrix.mul_one`/
  `Matrix.mul_assoc`, **not** the monoid `mul_one`/`mul_assoc`.

- **`DirectSum ι L` semisimple/finite instances** resolve through the `Π₀`
  (`DFinsupp`) instances: `inferInstanceAs (IsSemisimpleModule R (Π₀ i, L i))`.
  `DirectSum.lof R ι L i` is *defeq* to `DFinsupp.lsingle i`, so its injectivity
  comes from `DirectSum.component.lof_self` (a left inverse) and the coordinate
  lines span via `DFinsupp.iSup_range_lsingle`.

- **Transferring `IsSimpleModule` across a `Subalgebra` equality of acting rings**
  (recurs in Schur-Weyl: `diagonalActionImage = centralizer(symGroupImage)` via
  `Theorem5_18_4_centralizers`). The two `↥A`-module structures are over
  *propositionally* equal subalgebras, so there is no shared-ring `LinearEquiv`.
  Route: `φ := (Subalgebra.equivOfEq _ _ h).toRingEquiv`, build a `φ.toRingHom`-
  **semilinear** equiv `e : ↥M₁ ≃ₛₗ[φ.toRingHom] ↥M₂` (often the carrier-identity
  map — both submodules' carriers are defeq, both smuls are `b.val • x.val` and
  `(φ a).val = a.val` defeq, so `toFun/invFun = fun x => ⟨x.val, _⟩` and
  `map_add'/left_inv/right_inv = rfl`; `map_smul'` closes with
  `Subtype.ext` + the smul-coe lemmas + `SetLike.val_smul` then `rfl`). Then
  `Submodule.orderIsoMapComap e : Submodule R₁ M₁ ≃o Submodule R₂ M₂` and
  `(…).isSimpleOrder_iff.mpr h.toIsSimpleOrder`. Two gotchas: (1) **`RingHomInvPair
  φ.toRingHom φ.symm.toRingHom` is NOT a Mathlib instance for a `RingEquiv`** —
  provide both directions locally (`haveI : RingHomInvPair … := ⟨by ext x; simpa
  using φ.symm_apply_apply x, by ext x; simpa using φ.apply_symm_apply x⟩`), else
  the `≃ₛₗ` and `orderIsoMapComap` fail to synthesize. (2) `IsSimpleModule` is a
  *class extending* `IsSimpleOrder` (not defeq) — rebuild with
  `exact { toIsSimpleOrder := hso }`, and pin the semilinear ring hom explicitly
  (`≃ₛₗ[φ.toRingHom]`, not `≃ₛₗ[(φ : _ →+* _)]`) or it stays a metavariable and
  blocks `SetLike.val_smul`.

- **Reconstructing a public lemma's `LinearMap.restrict` map when its membership
  proof is `private`.** Lemmas like `youngSym_action_vanishes_off_block` /
  `_rank_one_scaled_proj` state their conclusion about
  `(f).restrict (p := S.restrictScalars k) … (private_mem_proof)`. You can still
  feed that map to an interface expecting `g : ∀ i, ↥(S i) →ₗ[k] ↥(S i)`: define
  `g i := (f).restrict … (your_own_mem_proof)` with a public membership lemma —
  the proof argument is a `Prop`, so the two `restrict`s are **defeq** (proof
  irrelevance), and `have hzero : g i = 0 := <the public lemma>` typechecks by
  defeq. Also: `↥(S.restrictScalars k)` is defeq to `↥S` (restrictScalars keeps
  the carrier), and for an `A`-submodule `S` with `IsScalarTower k A E` the two
  `Module k` structures on `↥S` and `↥(S.restrictScalars k)` agree by defeq, so
  the restrict-typed map slots in where `↥(S i) →ₗ[k] ↥(S i)` is expected. When a
  per-block scalar `α'` (from a rank-1 lemma's existential) must match an
  independently-obtained `α` (`c² = α•c`), reconcile via `f² = α•f`, `f = α'•π'`,
  `π' ≠ 0`, `smul_left_injective k hπ'_ne`, then `mul_right_cancel₀`.

- **Opaque-parameter isolation defeats `whnf`/`isDefEq` heartbeat timeouts in
  `compHom`/`restrictScalars` transfer constructions.** When building a
  `LinearEquiv` over the deep `Subalgebra → Subsemiring → Module` chain (e.g.
  transferring a `SymGroupAlgebra`-iso to a `symGroupImage`-iso through
  `symGroupAlgHomToImage`), a complex equiv held in a local `let`
  (`set g := e₁.trans e₂.symm`) makes the structure-field proofs time out —
  `whnf` unfolds the large source isos (here `Theorem5_12_2_classification`).
  `clear_value g` does **not** help. Fix: move the construction into a standalone
  `def` that takes the big equiv as an explicit **parameter** (`letI`-typed if it
  needs the `compHom` module instance); the body elaborates once with the equiv
  genuinely opaque. Then the caller is a one-line `exact ⟨transferDef S S' g⟩`.
  **Same fix for a `let`-heavy finite-family dedup/choice proof over a CONCRETE
  `Sum.elim` family** (Ch5 #5100, the clean constituent extractor): assembling
  `{L} ∪ {W j} ∪ {V ν}` as `R := Sum.elim … (Sum.elim …)` and then running the
  dedup-by-character machinery (`Finset.image`/`choose pick`/`Rep := fun w => R
  (pick w)`/engine call) *inline* hit a genuine `(deterministic) timeout at whnf`
  that did **not** clear even at `maxHeartbeats 6400000` — the `isDefEq` checks
  (`Rep w = R (pick w)`, `χ (pick w) = formalCharacter (Rep w)`, the engine's
  unification against the concrete `FDRep` carriers) loop while reducing `R`
  through `Sum.elim` + `FDRep`/`FGModuleCat` coercions. Fix: extract the entire
  dedup step into a standalone lemma quantified over an **abstract** `R : ι →
  FDRep` (conclusion a plain `∑ i ∈ univ.filter (char (R i) = w), a i = 0`); its
  body type-checks once with `R` opaque (no `Sum.elim` to reduce), and the caller
  applies it to the concrete family in one line. After extraction the main theorem
  compiled at the **default** budget. Heuristic: a `whnf` timeout that survives a
  6.4M bump is a defeq *loop*, not a budget shortfall — relocate the offending
  reduction behind an abstract parameter rather than raising heartbeats.

- **Pin `f (N := N) (n := n)` on a hom application feeding a `•`** whose scalar
  type is being inferred (e.g. `(symGroupAlgHomToImage (N := N) (n := n) a) • x`).
  Otherwise `N` is a stuck metavariable ("typeclass instance problem is stuck").

- **`congrArg Subtype.val (g.<lemma> ⟨x.val, x.property⟩)`** discharges the
  `left_inv`/`right_inv`/`map_add'` fields of a carrier-identity submodule
  `LinearEquiv` by defeq. Prefer it over `rw [show ⟨…⟩ = g … from rfl, …]`, which
  fails on "pattern not found" because the post-`Subtype.ext` goal is not
  syntactically normalised.

- **`set` reverts/shadows any hypothesis whose *type* mentions the set term —
  spawns a `S✝` that no longer unifies (Ch5, #4731).** Proving over Schur-Weyl
  hom-spaces `↥S →ₗ[symGroupImage k V n] TensorPower k V n`, writing
  `set A := symGroupImage k V n` / `set E := TensorPower k V n` for brevity
  abstracts those terms *inside* the types of `S`, `W`, `ψ`, forcing `set` to
  revert and reintroduce them — the binder comes back as inaccessible `S✝` and a
  later `exact`/`show` against the original `S` fails with a type mismatch. Only
  `set` the term that does **not** appear in any in-scope binder's type (here the
  centralizer `C`); leave `symGroupImage`/`TensorPower` written out literally.

- **`Algebra.adjoin_induction` over a `Subalgebra` element: `obtain ⟨cval, hcmem⟩
  := c` up front (Ch5, #4731).** The predicate
  `p := fun x _ => ∀ (hx : x ∈ C) …, … (⟨x, hx⟩ : ↥C) • l …` produces a goal in
  the `⟨cval, hcmem⟩` shape; if `c : ↥C` is still bundled, the final
  `… hgen c.2 l` leaves `ψ (⟨↑c, _⟩ • l) = …` versus goal `ψ (c • l) = …`, which
  is only `Subtype`-eta-defeq and a `show`/`exact` bridge **times out** (or hits
  the `c✝` shadow from a prior `set`). Destructuring `c` first makes the goal
  literally match. Mirror the model proof
  `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem`
  (`SchurWeylGLTransfer.lean`); since the generating set is the *units* one
  (`adjoin_unitsTensorPow_eq_diagonalActionImage`), no inner
  `Submodule.span_induction` is needed. In the `mul` case apply the IH to the
  *bundled* `(⟨y, hyC⟩ : ↥C) • l`, never the raw `y • l` (no `HSMul (End …)
  (hom-space)`). These heavy `Module.End (TensorPower)` chains need
  `maxHeartbeats 6400000 / synthInstance.maxHeartbeats 3200000`, matching the
  source theorems.

### Fraction-field bridge: principal open shares the polynomial ring's k(g) (Ch6, #4783)

To send an injective comorphism `φ : MvPolynomial (Fin N) k →ₐ[k] B` into
`FractionRing (MvPolynomial (Fin M) k)` when `B` is a localization of
`P := MvPolynomial (Fin M) k` (the coordinate ring of a principal open `{det ≠ 0}`,
e.g. the `det⁻¹`-localization forced by a base-change `g_j·M·g_i⁻¹` action), do **not**
hunt for an `Algebra B (FractionRing P)` instance — none exists. Build it:

```lean
set P := MvPolynomial (Fin M) k; set K := FractionRing P
have hSle : S ≤ nonZeroDivisors P := ...        -- 0 ∉ S since `IsDomain B`
have hunit : ∀ y : S, IsUnit (algebraMap P K y) :=
  fun y => IsLocalization.map_units K (⟨y, hSle y.2⟩ : nonZeroDivisors P)
letI : Algebra B K := (IsLocalization.lift (M := S) (g := algebraMap P K) hunit).toAlgebra
have hcomp : (algebraMap B K).comp (algebraMap P B) = algebraMap P K := by
  change (IsLocalization.lift hunit).comp (algebraMap P B) = algebraMap P K  -- `change`, not `show`
  exact IsLocalization.lift_comp hunit
haveI : IsScalarTower P B K := IsScalarTower.of_algebraMap_eq' hcomp.symm
haveI : IsFractionRing B K :=                    -- the principal-open identification
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S B K
haveI : IsScalarTower k B K := IsScalarTower.of_algebraMap_eq fun x => by
  rw [IsScalarTower.algebraMap_apply k P K x, ← hcomp, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply k P B x]
```

`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` (in
`Mathlib/RingTheory/Localization/LocalizationLocalization.lean`) is load-bearing — over
a domain it needs no `S ≤ nonZeroDivisors` side goal. `Algebra k (FractionRing P)` and
`IsScalarTower k P (FractionRing P)` are already global instances. Gotcha: when a helper
lemma's `{M}`/`{S}` appear only in *instance* args and the conclusion (not in an explicit
value arg like `φ`), pass them explicitly (`(M := M) (S := S)`) or TC resolution stalls
on a metavariable. See `Problem6_1_5_FieldEmbedding.lean`.

### Orbit-map comorphism: generic matrices over the det-localization (Ch6, #4803)

Building the comorphism `k[W] → B` of an orbit map `g ↦ g•v₀` into the principal-open
coordinate ring `B` (the `det⁻¹`-localization the bridge above consumes). Four idioms:

- **Index `MvPolynomial` by the sigma type, not `Fin N`.** Use
  `GIdx m := Σ i, Fin (m i) × Fin (m i)` and `WIdx m := Σ i j, (i⟶j) × (Fin (m j) × Fin (m i))`
  directly as the `MvPolynomial` index. `Fintype.card_sigma`/`card_prod` give the dimension
  formulas (`gIdx_card = Σmᵢ²`, `wIdx_card = Σbᵢⱼmᵢmⱼ`). Defer the `Fin N`/`Fin M` form the
  bridge wants to a `MvPolynomial.renameEquiv (Fintype.equivFin _)` at the assembly step.
- **A polynomial (or determinant) is nonzero by *evaluating at a concrete point*, not by
  Leibniz expansion.** For `detProd = ∏ᵢ det(genMat m i)`, build `evalId := aeval (fun w =>
  if w.2.1 = w.2.2 then 1 else 0)` (the identity matrix), then `evalId detProd = ∏ det 1 = 1`
  via `map_prod` + `AlgHom.map_det` + `Matrix.det_one`; a ring hom sends `0 ↦ 0`, so `≠ 0`.
- **`AlgHom.map_det f M` produces `(f.mapMatrix M).det`, NOT `(M.map ⇑f).det`.** State the
  "mapped matrix = 1" helper with `AlgHom.mapMatrix` (`simp [..., AlgHom.mapMatrix_apply,
  Matrix.map_apply, Matrix.one_apply]`) so it rewrites after `map_det`.
- **Two confusing-error gotchas when building `aeval`-style endomorphisms of
  `MvPolynomial`.** (1) Bare `X`/`C` do **not** resolve under `open MvPolynomial`
  with `import Mathlib` (another `X` is in scope) — symptom is a misleading
  `Function expected at ...`. Qualify `MvPolynomial.X` / `MvPolynomial.C`
  everywhere, including inside statements and `simp` args. (2) An unannotated sum
  binder `∑ l, ...` whose index type is only pinned by the body also throws
  `Function expected`; write `∑ l : Fin N, ...`. (3) `Finset.sum_congr rfl ...`
  can fail with `typeclass instance problem is stuck` when the two sides' sums
  carry syntactically different `Fintype`/`univ` instances even though both are
  `Finset.univ`; `simp only [mul_comm]` (or the relevant per-term rewrite under
  the binder) is instance-robust where `sum_congr` chokes.
- **Parametrize the comorphism `def` over an *abstract* localization `B`**
  (`[Algebra (MvPolynomial (GIdx m) k) B] [IsLocalization (Submonoid.powers (detProd m)) B]
  [Algebra k B] [IsScalarTower k _ B]`), not a concrete `Localization`: there is no
  `Algebra k (Localization S)` instance, and abstract `B` matches the bridge's style.
  Det-units come from `IsLocalization.map_units B ⟨detProd, Submonoid.mem_powers _⟩` plus
  `isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem ..))`; invert via
  `Matrix.mul_nonsing_inv _ (isUnit_det ..)`. See `Problem6_1_5_OrbitComorphism.lean`.
- **Orbit-comorphism injectivity via per-element evaluation (`Problem6_1_5_OrbitInjective.lean`,
  #4807).** To prove `orbitComorphism v₀ : k[W] →ₐ B` (into the abstract `detProd⁻¹`
  localization) injective, evaluate at each group element: `evalAt g := IsLocalization.liftAlgHom`
  of `aeval (groupEntries g)` (the `detProd`-units hypothesis discharges via
  `(Submonoid.mem_powers_iff _ _).mp y.2` + `map_pow` + `IsUnit.pow`). Prove the identity
  `evalAt g ∘ orbitComorphism v₀ = aeval (pointCoords (g • v₀))` by `MvPolynomial.algHom_ext`.
  The base-change product `g_j · M · g_i⁻¹` is **rectangular**, so `AlgHom.mapMatrix`/`map_mul`
  (square only) do NOT apply: push the ring hom through entrywise with
  `key : ∀ M, evalAt g (M a b) = (M.map (evalAt g)) a b := fun _ => rfl`, then `Matrix.map_mul`
  (a `NonUnitalRingHomClass` lemma — works for rectangular) twice. Map generic matrices via
  `evalAt_algebraMap` (= `IsLocalization.lift_eq`); for the inverse, get `(g i)⁻¹` from
  `Matrix.inv_eq_right_inv` (avoids `Ring.inverse`) and **match the GL-inverse-then-coerce form
  of `repSpace_smul_apply`** by stating the lemma RHS as `(((g i)⁻¹ : GL (Fin (m i)) k) : Matrix ..)`,
  not `((g i)⁻¹ : Matrix ..)`. Injectivity then follows from algebraic density of the orbit
  (`injective_iff_map_eq_zero` + the density predicate). The density itself (Problem 6.1.2a) is
  purely algebraic: finitely many orbits ⟹ a dense orbit by product-of-vanishing-witnesses
  (`Finset.prod_eq_zero`/`prod_ne_zero_iff`) + `MvPolynomial.funext` over `[Infinite k]` — no
  Zariski topology. Group-side lemmas (GIdx/genMat/detProd) need `omit [Quiver ..] [∀ i j, Fintype ..] in`
  to silence section-var linters; the `omit` must precede any docstring.

### Index-agnostic dimension bound: transport a localization bridge to `Fin` (Ch6, #4808)

Assembling `card σ ≤ card τ` (`dim W ≤ dim G`) from an injective comorphism
`φ : k[xσ] → B`, where `B` is a domain localization of `k[xτ]` at `S`, by reusing a
bridge phrased over `Fin N`/`Fin M` (`Problem6_1_5_DimBound.lean`). Both indices move
to `Fin` via `MvPolynomial.renameEquiv (Fintype.equivFin _)`:

- **Source: precompose.** `φ.comp (renameEquiv k (Fintype.equivFin σ).symm).toAlgHom`,
  injective via `hφ.comp (renameEquiv ..).injective` (align the coe with `AlgHom.coe_comp`
  / an `ext` + `simp` if `exact` balks).
- **Base: carry `IsLocalization` across the rename ring equiv.** Let
  `h := (renameEquiv k eτ).toRingEquiv`. `IsLocalization.isLocalization_of_base_ringEquiv S B h`
  proves `IsLocalization (S.map h) B` **but for a specific new algebra instance**
  `((algebraMap (MvPolynomial τ k) B).comp h.symm.toRingHom).toAlgebra` — you must
  `letI algB := that exact term` so the instance it returns matches. Then build
  `IsScalarTower k (MvPolynomial (Fin M) k) B` by hand: `IsScalarTower.of_algebraMap_eq`,
  unfold the new map with `RingHom.algebraMap_toAlgebra`, and discharge
  `h.symm.toRingHom (algebraMap k _ x) = algebraMap k _ x` by `(renameEquiv k eτ).symm.commutes x`
  (defeq: `h.symm.toRingHom` applied IS `(renameEquiv k eτ).symm` applied, since `h` is a `let`).
- **Pin the transported submonoid at the bridge call:** `bridge (S := S.map h) φ' hφ'` — the
  bridge's `{S}` is not fixed by its value args, so TC stalls otherwise (same metavar idiom as
  the FieldEmbedding note above).
- **The concrete `B = Localization (Submonoid.powers (detProd m))` has all instances.**
  `Algebra (MvPolynomial (GIdx m) k) B`, `IsLocalization`, `Algebra k B`, and
  `IsScalarTower k _ B` all synthesize **when `Localization S` is written directly** — contra
  the #4803 note's "no `Algebra k (Localization S)`", which bites only if you `let B := …`
  (a `let`-bound local blocks instance synthesis; inline the type instead). `IsDomain B` via
  `IsLocalization.isDomain_localization (M := …) (powers_le_nonZeroDivisors_of_noZeroDivisors
  (detProd_ne_zero ..))`.

### Norm-Based Contradiction (Analysis Proofs)

For proofs requiring algebraic integer arguments (e.g., Lemma 5.4.5):
1. Use `Algebra.norm` to map from the algebraic number to a rational integer
2. Establish `|Norm(α)| ≥ 1` (since α is a nonzero algebraic integer, its norm is a nonzero integer)
3. Establish `|Norm(α)| < 1` via triangle inequality and `norm_sum_lt_of_strictConvexSpace`
4. Derive contradiction

This two-step norm approach works whenever you need to show an algebraic quantity equals zero or a root of unity.

### Unitarizability: diagonalize a `ℂ[G]`-operator via the spectral theorem (#6311)

When a finite-group operator must be shown diagonalizable / to have bounded real eigenvalues, put an invariant inner product on `V` and use self-adjointness. Recipe (from `Problem5_16_3`, `sumTranspositionsWith1_diagonalizable_integer_eigenvalues`):

```lean
obtain ⟨c, hc⟩ := Etingof.Theorem4_6_2_existence G V ρ   -- c : InnerProductSpace.Core ℂ V, hc = G-invariance
letI icore : InnerProductSpace.Core ℂ V := c
letI : NormedAddCommGroup V := c.toNormedAddCommGroup           -- reuses the ambient AddCommGroup...
letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore inferInstance  -- ...so Module.End ℂ V is unchanged
```

Key points:
- **No diamond:** `Core.toNormedAddCommGroup` goes through `AddGroupNorm.toNormedAddCommGroup`, which keeps `.toAddCommGroup` defeq to the ambient one. So `T : Module.End ℂ V` and any produced `Module.Basis` still match the pre-existing goal types.
- **`ofCore` wants a `PreInnerProductSpace.Core`.** Make `c` a local instance (`letI icore := c`) and pass `inferInstance` — the `[InnerProductSpace.Core] → PreInnerProductSpace.Core` instance fires. Then `inner ℂ` is defeq to `c.inner`, so the invariance hypothesis `hc` is reusable verbatim (`have hc' : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w := hc`).
- **`ρ g` is an isometry** (`‖ρ g x‖ = ‖x‖`): square both sides, `rw [← inner_self_eq_norm_sq (𝕜 := ℂ), …, hc']`, finish with `Real.sqrt_sq`.
- **Self-adjoint:** a unitary involution `s` (with `s * s = 1`, e.g. `Equiv.swap_mul_self`) gives `(ρ s).IsSymmetric` from `⟪ρ s x, y⟫ = ⟪ρ s x, ρ s (ρ s y)⟫ = ⟪x, ρ s y⟫`; sums stay symmetric (`sum_inner`/`inner_sum`).
- **Spectral theorem:** `hT.eigenvectorBasis rfl |>.toBasis` (+ `OrthonormalBasis.coe_toBasis`, `hT.apply_eigenvectorBasis rfl i`) gives the eigenbasis; eigenvalue bounds come from `μ = ⟪w', T w'⟫` on a normalized eigenvector plus `norm_inner_le_norm` (Cauchy–Schwarz) and `norm_sum_le`.

### `sorry : Prop` for Unprovable Statements

When Mathlib lacks the types to express a theorem's statement at all (not just the proof), use:

```lean
/-- Theorem X.Y.Z: [natural language statement].
    Statement requires infrastructure not yet in Mathlib. -/
theorem theorem_X_Y_Z : (sorry : Prop) := sorry
```

This is sanctioned for items where the *statement itself* cannot be formalized (e.g., Gabriel's theorem needing quiver representation types, sl(2) classification). These items cannot be proved until infrastructure is built. Track them with status `needs_infrastructure` in items.json.

**Never use `True` as a placeholder** — it compiles silently and hides the gap.

### Multipart Theorem Strategy

When a theorem has multiple parts (e.g., existence + uniqueness, or (i)+(ii)+(iii)), prove them independently and leave unsolved parts as `sorry`:

```lean
theorem foo : Part1 ∧ Part2 ∧ Part3 := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: proved
    exact proof1
  · -- Part 2: hardest, work on this first
    sorry
  · -- Part 3: easy, fill in after Part 2
    sorry
```

**Always work on the hardest part first.** If Part 2 fails, all effort on Parts 1 and 3 is wasted. Commit partial proofs — they document exactly what's missing and unblock downstream work that doesn't need the sorry'd parts.

This pattern succeeded for Theorem 3.10.2 (part i proved, part ii sorry'd), Theorem 5.4.4 (main structure done, one ingredient sorry'd), and IrreducibleEnumeration (injectivity + simplicity proved, surjectivity sorry'd).

### Character Orthogonality for Span/Independence (Wave 30)

When proving that a set of characters spans or is linearly independent, use inner product orthogonality:

```lean
-- Prove ℚ-span via orthogonality + induction
have h_orth := FDRep.char_orthonormal
-- Use span_induction to reduce to showing each basis element is in the span
apply Submodule.span_induction ...
```

**Key APIs:** `FDRep.char_orthonormal`, `ClassFunction.inner_eq_zero_of_ne`, `Submodule.exists_le_ker_of_notMem`.

**Evidence:** This proved Theorem5_26_1 (Artin's theorem) completely — both `class_fun_vanishes_on_subgroup_of_orthogonal` and `artin_Q_span_of_induced_chars` used character inner products. Also proved the character orthogonality lemma for `principalSeries_simple_of_ne`.

**Pattern:** For any "show X is in the span of Y" problem in representation theory, first check if orthogonality gives you a clean proof. It usually does.

### Character reality `χ(g⁻¹) = conj χ(g)` is in the project, not Mathlib (Ch6 #6631)

Mathlib's finite-group character lemmas (`FDRep.char_orthonormal`,
`FDRep.scalar_product_char_eq_finrank_equivariant`) are stated with `V.character g⁻¹`, **not**
`conj (V.character g)`. Any Hermitian-positivity argument (`(f,f) ≥ 0`, `∑_g (…)·|f(g)|² ≥ 0`)
needs the reality identity to convert `f(g⁻¹)` into `conj (f(g)) = ↑normSq`. This identity is
**not in Mathlib** but **is already proved in the project**:
`Etingof.char_inv_eq_conj (V : FDRep ℂ G) (g : G) : V.character g⁻¹ = (starRingEnd ℂ) (V.character g)`
(`Chapter4/Discussion_4_4.lean`, needs `[Fintype G]`). **Grep `EtingofRepresentationTheory/Chapter4/`
for standard finite-group character theory before proving any such fact from scratch** — Ch4
formalizes orthonormality, class-function completeness (`Theorem4_2_1`,
`classFunction_eq_zero_of_orthogonal_simples`), unitarizability (`Theorem4_6_2`), and this reality
identity. Worked use: `mckayCartan_posSemidef` (McKay Cartan form `xᵀ(2δ−r)x ≥ 0`) computes
`|G|·(xᵀ(2δ−r)x) = ∑_g (2−χ_V(g))·f(g)·f(g⁻¹)`, rewrites `f(g⁻¹) = conj(f(g))` via
`char_inv_eq_conj` + `map_intCast` (real coefficients), then `Complex.mul_conj` gives `↑normSq`
and each factor `2−χ_V(g) ≥ 0` from the `SU(2)` trace bound. For the reality of a specific
character (`χ_V` real), combine `char_inv_eq_conj` with a self-duality fact like `charV_inv`
(`χ_V(g⁻¹)=χ_V(g)`) to get `conj z = z`, then `Complex.conj_eq_iff_im`.

### IsSplitMono + Cokernel for Representation Decomposition (Wave 30)

When proving a representation decomposes as a direct sum V ≅ A ⊕ B:

1. Construct a nonzero mono `f : A ⟶ V` (e.g., an embedding)
2. Apply Maschke's theorem to get `IsSplitMono f`
3. Use `binaryBiconeOfIsSplitMonoOfCokernel` to get V ≅ A ⊞ cokernel(f)
4. Identify cokernel(f) ≅ B (often via dimension counting)

```lean
-- Step 1: Get IsSplitMono from Maschke
have hsm : IsSplitMono detCharEmbedding := Abelian.IsSplitMono_of_mono _
-- Step 2: Build biproduct via cokernel
exact binaryBiconeOfIsSplitMonoOfCokernel detCharEmbedding
```

**Evidence:** This approach is set up for `principalSeries_decomp` (V(μ,μ) ≅ ℂ_μ ⊕ W_μ). The infrastructure lemmas (detChar_simple, detCharEmbedding_mono, detCharEmbedding_ne_zero) proved in PRs #1624, #1658 feed directly into this pattern.

### Dimension Contradiction Pattern (Wave 30)

For proving properties by contradiction using `Module.finrank`:

```lean
-- Show two finite-rank subspaces can't both fit
have h1 : Module.finrank k S₁ ≥ 1 := ...
have h2 : Module.finrank k S₂ ≥ 1 := ...
have h3 : Module.finrank k V = Module.finrank k S₁ + Module.finrank k S₂ := ...
-- Derive contradiction from dimension inequality
omega
```

**Evidence:** Proved nilpotent_nontrivial_decomp (d=1 contradiction in PR #1628, subrepresentation arguments in PR #1632). Also used in decomp_of_ker_sum_ge_two dimension argument (PR #1633).

### Graph Isomorphism for Classification Proofs (Wave 30)

For Dynkin-type classification proofs requiring graph isomorphisms between combinatorially-defined graphs:

```lean
-- Build explicit bijection via path permutation
def tree_branch_iso : G₁ ≃g G₂ where
  toEquiv := pathPermutation ...  -- permute vertices along a canonical path
  map_rel_iff' := ...
```

**Evidence:** PR #1634 used `tree_branch_iso` to prove all 4 arm cases (D_n, E₆, E₇, E₈) in `branch_classification`, reducing Theorem_Dynkin_classification from 6 sorries to 0. The key insight: express graph isomorphisms as path permutations with optional reversal.

### PolytabloidBasis Dual-Track Architecture (Wave 46)

The polytabloid basis proof uses **two complementary tracks**:

**Track 1: Group algebra (PolytabloidBasis.lean)** — works with elements of ℂ[S_n]:
- `polytabloid T = κ_T · of(σ_T) · a_λ` where κ_T is the T-dependent column antisymmetrizer
- Coefficient formulas (`polytabloid_apply`, `polytabloid_self_coeff`, `polytabloid_support`)
- Straightening: reducing arbitrary σ · c_λ to a sum of polytabloids (needs Garnir + WF order)
- Handles the **spanning** direction

**Track 2: Tabloid module (TabloidModule.lean)** — works with tabloid equivalence classes:
- Tabloid = left P_λ-coset = equivalence class under row permutations
- `tabloidDominance`: partial order via cumulative entry counts
- `polytabloid_syt_dominance`: if e_{T₁}(σ_{T₂}) ≠ 0 then tabloid(T₁) dominates tabloid(T₂)
- Unitriangular projection matrix → **linear independence**

**When to use which track:**
- Coefficient computations (evaluating e_T at σ) → Track 1
- Linear independence arguments → Track 2 (via tabloid dominance + unitriangularity)
- Spanning arguments → Track 1 (via straightening algorithm)
- The two tracks connect through `polytabloid_support` (Track 1 feeds into Track 2's dominance argument)

**Key pitfall:** Don't try to prove linear independence by direct evaluation in ℂ[S_n]. The evaluation matrix c_λ(σ_{T₁}⁻¹ · σ_{T₂}) is NOT upper-triangular — it can be nonzero in both directions for distinct T₁, T₂. Only the tabloid projection approach gives the triangularity structure.

### MonoidAlgebra Coefficient Computation (Wave 46)

For proving coefficient formulas in `MonoidAlgebra ℂ (Equiv.Perm (Fin n))`:

```lean
-- Evaluating (a * b)(σ) where a, b : MonoidAlgebra ℂ G
-- Uses: MonoidAlgebra.mul_apply, Finsupp.sum
-- Key: (a * b)(σ) = Σ_{g} a(g) * b(g⁻¹ * σ)

-- For sums like RowSymmetrizer:
-- (RowSymmetrizer)(σ) = if σ ∈ P_λ then 1 else 0
-- Use: Finsupp.single_apply, Finset.sum_ite

-- For products with of(σ):
-- (of(σ) * a)(τ) = a(σ⁻¹ * τ)
-- Use: MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply
```

**Pattern:** Expand definitions → use `Finsupp.sum` / `Finset.sum` manipulation → simplify using subgroup membership predicates. The hardest part is usually showing that sums over subgroups telescope to 0 or 1 using intersection triviality (e.g., `row_col_inter_trivial'`: P_λ ∩ Q_λ = {1}).

### Char-equality ⟹ iso, and FDRep semisimple-classification toolkit (Ch5 #5247)

`Etingof.charEq_iso` (`Chapter5/CharEqIso.lean`) is **done and sorry-free**: for
`V W : FDRep ℂ G` (finite `G`), `V.character = W.character → Nonempty (V ≅ W)`,
the converse of `FDRep.char_iso`. **Use it, don't rebuild it** when a character
identity needs upgrading to an isomorphism (e.g. induced-rep decompositions).

**Permutation- and sub-representation characters (Ch5 §5.11 `stdRep`, #5263).** To
get a permutation rep's character: `permRep g = ((g⁻¹).permMatrix ℂ).toLin'`
(`Matrix.permMatrix_mulVec` + `Matrix.toLin'_apply`), then
`LinearMap.trace … = Matrix.trace … = (Function.fixedPoints g⁻¹).ncard` via
`Matrix.trace_toLin'_eq` + `Matrix.trace_permutation` — i.e. `χ(g) = #fix(g)`. For
the character of an *invariant subspace* (e.g. the standard rep as the sum-zero
`stdSub`), split the trace over an internal direct sum with its complement:
`LinearMap.trace_eq_sum_trace_restrict` (needs `DirectSum.IsInternal N`, obtained for
a two-element family via `DirectSum.isInternal_submodule_iff_isCompl` +
`Submodule.isCompl_iff_disjoint`); the complementary trivial line contributes trace
`1`, giving `χ_std(g) = #fix(g) − 1`. The `Subrepresentation.toRepresentation g`
restriction is *defeq* to the `(permRep g).restrict _` term the trace lemma produces
(proof-irrelevant `MapsTo`), so the sub-character matches by `change`. For simplicity
via `FDRep.simple_iff_char_is_norm_one`, convert `∑_g χ(g)χ(g⁻¹)` to an **integer**
`Finset` sum (`fixCard g := (univ.filter (g · = ·)).card`, `push_cast`) and close with
`decide` — `Set.ncard`/`Function.fixedPoints` are noncomputable, so always bridge to a
`Finset.filter` cardinality first. Pitfall: `linarith` does **not** work over `ℂ`
(unordered) — use `eq_sub_iff_add_eq` / `linear_combination`. Lemmas in
`Chapter5/Discussion5_11_examples.lean`: `permRep_eq_toLin'`, `trace_permRep`,
`stdRep_character`, `stdRep_simple`.

Two lessons that cost ~hours of deliberation here:

1. **For FDRep iso-from-invariants, do the induction *inside* `FDRep`, not via
   `asModule` decomposition.** The categorical route reuses Mathlib's
   `finrank_hom_simple_simple` and `scalar_product_char_eq_finrank_equivariant`
   *directly* with zero `Representation.asModule`/`Rep ≌ ModuleCat k[G]` bridges
   (which the module route needs in both directions, plus a module-level Schur).
   Pattern: strong induction on `finrank ℂ (V : Type)`; peel a simple subobject
   `S₀ ↪ V` via `CategoryTheory.exists_simple_subobject` (needs
   `IsArtinianObject V`); it splits (`IsSplitMono` from `Injective S₀`, the
   `FinGroupCharZero` instance, retraction `Injective.factorThru (𝟙 S₀) ι`); then
   `splitSummand` gives `V ≅ S₀ ⊞ Q` and you match `Q` by induction. The
   character hypothesis enters only once, via `finrank_hom_eq_of_character_eq`
   (`= finrank ℂ (S ⟶ V)` for every `S`).

2. **`IsArtinianObject (FDRep ℂ G)` is the one genuinely-missing Mathlib fact, and
   it is provable in ~30 lines** (`instIsArtinianObjectFDRep`, now an instance):
   give the subobject lattice the strictly-monotone `ℕ`-length `len s = finrank ℂ
   (s : FDRep ℂ G)`, then `WellFoundedLT` via `Subrelation.wf` + `InvImage.wf …
   wellFounded_lt` + `isArtinianObject_iff_not_strictAnti`. Strict monotonicity:
   `a ≤ b` ⟹ `Subobject.ofLE a b h` mono ⟹ underlying linear map injective ⟹
   `finrank ≤`; equality forces the underlying map bijective ⟹ an underlying
   ModuleCat iso that the forgetful functor **reflects**, giving `a = b`. The
   load-bearing forgetful is `Action.forget (FGModuleCat ℂ) G ⋙ forget₂
   (FGModuleCat ℂ) (ModuleCat ℂ)` — it (a) preserves monos, (b) reflects isos, (c)
   has `Fwd.obj X` underlying-defeq to `(X : Type)`, and (d) gives
   `PreservesBinaryBiproduct` via `preservesBinaryBiproduct_of_preservesBinaryProduct`.
   **Gotcha:** `forget₂ (FDRep ℂ G) (FGModuleCat ℂ)` does *not* auto-resolve
   `Mono`/`ReflectsIsomorphisms`/`Subsingleton`-of-obj the way `Action.forget`
   does — use `Action.forget`, not `forget₂`, as the first leg.

Other reusable sorry-free lemmas now in that file: `finrank_biprod_obj`
(`finrank ℂ (A ⊞ B) = finrank A + finrank B`), `finrank_hom_biprod`
(hom-space additivity, via a hand-built `homBiprodEquiv : (S ⟶ A ⊞ B) ≃ₗ[ℂ] (S ⟶
A) × (S ⟶ B)`), `splitSummand` (split mono ⟹ `Y ≅ X ⊞ cokernel`, via
`isBilimitBinaryBiconeOfIsSplitMonoOfCokernel … |>.isLimit.conePointUniqueUpToIso
(BinaryBiproduct.isLimit …)`), `homCongrRight` (post-compose iso ⟹ hom-space
`≃ₗ`), and `isZero_of_finrank_eq_zero`.

### FDRep Categorical Plumbing

Working with `FDRep` (finite-dimensional representations as a category) requires navigating multiple abstraction layers. This is the #1 blocker in Chapters 4-5.

**The problem:** Book proofs work with concrete linear maps `V →ₗ[k] V`, but Mathlib's FDRep uses categorical morphisms. Converting requires unwrapping 3 levels: `Action.Hom → FGModuleCat.Hom → ModuleCat.Hom → LinearMap`.

**Pattern 1: Reflect through a full+faithful functor**

When you need to prove a property about FDRep objects (like simplicity), prove it for the underlying module and reflect through the functor:

```lean
-- Prove simplicity for the concrete module first
have h : IsSimpleModule k M := Matrix.instIsSimpleModule ...
-- Reflect to FDRep via full+faithful functor
exact Simple.of_full_faithful_preservesMono FDRep.forget₂ h
```

This avoids working inside the categorical abstraction entirely.

**Pattern 2: Use Representation directly instead of FDRep**

For character theory, prefer `Representation k G V` (which gives you `V →ₗ[k] V` directly) over `FDRep k G` (which wraps in a category). Most character computations don't need the categorical structure.

**Pattern 3: Avoid `.hom.hom` chains**

If your proof requires distributing `.hom.hom` over `Finset.sum` or similar, you're fighting the abstraction. Instead:
- Define a helper that states the result directly on `LinearMap`
- Or use `Representation.averageMap` which already works at the LinearMap level

**When stuck on FDRep plumbing after 2 attempts:** Sorry the categorical step with a comment explaining what's needed, and file an issue. Don't spend an entire session on unwrapping functors.

### Bezout Reduction for Integrality

When proving `IsIntegral ℤ (a / b)` where `a` and `b` are related by coprimality:

1. Find `m, n` with `m * b + n * a = 1` via `Nat.Coprime` and `Nat.gcd_eq_gcd_ab`
2. Rewrite `a / b = m * (stuff₁) + n * (stuff₂)` where both summands are provably integral
3. Apply `IsIntegral.add` and `IsIntegral.mul`

This avoids dependent type issues from rewriting `a/b` directly. Used successfully in Theorem 5.4.4.

### Full+Faithful Functor Reflection for Simplicity

To prove an FDRep is simple:
1. Prove `IsSimpleModule k M` for the underlying module (often via `Matrix.instIsSimpleModule`)
2. Lift through `IsSimpleModule.compHom` if needed (for algebra homomorphisms)
3. Reflect to categorical `Simple` via `Simple.of_full_faithful_preservesMono`

This chain: concrete simplicity → algebra hom transfer → functor reflection was the successful pattern for IrreducibleEnumeration (#678).

### Permutation Matrix Arguments

For character identities involving the regular representation (e.g., χ_reg(g) = 0 for g ≠ 1):
- Express the representation matrix as a permutation matrix of left-multiplication
- Show the permutation has no fixed points when g ≠ 1
- Conclude the trace (= character value) is zero

This is more concrete than abstract character theory and avoids FDRep entirely.

### Jacobson Radical for Injectivity

To prove a ring homomorphism from a semisimple ring is injective:
1. Show every element of the kernel acts as zero on all simple modules
2. Therefore the kernel element is in every maximal left ideal
3. The intersection of all maximal left ideals is the Jacobson radical
4. For semisimple rings, Jacobson radical = ⊥
5. Hence kernel = ⊥, so the map is injective

**Lean tip:** May need explicit universe parameters (`.{v}`) to make the Jacobson radical API work with the correct universe level.

### Injectivity of a hom OUT of a simple ring is free (matrix / division algebras)

When you build an explicit `AlgHom`/`RingHom` `f : R →ₐ[k] A` and need it injective,
and the **domain** `R` is a simple ring (`Matrix (Fin n) (Fin n) k` for a field `k`,
or a `DivisionRing` like `Quaternion ℝ`), do **not** hand-prove linear independence of
generators or a kernel-triviality/dimension argument. A nonzero ring hom out of a simple
ring is automatically injective:

```lean
haveI : Nontrivial A := ⟨…⟩            -- e.g. `1 ≠ 0` in the subalgebra; needs the codomain nontrivial
have hinj : Function.Injective f := f.toRingHom.injective   -- RingHom.injective, from [IsSimpleRing R] [Nontrivial A]
```

Instances that fire automatically: `DivisionRing.isSimpleRing` gives `IsSimpleRing k` for
a field, and `RingTheory/SimpleRing/Matrix.lean` gives `IsSimpleRing (Matrix ι ι A)` from
`IsSimpleRing A`. Combined with a surjectivity proof, `AlgEquiv.ofBijective f ⟨hinj, hsurj⟩`
finishes an `≃ₐ`. This is how `realGEndAlgebra_equiv_matrix_of_isRealType`
(`Chapter5/Problem5_1_2.lean`, #6327, `End_ℝ[G]V ≃ₐ[ℝ] Mat₂(ℝ)`) avoids a whole
`1,J,j',Jj'`-independence argument — only the surjectivity (decomposition) half needs work.
The same trick applies to the quaternionic case (target `Quaternion ℝ` is a division ring).

**Companion — the split-quaternion / matrix hom builder (`matrixToSplitQuat`, same file):**
for two elements `J, j'` of any `ℝ`-algebra with `J²=-1`, `j'²=1`, `Jj'=-j'J`, there is a
ready `Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] A` (via `AlgHom.ofLinearMap`, with `map_mul` closed by
the reusable `splitQuat_mul_expand` multiplication-table lemma + the `module` tactic). Reuse
it whenever you meet a 4-dimensional `≅ Mat₂(ℝ)` presentation; the `module` tactic collects
`ℝ`-linear combinations of a fixed set of atoms (here `1, J, j', J*j'`) and discharges the
scalar identities by `ring`, so you never expand a noncommutative product by hand.

## Mathlib Gap Handling

When you discover a Mathlib API gap during formalization, follow this escalation ladder:

### Level 1: Local Workaround (< 30 min)
If you can define the missing concept locally in ≤ 20 lines and it unblocks the proof:
```lean
-- Local definition until Mathlib adds IsIndecomposable
def IsIndecomposable (M : Type*) [AddCommMonoid M] [Module R M] : Prop :=
  ¬IsZero M ∧ ∀ N₁ N₂ : Submodule R M, N₁ ⊓ N₂ = ⊥ → N₁ ⊔ N₂ = ⊤ → N₁ = ⊥ ∨ N₂ = ⊥
```

### Level 2: `sorry` the Gap, File an Issue (> 30 min)
If building the infrastructure would take > 30 min:
1. Use `sorry` for the missing fact
2. Add a comment: `-- Requires [description], not in Mathlib as of v4.28`
3. File a GitHub issue with label `needs-mathlib-api` describing exactly what's needed
4. Move on to the next item

### Level 3: Infrastructure Issue (Blocks Multiple Items)
If the same gap blocks 3+ items (e.g., column orthogonality blocking all character theory):
1. File a detailed GitHub issue documenting:
   - What's missing (with mathematical description)
   - Which items are blocked
   - Whether Mathlib has partial coverage (e.g., row orthogonality exists but not column)
   - Estimated effort to build locally
2. Mark all blocked items as `needs_infrastructure` in items.json
3. Don't attempt to build major infrastructure during a proof session — that's a separate planned issue

### Known Gaps in This Project

| Gap | What Exists | What's Missing | Blocks | Status |
|-----|------------|----------------|--------|--------|
| Column orthogonality | `FDRep.char_orthonormal` (row) | `∑_V χ_V(g) · χ_V(h⁻¹) = \|C_G(g)\| · δ` | Thm 5.4.6, Burnside | Issue #633 |
| Regular rep decomposition | `FDRep`, `Simple` | `k[G] ≅ ⊕ dim(V_i) · V_i` | Thm 5.4.6 | Issue #643 |
| Simple module classification | `Simple` predicate | Every simple FDRep ≅ some columnFDRep | IrrepEnum surjectivity | Issue #655 |
| FDRep ↔ LinearMap plumbing | `.hom` unwrapping | Distributing `.hom.hom` over sums, Schur at LinearMap level | Prop 5.3.2 | Workaround: non-categorical pattern |
| Quiver representations | `Quiver`, `PathAlgebra` | `QuiverRepresentation`, hom, subobjects | Ch6 items | Workaround: concrete constructions |
| Pigeonhole transposition | `Finset` API | Row/column counting for Young tableaux | Lemmas 5.13.1, 5.13.2 | Issues #776, #777 |
| Non-commutative TensorProduct | `TensorProduct` (CommSemiring only) | Balanced tensor product `A ⊗_{eAe} N` for non-commutative rings | BasicAlgebraExistence, MoritaStructural | Manual quotient construction needed |
| Krull-Schmidt theorem | None | Unique decomposition of modules into indecomposables | basic_morita_algEquiv (#1877) | Not in Mathlib, blocks Morita isomorphism |
| ~~Clifford theory~~ | ~~None~~ | ~~Semidirect product orbit method~~ | ~~Theorem5_27_1~~ | **RESOLVED** (Wave 47): All Mackey machine sorries proved via bypass |
| ~~Right-multiplication dominance~~ | ~~Left-mult dominance proved~~ | ~~Right `σ · e_T` ≠ left `σ · e_T`~~ | ~~PolytabloidBasis~~ | **RESOLVED** (Wave 46): Tabloid module approach bypasses entirely |

## Proof Chain Completion Strategy

When multiple sorry'd items exist, **prioritize completing already-started chains** over beginning new proofs. A "chain" is a sequence of items where proving one unblocks the next.

**Why this works:** Chain completion has the highest ROI per agent-hour. Completing one helper lemma can cascade to chapter-level completion. In Wave 4, focusing on the Theorem 4.10.2 chain (2 helper lemmas) completed all of Chapter 4.

**How to identify chains:**
1. Look for items whose dependencies are all sorry-free except one
2. Look for chapters near 100% — one or two proofs may close them out
3. Check if a sorry'd helper lemma is used by 2+ other proofs

**Priority order for proof selection:**
1. Chain-completing proofs (unblock downstream items)
2. Chapter-completing proofs (achieve 100% for a chapter)
3. Infrastructure proofs (unblock 3+ items across chapters)
4. Standalone proofs (no downstream dependents)

### Categorical biproducts / progenerators (Ch9 §9.7, #5146)

Building biproduct-based constructions in an abstract abelian category (the §9.7
progenerator classification `multBiproduct P n = ⨁_{p : Σ i, Fin (n i)} P p.1` in
`Introduction_9_7.lean`) hits three non-obvious instance facts:

- **`Projective (⨁ g)` requires the index family in `Type v` (the hom universe), not an
  arbitrary `Type w`.** Mathlib's instance is `{β : Type v} (g : β → C) [HasBiproduct g]
  [∀ b, Projective (g b)] : Projective (⨁ g)`. A family indexed by `ι : Type w` with `w ≠
  v` fails with `failed to synthesize Projective (⨁ ...)` (cost one build cycle). Fix:
  constrain `ι : Type v` (matching `Category.{v}`). The finite-index Fintype `Σ i, Fin
  (n i)` then also lands in `Type v`. `HasBiproduct` itself is fine over any `Finite`
  index, so only the `Projective`/`Injective` biproduct instances force `Type v`.
- **`HasFiniteBiproducts C` is NOT a global instance from `Abelian C`** (it is a
  *theorem* `Abelian.hasFiniteBiproducts`, kept non-instance for performance). A `def`
  whose statement mentions `⨁` needs it; add `[HasFiniteBiproducts C]` as an explicit
  binder (callers in an abelian category discharge it with `haveI :=
  Abelian.hasFiniteBiproducts`). The biproduct of a `Finite`-indexed family then resolves
  via `hasBiproductsOfShape_finite`.
- **The "indecomposable object" predicate is `CategoryTheory.Indecomposable`** (defined in
  `Shapes/BinaryBiproducts.lean` *after* `end Limits`, so it lives in `CategoryTheory`,
  not `CategoryTheory.Limits`): `¬IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z`,
  needs `[HasBinaryBiproducts C]`.

Two reusable helpers landed for the Krull–Schmidt *existence* link
(`KrullSchmidt/Existence.lean`, #5206 — uniqueness/§9.7-assembly links will want both):
- **`clength` is an iso-invariant** (`clength_eq_of_iso (e : X ≅ Y)`): `Subobject.mapIsoToOrderIso
  e : Subobject X ≃o Subobject Y`, then `Order.height_orderIso` + `OrderIso.map_top` give equal
  heights. Needed so a well-founded induction measure descends across a splitting iso `X ≅ Y ⊞ Z`.
- **No Mathlib lemma for a biproduct over a `Sum`** (`⨁ (Sum.elim f₁ f₂) ≅ (⨁ f₁) ⊞ (⨁ f₂)`).
  Build it explicitly: `hom := biprod.desc (biproduct.desc fun a => ι _ (.inl a)) (biproduct.desc
  fun b => ι _ (.inr b))`, `inv := biproduct.desc fun k => match k with | .inl a => ι f₁ a ≫
  biprod.inl | .inr b => ι f₂ b ≫ biprod.inr`; both `*_id` close by `biprod.hom_ext'`/
  `biproduct.hom_ext'` + `rintro (a|b) <;> simp`. This is the step that concatenates two finite
  indecomposable families over `κ₁ ⊕ κ₂`.
- **`∃ (_ : Fintype κ) (f : κ → C), … ⨁ f` elaborates** because a `Sum`/`Exists`-bound hypothesis
  of class type *is* a local instance, so `⨁ f` resolves inside the binder. But after `refine ⟨κ,
  fin, f, …⟩` the supplied `fin` is **not** auto-registered for the remaining goals — add `haveI :=
  fin` before referencing `⨁ f`/`biproduct.ι f` again, or `HasBiproduct f` fails.

**Krull–Schmidt *uniqueness* (`krullSchmidt_unique`, #5480) — the two heavy categorical
ingredients are ALREADY in Mathlib; don't hand-bash them.** Before reimplementing biproduct
matrix algebra, reach for:
- **Cancellation = `CategoryTheory.Biprod.isoElim`** (`Preadditive/Biproducts.lean`): given
  `f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` with `[IsIso (biprod.inl ≫ f.hom ≫ biprod.fst)]` (top-left entry
  invertible), it produces `X₂ ≅ Y₂` by Gaussian elimination. This is the whole Schur-complement
  cancellation — the feared ~hundreds-of-lines step. Sibling `Biprod.gaussian`/`unipotentUpper`/
  `unipotentLower`/`isoElim'` for the component-level forms.
- **Peeling one summand off `⨁ g`** uses `biproduct.toSubtype g p` / `biproduct.fromSubtype g p`
  (`Limits/Shapes/Biproducts.lean`), with `Subtype.restrict p g = fun i' => g i'.val` as the
  sub-biproduct index. They are *definitionally* `biproduct.lift (fun _ => π …)` /
  `biproduct.desc (fun j => ι _ j.val)`, and crucially `biproduct.fromSubtype_toSubtype = 𝟙`,
  `toSubtype_fromSubtype = biproduct.map …`, plus simp lemmas `ι_toSubtype`/`fromSubtype_π`
  (dite on `p j`). So `peelIso g i₀ : ⨁ g ≅ g i₀ ⊞ ⨁ Subtype.restrict (· ≠ i₀) g` is built with
  `hom := biprod.lift (π g i₀) (toSubtype g (·≠i₀))`, `inv := biprod.desc (ι g i₀) (fromSubtype …)`
  and the iso laws close by `biprod.hom_ext'`+`biprod.hom_ext`+`simp` (the inr-snd corner is
  exactly `fromSubtype_toSubtype`). State the codomain with `Subtype.restrict` (NOT
  `fun i' => g i'.val`) so that corner's `𝟙` matches syntactically. Pin the top-left entry of the
  peeled iso to a chosen component with `@[reassoc (attr := simp)]` `peelIso_inv_inl`/`hom_fst`.
- To find the matching `m₀` whose component is *iso* (not just "some iso exists"), reuse the local
  endomorphism-ring sum argument of the exchange lemma but conclude `IsIso (s ≫ biproduct.π Z m₀)`
  (the `⟨⟨rr, hαrr, he1⟩⟩` already proves the component is the iso). Assemble the reindexing
  `κ ≃ μ` from `Equiv.sumCompl (· = k₀)`/`sumCongr`; `sumCompl_symm_apply_of_pos/neg` need the
  predicate pinned (`(p := (· = k))`) — bare `rfl` leaves `p` as `Eq ?m` and the rewrite fails.

Useful idioms from the same file: realise `⨁ P` as a *retract* of `multBiproduct P n`
(when each `n_i ≥ 1`) via a diagonal index inclusion `e i = ⟨i, 0⟩`, `s := biproduct.desc
(fun i => biproduct.ι _ (e i))`, `r := biproduct.lift (fun i => biproduct.π _ (e i))`;
`s ≫ r = 𝟙` by `biproduct.hom_ext'` + `biproduct.hom_ext` then `biproduct.ι_desc`/`lift_π`
and `biproduct.ι_π` (the `dif_pos rfl`/`dif_neg (fun h => …(he h))` dite split, with
`he : Function.Injective e`). A split epi `r` (`IsSplitEpi r := ⟨⟨s, key⟩⟩`) pulls back
generating epis; `biproduct.mapIso (fun _ => e)` transports a progenerator across an iso
of each summand. Krull–Schmidt (the *forward* "every progenerator is `⊕ n_i P_i`"
direction) is not in Mathlib — isolate it as one documented `sorry` (#5153).

**`finrank` of a biproduct Hom space (Ch9 §9.7 Cartan formula, #5144).** To prove
`dim_k Hom(⊕ⱼ fⱼ, ⊕ₖ gₖ) = ∑ⱼ ∑ₖ dim_k Hom(fⱼ, gₖ)` (e.g. `dim B_𝐧 = ∑ c_{ij} n_i n_j`
for `B_𝐧 = (End (multBiproduct P n))ᵐᵒᵖ`): Mathlib's `biproduct.matrixEquiv`
(`(⨁ f ⟶ ⨁ g) ≃ ∀ j k, f j ⟶ g k`) exists but is a bare `Equiv` **restricted to
`Type 0` index types** (`{J K : Type} [Finite J] [Finite K]`), so it does *not* apply when
the biproduct index is `Σ i, Fin (n i) : Type v` (multBiproduct's index lives in the hom
universe). Build your own *universe-polymorphic* `≃ₗ[k]` instead: `toFun m j l :=
biproduct.ι f j ≫ m ≫ biproduct.π g l` (k-linear by `Linear.comp_smul`/`Linear.smul_comp`
and `Preadditive.comp_add`/`add_comp`), `invFun M := biproduct.desc fun j => biproduct.lift
fun l => M j l`; `left_inv`/`right_inv` close by `biproduct.hom_ext'` + `biproduct.hom_ext`
then `simp` (`biproduct.ι_desc`/`lift_π`). Then `e.finrank_eq` + `Module.finrank_pi_fintype k`
(applied twice for the nested Pi) gives additivity — `Module.Free` is free over a field
(`Module.Free.of_divisionRing`, a global instance), `Module.Finite` from the §9.6
Hom-finiteness (`IsFiniteAbelianCategoryOverField.finiteDimensional_hom`). For the
opposite-algebra step `dim (End P)ᵐᵒᵖ = dim End P` use `MulOpposite.opLinearEquiv k`. Collapse
the double sum over `Σ i, Fin (n i)` with `← Finset.univ_sigma_univ` + `Finset.sum_sigma`
(the inner `Fin (n i)` sum is constant, so `Finset.sum_const` + `Fintype.card_fin` gives the
`n_i` weight). **Gotcha:** when re-declaring section instance binders in a `def`/`theorem` to
make one argument explicit (e.g. `def cartanEntry (k) … {C} [Category C] [Linear k C]`),
include `[Preadditive C]` *before* `[Linear k C]` — `Linear` takes `Preadditive` as a
parameter (does not extend it), so omitting it gives `failed to synthesize Preadditive C`.

### Morita/any equivalence of module categories preserves finite generation (Ch9 #5738)

To restrict `E : ModuleCat R ≌ ModuleCat S` to `FGModuleCat R ≌ FGModuleCat S` (the
`FGModuleCat`-vs-`ModuleCat` reconciliation of Corollary 9.7.3(i) — the split-conjunct
gap): feed `CategoryTheory.Equivalence.congrFullSubcategory E hobj` with
`hobj : (ModuleCat.isFG S).inverseImage E.functor = ModuleCat.isFG R` (`FGModuleCat R =
(ModuleCat.isFG R).FullSubcategory`), i.e. `∀ M, Module.Finite S (E.functor.obj M) ↔
Module.Finite R M` (prove by `funext M; exact propext (…)`; also supply the instance
`(ModuleCat.isFG S).IsClosedUnderIsomorphisms` via `of_iso e hX := Module.Finite.equiv
e.toLinearEquiv`). Sorry-free, axiom-clean in `Infrastructure/MoritaFGRestriction.lean`.
The whole thing is ~250 lines; the crux and its reusable pieces:
- **This is NOT formal from additivity** — it needs the regular module being a compact
  generator. The clean proof: `E.inverse.obj (of S S)` is f.g. over `R` (`inverse_regular_finite`);
  (F1) `Module.Finite S (E.functor.obj (of R R))` = `inverse_regular_finite E.symm`; then
  `functor_finite_of_finite` transports f.g. and `finite_functor_iff` gives the iff (reflection via
  the unit iso `E.unitIso.app M`). No k-linearity, no Noetherian, no compactness API needed.
- **Core `inverse_regular_finite`:** the regular module is a separator (`isSeparator_regular`,
  proved directly à la `ModuleCat.isSeparator` via `LinearMap.toSpanSingleton`), so
  `G := E.functor.obj (of R R)` is a separator of `ModuleCat S` (`IsSeparator.of_equivalence`).
  Show `⨆ (φ : G ⟶ of S S), range φ.hom = ⊤` by feeding the separator `f = ofHom N.mkQ`, `g = 0`
  (every `h : G ⟶ of S S` has `h ≫ mkQ = 0` since `range ⊆ N`), forcing `mkQ = 0` hence `N = ⊤`.
  Then `1 ∈ N`; extract a finite family via `Submodule.mem_iSup_iff_exists_finset` +
  `mem_iSup_finset_iff_exists_sum`, build `Φ := biproduct.desc g : ⨁ⁿ G ⟶ of S S` (epi, since
  `1 ∈ range Φ.hom`), and `E.inverse.map Φ` is a surjection onto `E.inverse (of S S)` from an
  `E.inverse`-image of a finite biproduct (f.g. by `finite_functor_biproduct`).
- **`finite_functor_biproduct`** (`F` additive, `f : Fin n → ModuleCat R`, each `F.obj (f i)`
  f.g. ⟹ `F.obj (⨁ f)` f.g.): `(F.mapBiproduct f).trans (ModuleCat.biproductIsoPi _)` then
  `Module.Finite.pi` + `Module.Finite.equiv e.symm.toLinearEquiv`.
- **Gotchas:** `IsSeparator`, `Functor.PreservesEpimorphisms`,
  `Functor.preservesEpimorphisms_of_adjunction` need the `Functor.` prefix even under
  `open CategoryTheory` (get epi-preservation from `E.toAdjunction`/`E.symm.toAdjunction`).
  `ModuleCat.biproductIsoPi` requires the index in **`Type 0`** (`{J : Type}`), so a `Finset`
  index (`{x // x ∈ t} : Type u`) must be reindexed to `Fin t.card` via `t.equivFin` (reindex sums
  with `Fintype.sum_equiv e.symm _ _ (fun i => rfl)` + `Finset.sum_coe_sort`). `E.symm.inverse =
  E.functor` is defeq — close with `exact`, not `simpa [Equivalence.symm_inverse]` (the simp lemma
  does not fire). `Submodule.eq_top_iff'` (not bare `eq_top_iff'`).

## Quiver Representation Patterns

Chapter 6 quiver representations use concrete finite-dimensional constructions rather than abstract quiver theory. This approach was discovered in Wave 4 (Examples 6.2.2-6.2.4) after three waves of zero progress with abstract approaches.

### Concrete Construction Pattern

For quiver representations with vertices V₁, ..., Vₙ and arrows between them:

```lean
-- Represent each vertex space as Fin d →₀ k (or Fin d → k)
-- Represent each arrow as a concrete LinearMap between vertex spaces
structure D₄Rep (k : Type*) [Field k] where
  V  : Type* -- central vertex
  V₁ : Type* -- arm vertices
  V₂ : Type*
  V₃ : Type*
  A₁ : V₁ →ₗ[k] V  -- arrow maps
  A₂ : V₂ →ₗ[k] V
  A₃ : V₃ →ₗ[k] V
```

**Key insight:** Work with explicit `LinearMap`s between finite-dimensional spaces, not abstract `QuiverRepresentation` types. Mathlib's quiver infrastructure is insufficient for the proofs we need, but the concrete linear algebra API is rich.

**Helper-lemma signatures: state them over explicit block spaces, not `(rep…).obj v`.** A flag/collapse helper whose statement mentions `x ∈ W ⟨k⟩` with `W : ∀ v, Submodule F ((someRep_kQ …).obj v)` can fail `Membership` synthesis *in the signature* (`failed to synthesize Membership (Fin (a*(m+1)) → F) (Submodule F ((rep …).obj ⟨k, ?m⟩))`): the `obj`/`*Dim` match does not reduce, especially under the `attribute [-instance] …toQuiver` pragma the rep lemmas carry. The robust fix for any helper that is *pure linear algebra over the per-vertex spaces* (e.g. `t125_prefix_sub`/`t125_suffix_sub`, `FieldGenericT125.lean` Section 3b) is to take **explicit block submodules** `W0 : Submodule F (Fin (6*(m+1)) → F)`, `W2 : Submodule F (Fin (4*(m+1)) → F)`, … instead of the rep family `W`. It elaborates cleanly, drops the `attribute`/`IsAlgClosed`/`Q`/`hOrient` clutter, and is reusable across shapes (one prefix-flag lemma serves Ẽ₆/Ẽ₇/T(1,2,5)). Call sites pass `W ⟨0⟩`, `W ⟨2⟩`, …; the dims match `*Dim` by defeq *at the call site*, where the expected type is known so `isDefEq` (default transparency) unfolds `obj`/`*Dim`. (In-proof `have`s and some standalone lemmas do tolerate `obj v` membership, so it is not a hard rule — but reach for explicit block spaces the moment a signature throws a Membership-synthesis error.) Also place such helpers *after* the rep `def` only if they reference it; pure block lemmas can sit anywhere after the block-map defs.

### Indecomposability via Kernel Splitting

For classifying indecomposable representations:
1. Check kernels of arrow maps — if `ker Aᵢ ≠ ⊥`, split off the kernel as a direct summand
2. This reduces to the "all injective" case, which is the hard subspace-configuration problem
3. For the injective case, use `Submodule.IsCompl` and `Module.finrank` to classify

### Indecomposability via Nilpotent Complement (Extended Dynkin Types)

For extended Dynkin quiver representations (Ẽ₆, Ẽ₇, T(1,2,5), D̃_n), the established
proof pattern uses `nilpotent_invariant_compl_trivial` (InfiniteTypeConstructions.lean:158).
Reference implementation: `cycleRep_isIndecomposable` (lines 304-372).

**Pattern:**
1. **Nontriviality:** Show representation is nonzero at some vertex
2. **Setup:** Assume complementary invariant submodules W₁, W₂ at all vertices
3. **Propagate to leaf:** Use map injectivity to show W₁(leaf) ≤ W₁(leaf') for
   leaves connected through arm chains. Establish W(leaf₁) = W(leaf₂) or similar.
4. **Nilpotent invariance:** Show W₁(leaf) and W₂(leaf) are both invariant under
   the nilpotent shift `nilpotentShiftLin m` at a leaf vertex. This is the HARD step —
   the nilpotent enters through one arm but must be shown to propagate to the leaf.
5. **Apply lemma:** `nilpotent_invariant_compl_trivial` gives W₁(leaf) = ⊥ or W₂(leaf) = ⊥
6. **Propagate back:** From W(leaf) = ⊥, propagate via injectivity of all edge maps
   to show W(v) = ⊥ for all vertices.

**Critical:** The m ≥ 1 hypothesis is essential. For m = 0, the nilpotent is zero and
the representations are genuinely decomposable (issues #2342, #2374, #2376).

### Refuting indecomposability (counterexample-first)

Single-twist D̃/Ẽ `_kQ` indecomposability theorems are frequently **false** for
reversed-leaf orientations (issue #4566: `starRep_kQ_isIndecomposable` is false
when the diagonal leaf is reversed). Before grinding a `sorry` on
`<X>Rep_kQ_isIndecomposable`, try to refute it at `m = 1`. Worked, sorry-free
example: `starRep_kQ_reversedLeaf3_decomposable` (`FieldGenericStar.lean`).

`IsIndecomposable` is `(∃ v, Nontrivial) ∧ (∀ W₁ W₂, inv₁ → inv₂ → compl → all-⊥)`.
To refute, exhibit explicit invariant complementary `W₁ W₂` with neither
everywhere `⊥`: `rintro ⟨-, hno⟩; have := hno W₁ W₂ ?inv1 ?inv2 ?compl` then derive
a contradiction from a vertex where both are nonzero. Reusable helpers
`isCompl_coordLines_two` / `isCompl_coordPlanes_four` (in `FieldGenericStar.lean`)
give `IsCompl` for coordinate-axis spans.

Three non-obvious Lean gotchas when building such counterexamples:

1. **Ambient `Quiver` instance interference.** Outside the
   `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
   CategoryTheory.ReflQuiver.toQuiver in` guard, a spurious category `Quiver`
   instance is active. `rw` with `ReversedAtVertexHom_eq_*` lemmas then fails to
   match — pass the base quiver explicitly:
   `rw [@Etingof.ReversedAtVertexHom_eq_eq (Fin n) _ starQuiver i a b ha hb]`.
   Also `reversedAtVertex` is noncomputable: use `@[reducible] noncomputable def`,
   not `abbrev`, for a named oriented quiver.
2. **`simp only [matchDef]` does not reduce a `match` on `Fin` literals.**
   `starRepMap_kQ F 1 1 0` will not rewrite to `starEmbed1_F F 1` via simp.
   Convert the map by a defeq `show starEmbed1_F F 1 x ∈ _` (do this *before*
   destructuring `x`, to avoid cross-type `HAdd` errors in the `show`).
3. **Arrow case order + empty Homs.** After `fin_cases a <;> fin_cases b`, arrow
   goals appear in `(a,b)` lexicographic order (e.g. `(0,3)` before `(1,0)`). In a
   `reversedAtVertex` orientation every non-arrow pair has empty Hom, closable
   uniformly by `first | exact absurd e.down (by decide) | skip`.

### Dimension Vector Pattern

Track dimension vectors `(dim V, dim V₁, ..., dim Vₙ)` as the primary classification tool. Indecomposability constraints on dimension vectors are often finite and enumerable.

## Combinatorial Counting Arguments

Pigeonhole-style counting arguments (e.g., "by counting, some row must have two elements mapping to the same column") are a persistent difficulty in Lean formalization. The mathematical intuition is simple but the formal proof requires careful API navigation.

### Recommended Approach

1. **State the counting lemma separately** — don't inline pigeonhole arguments in larger proofs
2. **Use `Finset.exists_ne_map_eq_of_card_lt`** (pigeonhole principle) when available
3. **For partition-based counting:** Express the constraint as a `Finpartition` or use `Finset.sum_card_fiberwise_eq_card` to relate partition sizes to totals
4. **For injection-based arguments:** Use `Fintype.card_lt_of_injective_of_not_surjective` or `Function.Injective.card_le`

### When Stuck on Combinatorial Proofs

After 2 serious attempts:
1. Sorry the combinatorial core with a precise comment describing the counting argument
2. Complete the algebraic frame around it (this is valuable and independently reviewable)
3. File an issue with status `attention_needed`

This "algebraic frame + combinatorial sorry" pattern was successfully used in Lemmas 5.13.1 and 5.13.2 (Young symmetrizer proofs).

## Non-Categorical Workaround Pattern

When a proof requires FDRep categorical machinery that's blocked by `.hom` plumbing, try reformulating the argument to avoid categories entirely.

**Example (Theorem 5.4.4, PR #721):** Instead of using the categorical Schur's lemma via FDRep:
- Used eigenvalues of central elements acting on simple modules
- Proved `character_div_dim_isIntegral` via direct algebraic argument
- Completely bypassed FDRep plumbing

**When to try this:**
- The proof fundamentally needs a fact about linear maps (traces, eigenvalues, determinants)
- The categorical formulation adds structure you don't actually need
- You've spent > 30 min fighting `.hom` unwrapping

**How to find the workaround:**
1. Write out the mathematical argument in terms of linear maps and matrices
2. Check if Mathlib has the needed lemmas at the `LinearMap` / `Matrix` level
3. If yes, build the proof there — it's usually cleaner than the categorical version

## Helper Lemma Extraction Pattern

When a proof is too complex for a single session, extract helper lemmas into separate declarations. This pattern was critical for Theorem 4.10.2 (block polynomial irreducibility) and the Young symmetrizer chain (5.13.1-5.13.4).

### When to Extract

- A proof attempt reveals a non-trivial subgoal that's independently meaningful
- The same fact is needed by 2+ proofs (e.g., `pigeonhole_transposition` used by both 5.13.1 and 5.13.2)
- A proof exceeds ~50 lines of tactics — break it up

### How to Extract

1. **State the helper as a separate `lemma`** in the same file, above the main theorem
2. **Use `sorry` for the helper's proof** — this lets you test the main theorem's proof structure immediately
3. **Commit the main theorem using the sorry'd helper** — this is valuable progress even if the helper is hard
4. **Work on the helper separately**

```lean
-- Helper extracted from complex proof
lemma helper_fact (n : ℕ) (h : n > 0) : some_property n := sorry

-- Main theorem uses the helper
theorem main_result : conclusion := by
  have h := helper_fact n hn
  exact ...
```

### Multi-PR Proof Chains

Complex theorems may span multiple PRs. This is expected and desirable:
- **PR 1**: State theorem + helpers, prove the algebraic frame, sorry the hard core
- **PR 2**: Prove helper lemmas
- **PR 3**: Close the last sorry

Each PR must compile. Label intermediate PRs with the item ID so reviewers can track the chain.

## Chapter Closure Tactics

When a chapter is within 1-3 items of 100% completion, prioritize closing it. Chapter closures have outsized value:
- Psychological milestone for the project
- Eliminates an entire category from the work queue
- Proves the formalization approach works end-to-end for that chapter

**Identifying closure candidates:**
1. Check `items.json` for chapters with high completion percentage
2. Look for items where all dependencies are sorry-free
3. Prefer the easiest remaining item to close the chapter first

**Evidence:** Ch3 closed via Jordan-Hölder (#831), Ch4 via block polynomial (#812). Both were chain-completion efforts that required focused multi-session work but had outsized impact on project morale and metrics.

## Endgame Priorities (Wave 47, 2026-04-11)

With **9 sorries** across 6 files, the project is at 99.5% items sorry-free (581/583). All definition-level sorries are resolved. The remaining sorries are the hardest in the project — each requires either deep combinatorial argument, new infrastructure, or architectural rethink.

**Trajectory:** 66 sorries (wave 28, Mar 22) → 13 (wave 43, Apr 4) → 15 (wave 45, Apr 6, architectural decomposition) → **9 (wave 47, Apr 11)**. Wave 47 broke through a two-wave plateau at 15 sorries via coefficient lemma proofs, Problem6_9_1 closure, and TabloidModule cleanup.

**Recently completed (Waves 44-47, PRs #2209–#2221):**
- Young symmetrizer coefficients: 4 lemmas proved (#2221) — PolytabloidBasis 8→4 sorries
- Problem6_9_1: compatible_product_decomp fully proved (#2215) — 0 sorry
- TabloidModule: unused polytabloid_syt_dominance removed (#2209) — 0 sorry
- CI fixed (#2213, #2214) — main branch CI breakage resolved

**Remaining sorry map (9 sorries, 6 files):**

```
Cluster A: Polytabloid Basis (Ch5, 5 sorries)
├── PolytabloidBasis (4): polytabloid_mem_spechtModule, polytabloid_linearIndependent,
│                         column_standard_in_span', perm_mul_youngSymmetrizer_mem_span_polytabloids
└── FormalCharacterIso (1): iso_of_glWeightSpace_finrank_eq (GL_N complete reducibility)

Cluster B: Gabriel Theorem Chain (Ch6, 2 sorries)
├── Corollary6_8_4 (1): mixed vertex case [PR #2208 in CI]
└── Problem6_1_5_theorem (1): positive definiteness → finite type [blocked on #2143 chain]

Cluster C: Morita Theory (Ch9, 1 sorry)
└── MoritaStructural (1): head_isomorphism [blocked on PR #2175]

Isolated:
└── Theorem2_1_2 (1): Gabriel's theorem classification [depends on Clusters A + B]
```

**6 PRs in CI (all re-triggered, infrastructure failures not code):**
- #2175 (Module.Finite) → unblocks #2174 (head_isomorphism)
- #2191 (D̃_n infinite type) → unblocks #2187 (non-ADE case analysis)
- #2198 (Ẽ_6 construction) → unblocks #2199 (indecomposability)
- #2200, #2219 → contribute to #2143 chain → unblocks Problem6_1_5_theorem
- #2208 → Corollary6_8_4 mixed vertex case (direct sorry reduction)

**Priority tiers:**

**Tier 1 — Highest ROI (waiting on CI):**
- **Wait for 6 PRs to pass CI.** When they merge, 3 blocked issues unblock (#2174, #2187, #2199). This is the highest-leverage action requiring zero code work.
- **PR #2208** — If CI passes, Corollary6_8_4 sorry may be directly resolved.

**Tier 2 — Tractable now:**
- **polytabloid_linearIndependent** (#2212, unclaimed) — Transfer from tabloid-module proof. Well-scoped, difficulty 4. Would reduce PolytabloidBasis to 3 sorries.
- **head_isomorphism** (#2174) — Becomes actionable when #2175 merges.

**Tier 3 — Hard but well-scoped:**
- **polytabloid straightening** (#2217) — column_standard_in_span' + perm_mul_youngSymmetrizer_mem_span. Difficulty 7. Tabloid-level Garnir + dominance induction.
- **polytabloid_mem_spechtModule** — T-dependent definition complicates membership proof. No open issue yet.

**Tier 4 — Deep infrastructure:**
- **FormalCharacterIso** — GL_N complete reducibility. Needs Schur-Weyl infrastructure. Lowest priority.
- **Theorem2_1_2** — Gabriel's theorem. Depends on both Clusters A and B.

**Key endgame insights:**
1. **All definitions are constructed.** Every remaining sorry is a pure proof obligation.
2. **Decomposition is the dominant value-creation pattern.** Converting a monolithic sorry into structured sub-goals (with 60-80% proved) is often the best outcome for a single session.
3. **Approach cycling is expensive.** After 3 genuinely different approaches, document and move on.
4. **Pessimism about infrastructure requirements can be wrong.** The Mackey machine was estimated to need ~500 lines of Clifford theory. It was proved without Clifford theory at all — direct constructions sufficed. Always try the simplest approach first.
5. **Element-level proofs bridge SMul instance diamonds.** When two Module instances are propositionally but not definitionally equal, work at element level with `ext`, then use `conv_lhs => rw [...]` to bridge the instances.
6. **Multi-PR iteration is normal for hard items.** Complex theorems routinely require 2-4 PRs: restructure → build infrastructure → prove.
7. **CI infrastructure failures are the #1 time sink.** Runner OOM/disconnects cause CANCELLED status. The fix is always re-triggering — never waste time diagnosing "code issues" when the build log shows runner communication lost.
8. **The tabloid module approach works.** TabloidModule.lean's dominance order + unitriangularity has been the successful path for polytabloid independence. Garnir straightening at the group algebra level was a dead end (tautology). Use tabloid-level reasoning for all remaining polytabloid sorries.

## Non-Commutative Ring Workarounds

Mathlib's `TensorProduct` requires `CommSemiring`. Multiple agents across 4+ sessions have hit this wall when working on Morita theory and corner rings. Here are the known workarounds:

### The Problem
`TensorProduct R M N` requires `[CommSemiring R]`. But Morita equivalence needs `A ⊗_{eAe} N` where `eAe` is a corner ring (non-commutative in general).

### Workaround 1: Balanced Tensor Product as Quotient
Construct `A ⊗_{eAe} N` as a quotient of `A ⊗_k N` by the balanced submodule:
```lean
-- The balanced submodule: generated by (a · r) ⊗ n - a ⊗ (r · n) for r ∈ eAe
def balancedSubmodule : Submodule k (TensorProduct k A N) := ...
def BalancedTensorProduct := (TensorProduct k A N) ⧸ balancedSubmodule
```
This construction appeared in BasicAlgebraExistence and was used in 3+ sessions.

### Workaround 2: Use `isUnit_of_sub_one_mem_jacobson_bot` alternatives
The `isUnit_of_sub_one_mem_jacobson_bot` API requires `CommRing`. For non-commutative rings, use `IsNilpotent.isUnit_one_sub` instead (only requires `Ring`).

**Jacobson-membership on `MonoidAlgebra k G` (noncommutative).** The clean unit
characterization `Ideal.mem_jacobson_bot : x ∈ jacobson ⊥ ↔ ∀ y, IsUnit (x*y+1)` lives in
the `CommRing` section — it fails instance synthesis on a group algebra. The
**`Ring`-general** form is `Ideal.mem_jacobson_iff {x} : x ∈ jacobson I ↔ ∀ y, ∃ z, z*y*x + z - 1 ∈ I`;
take `I = ⊥` and `Ideal.mem_bot` reduces each goal to `z*y*x + z - 1 = 0`. For a central
nilpotent `x` (e.g. the group sum `P = ∑_g g` when `|G| = 0` in `k`): `y*x` is nilpotent
(`Commute.isNilpotent_mul_left`), so `1 + y*x` is a unit (`IsNilpotent.isUnit_one_add`);
pick `z = ↑u⁻¹` for that unit `u`. Bridge to `⊥` with the **`Ring`-general**
`Ideal.jacobson_bot : jacobson ⊥ = Ring.jacobson R` and
`IsSemisimpleRing.jacobson_eq_bot : Ring.jacobson R = ⊥`. This proves "nonzero central
nilpotent ⇒ `¬ IsSemisimpleRing k[G]`" — the algebraic core of Exercise 4.2.3
(`Etingof.not_isSemisimpleRing_of_card_eq_zero`). NB: many
`Ideal.jacobson`/`mem_jacobson_bot`/`IsReduced` lemmas are `CommRing`-only; confirm the
lemma's section before reaching for it on `MonoidAlgebra k G`.

### Workaround 3: Avoid `linarith`/`linear_combination` over non-commutative rings
These tactics need `CommSemiring`. Use manual algebra (`calc` blocks with `mul_assoc`, `mul_comm` where applicable, or `ring_nf` after establishing commutativity of specific elements).

### Status
Non-commutative tensor products remain the hardest infrastructure gap. No clean resolution exists in Mathlib. The balanced quotient approach works but requires ~100 lines of boilerplate per use site.

## Type-Level If/Else Diamond Issue

When defining a structure whose `obj` field branches on vertex equality (e.g., `if v = i then T₁ else T₂`), Lean's typeclass system creates a diamond:

**The problem:** Structure fields like `[instAddCommMonoid : ∀ v, AddCommMonoid (obj v)]` and `[instModule : ∀ v, Module k (obj v)]` are filled sequentially. After `instAddCommMonoid` is filled (e.g., via `split; infer_instance`), it becomes opaque. The `instModule` field's type depends on `instAddCommMonoid`, but the opaque term prevents `split` from decomposing the `if` inside it.

**What doesn't work:**
- `split <;> infer_instance` for the Module field (can't split opaque match)
- `by_cases h; subst h; simp; infer_instance` (simp can't reduce `if` with opaque Decidable)
- `convert inferInstance` (leaves unsolvable HEq goals between opaque and concrete instances)
- Helper instances `iteAddCommMonoid`/`iteModule` (Module's AddCommMonoid dependency doesn't match)
- Sharing a `let`-bound `Decidable` value (doesn't reduce at type level)

**Current workaround:** Sorry the `instModule` field and the `mapLinear` field. The `obj` field (the mathematical content) and `instAddCommMonoid` can be concrete. This is acceptable per issue guidelines ("specific field obligations sorry'd").

**Potential solutions for a future refactor:**
1. Change `QuiverRepresentation` to not use `[...]` instance fields — use explicit bundled instances instead
2. Use `@[reducible]` on the obj definition so the `if` reduces
3. Define the representation for each case separately and combine using `Sigma`/`Sum`

This affects: Definition 6.6.3 (F⁺ᵢ), Definition 6.6.4 (F⁻ᵢ), and any future definition that branches `obj` on a proposition.

## Fintype Instance Mismatch in Sum Comparisons

When comparing two `Finset.sum` expressions over `Finset.univ` for a subtype (e.g., `↑(RowSubgroup n la)`), the `Fintype` instances may differ if one comes from a local `haveI : DecidablePred ... := Classical.decPred _` at the proof level and the other from a `haveI` inside the original definition. This makes the two `Finset.univ` propositionally but not definitionally equal.

**Symptoms:** `rfl` fails, `Finset.sum_congr rfl` fails, `congr 1; funext` fails, all with messages about `Finset.univ` not being definitionally equal.

**Fix:** Use `convert rfl using N` (typically `N = 2`) to handle the instance mismatch automatically via `Subsingleton (Fintype α)`. Then close remaining subgoals (e.g., summand equality) with `ext` + `simp`/`rw`.

```lean
-- Two sums that are "the same" but have different Fintype instances
-- ∑ x ∈ @Finset.univ _ inst₁, f x = ∑ x ∈ @Finset.univ _ inst₂, g x
convert rfl using 2
-- Remaining goal: f = g (pointwise)
ext ⟨σ, hσ⟩
simp [...]
```

**Preferred fix:** Add `open scoped Classical` at the section level (before any definitions that use `haveI : DecidablePred ... := Classical.decPred _`). This ensures all `DecidablePred` instances come from the same source, avoiding the mismatch entirely. This is better than `convert rfl` because it prevents the issue rather than patching it.

**Alternative:** Prove equality via `Finsupp.ext` (coefficient-wise) to sidestep sum comparison entirely.

## MonoidAlgebra Coefficient Computation

`MonoidAlgebra k G` is a `def` (not `abbrev`) alias for `G →₀ k`. This means `simp_rw` and `simp only` cannot see through it to apply `Finsupp` lemmas like `Finsupp.smul_apply`, `Finsupp.single_apply`, etc.

**Symptom:** `simp_rw [Finsupp.smul_apply, Finsupp.single_apply]` makes no progress on a goal involving `MonoidAlgebra` terms.

**Fix:** Use `Finset.sum_congr rfl` with `change` to coerce the term to `Finsupp` before `rw`:
```lean
rw [Finset.sum_congr rfl (fun i _ => show _ = _ from by
  change (c • (Finsupp.single g (1 : k))) σ = _
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply])]
```

**Key lemmas for MonoidAlgebra coefficients:**
- `MonoidAlgebra.single_mul_apply`: `(single g r * x) h = r * x (g⁻¹ * h)` (for groups)
- `MonoidAlgebra.mul_single_apply`: `(x * single g r) h = x (h * g⁻¹) * r` (for groups)
- `Finsupp.finset_sum_apply`: `(∑ i ∈ S, f i) a = ∑ i ∈ S, f i a`
- `Finsupp.smul_apply`: `(b • v) a = b • v a` (definitional, but needs coercion via `change`)

## Mathlib API Naming Gotchas

These naming mismatches have bitten multiple agents across waves 44-47. Check this list before reaching for `exact?` or `apply?`.

| What You Want | Wrong Name | Right Name | Notes |
|--------------|-----------|------------|-------|
| `a^(n+1) = a^n * a` | `pow_succ` | `pow_succ'` | `pow_succ` is `a^(n+1) = a * a^n` (reversed) |
| `u⁻¹ * u = 1` (Units) | `Units.inv_mul` | `Units.val_inv_mul` | `inv_mul` is for `Group`, not `Units` |
| Span induction | `Submodule.span_induction` (old sig) | `Submodule.span_induction` (new sig) | Signature changed: now uses a dependent predicate `{p : ∀ x, x ∈ span R s → Prop}` instead of `{p : M → Prop}`. Check the current type with `#check @Submodule.span_induction`. |
| `Finsupp.sum_apply` | `Finsupp.sum_apply` | `Finsupp.finset_sum_apply` | For `(∑ i ∈ S, f i) a = ∑ i ∈ S, f i a`. Needs explicit `(N := C)` type annotation when used with `MonoidAlgebra`. |
| DecidableEq for Finset.image | (missing) | Add `haveI : DecidableEq α := Classical.decEq _` | `Finset.image` requires `DecidableEq` on the codomain. Easy to forget. |
| `DFinsupp.smul_apply` | `DFinsupp.smul_apply` | Use `Finsupp.smul_apply` via `change` | `DFinsupp` and `Finsupp` have different APIs. MonoidAlgebra is `Finsupp`-based. |
| `p` splits over its field | `p.Splits (RingHom.id k)` | `p.Splits` | **`Polynomial.Splits` is now single-argument** (`Splits (f : k[X]) : Prop`, splits over `k` itself). The ring-hom form is deprecated; `p.Splits (RingHom.id k)` fails to elaborate ("Function expected at p.Splits"). Use `IsAlgClosed.splits p : p.Splits` (not `splits_codomain`), and `Splits.eq_prod_roots_of_monic (hf : p.Splits) hm : p = (p.roots.map (X - C ·)).prod`. (#5235) |
| Integer induction case names | `\| hz \| hp \| hn` | `\| zero \| succ \| pred` | `induction n using Int.induction_on with` alternatives are `zero` (`P 0`), `succ k ih` (`P k → P (k+1)`, `k : ℕ` cast to `ℤ`), `pred k ih` (`P (-k) → P (-k-1)`). Using `hz/hp/hn` gives "Invalid alternative name". (#5365) |
| Inner product | `inner x y` | `inner ℂ x y` | **`inner` now takes the scalar field as an explicit first arg** (`inner (𝕜) : E → E → 𝕜`). Bare `inner x y` fails with "argument … expected to have type `Type`". Either write `inner ℂ x y`, or `open scoped InnerProductSpace` and use `⟪x, y⟫_ℂ`. (#6311) |
| `(f * g) x`, `(1) x` for `Module.End` | `LinearMap.mul_apply` / `one_apply` | `Module.End.mul_apply` / `Module.End.one_apply` | `LinearMap.mul_apply` does not exist. |

**Combining `↑(q ^ a)` Units.val / zpow scalars in a `↑(q^a) * (↑(q^b) * c) = …` goal (quantum-torus / twisted-cocycle arithmetic, #5365).** Don't guess `rw` order on a mix of `Units.val`, `•`/`*`, and `zpow`. Normalize *both* sides to a single `↑(q ^ E) * c` first with `simp only [smul_eq_mul, ← mul_assoc, ← Units.val_mul]` (collapses each side's two unit factors into one `↑(q^a * q^b)`), then discharge with pre-proved unit-level equalities `have : (q ^ a * q ^ b : kˣ) = q ^ E := by rw [← zpow_add]; congr 1; ring` and `rw [hL, hR]`. `ring` does **not** equate `q ^ A` with `q ^ B` for equal `ℤ`-exponents — you must combine to one `zpow` (`← zpow_add`) and prove the exponent equality separately.

**General principle:** When a `rw`/`simp` doesn't fire on a MonoidAlgebra goal, the issue is usually that MonoidAlgebra is a `def` (not `abbrev`), so `simp` can't see through to `Finsupp` lemmas. Use `change` to coerce to `Finsupp` form first.

**When unsure about a lemma name:** Use `#check` or `exact?` on a small test goal. Don't guess and iterate — the 30 seconds spent checking saves 10 minutes of mysterious failures.

## Trace-Based Proof Pattern

When a proof involves showing a group algebra element is nonzero, or bounding the dimension of a representation, try using traces of left-multiplication operators.

**Pattern (Young symmetrizer squared nonzero, Theorem 5.12.2):**
1. Prove `trace_lmul_monoidAlgebra`: `Tr(L_a) = |G| · a(1)` for any group algebra element `a`
2. Show that if `c² = 0` then `L_c` is nilpotent, hence `Tr(L_c) = 0`
3. But `Tr(L_c) = |G| · c(id) = n! ≠ 0` in characteristic zero
4. Contradiction

**When to use:** Whenever the mathematical argument involves "evaluate at the identity element" or "take the trace of left multiplication". This is cleaner than trying to work with the group algebra directly because traces are computed via `LinearMap.trace`.

**Key Mathlib APIs:** `LinearMap.trace`, `MonoidAlgebra.lmul`, `IsNilpotent`, `LinearMap.trace_eq_zero_of_isNilpotent`

## Reynolds Operator / Symmetrization Pattern

For proofs involving invariant subspaces under group actions (e.g., `V^G ≅ Sym^n V`):

1. Construct the symmetrization/averaging map: `symSum(x) = Σ_{σ ∈ G} σ · x`
2. Show `symSum` factors through the quotient (e.g., `SymmetricPower.mk`) via `AddCon.addConGen_le`
3. For injectivity on invariants: `symSum(x) = |G| · x` when `x` is invariant, so if images agree, `|G| · (a - b) = 0`, giving `a = b` by `CharZero`
4. For surjectivity: use `(|G|)⁻¹ · symSum(lift(y))` as preimage

**Key insight:** The Reynolds operator `R = (1/|G|) Σ_σ σ` is an idempotent projection onto invariants. Most invariant-subspace identifications reduce to showing `R` factors through the target construction.

## `decide` for Concrete Finite Computations

For theorems about specific small finite structures (e.g., D₄ quiver with 4 vertices):

```lean
-- Example 6.8.5: concrete D₄ reflection functor computations
example : reflectionResult₁ = expected₁ := by decide
```

**When to use:** The statement involves only `Fin n` for small `n`, concrete matrices, or specific permutations. If `decide` doesn't terminate in reasonable time (< 30s), write a **manual proof** — do NOT fall back to `native_decide` (FORBIDDEN, see below).

## FORBIDDEN: `native_decide`

**`native_decide` is banned in this project.** It compiles the goal to native code and trusts the Lean compiler + runtime — it is *outside the kernel*, so every `native_decide` is an unverified assertion (it has had soundness bugs and is exactly the kind of trust hole a formalization exists to avoid). Do not use it, and do not silence its linter with `set_option linter.style.nativeDecide false`. If a finite computation is too slow for honest `decide`, that means: (a) prove it with real lemmas (`Finset.sum`/`Fintype` API, explicit rewrites), or (b) restructure so the heavy part is a one-off `have` over a `decide`-able sub-statement. "It's just a finite check" is not a license — a slow `decide` is a prompt to think, not to escape the kernel.

**Probe `decide` feasibility in an isolated scratch file, never via a full-module `lake build`.** Kernel `decide` has no internal timeout, so an infeasible one hangs (it ate 15 min / 3.3 GB before I killed it). Put the single goal in `/tmp/Scratch.lean` (import the needed modules + `set_option maxRecDepth …`/`maxHeartbeats …`) and run `gtimeout 300 lake env lean /tmp/Scratch.lean` (on machines without `gtimeout` — e.g. the pod runners — use plain `timeout 300 …`; `gtimeout: command not found` is the tell) — a self-contained scratch with explicit `set_option`s does not need the lakefile's `[leanOptions]`, so `lake env lean` is fine here. The OS timeout bounds the experiment and tells you the true cost before you touch the real file. Rough scaling from #5425's E-type root counts (filter over `Fin n → Fin B`): ~4k candidates ≈ 50 s with `maxRecDepth 10000` + `maxHeartbeats 4000000`; ~78k candidates → ~7 GB and climbing (impractical); millions → OOM materializing `univ`. When honest `decide` won't scale, decompose with a real-math plan (e.g. a branch-decomposition convolution that factors the count into small per-component `decide`s) rather than keeping `native_decide`.

**Honest `decide` DOES scale to `S₄`-sized character work — measure before assuming you need a class-function decomposition (#5429).** A predecessor assumed the Example 4.8.1 group-order / conjugacy-class / orthonormality computations *required* `native_decide`. In fact, over `Equiv.Perm (Fin 4)` (24 elements) honest `decide` evaluates in ~10s: norm-one character sums `∑ g : Perm (Fin 4), ((fixCard g : ℤ) - 1)^2 = 24` (for `FDRep.simple_iff_char_is_norm_one`), `Fintype.card (ConjClasses (Perm (Fin 4))) = 5` (needs `set_option maxRecDepth 4000` — the default overflows the quotient enumeration), and a `MulAction` spec like `∀ g a, invol (conjIdx g a) = g * invol a * g⁻¹` (the conjugation `S₄→S₃` action, 24×3 cases, `set_option maxHeartbeats 4000000`). `Fintype.card (Perm (Fin n)) = n!` should go through `Fintype.card_perm`/`Fintype.card_fin` then `decide`, NOT a 24-element enumeration. Calibration: **honest `decide` also scales to the `A₅` regime — measured in #5430, the predicted "too slow, use a class-function decomposition" was wrong, do NOT build a class-sum helper preemptively.** Over `alternatingGroup (Fin 5)` (60 elements, `Fin 5` perms), with `set_option maxRecDepth 8000` + `maxHeartbeats 4000000`, the following all `decide` in well under a minute each: norm-one sums `∑ g : G, ((fixCardM g : ℤ) − 1)^2 = 60` for `ℂ⁴`/`ℂ⁵` simplicity; `Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5` (~34 s); and a 60×6 conjugation-action spec `carrier (conjIdx5 g i) = (carrier i).image (conjPerm g)` (~41 s). For `|A₅|` use `card_alternatingGroup` (`= card α !/2`) + `decide`, NOT a 60-element enumeration. **Always probe the exact goal in a scratch file first** (`gtimeout 300 lake env lean /tmp/Scratch.lean`) — measuring took minutes and saved building an unnecessary conjugacy-class-sum helper. The reusable genuine-rep infrastructure — a generic deleted-permutation representation of any `MulAction G α` (`permRepM`/`stdSubM`/`stdRepM`) with character `#fix(g) − 1` and norm-one simplicity — lives in `Chapter4/Example4_8_1.lean` (namespace `Etingof.Example4_8_1.S4`); it is reused for `A₅`'s `ℂ⁴` (deleted natural action on `Fin 5`) and `ℂ⁵` (deleted permutation rep on the six Sylow-5 subgroups, via a conjugation `MulAction G (Fin 6)` whose closure is certified by honest `decide`) in namespace `Etingof.Example4_8_1.A5` (#5430). For elements of `alternatingGroup (Fin 5)`, build them as `⟨perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩` — bare `⟨perm, by decide⟩` fails to synthesize `Decidable (perm ∈ G)`. When stacking `set_option maxRecDepth … in` with `maxHeartbeats … in`, put `maxHeartbeats` **last** so the linter's required explanatory comment sits immediately under it.

**"An order-`n` subgroup `H ≤ A₅` is conjugate to a concrete point stabilizer" — use the orbit/fixed-point route, not the Sylow-normalizer route, when `H` is a point stabilizer of `natHom` (Problem 5.11.1 (d), `exists_conj_H12`, PR #6671).** The issue sketched a Sylow-`2`-normalizer argument for order-`12` `H`; a much shorter route proves `H` **fixes a point** of the natural `5`-point action and hence equals `stabSub natHom i`, then conjugates `stab i` to `stab 0 = A4std` by transitivity (`natHom_trans`, one `fin_cases i <;> fin_cases j <;> decide`) + `Subgroup.eq_of_le_of_card_ge` (with `card_stab_i : Nat.card (stabSub natHom i) = 12`). The fixed-point lemma `H12_fixes_point`: put `MulAction A5 (Fin 5)` via `MulAction.compHom (Fin 5) natHom` (subgroups act automatically, `Subgroup.instMulAction`), take the `H`-orbit `O` of `0`, get `|O| ∣ |H|` from the **existing** `Problem4_12_5.orbit_fiber_card` fiber-count + `Finset.card_eq_sum_card_fiberwise` (all fibers = stabilizer size), then case on `|O|` (`∣ 12`, `1 ≤ |O| ≤ 5`): size `5` impossible; size `4` ⟹ singleton complement is fixed; size `2`/`3` ⟹ all of `H` sits in the setwise stabilizer of `O`, which has **≤ 6 even permutations** — the parity obstruction to a `2 + 3` split, a `decide` `∀ O : Finset (Fin 5), 2 ≤ O.card → O.card ≤ 3 → (univ.filter (fun g : A5 => ∀ i ∈ O, natHom g i ∈ O)).card ≤ 6` (`revert`-then-`decide`, ~30 s). Burnside/character sums **cannot** separate `1+4` from `2+3` (both give the same orbit count and the same `∑ᵢ |Stab_H(i)|`) — the evenness `decide` is essential. **`decide` gotcha:** for `(univ.filter (· ∈ stabSub natHom i)).card = 12`, do NOT hand `decide` a local `haveI : DecidablePred (· ∈ stabSub natHom i) := decidable_of_iff …` instance — the kernel can't reduce it and errors "Expected type must not contain free variables". Instead `Finset.filter_congr` to the concrete predicate `fun a => natHom a i = i` (whose `Fin.decEq` decidability the kernel *can* reduce), then `fin_cases i <;> decide`.

## FORBIDDEN: `sorry` for theorems the book states without proof — use `proof_wanted`

**When the book explicitly cites a deep theorem without proving it (Ado's theorem in Remark 2.9.3, and any "this is a famous result, we omit the proof" remark), do NOT formalize it as a `theorem … := by sorry`.** A `sorry` is a broken proof obligation that pollutes the project's sorry count and reads as "we tried and failed", when the truth is "the book deliberately does not prove this". State it instead with one of:

- **`proof_wanted name (binders) : statement`** (from `import Batteries.Util.ProofWanted`) — elaborates and typechecks the statement as a genuine `Prop`, but introduces **no proof term, no `sorry`, no axiom**. This is the idiomatic Mathlib marker for "this theorem is wanted but unproved". Put any extra hypothesis in a `variable` so the `proof_wanted` signature is just `name : statement` (its pre-colon binder handling is fussier than `theorem`'s). Mirror `Chapter2/Remark2_9_3.lean` (Ado): pre-declare `k`/`L` + instances via `variable`, then `proof_wanted ado [FiniteDimensional k L] : ∃ V …`.
- **`def StatementOfFooTheorem : Prop := …`** — names the proposition as data (no proof needed, no `sorry`), when you want a referenceable handle rather than a wanted-marker.

The distinction matters: **proof sorries** (claims the book *proves*, which we discharge) must go to zero; **citation sorries must never exist at all** — they become `proof_wanted`. A reviewer scanning for `sorry` should find only genuine in-progress proof work, never a deliberately-unproved book citation. The forbidden-`native_decide` discipline and this one share a root: the sorry/axiom/native_decide count is the project's trust ledger, and nothing should sit in it that isn't a real, in-progress obligation.

## FORBIDDEN: vacuous "certificate" statements for tables / classifications

A **character table, multiplicity table, or classification claim is NOT formalized by encoding the numbers as a hand-typed matrix and proving an orthonormality / count / `∑dᵢ²=|G|` certificate.** Those properties are *necessary but radically insufficient*: a continuum of orthonormal bases of class functions satisfy them, so the certificate never pins down *the* character table, and it never connects the numbers to any representation. Such a "fix" is vacuous (the real claim survives only in the docstring). The required bar: **exhibit the actual representations and prove each table row is the character (trace) of its representation** — or state a decidable `IsCharacterTable G T` predicate that is provably unique up to row reordering and prove the table satisfies it (which forces the representation connection). If the genuine construction is hard (e.g. A₅'s 3-dim icosahedral reps over ℚ(√5)), land a real partial and decompose the rest — never ship the orthonormality certificate as the whole theorem.

**Caution:** `decide` only works when all types are decidable and small. It won't work for general `n` or abstract algebraic structures.

## Strong Induction on Coordinate Sums (Root System Pattern)

For proofs involving positive roots or dimension vectors where the claim is "every element can be reached from simple elements via reflections":

1. **Induct on `∑ dᵢ`** (the coordinate sum of the dimension vector)
2. **Base case:** When `∑ dᵢ` is minimal (e.g., a simple root `eᵢ`), the claim holds trivially
3. **Inductive step:** Find a "good vertex" `k₀` where `(B·d)_{k₀} > 0` (positive entry in Cartan matrix product)
4. **Key lemma:** If no good vertex exists, construct `d' = d - e_{k₀}` and show `B(d', d') ≤ 0`, contradicting positive-definiteness

**Implementation pattern:** Build helper lemmas systematically:
- Cartan matrix symmetry (`cartanMatrix_symm`)
- Simple reflection properties (`simpleReflection_preserves_bilinearForm`)
- `exists_good_vertex` (by contradiction using positive-definiteness)
- Main induction with `Nat.strongRecOn` or `WellFoundedRelation`

This pattern proved Theorem 6.8.1 (reaching simple roots via reflections) — the linchpin of Gabriel's theorem. It's applicable to any root-system argument requiring structural induction.

## Rank-Nullity for Non-Commutative Hom Spaces

For proofs about `Hom_A(P, M)` where `A` is a non-commutative algebra:

1. Use `LinearMap.finrank_range_add_finrank_ker` for Hom additivity on short exact sequences
2. Use `Submodule.comapSubtypeEquivOfLe` for relating submodule preimages
3. For composition factor simplicity: `covBy_iff_quot_is_simple`

**Key workaround:** `LinearEquiv.congrRight` requires commutativity. For non-commutative algebras, manually construct k-linear equivalences on Hom spaces instead. This was the successful pattern for Proposition 9.2.3.

## Partial Proof Publication Pattern

When a theorem has conceptually independent parts (e.g., symmetric power + exterior power):

1. **Split the theorem** into independent sub-declarations
2. **Prove the tractable part** completely (sorry-free)
3. **Sorry the hard part** with an explicit issue filed
4. **Submit as `proof_partial`** in items.json

This is strictly better than leaving the entire theorem sorry'd. Downstream work that only needs the proved part can proceed. Example: Example 5.19.3 symmetric power was proved completely while the exterior power part (blocked by the ExteriorAlgebra/PiTensorProduct coercion gap) was sorry'd with an issue.

## Verify Statement Correctness Before Proving (Convention Check)

**Before attempting any proof involving Mathlib conventions** (signs, orderings, normalizations), verify the statement is correct with a small concrete example.

**The problem:** Convention mismatches between the book and Mathlib silently make statements unprovable. These appear as "unprovable goals" rather than type errors. Agents spend entire sessions trying proof strategies before discovering the statement itself is wrong.

**Known convention differences:**
- `vandermondePoly` uses `∏_{i<j}(x_j - x_i)` (Mathlib) vs the book's `∏_{i<j}(x_i - x_j)`, differing by `Equiv.Perm.sign(Fin.revPerm)`
- Alternating sum conventions may differ in sign
- Partition/Young diagram indexing conventions may differ

**Verification pattern:**
```lean
-- Before proving: test with n=2 or smallest non-trivial case
#eval do
  let lhs := <your_LHS_computed_for_n_2>
  let rhs := <your_RHS_computed_for_n_2>
  return (lhs == rhs)  -- should be true!
```

If the concrete example fails, the statement has a convention bug. Fix the statement before attempting the proof. This check takes 5 minutes and can save an entire session.

## Dependent Type Rewriting Patterns

Direct `rw` on dependent types is a recurring friction point. These patterns work:

### `omega` cannot do variable-modulus `% n` or unfold `if-then-else`
`omega` supports `%`/`/` only by **numeral** divisors. For a *variable* modulus
`n` (e.g. cyclic adjacency `(i+1) % n = j`, `Fin n` rotation), `omega` treats
`(m+1) % n` as an opaque atom and fails even on trivial facts like
`(i+1) % n = i+1` given `i+1 < n`. It also does **not** case-split on
`if c then _ else _`. Recipe (used for `cycle_cartan_*`, #6745,
`Chapter6/Problem6_1_3_continued_E7_E8.lean`): first rewrite every mod into an
`if`-branch form with an explicit helper —
`have hmod : ∀ m, m < n → (m+1) % n = if m+1 = n then 0 else m+1 := fun m hm => by
  by_cases h : m+1 = n; · rw [if_pos h, h]; exact Nat.mod_self n;
  · rw [if_neg h]; exact Nat.mod_eq_of_lt (by omega)` — then `rw [hmod …]` at each
occurrence and finish with `split_ifs <;> omega` (now pure linear + `ite`
eliminated). To count the two cyclic neighbours as a `Finset`, show
`univ.filter P = {⟨(i+1)%n, _⟩, ⟨if i=0 then n-1 else i-1, _⟩}` (predecessor
written *without* an outer mod so its `.val` stays a raw natural), then
`Finset.sum_boole` + `Finset.card_pair hab`. Reuse `Fin.val_mk` in the `simp only`
so `(⟨x,h⟩ : Fin n).val` reduces to `x` before `omega`/`split_ifs`. A nonzero
kernel vector ⇒ `det = 0` is `Matrix.exists_mulVec_eq_zero_iff` (holds over any
`[CommRing] [IsDomain]`, so ℤ directly — no need to map through ℚ).

### Pattern 1: `congrArg` with `Fin.ext` (for Fin-indexed access)
When you need to rewrite a `Fin` value inside a dependent context (e.g., cycle access, list indexing):
```lean
-- Instead of: rw [some_fin_equality]  -- fails with "motive is not type correct"
-- Use:
exact congrArg cycle.get (Fin.ext (by omega))
```

### Pattern 2: `suffices ∀ s, ...` (generalize-then-instantiate)
When rewriting a term `b` that appears in dependent types like `hab : a ≤ b`:
```lean
suffices ∀ s, statement_about s by
  convert this ?_ <;> exact the_specific_equality
intro s
-- Now prove for arbitrary s (no dependent type issues)
```

### Pattern 3: `show`/`change` for `Fin.cons` goals
`Fin.cons_zero`/`Fin.cons_succ` don't match literal `(0, _)`/`(n+1, _)` syntactically:
```lean
-- Instead of relying on simp to reduce Fin.cons:
show <explicit_expected_form>  -- or use `change`
-- Then apply the appropriate lemma
```

### Pattern 4: `convert rfl using N` for Fintype instance mismatches
When two `Finset.univ` expressions use different `Fintype` instances:
```lean
convert rfl using 2  -- handles instance mismatch via Subsingleton
```

### Pattern 5: `unfold + match` for `Decidable.casesOn` composition
When two functions both use `match inst a b, inst c d with ...` on the same decidable instances,
their composition should reduce to identity. Standard tactics (`rw`, `simp`, `▸`, `split`, `cases`)
ALL fail because the scrutinee is an opaque application. Use `match` in the proof itself:
```lean
-- After unfolding both function definitions:
unfold foo bar
simp only [id]  -- remove @id wrappers from `change`/`unfold` in tactic definitions
revert e  -- revert the variable so its type enters the goal
exact match inst a b, inst c d with
| .isFalse h, _ => fun _ => (absurd rfl h).elim  -- vacuous
| .isTrue _, .isTrue h => fun _ => (absurd h hne).elim  -- vacuous
| .isTrue _, .isFalse _ => fun _ => rfl  -- both matches reduce to id
```
**Limitation**: This works for arrow-level (homogeneous) equalities but NOT for Sigma-level
equalities where the Sigma TYPE itself contains `Decidable.casesOn`. For Sigma-level round-trips,
define both conversion directions in the SAME file as the type definition, or use `Equiv.ofBijective`.

**Stop after 3 failed approaches** — if `match`-based proof doesn't work, the issue is structural
(needs upstream definition changes), not tactical.

### Pattern 6: freeze a derived term before `rw [h]` substitutes its variable

When a hypothesis `h : f = <expr>` is rewritten into a goal that *also* mentions
`f` **inside** a derived term like `detExp f`, `Nat.find _`, `degree f`, etc.,
`rw [h]` replaces **every** `f` — including the one inside `detExp f` — corrupting
the exponent/index (symptom: the goal sprouts `detExp (<expr>)` where you wanted a
plain `detExp f`). Freeze the derived term as an opaque local first:
```lean
obtain ⟨s, hsdef⟩ : ∃ s, detExp f = s := ⟨_, rfl⟩
rw [hsdef] at h ⊢   -- now the goal/h talk about `s`, not `detExp f`
rw [h]              -- safe: `s` contains no `f`
-- recover at the end:  rw [hsdef] at <the ≤ fact>; omega
```
Cleaner than `nth_rewrite`/`conv` targeting because it removes the `f`-dependence
everywhere at once. Use it whenever the minimal-exponent / `Nat.find` value of the
very element you are rewriting appears in the goal.

## Issue Description Feasibility Check

**Issue descriptions sometimes contain mathematically incorrect proof strategies.** Before committing to a proof approach described in an issue:

1. **Spend 10 minutes verifying feasibility** — check whether the described approach actually works mathematically
2. **Look for hidden complexity** — "the terms vanish individually" may only be true in special cases
3. **Test with small examples** — if the strategy says "by counting" or "by cancellation", check on a 2×2 or 3×3 case

**Evidence:** The alternating Kostka delta identity issue claimed "all non-rev terms vanish individually" — true only for λ=ν, not in general. The hook quotient identity was estimated at difficulty 2/3 but required 3 fundamentally different approaches before being decomposed into 4 sub-issues.

## Statement Correctness: Common Missing Hypotheses

Multiple sessions were wasted proving statements that turned out to be false due to missing hypotheses. Check for these **before** attempting the proof:

| Missing Hypothesis | Symptom | Example |
|-------------------|---------|---------|
| `[IsAlgClosed k]` | Classification/uniqueness fails | Corollary9_7_3 needed algebraic closure for basic algebra existence |
| `[IsBasicAlgebra A]` | Morita equivalence `B ≅ eAe` fails without basic assumption | MoritaStructural was false without this |
| `[CharZero k]` | Averaging/Reynolds operator arguments fail | Theorem5_18_4 `symGroupImage_faithful` needed char 0 |
| `Module.Finite k V` | Finite-dimensionality needed for rank-nullity | MoritaStructural needed explicit finiteness |
| Orientation constraints | Sink/source confusion in quiver proofs | Prop6_6_6 sink vs source cases |

**Pattern:** If a proof fails at a fundamental level (not a tactic issue but a mathematical impossibility) after 1 serious attempt, **suspect a statement bug**. Check the book's hypotheses carefully before trying more proof strategies.

### Universe mismatch: a `Type`-0 witness slot under a `variable (… : Type*)` (#6732)

For an existence / `¬ ∀` statement whose witness you must *build*, one-line-typecheck that the intended witness fits the bound variable's **universe before constructing it** (`have := @H (Fin p → k) …` in a scratch `example`). A statement like `∀ (M : Type) [Module k M] …` with a file-level `variable (k : Type*)` is **unprovable**: the natural witness `Fin p → k : Type u` does not fit the `M : Type` (`Type 0`) slot, and `M : Type*` does not help (it is a *fresh* theorem-level universe independent of `k`'s). Worse, it is *false* for large `k` — with no `Type 0` module of positive dimension the inner `∀` is vacuous, so `¬∀` fails. This is a **planner-level** bug (the statement was written statement-only without a universe check). The fix is to bind field and witness to one universe (`universe u; variable (k : Type u)` + `∀ (M : Type u)`, or `variable (k : Type)` keeping `M : Type`); since it is a signature change, `coordination skip` to `replan` rather than editing the agreed spec. Related: the `ULift` down-cast does **not** exist (`ULift` only lifts up), so you cannot rescue a `Type 0` slot from a `Type u` witness.

## Sorry-to-Helper Extraction Pattern (Endgame)

The dominant value-creation pattern in the endgame. Instead of trying to prove a hard sorry directly, extract it into a well-documented helper lemma.

**When to use:** Any sorry that has resisted 2+ attempts, or any theorem with 3+ sorries where the proof structure is unclear.

**Pattern:**
```lean
-- BEFORE: monolithic sorry
theorem main_result : conclusion := by sorry

-- AFTER: structured proof with isolated helper sorries
private lemma helper_1 : intermediate_fact_1 := sorry
private lemma helper_2 : intermediate_fact_2 := sorry

theorem main_result : conclusion := by
  have h1 := helper_1
  have h2 := helper_2
  exact final_combination h1 h2
```

**Why this is high-value:**
1. The main theorem file now has a complete proof term — only helpers are sorry'd
2. Each helper sorry is independently claimable by a future agent
3. The proof structure documents exactly what's needed, reducing onboarding time
4. Partial progress is visible and committable

**Evidence (waves 25-27):**
- Theorem5_25_2: parts 1, 2, 3a proved; sorry isolated in 6 helpers (#1545, #1562)
- Theorem5_26_1: forward direction decomposed into helper lemmas (#1568, #1569)
- Theorem9_2_1: sorry decomposed into targeted sub-goals (#1567)
- Corollary9_7_3: sorry pushed to infrastructure files (#1560)

**Infrastructure absorption pattern:** When helper lemmas are reusable across theorems, extract them into dedicated infrastructure files (e.g., `Infrastructure/BasicAlgebraExistence.lean`, `Infrastructure/MoritaStructural.lean`). This cleanly separates mathematical infrastructure from theorem proofs.

## SMul Instance Diamond Bridge (Wave 43)

When two `Module` instances on the same type are propositionally but not definitionally equal (common with equivalences, transport, or `restrictScalars`), direct `rfl` and `congr` fail.

**Symptoms:**
- `rfl` fails on what looks like `r • x = r • x`
- Error mentions two different `SMul` or `Module` instances
- `convert` leaves `HEq` goals between instances

**Pattern: Element-level proof with conv rewrite**
```lean
-- Two instances: inst₁ and inst₂ on the same carrier type M
-- You have: h : ∀ (r : R) (m : M), @SMul.smul R M inst₁.toSMul r m = @SMul.smul R M inst₂.toSMul r m
-- Goal: some statement involving inst₂ that you can prove using inst₁

ext m  -- reduce to element level
show @SMul.smul R M inst₂.toSMul r m = ...
conv_lhs => rw [show @SMul.smul R M inst₂.toSMul r m = @SMul.smul R M inst₁.toSMul r m from (h r m).symm]
-- Now the goal uses inst₁, which you can work with
```

**Evidence:** This resolved equivEndAlgEquiv scalar preservation in MoritaStructural (#2082), the hardest sub-task in Cluster E. The key was proving scalar action agreement at element level, then using `conv_lhs => rw [...]` to swap instances within larger expressions.

**When NOT to use:** If the instances are definitionally equal but Lean can't see it, try `change` or `show` first. This pattern is for genuinely different instances that happen to agree propositionally.

## Recognizing Design-Level Blockers vs Proof Difficulty (Wave 43)

**Critical distinction:** A "hard sorry" needs more effort on the same approach. A "design blocker" means the current approach is provably wrong and no amount of effort will fix it.

**How to tell them apart:**

| Signal | Proof Difficulty | Design Blocker |
|--------|-----------------|----------------|
| Counterexample exists | No | Yes — approach fails on specific inputs |
| "All other swaps also fail" | No | Yes — no variant of the approach works |
| Missing lemma | Yes — prove it | Maybe — check if lemma is actually false |
| Tactic timeout | Yes — simplify | No — not relevant |
| 3+ failed attempts, all similar | Yes — try harder | Check for counterexample first |

**The garnir_columnInvCount_decrease lesson (issue #2055):**
The swap-based approach was supposed to decrease `columnInvCount'` for the multi-column case. Analysis showed:
1. For partition (2,1,1), σ with filling [0,3,2,1], the swap preserves the column inversion at (2,3)
2. ALL other possible swaps for this σ INCREASE the count
3. The Garnir element approach gives `0 = 0` (trivial identity) due to row absorption

This is NOT "hard" — it's provably impossible with the current metric. The fix requires changing the induction measure or the entire proof architecture.

**Action when you identify a design blocker:**
1. Document the counterexample in a GitHub issue
2. Propose 2-3 alternative approaches
3. Do NOT attempt further proofs on the broken approach
4. Mark difficulty as 9-10 and add `replan` label

## Bypass Strategies That Worked (Waves 41-43)

Several sorry reductions succeeded by finding simpler approaches than originally estimated:

**1. Mackey machine without Clifford theory (#2047, #2049)**
- Original estimate: ~500 lines of Clifford theory infrastructure
- Actual approach: Direct construction using Frobenius reciprocity + simple subrepresentation existence
- Lesson: Always try the simplest approach first. Infrastructure estimates are often pessimistic.

**2. KLinearMoritaEquivalent bypass (#2073)**
- Original approach: Prove k-linear Morita equivalence (requires tensor product infrastructure)
- Bypass: Skip k-linearity entirely and work with the underlying additive equivalence + separate scalar preservation
- Lesson: If a type class requirement is hard to satisfy, check if you can decompose the proof to avoid needing the full type class.

**3. charValue stability chain (#2068)**
- Original approach: Direct polynomial manipulation
- Actual approach: Induction on the stability chain length, reducing each step to a base case
- Lesson: When polynomial arguments are complex, look for inductive structure.

## MonoidAlgebra.lift Pattern for Group Algebra Homomorphisms

When constructing algebra homomorphisms out of `MonoidAlgebra k G`, use `MonoidAlgebra.lift`:

```lean
-- MonoidAlgebra.lift : (G →* A) → (MonoidAlgebra k G →ₐ[k] A)
-- Given a group hom f : G →* A, lift it to an algebra hom
def myAlgHom : MonoidAlgebra k G →ₐ[k] A :=
  MonoidAlgebra.lift k G A f
```

**Key insight:** Don't try to define algebra homs on `MonoidAlgebra` by working with `Finsupp` directly. `MonoidAlgebra.lift` is the universal property and handles all the algebraic structure automatically.

**Companion pattern:** Use `Finsupp.induction_linear` (cases: zero, add, single) instead of `Finsupp.induction` when proving properties of `MonoidAlgebra` elements. The `induction_linear` variant is easier because it doesn't require tracking a `not_mem_support` hypothesis.

## HEq and eqRec Patterns for Dependent Type Transport

When working with dependent types where direct `rw` fails (common in reflection functor proofs):

### Pattern: `eqRec_heq_self` with field projection motive

When you need to show that transporting a value along a proof and then projecting a field gives the same result:

```lean
-- When goal involves: (Eq.rec x proof).field = x.field
-- Use eqRec_heq_self to get HEq between the transported and original value
have : HEq (Eq.rec x proof) x := eqRec_heq_self proof x
-- Then use field projection congruence
exact heq_of_field_projection this
```

### Pattern: `Subsingleton.elim` for Decidable proof irrelevance

When two `Decidable` instances block definitional equality:

```lean
-- When inst₁ inst₂ : Decidable P appear in the goal and prevent reduction
have : inst₁ = inst₂ := Subsingleton.elim _ _
subst this  -- Now only one instance, and dif_pos/dif_neg can reduce
```

This was critical for the `reversedArrow_ne_ne_twice` proof in Prop6_6_6 (#1561).

If the issue's strategy doesn't work after verification, **update the issue comment** with your findings before trying alternative approaches. This saves the next agent from repeating your investigation.

## Module Instance Agreement Pattern

When two `Module R M` instances exist on the same type (e.g., one from `Representation.asModule` and one from `Submodule.module`), direct `rfl` or `congr` fails because the instances are constructed differently.

**Pattern: Prove pointwise agreement via algebra induction**

```lean
-- Two Module (MonoidAlgebra ℂ G) M instances that act identically
-- inst₁ comes from Representation.asModule, inst₂ from Submodule.module
-- They agree on all elements but are not definitionally equal

-- Step 1: Prove the SMul actions agree on generators
have smul_agree : ∀ (g : G) (m : M), @SMul.smul _ _ inst₁.toSMul (single g 1) m
    = @SMul.smul _ _ inst₂.toSMul (single g 1) m := by
  intro g m; simp [...]

-- Step 2: Lift to all MonoidAlgebra elements via induction
have : inst₁ = inst₂ := by
  ext a m
  induction a using MonoidAlgebra.induction_on with
  | single g r => simp [smul_agree g m, ...]
  | zero => simp
  | add x y hx hy => simp [add_smul, hx, hy]
```

**When to use:** Module instance diamonds from `FDRep`/`Representation.asModule` vs. submodule inheritance. This was critical for the FDRep bridge (#1601) — `spechtModuleFDRep_simple` required proving `IsSimpleModule` transfers across instance-incompatible equivalences.

**Companion:** Use `Finsupp.induction_linear` instead of `MonoidAlgebra.induction_on` when working with Finsupp directly (cases: zero, add, single — no `not_mem_support` hypothesis needed).

## Submodules of `Representation.asModule`: Missing Instances

When working with a simple submodule `m : Submodule (MonoidAlgebra ℂ A) ρ.asModule`, several instances needed for Schur-type arguments must be registered explicitly:

```lean
-- FiniteDimensional over the base field (not auto-derived from the algebra module)
haveI : FiniteDimensional ℂ m :=
  Module.Finite.of_injective (m.subtype.restrictScalars ℂ) Subtype.val_injective

-- IsMulCommutative for MonoidAlgebra (not auto-derived from CommSemiring)
haveI : IsMulCommutative (MonoidAlgebra ℂ A) := ⟨⟨mul_comm⟩⟩

-- Nontrivial (IsSimpleModule.nontrivial is a theorem, not an instance; both args explicit)
haveI : Nontrivial m := IsSimpleModule.nontrivial (MonoidAlgebra ℂ A) ↥m
```

**Connecting FDRep action to MonoidAlgebra action:** `W.ρ ⟨a, 1⟩` and `MonoidAlgebra.of ℂ A a • v` are related through `Representation.asAlgebraHom_of`, which is proved by `simp` (not `rfl`). Use explicit `rw [show ... from rfl, show ... from (asAlgebraHom_of ..).symm]` to bridge the gap.

**When to use:** Any proof that extracts characters from representations of commutative groups (e.g., `exists_character_in_rep` in the Mackey machine, #2036).

## Building `≃ₗ[k[G]]` equivalences between `asModule`s (glue-A/B, #4714/#4715)

When promoting a `k`-linear intertwiner to a `MonoidAlgebra k G`-linear equivalence (the Schur-Weyl Step E "glue" cluster, `Chapter5/PolynomialGLDecomposition.lean`), three instance/unification stalls recur:

1. **Keep both sides genuine `asModule`s; never map straight to a raw `DirectSum` of carriers.** A `k`-linear equiv `e : V ≃ₗ[k] ⨁_β W` has codomain `DirectSum β (fun _ => W)`, and bare `W` carries *no* `k[G]`-module, so the `r • _` on the target in `map_smul'` is a **stuck instance** ("typeclass instance problem is stuck", `(i : ?m) → AddCommMonoid …`). Land in `asModule (Representation.directSum (fun _ => σ))` first (both sides are `asModule`s of representations, so `single_smul` and the `k[G]`-action resolve), then `.trans asModule_directSum_equiv` (glue-A) to reach `DirectSum β (fun _ => asModule σ)`.

2. **Pin `Representation.directSum`'s family `V` explicitly.** `Representation.directSum (fun _ : β => σ)` leaves `V : β → Type` as a higher-order-unification metavar → the same stuck-instance error. Write `Representation.directSum (V := fun _ => W) (fun _ : β => σ)`, and call glue-A as `asModule_directSum_equiv (ι := β) (V := fun _ => W) (fun _ : β => σ)`. Use the *same* `(V := …)` everywhere so the `.trans` typechecks.

3. **`DirectSum.ext`'s family implicit is named `β`.** If your index type is also `β`, supply it: `refine DirectSum.ext (β := fun _ : β => W) fun i => ?_`. Then close componentwise with `tprodSplitEquiv_tmul_apply`, `Representation.directSum_apply`, `DirectSum.lmap_apply`, `DirectSum.smul_apply`, `map_smul`.

The `map_smul'` of the `asModule`-to-`asModule` aux reduces to the carrier-level intertwiner via `rw [single_smul, single_smul, map_smul]; simp only [Representation.asModuleEquiv]; congr 1; exact <intertwiner>` (`asModuleEquiv` is `LinearEquiv.refl`, so it normalizes away with the def-unfold alone — `LinearEquiv.refl_apply` is then an unused simp arg).

**Dot notation on a `Representation`-typed value resolves to `MonoidHom`, not your `Representation.*` lemmas.** `Representation k G V` is definitionally `G →* (V →ₗ[k] V)`, so for `ρ : Representation k G V` the term `ρ.myLemma` elaborates as `MonoidHom.myLemma ρ` and fails with `Invalid field 'myLemma': … does not contain MonoidHom.myLemma`. Even when you *defined* `Representation.myLemma`, you must call it with the **fully-qualified name** `Representation.myLemma ρ …` (not `ρ.myLemma`). This bit me defining `Representation.stableSubmodule` (#4902) — both the definition's own `@[simp]` mem-lemma and every call site needed the explicit `Representation.stableSubmodule ρ …` form.

## Hand-built codiscrete categories: discharge coherence with `rfl`, not `Subsingleton.elim`

When constructing a small category by hand with singleton hom-sets
(`Hom _ _ := PUnit`, `id _ := ⟨⟩`, `comp _ _ := ⟨⟩` — the codiscrete category, useful for
the toy `C₁`/`C₂` of Ch7 §7.4), every law/naturality/coherence equation is an equality of
`PUnit`-valued morphisms and closes by **`rfl`** via structure eta. Do **not** reach for
`Subsingleton.elim _ _`: `Subsingleton (X ⟶ Y)` fails to synthesize because `⟶` does not
reduce to `PUnit` through the `Category` instance at instance-resolution transparency
(cost one build cycle in #5138). So `NatIso.ofComponents (fun _ => …) (fun _ => rfl)` and
`functor_unitIso_comp _ := rfl` work where the `Subsingleton` forms don't. The `Category`
structure's `id_comp`/`comp_id`/`assoc` fields can simply be omitted (their `by aesop_cat`
defaults close trivially). For an equivalence `C₁ ≌ C₂` of two such categories, build it
with `Equivalence.mk`-style fields and per-object isos `Iso.mk ⟨⟩ ⟨⟩` (or `Iso.refl _`
where the objects are defeq). An equivalence then descends to a bijection of iso-classes
of objects via `Quotient.map e.functor.obj (fun _ _ ⟨f⟩ => ⟨e.functor.mapIso f⟩)` with
`left_inv`/`right_inv` from `e.unitIso`/`e.counitIso` and `Quotient.ind`/`Quotient.sound`
(needs `attribute [local instance] CategoryTheory.isIsomorphicSetoid`); compose with
`Equivalence.congrLeft` to get the iso-class bijection on functor categories `C₁ ⥤ D` vs
`C₂ ⥤ D`.

## FDRep Morphism Extensionality Patterns

FDRep morphisms are `Action.Hom` wrapping `FGModuleCat.Hom` wrapping `ModuleCat.Hom` wrapping `LinearMap`. Proving `f = g` for FDRep morphisms requires decomposing through all layers.

**Pattern 1: Standalone lemma proofs** (f ≫ g = 0, f ≫ g = 𝟙, etc.)
```lean
apply Action.Hom.ext
simp only [Action.comp_hom, Action.zero_hom]  -- or Action.id_hom
apply FGModuleCat.hom_ext
ext c
-- Now at LinearMap level. Use `show` to set the expected form.
show <expected_pointwise_equality>
```

Key lemmas: `Action.comp_hom`, `Action.zero_hom`, `Action.id_hom` (from `Mathlib.CategoryTheory.Action.Basic` and `Limits`).

**Pattern 2: Term-mode** (useful in `exact` or `refine`)
```lean
exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => ...)))
```

**Pattern 3: Inside `where` clause `comm` proofs**
The `comm` field is already at FGModuleCat level. Use:
```lean
comm g := by
  apply FGModuleCat.hom_ext; ext ⟨f, hf⟩
  -- For subtypes: apply Subtype.ext; funext g
  show <expected_pointwise_form>
  ...
```

**WARNING**: With high `maxHeartbeats`, Lean may eagerly reduce definitions, causing `show`/`change` to fail because the normal form differs from the expected mathematical form. If `show` fails, try `sorry` and revisit with lower heartbeats or restructured definitions.

**Evidence:** Discovered during principalSeries_decomp (#1647, #1674) — ~15 build iterations were spent fighting FDRep morphism equality before these patterns were identified.

## PID Structure Theorem Bridge Pattern

When using Mathlib's `Module.torsion_by_prime_power_decomposition` to decompose a module over a PID (e.g., ℂ[X]-modules for nilpotent operators), the output is a `DirectSum` of quotient modules `ℂ[X] ⧸ Ideal.span {X^nᵢ}`. Bridging this to concrete vector subspaces requires careful infrastructure.

**Pattern:**

```lean
-- Step 1: Get the PID decomposition
-- The polynomial ring ℂ[X] is a PID (EuclideanDomain → PrincipalIdealRing)
-- T : V →ₗ[ℂ] V nilpotent gives a ℂ[X]-module structure on V via X ↦ T

-- Step 2: Map quotient modules to kernel spaces
-- Key fact: ℂ[X] ⧸ Ideal.span {X^n} ≅ ker(T^n) / ker(T^(n-1)) as ℂ-vector spaces
-- This requires:
private lemma quotient_poly_dim (n : ℕ) :
    Module.finrank ℂ (Polynomial ℂ ⧸ Ideal.span {X ^ n}) = n := sorry

-- Step 3: Track dimensions through the decomposition
-- dim(ker T^k on ℂ[X]/(X^n)) = min(k, n)
-- This determines the Jordan block structure
```

**Key difficulties:**
- The `Module.torsion_by_prime_power_decomposition` API produces existential types (primes, exponents) that need careful handling with `Exists.choose`
- ℂ[X]-module structure on V must be constructed explicitly from the linear map T
- Dimension tracking through quotients requires `Module.finrank` lemmas for polynomial quotient rings

**Evidence:** Problem6_9_1 Case 2b (#1617) — proved 4/5 nilpotent decomp cases using this bridge. The remaining case (2b-ii) is blocked on the kernel dimension computation.

## Type Class Shadowing for Instance Pollution

When a typeclass instance leaks through from an outer scope and interferes with proof goals, use `letI` to shadow it with the correct instance.

**Pattern:**
```lean
-- Problem: `inst✝ : Quiver Q` in context is wrong/opaque, preventing reduction
-- Solution: Shadow it with the concrete instance you want
letI : Quiver Q := concreteQuiverInstance
-- Now tactics see the concrete instance, not the opaque one
```

**When to use:** Proposition6_6_6 hdim proof (#1598) needed this to shadow a `Quiver` instance that was preventing `simp` from reducing. Also useful when `inferInstance` finds the wrong instance in the presence of multiple candidates.

**Caution:** Only shadow when you're sure the shadowed instance agrees with the one you're replacing — otherwise proofs may become inconsistent.

## Inductive Construction on Finite Sets (Finset.strongInduction)

For existence proofs that build a structure incrementally on a finite set (e.g., constructing orderings, colorings, assignments), use `Finset.strongInduction` or equivalent well-founded recursion on `Finset.card`.

**Pattern:**
```lean
-- Construct an admissible ordering of vertices by repeatedly finding local sinks
-- At each step, remove a local sink from the remaining set and recurse

theorem exists_ordering : ∃ (l : List V), l.Nodup ∧ l.toFinset = Finset.univ ∧ P l := by
  -- Use strong induction on |remaining vertices|
  suffices ∀ (S : Finset V), ∃ (l : List V), l.Nodup ∧ l.toFinset = S ∧ P' S l from
    this Finset.univ
  intro S
  induction S using Finset.strongInduction with
  | ind S ih =>
    -- Find an element to remove (e.g., a local sink)
    obtain ⟨v, hv, hprop⟩ := exists_special_element S hS
    -- Recurse on S \ {v}
    obtain ⟨l, hl⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
    exact ⟨v :: l, ...⟩
```

**Evidence:** admissibleOrdering_exists (#1613) — constructed admissible orderings for Dynkin quivers by iteratively removing local sinks, proved via `Finset.strongInduction`. Helper lemmas for sink existence were proved separately using a counting argument on forward/backward edge pairs.

**Key helper pattern:** When the "special element" existence requires a counting/pigeonhole argument, prove it as a separate lemma first. The inductive construction is cleaner when the "find next element" step is a black box.

## Decidable.casesOn Workaround Patterns (Quiver Reflection Functors)

The `reflectionFunctorPlus`/`Minus` definitions use `Decidable.casesOn` via `if h : v = i then ... else ...`. Outside these definitions, Lean cannot reduce through `Decidable.rec`, causing type mismatches. Three workaround variants exist, discovered across PRs #1723, #1735, #1739, #1760:

### Variant A: Revert-Unfold-Rewrite-Intro (most common)

Used 6+ times across Proposition6_6_7 and Proposition6_6_6. The canonical pattern for ne/ne cases:

```lean
-- Fix the decidable instances to their known values
have h_da : DecidableEq Q a' i = .isFalse ha' := by
  cases DecidableEq Q a' i with | isTrue h => exact absurd h ha' | isFalse _ => rfl
have h_db : DecidableEq Q b' i = .isFalse hb' := by
  cases DecidableEq Q b' i with | isTrue h => exact absurd h hb' | isFalse _ => rfl
-- Revert ALL dependent variables
revert hw w e' hsubrep Sb Sa
-- Unfold the definitions containing Decidable.casesOn
unfold reflFunctorMinus_equivAt_ne reflectionFunctorMinus reversedAtVertex ReversedAtVertexHom
simp only []
-- Rewrite with the fixed decidable values
rw [h_da, h_db]
simp only []
-- Re-introduce the variables
intro Sa Sb hsubrep e' w hw
```

### Variant B: Refine-Match (for definitions)

Preferred when defining equivs at specific vertices:

```lean
refine match inst_dec i i with
| .isFalse h => absurd rfl h
| .isTrue _ => ?_
```

Avoids `Eq.mpr` wrappers from `rw` that block downstream computation.

### Variant C: Two-variable fix (for naturality proofs)

When both equality and inequality branches need fixing simultaneously:

```lean
have h_ii : inst_dec i i = .isTrue rfl := by match ...
have h_bi : inst_dec b i = .isFalse hb := by match ...
```

### Key Insight: Avoid `= 0` with Decidable dependency

When `0 : F(rho).obj i` has `Decidable.rec` in its type, prove `f x = mkQ(0)` (where `0 : DirectSum` has no Decidable dependency) then use `map_zero`.

## Instance Construction via `show ... from inferInstance`

When a definition is a type alias (e.g., `AlgIrrepGL` wrapping `SchurModuleSubmodule`), derive instances by showing they follow from the underlying type:

```lean
noncomputable instance AlgIrrepGL.addCommGroup : AddCommGroup (AlgIrrepGL n lam k) :=
  show AddCommGroup (SchurModuleSubmodule k n lam.toNatWeight) from inferInstance
```

Works for `AddCommGroup`, `Module k`, `Module.Finite k`. Discovered in PR #1752. More reliable than `@inferInstance` or manual instance construction.

## Tabloid and Young Tableau Infrastructure Patterns

### Quotient type via Setoid (PR #1754)

```lean
-- TabloidSetoid: two fillings are equivalent if row assignments agree up to permutation
instance : Setoid (Filling n la) where
  r f g := ∃ σ ∈ RowSubgroup n la, σ • f = g
  iseqv := ⟨fun _ => ⟨1, one_mem _, one_smul _ _⟩,
            fun ⟨σ, h, e⟩ => ⟨σ⁻¹, inv_mem h, by rw [← e]; group⟩,
            fun ⟨σ, h1, e1⟩ ⟨τ, h2, e2⟩ => ⟨τ * σ, mul_mem h2 h1, by rw [← e2, ← e1]; group⟩⟩
```

### Fintype for quotient types

```lean
noncomputable instance : Fintype (Tabloid n la) := by
  haveI : DecidableRel (TabloidSetoid n la).r := Classical.decRel _
  unfold Tabloid
  exact Quotient.fintype (TabloidSetoid n la)
```

Must provide `DecidableRel` via `Classical.decRel` before `Quotient.fintype` works.

### False theorem discovery pattern (PRs #1769, #1771)

`RelColumnSubgroup_ne_tabloid` was initially stated with wrong conjugation direction (`σ_T Q_λ σ_T⁻¹` vs `σ_T⁻¹ Q_λ σ_T`). A concrete counterexample for partition (2,2) was found. **Always verify conjugation/action direction with a small example before proving.**

## Orbit-Stabilizer via Burnside's Lemma (PR #1755)

For counting arguments involving group orbits on combinatorial structures:

1. `FiberPerm h ≅ stabilizer h` via `Equiv.subtypeEquiv`
2. Sigma swap `(Σ h, stab h) ≅ (Σ σ, fixedBy σ)` via `Equiv.subtypeProdEquivSigmaSubtype` + `Equiv.prodComm`
3. Burnside: `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
4. Orbit classification: `Equiv.ofBijective` with `Quotient.lift` on fiber sizes

Use `Equiv.ofFiberEquiv` to show structures with the same fiber sizes are in the same orbit — leverages `Fintype.equivOfCardEq` per fiber.

## Simp Lemma Instability Across Lean/Mathlib Versions

`simp` arguments that work locally may stop working after Lean/Mathlib version bumps (PR #1767 was entirely a CI fix for this). Common culprits:
- `LinearEquiv.refl_apply`, `LinearEquiv.coe_toLinearMap` — may be removed from simp set
- `Submodule.coe_mk` — behavior changes across versions

**Mitigation:** After CI failure on `simp` calls, try removing specific simp lemmas rather than adding new ones. Use `simp?` to find the current minimal simp set.

## Known Dead-Ends (Don't Waste Context Windows)

These are proof approaches that multiple agents have attempted and failed. Don't retry them without new Mathlib infrastructure.

### ExteriorAlgebra / PiTensorProduct Coercion Gap

**Problem:** Proving `∧^n V ≅ (V⊗ⁿ)^{Alt}` (the alternating subspace of the tensor power is the exterior power) requires bridging two incompatible Mathlib constructions:
- `exteriorPower n V` is a `Submodule` of `ExteriorAlgebra V` (built on `CliffordAlgebra`)
- The alternating subspace lives in `PiTensorProduct` (or `TensorProduct`)

**What fails:**
- `exteriorPower.linearMap_ext` creates `compAlternatingMap` goals with `↑` coercions that `simp` cannot resolve
- `Fintype.sum_equiv` gets type mismatches when goals are wrapped in `compMultilinearMap`
- `congr 1` strips one coercion layer but leaves incompatible goal forms

**Status:** 3+ agents have attempted this (Example 5.19.3 exterior part). All failed. **Sorry and move on.** This requires new Mathlib bridging infrastructure between `ExteriorAlgebra` and `PiTensorProduct`.

### Dependent Type Issues with `if`-branching `obj` Fields

**Problem:** When a `QuiverRepresentation`-like structure has `obj v := if v = i then T₁ else T₂`, filling `Module` instance fields fails because the `AddCommMonoid` instance becomes opaque after filling.

**Status:** Documented in detail above (Type-Level If/Else Diamond Issue). The workaround is to sorry the `instModule` field. Don't attempt to solve the diamond — it requires a structural refactor.

### Decidable.casesOn Opacity in reflectionFunctorPlus Proofs

**Problem:** `reflectionFunctorPlus` (Definition 6.6.3) defines vertex objects and maps using `Decidable.casesOn` on the `DecidableEq` instance. Any proof that needs to relate the F⁺ maps to the underlying representation maps requires reducing this `casesOn`, but:
- `rw`/`simp` with `inst a i = .isFalse ha` fails: "motive is not type correct"
- `generalize` on `inst a i` fails: "result is not type correct"
- Term-mode `match` on `inst a i` resolves the outer match but does NOT substitute `inst a i` in the inner goal (non-dependent motive inferred)
- `exact rfl` fails: types are not definitionally equal across the casesOn boundary

**Affected items:** Prop 6.6.7 (all sink-case sorry's), Prop 6.6.6 (equivAt lemmas), any proof composing reflection functor maps.

**What to do — depends on which vertices are involved:**
- **Both vertices ≠ i (ne_ne case):** SOLVABLE. Use `.trans` composition of equivAt_ne equivs instead of monolithic equivAt_ne_sink/source. Then apply API lemmas (`reflFunctorMinus_mapLinear_ne_ne`, `reflFunctorPlus_mapLinear_ne_ne`, `reversedArrow_ne_ne_twice`) via `rw`. See Proposition6_6_6_sink ne_ne case for the working pattern.
- **One vertex = i (ne_eq or eq_ne case):** BLOCKED. The `(reflectionFunctor...).obj i` type is opaque — API lemma statements can't even typecheck because Lean can't see through `Decidable.casesOn` to recognize it as a quotient/kernel. **Sorry immediately.** The fix requires refactoring `reflectionFunctorPlus`/`Minus` to avoid `Decidable.casesOn`.

**Workaround for API lemma application:** When proofs have local `let instR := reversedAtVertex Q i` bindings, Lean's type class synthesis finds `instR` for `[Quiver Q]` instead of the registered `inst`, causing "synthesized type class instance is not definitionally equal" errors when applying API lemmas. **Fix**: Extract the computation as a separate top-level theorem (outside the proof) where `instR` doesn't exist as a local binding. Use explicit `@`-prefixed terms with `Etingof.reversedAtVertex Q _ inst i` to control instance resolution. See `Φ_comp_source_eq_zero` in Proposition6_6_6.lean and `reflFunctorPlus_mapLinear_eq_ne` in Definition6_6_3.lean for examples of this pattern.

**Building hom-set equivalences over `reversedAtVertex` (Exercise 7.9.8 `homFMinusEquivReduced`, #6031, sorry-free):** the same two-Quiver-instance friction bites `QuiverRepresentationHom` structure operations, plus a few reduction gotchas that each cost several iterations:
- `f.app v` / `.naturality` / the `{ app := …, naturality := … }` constructor **re-synthesize `[Quiver Q]` to the ambient `inst`** — the error is the usual "synthesized `inst✝¹` / inferred `reversedAtVertex Q i`". Always write these fully `@`-applied: `@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i) ρ₁ ρ₂ f v` and `@…mk … app_fn nat_proof`. Destructuring `fun ⟨fapp, fnat⟩ => …` does NOT avoid it (the anonymous constructor re-synthesizes on the way out).
- **`simp only [LinearMap.comp_apply]` can silently "make no progress" on `(g ∘ₗ ↑e.symm) x` goals, while `rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]` works.** When a `simp only` reduction of composed linear maps stalls for no visible reason, switch to `rw`.
- `Submodule.liftQ` needs `[AddCommGroup]` on its **codomain** (`W.obj i`), not just the quotient. Supply it with `letI : AddCommGroup (…W i) := Etingof.addCommGroupOfRing (k := k)` scoped *inside* the `liftQ` term (a top-level `letI ∀ v` pollutes instance resolution elsewhere and re-triggers the not-defeq errors).
- `subst b` (naming the variable), not `subst hb`, when `hb : b = i` and you need to keep `i` (plain `subst hb` eliminates `i`).
- The dependent `hv ▸ appAtI r` in an `if hv : v = i then …` branch: don't re-`show` the `▸` (motive fails to compute); reduce the *existing* term applied to an argument with `simp only [reduceDIte]` (works where bare `rw [dif_pos rfl]` hits "motive not type correct").
- `DirectSum.induction_on` case names are `zero` / `of` / `add` (not `H_*`); the `of` case yields `DirectSum.of` which is *defeq but not syntactically* `DirectSum.lof` — bridge with a one-line `show … lof … = … lof …` before applying `lof`-stated lemmas.
- Give the whole assembly `set_option maxHeartbeats 3200000 in` (the `let g`/`liftG`/`appAtI` chain plus two `ext` proofs is heavy).

## Common Failure Modes

### Explicit Bijection Construction (Counting Proofs)

When proving cardinality results or counting arguments, prefer explicit bijection constructions over abstract reasoning:

1. Define the forward map explicitly
2. Define the inverse map explicitly
3. Prove round-trip properties

This pattern proved GL2 conjugacy class cardinalities (disc=0 split into g01=0 and g01≠0 cases) and the `invColorEquivMC` equivalence (σ-invariant colorings ↔ monochromatic colorings). It works well because Lean's `Equiv` API is rich and `simp` handles most round-trip goals.

**Avoid `Finset.univ.image f` + `Finset.card_image_of_injective` for cardinality proofs.**
This approach requires `DecidableEq` on the codomain, causes elaboration issues with
`fin_cases` (producing unreduced `σ ^ ↑((fun i ↦ i) ⟨0, ⋯⟩)` terms), and anonymous
constructor matching in `Finset.mem_image` existentials is fragile. Instead use
`Fintype.card_congr` with an explicit `Equiv`, or `Finset.card_union_of_disjoint`.

**Counting conjugacy classes (or any quotient) of a given type: define via `Set.ncard (f '' S)`, not a `Finset.image`.** Etingof's GL₂ §5.25 table needs "number of conjugacy *classes* of each type" alongside the existing element-count theorems `GL2.card_is*` (`Chapter5/GL2ConjugacyClassCount.lean`, #5679, first `ConjClasses` instantiation for GL₂). Define each count as `(ConjClasses.mk '' {g | IsType g}).ncard` — `Set.ncard` needs **no** `DecidableEq` on the quotient (there is none natural for `ConjClasses G`) and no `Fintype`, so the `def` is instance-free. To evaluate: `Set.ncard_image_of_injOn hinj` (injectivity of `mk` on the type-set — for scalars, each central element's class is a singleton, so `IsConj g h → g = h`), then `Set.ncard_coe_finset` (note lowercase `finset`) after rewriting `{g | IsType g} = ↑(univ.filter …)` to land on the existing `card_is*` value. **Do NOT reach for `open scoped Classical` here** (the skill's usual Strategy-1 prevention): the existing `card_is*` theorems elaborated their `univ.filter (IsType ·)` with the *concrete* `DecidablePred` instances from `GL2ConjugacyClasses`, so a Classical filter in your new file is a different term and `rw [card_isScalar]` silently fails to match. Keep the concrete instances (supply `[Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)]`) and route the only genuinely-needed classical choice through `Set.ncard`, which avoids `DecidableEq (ConjClasses _)` entirely. Type predicates defined through conjugation-invariants (`disc`, `IsScalar`) are provably conjugation-invariant (`disc_conj_eq` + scalar centrality via `ext i j; fin_cases <;> simp [Matrix.mul_apply, Fin.sum_univ_two, …]` — `Matrix.one_apply` in a `simp` set here overflows `maxRecDepth`, use `mul_apply` instead), which is what makes "the type of a class" well defined.

### Well-Founded Recursion on Natural Measures

For recursive definitions where termination isn't structural:

1. Identify a natural `ℕ`-valued measure that strictly decreases
2. Prove the decrease lemmas as separate helper lemmas first
3. Define the function using `WellFoundedRelation` or `termination_by`

This pattern defined the hook walk weight function with termination via strictly decreasing hook length. Prove the decrease lemmas before attempting the definition — interleaving them causes elaboration issues.

### Fin.cons + Equiv.ofBijective for Explicit Equivalences

When constructing an equivalence between a finite type and `Fin n` (e.g., for counting conjugacy classes, enumerating roots):

1. Build the forward map inductively using `Fin.cons` to handle each case
2. Prove injectivity by case analysis on each pair
3. Prove surjectivity by showing the image covers all elements
4. Combine via `Equiv.ofBijective`

```lean
-- Example: equivalence between conjugacy class representatives and Fin 4
def classEquiv : Fin 4 → ConjClass G :=
  Fin.cons scalar (Fin.cons splitSS (Fin.cons parabolic (Fin.cons elliptic Fin.elim0)))

theorem classEquiv_bijective : Function.Bijective classEquiv := by
  refine ⟨fun i j h => ?_, fun c => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [classEquiv]
  · obtain ⟨g, rfl⟩ := c.exists_rep
    -- case analysis on g to find preimage
    sorry

noncomputable def classFinEquiv : ConjClass G ≃ Fin 4 :=
  (Equiv.ofBijective classEquiv classEquiv_bijective).symm
```

This pattern proved GL₂(𝔽_q) conjugacy class cardinalities and `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`. It works well because `fin_cases` handles all pairs for injectivity automatically.

### Finite set of representatives indexed by a finite predicate-set

"Finitely many iso classes" / "finite covering set of representatives" goals (the
Ch6 finite-type definition, the orbit-counting chain #4780–#4786) reduce to:
pick one representative per element of a finite set `S = {x | P x}` (e.g. the
positive roots, finite by Theorem 6.5.2a), then show the representatives form a
finite set. Two gotchas, both hit in #4779:

- `choose!` on `∀ x, P x → ∃ y, Q y` returns a **dependent** function
  `g : ∀ x, P x → β` — the hypothesis argument is **kept**, not dropped. So `g`
  is not a plain `α → β` and `Set.image g` / `hS.image g` fail with a type
  mismatch.
- Use `Set.Finite.dependent_image` for finiteness: from `hS : S.Finite` and
  `F : ∀ x ∈ S, β` it gives `{y | ∃ x hx, F x hx = y}.Finite`. Let the set be
  inferred — `refine ⟨_, hS.dependent_image (fun x hx => g x hx), ?_, ?_⟩` —
  rather than writing a nested set-builder `{y | ∃ x (hx : x ∈ {x | P x}), …}`,
  which fails to parse. `x ∈ {x | P x}` is defeq to `P x`, so `g x hx`
  typechecks directly; recover witnesses downstream with `rintro y ⟨x, hx, rfl⟩`.

### Bridge to Mathlib's Native Abstractions

When the project uses a custom representation (e.g., list-based paths, adjacency matrices) but Mathlib has richer API for a different representation (e.g., `SimpleGraph`):

1. Build a conversion function to Mathlib's type
2. Prove key properties transfer across the conversion
3. Use Mathlib's existing API on the converted representation

This proved `dynkin_edge_count` by converting adjacency matrices to `SimpleGraph` and leveraging Mathlib's connected graph theory.

## Issue Feasibility Triage (Before Committing to Work)

Before spending a full session on an issue, spend 10-15 minutes on feasibility triage:

### Step 1: Check sorry count and location
```bash
grep -n "sorry" <target-file>.lean | head -20
```
Count the sorries. If the issue claims "1 sorry remains" but the file has 5, the issue is stale.

### Step 2: Identify the mathematical core
Read the blob (`blobs/<Chapter>/<Item>.md`) and identify what mathematical result is needed. Ask:
- Is this a computation (finite cases, arithmetic)? → Likely Tier 1
- Does it need a named theorem not in Mathlib (Krull-Schmidt, Schur-Weyl)? → Likely Tier 3
- Is it standard algebra/linear algebra with Mathlib API? → Likely Tier 1-2

### Step 3: Check for known dead-ends
Search the "Known Dead-Ends" section above. If the proof touches `Decidable.casesOn` in Ch6, `ExteriorAlgebra ↔ PiTensorProduct`, or `SchurModule`, it's blocked.

### Step 4: Verify infrastructure exists
For each dependency the proof needs:
```bash
grep -rn "theorem <dep_name>\|def <dep_name>" EtingofRepresentationTheory/
```
If a dependency is sorry'd, that's OK (sorry acts as axiom). But if a dependency doesn't exist at all, you need to build it — factor that into your time estimate.

### Step 5: Skip or decompose if needed
- If blocked → `coordination skip <N> "reason"` immediately
- If too large → decompose into sub-issues (see agent-worker-flow Step 4b)
- If feasible → proceed with confidence

**Common triage mistakes:**
- Spending 2 hours before realizing a theorem needs Krull-Schmidt
- Not checking if the issue's sorry count matches reality (other agents may have merged changes)
- Assuming a "1 sorry" issue is easy — the sorry may hide a 200-line proof

## Common Failure Modes

From Phase 2 review patterns and Stage 3.2 proof experience (110+ merged PRs through wave 20):

1. **Wrong Mathlib declaration name.** Always `#check` the declaration before using it.
2. **Fabricated references.** If `.refs.md` cites a Mathlib declaration, verify it exists.
3. **Scope mismatch.** The book may state a theorem for a specific case (e.g., finite-dimensional) but Mathlib has it more generally. Use the general version.
4. **Missing instances.** Representation theory needs many type class instances. If Lean can't find one, check if Mathlib has it under a different name or if you need to `open` a namespace.
5. **Hidden hypotheses in book statements.** The book may omit hypotheses that are implicit in context (e.g., algebraic closure, field characteristic). Discovered examples: Theorem 3.10.2 needed `[IsAlgClosed k]`, Example 8.1.7 needed `Field k` not `CommRing R`. When a proof attempt fails at a fundamental level, check whether the statement needs additional hypotheses.
6. **Status tracking lag.** After proving a theorem, update `items.json` immediately in the same commit. Audits have found items marked `scaffolded` that were actually `sorry_free`. Always update proactively — manual tracking in `progress/items.json` is the only status tracking mechanism. **Edit `items.json` surgically (`Edit` on the exact field lines), never rewrite it with `json.dump`/`json.load`+dump** — the reserializer reflows indentation/key-order/unicode and produces a multi-thousand-line diff against the 13k-line shared file (caught only by `git diff --stat`). When changing a `fidelity`/`status` field, `grep -n` the item id, Read those ~15 lines, and `Edit` just the value (and drop any now-stale `fidelity_note`).
7. **FDRep abstraction fighting.** If your proof requires distributing `.hom.hom` over sums or otherwise unwrapping 3+ layers of categorical abstraction, you're fighting the wrong abstraction. See the FDRep Categorical Plumbing patterns above for alternatives.
8. **Universe level mismatches.** Representation theory proofs sometimes need explicit universe annotations (`.{v}`) especially when working with Jacobson radical or maximal ideal APIs. If type unification fails mysteriously, try adding explicit universe parameters.
9. **Sinking entire context windows on known dead-ends.** Before starting a proof, check the "Known Dead-Ends" section above. If the proof requires bridging `ExteriorAlgebra` ↔ `PiTensorProduct` or resolving the `if`-branching diamond, sorry it immediately and move on. Multiple agents have confirmed these are blocked on missing infrastructure.
10. **Opaque placeholder accumulation.** Defining key structures as `sorry : FDRep k G` (e.g., `SchurModule k N lam`) creates downstream dependency chains that block entire proof clusters. When you must sorry a definition, prefer making the carrier type concrete and sorry-ing only specific operations/instances (see "Never sorry a Type" above). Each opaque placeholder blocks all items that depend on it.
11. **Convention mismatch between book and Mathlib.** Sign conventions, ordering conventions, and normalization conventions can silently make statements unprovable. See "Verify Statement Correctness Before Proving" section above. The vandermondePoly sign mismatch wasted multiple agent sessions before being discovered via a concrete n=2 counterexample.
12. **Issue description proof strategies are sometimes wrong.** The proof approach described in an issue body may be mathematically incorrect or only work for special cases. Always spend 10 minutes verifying the described approach before committing to it. See "Issue Description Feasibility Check" section above.
**Encoding an `xᵢ ↦ xᵢ⁻¹` (inverse-variable) symmetric-polynomial identity honestly — no Laurent variables (Ch5 §5.23 fact (b), #5534, `SchurPolyInverseShift.lean`).** The repo's `schurPoly N : (Fin N → ℕ) → MvPolynomial (Fin N) ℚ` lives in honest polynomials, so `s_λ(x⁻¹)` cannot be written literally. Encode `(x₁⋯x_N)^c · s_e(x⁻¹)` as the **complemented-exponent alternant** `det(Xᵢ^{c - e_j})`: multiplying `a_e(x⁻¹) = det(Xᵢ^{-e_j})` by `(∏x)^c` scales row `i` by `Xᵢ^c`, giving honest nonnegative exponents *provided `c ≥ e_j` for all `j`* (here `e = shiftedExps λ`, `c = s+N-1`, and `λ_j + δ_j ≤ s+N-1` follows from `λ_j ≤ s`). A **column reversal** (`Matrix.det_permute'` with `Fin.revPerm`) turns the complemented exponent sequence into a genuine `shiftedExps ν` (up to the reversal sign `sgn(w₀)`), where `ν j = s - λ_{rev j}`; then `schurPoly_mul_vandermonde` reads off `s_ν · Δ`. The whole proof is alternant linear algebra — no `formalCharacter`, no reps. The one arithmetic obligation is the pointwise exponent identity `(c) - shiftedExps λ j = shiftedExps ν (rev j)`, closed by `simp only [shiftedExps, Fin.rev_rev, Fin.val_rev]` + `omega` (feed `λ j ≤ s` and `j.isLt`). Rewrite the funext at the **matrix-argument level before `ext`** (`rw [complementExps_eq]` on `alternantMatrix N (fun j => …)`), not after — post-`ext` the exponent appears beta-reduced and a lambda-equality `rw` won't match. This "complement-and-reverse the exponents" recipe is the honest avatar of any inverse-variable Schur/character identity (dual characters, contragredients).

**Order-by-order deformation / 1-cocycle-obstruction arguments: model the Cauchy convolutions as `PowerSeries (Module.End k V)` multiplication (Problem 3.9.4(a), #6002, sorry-free in `Chapter3/Problem3_9_4.lean`).** When the proof needs the associativity reindex `∑_{i+j=n} bᵢ∘(∑_{s+t=j} P_s∘Q_t) = ∑_{r+q=n}(∑_{i+s=r} bᵢ∘P_s)∘Q_q` (deformation multiplicativity, star products, `Cₙ(ac)=∑ Cᵣ(a)∘ρ_q(c)`), do **not** grind a triple-antidiagonal reindex by hand. `Module.End k V` is a *non-commutative* `Ring` and `PowerSeries R` is a `Semiring` for any (non-comm) `Semiring R` (`variable [Semiring R]` governs the instance — comm is only needed for `CommSemiring`), so package each sequence with `PowerSeries.mk` and get the reassociation from `mul_assoc` + `PowerSeries.coeff_mul` + `PowerSeries.coeff_mk` (`PowerSeries.ext` for series equality). Composition ↔ ring mult is `Module.End.mul_eq_comp : f*g = f.comp g` (`rw [← …]` turns `.comp` into `*`; `Module.End.mul_apply : (f*g) x = f (g x)`). Gotchas that cost iterations: (a) **`LinearMap.mulLeft k x` fails instance synthesis for `End`** ("`Module ?m ?m` stuck") — use `LinearMap.llcomp k V V V x` (left-composition = left-multiplication, needs only module instances) and unfold with `LinearMap.llcomp_apply'` (the *2-arg* `llcomp f g = f ∘ₛₗ g`; `llcomp_apply` is the 3-arg form and won't fire). (b) **`rw [if_pos/if_neg …]` can't see an `if` hidden under an un-beta-reduced structure-field lambda** (`D.coeff p.1 a` elaborates as `(fun n => if n=0 …) p.1 a`) — precede with `dsimp only`/`simp only` to beta-reduce, or just use `simp [h]` which beta-reduces itself. (c) `if h : ∃ X, … then h.choose else 0` in a `noncomputable def` needs `open Classical in` *before* the docstring (docstring must sit immediately above the `def`). Build the intertwiner coefficient sequence by structural recursion over `Fin`-prefixes (`bVec : (n:ℕ)→Fin (n+1)→End`, `Fin.snoc`; coherence `bVec n i = bSeq ↑i` by `Fin.lastCases` + `Fin.snoc_castSucc`/`Fin.snoc_last`), and prove the trivialisation equation by `Nat.strong_induction_on`. `Ext¹(V,V)=0 ⇒ every cocycle is a coboundary`: from `Subsingleton (Ext1 …)` use `Subsingleton.elim` + `Submodule.Quotient.mk_eq_zero` + `Submodule.mem_comap`, and `g ∈ coboundaries` (a `Submodule.span`) `⇒ ∃X, coboundaryOf X = g` by `Submodule.span_induction` using `coboundaryOf`'s additivity/homogeneity/`_zero` (the coboundary map is linear so its range is already a submodule — no need to bundle it). Value-level ring identities in `End` (with products as opaque atoms) close with `noncomm_ring` (`import Mathlib.Tactic.NoncommRing`), not `ring`/`ring_nf`.

13. **A prior agent's "circular / needs missing theorem" skip can be wrong.** When an issue was already skipped as circular or blocked on a named result "not in the project," do not just re-skip — check whether an existing **off-block / orthogonality / character lemma's diagonal (special) case** already supplies the missing independent input. Concrete example (#2693): the rank-1 Young-symmetrizer fact was twice skipped as "needs primitivity `c_λ k[S_n] c_λ = k·c_λ`, not in project." But the diagonal case of the existing `youngSym_trace_kronecker'` is exactly `trace(c_λ|_S) = α` (an independent `ℂ[S_n]` computation), and `trace(α⁻¹·c_λ|_S) = 1` via `IsProj.trace` gives rank 1 directly — no primitivity, no whole-space trace, no dimension bridge. Pattern: if a proved `..._vanishes_off_block` lemma gives the off-diagonal value (`if h_ne then 0`), its `if_pos rfl` diagonal twin usually gives the special-block value you need. Spend 10 minutes looking for the diagonal twin before re-skipping.
14. **Namespace dot-notation mismatch.** Most Lean files in this project wrap code in `namespace Etingof` (and `noncomputable section`). If you define `def YoungDiagram.foo` inside `namespace Etingof`, the full name is `Etingof.YoungDiagram.foo` — dot notation `μ.foo` (where `μ : YoungDiagram`) will NOT find it. **Symptoms:** The definition silently fails to register (no error reported) and downstream references get "Invalid field" errors. **Fix:** Close the namespace before defining `YoungDiagram.*` declarations that need dot-notation access, then reopen it. Remember to also close/reopen any `noncomputable section`.


### Tactic Gotchas with `rw`, `omega`, and `nsmul`

1. **`rw [← Finset.sum_filter]` fails on lambda matching.** `rw` does strict term matching and often can't unify `fun x => if x ∈ S then f x else 0` with `Finset.sum_filter`'s pattern. Use `simp only [← Finset.sum_filter]` instead — `simp` is more flexible with lambda matching.

2. **`omega` can't see through `Fin` equalities.** After `Fin.val_eq_of_eq`, omega may not recognize the resulting Nat equality. Fix: use `simp only [Fin.mk.injEq] at h` to normalize `⟨a, _⟩ = ⟨b, _⟩` into `a = b` before calling `omega`.

3. **`omega` can't handle `min`/`if` from `List.length_take`.** `List.length_take` gives `(l.take n).length = min n l.length`, and `min` unfolds to `if n ≤ l.length then n else l.length`. omega can't simplify `if`. Fix: extract the bound you need with `lt_of_lt_of_le h (min_le_left a b)` or `min_le_right`.

4. **`nsmul_eq_mul` produces `↑n * x` not `n * x`.** Converting `n • x` (where `n : ℕ`, `x : ℤ`) via `nsmul_eq_mul` gives `↑n * x` with a Nat cast. `linarith` can't equate `↑2 * x` with `(2 : ℤ) * x`. Add `push_cast` after `nsmul_eq_mul` to normalize.

5. **`linarith` requires a linear order — use `linear_combination` over ℂ.** `linarith` only works on linearly ordered types (ℝ, ℤ, ℕ, etc.). For goals over ℂ like `a + b = 0 → a = -b`, use `linear_combination h` instead. The `linear_combination` tactic works over any commutative ring.

6. **sl(2)-triple bracket relations are stated with ℕ-smul — use `nsmul_lie`, not `smul_lie` (Ch2 #5307).** `Sl2Irrep.lie_h_e : ⁅sl2_h, sl2_e⁆ = 2 • sl2_e` and `lie_h_f : ⁅sl2_h, sl2_f⁆ = -(2 • sl2_f)` use **ℕ-smul** (`2 : ℕ`). In a module computation, after `rw [leibniz_lie .., lie_h_f, neg_lie]` you get `-⁅(2:ℕ) • sl2_f, m⁆`; `smul_lie` (the ℂ-scalar lemma) does **not** match the pattern `⁅?t • ?x, ?m⁆`. Use `nsmul_lie : ⁅n • x, m⁆ = n • ⁅x, m⁆`, then `two_nsmul` (or `push_cast`) to turn the resulting `(2:ℕ) • y : M` into something `module` closes. This is the workhorse for the highest-weight ladder (`fIter`/`lie_sl2_h_fIter`/`lie_sl2_e_fIter` in `Problem2_15_1_m_Module.lean`) feeding the #5301 Clebsch–Gordan module-iso assembly.

### Counting solutions / orbits in `ZMod n` where `n` is a *symbolic* modulus (e.g. `q²−1`)

Formalizing a "count the `ν ∈ K^∨` with property P" claim by modelling `K^∨ ≅ ZMod n`
(Ch5 Discussion 5.25.4 / #5169, `Chapter5/Discussion5_25_4.lean`) hits two recurring traps:

1. **`Finset.univ`/`.filter`/`.card` over `ZMod n` needs `Fintype (ZMod n)`, which only
   exists given `[NeZero n]` — and the *statement* elaborates before any in-proof `haveI`.**
   So a `def`/`theorem` whose *type* mentions `Finset.univ : Finset (ZMod (q²−1))` (or any
   `.filter`/`.card` of it) must carry `[NeZero (q ^ 2 - 1)]` as an **instance binder**; you
   cannot derive it inside the proof from a `(hq : 2 ≤ q)` Prop hypothesis (that's too late —
   `Finset.univ` in the signature has already failed to synthesize `Fintype`). Put `[NeZero
   (q ^ 2 - 1)]` on the def and on every theorem referencing it; lower-level lemmas whose
   *statements* avoid `univ` (e.g. an `x.val` divisibility iff) can instead `haveI : NeZero
   … := ⟨by …⟩` internally where they need `ZMod.val_lt`/`natCast_zmod_val`. Callers with a
   concrete `q ≥ 2` discharge the instance trivially; an abstract caller does one `haveI`.

2. **`rw [hfac]` to replace the modulus `n` (e.g. `q²−1 = (q−1)(q+1)`) gives "motive is not
   type correct" whenever a `(x : ZMod n).val` term is in scope** — because `ZMod.val x =
   @ZMod.val n x` has `n` as an *explicit argument*, and `x : ZMod n`, so rewriting `n`
   retypes `x`. **Never rewrite the modulus on a hypothesis/goal containing `.val` of that
   `ZMod`.** Instead rewrite in the *opposite* direction on a term where the product form
   `(q−1)*(q+1)` does **not** overlap the `.val`: e.g. to turn goal `(q+1) ∣ x.val` into
   `(q²−1) ∣ (q−1)*x.val`, do `rw [← mul_dvd_mul_iff_left hq1, ← hfac]` (the `← hfac`
   collapses the freshly-introduced `(q−1)*(q+1)` divisor, leaving `x.val` untouched); to
   prove `(q²−1) ∣ (q−1)*x.val`, build `h2 : (q−1)*(q+1) ∣ (q−1)*x.val` first then `rwa
   [← hfac] at h2`; to bound `x.val < (q−1)*(q+1)`, `rw [← hfac]` then `exact ZMod.val_lt x`.
   The fixed-point count itself is a clean `Finset.card_nbij'` between the fixed set and
   `Finset.range (q−1)` via the multiples-of-`(q+1)` map `k ↦ ((q+1)*k : ZMod n)` (with
   `ZMod.val_natCast_of_lt` for the round-trips); a fixed-point-free involution's orbit count
   is `card/2`, proved by exhibiting a transversal (val-minimal element per pair) and
   `Finset.card_union_of_disjoint` on `moved = reps ∪ reps.image f`.

## Breadth-vs-Depth Phase Awareness

The project alternates between **breadth phases** (statement formalization) and **depth phases** (proof completion). Recognizing which phase you're in prevents misallocating effort.

### Breadth Phase (Statement Formalization)
- **Trigger:** Proof backlog < 30 items, or agents are running out of proof targets
- **Focus:** Formalize new theorem/definition statements across multiple chapters
- **Expected metrics:** Low items/PR ratio, sorry count may increase (new sorry'd statements added)
- **This is not a failure mode** — it's strategic investment in the proof pipeline

### Depth Phase (Proof Completion)
- **Trigger:** Proof backlog > 40 items, or enough targets exist across 3+ chapters
- **Focus:** Prove sorry'd items, prioritizing chain completion and chapter closures
- **Expected metrics:** Higher items/PR ratio, sorry count declining
- **Planners should create 80%+ proof issues** during this phase

### Current Status (as of Wave 42, 2026-04-03)
The project has 25 sorries across 14 files (down from 66 at wave 28). Sorry-free rate: 266/280 files (95.0%). 577/583 items (98.9%) sorry-free. This is deep in a **depth phase** — all remaining work is proof completion on hard items. Statement formalization is complete.

**Chapter status (Wave 42):** Ch3, Ch4, Ch7, Ch8 are 100% sorry-free. Ch2 has 1 sorry (Theorem2_1_2). Ch5 has 13 sorries across 6 files. Ch6 has 7 sorries across 6 files. Ch9 has 4 sorries across 1 file (MoritaStructural).

**Major milestones since wave 40:**
- **Proposition5_14_1 sorry-free** (#2048) — Convention swap regression fully recovered (2→0)
- **PolytabloidBasis 6→3** (#2018, #2041) — T_col_inc proved, garnirSet helpers proved
- **Corollary6_8_3 restructured** (#2050) — parallel reflection chain approach
- **Theorem5_22_1 decomposed** (#2042, #2058) — 2→5 sorries from strategic scaffolding
- **FormalCharacterIso 2→1** (#2059) — shift formula proved
- **Mackey machine progress** (#2034) — Theorem5_27_1 from 4→2 sorries
- **OrientationDefs extracted** (#2057) — circular import broken for Corollary6_8_4

**Major blocker clusters (updated wave 42):**
1. **Weyl character formula** (7 sorries, 3 files): Theorem5_22_1 (5), FormalCharacterIso (1), Proposition5_22_2 (1). Active: #2054 targeting charValue chain (5→1)
2. **Gabriel's theorem chain** (7 sorries, 6 files): Corollary6_8_3 (2), Corollary6_8_4 (1), CoxeterInfrastructure (1, universe-blocked), Problem6_1_5_theorem (1), Problem6_9_1 (1), Theorem6_5_2 (1). Active: #2053
3. **Polytabloid basis** (4 sorries, 2 files): PolytabloidBasis (3), TabloidModule (1). Active: #2055
4. **Morita/Eilenberg-Watts** (4 sorries, 1 file): MoritaStructural — all 4 relate to k-linearity gap. No active work.
5. **Mackey machine** (2 sorries, 1 file): Theorem5_27_1 — two open PRs (#2047, #2049) pending CI fixes

**Velocity trend:** 66 → 43 → 36 → 27 → 29 → 28 → 25 sorries over waves 28-42. Rate decelerating as remaining items are increasingly hard. The bump at wave 39 (27→29) was from strategic decomposition; steady decline resumed.

**Key velocity insight:** Difficulty 3/3 items have a ~30% single-session success rate — agents should budget accordingly and commit partial progress early. **Agents that don't commit intermediate work produce zero value** — stale claims continue to be a recurring problem.

## Convention Swap Regressions

**Lesson from Wave 41-42:** Changing a foundational convention (e.g., YoungSymmetrizer from `a_λ * b_λ` to `b_λ * a_λ`, PR #2002) can cause cascading regressions in downstream files that depend on the old convention. The Proposition5_14_1 regression (#2048) took a dedicated PR to fix.

**Wave 44 update:** Meditate #2102 determined that the current `b_λ * a_λ` convention MUST be switched BACK to `a_λ * b_λ` (#2103). The `b_λ * a_λ` convention fundamentally blocks the straightening lemma (no left P_λ absorption). The previous convention change was premature — it was done to make `polytabloid_self_coeff` work but broke the more important straightening proof. Budget ~150 lines for the switch and downstream fixes.

**Prevention pattern:**
1. Before swapping any convention, `grep` for ALL downstream uses across the codebase
2. Fix ALL downstream files in the SAME PR as the convention change
3. If the blast radius is too large for one PR, create issues for each affected file before merging
4. Never merge a convention swap that breaks existing sorry-free theorems — this is a net regression even if the new convention is "more correct"

**Detection:** After merging a convention change, immediately build ALL files that import the changed module: `lake build <ImportingModule1> <ImportingModule2> ...`

## `simp` Doesn't See Through Local `let` Bindings

When `simp` fails to make progress on a goal involving a term bound by a local `let`:

**The problem:** `simp` and `simp_rw` do not beta-reduce through local `let` bindings. If you have:
```lean
let f := DirectSum.component R i
-- Goal: ... f (Finset.sum ...) ...
simp [DirectSum.component.of]  -- makes no progress!
```

**Workaround 1: Use `rw` before `simp`**
```lean
rw [DFinsupp.finset_sum_apply]  -- expand the sum application first
simp_rw [show f x = ... from rfl]  -- then rewrite with explicit `show`
```

**Workaround 2: Use `change` to eliminate the `let`**
```lean
change <explicit_form_without_let>
simp [...]  -- now simp can see the structure
```

**Workaround 3: Use `dsimp only` to reduce `let` bindings**
```lean
dsimp only []  -- reduces let-bindings in the goal
simp [...]  -- now works
```

**Evidence:** Discovered independently in Proposition6_6_7 (#1800) and Problem6_9_1 (#1807). The `DFinsupp.finset_sum_apply` + `show` pattern was the successful resolution in both cases.

## Decidable Instance Mismatch Patterns (Comprehensive)

Decidable instance mismatches are a recurring friction point across the project. They arise when `classical` decidability and concrete `DecidableEq`/`DecidablePred` instances coexist, creating terms that look identical but are not definitionally equal.

### Symptom Recognition

- `rfl` fails on two expressions that are "obviously equal"
- `rw` fails with "motive is not type correct" on a Decidable-dependent term
- Two `Finset.univ` expressions have different `Fintype` instances
- `if`/`dite` expressions don't reduce under `simp` because the `Decidable` instance is opaque

### Strategy 1: `open scoped Classical` (Prevention)

Add at the section level, **before** any definitions that use `haveI : DecidablePred ... := Classical.decPred _`:
```lean
open scoped Classical
```
This ensures all `DecidablePred` instances come from the same source. **Best approach** — prevents the problem rather than patching it.

### Strategy 2: `convert rfl using N` (Patching)

When two sums over `Finset.univ` differ only in their `Fintype` instance:
```lean
convert rfl using 2  -- handles via Subsingleton (Fintype α)
```

### Strategy 3: `trans` + separate goals

When `rw` fails due to a dependent Decidable in the motive, split into two steps:
```lean
-- Instead of: rw [h]  -- fails with "motive is not type correct"
calc lhs = middle := by <prove_without_h>
       _ = rhs := by <prove_using_h>
```

### Strategy 4: `Subsingleton.elim` for proof irrelevance

When two `Decidable` instances block definitional equality:
```lean
have : inst₁ = inst₂ := Subsingleton.elim _ _
subst this  -- now only one instance exists
```

### Strategy 5: Avoid `set` for local definitions

The `set x := expr` tactic introduces a local definition that can capture the "wrong" Decidable instance. Prefer `have` or `let` with explicit type annotations instead.

**Evidence:** Decidable mismatches appeared in Theorem5_27_1 (sessions #5, #15), Proposition6_6_7 (#1800), and Proposition6_6_6_source (#1821). Strategy 1 (`open scoped Classical`) is the most reliable prevention.

## Universe Pinning Strategy

When universe level errors or mismatches arise (common in representation theory where multiple universe levels interact):

**Pattern:** Change from `Type*` to explicit `universe u v` declarations:
```lean
universe u v

theorem my_theorem
    (k : Type u) [Field k]
    (V : Type v) [AddCommGroup V] [Module k V] :
    ... := by
  ...
```

**When to use:**
- `universe polymorphism` errors
- Sigma types with universe-level mismatches
- `MoritaEquivalent`, `FDRep`, or other constructions that require universe alignment
- `SchurModule`, `AlgIrrepGL`, or similar constructions that mix multiple universe-polymorphic types

**Evidence:** Universe pinning resolved issues in Theorem5_18_4 (SchurModule universe annotations), IsFiniteTypeQuiver (pinned to `Type` to avoid universe mismatch), and BasicAlgebraExistence (explicit `Type u` throughout).

## Section Variable Auto-Inclusion Gotcha

Lean 4 section variables declared with `variable (h : P)` are only auto-included
in declarations where they appear **syntactically** in the type or proof body.
Dot notation like `h.eq` may not trigger auto-inclusion — Lean's variable scanner
doesn't always resolve dot notation to find the underlying variable.

**Symptom**: "Unknown identifier `h.eq`" or "Unknown identifier `h`" inside a
proof in a `section` block, even though `h` is declared as a `variable`.

**Fix**: Add `include h` after the `variable` declaration to force inclusion in
all subsequent declarations in the section:
```lean
section Foo
variable {e : A} (he : IsIdempotentElem e)
include he  -- forces he into all declarations in this section

lemma bar ... := by
  ... he.eq ...  -- works now
end Foo
```

**Alternative**: Explicitly add the parameter to each declaration (the pattern
used in this project's `cornerSubmodule_left_mul` etc.).

### Reverse problem: an *unused* section variable trips the linter

This project's CI runs `weak.linter.mathlibStandardSet = true`, so an
instance/hypothesis from the `variable` block that a lemma does not use emits
`automatically included section variable(s) unused` (and unused hypotheses like
a stated `(hdeg : …)` emit `Variable name … is not explicitly referenced`).
These are **warnings only** — plain `lake build` still returns 0, so CI passes —
but the project keeps lint clean. Silence an unused instance with
`omit [Inst] in` immediately before the declaration. Gotcha: `omit … in` must go
**before** the docstring, not between the `/-- … -/` and the `theorem`
(`omit` after a docstring gives `unexpected token 'omit'; expected 'lemma'`):
```lean
omit [FiniteDimensional ℂ V] in
/-- doc … -/
theorem foo … := …
```
Related `mathlibStandardSet` linter: `linter.style.show` flags every `show` used
to *change* the goal to a defeq form. Use `change` instead of `show` for those
(reserve `show` for readability of an intermediate state).

### Calling a section-variabled lemma: don't guess positional args

When you *apply* a lemma defined under a `variable (k : Type*) [Field k]
(N n : ℕ)` block, the used section variables are prepended as **explicit**
arguments in declaration order — so `foo` may really take `foo k N n M halg …`
even though its written signature starts at `M`. The order is often
non-obvious (a section `n` redeclared locally by an earlier lemma can drop out;
an implicit-looking variable can be explicit and vice versa). Guessing
positionally wastes build cycles on `Application type mismatch: argument … has
type ℕ but is expected to have type FDRep …`.

**Fix**: before the first call, run `#check @Namespace.foo` (in a throwaway file
or scratch `#check`) to read the real binder list, then either match it
positionally or pass the data argument by name (`foo (M := M) …`) and let the
preceding section variables infer. Thirty seconds of `#check` beats four failed
`lake build`s.

## When to Decompose vs. Attempt Directly

**Decompose immediately** when:
- The sorry has resisted 2+ attempts by prior agents (check issue comments)
- The proof has 3+ conceptually independent sub-goals
- You estimate the proof at 100+ lines of tactics
- The file is 500+ lines and you need to understand most of it
- You're past the midpoint of your context window

**Attempt directly** when:
- The sorry is in a Tier 1 (achievable) category
- A clear tactic sequence is visible after reading the book's proof
- The file is short (<200 lines) and self-contained
- No prior agent has attempted this sorry

**The decomposition output pattern:**
```lean
-- BEFORE: monolithic sorry
theorem hard_theorem : conclusion := by sorry

-- AFTER: structured proof with isolated helper sorries
private lemma step1 : ... := sorry  -- clear, independently claimable
private lemma step2 : ... := sorry  -- clear, independently claimable

theorem hard_theorem : conclusion := by
  have h1 := step1
  have h2 := step2
  exact final_combination h1 h2
```

**Value assessment:** A session that decomposes a monolithic sorry into 5 sub-goals and proves 3 of them is MORE valuable than a session that attempts the monolithic sorry directly and fails. Decomposition creates independently claimable work items and documents the proof strategy.

**Evidence:** Problem6_9_1 was decomposed from 1 sorry into 8 sub-goals, 6 proved (#1807). Theorem5_22_1 was decomposed into coefficient extraction + core identity (#1806). BasicAlgebraExistence was split into 2 targeted helpers (#1803). All three patterns created visible, committable progress.

### Reframe a geometric crux algebraically when the deliverable is abstract (SO(3) icosahedral, #6971)

When an issue *describes* a hard geometric construction ("the five inscribed tetrahedra / Kepler
cubes of the dodecahedron", "the four body diagonals of the cube") but the actual **deliverable
is an abstract existence statement** (`∃ φ : G →* Equiv.Perm (Fin 5), Function.Injective φ`, or
`Nonempty (G ≃* …)`), do NOT reach for a coordinate model (golden-ratio matrices, explicit vertex
sets) first — that path is thousands of lines. Look for a purely group-theoretic reduction that
delivers the *same abstract object* without the geometry.

Concretely for #6971 (icosahedral, `|G| = 60`): "faithful action on the 5 tetrahedra" reduces to
**"`G` is simple + has an index-5 subgroup"**, because a finite simple group with an index-5
subgroup embeds faithfully into `Equiv.Perm (Fin 5)` via the **core-free coset action** —
`Subgroup.normalCore_eq_ker H` says the kernel of `MulAction.toPermHom G (G ⧸ H)` is
`H.normalCore`, which simplicity forces to `⊥` (`Subgroup.Normal.eq_bot_or_eq_top`); transport
`G ⧸ H ≃ Fin 5` (from `H.index = 5`) with `Equiv.permCongrHom`. This dissolves the entire
"construct the 5-element G-set" difficulty (no icosahedron coordinates), leaving two standard
group-theory sorries (`G` simple; index-5 subgroup) — see #6982/#6983. Before checking Mathlib for
"heavy" infrastructure, note Mathlib has NO order-60→A₅ classification and NO Sylow⟶simple lemma,
but DOES have every Sylow-counting primitive plus `normalCore_eq_ker`, `MonoidHom.ker_eq_bot_iff`,
`Equiv.Perm.eq_alternatingGroup_of_index_eq_two`. Rule of thumb: **the coset/normalCore embedding
is the standard way to realize an abstract finite group as a concrete permutation group of a given
degree** — prefer it over any explicit configuration whenever the target is `Equiv.Perm (Fin n)`.

## Rewriting Inside Coercion Wrappers (`.ker`, `↥`, `Module.finrank`)

When `rw [h]` fails to find a pattern that is visibly present in the goal — especially inside
`LinearMap.ker`, `↥(Submodule)`, or `Module.finrank k ↥(...)` — the issue is coercion mismatch.

**Don't iterate**: If `rw`, `simp only`, `conv`, and `show` all fail on the same pattern, stop
trying variations. Instead:

1. **For `.ker` rewrites**: Use `calc` with `congr_arg LinearMap.ker h` to rewrite the argument:
   ```lean
   calc LinearMap.ker LHS
       = LinearMap.ker RHS1 := congr_arg LinearMap.ker h_eq
     _ = LinearMap.ker RHS2 := LinearMap.ker_smul _ _ h_ne_zero
   ```

2. **For `Module.finrank` on equal submodules**: Add a helper:
   ```lean
   private lemma finrank_submodule_congr {S₁ S₂ : Submodule R M} (h : S₁ = S₂) :
       Module.finrank R S₁ = Module.finrank R S₂ := by subst h; rfl
   ```
   Direct `h ▸ rfl` may timeout due to expensive coercion unification.

3. **For `iInf` equality**: Use `iInf_congr` (not `iInf_mono` + `le_antisymm`) when you need
   equality, not just inequality.

## Quiver Hom Universe in Lean 4/Mathlib

`Quiver.{v, u}` has `Hom : V → V → Type v`, NOT `Sort v`. You CANNOT have
Prop-valued arrows directly. For Prop-valued quiver arrows (as used in
`IsFiniteTypeQuiver` with `@Quiver.{0, 0}`), wrap with `PLift`:

```lean
def myQuiver : Quiver (Fin k) where
  Hom i j := PLift (j.val = (i.val + 1) % k)  -- Type 0, not Prop
```

The CategoryTheory instances on `Fin k` (`CategoryStruct.toQuiver`,
`ReflQuiver.toQuiver`) conflict with custom quivers. Suppress per-declaration:

```lean
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
def/theorem ... := by letI := myQuiver k hk; ...
```

Dot notation on `QuiverRepresentation` fields (e.g., `.obj`) triggers Quiver
instance synthesis. Use explicit `@QuiverRepresentation.obj ... inst ...` when
instances are suppressed.

## `Finsupp.lmapDomain` Coercion Gotcha

`Finsupp.lmapDomain` is a `LinearMap` wrapper around `Finsupp.mapDomain`. They are
**definitionally equal**, but `simp [Finsupp.lmapDomain_apply]` often fails because
the coercion `⇑(lmapDomain ...)` doesn't match the simp lemma's LHS pattern.

**Workaround:** Don't try to simp through the coercion. Instead, unfold the
definition manually with `simp only [myDef]` (where `myDef` uses `lmapDomain`),
then use `Finsupp.mapDomain_single`, `Finsupp.mapDomain_zero`, etc. directly.
Since `lmapDomain` is definitionally `mapDomain`, the `mapDomain` lemmas apply
without any conversion step.

## `Nat.card` vs `Fintype.card` in Theorem Statements

Prefer `Nat.card` over `Fintype.card` in theorem **statements** (not just proofs).
`Fintype.card` requires a `Fintype` instance, which for subgroups needs
`DecidablePred (· ∈ S)` — unavailable outside `classical` blocks. This means
theorems using `Fintype.card` can't be applied without `classical`.

`Nat.card` works without decidability instances. Inside proofs, convert via:
```lean
classical
rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
```

## Lean 4 List API Naming Conventions

Many Lean 3 / old Mathlib List lemma names have changed. Common pitfalls:

| What you want | Wrong name | Correct name |
|---|---|---|
| Map preserves indexing | `List.get_map` | `List.getElem_map` |
| Nodup + injection | `List.Nodup.get_inj` | `List.Nodup.get_inj_iff` |
| getLast? to getLast | `List.getLast?_eq_getLast` | `List.getLast?_eq_some_getLast` |
| getLast as getElem | `List.getLast_eq_get` | `List.getLast_eq_getElem` |

**Pattern for `head?` extraction:** Don't chain `head?_eq_getElem?` + `getElem?_eq_getElem`.
Instead, pattern-match directly:
```lean
cases path with
| nil => absurd hlast (by simp)
| cons a t => simpa using hhead
```

**`Matrix.IsSymm.apply` direction:** `hsymm.apply a b` gives `adj b a = adj a b`
(swapped from what you might expect). So `hsymm.apply (φ i) (φ j)` gives
`adj (φ j) (φ i) = adj (φ i) (φ j)` — useful when rewriting a hypothesis
that has `adj (φ j) (φ i)`.

## Closing character-table identities after `fin_cases j` (`![…] j` reduction)

In `A₅`/character-table proofs you often reduce to `<expr in j> = ![a,b,c,d,e] j` and finish with
`fin_cases j`. **`fin_cases j` substitutes the index as `⟨k, ⋯⟩` (a `Fin.mk`), which
`simp only [Matrix.cons_val_zero, Matrix.cons_val_one, …]` does NOT reliably reduce.** Use
`norm_num` (or `decide`) to evaluate `![…] ⟨k,⋯⟩` — those tactics see through the `Fin.mk`.

- Pure numeric per-class goal: `fin_cases j <;> norm_num` (this is what the working `indZ2_*` /
  `twisted_*` lemmas use).
- Per-class goal that ALSO needs a scalar hypothesis (e.g. a cube-root identity `z + z^2 = -1`
  for a nontrivial character): `fin_cases j <;> norm_num <;> linear_combination h`. `norm_num`
  reduces the matrix entries per branch (zeroing out the branches where the scalar coefficient is
  `0`); `linear_combination h` closes the one branch where the scalar survives, and is a no-op on
  the already-closed branches.

**Do not chase a misleading `ring` failure here.** If `linear_combination`/`ring` fails on a goal
that looks trivially true (`1/3*(z*3+z^2*3) = -1`), the cause is almost always an *unreduced*
`![…] ⟨k,⋯⟩` still lurking as an atom — not a `set`/`let` zeta-unfold or a division issue.
`clear_value`, `obtain`, and `field_simp` are red herrings; fix the matrix reduction (run
`norm_num` first) instead. (Cost ~8 iterations in #6624 before this was spotted.)

Related: `orderOf_eq_card_of_forall_mem_zpowers` (cyclic generator) returns `Nat.card α`, not
`Fintype.card α`; close the order fact with `... ; exact hH` where `hH : Nat.card ↥H = n`.

**When the five classes need DIFFERENT tactics, don't `fin_cases j <;> <uniform>`.** For an
induced character `Ind_{H}^{A₅}` where `H` is *nonabelian* (e.g. the order-12 `A₄` = `A4std`,
`indA4_nontriv_linear` #6659), each class rep is finished by a genuinely different argument (1a/2a
reduce to a conjugator count via a `σ=1`-on-involutions lemma; 5a/5b vanish because order 5 ∤ 12;
3a needs a twisted-sum reindexing over `↥H`). The robust shape is: prove five **separate
`have hjk : (ind σ).character (classRepA5 k) = ![…] k`** facts with clean *literal* indices `0..4`,
then close with `fin_cases j; · exact hj0; · exact hj1; …`. Do NOT state `have`s referencing
`classRepA5 2` *inside* a `fin_cases j` branch — `fin_cases` leaves the index as `(fun i ↦ i) ⟨2,⋯⟩`,
which will not `rw`-match a literal `classRepA5 2` (cost a full rewrite). The trailing
`fin_cases j <;> exact hjk` matches each `⟨k,⋯⟩` branch to the literal-`k` `have` by defeq.
End each `have` with `norm_num [Matrix.cons_val_zero, …_one, …_two, …_three, …_four,
Matrix.head_cons, Matrix.tail_cons]` — with *literal* (OfNat) indices, plain `norm_num` does NOT
reduce `![…] 2`; the explicit `Matrix.cons_val_*` set is required (unlike the `fin_cases`-`⟨k,⋯⟩`
form above, which plain `norm_num` handles).

**`group` does NOT close conjugation-of-powers.** `(d * y * d⁻¹) ^ n = d * y^n * d⁻¹` is left
unsolved by `group` (it normalizes but won't cancel across the power). Expand the power first:
`rw [pow_two, pow_two]; group` for `n=2`, `rw [pow_three', pow_three']; group` for `n=3`
(`pow_three' : a^3 = a*a*a`). This recurs whenever you transport an order fact through the
`exists_conj_H12`/`A4std` conjugator `d`.

## Fin Arithmetic in Proofs

When proving `Fin.ext` goals where the nat-level equality needs `omega`
(e.g., `chain.length - 2 + 1 = chain.length - 1`), **extract the nat proof first**:
```lean
have h_nat : chain.length - 2 + 1 = chain.length - 1 := by omega
congr 1; exact Fin.ext h_nat
```
Don't try `Fin.ext (by omega)` in term mode — omega often can't see the goal
through the Fin wrapper.

**Finset.erase parsing:** `S.erase a |>.erase b` in a type annotation
parses as `(S.erase a).erase b` in term position but `(x ∈ S.erase a).erase b`
in proposition position. Always use explicit parentheses: `(S.erase a).erase b`.

## BigOperators / Equiv reindexing gotchas (walk-sum & orbit-partition proofs, #6506)

Two recurring traps when expanding matrix products / reindexing sums over `Fin`-tuples:

- **`@[simps]`-generated `Equiv` `_apply` may not fire under a function head.** e.g.
  `Fin.consEquiv_apply` rewrote `(consEquiv (z,v)) 0` inside an `if`-condition but left
  `walkWeight N (consEquiv (z,v))` (the equiv passed *as a whole function* to another def)
  untouched, silently. Don't debug simp — the toFun is definitional, so bridge with a local
  `rfl`: `have hce : ∀ z w, (Fin.consEquiv (fun _ => ι)) (z, w) = Fin.cons z w := fun _ _ => rfl`
  then `simp only [hce, …]`. Same for `Equiv.sigmaFiberEquiv`, `Fin.succFunEquiv`, etc.
- **Dependent-summand big-operator lemmas whnf-timeout with an implicit function.**
  `(Fintype.prod_sum _).symm` on a goal whose `κ r = ({x // p x = r} → ι)` blew past 200k
  heartbeats at `whnf` while unifying the implicit `f`. Fix: pass `f` explicitly —
  `(Fintype.prod_sum (fun r q => ∏ x : {x // p x = r}, …)).symm`. Same for `Finset.prod_univ_sum`.
- **Cyclic-trace / walk expansion engine already exists** in
  `Chapter5/PermutationTraceWord.lean` (`Etingof.bigProd_apply`, `Etingof.trace_bigProd`,
  `walkWeight`): the `(x,y)` entry of an ordered matrix product as a sum over walks, and the trace
  as a sum over closed walks. Reuse before re-deriving. Peel the *first* matrix (`Fin.cons`) not
  the last — `Fin.cons`'s simp set (`cons_zero`/`cons_succ`) is far cleaner than `Fin.snoc`'s.

## obj↔concrete type bridge in `leaf_equalities` (quiver-rep collapse proofs)

When writing an orientation-generic `leaf_equalities`/collapse lemma over a
quiver representation, the invariant subspaces are typed
`W : ∀ v, Submodule F ((someRep_kQ …).obj v)`. The per-vertex object
`(someRep_kQ …).obj ⟨v, _⟩` is **definitionally** `Fin (k·(m+1)) → F`, but the
unifier will **not** reduce it to the concrete form — not even under an explicit
ascription `(W ⟨v,_⟩ : Submodule F (Fin (k·(m+1)) → F))`, which errors with a
"type mismatch … `(someRep_kQ …).obj ⟨v, ?m⟩` vs `Fin (k·(m+1)) → F`". This bites
hardest when the per-vertex dimension `…Dim` is defined by `match v.val with …`
(does not reduce through the `Fin 8` proof metavar); an `if … then … else …`
dimension reduces and avoids the wall (this is why some `_kQ_leaf_equalities`
families compile in obj-form and others do not).

**Consequence:** you cannot directly pass obj-typed `W ⟨v⟩` into a foundation
lemma stated over concrete `Fin (k·(m+1)) → F` spaces. Two fixes:
1. **Stay obj-form (preferred, mirrors the working D̃₇ family).** Build the
   leaf→center map `e` as a composite of the rep's **own** `mapLinear` along the
   relevant arrows (e.g.
   `(rep).mapLinear a20 ∘ (rep).mapLinear a32 ∘ (rep).mapLinear a43`), which is
   obj-typed by construction, and apply a space-generic criterion like
   `leaf_center_mem_iff_of_forward` (`FieldGenericETilde6.lean`). Then
   `simp only [someRep_kQ, someRepMap_kQ]` rewrites that composite to the concrete
   map (`blockEmbedAt_F …`, etc.) only where you actually need the concrete form.
2. Add obj-form wrappers of the concrete foundation lemmas.

A membership *statement* `concreteMap x ∈ W ⟨0,_⟩` (deposit into an obj-typed
submodule) elaborates if you ascribe the element to the obj type:
`(concreteMap x : (rep).obj ⟨0, by omega⟩) ∈ W ⟨0, by omega⟩` — the ascription
forces a default-transparency defeq that *does* reduce. The proof body still
needs fix (1) or (2).

### Working recipe for fix (1) on a `match`-`Dim` family (landed for Ẽ₇)

`etilde7Rep_kQ_{prefix,suffix}Arm_collapse` (`FieldGenericETilde7.lean`,
Section 3b, #4642) are the first obj-form collapse criteria actually carried to a
compile over a `match`-based `Dim`. Two non-obvious gotchas beyond "build the
obj composite + call `leaf_center_mem_iff_of_forward`":

1. **Instance wall + diamond.** `leaf_center_mem_iff_of_forward` (and any lemma
   with `[AddCommGroup Vᵢ] [Module F Vᵢ]`) needs those instances on the stuck
   obj-type `(rep).obj ⟨v,_⟩`; synthesis fails (reducible transparency won't
   reduce the `match`). Supply them with `letI` + `inferInstanceAs`, but use the
   **stuck index form**, not the reduced one:
   ```
   letI : AddCommGroup ((rep).obj ⟨v, by omega⟩) :=
     inferInstanceAs (AddCommGroup (Fin (someDim m ⟨v, by omega⟩) → F))
   letI : Module F ((rep).obj ⟨v, by omega⟩) :=
     inferInstanceAs (Module F (Fin (someDim m ⟨v, by omega⟩) → F))
   ```
   Using the **reduced** form `Fin (k*(m+1)) → F` typechecks but produces a
   `.toAddCommMonoid` that does **not** match the rep's bundled
   `instAddCommMonoid ⟨v,_⟩` (which is `Pi.addCommMonoid` at the *stuck* index),
   so the subsequent `W ⟨v⟩` argument fails with an "Application type mismatch …
   `this✝.toAddCommMonoid` vs `(rep).instAddCommMonoid ⟨v,_⟩`" instance diamond.
   The stuck-index form keeps `Pi.addCommMonoid` at the same index and the
   diamond closes.
2. **Conclusion membership index must be inferred, not re-proved.** Writing the
   conclusion as `… ∈ W₁ ⟨0, by omega⟩` while the element already pins vertex `0`
   (via the composite's target / the bound `x`'s type) makes the second
   `by omega` run against an already-unified metavar and report a spurious
   `No goals to be solved`. Write `… ∈ W₁ _` and let the index infer from the
   element type.

With both, containments come from pure invariance chaining
(`hW₁_inv a20 _ (hW₁_inv a32 _ (hW₁_inv a43 p hp))`) and injectivity descends via
`simp only [LinearMap.comp_apply, rep, repMap] at h` then the concrete
`*ArmComp_F_injective` (term-mode defeq unfolds the `match` at the leaves).

## Bundled-hom defeq blowup: `ρ g f = underlyingHom f` is cheap *only* in the defining file

`polyRightRep g f = rTransAlgHom (↑g) f` (a `Representation` applied, vs the
underlying `AlgHom`) holds by `rfl`. But proving it as a fresh `have ... := rfl`
— or relying on the defeq through `exact`/`show` — in a **downstream** file
**diverges at `whnf`** (times out even at 1.6M heartbeats): reconciling the two
FunLike coercion paths (`Representation`/`LinearMap` vs `AlgHom`) forces Lean to
whnf into `aeval`/the underlying function. The identical `rfl` is cheap *inside*
the file where the rep is defined (its `_apply_X` lemmas already use it).

Fix: put the equation as a named lemma in the **defining** file
(`theorem foo_apply (g) (f) : ρ g f = underlyingHom (↑g) f := rfl`), then
downstream use `rw [foo_apply]` — the proof is already compiled, so no `rfl`
re-elaboration. After the `rw`, close with the underlying lemma but let Lean
**infer the matrix/group argument with `_`** (`exact bar _ hf`, not `bar (↑g) hf`):
pinning `↑g` yourself reintroduces a second coercion spelling and re-triggers the
same whnf blowup. Symptom to recognize: `(deterministic) timeout at whnf` on a
line that is "obviously" `rfl` or a trivial `exact`.

**Same trap when proving `Commute`/equality *of* such endos** (e.g. left and
right `GL_N`-actions on `k[Xᵢⱼ]` commute). `exact AlgHom.congr_fun h_comp f` —
where `h_comp` equates the underlying `AlgHom.comp`s — blows up `whnf` (even at
6.4M heartbeats): Lean reconciles the `Module.End` product form against the
applied form through `aeval`. Make every step syntactic instead:
1. `apply LinearMap.ext; intro f` — **not** bare `ext f`, which over-applies into
   `MvPolynomial` *coefficient* extensionality (`f` becomes a `Finsupp` exponent).
2. `rw [Module.End.mul_apply, Module.End.mul_apply, ρ_apply, σ_apply, …]` (all
   `rfl`-lemmas) to reach the applied form on both sides.
3. Normalise the underlying lemma the same way and close by matching, not defeq:
   `have h2 := AlgHom.congr_fun h_comp f; rw [AlgHom.comp_apply, AlgHom.comp_apply] at h2; exact h2`.
With the fully-syntactic route the proof needs **no** `maxHeartbeats` bump at all.

### Unfolding a representation across a defeq carrier-alias: `change`, not `rw [… from rfl]`

When a representation's carrier is a `def`-alias (e.g. `AlgIrrepGL n lam k :=
↥(SchurModuleSubmodule k n lam.toNatWeight)`, `Theorem5_23_2Core.lean`) and you want
to unfold the rep to its concrete form (e.g. `algIrrepGLRepρ n lam k =
charTwistRep (detChar^…) (schurModuleRep …)`), do **not** use
`rw [show algIrrepGLRepρ … = charTwistRep … from rfl]`. Even though the equation is
`rfl`, `rw` fails: the LHS carries the *alias* instances (`Module.Dual k (AlgIrrepGL …)`)
while the RHS carries the *underlying* ones (`Module.Dual k ↥(SchurModuleSubmodule …)`),
so the rewrite motive over a dependent `glWeightSpaceℤ …`/`finrank` is ill-typed
("application type mismatch … `LinearMap.addCommGroup` vs `…toAddCommMonoid`"). Use
`change <goal with the rep unfolded>` instead — it reconciles the two instance paths by
defeq at default transparency (which unfolds the semireducible alias). Do this once at the
top so the whole proof lives on the underlying carrier, then `rw [dual_charTwistRep,
charTwistRep_charTwistRep, …]` are ordinary same-carrier rewrites. Diagnosed building
`coeff_formalCharacter_detTwist_dual` (#5553, `LinearDualDetTwistCharacter.lean`).

**A second instance path collides here: `FDRep`/`ModuleCat` vs native.** When you build a
weight eigenbasis with `exists_weight_eigenbasis (SchurModule k n lz)`, the resulting
`v : Basis _ k ↑(SchurModule k n lz).V` (and its `v.dualBasis`) carries the *FDRep* module
instances (`…V.obj.isModule`), which are **defeq-but-not-syntactically** the native
`SchurModuleSubmodule`/`schurModuleRep` instances that `algIrrepGLRepρ` is *defined*
through. Feeding `v.dualBasis` into `dual_diagUnit_dualBasis`/`charTwistRep_apply` over a
goal phrased with native `schurModuleRep` then errors mid-`rw`
("`AddCommMonoid (↥… →ₗ k)` vs `↑M.V`"). **Fix:** phrase the whole `h_span`/eigenbasis
derivation through `(SchurModule k n lz).ρ` (defeq to `schurModuleRep`, but carrying the
*same FDRep instances as `v`*) — i.e. `change` `M.ρ` to the nested twist written with
`(SchurModule k n lz).ρ`, and call `dual_diagUnit_dualBasis _ _ ((SchurModule k n lz).ρ) v …`.
Conversely, side goals with **no** eigenbasis vector in them (e.g. `IsAlgebraicRepresentation`
of the same `M.ρ`, fed by `IsAlgebraicRepresentation.dual (schurModuleRep …)`) should stay on
the **native** `schurModuleRep` form — pick the instance path that matches the *other* terms
in the goal. Also note `schurModule_isAlgebraic`/`iso_of_formalCharacter_eq_schurPoly` take
`k` as their first *explicit* arg (`variable (k : Type)`), while `schurModule_isAlgebraic`'s
`k` is unconstrained by `(N) (lam)` — pass `(k := k)` or it stalls on `IsAlgClosed ?m`.
Diagnosed building `linearDual_half_detTwist_contragredient` (#5544,
`LinearDualContragredientHalf.lean`).

### Degree-bound `Finset.sup` over an `AlgEquiv`-image: two whnf traps (#5486)

When `s` is a uniform degree bound `Finset.univ.sup (… natDegree (E (P …)) …)` for a heavy
algebra-equiv `E` (e.g. `glCoordToPoly : k[Xᵢⱼ,det⁻¹] ≃ₐ Polynomial k[Xᵢⱼ]`), two separate
`(deterministic) timeout at whnf`/`isDefEq` traps appear, *both* because Lean eagerly
whnf-reduces `E` (the AlgEquiv `trans`/FunLike coercion) when a defeq check stalls. Symptom:
the timeout is reported at the **enclosing `theorem`/docstring line** (col 0), not the real
tactic — bisect with `sorry` to find which `have` is at fault. Fixes (`Chapter5/DetClearing.lean`):

1. **`set s := …sup… with hs_def` makes `s` an opaque fvar**, so a term like
   `Finset.le_sup … : f x ≤ Finset.univ.sup f` no longer unifies with the goal `… ≤ s`, and
   Lean whnf-loops trying. **Fix:** `rw [hs_def]` to unfold `s` *before* `exact Finset.le_sup …`.
2. **A pair-indexed `Finset.sup (fun p : ι × κ => … E (P p.1 p.2) …)`** then forces
   `isDefEq` to compare `P (a,c).1 (a,c).2` with the goal's literal `P a c` — and that
   `Prod.fst`/`Prod.snd` projection comparison whnf-reduces `E` into a timeout. **Fix:** use a
   **nested** `sup (fun a => sup (fun c => … E (P a c) …))` so every `P a c` appears literally;
   bound via `le_trans (Finset.le_sup (mem_univ c)) (Finset.le_sup (mem_univ a))`, each `f`
   given explicitly. No projection ⇒ no whnf.

General rule reinforced (see the two bullets above and the abstract-scalar trick): never let
`rw`/`ring`/`exact`/`isDefEq` traverse a heavy `AlgEquiv`/`eval`/`det` term while searching for
a pattern or checking a defeq. Bridge equalities with `congrArg <explicit-motive-λ>` (no
kabstract search), prove per-term field arithmetic over **abstract scalars** `(have key : ∀ A D : k, …)`
then `exact key _ _ _`, and pin a polynomial→`Polynomial` factorization (`evalAtGL = eval₂ … ∘ E`)
once via `MvPolynomial.ringHom_ext` on generators rather than unfolding `E`.

## Extracting a simple sub-representation from an infinite-dim graded rep (#4922)

`Chapter5/SimpleSubrepExtraction.lean` builds `exists_simple_subrep_of_quotDetRep`
— from a nonzero `GL_N`-invariant submodule of `A/det` (infinite-dim) produce a
simple `FDRep` constituent with an injective equivariant embedding. Reusable recipe
when you need a *simple sub-representation* and `Theorem5_23_2_i` only gives the
vacuous `IsSemisimpleModule k` (k-vector-space) semisimplicity:

- **Finite-dim reduction in a graded rep:** lift a nonzero `w` to a polynomial of
  total degree `D`; `MvPolynomial.restrictTotalDegree σ k D` is a ready
  `Module.Finite k` submodule (instance), and the degree-preserving action keeps it
  invariant (decompose into `homogeneousComponent`s + `IsHomogeneous.totalDegree_le`).
  Push it through `mkQ` (`Module.Finite.map` is an instance) and intersect with the
  invariant `W` for a *nonzero, finite-dim, invariant* `M₀ ≤ W`.
- **Atom = simple sub-rep (the reusable lemma `Etingof.exists_isSimpleModule_le`):**
  a nonzero `k[G]`-submodule of `ρ.asModule` finite over `k` is Artinian over `k[G]`
  via `isArtinian_of_tower k inferInstance` (needs `IsScalarTower k k[G] ↥W`,
  auto), so `isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf` gives an atom;
  `isSimpleModule_iff_isAtom.mpr` + push forward along `W.subtype`
  (`Submodule.equivMapOfInjective ... |>.symm` + `IsSimpleModule.congr`) gives the
  simple submodule. (`IsArtinian` is an `abbrev` for `WellFoundedLT (Submodule …)`,
  so `IsWellFounded.wf` supplies the `WellFounded` term directly.)
- **`asModule` ↔ `asSubmodule` simplicity bridge:** packaging the atom as an
  `FDRep.of σ.toRepresentation` forces proving `IsSimpleModule k[G]
  (σ.toRepresentation).asModule`, which is NOT defeq to `IsSimpleModule k[G]
  ↥σ.asSubmodule` (the `Module k[G]` instances differ — `:= h` fails). Build the
  k[G]-linear equiv `(σ.toRepresentation).asModule ≃ₗ[k[G]] ↥σ.asSubmodule` by hand:
  carriers coincide on `σ.toSubmodule` (use `σ.toRepresentation.asModuleEquiv`, which
  is `LinearEquiv.refl`, to access `.1`/`.2`); `map_smul'` reduces via
  `MonoidAlgebra.induction_linear`, and the `single g t` case closes by **`rfl`**
  after `rw [Representation.single_smul, Representation.single_smul]` (both sides are
  `t • ρ g y`). Then `IsSimpleModule.congr`. Mathlib's
  `Subrepresentation.{asSubmodule, ofSubmodule', subrepresentationSubmoduleOrderIso}`
  give the order iso between subrepresentations and `Submodule k[G] ρ.asModule`.
  **Cleaner reusable build of that same `↥σ.asSubmodule ≃ₗ[k[G]] σ.toRepresentation.asModule`
  bridge** (no by-hand `map_smul'`, #5487 `asSubmodule_semisimple_of_toRep`,
  `Chapter5/PolynomialGLSemisimple.lean`): the inclusion `σ.toSubmodule.subtype` is a
  `k`-intertwiner `σ.toRepresentation → ρ` (`hf := fun _ _ => rfl`), so
  `Representation.asModuleHomOfIntertwiner σ.toSubmodule.subtype hf` is a `k[G]`-linear
  `σ.toRepresentation.asModule →ₗ[k[G]] ρ.asModule`, injective (its function *is* `subtype`
  via `asModuleHomOfIntertwiner_apply`, so `Subtype.coe_injective`), with
  `LinearMap.range = σ.asSubmodule` (`SetLike.ext`; `mem_range ↔ ∈ σ.toSubmodule ↔
  mem_asSubmodule_iff`). `(LinearEquiv.ofInjective F _).trans (LinearEquiv.ofEq _ _ hrange)`
  then `IsSemisimpleModule.congr`. NB `LinearEquiv.refl` between the two does NOT typecheck —
  the `Module k[G]` instances (`Submodule.module` restriction vs `Representation.asModule`)
  are not defeq. (`asModuleHomOfIntertwiner` lives in `namespace Representation`, so qualify
  it `Representation.asModuleHomOfIntertwiner` from another namespace.)

- **Total-degree grading of a polynomial `GL_N`-rep into `GL`-stable homogeneous pieces
  (#5487, the general reductivity reduction):** to remove the homogeneity hypothesis of
  `decompose_polynomial_gl_rep` (which needs all weights concentrated in one total degree),
  the `GL`-stable degree-`d` component is `degComponent d := ⨆_{∑μ=d} glWeightSpace μ`. Its
  `GL`-stability is NOT free from the weight-space definition (`GL` does not preserve
  individual weight spaces) — prove `degComponent d = eigenspace(M.ρ(scalarGL t₀), t₀^d)`
  for a central scalar `t₀` of infinite order (`(2:k)` in char 0), then it is an eigenspace
  of a *central* operator (`scalarGL` central via `Matrix.scalar_commute`), hence `GL`-stable.
  The eigenspace identity is the generic modular-lattice fact `T i ≤ E i` + `iSupIndep E`
  (here `Module.End.eigenspaces_iSupIndep`, reindexed by the injective `d ↦ t₀^d`) +
  `⨆ T = ⊤` ⟹ `T = E` (`eq_of_le_iSupIndep_iSup_top`). Each component's `h_span`/`h_homog`
  come from `glWeightSpace_restrict` (weight space of a sub-rep = `comap subtype` of the
  ambient's) + `glWeightSpace_iSupIndep`; assemble all degrees with
  `isSemisimpleModule_of_isSemisimpleModule_submodule'` (its `⨆ p = ⊤` proved through
  `restrictScalars` back to the `k`-level `⨆ degComponent = ⊤`). `scalarGL_eq_noncommProd`
  is `private` in `PolynomialRepEmbedding` — copy it locally if you need the
  `scalarGL t = ∏ᵢ diagUnit i t` product to compute the scalar action on a weight space.
- **Gotcha:** `MvPolynomial.mem_restrictTotalDegree` takes the index type `σ` and
  the degree `m` as *explicit* positional args before `p` (`mem_restrictTotalDegree
  (Fin N × Fin N) D p`), even though `R` is implicit — term-mode calls need all
  three. `rw` forms infer them fine.
- **`open MvPolynomial` inside `namespace Etingof.*` opens the WRONG namespace.**
  `EvalEqOnGL.lean` declares an `Etingof.MvPolynomial` namespace, so a bare
  `open MvPolynomial` inside any `namespace Etingof.Foo` resolves to *that* (the
  relative match wins), and `monomial`/`coeff`/`C` come up as "unknown identifier"
  (autoImplicit then mis-reports them as "function expected at monomial"). Use
  `open _root_.MvPolynomial`. Same trap for any root namespace shadowed by an
  `Etingof.<Name>` subnamespace.
- **Reading the underlying object from an `FDRep.of σ.toRepresentation` carrier:**
  `(FDRep.of ρ').ρ g w`'s coercion to the ambient type is not auto-inserted, but the
  carrier is defeq to `↥σ.toSubmodule`, so `σ.toSubmodule.subtype` typechecks directly
  as a `LinearMap` *from the FDRep carrier* (`def polyOf := (homog…).subtype`). Use it
  to read elements / the `.ρ` action on the ambient module (`polyOf (M.ρ g w) =
  ambientRep g (polyOf w)` holds by `rfl`), sidestepping all `.V`/`FGModuleCat` coe pain.
- **`rw` won't close `finrank ↥A = finrank ↥A` when `A` came from rewriting across two
  *defeq-but-distinct* FDRep carriers** (e.g. after `rw [glWeightSpace_twistFDRep_pos]`
  turning `glWeightSpace twistFDRep μ` into `glWeightSpace polyRightDegreeFDRep …`): the
  two `↥(...)` carry mismatched `Module` instances, so the post-`rw` `rfl` silently fails
  and you get "unsolved goals ⊢ ↑A = ↑A". Close it with a `congrArg` term instead:
  `Nat.cast_inj.mpr (congrArg (fun w => Module.finrank k (glWeightSpace k N M w)) hweight)`
  (or prove the `ℕ` equality first to dodge the extra `Nat.cast` layer). Same fix for any
  `finrank`/`glWeightSpace` equality that "should be `rfl`" but isn't.
- **Stars-and-bars count:** `#{f : Fin N → ℕ | ∑ f = m}` is `Finset.piAntidiag univ m`;
  its card is `Nat.multichoose N m` via `Finset.map_sym_eq_piAntidiag` +
  `Finset.sym_univ` + `Sym.card_sym_fin_eq_multichoose`. Then
  `Nat.multichoose_eq`/`Nat.choose_symm` give `= C(m+N-1, N-1)` (needs `N ≥ 1`, which
  `Fin.pos j` supplies inside a `∏ j : Fin N`). For a product of independent column
  counts, biject to `Fintype.piFinset (fun j => piAntidiag …)` and use
  `Fintype.card_piFinset`.

**Workflow note:** `lake build <YourNewLeafModule>` is authoritative for a leaf file
that nothing else imports; building the *chapter aggregator* rebuilds all ~120
project files from source (`lake exe cache get` only fetches Mathlib oleans, not the
project's), which is slow and adds no signal for a leaf addition. After a clean
standalone build, just grep for declaration-name collisions and trust CI for the
full graph rather than waiting on the aggregator locally.

## `End X` ring-structure gotchas (endomorphism-ring proofs: Krull–Schmidt, Morita)

`CategoryTheory.End X := X ⟶ X` carries `Monoid`/`Ring` instances (preadditive), but
`End X` is a *semireducible def* over the morphism type, and that bites instance search:

- **`f ^ n` on an *ascribed* morphism fails to synthesize the power.** Writing
  `(biprod.map a b : End (K ⊞ I)) ^ n` errors with `failed to synthesize HPow (K ⊞ I ⟶ K ⊞ I) ℕ`
  — the ascription unfolds `End` to the `⟶` type *before* instance search, and `End.monoid`
  is keyed on head symbol `End`, not `Quiver.Hom`. **Fix:** carry the endomorphism as an
  explicit `End`-typed *variable* (a lemma parameter `(M : End (K ⊞ I))` with a hypothesis
  `hM : (M : K ⊞ I ⟶ K ⊞ I) = biprod.map a b`), then `M ^ n` resolves. Same for `f ^ n` on
  any constructed-then-ascribed morphism: bind it to a variable first.
  - **Corollary (`set`-binding an End power as a bare morphism kills `^`, #5274).** `(f : X ⟶ X) ^ n`
    *does* elaborate (Lean resolves `^` at `End X` because `f : End X` drives it), but
    `set F : X ⟶ X := (f : X ⟶ X)` then `F ^ n` fails with `failed to synthesize HPow (X ⟶ X) ℕ ?` —
    `F` is now a bare `X ⟶ X` fvar with no `End` head to trigger `End.monoid`. **Fix:** don't `set`
    the base morphism; `set` the *whole power* instead — `set g : X ⟶ X := (f : X ⟶ X) ^ n with hg`,
    `set g2 := (f : X ⟶ X) ^ (2 * n)` — and phrase the proof over the plain morphisms `g`, `g2`
    (their type is `X ⟶ X`, no `^` needed downstream). `g ≫ g = g2` then closes by
    `rw [hg, hg2, two_mul, pow_add, End.mul_def]` (the `End.mul_def` turns the `pow_add` `*` back
    into `≫`).
  - **Precedence: `^` binds *looser* than `≫`.** `(f : X ⟶ X) ^ n ≫ (f : X ⟶ X)` parses as
    `(f : X ⟶ X) ^ (n ≫ (f : X ⟶ X))` (→ `CategoryStruct.comp n` type error). Always parenthesise
    the power: `((f : X ⟶ X) ^ n) ≫ (f : X ⟶ X)`.
- **Multiplication is *reversed* composition:** `End.mul_def : x * y = y ≫ x`, `End.one_def :
  (1 : End X) = 𝟙 X`. So `pow_succ` then `End.mul_def` turns `x ^ (n+1)` into `x ≫ x ^ n`. A
  block-power induction `(biprod.map a b) ^ n = biprod.map (a ^ n) (b ^ n)` closes with
  `rw [pow_succ, End.mul_def, ih, hM, biprodMap_comp]; congr 1` (rewrite `ih` *before* `hM` so
  the `M ^ n` subterm is gone before `M` is substituted — otherwise you re-introduce
  `(biprod.map a b) ^ n` and the HPow failure returns).
- **`isUnit_iff_isIso` is in `CategoryTheory`, NOT `End`** (`open CategoryTheory` → bare
  `isUnit_iff_isIso (f : End X) : IsUnit f ↔ IsIso f`). Pair with `End.isUnit_iff_isIso`-style
  guesses being wrong.
- **Transport nilpotence/units along an iso with `Iso.conj`** (`Mathlib/CategoryTheory/Conj.lean`):
  `e.conj : End X ≃* End Y`, `e.conj_apply : e.conj f = e.inv ≫ f ≫ e.hom`. It is only a
  `MulEquiv`, but `conj_apply` lets you compute `e.conj 0 = 0` by `simp`, so it carries
  `IsNilpotent` (via `map_pow` + that zero fact) and `IsUnit` (`IsUnit.map e.conj`) both ways.
  Conjugating `f = e.hom ≫ M ≫ e.inv` is exactly `f = e.symm.conj M` (`e.symm.inv = e.hom`).
- **`ext` may not fire on `𝟙 (X ⊞ Y) = biprod.map …`;** use `apply biprod.hom_ext'` (out of a
  biproduct, post-compose with `inl`/`inr`) or `biprod.hom_ext` (into one, with `fst`/`snd`),
  then `simp`. `biprod.map`-composition (`biprod.map a b ≫ biprod.map c d = biprod.map (a≫c)(b≫d)`)
  and `biprod.map 0 0 = 0` both close by `ext <;> simp` — there is no `biprod.map_id`/`map_map`.
- **`End X` is *noncommutative*, so most of Mathlib's `IsLocalRing` consumer API is unusable** —
  it silently assumes `CommRing`/`CommSemiring` (or `IsDedekindFiniteMonoid`). Specifically
  `IsLocalRing.isUnit_or_isUnit_one_sub_self` (CommRing), `isUnit_or_isUnit_of_isUnit_add` and
  `nonunits_add` (CommSemiring), `isUnit_of_mul_isUnit_right` (comm), and
  `IsIdempotentElem.iff_eq_one_of_isUnit` (`IsDedekindFiniteMonoid`) all fail to synthesize on
  `End X`. **Re-derive from the class field `IsLocalRing.isUnit_or_isUnit_of_add_one {a b} (h : a +
  b = 1) : IsUnit a ∨ IsUnit b`**, which holds for any `Semiring`. From it: `IsUnit a ∨ IsUnit (1 -
  a)` via `(by abel : a + (1 - a) = 1)`; "unit summand of a unit finite sum" via
  `Finset.sum_induction` with `nonunits` closure proved through `isUnit_or_isUnit_of_add_one`; and
  "idempotent unit ⇒ `= 1`" by left-multiplying `a*a = a` by the inverse unit (works in any
  `Monoid`). See `Chapter9/KrullSchmidt/Exchange.lean` for all four helpers.
- **`IsIdempotentElem (g : End Z)` written with a type *ascription* `(g : End Z)` fails** with
  `failed to synthesize Mul (Z ⟶ Z)` (the ascription unfolds `End` before instance search, same
  semireducible-def bite as `^`). **Fix:** pass the type as the named implicit —
  `IsIdempotentElem (M := End Z) g` with `g : Z ⟶ Z` — then feed `hg : g ≫ g = g` *directly*
  (`IsIdempotentElem (M := End Z) g` is defeq to `g * g = g` is defeq to `g ≫ g = g`). For the
  output, an idempotent in a local ring being `0`/`1` (End ring `1 = 𝟙` via `End.one_def`)
  bridges back to morphism `g = 0 ∨ g = 𝟙 Z` cleanly; wrap this once and consume the morphism-level
  result so callers never touch `End`-vs-`Hom` zero/one mismatches.
- **`set_option … in` must precede the doc comment, not sit between `/-- … -/` and the theorem**
  (otherwise: `unexpected token 'set_option'; expected 'lemma'`). To silence
  `linter.unusedFintypeInType` on a theorem whose `[Fintype κ]` is only used to form `⨁` in the
  type, put `set_option linter.unusedFintypeInType false in` on the line *above* the docstring.
- **Round-tripping a functor/decomposition through a *derived* module (e.g. `forwardRep`/
  `vertexSpace` applied to `reverseModule R`) — three frictions that cost many iterations
  (see `Chapter2/Discussion_quiver_rep_bijection.lean`):**
  1. *Instances on the derived carrier.* A `noncomputable def` module structure (`reverseModule R :
     Module (PathAlgebra k Q) (⊕ᵢ …)`) is not an instance. Threading `letI := reverseModule R;
     haveI := …isScalarTower R` through *every* statement is fragile (the `letI` inside
     `…isScalarTower`'s type leaves `k`/the tower stuck with metavariables). Instead
     `attribute [local instance] reverseModule` once, then a clean
     `local instance … : IsScalarTower k (PathAlgebra k Q) (⊕ᵢ …) := reverseModule_isScalarTower R`.
     Even then, generic defs like `vertexProj`/`vertexSpace`/`forwardRep` leave `k` (and sometimes
     `V`) floating → `IsScalarTower ?k …` / `Field ?k` "stuck" errors; pin them explicitly with
     `(k := k) (V := …)` at the call site.
  2. *Family-spelling defeq.* `DirectSum Q F` with `F i = R.obj (op i)` is *definitionally* but not
     *syntactically* `⨁ i, ↥(vertexSpace i)`, so `DirectSum.coeLinearMap_lof` / `component.of` /
     coercion-to-ambient (`(z : V)`) do not fire or even elaborate (the coercion resolver does not
     see `R.obj (op i)` as a `SetLike` subtype). Bridge with a one-line `rfl`/defeq lemma stated in
     the projection spelling (`coeV_lof i z : coeV (lof … i z) = (vertexSpace i).subtype z :=
     DirectSum.coeLinearMap_lof _ i z`) and use `(submodule).subtype z` instead of `(z : V)`.
  3. *Coe-head mismatch in naturality.* `apply Subtype.ext` yields `Subtype.val`, but
     `arrowMap_coe_apply`/your `…_coe` lemmas are stated with the `SetLike`/`↑` coe, and a
     structure field `app := (equiv).toLinearMap` puts a `toLinearMap`-coe between you and the
     equiv-coe `…_coe` lemma — so `rw`/`simp` silently fail to match. Don't fight it lemma-by-lemma:
     `change` the whole goal into a fully *definitionally-equal* computed form (here all the bridging
     coe lemmas — `ofLinear` apply, `codRestrict`/`restrict` `.val`, `reverseModule_smul_def`,
     `…_coe` — are `rfl`), e.g. `change lof Y.unop (R.mapLinear e x) = toEnd R (ofArrow e.unop)
     (lof X.unop x)`, then finish with the *non*-`rfl` rewrites (`toEnd_ofPath`, `pathEnd_mk`, …).
- **A `QuiverRepresentation` `obj` is only `AddCommMonoid`** (it is built over `CommSemiring k`).
  So a module assembled from rep vertex spaces (`⊕ᵢ R.obj (op i)`) is *not* an `AddCommGroup`, and
  any decomposition machinery requiring `[AddCommGroup V]` (e.g.
  `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, which needs subtraction) cannot be
  applied to it. Keep the bulk of the machinery at `[AddCommMonoid V]` and split *only* the
  group-requiring lemma (`isInternal_vertexSpace`) into its own `[AddCommGroup V]` section.
- **There is no `QuiverRepresentation.Iso` reachable from Chapter 2** (it lives in Chapter 6, which
  *imports* Chapter 2 — using it would be circular, and redefining it clashes). For a Chapter-2
  representation isomorphism, use `Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂` (note: `k` and `Q` are
  *explicit*) and expose the per-vertex `LinearEquiv`s separately as the witness that the
  components are isos.

## Pseudoelement diagram chases in an abelian category (Fitting/Krull–Schmidt, #5274)

`Abelian.Pseudoelement` (`Mathlib/CategoryTheory/Abelian/Pseudoelements.lean`) is the clean tool for
"diagram chase" proofs that a categorical map is mono/epi/iso — e.g. that the image restriction
`g' = image.ι (fⁿ) ≫ factorThruImage (fⁿ)` is iso once the `im (fⁿ)` and `ker (fⁿ)` chains stabilise
(`Etingof.exists_pow_stabilizes`, `Chapter9/KrullSchmidt/Length.lean`). Setup and gotchas:

- **Activate the coercions with `attribute [local instance]`, NOT `open scoped`.** The sort coercion
  `objectToSort` (lets `X : C` be the type of pseudoelements), `homToFun` (lets `f a` mean
  pseudo-application), and `overToSort` are `scoped[Pseudoelement] attribute [instance]`, but
  `open scoped Pseudoelement` / `open scoped CategoryTheory.Abelian.Pseudoelement` did **not** turn
  them on (symptoms: `∀ y : X` → "type expected, got (X : C)"; `f a` → `Function expected at ?m`).
  The reliable incantation (also given in the file's own header comment) is
  `attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
  CategoryTheory.Abelian.Pseudoelement.homToFun CategoryTheory.Abelian.Pseudoelement.overToSort`.
  Qualify the lemmas fully (`Abelian.Pseudoelement.comp_apply` / `.apply_zero` / `.zero_apply` /
  `.pseudo_exact_of_exact` / `.pseudo_surjective_of_epi` / `.pseudo_injective_of_mono` /
  `.zero_of_map_zero` / `.mono_of_zero_of_map_zero` / `.epi_of_pseudo_surjective`) — bare
  `comp_apply` collides with `CategoryTheory.comp_apply`.
- **Prove mono/epi/iso the pseudoelement way.** `mono_of_zero_of_map_zero f : (∀ a, f a = 0 → a = 0)
  → Mono f`; `epi_of_pseudo_surjective f : Function.Surjective f → Epi f`; then
  `isIso_of_mono_of_epi f` (abelian is `Balanced`). `comp_apply f g a : (f ≫ g) a = g (f a)`,
  `apply_zero f : f 0 = 0`, `zero_apply Q a : (0 : P ⟶ Q) a = 0` drive the algebra.
- **Bridge subobject equality ⟷ pseudoelement membership via exactness.** To turn
  `kernelSubobject g2 = kernelSubobject g` (a `Subobject` equality from chain stabilisation) into the
  pseudoelement fact `g2 w = 0 → g w = 0`: build the exact short complex
  `ShortComplex.mk (kernelSubobject g).arrow g (kernelSubobject_arrow_comp g)` — exact because
  `imageSubobject (mono).arrow = Subobject.mk (.arrow) = that subobject` (`ShortComplex.exact_iff_image_eq_kernel`
  + `imageSubobject_mono` + `Subobject.mk_arrow`) — then `pseudo_exact_of_exact` gives
  `∃ a, (kernelSubobject g2).arrow a = w`, and `(kernelSubobject g).arrow ≫ g = 0`
  (`kernelSubobject_arrow_comp`) finishes. Dually for images, use `factorThruImageSubobject`
  (epi → `pseudo_surjective_of_epi`) and `imageSubobject_arrow_comp`.
- **Never `rw` a morphism that also appears in a dependent type position.** `rw [← hpi]` to turn
  `g (i a)` into `(p ≫ i)(i a)` fails with `motive is not type correct` because `g` reappears in the
  type of `i = Abelian.image.ι g` (`i : Abelian.image g ⟶ X`). **Fix:** route through an
  *intertwining application lemma* stated once as `∀ y, i (p y) = g y` (from `p ≫ i = g` via
  `← comp_apply`), and rewrite with *that* (`← hint (i a)`) instead of rewriting `g` directly — it
  never abstracts the `g` buried in `i`'s type.
- **`FGModuleCat` / `Core`-groupoid naturality extraction (#5643, `Chapter7/Example7_3_2.lean`).**
  Etingof's `FVect'_k` (f.d. spaces, isomorphisms only) is `CategoryTheory.Core (FGModuleCat k)`;
  a functor out of it is `where obj X := Core.mk …; map f := ⟨…f.iso…⟩` (`CoreHom` wraps an `X.of ≅
  Y.of`). To turn a `NatIso`/`NatTrans` naturality square into a plain linear-map equation, apply
  `congrArg (fun p => p.iso.hom.hom.hom)` to `ε.hom.naturality g`, then `simp only [Functor.id_map,
  coreCategory_comp_iso, Iso.trans_hom, FGModuleCat.hom_hom_comp, LinearEquiv.toFGModuleCatIso_hom,
  <your F_map .iso rfl-lemma>]`. Two Mathlib gaps bite: (a) **no roundtrip lemma**
  `isoToLinearEquiv (e.toFGModuleCatIso) = e` — prove it inline by `LinearEquiv.toLinearMap_injective;
  ext x; rfl` (or just `ext x; rfl`); (b) **`ModuleCat.Hom.hom (ConcreteCategory.ofHom φ).hom = φ` is
  `rfl` but has NO simp lemma**, so `simp` leaves `ofHom` noise stuck. Don't fight it: **re-ascribe the
  stuck hypothesis to its clean defeq type** — `have hx2 : (η (a x)) (a w) = (η x) (a.symm (a w)) := hx`
  typechecks through all the rfl-reductions at once — then finish with the one genuinely-non-rfl step
  (`rw [LinearEquiv.symm_apply_apply] at hx2`). A component of a `NatIso` is bijective via
  `(FGModuleCat.isoToLinearEquiv (ε.hom.app X).iso).bijective`.

## A new global `Module`/scalar instance perturbs elaboration of *earlier* defs (base-change, restricted scalars, #6020)

When you add a global `noncomputable instance : Module A M` (e.g. restricting an
`L ⊗[K] A`-module `bcMod` along `includeRight` to view `L ⊗[K] V` as an `A`-module via
`Module.compHom`), that instance re-enters typeclass search for **every subsequent term** —
including elaboration of defs that already compiled before you added it. Two concrete failures
seen in `Chapter3/Problem3_8_4_Power.lean`:

- **Looping/slow instance synth.** Unfolding `rep`/`repTensor` (type `A →ₐ[K] Module.End L (L ⊗[K] V)`)
  now triggers a `(deterministic) timeout at typeclass … Algebra K (Module.End L (L ⊗[K] V))`,
  even though the *same* term compiles fine in the file that defines it. The extra `Module A (L ⊗[K] V)`
  gives TC new (dead-end) paths to explore.
- **Diamond in `Semiring K` / `Field` paths.** `TensorProduct.comm K L V ≪≫ₗ …` fails to unify with
  "synthesized … `Field.toSemifield.toSemiring`" vs "expected … `Field.toSemifield.toDivisionSemiring.toSemiring`".

**Fix: order declarations so everything that elaborates the perturbed terms comes *before* the
instance.** Prove the `repTensor`-on-`tmul` reduction and the underlying `K`-linear equiv
(`TensorProduct.comm`/`congr`/`piScalarRight`) and its `_tmul` simp lemma first; declare the
`Module A M` instance only afterward; then the smul lemmas and the `A`-linear packaging. A scratch
file (`import`ing the same deps, sans the instance) confirms in seconds whether a given term
elaborates without the instance in scope.

## Upgrading a `≃ₗ[K]` to `≃ₗ[A]`: fresh `→ₗ[A]` + `ofBijective`, not `{ e.toAddEquiv with … }`

To promote a `K`-linear equiv `e : M ≃ₗ[K] N` that is *also* `A`-linear (A a `K`-algebra,
`SMulCommClass K A V` automatic from `IsScalarTower K A V`) to an `A`-linear equiv, do **not**
write `{ e.toAddEquiv with map_smul' := … }` — it fails with
"synthesized `<yourInstance>` / inferred `TensorProduct.instModule`" because the reused `AddEquiv`
drags the `K`-module along. Instead build a genuine `M →ₗ[A] N` from scratch
(`toFun := e`, `map_add' := e.map_add`, `map_smul' := …` by `TensorProduct.induction_on`), then
`LinearEquiv.ofBijective thatMap e.bijective`. `⇑thatMap` is defeq to `⇑e`, so `e.bijective`
typechecks directly. `A`-linearity of the `tmul` case is `smul_comm (c : K) (a : A) v` after the
scalar identity `a • (l ⊗ v) = l ⊗ (a • v)`.

## Induced representations: the `Rep.indResAdjunction` universe trap

For isomorphisms between induced representations (`Representation.ind`/`IndV`,
Chapter 5 induction items), the slick categorical route — `Rep.indResAdjunction`
+ `Adjunction.comp` + `Adjunction.leftAdjointUniq` to get e.g. induction-in-stages
`Ind_ψ(Ind_φ τ) ≅ Ind_{ψ∘φ} τ` — **only works when `univ(V) ≥ univ(G)`.**
`indResAdjunction` is stated at a *single* universe `Rep.{max w v' u}` (see its
`resFunctor.{max w v' u}` and `indResHomEquiv (A B : Rep.{max w v' u} …)`), so
composing adjunctions and applying the functor iso at a genuine `Rep.of ρ`
(module `V : Type u_V`) fails with `stuck at solving universe constraint` whenever
`u_V < u_G`. A theorem with independent `V G : Type*` is not provable this way.

**Fix: build the iso explicitly at the module level** (`Coinvariants.lift` /
`TensorProduct.lift` / `Submodule.quotEquivOfEq`), which has no universe coupling.
Useful facts: `leftRegular ℂ G g` is *left* multiplication by `single g 1`
(`ofMulAction_single`); `ind φ τ h` acts on `⟦a⊗v⟧` by *right* mult `a * single h⁻¹ 1`;
`ind φ τ h = Coinvariants.map ⟨(lmapDomain (·*h⁻¹)).rTensor _, _⟩`, and the `G`-action
touches only the `ℂ[G]` factor. When two inductions share the module `ℂ[G]⊗V` and
differ only by relabelling the coinvariance subgroup along an iso `σ` (the `f∘σ` vs
`f` case), their `Coinvariants.ker`s are *equal* (generating set reindexed by `σ`),
so the iso is `Submodule.quotEquivOfEq` and its equivariance is `rfl`-on-generators
after `ind_apply`/`Coinvariants.map_mk`/`quotEquivOfEq_mk`. Keep the composite-hom
and inner-rep in *syntactic* agreement between the kernel-equality lemma and the
`quotEquivOfEq` call (pass the composite `fφ` and inner rep `τ'` as explicit args
with `hfφ`/`hτ` equations and `subst` them) — else defeq-but-not-syntactic forms
like `H.subtype.comp K.subtype` vs `K.subtype.comp σ` make `exact`/`rw` fail.

### Two follow-on gotchas when proving `IndV` isomorphisms via `Coinvariants.lift`

- **`Representation.IndV.mk` is a `noncomputable abbrev`, so `simp` unfolds it.**
  `Representation.IndV.mk φ ρ h = Coinvariants.mk _ ∘ₗ TensorProduct.mk _ _ _ (single h 1)`.
  Inside a `hom_ext` proof, `simp only [LinearMap.comp_apply]` (or any `simp` touching the
  composition) rewrites `(f ∘ₗ IndV.mk φ ρ h) z` all the way to
  `f (Coinvariants.mk _ (TensorProduct.mk .. (single h 1) z))`, after which `rw [fwd_mk]` /
  `Representation.ind_mk` (stated with the folded `IndV.mk`) no longer match. Fix: prove the
  generator identity as a standalone pointwise `have hpt : ∀ h z, f (IndV.mk φ ρ h z) = …` (these
  `rw`s match because the argument stays `IndV.mk φ ρ h z`), then discharge the `hom_ext` +
  `LinearMap.ext` goal with a definitional `change f (IndV.mk φ ρ h z) = … ; exact hpt h z`
  (`LinearMap.comp_apply`/`mulLeft_apply`/`id` are all rfl, so `change` bridges it). Never `simp`
  the composition itself.

- **Unit-inverse coercions get normalised by a `norm_cast` simp lemma.**
  `((χ g : ℂˣ)⁻¹ : ℂ)` elaborates as `↑((χ g)⁻¹)` but the `@[simp, norm_cast]` lemma
  `Units.val_inv_eq_inv_val` rewrites it to `(↑(χ g))⁻¹` after any `simp`/`field_simp`. So
  `Units.inv_mul`/`Units.mul_inv` (pattern `↑u⁻¹ * ↑u`) stop matching; use
  `inv_mul_cancel₀ (Units.ne_zero _)` / `mul_inv_cancel₀ (Units.ne_zero _)` on the complex-inverse
  form instead. To convert a bare `(↑(χ g))⁻¹` into `↑(χ g⁻¹)` (e.g. to feed a twisted
  coinvariance lemma `IndV.mk (κ·x) (χ κ • w) = IndV.mk x w`), `rw [map_inv, Units.val_inv_eq_inv_val]`
  in reverse via a small `have`. For character sums, reindex the defining sum of `e_χ` with
  `Equiv.mulLeft k` and `Equiv.sum_comp` to get `of k * e_χ = χ(k) • e_χ`.

### Orbit-method assemblies: use the character formula, not base-point independence

When assembling a `Theorem5_27_1`-style classification (`heisenberg_classification` is the
worked example), note the exposed existential only gives (i)-(vi): irreducibility, iso⟹orbit,
completeness, **character formula (iv)**, dimension, functoriality. It does **not** expose
"same orbit ⟹ `V` iso" (base-point independence). Do not try to prove pairwise
non-isomorphism from (ii)'s opaque `transport`, or completeness by moving `χ` to a
representative — both need the unexposed lemma. Instead route everything through (iv):
compute closed-form characters of each `V(χ, U)`, then use `FDRep.char_iso` (iso ⟹ equal
character) for distinctness and `Etingof.charEq_iso` (equal character ⟹ iso) for the
completeness base-point move. The inner sum in (iv) collapses via `AddChar.sum_mulShift`
(package `ζ^(·)` as an `AddChar (ZMod p) ℂ` with `AddChar.zmodChar` +
`zmodChar_primitive_of_primitive_root`). `charEq_iso` needs `Finite` of the semidirect
product — supply `Finite.of_equiv _ SemidirectProduct.equivProd.symm`.

### Two small tactic gotchas (cost several iterations)

- **`ext` on a `MonoidHom` valued in `ℂˣ` (or any group) picks the *additive* extensionality**,
  turning the goal into `↑(Additive.toMul ((MonoidHom.toAdditiveRight f) a)) = …`, which then
  fails `exact`/`Units.ext`. Use `refine MonoidHom.ext fun a => ?_` explicitly instead of `ext a`.
- **A `let`-bound `Fintype` index type blocks `Fintype.card_sum` / `Fintype.sum_sum_type` `rw`.**
  If you write `let ι := A ⊕ B`, do *not* also add `haveI : Fintype ι := inferInstanceAs …` — the
  named instance is an opaque fvar, so `@Fintype.card ι this` never matches the `instFintypeSum`
  in `Fintype.card_sum`. Let synthesis find the instance transparently, and state the
  decomposition as a defeq `have hcard : Fintype.card ι = Fintype.card A + Fintype.card B :=
  Fintype.card_sum` (likewise `Fintype.sum_sum_type _`), then `rw [hcard]`.
- **Never put `ring` first in a `first | … | …` block** (cost ~4 build cycles). When `ring`
  cannot close a goal it does *not* reliably fail — recent Mathlib falls back to `ring_nf`,
  emitting "Try this: [apply] ring_nf" and **succeeding without closing the goal**, so `first`
  stops there and the later `linear_combination` alternatives never run. Symptom: "unsolved
  goals" at the enclosing bullet with *no* tactic error, on exactly the goals your
  `linear_combination`s target. Fix: put the `linear_combination`s first and use
  `linear_combination (0 : ℝ)` (not `ring`) as the trivial-goal fallback last.
- **`fin_cases i <;> fin_cases j <;> simp only […]` does not reduce the matrix indices** — the
  `⟨0, ⋯⟩` Fin values from `fin_cases` leave `!![…]`/`vecCons … ⟨k,⋯⟩` unreduced even with
  `cons_val_*`/`Fin.isValue` in the set. Follow the `simp only [defs, mul_apply,
  Fin.sum_univ_three]` with a bare `simp` (as `rotMat_mem_SO3` does) to finish index reduction,
  then substitute/close.

## Counting a finite set of ℚ/ℝ-valued vectors (`ncard = N`; root systems, lattice enumerations, #6595)

To prove `(S : Set (Fin n → ℚ)).ncard = N` where `S` is carved out by norm/parity/coordinate
conditions (e.g. `rootsOf E8Lattice`), the reliable route is: realize `S` as the coercion of an
explicit `Finset`, then `Set.ncard_coe_finset` reduces to `Finset.card`. Assemble that finset as
the (possibly disjoint-union of) **injective image(s) of a decidable finite index set**, and read
the count off with `decide`. Two hard-won constraints:

- **`decide` is blind to ℚ/ℝ but fluent in `Fin`/`Bool`/`ℤ`.** A `decide` over an index set whose
  predicate evaluates a ℚ expression (`intVec … 0 = intVec … 1`, anything through `smul`/`e j`/
  `Rat`) gets *stuck* ("reduction got stuck at the `Decidable` instance"). Keep every index-set
  condition over `ℤ`/`Bool`: back each vector by an **ℤ-valued coordinate function** (`coordZ …`)
  and cast to ℚ only at the end, bridging ℚ-equalities to ℤ with `exact_mod_cast` / `Int.cast_inj`.
  Coordinate constraints for sub-objects (E₇'s `x₀=x₁`, E₆'s `x₀=x₁=x₂`) then become ℤ/`Bool`
  conditions on the *index* set (`cz p 0 = cz p 1`, `s 0 = s 1`), countable by `decide`.
- **`decide` over `Fin n → Bool` (256 elts for `n=8`) needs `set_option maxRecDepth 10000`** (else
  "maximum recursion depth"); it is fast (~2s) once the limit is raised. A brute-force `decide`
  over the whole ambient box (`{-2..2}^8` etc.) is NOT feasible — you still need the mathematical
  **classification lemma** (exact shape of a member: "two `±1` coords" via a support-card-`=2`
  argument; "every coord `±½`" via `Finset.sum_eq_zero_iff_of_nonneg` on `xₖ²−c ≥ 0`).

Image cardinality needs injectivity: `Finset.card_image_of_injOn` (feed a `Set.InjOn … ↑(filter)`,
obtained from a global `InjOn` via `.mono`); disjoint families combine with
`Finset.card_union_of_disjoint`. Prototype each classification/injectivity lemma in a throwaway
`EtingofRepresentationTheory/Scratch*.lean` (`import Mathlib`, a local `namespace`) before porting
— iterating there is far faster than rebuilding the real chapter file, and it sidesteps the
`inner`/Mathlib-`Inner` name clash the real (namespaced) file doesn't have. Worked example:
`Chapter6/Problem6_9_2.lean` (`E8_root_count`/`E7_root_count`/`E6_root_count`, `intShape`,
`halfShape`, `intVec'_injOn`).

## `ComposableArrows.map'` / `sc'` autoParam bug in term position (six-term windows, #6611)

The `ComposableArrows` API (`W.map' i j`, `W.sc' hc i j k`, `W.obj' i`) fills its index-bound
side conditions with a `by valid` autoParam. In a **type-ascription / signature position** this
works, but in a **term/value position** it fails with

    could not synthesize default value for parameter 'hij' using tactics: No goals to be solved

(both when left implicit and when you pass `(by omega)` explicitly). Symptoms: `asIso (W.map' 2 3)`,
`have S := W.sc' hc 2 3 4`, `kernel (W.map' 3 4)` all break; but `haveI : Mono (W.map' 2 3) := …`
and `lemma foo … : IsIso (W.map' 2 3)` are fine.

**Workaround:** bind the arrow first, so `map'` sits in the `have`/`let` *type*, then use the bound
name in term position:

```lean
haveI : IsIso (W.map' 2 3) := isIso_of_mono_of_epi _
let g : W.obj 2 ⟶ W.obj 3 := W.map' 2 3   -- `let` (not `have`) so `IsIso g` stays defeq-linked
exact asIso g
```

For the connecting-map short complex, avoid `sc'` entirely: build `ShortComplex.mk δ a hcomp`
directly with `hcomp : δ ≫ a = 0 := hW.toIsComplex.zero' 2 3 4` (`zero'` returns a Prop and is safe
in value position, unlike `sc'`), then transport `hW.exact' 2 3 4 : (W.sc' …).Exact` into
`ST.Exact` by defeq (the two ShortComplexes differ only in the proof-irrelevant `zero` field).
Worked example: `iso_of_sixTerm_exact` and the `n = 1` branch of `Problem_8_2_6_iv` in
`Chapter8/Problem8_2_6.lean`.

## Naturality of `Functor.fromLeftDerivedZero` in the functor variable (balancing theorem, #6611)

For `α : F ⟶ G` of additive functors (`C` abelian with enough projectives), the square

    (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X
      = F.fromLeftDerivedZero.app X ≫ α.app X

is **not** in Mathlib but is provable in ~10 lines: pick `P := projectiveResolution X`, rewrite
with `ProjectiveResolution.leftDerived_app_eq` and `ProjectiveResolution.fromLeftDerivedZero_eq`
(twice), cancel the `isoLeftDerivedObj` isos, push through `ChainComplex.isoHomologyι₀`-naturality
(`isoHomologyι₀_inv_naturality_assoc`) and `HomologicalComplex.p_opcyclesMap`, then finish with
`α.naturality (P.π.f 0)`. This is the crux input for the degree-0 half of a balancing / derived-
functor-symmetry argument (`balancing_zero_naturality` in `Chapter8/Problem8_2_6.lean`). The two
degree-0 functoriality maps of a "Tor computed either way" pair coincide via
`leftDerivedZeroIsoSelf` precisely because of this lemma.

## Reducing `2•1 - adj` when `adj` is a bare function in a `Matrix` slot (#6665)

A predicate like `IsAffineDynkinDiagram n (adj : Matrix (Fin n) (Fin n) ℤ)` whose body
contains `(2 • (1 : Matrix …) - adj).mulVec x` is often *applied* to a bare function
`f : Fin m → Fin m → ℤ` (e.g. `mckayAdj W`, defined as `fun i j => …`). Inside the goal
the subtraction is the genuine `Matrix.instSub` (elaborated once at def time with
`adj : Matrix`), and is well-typed. **But if you re-state that subtraction yourself**
(`have : (2 • 1 - f) a b = …`) Lean picks the *Pi* `Sub` instance because `f`'s type is
`Fin m → Fin m → ℤ`, producing an ill-typed `@HSub … Matrix instHSub` term — `simp`/`rw`
then report "made no progress" / "target not type-correct under instances", and
`Matrix.sub_apply` never fires. Symptom in a scratch: the note *"The target expression is
not type-correct under the `instances` transparency level"*.

Fix: never hand-write the subtraction. Discharge the PSD / not-PSD conjuncts against a
`Matrix.of`-wrapped Cartan lemma by `convert`-ing onto the goal's own term, then reduce the
scalar with `Matrix.smul_apply` (NOT `two_nsmul`, which rewrites `2•1 → 1+1` at matrix level
and reintroduces the ill-typed sub):

```lean
· intro x
  convert myCartan_posSemidef … x using 3          -- references the goal's genuine Matrix.sub
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    myCartan, myAdj]
  split_ifs <;> simp                                -- `2 • (1:ℤ)` / `2 • (0:ℤ)` close by simp
```

`using 3` descends `0 ≤ · ⬝ᵥ (M.mulVec x)` down to the matrix equality `M = Matrix.of …`;
`ext a b` then gives a well-typed entry goal because `M` came from the goal, not from you.

## `HomologicalComplex.mapBifunctor`/`tensorObj` degreewise iso proofs (`extend`/Künneth, #6693)

Building a degreewise iso between `(tensorObj K₁ K₂).X j` objects (e.g. the crux
`extend C ⊗ extend D ≅ extend (C ⊗ D)`) fights three recurring traps. Working recipe:

1. **Reduce along summands with `mapBifunctor.hom_ext` + `ι_mapBifunctorDesc`, never manual
   `Category.assoc`.** `(tensorObj K₁ K₂).X j` unfolds to `GradedObject.mapBifunctor … .obj K.X`,
   which is *not type-correct at `instances` transparency* (`K.X : ι → C` vs `GradedObject ι C`).
   So `rw [Category.assoc]`, `simp only [Category.assoc]`, `slice_lhs`, and even `conv_lhs => rw
   [Category.assoc]` all fail with "motive is not type correct" / "not type-correct under the
   instances transparency level" whenever the composite's middle object is a `.X` of a tensor.
   `←Category.assoc` on a *clean* `hom_ext` goal (`ι ≫ (f ≫ g)`) works; the forward direction on
   an unfolded body does not.

2. **The fix that unblocks everything:** put
   `set_option backward.isDefEq.respectTransparency false in`
   on the lemma. This is exactly what `Mathlib/…/Embedding/Extend.lean` uses. With it, the
   standalone composite-reduction lemmas (`phiInv ≫ fwdNeg = ι`, proved by `rw [phiInv,
   Category.assoc, ι…desc, …]`) go through. Structure the round-trips so the painful step lives in
   such a standalone lemma (clean starting goal, no prior unfolds polluting it), then the
   `hom_ext` proof is just `rw […, ι…_desc]; exact that_lemma`.

3. **Match your own `ι` spelling to `hom_ext`'s.** `hom_ext`/`ι_mapBifunctorDesc` produce/expect
   `HomologicalComplex.ιMapBifunctor …`, but `ιTensorObj` (a reducible abbrev) does *not* rw-match
   it. Define your summand maps with `ιMapBifunctor` directly (wrap in a local `abbrev ιN`/`ιZ`
   fixing `curriedTensor _` and the shape) — do **not** `simp only [ιTensorObj]` to convert, since
   that unfolds into the ill-typed `GradedObject` form and re-triggers trap 1.

**Match-with-binder defs reduce via `split`, not `simp`.** For a per-summand map defined
`match ha : e.r a, hb : e.r b with | some p, some q => … | _,_ => 0`, prove its reduction lemma
with `rw [phiFwd]; split; next p' q' hh1 hh2 => obtain rfl := Option.some.inj (hh1 ▸ ha); …;
next hh => exact (hh p q ha hb).elim`. `simp only [phiFwd, ha, hb]` will *not* fire (the match
binds its own scrutinees); a `dite`-on-`isSome` reformulation reduces cleanly but then `.get`
sits in dependent positions and `rw`/`simp` cannot rewrite `(e.r a).get → p` (motive). Prefer the
match+`split`.

**Transport a `-n`-indexed iso to a variable `j'` via a `match hj : e.r j'` def**, `some n` branch
`eqToIso (congrArg (…).X (j' = -n)) ≪≫ isoNegExt … ≪≫ eqToIso (…)`. Prove `foo_neg : foo (-n) =
isoNegExt n` by `rw [foo]; split; next m hm => obtain rfl := …; apply Iso.ext; simp`. Do **not**
use `.get` for `n` (dependent-position `get` is unrewritable); the match binder gives a real `n`.

**Mirroring the chain (`down ℕ`) Künneth to the cochain (`up ℕ`) case (`embeddingUpNat`, #6825,
`Chapter7/KunnethCochainComplexNat.lean`).** Two extra traps the `-n` chain version dodges:
- Mathlib ships `TensorSigns (up ℤ)` and `TensorSigns (down ℕ)` but **not** `TensorSigns (up ℕ)`;
  `HomologicalComplex.tensorObj` won't elaborate on `up ℕ` until you add it (`ε n = (-1)^n`, copy
  the `down ℕ` instance, flip only the `Rel` direction: `rel_add`/`add_rel` by
  `simp only [ComplexShape.up_Rel]; omega`, `ε'_succ` by `change (-1:ℤˣ)^(p+1) = -(-1:ℤˣ)^p`).
- **Cast-spelling war `↑(n+1)` vs `↑n+1`.** The upward differential targets degree `n+1`, and
  `fwdNat (n+1)` / `r_nat (n+1)` are locked to `↑(n+1)`, but a plain **`dsimp` silently rewrites
  `↑(n+1)` to `↑n+1`**, after which `rw [ιZ_fwdNat …]` / `phiFwd_some` fail "did not find pattern".
  The chain case never hits this (its downward differential targets `-↑n`, no `+1`). Fixes: (1)
  never let `dsimp` touch the goal here — reduce the Koszul signs with explicit rewrites instead,
  `show ComplexShape.ε₁ (up ℕ) (up ℕ) (up ℕ) (p,q) = (1:ℤˣ) from rfl` (then `one_smul`) and
  `show ComplexShape.ε₂ … (p,q) = Int.negOnePow ↑p from (negOnePow_natCast p).symm` (then `congr 1`);
  (2) spell every shifted index as `((p+1 : ℕ) : ℤ)` (not `(p:ℤ)+1`) in the `mapBifunctor.d₁_eq`/
  `d₂_eq` `Rel` proofs, `extend_d_eq` via `ef_eq (p+1)`, and the `ιZ_fwdNat`/`r_nat` calls, so all
  four agree. Sign lemma is the simpler `negOnePow_natCast` (`Int.negOnePow ↑n = (-1)^n`); the
  up-differential `C.d p (p+1)` never vanishes, so there are **no** `p=0`/`q=0` boundary sub-cases.
- Importing the chain twin to reuse `sigmaIsoOfInjOfIsZeroCompl` also pulls its `Etingof.`-namespaced
  `homology_extend_iso`/`homology_extend_isZero` into scope — rename your parallel helpers
  (`…_up`) or you get "already declared".

## `omega` proves atoms, not `∨`/`∧` *goals*; matrix-entry `split_ifs <;> omega` traps (#6755)

Computing entries / cofactor recursions of concrete matrices (e.g. tridiagonal Cartan
matrices `2 • 1 - adj`) hits two recurring `omega` limitations that surface as the cryptic
`omega could not prove the goal: No usable constraints found`:

1. **`omega` cannot prove a disjunctive (`A ∨ B`) or conjunctive (`A ∧ B`) *goal*.** It only
   closes a single (in)equality, `False`, or a *negation* `¬(…)` (including `¬(A ∨ B)`, which is
   fine — that is a conjunction of refutable atoms). So a condition like an off-diagonal
   `i.val + 1 = j.val ∨ j.val + 1 = i.val` must be handed the disjunct explicitly:
   `Or.inl (by …)` / `Or.inr (by …)`; a conjunction `(eq ∧ le)` must be split
   `⟨by …, by …⟩`. `by simp only [Fin.val_succ, Fin.val_zero]; omega` on such a goal fails.
   Reflexive equality sub-goals (`0 + 1 = 0 + 1`) are closed by the `simp only` itself — do
   **not** append `omega` there or you get "No goals to be solved".

2. **Reduce single matrix entries with helper lemmas, not `split_ifs <;> omega`.** For a
   `def M i j := if i.val = j.val then a else if <cond> then b else 0`, prove three helpers
   (`M_diag`/`M_offdiag`/`M_far`) that take the resolved condition and finish with
   `simp only [M, if_pos/if_neg …]`. Then each entry fact is
   `M_far (by simp only [Fin.val_succ, Fin.val_zero]; omega) (by …; omega)` — omega only ever sees
   clean ℕ atoms. `split_ifs <;> omega` directly on `M i j = c` is flaky (leftover `↑↑j` int
   coercions, disjunctive branch hyps) even though it *works* on two-sided `ext` matrix-equality
   goals where both sides carry the same `ite`s.

3. **`2 • (1 : Matrix _ _ ℤ)` is invisible to `omega`.** The `2` is a `ℕ`-nsmul, so
   `smul_eq_mul` does *not* fire and omega treats `2 • 1` as an opaque atom. In the `ext`+`omega`
   proof relating a `cartan := 2 • 1 - adj` matrix to a bare `if`-matrix, add `two_nsmul`
   (→ `x + x`) and `Matrix.add_apply` to the `simp only` set (drop `Matrix.smul_apply`) so the
   diagonal `2` becomes `1 + 1` before `split_ifs <;> omega`.

4. **Two-step (continuant) recursion + induction.** `det(C (n+2)) = 2·det(C (n+1)) − det(C n)`
   via `Matrix.det_succ_row_zero` then `det_succ_column_zero`; peel the sum with
   `Fin.sum_univ_succ` twice and kill the tail with a `∀ j, C 0 (succ (succ j)) = 0` hypothesis
   fed to `simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, …]; ring`. Close with
   `private lemma f : ∀ n, … | 0 => … | 1 => … | (n+2) => by rw [rec, f (n+1), f n]; …` (Lean's
   equation compiler accepts the two-step recursion). Keep the smaller-index submatrix identities
   (`(C (m+1)).submatrix Fin.succ Fin.succ = C m`) as separate `ext … <;> split_ifs <;> omega`
   lemmas.

## Taking `Ext¹`/cokernel of a `QuiverRepresentation` differential and computing `finrank` (#7376)

`Etingof.QuiverRepresentation` bundles only `AddCommMonoid`/`Module` on each `obj v`
(both `[instance]`). Forming a cokernel `codomain ⧸ LinearMap.range d` or an Ext module
needs `AddCommGroup` on the carriers, and this is where the diamonds bite. Pattern that
works (Problem 3.9.3, `dim Ext¹(S_i,S_j) = #(i ⟶ j)`):

1. **Subtraction in the differential:** define the differential `d(f)_a = W_a ∘ f_i - f_j ∘ V_a`
   with `letI : ∀ v, AddCommGroup (W.obj v) := fun _ => Etingof.Problem6_9_3.acg` *inside* the
   def body (as the bare-function `extDiff` already does). `acg = { bundledInst with neg := (-1)•· }`
   **extends** the bundled `AddCommMonoid`, so `acg.toAddCommMonoid` is defeq to it and the
   subtraction lands in the bundled-monoid `LinearMap` space. Do **not** take
   `[∀ v, AddCommGroup (W.obj v)]` as an instance argument on a *general* `V W` def — an abstract
   group's monoid ≠ the bundled monoid, and `HSub` fails to synthesize (`?m` stuck).

2. **Quotient/`finrank` at the use site:** instance search will **not** unfold `(simpleRep j).obj v`
   to `Fin _ → k` to find `Pi.addCommGroup` (it stops at the bundled monoid). So the *statement*
   `finrank k (Ext1Simple i j)` won't elaborate. Register a **low-priority** compatible instance
   `instance (priority := 100) : AddCommGroup ((simpleRep j).obj v) := by change AddCommGroup (Fin _ → k); infer_instance`.
   Low priority keeps the bundled `AddCommMonoid` preferred everywhere else; its `toAddCommMonoid`
   is the same `Pi` monoid, so no downstream proof breaks (verify by building the chapter aggregate).
   Specialize the Ext object to the concrete reps (`Ext1Simple i j`, an `abbrev` so `finrank` sees
   the quotient's `Module`), not a general `Ext1 V W` (whose quotient-group ≠ range-submodule-monoid
   for abstract `W`).

3. **Zero differential between simples:** prove `d = 0` at `LinearMap` level, not element level.
   `refine LinearMap.ext fun f => funext fun p => ?_` (a plain `ext f p x` drills to `x✝` and
   leaves an unclosable `(0 - 0) x✝ = (0 f p) x✝`), then a `letI acg` to align the ambient group
   with the one baked into the differential, `show <the toFun expr> = 0`,
   `simp only [simpleRep, LinearMap.zero_comp, LinearMap.comp_zero]`, `exact sub_self 0`.
   `sub_self`/`sub_zero` silently *fail to fire in `simp`* when the ambient `AddCommGroup` differs
   from the term's — this is why the `letI acg` matters.

4. **`finrank` of the codomain product:** `coker 0 ≅ codomain` via `Submodule.quotEquivOfEqBot _ hbot`
   (first arg is the submodule, explicit) then `.finrank_eq`. `Module.finrank_pi_fintype k` needs
   `Free`+`Finite` on each Hom component — supply `∀ r a, Module.Finite/Free k ((simpleRep r).obj a)`
   as `∀`-quantified `haveI`s (via `change … (Fin _ → k); infer_instance`); `Module.Finite.linearMap`
   / `Module.Free.linearMap` then derive the Hom instances. `Module.finrank_linearMap` gives
   `finrank Hom = finrank dom * finrank cod`.

5. **Collapsing the sigma-count `∑ p : (Σ a b, (a⟶b)), [a=i][b=j]`:** `rw [Fintype.sum_sigma]`
   (outer) works, but the *inner* sigma sum lives under the `∑ a` binder — `rw` can't reach it and
   `conv … ext a` fails (`ext` does not enter `Finset.sum`). Use `simp only [Fintype.sum_sigma]` for
   the inner expansion. **`Finset.sum_const` does not fire in `simp only` on `∑ (e : a ⟶ b), C`** — a
   full `simp [Finset.sum_const, Finset.card_univ, Finset.card_empty, mul_ite, ite_mul, apply_ite Finset.card, Fintype.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero]`
   collapses the whole thing (it routes the constant arrow-sum through
   `(if … then Finset.univ else ∅).card`, which `apply_ite Finset.card` + `Finset.card_univ`/`card_empty`
   finish). Trace the intermediate goal with `trace_state` when a staged `simp only` stalls.

## `addCommGroupOfRing` AddCommMonoid→AddCommGroup diamond breaks fresh builds (#7525, the "restore fresh-buildable" wave)

`Etingof.QuiverRepresentation` bundles only `AddCommMonoid`+`Module` on `obj v`. Many proofs
upgrade to a group with `letI : ∀ v, AddCommGroup (V.obj v) := fun v => Etingof.addCommGroupOfRing`.
`AddCommGroup` does **not** store `toAddCommMonoid` as a field (it derives it from `toAddGroup`+comm),
so `(addCommGroupOfRing).toAddCommMonoid` is defeq to the ambient `AddCommMonoid` only at `default`
transparency, **not** the `instances`/reducible transparency that instance search and `rw`/`simp`
motive-checks use. A Mathlib bump made this fatal, and it is the root cause of a whole wave of
"restore fresh-buildable" regressions (`DecompositionExistence`, `Proposition6_6_5`, `Theorem6_5_2`
#7518, `Problem6_1_5_OrbitFiniteness`, …). Stale oleans hide it at import time; a *fresh*
`lake env lean` on each file exposes it. Symptoms:

- `rw`/`simp` reports **"target expression is not type-correct under the `instances` transparency
  level"** and refuses to fire (even `LinearMap.comp_apply`), or leaves the goal untouched with all
  simp args "unused".
- With the `letI acg` in scope, `Module k (V.obj v)` / `Module.Finite k (V.obj v)` /
  `Module.Finite k ↥(W v)` **fail to synthesize** — the upgraded monoid shadows the bundled one.

**Do not** try to make the diamond reducible (impossible with `{ inst with … }`) and **do not** put
the group in scope when you also need the bundled `Module`/`Module.Finite`. Instead:

1. **Never unfold `directSum` under `simp`.** Add `rfl` `@[simp]` lemmas
   `directSum_obj : (directSum k Q V₁ V₂).obj v = V₁.obj v × V₂.obj v` and
   `directSum_mapLinear : (directSum …).mapLinear f = (V₁.mapLinear f).prodMap (V₂.mapLinear f)`.
   These keep every goal type-correct. Note `LinearMap.prodMap_apply` will *not* fire when the arg
   has type `(directSum …).obj a` (it doesn't whnf to `_ × _` at simp's transparency) — a `rfl`
   pair-form lemma `((directSum …).mapLinear f y).1 = V₁.mapLinear f y.1` does.
2. **Intertwining that is definitional** (unit/assoc/`prodUnique`/`uniqueProd`/`prodAssoc`): just
   `intro a b f; ext x <;> rfl`. Don't fight it with `simp`.
3. **Vertex isomorphism from `IsCompl`** (`areIsomorphic_subRep_directSum`): build it as
   `LinearEquiv.ofBijective (sc v) (hbij v)` where `sc v := (W₁ v).subtype.coprod (W₂ v).subtype`
   is **structure-typed** (needs no group), and the group only appears inside `hbij v` as
   `(@Submodule.prodEquivOfIsCompl k _ (V.obj v) (addCommGroupOfRing) (V.instModule v) …).bijective`.
   This keeps the group out of every term the arrow maps act on. Prove the intertwiner via a
   naturality lemma for `sc` (`coprod_apply` + `restrict_coe_apply`).
4. **finrank / complement facts** (`finrank_add_eq_of_isCompl`, `finiteDimensional_submodule`,
   `finrank_pos`): keep the group **out of scope** and pass it explicitly, e.g.
   `@Submodule.finrank_add_eq_of_isCompl k (V.obj v) _ (Etingof.addCommGroupOfRing (k := k))
   (V.instModule v) (inferInstanceAs (Module.Finite k (V.obj v))) …`. `inferInstanceAs` resolves
   the bundled `Module.Finite` *because no `acg` is in scope*; the `@`-application then accepts it
   for the group-keyed argument by `default`-transparency defeq. For anything messier (positivity),
   factor a standalone helper lemma with plain `[AddCommGroup M] [Module k M] [FiniteDimensional k M]`
   hypotheses and apply it with `@` + explicit `addCommGroupOfRing`.
