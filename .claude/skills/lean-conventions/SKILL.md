---
name: lean-conventions
description: Read before writing or editing any .lean file in this repository. The build commands, linter/`omit` placement rules, and import conventions that every Lean session needs. Use when starting a feature issue that touches EtingofRepresentationTheory/.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Lean Conventions for This Repository

The house rules every Lean session needs, in the order you will hit them. Read this
in full before your first edit; it is short by design.

This is **not** the reference. `lean-formalization/SKILL.md` is a ~7900-line searchable
catalogue of specific mathematical traps (tensor products, `ModuleCat`, quiver
representations, Specht modules, …). Do not read it front to back. `grep` it for the
Mathlib name, error message, or chapter you are stuck on:

```bash
grep -n 'TensorProduct.liftAddHom' .claude/skills/lean-formalization/SKILL.md | cut -c1-200
```

Its lines are very long, so pipe through `cut` and read the hits with `awk`/`Read` at
a narrow offset rather than reading whole sections.

## Build and typecheck

Before the first build of any session:

```bash
lake exe cache get
```

Skipping it triggers a full Mathlib rebuild (1800+ jobs).

**Typecheck with `lake build EtingofRepresentationTheory.<Module>`, not `lake env lean
<file>`.** `lake env lean` ignores the lakefile's `[leanOptions]`, in particular
`maxSynthPendingDepth = 3` (the Lean default is 2). Deep instance chains in this project
throw *spurious* `synthInstanceFailed` errors under `lake env lean` that do not occur
under `lake build`. If a file fails `lake env lean` with instance-synthesis errors,
re-check with `lake build` before debugging: files already on `main` fail `lake env lean`
too.

**Never `cd` into `.lake/packages/mathlib`** (or any subdirectory). The shell's working
directory persists across calls, and that directory is itself a lake project: once you are
inside it, `lake build EtingofRepresentationTheory.<Module>` fails with "unknown target",
and a bare `lake build` **silently builds Mathlib and reports success**. If a build reports
"unknown target" or an unexpected job count, run `pwd` first. Read Mathlib sources by
absolute path from the worktree root instead.

**Use `set -o pipefail` when piping a build through `tee`/`tail`**, otherwise the
pipeline's exit status is `tee`'s `0` and a real failure reads as success:

```bash
set -o pipefail
lake build EtingofRepresentationTheory.Chapter5.Foo 2>&1 | tee /tmp/build-Foo.log | tail -30
```

## The build stays lint-clean

`lakefile.toml` sets `weak.linter.mathlibStandardSet = true`. These warnings do **not**
fail CI (CI runs plain `lake build`, which exits 0 on warnings), but the project keeps the
build clean, and a PR that adds warnings will be asked to remove them.

The linters you will actually trip:

| Linter | Fires when |
|---|---|
| `unusedSectionVars` | a `variable` block instance/hypothesis is not used by the declaration |
| `unusedDecidableInType` | a `[DecidableEq _]` section variable is unused |
| `unusedFintypeInType` | a `[Fintype _]` section variable is used only to *form* the type, not in the proof |
| `linter.style.show` | `show` is used to change the goal to a defeq form (use `change` instead) |
| `linter.style.setOption` | a `set_option maxHeartbeats … in` has no explanatory comment, or sits below an `omit … in` (see below) |

A statement-only theorem trips these easily: what counts is whether the declaration's
**type** mentions the variable, not whether the file needs it elsewhere.

### `omit` and `set_option` placement (the single most repeated slip)

There is exactly one order that is both a parse success and lint-clean. Everything above
the declaration goes in this sequence:

```lean
set_option maxHeartbeats 400000 in
-- Why the raised budget is needed.
omit [FiniteDimensional ℂ V] in
/-- Doc comment. -/
@[simp]
theorem foo : … := …
```

`set_option … in`, then its explanatory comment, then `omit … in`, then the docstring,
then attributes, then the declaration. Three separate rules force this, each verified
against the current toolchain:

- **`omit`/`set_option` must precede the docstring.** Putting either between the
  docstring and the declaration is a parse error, `unexpected token 'omit'; expected
  'lemma'` (likewise `unexpected token 'set_option'`), reported at a column that points
  nowhere useful. Note the `unusedSectionVars` linter's own suggested fix is `omit [Inst]
  in theorem …`, which is exactly the wrong thing to paste above a documented declaration.
- **`set_option maxHeartbeats` needs a `--` comment between the `in` and whatever follows**,
  or `linter.style.setOption` asks you to "add a comment explaining the need for modifying
  the maxHeartbeat limit". **A docstring does not satisfy this**: it must be a `--`
  comment.
- **`set_option … in` must come *above* `omit … in`, not below it.** With the `omit` on
  top, `linter.style.setOption` loses track of the scope and reports the confusing
  "Unscoped option maxHeartbeats is not allowed" even though you did write `in`. Reversing
  the two lines silences it.

Three follow-on details:

- **The linter reports unused instances one at a time.** After omitting the flagged ones
  it may flag a further instance (e.g. `Module.Finite` once `Fintype`/`DecidableEq` are
  omitted). Expect to extend the `omit` list across a build cycle or two.
- **Section-wide vs per-lemma.** If an earlier `def` in the section *captured* the
  instance (Lean auto-includes an instance-implicit section variable whenever its type
  mentions an already-used variable, even if the body never touches it), a per-lemma
  `omit [Inst] in` on a *downstream* lemma that calls that def fails with `failed to
  synthesize instance … Inst`, because the def now demands it. Fix by putting a bare `omit
  [Inst]` command (no `in`, no docstring) right after the section's `variable` line, so
  nothing in the section captures it.
- **`set_option … in` does not work before `private`.** Wrap those declarations in a
  `section` with a bare `set_option linter.unusedFintypeInType false` instead.

## Imports

**`import Mathlib` is fine, and is the normal choice for a new file** (336 of the 765
files in `EtingofRepresentationTheory/` use it). Do not spend a build cycle hand-narrowing
imports for a file that has no reason to be narrow.

Go granular only when there is a specific reason:

- **Import-cycle work**, where a file must avoid a named transitive edge. Verify with a
  real transitive trace, never a direct-import grep (see the "import-cleanliness" section
  of the reference).
- **A `Finsupp`-based algebra.** Under `import Mathlib` the pointwise `Finsupp.instMul`
  becomes a valid `Mul` and can outrank an intended convolution/concatenation
  multiplication. The defence is to declare such a carrier as a semireducible `def`, never
  an `abbrev`; a `def` blocks the pointwise instance regardless of imports.

**A missing *tactic* import reads as a broken proof, not a missing import.** In a file with
granular imports, `unknown tactic` is reported at a misleading line (often the next
declaration) plus cascading `unsolved goals` on every `have` that used it, which reads as
"my algebra was wrong". `linear_combination` needs `Mathlib.Tactic.LinearCombination`,
`module` → `Mathlib.Tactic.Module`, `noncomm_ring` → `Mathlib.Tactic.NoncommRing`, `group`
→ `Mathlib.Tactic.Group`.

**`Basis` lives in the `Module` namespace** in this Mathlib version: the type is
`Module.Basis ι R M`, and explicit references need the prefix (`Module.Basis.ext`,
`Module.finBasis`). Dot notation on a basis term (`b.repr`, `b.constr`) resolves fine
unprefixed.

## Non-negotiables

- **Never `sorry` the body of a `def`, `noncomputable def`, `instance`, or `abbrev`.** A
  sorry'd definition means the object does not exist and every theorem about it is
  vacuous. Proof obligations *inside* a definition (`where` clauses) may be sorried.
- **`native_decide` is forbidden.** CI fails fast on it before the build, and the guard
  also rejects `set_option linter.style.nativeDecide false`. A finite check too slow for
  honest `decide` is a signal to find a real proof, not a bigger hammer.
- **Never use `True` as a placeholder** for a proposition you have not worked out. Sorry
  the real statement instead.

## Writing style

Comments and docstrings read as mathematics, never as a record of the formalization.

- **No war stories.** No PR/issue numbers, no `relocated`, `is now in`, `## Status`,
  `sorry-free`, `route B`. That history belongs in git and GitHub.
- **Banned words** (standing bans, all technical writing): `bridge`, `gate`, `smoke`, and
  em-dashes. Also avoid the AI register: `genuine`, `crux`, `payoff`, `seam`, `glue`,
  `assembly` (for a proof), `would-be`, `routes through`, `feeding`.

`EtingofRepresentationTheory/Chapter6/Problem6_1_5_OrbitInjective.lean` is written to this
standard; use it for calibration.
