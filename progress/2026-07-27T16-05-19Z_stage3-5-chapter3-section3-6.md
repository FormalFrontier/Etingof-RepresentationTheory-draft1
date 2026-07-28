# Stage 3.5 Mathlib-quality review — Chapter 3 §3.6

## Scope and result

This review is stacked exactly on the completed Stage 3.4 dependency audit in draft PR
#8079 at commit `7853fe90c463d3a1f5cc1091089ca20672b5b580`. It covers the three
reading-order items at global indices 156–158 and all four exact providers. The immediate
predecessor is Proposition 3.5.8; the strict successor is the introduction to §3.7.

The implementation is now warning-free and clean under Mathlib's declaration linters. The
mathematics and claim coverage are unchanged. The source polish strengthens two public APIs:
the irreducible-family index assumption on both character theorems is now `Finite ι` rather
than `Fintype ι`, with a local `Fintype.ofFinite` used only by the proof; the private
semisimple injectivity helper drops its entirely unused finiteness assumption.

The remaining edits are maintenance:

- nine goal-changing `show` tactics are expressed as `change`;
- four unused simp arguments are removed;
- deprecated `LinearMap.coeFn_sum` is replaced by `LinearMap.coe_sum`;
- `Etingof.character` documents and narrowly exempts its construction-only
  `Free` and `Module.Finite` instances from `unusedArguments`;
- both formerly warning-producing providers are removed from the checked warning baseline.

## Lint, import, style, and axiom audit

- Temporary per-provider `#lint+ docBlameThm` checks ran all 16 default declaration
  linters plus `docBlameThm`. They found zero errors across 13 lint-visible declarations
  and 19 automatically generated declarations: theorem provider 3+13, matrix provider 2+2,
  introduction provider 5+3, and exercise provider 3+1.
- Temporary complete-provider `#redundant_imports` checks found no transitively redundant
  import in any header. Stage 3.4's five focused direct imports remain unchanged.
- `#print axioms` re-audited all 13 durable declarations. None depends on `sorryAx`;
  the only reported dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- Final isolated elaboration of all four providers succeeds in 1,957 jobs without a scoped
  warning. The warning ratchet passes after removing the two now-stale baseline entries.
- Scoped scans find no `sorry`, `admit`, project `axiom`, `opaque`,
  `proof_wanted`, `native_decide`, deprecated `push_neg`, leftover diagnostic command,
  or line over 100 characters.

## Durable completion and validation

- all three exact records now have `status = proof_polished` and complete section 3.6
  Stage 3.5 metadata with `mathlib_quality = verified`;
- Stage 3.2, Stage 3.3, Stage 3.4, claim, fidelity, and dependency metadata are unchanged;
- `lake build EtingofRepresentationTheory.Chapter3` succeeds in all 8,692 jobs; reported
  warnings are pre-existing and outside the four scoped providers;
- all four repository validators pass;
- exact scope adjacency, scoped prior-stage invariance, normalized non-scope tracker
  invariance, both dependency files, import headers, and the two unaffected providers are
  unchanged from Stage 3.4;
- JSON parsing, source scans, the warning-baseline ratchet, line-length checks, and
  `git diff --check` all pass.

The temporary lint, redundant-import, and axiom-audit commands were removed from committed
source. This PR is limited to Chapter 3 §3.6 and Stage 3.5.
