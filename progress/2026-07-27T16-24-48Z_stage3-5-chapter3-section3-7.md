# Stage 3.5 Mathlib-quality review — Chapter 3 §3.7

## Scope and result

This review is stacked exactly on the completed Stage 3.4 dependency audit in draft PR #8085 at
commit `80055312a5780977fb3d8537e7ce1e95fa09ba2f`. It covers the three reading-order
items at global indices 159–161 and all three exact providers. The immediate predecessor is
`Chapter3/Theorem3.6.2`; the strict successor is `Chapter3/Introduction_to_3.8`.

The Jordan–Hölder and length providers were already at the requested quality level. The footnote
provider had two small public-API defects exposed by the complete declaration-linter pass:

- `Etingof.diagPi` unnecessarily required `[Fintype ι]`, although coordinatewise application is
  defined for an arbitrary index type;
- its public simp theorem `Etingof.diagPi_apply` had no declaration docstring.

The unused finiteness assumptions were removed from both declarations and the simp theorem was
documented. The proofs, theorem statements, mathematical coverage, and imports are otherwise
unchanged. Finiteness remains required exactly where it is mathematically needed, in the trace
theorem for `Fin n → V`.

## Lint, import, style, and axiom audit

- Temporary per-provider `#lint+ docBlameThm` checks ran all 16 default declaration linters plus
  `docBlameThm`. After the two scoped fixes they found zero errors across ten authored
  declarations and two automatically generated constants: theorem provider 4 + 0, discussion
  provider 1 + 0, and footnote provider 5 + 2.
- Temporary complete-provider `#redundant_imports` checks found no transitively redundant import
  in any header. Stage 3.4's three focused direct imports remain unchanged.
- `#print axioms` re-audited all ten durable declarations and both generated `Etingof.diagPi`
  constants. None depends on `sorryAx`; the only reported dependencies are `propext`,
  `Classical.choice`, and `Quot.sound`.
- Final isolated elaboration of each provider is warning-free. The exact aggregate provider build
  succeeds in all 1,960 jobs; its replayed warnings come only from imported §3.2 and §3.6 files,
  never from a §3.7 provider. None of the three providers is in the checked warning baseline, so
  the baseline correctly remains unchanged.
- Scoped scans find no `sorry`, `admit`, project `axiom`, `opaque`, `proof_wanted`,
  `native_decide`, deprecated `push_neg`, leftover diagnostic command, or line over 100
  characters.

## Durable completion and validation

- all three exact records now have `status = proof_polished` and complete section 3.7 Stage 3.5
  metadata with `mathlib_quality = verified`;
- Stage 3.2, Stage 3.3, Stage 3.4, claim, fidelity, and dependency metadata are unchanged;
- `lake build EtingofRepresentationTheory.Chapter3` succeeds in all 8,692 jobs; all reported
  warnings are pre-existing and outside the three scoped providers;
- `python3 scripts/validate_items.py` passes with 5,721/5,721 source-line coverage, 583 unique
  item IDs, and only its pre-existing extra-field warnings;
- dependency validation passes with 583 entries and 580 exact internal edges; external-dependency
  and Mathlib-coverage validation also pass;
- exact scope adjacency, scoped prior-stage invariance, normalized non-scope tracker invariance,
  both dependency files, all import headers, the two source-unchanged providers, and the warning
  baseline are unchanged from Stage 3.4;
- JSON parsing, source scans, line-length checks, graph-to-tracker consistency, backward-edge
  ordering, and `git diff --check` all pass.

The temporary lint, redundant-import, and axiom-audit commands were removed from committed source.
This PR is limited to Chapter 3 §3.7 and Stage 3.5.
