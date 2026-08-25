# Handoff prompt: finish the Etingof representation-theory repository split

You are taking over a release-preparation project that turns one development
corpus into two clean-history repositories. This handoff is
self-contained for a new machine. Do not assume access to any previous
worktree, build cache, shell history, or uncommitted state.

Read this document fully before editing or publishing anything.

## Obtain the exact checkpoint

The checkpoint is in the existing public repository
`FormalFrontier/Etingof-RepresentationTheory-draft1`. No GitHub organization
membership or repository permission is needed to obtain it.

Clone the portable release checkpoint:

```bash
git clone \
  --branch release-handoff-2026-08-11 \
  --single-branch \
  https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1.git \
  Etingof-release-handoff
cd Etingof-release-handoff
git rev-parse HEAD
```

The result must be:

```text
112df00abbe56f6a4820465ef57ec12553b7fcd8
```

This is an orphan checkpoint commit whose repository root is the complete
release-preparation staging tree. The branch is a handoff vehicle, not one of
the two final repositories and not a branch to merge into `main`. Create a new
continuation branch from this commit before working:

```bash
git switch -c continue-release-preparation
```

Some migration and validation tasks also need the original Lean source and
packet blobs. Obtain those through a second, fresh clone:

```bash
cd ..
git clone \
  https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1.git \
  Etingof-draft-source
cd Etingof-draft-source
git checkout --detach 2712420950ca8da299737f1d21d5c395ec9e27b4
cd ../Etingof-release-handoff
```

The pinned original-source commit is:

```text
2712420950ca8da299737f1d21d5c395ec9e27b4
```

In commands below, the current directory is always the checkpoint repository
root unless a command explicitly enters a subdirectory. When a validator needs
the original clone, use the freshly created sibling checkout
`../Etingof-draft-source`. No other external filesystem state is required.

The checkpoint intentionally excludes `.git` directories from staged
projects, `.lake`, `_out`, `.verso`, compiled Lean objects, Python caches, and
process-only directories. Regenerate build caches normally with Lake.

### Which agent harness governs

Do **not** use `pod` for this release-preparation work. Do not claim GitHub
issues, auto-merge PRs, or write per-turn `progress/<timestamp>.md` files merely
because the historical source checkout's `.claude/CLAUDE.md` says to do so.
Those instructions govern the earlier book-formalization harness, not this
repository-split project.

Run agents from the checkpoint repository, never from
`../Etingof-draft-source`. The original checkout is a pinned, read-only source
input. This handoff's clean-room, review, migration, validation, and checkpoint
workflow takes precedence for the split.

### Write access and credentials

Anonymous HTTPS access is sufficient to clone both inputs and do all local
conversion work. It is not sufficient to push progress.

Before promising remote checkpoints, establish one of the following:

- collaborator write access to
  `FormalFrontier/Etingof-RepresentationTheory-draft1`, with authenticated Git
  credentials; or
- a writable fork/remote supplied by the operator.

Check the chosen remote explicitly before relying on it. If the operator has
not supplied write credentials, continue on a local branch but report that the
work is not yet backed up remotely; do not silently assume FormalFrontier
permissions.

Creating the two final organization repositories, configuring protections,
and installing private updater secrets require a human or service account with
the relevant FormalFrontier organization rights. Those publication credentials
are not contained in this checkpoint and are intentionally a final human
handoff, not a prerequisite for the conversion agents.

## Objective: two final repositories

The work is a legal and technical split, not merely a rename.

### 1. Public independent Lean formalization

Final GitHub repository:

```text
FormalFrontier/EtingofRepresentationTheory
```

It must be public and have a clean, single-root-commit history at first
publication. Its staged source tree is `clean-code/release/`.

It contains independently written Lean formalizations of mathematics also
covered by the Etingof book. It must contain neither book prose nor the book's
page/chapter/section organization.

The legal files already staged require:

- exact filename `LICENSE`, not `LICENCE`, matching Mathlib and the surrounding
  ecosystem; Mathlib's `linter.style.header` requires the header line to name
  `LICENSE`, and this project enables `weak.linter.mathlibStandardSet`;
- Apache License 2.0;
- copyright 2026 FormalFrontier;
- a README citation of Pavel Etingof, Oleg Golberg, Sebastian Hensel, Tiankai
  Liu, Alex Schwendner, Dmitry Vaintrob, and Elena Yudovina, with historical
  interludes by Slava Gerovitch, *Introduction to Representation Theory*,
  Student Mathematical Library 59, AMS, 2011,
  ISBN 978-0-8218-5351-1, <https://bookstore.ams.org/stml-59/>;
- a clear statement that this is an independent formalization covering some
  of the same mathematical material, that it quotes no book prose and does not
  reproduce the book's structure, and hence is not a derivative work of the
  book for copyright purposes; and
- a statement that the AMS has a corresponding access-controlled repository
  containing the fully aligned formalization and book text rendered with
  Verso, hosted by FormalFrontier on the AMS's behalf, and not yet publicly
  available.

### 2. Private AMS-owned aligned Verso edition

Final GitHub repository:

```text
FormalFrontier/EtingofRepresentationTheory-verso
```

It must be private and have a clean, single-root-commit history at first
publication. Its staged source tree is `verso/release/`.

It contains the book transcription, semantic metadata, native Verso content,
generated navigation, and formalization panels aligned to declarations in the
public Lean repository.

The legal files already staged require:

- exact filename `LICENSE`, not `LICENCE`, matching Mathlib and the surrounding
  ecosystem; Mathlib's `linter.style.header` requires the header line to name
  `LICENSE`, and this project enables `weak.linter.mathlibStandardSet`;
- copyright © 2026 American Mathematical Society, all rights reserved;
- a clear statement that the AMS owns the repository content and aligned
  edition;
- acknowledgment that FormalFrontier assisted with the technical preparation
  and Verso alignment and hosts the repository for the AMS; and
- an explicit disclaimer by FormalFrontier of copyright, ownership, or any
  other intellectual-property claim in the book, its text, or the aligned
  edition.

The private repository may produce an access-controlled CI artifact. It must
not publish GitHub Pages or otherwise expose the book publicly.

The private project pins the public Lean repository as a Git dependency.
`AlignmentExport.lean` extracts public `source_ref` attributes, and
`scripts/sync_formalization_panels.py` deterministically generates the panels
shown beside the book text.

### Development dependency layout

During release preparation, keep the checkpoint directory layout intact.
`verso/release/lakefile.toml` has two deliberate path dependencies:

```toml
[[require]]
name = "verso"
path = "../../toolchain-spike/.lake/packages/verso"

[[require]]
name = "RepresentationTheoryFormalization"
path = "../../clean-code/release"
```

From `verso/release/`, the formalization path resolves to the staged public
project in the same checkpoint. The Verso path resolves to the dependency
fetched by the sibling `toolchain-spike/` project. On a cold checkout, populate
that path before building the private project:

```bash
cd toolchain-spike
lake update
cd ../verso/release
lake update
cd ../..
```

Do not clone or move `verso/release/` as an independent development checkout;
doing so breaks both relative dependencies. The final materializer replaces
the formalization path dependency with the exact clean public Git commit and
replaces the development Verso path with its configured pinned Git dependency.

Do not create either final GitHub repository until every completion gate near
the end of this document passes.

## Publication-boundary and clean-room rules

The public checkpoint currently contains the complete work-in-progress corpus
to simplify handoff. That does not change the intended final repository
boundary: only the materialized `clean-code/release/` tree belongs in the final
public formalization repository. The book corpus, private mapping, packet
evidence, and alignment staging data must not be copied into that final public
repository.

### How independent review is enforced and recorded

“A different agent” means a genuinely fresh agent/session with no inherited
conversation from the creator. Give it only the specific `packet.json` and
`response.json` pair being reviewed, or an isolated directory containing only
those files. Do not give the review agent the original source checkout, book
blobs, private mapping, proposal aggregate, migration plan, or summaries of the
creator's mathematical reasoning.

The controller may know the canonical paths, but the review agent should see
only copies of the authorized pair. After review, copy back only an approved or
corrected `response.json`, then run the repository validator from the
checkpoint root. For migration reciprocal review, use a fresh agent that may
see the approved proposal, migrated target, and the specifically authorized
comment-stripped source module, but not unrelated response files.

The response schemas intentionally have no reviewer-identity field. Do not add
one. Record review persistently in Git instead:

- commit the creator's response first;
- make a separate reviewer commit for corrections;
- for an unchanged PASS, make an empty review commit with `git commit
  --allow-empty`; and
- name the reviewed packet/module paths, verdict, packet-only or reciprocal
  scope, and reviewer session/model in the commit message.

Thus the response file is the canonical decision, while the continuation
branch history proves that an independent pass occurred. Do not merge a batch
whose independent-review commit is absent.

### Clean-room declaration naming

For each module:

1. A naming agent reads only that module's `packet.json` and writes its sibling
   `response.json`.
2. That agent must not inspect the original Lean source, the book, the private
   mapping, manifests, or other responses.
3. A different agent independently reviews the response using only the same
   packet evidence.
4. Null, opaque, elided, and failed-pretty-print types require conservative
   `Auxiliary...` or `auxiliary...` names and docs. Never infer semantics from
   suggestive historical names.
5. Only after independent review should the repository validator update
   `manifests/alignment/cleanroom-proposals.jsonl`.

### Mechanical Lean migration

After names are independently approved, a migration agent may inspect the
original source and migrate it mechanically:

- use only approved public names and docstrings;
- preserve the complete executable command stream and order;
- preserve private declarations, anonymous `example`s, attributes, scoped
  commands, `omit` blocks, and proofs;
- replace imports and internal references only according to the approved
  dependency plan; and
- never solve a missing dependency by importing tainted code or silently
  inlining another module's declarations.

A different agent must then compare the migration with the comment-stripped
source and reciprocally review it.

Comment stripping must be apostrophe-safe. An earlier implementation treated
apostrophes in identifiers such as `p'` as character-literal delimiters and
could retain trailing comments. The corrected approach understands nested
block comments and strings without treating an identifier apostrophe as the
start of a character literal.

There is currently no single repository-wide “comment stripper” executable.
The rule above describes the normalization used by migration and reciprocal
review. `build_filtered_code_workspace.py` is the named script that produces
`clean-code/tainted/` from the pinned original source and
`manifests/module-disposition.json`; it copies the authorized modules but does
not strip their comments. Its invocation is:

```bash
python3 build_filtered_code_workspace.py \
  ../Etingof-draft-source \
  manifests/module-disposition.json \
  clean-code/tainted
```

The checkpoint already contains the filtered source. Regenerate it only after
an intentional disposition/source change, because the command replaces that
output tree. Any future shared stripping helper must preserve nested block
comments and strings while treating apostrophes inside Lean identifiers as
identifier characters.

### Alignment adjudication

For each alignment packet:

1. One agent reads only `packet.json` and creates or reviews `response.json`.
2. A different agent reviews the roles using only displayed packet evidence.
3. Use `primary` only when the displayed formal type directly states the
   source claim.
4. Use `supporting` for null, opaque, elided, contextual, prerequisite,
   helper, proof-strategy-only, or merely consequence-level candidates.
5. Merge only after independent review and an exact before/after audit proving
   that no unrelated association changed.

Do not run concurrent aggregate Lake builds in `clean-code/release/`. Shared
cache races can transiently remove or stale `.olean` and `.ilean` files.

## Current verified state at checkpoint

The following figures describe commit
`112df00abbe56f6a4820465ef57ec12553b7fcd8`.

### Verso conversion and assembly: complete

Do not redo the item conversion.

- 583 approved semantic items are accounted for.
- 581 items render as `Content.lean` documents.
- one Chapter 4 introduction is projected inline into chapter Structure;
- one Chapter 2 heading-only item is represented only by Structure;
- 109 semantic `Structure.lean` modules are generated;
- every normal item is included exactly once under its semantic chapter,
  section, or subsection parent;
- native tables and footnotes are repaired, with no legacy `$^n$` markers;
- 59 Content modules currently contain formalization panels;
- the public alignment export and private panels agree at 154 rows;
- panel synchronization is idempotent;
- the full private build and render passed; and
- 701 HTML pages were produced, with all 154 rendered formalization references
  resolving and zero validation errors.

The private tree also retains the original page-level Markdown transcription
under `verso/source-markdown/` and the semantic book metadata under
`verso/metadata/`.

Whenever public `source_ref` metadata changes, regenerate panels and rerun the
private build/render gates.

### Clean-room naming: incomplete

Latest validated inventory:

- 204 response modules;
- 3,486 declaration responses;
- 796 eligible source modules;
- 202 fully named modules;
- 2 partially named modules;
- 12 directly blocked modules;
- 1 transitively blocked module; and
- 189 currently export-ready modules.

Therefore 594 eligible modules are not yet fully named. The reviewed frontier
includes module-0194, but numbering is sparse and some later modules already
have responses. The canonical packet inventory is
`clean-room-packets/index.json`. Iterate its `packets` entries and select the
first canonical packet whose sibling `response.json` is absent; do not infer
the next packet from its numeric suffix.

Validation and plan refresh:

```bash
python3 validate_cleanroom_responses.py \
  clean-room-packets \
  ../Etingof-draft-source/blobs \
  manifests/alignment/cleanroom-private-mapping.jsonl \
  manifests/alignment/cleanroom-proposals.jsonl

python3 plan_clean_migration.py \
  ../Etingof-draft-source \
  manifests/module-disposition.json \
  manifests/alignment/cleanroom-private-mapping.jsonl \
  manifests/alignment/cleanroom-proposals.jsonl \
  clean-migration-plan.json
```

Do not commit `clean-migration-plan.json` unless it is intentionally promoted
to a tracked manifest.

### Alignment adjudication: incomplete

Response inventory, including the newest unmerged batch:

- 483 responses out of 1,267 alignment packets;
- 821 validated association decisions in response files; and
- 784 packets without responses.

Merged aggregate state:

- 803 adjudicated edges;
- 1,722 pending edges; and
- reviewed batches merged through `align-0495`.

Immediate unmerged work:

- `align-0496` through `align-0505` have packet-only responses;
- the batch contains 18 associations: 6 primary and 12 supporting;
- it has not received independent packet-only review; and
- it has not been merged.

First assign a different reviewer to those ten packets. After they pass,
preserve the current aggregate for comparison, merge, and prove that only the
intended association IDs changed:

```bash
python3 validate_alignment_adjudications.py alignment-adjudication-packets

cp manifests/alignment/adjudicated-alignment-edges.jsonl \
  adjudicated-alignment-edges.before.jsonl

python3 merge_alignment_adjudications.py \
  alignment-adjudication-packets \
  manifests/alignment/alignment-edges.jsonl \
  manifests/alignment/adjudicated-alignment-edges.jsonl
```

Remove or archive the local `*.before.jsonl` comparison file after the audit;
do not accidentally publish it.

Then continue with independently reviewed ten-packet batches beginning at
`align-0506`, while respecting already existing sparse responses. The
canonical alignment inventory is `alignment-adjudication-packets/index.json`;
use it, rather than directory-number guesses, to identify missing responses.

### Public Lean migration: incomplete but green

Current validated public release:

- 98 proposal-backed modules;
- 981 exported proposal declarations;
- 101 Lean files including umbrella/support files;
- 154 exported `source_ref` attributes on 136 declarations;
- export validator: 0 errors;
- exact reference validator: 154 expected, 154 actual, 0 errors; and
- public leak scanner: 0 errors.

The recent dependency-first chain now present includes:

- module-0132 `RingTheory.SimpleModuleAnnihilator`;
- module-0144 `Algebra.Module.EndomorphismDichotomy`;
- module-0184 `Algebra.Module.IndependentSpanningFamilies`;
- module-0146 `Algebra.Module.FiniteDecompositions`;
- module-0147 `Algebra.Module.TensorScalarExtension`;
- module-0148 `Algebra.Module.EquivalenceTransfers`;
- module-0149 `Algebra.Module.FinitelyGeneratedSubalgebraDescent`;
- module-0150 `Algebra.Module.TensorRestriction`;
- module-0151 `LinearAlgebra.TensorProduct.ModuleBaseChange`;
- module-0152 `Algebra.Module.TensorSplitDescent`;
- module-0153 `Algebra.Module.TensorEquivDescent`;
- module-0154 `Algebra.Module.TensorProductCoordinates`; and
- module-0179 `Algebra.Semisimplicity.EndomorphismProduct`.

The dependency chain through module-0154 has reciprocal review. Module-0179
passed focused, root, export, reference, and leak gates but still needs an
independent reciprocal migration review. Its sole current reference is primary
`Chapter3/Theorem3.5.4`.

Public gates:

```bash
cd clean-code/release
lake build RepresentationTheory alignmentExport

python3 ../../validate_clean_release_exports.py \
  . ../../manifests/alignment/cleanroom-proposals.jsonl

python3 ../../validate_clean_release_source_refs.py \
  . \
  ../../manifests/alignment/cleanroom-proposals.jsonl \
  ../../manifests/alignment/adjudicated-alignment-edges.jsonl \
  ../../manifests/alignment/source-nodes.jsonl

python3 ../../scan_clean_release.py . ../../verso/source-markdown
cd ../..
```

The “rename audit” named in the completion gates is
`audit_ilean_rename_coverage.py`. It checks the tainted workspace's Lean
identifier indexes against the approved old→new proposal mapping. It requires
a current tainted build and writes a JSON report:

```bash
cd clean-code/tainted
lake build EtingofRepresentationTheory
cd ../..

python3 audit_ilean_rename_coverage.py \
  clean-code/tainted \
  manifests/alignment/cleanroom-proposals.jsonl \
  reports/ilean-rename-audit.json
```

An audit is successful only when its summary reports zero errors. Refresh it
after proposal or migrated-dependency changes that affect rename coverage.

The source-reference validator intentionally collapses duplicate
`(declaration, canonical item reference)` expectations, with `primary` taking
precedence. The panel synchronizer uses the same rule.

### Legal, workflows, and materialization: implemented

Already staged:

- both required `README.md` and `LICENSE` files, plus public `NOTICE`;
- public CI and notification workflows;
- private CI, dependency updater, and access-controlled artifact workflow;
- no Pages deployment;
- deterministic alignment export and panel synchronization;
- legal and complete-release validators; and
- `materialize_release_repositories.py`, including deterministic copying,
  build-artifact exclusion, dependency-pin rewriting, optional clean Git
  initialization, and self-tests.

Current results:

- `validate_release_legal_metadata.py`: pass;
- `materialize_release_repositories.py --self-test`: pass;
- full private build/render: pass, 701 pages; and
- rendered formalization validation: 154/154, zero errors.

The complete release-candidate validator intentionally fails at present
because naming, adjudication, and migration are unfinished. This is expected;
do not weaken its `--require-all` or completeness checks.

`validate_release_candidate.py` takes no positional arguments. Run the final
end-to-end gate from the checkpoint root as:

```bash
python3 validate_release_candidate.py
```

It invokes the require-all response gate, merges the complete adjudication
ledger, checks proposal completeness, builds the public project, validates
exports/references/leaks/native Verso, reassembles and renders the private
project, validates rendered links and legal metadata, and runs the materializer
self-test. Run it only on a clean, quiescent continuation branch and inspect
the resulting diff. Do not use `--help`: the script has no help parser and is
the gate itself.

## Scale and prioritization

This is a sustained multi-session conversion, not a one-session cleanup. At
the checkpoint there are 594 modules still to name, 784 alignment packets still
to adjudicate, and about 698 eligible modules not yet in the public Lean tree;
each semantic decision or migration also needs an independent pass.

Use this priority order:

1. Close the tiny immediate review backlog (module-0179 and align-0496–0505),
   keeping the current green state green.
2. Name modules on the dependency frontier shown as ready or directly blocking
   export-ready work in the generated migration plan.
3. Migrate the smallest export-ready dependency leaves, then reciprocally
   review them before starting long downstream chains.
4. Process alignment in independent ten-packet batches continuously; merge only
   reviewed batches and immediately update affected migrated declarations.
5. Periodically recompute the migration plan rather than following numeric
   module order.

Independent naming, alignment adjudication, and reciprocal review can be
parallelized across agents. Shared aggregate edits and Lake builds must remain
serialized.

## Immediate continuation sequence

1. Independently reciprocally review migrated module-0179.
2. Independently review alignment responses `align-0496`–`align-0505` using
   packet evidence only.
3. Merge exactly that batch and run a before/after association-ledger audit.
4. Update `source_ref` attributes on any already migrated declarations affected
   by the merge.
5. Rebuild the public root and `alignmentExport`, then make export, exact-ref,
   and leak validators green.
6. Regenerate and verify private formalization panels:

   ```bash
   cd verso/release
   lake env lean --run AlignmentExport.lean > alignment-export.json
   python3 scripts/sync_formalization_panels.py alignment-export.json
   python3 scripts/sync_formalization_panels.py \
     --check alignment-export.json
   cd ../..
   ```

   Treat `alignment-export.json` as a generated local work file unless the
   project metadata explicitly designates it for tracking.

7. Continue clean-room naming from the next canonical missing packet after the
   currently reviewed frontier, always followed by an independent packet-only
   review.
8. Continue alignment in independently reviewed ten-packet batches from
   `align-0506` onward.
9. Continue dependency-first public migrations from the refreshed migration
   plan. Follow missing dependencies backward; never inline them or import
   tainted modules.
10. Reciprocally review each migrated file and remove unnecessary
    `RepresentationTheory.Alignment.Attribute` imports where a module exports
    no adjudicated references.
11. Periodically rebuild and rerender the private project after public
    reference changes.
12. Commit coherent checkpoints to the continuation branch. Push them to the
    operator-designated writable remote if credentials were supplied; otherwise
    explicitly report that remote backup is awaiting a human with write access.

## Completion gates before publication

Do not create or push the two final repositories until all of these are true:

- all 796 eligible modules are fully named;
- no partial, direct, or transitive naming blockers remain;
- all 1,267 alignment packets have independently reviewed responses;
- `validate_alignment_adjudications.py --require-all` passes;
- the merged adjudication ledger covers every intended edge;
- every approved proposal is mechanically migrated and independently
  reciprocally reviewed;
- the public root build, export validator, exact source-ref validator, rename
  audit, and leak scan all pass;
- panel synchronization is idempotent;
- the complete private Verso build/render passes;
- every exported formalization reference resolves in rendered HTML;
- the legal validator passes;
- `validate_release_candidate.py` passes without weakening any gate;
- materializer self-tests pass; and
- two independent materializations are byte- and mode-identical apart from
  the deliberately rewritten public dependency pin.

## Final publication procedure

Only after every gate passes:

1. Use `materialize_release_repositories.py` to create two fresh empty output
   trees.
2. Use its clean-history mode with `--init-git --derive-clean-rev`, so the
   public repository receives one root commit and the private repository pins
   that exact public root commit.
3. Confirm the materialized public tree contains none of the book corpus,
   private mapping, clean-room packets, alignment packets, staging manifests,
   process notes, caches, or path dependencies.
4. Confirm the private materialization contains no caches, process traces,
   local path dependencies, or unintended Git metadata.
5. Have the designated human or service account with FormalFrontier
   organization rights use authenticated `gh` to create public
   `FormalFrontier/EtingofRepresentationTheory` and private
   `FormalFrontier/EtingofRepresentationTheory-verso`.
6. Push the single clean root commit to each repository.
7. Configure default branches, branch protection, required CI, and the private
   updater credentials/secrets.
8. Confirm the private repository has no public Pages deployment and all
   rendered artifacts remain access-controlled.
9. Inspect actual workflow job state and logs with `gh run view` or `gh api`,
   not only `gh pr checks`.

Never publish the checkpoint branch itself as either final repository. Never
publish the original development history, source book corpus, clean-room or
alignment packets, private mappings, or staging metadata in the public
repository.

## Useful top-level files and directories

- `clean-code/release/`: staged public Lean repository.
- `clean-code/tainted/`: private filtered source used only for mechanical
  replay and comparison.
- `verso/release/`: staged private AMS Verso repository.
- `clean-room-packets/`: packet-only public-name work.
- `alignment-adjudication-packets/`: packet-only source-alignment decisions.
- `manifests/alignment/`: private mappings, proposals, source nodes, and merged
  alignment ledger.
- `manifests/book/`: semantic book manifests.
- `clean-room-packets/index.json`: canonical clean-room packet inventory.
- `alignment-adjudication-packets/index.json`: canonical alignment packet
  inventory.
- `build_filtered_code_workspace.py`: reconstructs the authorized tainted
  migration workspace from the pinned original checkout.
- `validate_cleanroom_responses.py`: clean-room response validator.
- `plan_clean_migration.py`: dependency/readiness planner.
- `validate_alignment_adjudications.py`: alignment response validator.
- `merge_alignment_adjudications.py`: reviewed-alignment merger.
- `validate_clean_release_exports.py`: public proposal/export checker.
- `validate_clean_release_source_refs.py`: exact public-reference checker.
- `audit_ilean_rename_coverage.py`: identifier-index rename coverage audit.
- `scan_clean_release.py`: public leak scanner.
- `validate_release_legal_metadata.py`: legal/repository-policy validator.
- `validate_release_candidate.py`: complete end-to-end gate.
- `materialize_release_repositories.py`: final deterministic splitter and
  clean-history materializer.

The checkpoint branch is publicly cloneable and intentionally contains both
publication sides for this handoff. It is only a staging checkpoint: do not
mistake its contents or history for either final repository. The materializer
must still produce two policy-checked clean-history trees, with the aligned AMS
Verso repository created as private.
