# Execute a Summarize Work Item

You are a **summarize** session. Your job is to produce an accurate summary of
project progress that honestly identifies both achievements and limitations.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to summarize sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label summarize` to find work for this session type.

## The Summary Task

### Step 1: Read the project specification

Find and read the top-level specification/roadmap document to understand the
project's intended goals. This is the ground truth against which you measure progress.

### Step 2: Read the current progress document

Understand what the project currently claims to have achieved.

### Step 3: Survey recent work

- Read the last 15 entries in `progress/` (sorted by filename, most recent last)
- Fetch titles of PRs merged since the last `summarize` issue was closed

### Step 4: Inspect the codebase

- List source files and read their module-level docstrings
- Read key top-level declarations/signatures (not full implementations)
- Record current quality metrics as described in the project's CLAUDE.md

### Step 5: Produce an updated progress document

Write an updated progress document that:

- **Accurately reflects** current quality metrics and phase
- **Describes the architecture structurally** (layers, relationships)
- **Identifies flaws and limitations honestly** (scope restrictions,
  remaining work, gaps between goals and achievements)
- **Is honest in its framing** — don't overstate what has been achieved

## Constraints

- Do NOT modify any code or implementation files
- Commit ONLY the progress document (and `progress/items.json` if you reconcile statuses)
- The progress entry should note what changed and why

## Reconciling `progress/items.json` (if you correct statuses)

- **Preserve the file's exact formatting.** It is `json.dump(..., indent=2,
  ensure_ascii=False)` with literal unicode and **no trailing newline**. A
  round-trip with any other indent (e.g. `indent=1`) or `ensure_ascii=True`
  reformats all ~592 entries into a 15k-line diff. Dump with
  `json.dumps(d, indent=2, ensure_ascii=False)` and `open(path,'w').write(s)`
  (no extra newline), then `git diff --stat` to confirm only your status lines
  changed.
- **A sorry-free file is not proof that an item is done.** Statements recorded
  via `proof_wanted` (e.g. `Remark2_9_3.lean` — Ado's theorem) are genuinely
  unproved yet carry 0 `sorry` tactics. Before promoting to `sorry_free`,
  require: status signals an *incomplete proof* (`statement_formalized` /
  `proof_partial`); **all** covering files have 0 genuine sorries; **no**
  covering file uses `proof_wanted`; **no** sibling file for the same problem
  (e.g. `Problem5_24_1_b.lean`) carries a sorry. Leave terminal-vocab
  (`proved`/`proof_complete`/`formalized`) and coverage-partial
  (`partially_proved`/`accepted`) statuses alone and document them as audit
  candidates rather than guessing their intent.

## Reflect

Run `/reflect` before finishing.
