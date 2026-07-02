# Execute a Review Work Item

You are a **review** session. Your job is to claim and execute a pre-planned review
work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to review sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label review` to find work for this session type.

## Review Focus Areas

Each session should pick **one or two** focus areas and go deep, rather than
superficially covering everything. The issue body will specify what to focus on.
Rotate through these areas across sessions:

**Refactoring and code improvement** (top priority):
- Can code be simplified? Are there redundant steps?
- Would extracting a function/lemma improve readability or enable reuse?
- Are there generally useful constructions worth upstreaming?

**Slop detection**:
- Dead code, duplicated logic, verbose comments, unused imports
- Other signs of AI-generated bloat

**Idioms and best practices**:
- Are newer APIs or language features being used where appropriate?
- Opportunities to improve type safety, remove unsafe operations

**Toolchain**:
- Check if a newer stable toolchain release is available; upgrade if tests pass

**File size and organization**:
- Files over 500 lines are candidates for splitting; never let a file grow past 1000

**Security**:
- Check for new issues in recent code, verify past fixes

## Fidelity audits (Stage 3.7)

If your issue is a per-chapter fidelity audit (epic #5338), two things recur:

- **Editing `progress/items.json`:** change `fidelity`/`status` fields **surgically**
  — `grep -n` the item id, Read those ~15 lines, and `Edit` just the value. Never
  `json.load`+`json.dump` the whole file: the reserializer reflows indentation
  (the file is `indent=2`), key order, and unicode, producing a multi-thousand-line
  diff against the shared file. If you must script a bulk update, match the exact
  serialization (`indent=2, ensure_ascii=False`, no trailing newline) and check
  `git diff --stat` before committing.
- **Residual non-canonical verdicts:** a chapter's items may already be labeled by
  prior waves with non-canonical values (`faithful`/`partial`/`covered`) or a stale
  `gap` whose repair issue is already CLOSED. Don't re-audit from scratch — query
  items.json for non-canonical `fidelity` values, confirm each linked repair issue
  is CLOSED and the current Lean genuinely matches the book, then normalize to
  `verified`/`gap`. Reserve `gap` for a *present* statement that is vacuous or
  silently weaker; honestly-named partial coverage (e.g. an "existence half" with
  no masquerading full-theorem decl) is a coverage follow-up, not a fidelity gap.

## Updating Skills

When you discover a recurring pattern or encounter a situation not covered by
existing skills, update the relevant skill file or create a new one.

## Reflect

Run `/reflect` before finishing.
