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

  **Counting sorries accurately:** do NOT report `grep -rc sorry` as the sorry
  count. This repo documents *where sorries are and are not* in docstrings
  ("sorry-free", "isolated `sorry`", "sorry'd dependency (#N)"), which inflates
  the raw grep by ~18× (e.g. 76 raw vs 4 real, as of #5018). Strip comments
  first, then count whole-word `sorry` in the surviving code, and also check for
  `axiom`/`admit` (sorry-equivalents that don't use the keyword). A
  comment-stripping awk pass:
  ```bash
  cat > /tmp/sorrycount.awk <<'AWK'
  BEGIN{depth=0}
  {line=$0; out=""; i=1; L=length(line)
   while(i<=L){two=substr(line,i,2)
     if(depth>0){if(two=="-/"){depth--;i+=2;continue} if(two=="/-"){depth++;i+=2;continue} i++;continue}
     else{if(two=="/-"){depth++;i+=2;continue} if(two=="--")break; out=out substr(line,i,1); i++}}
   s=out
   while(match(s,/(^|[^A-Za-z0-9_'"'"'])sorry([^A-Za-z0-9_'"'"']|$)/)){cnt++;print FILENAME":"FNR;s=substr(s,RSTART+RLENGTH-1)}}
  END{print "REAL_SORRIES="cnt > "/dev/stderr"}
  AWK
  find EtingofRepresentationTheory -name '*.lean' | sort | xargs awk -f /tmp/sorrycount.awk
  ```
  Report both the raw `grep -rc` per-file numbers (the verification spot-checks
  against these) AND the real comment-stripped count, and explain the gap.

### Step 5: Produce an updated progress document

Write an updated progress document that:

- **Accurately reflects** current quality metrics and phase
- **Describes the architecture structurally** (layers, relationships)
- **Identifies flaws and limitations honestly** (scope restrictions,
  remaining work, gaps between goals and achievements)
- **Is honest in its framing** — don't overstate what has been achieved

## Constraints

- Do NOT modify any code or implementation files
- Commit ONLY the progress document changes
- The progress entry should note what changed and why

## Reflect

Run `/reflect` before finishing.
