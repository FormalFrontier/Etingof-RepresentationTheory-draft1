# EtingofRepresentationTheory

## Project scope

The project aims to formalize the mathematical content of Etingof's representation
theory text. Deliberate exceptions are recorded in
[Intentional omissions and exercise scope](skipped-exercises.md). That document
distinguishes project-wide omissions from work that is merely incomplete or outside
the scope of a particular issue. Exercises deferred to a later import point, with
partial results recorded now, are tracked separately in
[Deferred reprises](deferred-reprises.md).

Project completion requires zero accidental `sorry` or `admit` terms and zero
project axioms. Every `proof_wanted` must instead be individually enumerated and
justified in the scope document, with matching machine-readable approval metadata
in `progress/items.json`. The currently approved Ado–Iwasawa marker in Remark
2.9.3 is non-blocking; no future marker inherits that exception automatically.
Run `scripts/check_proof_placeholders.py --enforce-completion` to check these
release criteria.

The mathematical formalization reached this completion gate on 2026-07-29:
the scanner reports zero blocking placeholders, the exercise ledger reports no
untracked gaps, and the sole wanted theorem is the explicitly approved Ado–Iwasawa
scope marker. The post-formalization dependency-trimming and style-polishing
workflow remains tracked separately and does not change this scope decision.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
