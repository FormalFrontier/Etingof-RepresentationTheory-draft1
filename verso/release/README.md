# Introduction to Representation Theory — aligned Verso edition

This access-controlled repository contains the complete text of:

> Pavel Etingof, Oleg Golberg, Sebastian Hensel, Tiankai Liu, Alex Schwendner,
> Dmitry Vaintrob, and Elena Yudovina, with historical interludes by Slava
> Gerovitch, *Introduction to Representation Theory*, Student Mathematical
> Library 59, American Mathematical Society, 2011. ISBN 978-0-8218-5351-1.
> [AMS catalogue entry](https://bookstore.ams.org/stml-59/)

The text is rendered as a section/subsection/item-structured Verso book and is
aligned with the independent Lean formalization in
[`mathlib-initiative/EtingofRepresentationTheory`](https://github.com/mathlib-initiative/EtingofRepresentationTheory).
The Lean repository is pinned as a Git dependency, so an approved dependency
update refreshes the formalization displayed by this book.

The complete page-level Markdown transcription is retained verbatim in
`source-markdown/`. Semantic chapter/section/subsection/item metadata lives in
`metadata/`; generated Verso navigation is driven by that metadata rather than
by source page boundaries. The native item modules under
`IntroductionToRepresentationTheoryVerso/Content/` are the reviewed,
item-by-item Verso conversions of the Markdown corpus.

Formalization panels are not maintained by hand. `AlignmentExport.lean`
exports the `source_ref` attributes from the exact pinned public revision, and
`scripts/sync_formalization_panels.py` maps those references to semantic item
IDs and deterministically regenerates the corresponding Verso panels. Private
CI rejects any panel set that is stale with respect to the pinned dependency.

## Copyright and ownership

Copyright © 2026 American Mathematical Society. All rights reserved.

mathlib-initiative hosts this private repository on behalf of the American
Mathematical Society and assisted with the technical preparation of the Verso
alignment. mathlib-initiative disclaims any copyright, ownership, or other
intellectual-property claim in the book, its text, and this aligned edition.
See [LICENSE](LICENSE) for the repository's access and use terms.

This repository and its rendered output are not public. Do not publish, copy,
distribute, or grant access without express authorization from the American
Mathematical Society.

## Building

The formalization dependency is pinned by Git URL and revision in
`lakefile.toml`; no local copy is included. To build the private site:

```text
lake update
lake env lean --run AlignmentExport.lean > formalization-alignment.json
python3 scripts/sync_formalization_panels.py --check formalization-alignment.json
lake build
python3 scripts/build_site.py
```

Continuous integration uploads the rendered site as an access-controlled build
artifact. It does not deploy GitHub Pages.
