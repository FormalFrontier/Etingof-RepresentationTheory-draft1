# Etingof Representation Theory

This repository contains an independently written Lean 4 formalization of
representation theory. It covers mathematical material also treated in:

> Pavel Etingof, Oleg Golberg, Sebastian Hensel, Tiankai Liu, Alex Schwendner,
> Dmitry Vaintrob, and Elena Yudovina, with historical interludes by Slava
> Gerovitch, *Introduction to Representation Theory*, Student Mathematical
> Library 59, American Mathematical Society, 2011. ISBN 978-0-8218-5351-1.
> [AMS catalogue entry](https://bookstore.ams.org/stml-59/)

The Lean source was written independently and does not quote or reproduce the
book's prose. Some declarations carry machine-readable `source_ref` metadata
identifying related locations in the book, including numbered results,
discussions, introductions, and section headings. These references are
provided for scholarly cross-reference and allow aspects of the book's
numbering and organization to be inferred. The formalization's Lean code,
proofs, declaration names, and module structure were written independently.

The American Mathematical Society has a corresponding access-controlled
repository containing the complete book text together with a Verso rendering
of the alignment to this formalization. The mathlib-initiative organization
hosts that repository on the AMS's behalf. It is not publicly available at
this time.

## Building

The project uses Lean 4 and Mathlib. After cloning, run:

```text
lake update
lake exe cache get
lake build
```

## License

Copyright 2026 mathlib-initiative.

The Lean formalization in this repository is licensed under the
[Apache License, Version 2.0](LICENSE). See [NOTICE](NOTICE).
