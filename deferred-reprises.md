# Deferred reprises

Some exercises occur before the formalization has the infrastructure needed for a
faithful full solution. In those cases the original location may contain useful
partial results, while this document records a later reprise that must complete the
exercise.

A reprise is unfinished work, not an intentional omission. The original Lean file
and progress metadata must say exactly which claims are already proved and must not
describe partial coverage as a complete solution. The eventual reprise should live
at a later import point, where it can use the intervening infrastructure, and should
cross-reference the original problem.

## Problem 2.16.4 — irreducible representations of sl(2) in characteristic p

The Chapter 2 file proves:

- every finite-dimensional irreducible representation has dimension at most `p`;
- the bound is sharp, by constructing irreducible modules of dimension `p` (and,
  more generally, the standard modules of dimensions `1` through `p`).

These results are source-present and pass a fresh source check; regression #7531 restored the
existing partial endpoints. That completed compiler repair is separate from the missing
classification below.

It does not classify all irreducible modules up to isomorphism, as the exercise asks.
The source is `blobs/Chapter2/Problem2.16.4.md`; no later source item in the current
book transcription revisits this modular classification. Unlike the intentionally
omitted quantum-group enumeration in Problem 2.16.5, this is a bounded classical
classification whose highest-weight and characteristic-`p` central-character
infrastructure should be reusable. The formalization will therefore provide its
own later reprise once that infrastructure is available.

The reprise is complete only when it gives an explicit parameter family, proves each
member irreducible, identifies when two parameters give isomorphic modules, and
proves that every finite-dimensional irreducible module occurs in the family. The
intended eventual location is
`EtingofRepresentationTheory/Reprises/Problem2_16_4.lean`. The doc-only
[`Reprises/README.md`](EtingofRepresentationTheory/Reprises/README.md) records the
eventual import convention and acceptance scope; no placeholder Lean file is
created in the meantime.
