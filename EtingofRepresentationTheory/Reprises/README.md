# Deferred reprises

This directory is reserved for faithful completions of exercises whose original
location occurs before the project has the needed infrastructure. It contains
documentation only until a reprise is implemented; no placeholder Lean theorem
should be added.

## Planned reprise: Problem 2.16.4

The eventual file is `EtingofRepresentationTheory/Reprises/Problem2_16_4.lean`.
It must import and cross-reference `Chapter2/Problem2_16_4.lean`, then provide the
missing parameter family, irreducibility proof, isomorphism criterion, and
exhaustiveness theorem. When that file exists, add a `Reprises.lean` aggregator
and import it from the project root like the chapter aggregators.

The current Chapter 2 source contains useful partial results, but its fresh-source
build is temporarily blocked by regression #7531. Repairing that regression does
not complete or cancel this reprise.
