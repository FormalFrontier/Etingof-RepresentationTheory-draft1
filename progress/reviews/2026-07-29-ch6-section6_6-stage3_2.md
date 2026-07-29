# Stage 3.2 review — Chapter 6, §6.6

Section 6.6 is complete. Sinks, sources, and vertex reversal are defined. Both reflection
constructions have their kernel/cokernel object assignments, internal arrow maps, actions on
representation morphisms, and categorical functor laws.

Proposition 6.6.5 proves surjectivity at a sink and injectivity at a source for the relevant
indecomposables. Proposition 6.6.6 proves both reflection round trips. Proposition 6.6.7 proves
that reflecting an indecomposable gives an indecomposable or zero, and Proposition 6.6.8 gives
the exact simple-reflection formula for the dimension vector in both cases.

Fresh source checks pass for every definition, functor implementation, public test, and
proposition provider. Three files needed explicit instance transparency for dependent reversed
quiver carriers; after that repair both round trips and both indecomposability proofs elaborate
directly. The stale #7524 and #7490 regression records are removed.
