# Stage 3.2 review — Chapter 8, §8.2

Section 8.2 is complete within the project's documented sound scope. Projective and free
resolutions, the general-ring Tor functor, Ext via Hom cohomology, resolution independence,
zeroth identifications, Ext¹ comparison, both-variable long exact sequences, balancing, and the
horseshoe construction are all formalized. The old #7510 Tor-definition regression is gone.

The PID computations cover all finitely generated abelian groups and k[x]-modules. Problem 8.2.8
proves the Tor Künneth formula in the source's scope, formally refutes the book's false literal Ext
scope in degree zero, and proves the strongest usable corrected theorem under degreewise finite
projective hypotheses plus its finite-dimensional corollary. Its `covered_partial` label is
intentionally retained as the documented source correction required by `skipped-exercises.md`,
not as unfinished work.

Exercise 8.2.9 handles both categories without nonzero projectives and the finitely generated
module category with enough projectives. Problem 8.2.10 constructs the ordinary, direct-sum,
bimodule, and arbitrary-module Koszul resolutions, proves Hilbert syzygy vanishing, and computes
Tor and Ext of the trivial module.

Fresh checks pass for every Chapter 8 provider and the full chapter build. Clean-source repairs
added explicit instance transparency throughout the tensor, derived-functor, external-tensor,
rearrangement, bar, and Koszul support graph. The bar and Koszul homotopies also received explicit
sign-transport proofs where definitional equality was too fragile. All detailed exercise ledgers
are preserved and updated.
