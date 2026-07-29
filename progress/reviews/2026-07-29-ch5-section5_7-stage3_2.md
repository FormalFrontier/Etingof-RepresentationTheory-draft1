# Stage 3.2 review — Chapter 5, §5.7

The four §5.7 records are fully covered. `Etingof.VirtualRepresentation` is the free abelian
group on irreducible isomorphism classes, with coefficients, addition, negation, dimension,
and character maps. In particular, `character_apply` and `character_single` give exactly the
integer-linear-combination character formula in Definition 5.7.1.

`Etingof.Lemma5_7_2` formalizes the complete irreducibility criterion: orthonormality turns
character norm one into a coefficient vector with one coefficient equal to `±1`, and positivity
at the identity rules out the negative choice. Both provider files pass fresh source checks
without warnings.
