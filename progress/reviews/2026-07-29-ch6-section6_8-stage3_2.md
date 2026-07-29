# Stage 3.2 review — Chapter 6, §6.8

Section 6.8 is complete. The admissible sink ordering exists for every Dynkin orientation and
can be repeated through the changing orientations. Theorem 6.8.1 has both its numerical
root-reflection endpoint and its source-faithful categorical endpoint: an arbitrary
finite-dimensional indecomposable is carried by actual reflection functors to an indecomposable
with simple-root dimension vector.

The corollaries establish that every indecomposable dimension vector is a positive root, that
two indecomposables with the same dimension vector are isomorphic, and that every positive root
is realized by an indecomposable for the chosen orientation. Example 6.8.5 computes the displayed
D₄ sequence through actual reflection functors and identifies the maximal-root representation's
three one-dimensional images inside its two-dimensional centre.

Fresh source checks pass for the numerical theorem, Coxeter infrastructure and public test, all
three corollaries, and every D₄ computation provider. `Corollary6_8_4.lean` needed explicit
instance transparency for its dependent reversed-orientation induction. The stale #7509, #7436,
and inherited #7490 blockers are removed.
