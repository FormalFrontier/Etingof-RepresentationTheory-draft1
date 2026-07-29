# Stage 3.2 review — Chapter 7, §7.9

Section 7.9 is complete. Additive and k-linear functors, preservation of biproducts, left/right
exactness, exact functors, and semisimple abelian categories are represented directly. Induction,
restriction, and representation Hom are proved additive and linear, while categorical Maschke
gives the semisimple finite-group example and exactness of additive functors from semisimple
categories.

Example 7.9.6 proves exactness of restriction and finite-index induction, left exactness and the
failure of right exactness for Hom, and arbitrary-ring right exactness plus failure of left
exactness for balanced tensor, with the requested Z/2 counterexamples. Exercise 7.9.7 derives
the exactness sides of additive adjoints. Exercise 7.9.8 packages the reflection functors as an
adjunction and obtains their exactness consequences.

Fresh source checks pass for all eleven §7.9 providers. `Example7_9_6.lean` needed explicit
instance transparency in its balanced-tensor quotient arguments. Both detailed exercise ledgers
are preserved and updated.
