# Stage 3.2 review — Chapter 6, §6.5

Section 6.5 is complete. The dimension vector is the vertexwise finite dimension. Gabriel's
theorem is exposed through separate public clauses and a combined endpoint: finite representation
type is equivalent to Dynkin type; every indecomposable has a positive-root dimension vector;
and every positive root is realized by a unique indecomposable isomorphism class.

Fresh source checks pass for the dimension-vector definition, all Gabriel-theorem clauses, the
combined theorem, and the downstream public-signature test. The stale #7518 source-regression
record is removed; no module-instance or zero-dimension elaboration failure remains.
