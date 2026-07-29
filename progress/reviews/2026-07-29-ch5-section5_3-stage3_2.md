# Stage 3.2 review — Chapter 5, §5.3

## Scope and result

This review covers the five records from `Chapter5/Introduction_5.3` through
`Chapter5/Exercise5.3.3`. Every formalizable source claim is represented by an admission-free
declaration with verified fidelity and nonvacuity. The exercise retains its detailed final-exercise
claim ledger; its stale `partially_proved` status has been normalized to `sorry_free`.

## Frobenius divisibility

`Etingof.Proposition5_3_2` constructs the integral class sum, proves that it acts by a scalar on
an irreducible representation, identifies that scalar by taking traces, and proves that
`|C| chi(g_C) / dim(V)` is an algebraic integer. `FDRep.character_isIntegral` proves the required
integrality of finite-group character values.

`Etingof.Theorem5_3_1` carries out the remaining book argument. It regroups the character sum by
conjugacy classes, uses `FDRep.char_orthonormal` to identify it with `|G|/dim(V)`, and applies
`Etingof.Proposition5_2_5` to conclude that this rational algebraic integer is an integer. Its
public endpoint is exactly `Module.finrank C V ∣ Fintype.card G`.

Finally, `Etingof.isComplexType_of_odd_order_of_nontrivial_irreducible` proves Exercise 5.3.3:
every nontrivial irreducible representation of an odd-order group is of complex type, using the
even-dimensionality of the quaternionic case to exclude the remaining self-dual possibility.
