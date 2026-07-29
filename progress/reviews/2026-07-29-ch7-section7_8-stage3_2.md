# Stage 3.2 review — Chapter 7, §7.8

Section 7.8 is complete. Complexes, differentials, cohomology, exactness, complex morphisms,
boundedness, and short exact sequences are represented directly. The canonical biproduct short
exact sequence has an explicit splitting and a pinned downstream signature test.

Exercise 7.8.4 decomposes every exact vector-space complex into two-term identity disks, derives
splitting of short exact vector-space sequences, and supplies a concrete abelian-group
counterexample. Problem 7.8.5 constructs the connecting map at representative level, proves its
choice independence, identifies it with the categorical boundary map, and proves the long exact
sequence. Problem 7.8.7 constructs the tensor complex, proves preservation of exactness over a
field, splits arbitrary complexes into exact and cohomology pieces, and establishes the natural
Künneth isomorphism.

Fresh checks pass for all fourteen §7.8 providers and support modules. Five files needed explicit
instance transparency to repair hidden clean-source regressions in homological-complex and
reindexing arguments. The three detailed final-exercise ledgers are preserved and updated.
