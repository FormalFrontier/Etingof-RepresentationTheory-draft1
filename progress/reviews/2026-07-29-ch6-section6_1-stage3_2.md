# Stage 3.2 review — Chapter 6, §6.1

Section 6.1 is complete modulo only the exact McKay-classification units explicitly listed in
`skipped-exercises.md`. Problems 6.1.1 and 6.1.2 establish the transcendence-degree and orbit
dimension tools. Problem 6.1.3 formalizes the finite and affine simply-laced Dynkin diagrams,
their determinant and positivity calculations, the obstruction arguments, and both exhaustive
classifications. Definition 6.1.4 and the public Dynkin-classification theorem expose the book's
notion and ADE list.

Problem 6.1.5 proves the finite-representation-type iff Dynkin theorem. Its three requested
steps—finite orbit reduction, positivity of the Tits form, and exclusion/classification—are
present in the detailed `final-exercise-audit` ledger. Problem 6.1.6 proves symmetry and
connectivity of the McKay graph, its affine-Cartan conclusion, and the kernel-vector statement;
the two-vertex normalization and family-by-family finite-subgroup identification remain the
explicit accepted omission recorded in `skipped-exercises.md`.

Fresh source checks pass for all section providers. This audit repaired four hidden regressions:
matrix-instance transparency in `DynkinTypes.lean`, the E7/E8 and affine-E providers, and the
orbit-finiteness realization/decomposition bridge. The downstream finite-type theorem also
passes a fresh check. The stale #7525 and #7518 blockers are therefore removed.
