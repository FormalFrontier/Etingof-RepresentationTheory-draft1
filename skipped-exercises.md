# Intentional omissions and exercise scope

This document records omissions that are deliberate decisions about the scope of the
project. An item belongs here only when the project has decided not to formalize it,
not merely because it is difficult, unfinished, or outside the scope of one issue or
pull request.

An intentional omission is not a missing proof. The corresponding Lean file should
describe what is and is not formalized, link to this document, and contain no
`sorry`, `admit`, axiom, or proof-placeholder declaration for the omitted material.
Progress metadata should record partial coverage and the scope decision explicitly.

## Current intentional omissions

### Problem 2.13.1 — the Dehn invariant and Hilbert's third problem

Part (b), the irrationality of `arccos(1/3) / π`, is formalized. Parts (a) and
(c) are intentionally omitted: they require a theory of polyhedra, dissection and
scissors congruence, dihedral angles, and the Dehn invariant valued in
`ℝ ⊗_ℚ (ℝ / ℚ)`. Building that geometric infrastructure is outside the chosen scope
of this representation-theory formalization.

The omission is documented in
`EtingofRepresentationTheory/Chapter2/Problem2_13_1.lean`; it is not represented by
a placeholder theorem.

### Problem 2.16.5 — full quantum sl₂ classification

The quantum enveloping algebra and substantial structural results in both the
root-of-unity and non-root-of-unity cases are formalized. The exhaustive
classification of all finite-dimensional irreducibles up to isomorphism is
intentionally omitted. In particular, the existing highest-weight, eigenvalue,
central-scalar, semisimplicity, and dimension-bound theorems are not presented as
an enumeration theorem. Unlike the bounded modular `sl₂` reprise below, the
root-of-unity classification requires a substantial quantum-specific parameter
and case-analysis development that the project has chosen not to build.

This omission is documented in
`EtingofRepresentationTheory/Chapter2/Problem2_16_5.lean`; no unproved
classification declaration is introduced.

### Problem 6.1.6 — residual McKay-correspondence classification

The project has formalized the tautological representation, symmetry and
connectivity of the McKay graph, the affine-Cartan positivity argument for graphs
with at least three vertices, and the kernel equation for the dimension vector.
Problem 4.12.8's finite-subgroup classification is now available; nevertheless,
the project retains its original decision not to build the additional concrete
group-family-to-diagram identifications. Thus the residual part (d) decision below
is a deliberate scope boundary, not a claim that the prerequisite is still missing.
The following residual parts are intentionally omitted:

- the two-vertex double-edge `Ã₁` case, which is outside the simple-edge affine
  diagram model used by the current development;
- the family-by-family identification of cyclic, binary dihedral, and binary
  polyhedral groups with affine `A`, `D`, and `E` diagrams (part (d));
- the explicit normalized marks for every family beyond the proved kernel equation
  (the remaining content of part (e)).

These omissions are documented in
`EtingofRepresentationTheory/Chapter6/Problem6_1_6.lean`; no unproved headline
declaration stands in for them.

## Completed former exclusions

The following exercises appeared in the original hard-problem/skip list but were
subsequently formalized. The former scope decision is therefore superseded:

- Problem 2.7.5 — q-Weyl algebra;
- Problem 2.16.3 — the Lie algebras `g_n`;
- Problem 4.12.8 — finite subgroups of `SO(3)` and `SU(2)`;
- Problem 5.24.2 — invariants of matrix tuples;
- Problem 6.1.3 — finite and affine Dynkin diagrams;
- Problem 8.2.8 — Künneth formulas for Tor and Ext;

Their Lean files and `progress/items.json` are authoritative for the precise
coverage and hypotheses of the completed results.

## Reopened former exclusions

These exercises were removed from the original skip list after substantial
formalization, but a later fidelity audit found a remaining source-level endpoint.
They are active work, not intentional omissions:

- Problem 9.6.5 — an abstract quasi-inverse is proved, but the book's named balanced
  tensor/cokernel functor and its comparison maps remain to be constructed; see #6567.
