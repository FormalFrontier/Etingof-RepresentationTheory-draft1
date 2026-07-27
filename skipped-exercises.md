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

### Problem 2.11.6 — standalone bimodule tensor calculus

The associativity isomorphism for relative tensor products and the bimodule
tensor–Hom adjunction are intentionally not rebuilt as a standalone API. The
book's only later use is to derive Frobenius reciprocity in Theorem 5.10.1, and
the formalization proves that theorem directly through Mathlib's representation
induction/restriction adjunction. Formalizing Problem 2.11.6 literally would
require a separate bimodule/universal-property layer over the project's custom
relative tensor product without adding a new downstream result.

The exact source statements, the downstream citation, and the replacement route
are documented in
`EtingofRepresentationTheory/Chapter2/Problem2_11_6.lean`. The file contains no
placeholder declaration for the omitted exercise.

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

### Remark 5.23.3 — the `𝔰𝔩(V)` complete-reducibility and highest-weight assertions

Remark 5.23.3 records two assertions about the Lie algebra `𝔰𝔩(V)`: every
finite-dimensional `𝔰𝔩(V)`-representation is completely reducible, and every
irreducible one is an `L_λ`. The book states both and then writes "we will not do
this here". Following the policy above, the project does not carry a declaration
for either assertion, and in particular does not record them as `proof_wanted`:
they are not results the book proves, so they are not proof obligations this
formalization inherits.

The rest of the remark is formalized. The group-level content — the restriction of
a `GL_N`-representation to `SL_N`, the triviality of the determinant character
there, the `SL_N`-equivariant isomorphism `L_λ ≅ L_{λ + c·1ᴺ}`, and the
well-defined surjection from `SLWeightParam N` (dominant weights modulo a
simultaneous constant shift) onto the isomorphism classes of the
`L_λ|_{SL_N}` — lives in
`EtingofRepresentationTheory/Chapter5/Remark5_23_3.lean`. The `dim V = 2` case
that the remark points at, complete reducibility for `𝔰𝔩(2)`, is proved
independently as `Etingof.Sl2Irrep.complete_reducibility` (Problem 2.15.1).

The group-level parametrization is now injective as well as surjective onto the
constructed restrictions.  In addition, `SLIrrepExhaustive.lean` defines intrinsic
algebraicity for `SL_N`, proves that algebraic `GL_N` representations remain
algebraic on restriction, and proves that every simple `SL_N` representation
equipped with an algebraic `GL_N` extension is one of the `L_λ|_{SL_N}`.
Unconditional exhaustiveness remains an ordinary work item: its exact missing
input is an extension theorem saying that every intrinsically algebraic simple
`SL_N` representation admits an algebraic `GL_N` extension.

### Problem 6.1.6 — residual McKay-correspondence classification

The project has formalized the tautological representation, symmetry and
connectivity of the McKay graph, the affine-Cartan positivity argument for graphs
with at least three vertices, and the kernel equation for the dimension vector.
Problem 4.12.8 supplies the `SO(3)` classification and substantial double-cover
infrastructure, while its exact `SU(2)` list still has the active residual #7281.
Independently of that residual, the project retains its original decision not to
build the additional concrete group-family-to-diagram identifications. Thus the
part (d) decision below is a deliberate scope boundary, not a temporary dependency
on completion of Problem 4.12.8.
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

The endpoints that are in scope remain source-present, but the file currently
fails a fresh source check. Regression #7550 tracks restoring those implemented
symmetry, connectivity, affine-Cartan, and dimension-vector results without
expanding the intentional-omission boundary above.

## Completed former exclusions

The following exercises appeared in the original hard-problem/skip list but were
subsequently formalized. The former scope decision is therefore superseded:

- Problem 5.24.2 — invariants of matrix tuples;
- Problem 6.1.3 — finite and affine Dynkin diagrams;
- Problem 8.2.8 — a corrected finite-dimensional Künneth theorem for Tor and Ext is
  formalized. The literal source statement for Ext omits necessary finiteness
  hypotheses and is false already in degree zero; the formalization deliberately
  uses the sound strengthened scope. See the erratum under "Documented source
  corrections" below, so this item is not recorded as literal `covered_full` in
  `progress/items.json`;

Their Lean files and `progress/items.json` are authoritative for the precise
coverage and hypotheses of the completed results.

## Documented source corrections

These items record places where the book's literal statement is mathematically
false or omits a necessary hypothesis, and the project deliberately formalizes a
corrected, sound version. Unlike an intentional omission, the corrected result is
fully proved; what is "departed from" is the source's exact scope, and that
departure is recorded here so coverage metadata stays honest.

### Problem 8.2.8 — the Ext Künneth formula needs finite-dimensional source modules

The book states the Ext Künneth formula

`Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ₖ Extᵐ_{A₂}(M₂, N₂)`

assuming only that the target modules `Nᵢ` are finite dimensional. That literal
statement is false. Already in degree zero, with `A₁ = A₂ = k` and `N₁ = N₂ = k`,
it reduces to the claim that the canonical map

`M₁* ⊗ₖ M₂* → (M₁ ⊗ₖ M₂)*`  (`TensorProduct.dualDistrib`)

is an isomorphism. This map is always injective but is **not surjective** once the
`Mᵢ` are infinite dimensional: the "diagonal" functional `eᵢ ⊗ eⱼ ↦ δᵢⱼ` on
`(ℕ →₀ k) ⊗ₖ (ℕ →₀ k)` is not a finite sum of decomposable functionals.

The corrected, sound theorem `Etingof.Problem_8_2_8_ext` therefore adds finite
dimensionality of `A₁, A₂, M₁, M₂` (finiteness of the `Mᵢ` is what lets the
resolving projectives be chosen finitely generated projective, which is exactly the
condition making the degreewise Künneth map an isomorphism). The `Tor` half
`Etingof.Problem_8_2_8_tor` holds in the book's stated scope.

The strongest sound form is stated under minimal usable hypotheses by
`Etingof.Problem_8_2_8_extₖ`: it does not ask for finite dimensionality at all, only
for projective resolutions `Pᵢ` of the `Mᵢ` that are degreewise finitely generated
projective over `Aᵢ` (`Module.Finite`), which is the actual condition the proof
uses. The finite-dimensional `Problem_8_2_8_ext` is the convenient corollary,
obtained by feeding in the (finitely generated projective) bar resolution.

- Corrected theorem and its module machinery:
  `EtingofRepresentationTheory/Chapter8/Problem8_2_8.lean`.
- Formalized degree-zero counterexample
  (`TensorProduct.dualDistrib_not_surjective`):
  `EtingofRepresentationTheory/Chapter8/Problem8_2_8Counterexample.lean`.
- Coverage is recorded as `covered_partial` (not `covered_full`) in
  `progress/items.json`, with the scope correction noted there. Naturality/API
  packaging of the corrected theorem is separately tracked by #7397.

## Reopened former exclusions

These exercises were removed from the original skip list after substantial
formalization, but a later fidelity audit found a remaining source-level endpoint.
They are active work, not intentional omissions:

- Problem 2.16.3 — the dimension and non-finiteness results are proved, but the
  requested explicit basis of `g_4` remains #7394;
- Problem 4.12.8 — the finite-subgroup classification of `SO(3)` and much of the
  `SU(2)` double-cover analysis are proved, but the `-1 ∉ H` branch currently gives
  only `H ≃ h(H)` rather than the required cyclic conclusion. The exact `SU(2)`
  list therefore remains #7281;
- Problem 9.6.5 — an abstract quasi-inverse is proved, but the book's named balanced
  tensor/cokernel functor and its comparison maps remain to be constructed; see #6567.
