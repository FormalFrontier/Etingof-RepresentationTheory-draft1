# Intentional omissions and exercise scope

This document records omissions that are deliberate decisions about the scope of the
project. An item belongs here only when the project has decided not to formalize it,
not merely because it is difficult, unfinished, or outside the scope of one issue or
pull request.

An intentional omission is not a missing proof. The corresponding Lean file should
describe what is and is not formalized, link to this document, and contain no
`sorry`, `admit`, axiom, or proof-placeholder declaration for the omitted material.
Progress metadata should record partial coverage and the scope decision explicitly.

## Book-stated external results intentionally left as `proof_wanted`

This section is a narrow exception to the omission policy above. A
`proof_wanted` records and typechecks a proposition but creates no proof term,
`sorryAx`, or project axiom. Such a marker is non-blocking only when it is
individually enumerated here and has matching `scope_approved_proof_wanted`
metadata in `progress/items.json`. Adding another exception requires a new entry
in both places and explicit review; unapproved `proof_wanted` markers remain
blocking proof gaps. `scripts/check_proof_placeholders.py` enforces that
correspondence.

### Remark 2.9.3 — Ado–Iwasawa theorem

The book states Ado's theorem—that every finite-dimensional Lie algebra has a
faithful finite-dimensional representation—but supplies no proof. Because the
chapter works over an arbitrary field, the faithful Lean statement
`Etingof.ado` records the arbitrary-characteristic Ado–Iwasawa theorem, not only
the characteristic-zero case.

The project intentionally does not undertake the Ado–Iwasawa proof. Its
arbitrary-characteristic proof requires substantial Lie-theoretic machinery
beyond the representation-theory development selected for this book, including
the characteristic-dependent construction of a finite-dimensional quotient of
the universal enveloping algebra that remains faithful on the Lie algebra.
Building that theory solely to prove a result the book invokes without proof is
outside this formalization's boundary.

Accordingly, the sole `proof_wanted ado` in
`EtingofRepresentationTheory/Chapter2/Remark2_9_3.lean`, tracked by
`Chapter2/Remark2.9.3`, is an approved non-blocking marker. The file still proves
the useful constructive reductions between a faithful finite-dimensional
representation and a finite-dimensional enveloping-algebra target. Its
`proof_wanted` records that the theorem itself has no project proof; it is not
active mathematical work and does not prevent completion.

## Current intentional omissions

### Theorem 2.1.2 — arbitrary-field Gabriel classification

The book notes in a footnote that Gabriel's finite-type classification remains
valid over an arbitrary field, but explicitly proves only the algebraically
closed case. The formalization follows that supplied proof scope. Its general
quiver theorem removes restrictions on loops, parallel arrows, and orientation,
but still assumes that the coefficient field is algebraically closed; it does
not claim the stronger arbitrary-field classification. See
`EtingofRepresentationTheory/Chapter2/Theorem2_1_2_General.lean`.

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
algebraic on restriction, constructs an algebraic `GL_N` extension of every
intrinsically algebraic simple `SL_N` representation, and concludes that every such
representation is one of the `L_λ|_{SL_N}`.

### Problem 6.1.6 — residual McKay-correspondence classification

The project has formalized the tautological representation, symmetry and
connectivity of the McKay graph, the affine-Cartan positivity argument for graphs
with at least three vertices, and the kernel equation for the dimension vector.
Problem 4.12.8 supplies the complete `SO(3)` and `SU(2)` finite-subgroup
classifications together with the double-cover infrastructure. The project
nevertheless retains its original decision not to build the additional concrete
group-family-to-diagram identifications. Thus the part (d) decision below is a
deliberate scope boundary, not a temporary dependency on Problem 4.12.8.
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

### Problem 6.9.1(d) — Kronecker-quiver classification

Part (d) asks for the preceding cyclic-`Q₂` classification to be generalized to
the Kronecker quiver.  This is a genuine formalizable classification problem,
not an informal prompt: a faithful solution would introduce representations by
two parallel maps, construct the preprojective, preinjective, and regular
matrix-pencil families, and prove existence and uniqueness of those normal
forms.  The project deliberately does not add that separate matrix-pencil
classification, which is not used by any later result in the book.

Parts (a)--(c), including isomorphism-level exhaustiveness and uniqueness for
the four cyclic-`Q₂` families, are fully formalized in
`EtingofRepresentationTheory/Chapter6/Problem6_9_1.lean` and
`EtingofRepresentationTheory/Chapter6/Problem6_9_1_Classification.lean`.
Part (e) remains recorded in the claim ledger as an open-ended prompt: unlike
part (d), it asks whether one can generalize to all longer cyclic quivers and
arbitrary orientations without specifying a single classification theorem.

## Proof-route details intentionally not separately packaged

The items in this section have their full mathematical endpoints formalized, so
their ledger coverage remains `covered_full`. What is omitted is only a second
presentation, intermediate construction, or basis-dependent calculation from
the source proof. Unlike the scope omissions above, these entries do not mark a
missing theorem and do not require a scope note in the corresponding Lean file.

### Proposition 4.1.2 — the source's Hom-space proof route

The proposition itself—failure of semisimplicity when the characteristic divides
the group order—is fully formalized. The proof uses the group sum and an
idempotent-generator argument for ideals. The source instead packages the
invariant inclusion and augmentation as the one-dimensional Hom spaces
`Hom_{k[G]}(k,k[G]) = kΛ` and `Hom_{k[G]}(k[G],k) = kε`, normalizes their
composite to `|G|`, and derives a no-left-inverse contradiction. Those four
proof-route statements are intentionally not duplicated as a second proof. See
`EtingofRepresentationTheory/Chapter4/Proposition4_1_2.lean`.

### Example 4.1.3 — the scalar-root proof route

The formalization proves the stated endpoint that every irreducible
representation of `ℤ/pℤ` in characteristic `p` is trivial. It directly combines
nilpotence of `ρ(g) - 1` with Schur's lemma. The source's intermediate route—first
showing the representation is one-dimensional and then proving that every
`p`-th root of unity in characteristic `p` is `1`—is intentionally not separately
packaged. See `EtingofRepresentationTheory/Chapter4/Example4_1_3.lean`.

### Theorem 4.2.1 — the commutator-quotient dual proof route

The spanning and linear-independence statements saying that irreducible
characters form a basis of the class functions are fully formalized. The proof
uses the center of the group algebra, Wedderburn decomposition, and character
orthogonality. The source's separate identification of
`(k[G]/[k[G],k[G]])*` with the class functions is an unused proof-route artifact
and is intentionally not rebuilt. See
`EtingofRepresentationTheory/Chapter4/Theorem4_2_1.lean`.

### Example 4.3 for S₃ — basis-dependent geometric matrices

The trivial, sign, and standard representations are constructed, proved simple,
and shown to have dimensions `1, 1, 2`; the standard representation is realized
canonically as the sum-zero subrepresentation of the permutation representation.
The source's displayed matrices for a transposition and a 3-cycle depend on a
chosen geometric eigenbasis. They are intentionally not added as a second,
basis-dependent model of the same representation. See
`EtingofRepresentationTheory/Chapter4/Example4_3_S3.lean`.

### Discussion — completion of the proof of Theorem 5.4.6

The formalization proves the discussion's required endpoint by contradiction
from simplicity. It intentionally does not separately construct the book's
particular subgroup generated by the elements `ab⁻¹` for `a,b` in a conjugacy
class and prove that this witness is proper, nontrivial, and normal. This subgroup
is specific to the source's proof route and is not used later. See
`EtingofRepresentationTheory/Chapter5/Theorem5_4_6.lean`.

## Completed former exclusions

The following exercises appeared in the original hard-problem/skip list but were
subsequently formalized. The former scope decision is therefore superseded:

- Problem 4.12.8 — the complete finite-subgroup classifications of `SO(3)` and
  `SU(2)`, including the cyclic `-1 ∉ H` branch;
- Problem 5.24.2 — invariants of matrix tuples;
- Problem 6.1.3 — finite and affine Dynkin diagrams;
- Problem 9.6.5 — the explicit balanced-tensor functor, its comparison maps,
  and the resulting quasi-inverse equivalence;
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
