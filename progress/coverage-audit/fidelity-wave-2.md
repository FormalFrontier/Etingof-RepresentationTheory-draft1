# Stage 3.7 Fidelity Sweep — Wave 2 certificate (depth, Sonnet)

10→18 Sonnet subagents (model-diverse from wave-1's Opus), depth-enforced (read blob → locate decl → read full statement/definiens), per PLAN.md §3.2 steps 6–7. Codex used as cross-vendor calibration. Run under a quota pace-gate (pause if used>elapsed).

## Headline

- Re-audited **239** items (the wave-1 `verified`+`unsure`+unaudited set).
- **verified 179 / gap 53 / unsure 7**.
- Depth re-audit downgraded **40** items wave-1 had called verified — the wave-1 83% was optimistic, as warned.
- **15** wave-1 gaps now pass: the concurrent pod repaired them mid-sweep (5+ confirmed CLOSED). The find→file→fix→re-audit pipeline is self-correcting.

## The 53 gaps split into 4 kinds (different remedies)

- **Statement-fidelity (17)** — present statement vacuous/weaker/wrong. File repair issues.
- **Partial-example (19)** — multi-part Examples where only representative sub-items were formalized. **Policy call**: is representative-witness formalization acceptable for Examples, or must every sub-item be covered?
- **Coverage-missing (16)** — marked `sorry_free` but no declaration (mostly Remarks + a few real theorems). Coverage-arm work.
- **Structural-naming (1)** — content exists under a different name than the item.

## High-confidence NEW statement-fidelity gaps (file these)

- **Chapter2/Definition2.2.1** — `Etingof.AssociativeAlgebra` — Book Definition 2.2.1 defines a NON-UNITAL associative algebra: a vector space with bilinear multiplication satisfying associativity only. The Lean abbrev uses [Ring A] which requires a multiplicative unit (1 : A with one_mul and mul_one). The book explicitly defers the unit to Definition 2.2.2, making 2.2.1 genuinely non-unital. The Lean definition adds a strictly stronger constraint (existence of unit) not present in the book. The correct Mathlib type would be NonUnitalAlgebra k A or NonUnitalNonAssocAlgebra k A restricted to associative. This is a silent strengthening (added 'unital' adjective not in the book definition).
- **Chapter2/Definition2.2.2** — `EtingofRepresentationTheory.Chapter2.one_isUnit` — Book Definition 2.2.2 DEFINES the concept of 'unit in an associative algebra'. The Lean formalization is a theorem one_isUnit : [Ring A] → (a : A) → 1 * a = a ∧ a * 1 = a, which merely demonstrates that the already-existing ring element 1 satisfies the unit property. This is vacuous as a definition: the theorem is provably true for any Ring A and says nothing about whether a 'unit' concept is newly defined. The actual concept is baked into [Ring A]'s MulOneClass, which was already required in Definition2_2_1. The formalization records a proof of an axiom rather than a definition of a concept. Decision test: provable for any [Ring A] regardless of mathematical content — passes trivially. Should instead be a typeclass abbreviation or an 'abbrev Etingof.HasUnit A := One A' capturing the existential definition.
- **Chapter3/Definition3.4.1** — `Etingof.Filtration` — The definition is 'abbrev Etingof.Filtration A V := RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2}'. A RelSeries with this relation is a strictly ascending chain of submodules of any length, with NO constraint that the first term equals ⊥ (zero) or the last term equals ⊤ (all of V). The book's Definition 3.4.1 requires specifically 0 = V_0 ⊂ V_1 ⊂ ⋯ ⊂ V_n = V — a filtration OF V that starts at 0 and ends at V. The Lean type models 'a chain of submodules' not 'a filtration of V': any chain between arbitrary submodules qualifies. The dropped conjuncts are the boundary conditions head = ⊥ and last = ⊤.
- **Chapter3/Theorem3.10.2** — `Etingof.tensor_product_irreducible / Etingof.tensor_product_irreducible_classification` — Book Theorem 3.10.2(ii): any irreducible M of A⊗B has the form V⊗W for **unique** V and W. The Lean theorem tensor_product_irreducible_classification proves existence (∃ V W ...) but entirely drops the uniqueness claim. The conclusion is existential with no uniqueness quantifier (∃! or ∀ ... → isomorphic). Part (i) (tensor product of irreducibles is irreducible) is faithfully formalized in tensor_product_irreducible. Part (ii) drops the uniqueness conjunct.
- **Chapter4/Definition4.10.1** — `Etingof.FrobeniusDeterminant` — The book defines X_G as the matrix with entries a_{ij} = x_{g_i g_j} (product g_i * g_j, NOT g_i * g_j^{-1}). The Lean definition uses `Matrix.of fun (g h : G) => MvPolynomial.X (g * h⁻¹)`, i.e. entries x_{g * h^{-1}}. This is a different matrix from the book's x_{g * h}. The book's definition indexes variables by g_i g_j (forward product); the Lean definition by g_i g_j^{-1} (inverse). These are isomorphic as polynomials (by variable relabeling h ↦ h^{-1}) but the stated object does not match the book's stated definition. This is a misalignment in the defining formula, not just a style choice.
- **Chapter5/Corollary5.19.2** — `Etingof.Corollary5_19_2` — The statement is rich and correct (existential over Nat.Partition n with the right simplicity and distinctness constraints), but the proof body is a single 'sorry' delegated to Theorem5_18_4_partition_decomposition (in Theorem5_18_4.lean line 416: 'sorry'). The theorem itself is not proved. This is a sorry-blocked theorem, not a vacuous one, but per the audit criteria it is a gap.
- **Chapter5/Definition5.7.1** — `Etingof.VirtualRepresentation` — The 'coeffs' field has type 'FDRep ℂ G → ℤ', a function on ALL FDReps, not restricted to irreducible (simple) ones. The book defines a virtual representation as an 'integer linear combination of irreducible representations'. The structure is more permissive: any FDRep can appear in the support, including reducible ones. The 'character' computation then sums W.character g over arbitrary W in the support — for a non-simple W, this is NOT the decomposed character formula the book intends. The missing constraint is 'CategoryTheory.Simple W' on the support elements.
- **Chapter5/Proposition5.21.1** — `Etingof.Proposition5_21_1` — Book: ∏_m (x_1^m+⋯+x_N^m)^{i_m} = ∑_{λ: ℓ(λ)≤N} χ_λ(C_i) S_λ(x), where the sum ranges over ALL partitions of n with at most N parts. Lean's canonical declaration is: ∃ (lams : Finset (BoundedPartition N n)), psumPart = ∑ lam ∈ lams, charValue(lam) • schurPoly(lam.parts). This is strictly weaker: the existential does not specify that lams must be ALL bounded partitions of n with at most N parts. The full statement is in the non-canonical Proposition5_21_1_univ (summing over Finset.univ) but that declaration is named _univ, not Proposition5_21_1. The canonical declaration drops the 'which finset' conjunct.
- **Chapter5/Theorem5.10.1** — `Etingof.Theorem5_10_1` — Wrong adjunction direction. Book states Frobenius reciprocity as Hom_G(V, Ind_H^G W) ≅ Hom_H(Res V, W) (i.e., Res ⊣ CoInd direction, or equivalently: Ind is left adjoint gives Hom_G(Ind W, V) ≅ Hom_H(W, Res V)). The Lean declaration is `Nonempty ((Rep.ind H.subtype W ⟶ V) ≃ₗ[k] (W ⟶ (Rep.resFunctor H.subtype).obj V))`, i.e., Hom_G(Ind W, V) ≅ Hom_H(W, Res V). The book writes it as Hom_G(V, Ind W) ≅ Hom_H(Res V, W) — the Lean has the domain/codomain roles flipped relative to the book's stated form.
- **Chapter5/Theorem5.14.3** — `Theorem5_14_3` — Book states χ_{U_λ}(C_i) = coeff of x^λ in ∏ H_m(x)^{i_m} (complete homogeneous symmetric polynomials). Lean uses `cycleTypePsumProduct` = ∏ psum_m^{i_m} (power sum symmetric polynomials p_m = Σ xᵢᵐ). The file's own docstring says 'Previous version used hsymm (H_m), which is incorrect' — the developer believes the book's stated H_m is a typo and the proof uses p_m. Regardless, the Lean statement diverges from the book's written theorem.
- **Chapter5/Theorem5.15.1** — `Theorem5_15_1` — Book states χ_{V_λ}(C_i) = coeff of x^{λ+ρ} in Δ(x) · ∏ H_m(x)^{i_m}. Lean: `(sign(revPerm)) • spechtModuleCharacter n la σ = MvPolynomial.coeff (toFinsupp la + rhoShift n) (vandermondePoly n * cycleTypePsumProduct n σ)`. vandermondePoly is Δ(x) and cycleTypePsumProduct is ∏ psum_m^{i_m} — same psum-vs-H_m substitution as Theorem5.14.3. The factor sign(revPerm) is also not in the book statement.
- **Chapter5/Theorem5.6.1** — `Etingof.extTprod_isIrreducibleRep, Etingof.exists_extTprod_of_isIrreducibleRep` — Two gaps: (1) The book states the result 'over a field k (of any characteristic),' but the Lean formalization requires [IsAlgClosed k] for both the irreducibility direction (extTprod_isIrreducibleRep) and the exhaustion direction (exists_extTprod_of_isIrreducibleRep). Over an arbitrary non-algebraically-closed field, the result is false, so algebraic closure is mathematically necessary—but the book claims more generality than is formalized. (2) There is no single named declaration Etingof.Theorem5_6_1; the book's theorem is split into two unnamed-as-theorem lemmas without a wrapper that captures both parts simultaneously. The use of a local irreducibility predicate (IsIrreducibleRep) rather than Mathlib's Simple also introduces a layer of translation not present in the book.
- **Chapter7/Example7.6.3** — `Etingof.frobenius_reciprocity, Etingof.uea_adjunction` — The book lists 5 adjunction examples. The Lean formalizes 2: (2) `frobenius_reciprocity` proves `Rep.indFunctor k φ ⊣ Rep.resFunctor φ` (Ind ⊣ Res) — but the book says 'Res_K^G is left adjoint to Ind_K^G' (Res ⊣ Ind), which is the OPPOSITE direction. Mathlib's `indResAdjunction` gives Ind ⊣ Res (the standard Frobenius reciprocity direction: Hom_G(Ind M, N) ≅ Hom_K(M, Res N)), so Lean is mathematically correct, but it contradicts the book's stated direction. (3) `uea_adjunction` gives the hom-set bijection for UEA ✓. Missing entirely: (1) V⊗ ⊣ V*⊗ for group/Lie algebra reps; (4) GL₁ ⊣ k[G] (group algebra adjunction); (5) tensor algebra and symmetric algebra adjunctions.
- **Chapter7/Example7.9.5** — `Etingof.maschke_semisimple` — The book claims the category of representations of a finite group G over a field of characteristic not dividing |G| is semisimple (in the sense of Definition 7.9.4: every SES splits). The Lean proves `IsSemisimpleRing (MonoidAlgebra k G)` — that the group algebra k[G] is a semisimple ring. This is related but different from the categorical statement: it does not invoke or produce `Etingof.IsSemisimpleCategory (Rep k G)` (defined in Definition7.9.4.lean, not imported). The bridge 'IsSemisimpleRing R → Etingof.IsSemisimpleCategory (ModuleCat R)' is not formalized in the file. The book's claim is about the CATEGORY being semisimple (every SES splits), not about the group ring being a semisimple ring.
- **Chapter8/Definition8.1.8** — `Etingof.ProjectiveObject, Etingof.InjectiveObject` — The abbrevs alias CategoryTheory.Projective and CategoryTheory.Injective, which are defined via the lifting property (factoring through epimorphisms) over an arbitrary Category C. The book explicitly says 'projective object in an abelian category C such that Hom_C(P,?) is exact' — the definition is via exactness and the ambient category is required to be abelian. The Lean abbrevs: (1) use [Category C] not [Abelian C], so they apply to any category; (2) characterize via lifting property, not exactness. In abelian categories these are equivalent, but the abbrev is typed too weakly and uses a different (lifting) characterization than the book's (exactness).
- **Chapter8/Theorem8.1.5** — `Etingof.Theorem_8_1_5_i_iff_ii, Etingof.Theorem_8_1_5_Baer` — The book's Theorem 8.1.5 states three conditions (i)-(iii) are equivalent. The Lean file formalizes (i)↔(ii) and adds Baer's criterion. Condition (iii) — 'the functor Hom_A(?,I) is exact' — is mentioned in the module docstring but has no corresponding Lean theorem. Baer's criterion is not one of the book's three stated conditions. A dropped conjunct and a substituted non-book statement.
- **Chapter9/Definition9.3.1** — `Etingof.algebraCartanMatrix` — The book defines the Cartan matrix of A as the specific matrix with entries c_ij = [P_j : M_i] (Jordan-Holder multiplicity of M_i in P_j). The Lean definition takes any arbitrary function jhMultiplicity : Fin n -> Fin n -> ℕ and wraps it as Matrix.of jhMultiplicity. The definition is entirely unconstrained: it accepts ANY function, not necessarily the Jordan-Holder multiplicity function of any algebra. No algebra input, no simple/projective module data. The definition constructs nothing — it is effectively just a type alias for Matrix.of. Under the PLAN.md §3.2 step 6 decision test: this passes trivially for any input, meaning the real mathematical object (the Cartan matrix of a specific algebra A) is not constructed. The def body 'Matrix.of jhMultiplicity' is degenerate: the parameter name says jhMultiplicity but there is no constraint that this is actually a Jordan-Hölder multiplicity function.

## Needs Codex cross-vendor tiebreak (genuine disputes)

- **Chapter5/Theorem5.14.3 & Theorem5.15.1** — Lean uses power-sums where the book writes complete-homogeneous H_m; the file claims a book typo. Math dispute → third opinion.
- **Chapter5/Theorem5.10.1** — Frobenius reciprocity stated in the Ind⊣Res direction vs the book's written Hom(V,Ind W)≅Hom(Res V,W); equivalent forms, confirm acceptable.
- **Chapter8/Definition8.1.8** — `CategoryTheory.Projective` (lifting property) vs the book's Hom-exactness; equivalent in abelian categories, confirm.

## Concurrently-repaired (wave-1 gap → wave-2 verified)

- Chapter2/Definition2.14.1
- Chapter2/Definition2.14.2
- Chapter2/Example2.9.8
- Chapter2/Proposition2.7.1
- Chapter3/Corollary3.2.1
- Chapter3/Definition3.1.1
- Chapter3/Proposition3.1.4
- Chapter3/Proposition3.5.8
- Chapter3/Theorem3.3.1
- Chapter4/Example4.1.3
- Chapter4/Example4.3_FiniteAbelianGroups
- Chapter4/Theorem4.2.1
- Chapter5/Corollary5.12.4
- Chapter8/Example8.1.7
- Chapter9/Definition9.7.2

## Caveat
Wave 2 is depth but still single-judge per item (Sonnet) and strict about multi-part examples; treat `partial-example`/`structural` as needing a policy decision, not automatic bugs. Not a dry wave — a wave 3 should Codex-tiebreak the disputes and re-check repairs.


## Codex cross-vendor tiebreak — outcomes
- **5.14.3 / 5.15.1** (H_m vs power-sum): `lean-correct` — power sums are right; the book's H_m would be wrong (S₂ counterexample). Marked verified.
- **8.1.8** (projective object: lifting vs Hom-exactness): `faithful` — equivalent in abelian categories. Marked verified.
- **5.10.1** (Frobenius reciprocity direction): `gap` — Lean proves Ind⊣Res form, book states the other; bridge not formalized. Filed.

## Wave-2 issues filed
- Statement-fidelity: #5616–#5631 (+ pre-existing for 3.10.2, 5.21.1).
- Complete-the-example: #5632–#5648.
- Coverage (formalizable-missing): #5649–#5657.
- Marked `non_formalizable` (no issue): Remark2.9.14.
- Structural (content exists under another name, no issue): Definition5.4.1, Proposition5.21.2.
