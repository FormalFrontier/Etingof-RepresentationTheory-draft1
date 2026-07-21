# Statement-Fidelity & Non-Vacuity Audit: Theorem 4.10.2 (Frobenius determinant factorization)

**Issue:** #7171
**File:** `EtingofRepresentationTheory/Chapter4/Theorem4_10_2.lean` (1078 lines, sorry-free)
**Supporting:** `EtingofRepresentationTheory/Chapter4/Definition4_10_1.lean`,
`EtingofRepresentationTheory/Infrastructure/IrreducibleEnumeration.lean`
**Date:** 2026-07-21
**Verdict: PASS — FAITHFUL, non-vacuous, axiom-clean. No defect. Report-only; no Lean changes.**

---

## Book statement (`blobs/Chapter4/Theorem4.10.2.md`)

> **Theorem 4.10.2.** det X_G = ∏_{j=1}^{r} P_j(**x**)^{deg P_j} for some pairwise
> nonproportional irreducible polynomials P_j(**x**), where r is the number of conjugacy
> classes of G.

Definition 4.10.1: X_G is the matrix with entries a_{ij} = x_{g_i g_j}; det X_G is the
Frobenius (group) determinant, a degree-n polynomial in x_{g_1}, …, x_{g_n}.

Proof (`Discussion_proof_Theorem4.10.2.md`): via the regular representation and Maschke,
det_V L(**x**) = ∏_i (det_{V_i} L(**x**))^{dim V_i}; set P_i = det_{V_i} L; each P_i is
irreducible (Lemma 4.10.3) and the P_i depend on disjoint variable collections y_{i,jk}, so
are non-proportional. The operator matrix of L(**x**) = ∑_g x_g ρ(g) is X_G with columns
permuted, so its determinant equals det X_G up to sign.

## Lean headline (`Theorem4_10_2.lean:979`)

```lean
theorem Etingof.Theorem4_10_2
    (k G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]
    [Invertible (Fintype.card G : k)] :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial G k),
      (∀ j, Irreducible (P j)) ∧
      (∀ i j, i ≠ j → ¬Associated (P i) (P j)) ∧
      Etingof.FrobeniusDeterminant k G = ∏ j : Fin r, P j ^ (P j).totalDegree ∧
      r = Fintype.card (ConjClasses G)
```

---

## 1. Statement fidelity — FAITHFUL

| Book element | Lean encoding | Assessment |
|---|---|---|
| `det X_G` | `Etingof.FrobeniusDeterminant k G` | **Faithful.** `Definition4_10_1.lean` defines it as `Matrix.det (Matrix.of fun g h => X (g * h))` — literally the determinant of the matrix with entries `x_{g·h}`, matching `a_{ij} = x_{g_i g_j}` exactly (forward product). Real construction. |
| `∏_{j=1}^r` | `∏ j : Fin r` | Faithful. `r` a genuine `ℕ` witness. |
| `P_j^{deg P_j}` | `P j ^ (P j).totalDegree` | **Faithful.** Exponent is the factor's own total degree. `blockPoly_totalDegree` (line 487) proves `(blockPoly i).totalDegree = D.d i = dim V_i`, matching the book's `deg P_j = dim V_j`. Self-referential form `P^{deg P}` transcribes "P_j raised to deg P_j" verbatim. |
| "irreducible" | `∀ j, Irreducible (P j)` | Faithful. `blockPoly_irreducible` (line 608) via generic-determinant irreducibility `genDet_irreducible` (Lemma 4.10.3 analogue). |
| "pairwise nonproportional" | `∀ i j, i≠j → ¬Associated (P i) (P j)` | **Faithful.** Over a field, `Associated p q` ⟺ p = u·q for a unit u ⟺ p, q differ by a nonzero scalar constant (units of `MvPolynomial G k` are the nonzero constants). So `¬Associated` is exactly "not proportional." |
| "r = number of conjugacy classes" | `r = Fintype.card (ConjClasses G)` | Faithful. `n_eq_card_conjClasses` (line 827): dim Z(k[G]) = |ConjClasses G| and dim Z(∏ Mat) = n, preserved by the Wedderburn iso. |
| Field ℂ | general `[Field k] [IsAlgClosed k] [Invertible (card G : k)]` | **Faithful generalization, harmless.** Alg-closedness gives the matrix-block Wedderburn decomposition + irreducible factorization; `Invertible (card G : k)` is Maschke's char ∤ \|G\| hypothesis. ℂ satisfies both. Strictly more general, no weakening. |

### Fidelity nuance: the sign (rigorous, not a defect)

The book writes `det X_G = ∏ P_j^{deg P_j}` with no sign, after noting the operator matrix
of `L(x)` (entries `x_{g·h⁻¹}`) is `X_G` (entries `x_{g·h}`) "with permuted columns … hence
has the same determinant up to sign." The Lean development is more rigorous:

- `FrobeniusDeterminant` is literally `det X_G` (forward entries `x_{g·h}`), per Def 4.10.1.
- `frobeniusDet_eq_signSmul_prod` (line 162) proves `FrobeniusDeterminant = sign(inv) • ∏ blockPoly_i^{d_i}`, tracking the inversion-permutation sign `s = sign(g ↦ g⁻¹)` explicitly.
- The headline absorbs `s` into **one** rescaled factor: using alg-closedness it picks `c` with `c^{d_{j₀}} = s` (`IsAlgClosed.exists_pow_nat_eq`, line 1012) and sets `P j₀ = C c * blockPoly j₀`. Then `P j₀^{d_{j₀}} = C s · blockPoly j₀^{d_{j₀}}`, cancelling the sign, so the clean equation `FrobeniusDeterminant = ∏ P_j^{deg P_j}` holds exactly as the book states.

`P j₀` remains irreducible (nonzero-scalar multiple of an irreducible), non-associated to the
other factors (associated to `blockPoly j₀`, which is non-associated to the rest), and of the
same total degree. The book only asserts existence of *some* such family, and the Lean `∃`
supplies exactly such a witness — so this is a faithful, indeed more careful, transcription.

## 2. Non-vacuity — GENUINE

- The conclusion is a real `∃ r P, (irreducible) ∧ (pairwise non-associated) ∧ (equation) ∧ (r = #classes)`. No `True`, no trivial placeholder.
- **`FrobeniusDeterminant` is a real object**: `det` of the generic group matrix (entries `X (g*h)`), a genuine degree-\|G\| multivariate polynomial — not `0`, not stubbed. A zero/constant here would have made the factorization vacuous; it is neither.
- **`blockPoly` is a real construction** (`Theorem4_10_2.lean:35`): `det (of fun a b => ∑ g, C (projRingHom i (of g) a b) * X g)` — the determinant of the generic per-block matrix `∑_g x_g ρ_i(g)`. `projRingHom` (infra line 161) is the honest projection through the Wedderburn iso `D.iso`; `IrrepDecomp.mk'` (infra line 70) builds `D` from `MonoidAlgebra.wedderburnArtin` (a genuine algebra iso `k[G] ≃ₐ Π Mat(d_i, k)`), not a stub. Infra file is sorry-free.
- The existential is *pinned*, not vacuously satisfiable: the P must be irreducible, pairwise non-associated, and their exponentiated product must equal a fixed nonzero polynomial, with `r = card (ConjClasses G)`.
- **`[IsAlgClosed k]` is load-bearing**: used in `blockPoly_irreducible` (generic-determinant irreducibility over the field), in the sign root `IsAlgClosed.exists_pow_nat_eq`, and in the matrix-block Wedderburn structure underlying `mk'`. Removing it breaks the factorization. Genuinely used.

## 3. Axiom cleanliness — CLEAN

```
'Etingof.Theorem4_10_2'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.FrobeniusDeterminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'IrrepDecomp.blockPoly'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no stray axiom. `grep -c sorry` on both the theorem file and the infra file
returns 0. `lake build EtingofRepresentationTheory.Chapter4.Theorem4_10_2` succeeds (style
linter warnings only: three `longLine`/`show` lints, cosmetic).

---

## Conclusion

**PASS.** `Etingof.Theorem4_10_2` faithfully transcribes Etingof Theorem 4.10.2:
`FrobeniusDeterminant` = `det X_G` per Definition 4.10.1; the factorization uses `totalDegree`
= `deg P_j` = `dim V_j` as exponent; `Irreducible` + `¬Associated` faithfully captures
"pairwise nonproportional irreducible"; and `r = card (ConjClasses G)` matches the number of
conjugacy classes. The generalization to an algebraically closed field with `Invertible
(card G : k)` (Maschke) is faithful and harmless. The conclusion is a genuine
existence-with-properties over real, non-stubbed data (`FrobeniusDeterminant`, `blockPoly`,
the Wedderburn `IrrepDecomp`), `[IsAlgClosed k]` is genuinely used, and all three declarations
are axiom-clean. The explicit sign-tracking and single-factor sign absorption are a more
rigorous rendering of the book's "up to sign" remark, not a defect.

No follow-up `feature` issue warranted. Cosmetic style-linter cleanups (lines 918, 934, 966)
are optional and out of scope for this report-only audit.
