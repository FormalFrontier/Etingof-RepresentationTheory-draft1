# Route: `schurModule_isSimple_general` (general-`k` Schur-module simplicity, #4946)

## Summary

Issue #4946 asks to lift `schurModule_isSimple` (Schur-module simplicity, currently
proved only for `k = ℂ` in `SchurModuleSimple.lean:314`) to a general algebraically
closed characteristic-zero field `k`. After investigation this is **not a single
ingredient**: it requires generalizing essentially the entire ℂ-based symmetric-group /
Specht-module / Schur-Weyl simple-module foundation of Chapter 5 from ℂ to general `k`.
The parent was decomposed into the layered sub-issue chain below.

## Why it is large

`schurModule_isSimple` (ℂ) reduces to two halves:

- **GL transfer** `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
  (`SchurWeylGLTransfer.lean`) — **already generic over `k` with `[IsAlgClosed k]`**. ✓
- **Centralizer-simplicity core** `schurModuleSubmodule_isSimple_centralizer`
  (`SchurModuleSimple.lean:254`) — ℂ-hardcoded. It uses:
  - `Theorem5_18_4_centralizers` (double centralizer) — **already generic over `k`,
    `[CharZero k]`**. ✓
  - `schurBlock_imageSubmoduleB_isSimple` (`SchurModuleSimple.lean:167`, ℂ) — the special-
    block analysis, which pulls in:
    - `exists_unique_special_block` (`SchurModuleSpecialBlock.lean:148`, ℂ)
    - `youngSym_action_vanishes_off_block`,
      `youngSym_action_on_special_block_rank_one_scaled_proj` (`Theorem5_22_1.lean`, ℂ)
    - `trace_symGroupAction_eq_spechtModuleCharacter`,
      `simpleSubmodule_iso_of_spechtCharacter_eq` (`Theorem5_22_1.lean`, ℂ) — the Specht
      character bridge, which rests on
    - `Theorem5_12_2_classification` (`Theorem5_12_2_Classification.lean`, ℂ): every simple
      `ℂ[S_n]`-module is a Specht module, and
    - `SpechtModule`, `SymGroupAlgebra := MonoidAlgebra ℂ (Equiv.Perm (Fin n))`
      (`Theorem5_12_2_Irreducible.lean:22,26`) — **the ℂ root**.

`SymGroupAlgebra`/`SpechtModule` over ℂ are referenced by ~20 files (the whole §5.12–5.17
tabloid/polytabloid/Specht/hook-formula development). There is **no genuinely ℂ-specific
fact** anywhere in the chain (the `conj`/`trace_conj'` occurrences are linear-algebra
conjugation, not complex conjugation); ℂ is used purely as "an algebraically closed field
of characteristic zero." So the work is a careful but mechanical ℂ→`k` generalization.

## The crucial shortcut: build on the existing generic track

The project **already has a generic-`k` Specht/Young infrastructure**, so the general-`k`
path should extend it rather than ℂ→`k`-editing the §5.12–5.17 ℂ files:

- `SpechtModuleK (k) [CommRing k] n la` — `Infrastructure/SpechtModuleSimple.lean:28`
- `YoungSymmetrizerK (k) [CommRing k] n la` — `Theorem5_22_1.lean:50`
- `YoungSymmetrizerK_sq_scalar (k) [CommRing k] [CharZero k]` — `Theorem5_22_1.lean:165`
- `SpechtModuleK_isSimpleModule` — `Infrastructure/SpechtModuleSimple.lean:172`, **proved
  over ℚ, sorry-free**. Its proof only needs `k[S_n]` semisimple + the sandwich property,
  both of which hold for any characteristic-zero field; extending ℚ → general char-0 `k`
  should be light.

## Recommended layered chain (sub-issues)

1. **Sub-A (root):** general-`k` `SpechtModuleK_isSimpleModule` (extend the ℚ proof to any
   char-0 field) and a general-`k` simple-module classification
   (`Theorem5_12_2_classification` over `k`: every simple `k[S_n]`-module ≅ `SpechtModuleK k n la`).
2. **Sub-B:** general-`k` Specht character bridge —
   `trace_symGroupAction_eq_spechtModuleCharacter`,
   `simpleSubmodule_iso_of_spechtCharacter_eq` over `k`. (`spechtModuleCharacter` is
   field-independent, integer-valued.) Depends on Sub-A.
3. **Sub-C:** general-`k` special-block analysis — `youngSym_action_vanishes_off_block`,
   `youngSym_action_on_special_block_rank_one_scaled_proj` (`Theorem5_22_1.lean`),
   `exists_unique_special_block` + helpers (`SchurModuleSpecialBlock.lean`). Depends on Sub-B.
4. **Sub-D (residual #4946):** general-`k` `schurBlock_imageSubmoduleB_isSimple` →
   `schurModuleSubmodule_isSimple_centralizer` → **`schurModule_isSimple_general`**
   (`SchurModuleSimple.lean`). Depends on Sub-C.

## The `hN` question (carry into Sub-D)

The ℂ result `schurModule_isSimple` carries `hN : (∑ i, lam i) ≤ N`, but the assembly
statement `schurModule_isSimple_general` (and its consumer
`simpleRep_iso_schurModule_of_formalCharacter_eq`, #4901) omits it. Sub-D must determine
whether `hN` is genuinely required for the general-`k` simplicity argument; if it is, this
forces a statement change to the #4901 assembly and must be coordinated there.

## Pointers

- Target sorry: `schurModule_isSimple_general`, `SchurWeylFormalCharacterIso.lean:131`.
- ℂ proof to lift: `schurModule_isSimple`, `SchurModuleSimple.lean:314`.
- Consumer: `simpleRep_iso_schurModule_of_formalCharacter_eq` (#4901).
