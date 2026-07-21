# Statement-fidelity & non-vacuity audit — Problem 5.8.4 (transitivity of induction / induction in stages)

**Issue:** #7199
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 2bf9b8af)
**Scope:** report-only fidelity + non-vacuity audit of `Etingof.ind_ind_iso_ind`
(`EtingofRepresentationTheory/Chapter5/Problem5_8_4.lean`), with the abstract
core `Etingof.ind_stages_exists` and the supporting
`indStagesInnerRep` / `indStages_ker_eq` inspected as context.
**Verdict: FAITHFUL — the book's `Ind_H^G Ind_K^H V ≅ Ind_K^G V` is rendered as a
genuine `G`-equivariant linear isomorphism, non-vacuously, and all headline
declarations are axiom-clean. Nothing filed.**

## Book statement

`blobs/Chapter5/Problem5.8.4.md` (one line):

> **Problem 5.8.4.** Check that if `K ⊂ H ⊂ G` are groups and if `V` is a
> representation of `K`, then `Ind_H^G Ind_K^H V` is isomorphic to `Ind_K^G V`.

## Headline findings

1. **Genuine `G`-representation isomorphism, not merely a `ℂ`-linear iso.**
   `ind_ind_iso_ind` produces `∃ e : IndV H.subtype (Ind_{K.subgroupOf H} ρ) ≃ₗ[ℂ]
   IndV K.subtype ρ` **together with** the intertwining clause
   `∀ g x, e (Definition5_8_1 H (…) g x) = Definition5_8_1 K ρ g (e x)`.
   `e` is a bona-fide `LinearEquiv` (built via `LinearEquiv.ofLinear (IndStages.fwd)
   (IndStages.inv)` with **both** round-trips `fwd_comp_inv` and `inv_comp_fwd`
   proven `= LinearMap.id`), and the intertwining clause is the honest
   `G`-equivariance condition `e ∘ (g •) = (g •) ∘ e`. Bijective linear + equivariant
   = isomorphism of `G`-representations. This is the book's `≅`, not a weaker
   underlying-space iso.

2. **The two `G`-actions being intertwined are the real induced-representation
   actions.** `Etingof.Definition5_8_1 H ρ` is *defined* as `Representation.ind
   H.subtype ρ` (`Definition5_8_1.lean:36–42`), and `Representation.ind` /
   `Representation.IndV` are the genuine Mathlib induction functor and its carrier
   (`ind φ ρ : Representation ℂ (target φ) (IndV φ ρ)`, the `H`-coinvariants of
   `ℂ[G] ⊗ V` with `G` acting on the `ℂ[G]` factor). So both sides carry the
   project's canonical `Ind` action, and `e` intertwines them.

3. **Correct subgroups; the inner `Ind_K^H` is faithfully rendered.**
   - Outer induction: `Definition5_8_1 H (…) = ind H.subtype (…)`, i.e. `Ind_H^G`.
   - Inner induction: `Definition5_8_1 (K.subgroupOf H) (indStagesInnerRep H K hKH ρ)
     = ind (K.subgroupOf H).subtype (…)`, i.e. `Ind` from the copy of `K` inside `H`
     (`K.subgroupOf H`) up to `H` — exactly `Ind_K^H`. The `K`-representation `V` is
     transported to `K.subgroupOf H` along the canonical `K.subgroupOf H ≃* K`
     (`indStagesInnerRep = ρ.comp (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom`),
     which is the mathematically correct relabelling, not a mismatched subgroup.
   - Direct induction (RHS): `Definition5_8_1 K ρ = ind K.subtype ρ`, i.e. `Ind_K^G`.
   - The abstract stages lemma is applied with `φ = (K.subgroupOf H).subtype`,
     `ψ = H.subtype`, giving `Ind_{ψ∘φ}` with `ψ∘φ = H.subtype ∘ (K.subgroupOf H).subtype`.
     The relabelling `indStages_ker_eq` closes the gap to `Ind_K^G` via hypotheses
     `hfφ : ψ∘φ = K.subtype ∘ σ` and `hτ : (ρ transported) = ρ.comp σ`, **both discharged
     by `rfl`** — so the composite inclusion of `K.subgroupOf H` into `G` is
     *definitionally* the inclusion of `K` into `G` reindexed by the bijection
     `σ = subgroupOfEquivOfLe hKH`. This is precisely `K ↪ H ↪ G = K ↪ G`.

4. **Hypotheses faithfully render `K ⊂ H ⊂ G`, with no hidden narrowing.**
   `H K : Subgroup G` and `hKH : K ≤ H` render the chain `K ⊂ H ⊂ G` (subgroups of a
   common ambient group with `K ≤ H`). `ρ : Representation ℂ K V` renders "`V` a
   representation of `K`." The statement is fully general: `[Group G]` (no finiteness),
   `V` any `ℂ`-module (`[AddCommGroup V] [Module ℂ V]`). No `[Fintype]`,
   `[DecidableEq]`, or extra structural hypothesis silently weakens the claim; the
   `classical` in the proof is proof-side only and does not appear in the statement.

5. **Ground-field / model nuance (documented, not a gap).** The project's canonical
   `Ind` (`Definition5_8_1`) is Mathlib's tensor model `Representation.ind` (the left
   adjoint of restriction). Etingof's Definition 5.8.1 is stated in the function-space
   / coinduced model, which coincides with the tensor model only for finite groups
   (documented in `Definition5_8_1.lean:20–23`). This item uses `Ind` *consistently on
   both sides*, and transitivity of induction ("in stages") holds for the tensor model
   in **full generality** — so `ind_ind_iso_ind` is, if anything, a *stronger* (finiteness-
   free) theorem than the book's finite-group setting requires, and is faithful to the
   book's claim about the project's `Ind`. The choice of model is a `Definition5_8_1`
   concern, already documented there and out of scope for this item.

6. **All four inspected declarations are axiom-clean** — `#print axioms` on
   `ind_ind_iso_ind`, `ind_stages_exists`, `indStagesInnerRep`, and `indStages_ker_eq`
   each report exactly `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.

## Non-vacuity

- **Setup is inhabited by a concrete witness.** Instantiating `G = Equiv.Perm (Fin 3)`
  (`S₃`), `H = ⊤`, `K = ⊥`, `hKH = bot_le`, `ρ = Representation.trivial ℂ _ ℂ`
  typechecks and produces the existential's `e` (verified: the example
  `⟨(ind_ind_iso_ind ⊤ ⊥ bot_le (trivial …)).choose, trivial⟩` elaborates). The
  hypothesis chain `K ≤ H ≤ G` with a genuine `K`-representation is trivially
  satisfiable, so the theorem is not vacuously true.
- **`e` is a genuine bijection, not a degenerate map.** The forward map `IndStages.fwd`
  explicitly sends `⟦aG ⊗ ⟦aH ⊗ v⟧⟧ ↦ ⟦ψ_*(aH)·aG ⊗ v⟧` (concrete, non-constant),
  with inverse `⟦aG ⊗ v⟧ ↦ ⟦aG ⊗ ⟦1 ⊗ v⟧⟧`; both `fwd ∘ inv = id` and `inv ∘ fwd = id`
  are proven. The carriers `IndV …` are the honest coinvariant modules (e.g. dimension
  `[G:K]·dim V` for `V = ℂ` and `G` finite), so this is a real isomorphism of
  possibly-nonzero representations, not a vacuous equivalence of zero spaces.

## Verification performed

- `lake build EtingofRepresentationTheory.Chapter5.Problem5_8_4` → `Build completed
  successfully (8581 jobs)`.
- `#print axioms Etingof.ind_ind_iso_ind` → `[propext, Classical.choice, Quot.sound]`
  (likewise `ind_stages_exists`, `indStagesInnerRep`, `indStages_ker_eq`). No `sorryAx`.
- Concrete non-vacuity instantiation (`S₃`, `K = ⊥ ≤ H = ⊤`, trivial rep) elaborates.
- Confirmed `Representation.ind` / `Representation.IndV` / `Representation.ind_apply` /
  `Subgroup.subgroupOfEquivOfLe` are genuine Mathlib declarations, and
  `Definition5_8_1 = Representation.ind ·.subtype`.

## Verdict

**FAITHFUL.** The book's transitivity-of-induction claim
`Ind_H^G Ind_K^H V ≅ Ind_K^G V` is rendered as a genuine, `G`-equivariant,
non-vacuous linear isomorphism using the project's canonical `Ind`, over the correct
subgroup chain `K ≤ H ≤ G`, with no hidden weakening, and every headline declaration is
axiom-clean. `progress/items.json` `Chapter5/Problem5.8.4` `fidelity` set to `verified`.
No follow-up issue filed.
