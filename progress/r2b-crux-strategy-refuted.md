# Wall 3 R2.b sub-A (#4604): stated crux strategy is computationally REFUTED

Feature session (UUID c8db6773). Outcome: **the deliverable lemma is true, but
the proof strategy the issue prescribes (column-antisymmetry on `f_w` via the
`Q ∩ w⁻¹Pw` stabiliser) is refuted by computation.** No Lean landed; issue
routed back to replan with a corrected analysis. The mandated pre-formalization
validation (issue: "extend `r2b_crux.py` ... confirm the coset-sum-cancellation
mechanism") is what exposed the flaw.

Scripts (saved this session):
* `progress/r2b-crux-ext-validation.py` — the f_w/coset/non-col-std checks.
* `progress/r2b-crux-mechanism-probe.py` — max(f_w) vs max(Δ) vs [σ].
* (probe `max ∈ {[τ_q]}` reproduced inline below.)

## The flaw in the prescribed strategy

The issue says:

> `f_w(σ)([β]) = Σ_{q : [w q⁻¹ σ] = [β]} sign(q)`. The `q` giving a fixed `[β]`
> form a coset of `Q ∩ w⁻¹ P w`. If that stabiliser contains an odd-sign
> element the coset sum cancels to 0, so any `[β] ∈ supp(f_w(σ))` has a
> column-standard representative.

`H := Q ∩ w⁻¹ P w` is a **single global subgroup**, and the fibers
`{q : [w q⁻¹ σ] = [β]}` are its cosets `q₀·H` (all the same size, same `H`).
So "H contains an odd-sign element" is **not a per-`β` condition** — it is
global and all-or-nothing:

* `H ⊆ Aₙ` (all even)  ⟹  no fiber cancels  ⟹  `supp(f_w) = { [w q⁻¹ σ] : q∈Q }`
  in full, **including non-column-standardizable tabloids**;
* `H ⊄ Aₙ`            ⟹  *every* fiber sum vanishes  ⟹  `f_w ≡ 0`.

Either way the mechanism cannot single out individual non-col-std tabloids, so
it does **not** prove "`[β] ∈ supp(f_w) ⟹ [β] col-std-izable". And that
implication is **false**: `r2b-crux-ext-validation.py` exhibits 56
non-column-standardizable tabloids in `supp(f_w)` on shape (3,3) (search
`FW-VIOLATION`). The earlier S_n-invariance and explicit-`q∉R`-formula dead ends
(see `r2b-crux-is-column-antisymmetry.md`) were correctly ruled out; this third,
*prescribed* route is a fourth dead end.

## What IS true (validated)

1. **The deliverable holds.** Over 4 shapes the dominance-maximal tabloid of `Δ`
   is always column-standardizable: `non-colstd-in-Delta=167  of which MAXIMAL=0`
   (`r2b-crux-ext-validation.py`). Consistent with the original `stuck=0` over
   160 examples.

2. **The genuine clean fact is one level up:** the dominance-**maximal** tabloid
   of `f_w` is column-standardizable (0 violations across all shapes;
   `r2b-crux-mechanism-probe.py`, `max(f_w) NOT col-std-izable: 0`). The
   non-col-std tabloids of `f_w` are all strictly below its maximal tabloid(s).
   This is the standard James "leading tabloid is column-standard" phenomenon,
   but for the *twisted* polytabloid.

3. **No cheap bridge from f_w-max to Δ-max.** `max(Δ) = max(f_w)` only
   ~30–40% of the time, and `max(Δ) = [σ]` only ~65–75% of the time
   (`r2b-crux-mechanism-probe.py`). Even "`max(Δ)` is some `[τ_q]`" fails
   (124/133, 75/82, 83/87, 45/52 — NOT 100%). So the maximal-support
   col-std-izability of `Δ` is **not** reducible to membership in the
   col-std set `{[τ_q]}` nor to any single coset-cancellation.

## Corrected mechanism (for the planner)

The real reason is the **classical James column-straightening / dominance
induction**, not a one-shot coset cancellation. Concretely, the property
"the dominance-maximal support tabloid is column-standardizable" is preserved
by the whole elimination because:

* it is a structural invariant of `f_w − (any V-element with support ≼ [σ])`,
  i.e. of `Δ_k = f_w − M_k` where `M_k ∈ V` is the accumulated peeled part
  (`M_0 = twistedIHPart`; each peel adds `c·ψ_{β'}` with `β'` col-std,
  `[β'] ≼ [σ]`), and
* each polytabloid `ψ_τ` (τ col-std) has *column-standard leading tabloid* `[τ]`
  with everything else strictly below it (`generalizedPolytabloidTab_coeff_dominance`
  + `..._coeff_self` already give this).

The honest statement that sub-B actually consumes (iterated, not just `Δ_0`) is:

> For col-std σ, arbitrary w, and **any** `M ∈ V` (SYT-polytabloid span) with
> `supp(f_w σ − M) ≼ [σ]`, every dominance-maximal tabloid of `X := f_w σ − M`
> is column-standardizable, with a representative `β'` that is IH-available
> (`[β'] ≼ [σ]`).

This subsumes the issue's `Δ_0`-only statement and is what the leading-term
elimination in sub-B needs at every step. Proving it is a genuine
column-straightening theorem on the twisted polytabloid — **substantially
larger than the single conjugate-coset lemma the issue scoped**, and the
`Q ∩ w⁻¹Pw` machinery the issue suggested building is *not* the right tool.

## Recommendation

Re-scope #4604 (and re-examine #4605/#4593). Options for the planner:

* **(a)** Split the corrected lemma into: (a1) "max tabloid of `f_w` is
  col-std-izable" (the reusable James leading-term fact for the twisted
  polytabloid), and (a2) the `M`-subtraction stability bridge to `X = f_w − M`.
  (a1) is the hard, reusable nut; (a2) is a dominance-bookkeeping induction.
* **(b)** Reconsider whether R2.b needs maximal-support col-std-izability at
  all, or whether `Δ ∈ V` can be reached by a different decomposition that
  keeps `f_w`'s leading structure explicit (e.g. peel `f_w`'s own maximal term
  first, where col-std-izability *is* clean, then induct on a smaller twisted
  object). The validated invariant in §"Corrected mechanism" suggests an
  induction on `(srRank, rowInv)` of the *running maximal tabloid* rather than
  on `σ`.

The deliverable's Lean signature in the issue is fine to keep; only the
"Strategy — column-antisymmetry (James) ... `Q ∩ w⁻¹Pw` sign-cancellation"
section is wrong and must be replaced by the column-straightening induction
above.
