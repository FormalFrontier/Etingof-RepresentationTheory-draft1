# Wall 3 R2.b (`Δ ∈ V`) — the crux is column-antisymmetry, not "re-packaging"

Feature session for issue #4593. Outcome: **validated candidate 1, located and
corrected the real crux, decomposed into two sub-issues.** No Lean changes
landed (the theorem is larger than the design doc scoped).

## What was validated (mandatory pre-formalization step)

Scripts `progress/r2b-decomp-validation.py` (exact rational linear algebra) and
the broad randomized check `/tmp/r2b_crux.py` (reproduced below as
`progress/r2b-peeling-validation.py` lineage):

1. **`Δ ∈ V` is TRUE and witnessed at strictly-smaller rank.** Solving
   `Δ = Σ x_T e_T` in the SYT-polytabloid basis on (2,2) and (3,2): every
   constituent SYT `T` has `(srRank T, rowInv T) <lex (srRank σ, rowInv σ)`.
   E.g. (2,2): `Δ = −e_{(0,2,1,3)}`; (3,2): `Δ = −2·e_{(0,1,3,4,2)}`.

2. **Direction fix.** The codebase `srRank σ = #{τ : σ strictly dominates τ}`
   counts tabloids **below** σ, so a tabloid dominated by σ has *smaller*
   srRank (IH-available). An earlier draft of the validation script had the
   direction flipped and spuriously reported constituents "above σ". With the
   correct direction every constituent is strictly below σ.

3. **The leading-term elimination never gets stuck and always reaches zero.**
   Across 160 random `(σ, w)` on shapes (2,2), (3,2), (2,2,1), (3,3): peeling
   the dominance-maximal support tabloid of `Δ` (using any column-standard
   representative) is *never* blocked by a no-column-standard maximal tabloid
   (`stuck=0`), the maximal is always `≼ [σ]` (`above=0`), and the remainder
   always terminates at `0`.

## The real crux (corrects the #4584 design doc)

The design doc `progress/r2b-redesign-direct-polytabloid.md` claims candidate 1
is "largely a re-packaging of existing Algorithm A internals
(`tabloidSupport_straightening`'s `hclaim`)". **This is wrong.** `hclaim` reads
off the SYT coefficient expansion `v = Σ c_T e_T`, which *exists only because it
takes `v ∈ V` as a hypothesis*. For `Δ` we do not have `Δ ∈ V` a priori — that
is the goal. Naive leading-tabloid peeling of a support-bounded element
terminates at zero **iff** the element is in `V`, so it is circular.

Two further dead ends ruled out this session:

* **S_n-invariance shortcut is invalid.** `f_w(σ) = Σ_{q∈Q} sign(q)[w q⁻¹ σ]`
  uses *left* multiplication by `w` on tabloid representatives. The genuine
  `M^λ` left action is `of(τ) • single([β]) = single([β τ⁻¹])` (right mult on
  reps); under it `τ • ψ_σ = ψ_{στ⁻¹}`. So `f_w` is **not** a module translate
  of `ψ_σ`, and `V` being a submodule does not give `f_w ∈ V`. (The reduction
  `f_w(σ) = of(σ⁻¹) • f_w(1)` *is* valid for V-membership, but right-mult by σ
  scrambles the dominance order, so it does not help the maximal-support claim.)

* **No explicit `q∉R` polytabloid formula.** `f_w ≠ Σ_{q∈Q} sign(q) ψ_{wq⁻¹σ}`
  (single tabloids vs polytabloids), and
  `Δ ≠ Σ_{q∉R} sign(q) ψ_{wq⁻¹σ}`. The leftover `q∉R` region is `Q_eqHi`
  (`[τ_q]=[σ]`, `rowInv τ_q ≥ rowInv σ`), which is not even IH-dischargeable, so
  there is no closed form along that decomposition.

The genuine non-circular reason the peel never gets stuck is the **classical
James column-antisymmetry argument**, w.r.t. the *conjugate* column group:

> `f_w(σ)([β]) = Σ_{q : [w q⁻¹ σ] = [β]} sign(q)`. The `q`'s giving a fixed `[β]`
> form a coset of `Q ∩ w⁻¹ P w`. If that stabiliser contains an odd-sign
> element the coset sum cancels to 0. Hence at any `[β] ∈ supp(f_w(σ))` the
> column rep is forced to be "regular" — column-standardizable — and the
> dominance-maximal such `[β]` has a column-standard representative.

This is the missing structural lemma. It is a genuine theorem (needs the
`Q ∩ w⁻¹Pw` sign-cancellation), not a re-packaging.

## Decomposition

* **sub-A (crux):** `twistedPolytabloid_maximal_support_colStd` — for col-std σ
  and any w, a dominance-maximal tabloid in `supp(twistedPolytabloid w σ −
  twistedIHPart σ w)` is column-standardizable, with a representative that is
  IH-available (`≼ [σ]` in the lex `(srRank, rowInv)` order). Proof via the
  column-antisymmetry / `Q ∩ w⁻¹Pw` sign-cancellation above. This is the hard
  nut; check whether the conjugate-column-stabiliser sign machinery exists
  (`garnirAnnihilate_tabloid` is the standard-Q analogue).

* **sub-B (assembly):** `twistedPolytabloid_residual_in_V` — leading-term
  elimination over the `Finsupp (Tabloid n la)` support of `Δ`, peeling
  `c_β • ψ_{β'}` for the maximal `[β]` (sub-A gives col-std IH-available `β'`),
  discharging each `ψ_{β'}` by `ih`, concluding `Δ ∈ V` by `Submodule.sum_mem`.
  Needs a dominance-maximal-element helper over `Finsupp` support
  (`exists_dominance_maximal` currently only covers SYT finsets).

## Files

* `progress/r2b-decomp-validation.py` — exact SYT-basis decomposition of Δ, f_w.
* `progress/r2b-peeling-validation.py` — leading-term peeling (illustrates the
  multiple-col-std-rep subtlety).
* Codex second opinion (this session) independently arrived at the same
  leading-term-elimination route and named the missing structural lemma
  ("structured residual ... has an IH-available column-standard leading tabloid
  whenever nonzero"), confirming the crux is a separate lemma, not a
  re-packaging.
