import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Problem 8.2.5: `Tor` and `Ext` are independent of the projective resolution

Let `P_•`, `Q_•` be two projective resolutions of `M`.

* (i) There exists `f₀ : P₀ → Q₀` with `d^Q₀ ∘ f₀ = d^P₀`.
* (ii) Inductively there exist `f_j : P_j → Q_j` with `d^Q_j ∘ f_j = f_{j-1} ∘ d^P_j`; the
  collection `f : P_• → Q_•` is a **morphism of resolutions**.
* (iii) `f` induces maps `ψ_i(P, Q, f) : Tor_i^P(M, N) → Tor_i^Q(M, N)` independent of `f`.
* (iv) The `ψ_i(P, Q)` are isomorphisms.
* (v) Similarly for `Ext`: `ξ_i(Q, P, f) : Ext^i_P(M, N) → Ext^i_Q(M, N)` are independent of
  `f` and are isomorphisms.

The upshot is that the groups `Tor_i` and `Ext^i` do not depend on the chosen resolution, which
justifies suppressing `P_•` from the notation.

## Formalization notes

Parts (i) and (ii) are exactly the existence of a lift of the identity `𝟙 M` to a chain map
between the two resolutions, compatible with the augmentations `π`. This is captured by the
first statement: a morphism `f : P.complex ⟶ Q.complex` with `f ≫ Q.π = P.π`.

Parts (iii)–(v), independence of `f` up to the induced map on homology and the isomorphism
property, are exactly the statement that any two projective resolutions of `M` are homotopy
equivalent (`ProjectiveResolution.homotopyEquiv`). A homotopy equivalence induces isomorphisms
on the homology of any additive functor applied to the resolution, i.e. on `Tor_i` and `Ext^i`,
and any two lifts are homotopic (so the induced maps agree). We record this as the existence of
a homotopy equivalence between the two complexes.

Both facts are discharged directly by Mathlib's `ProjectiveResolution.lift`/`lift_commutes`
(morphism of resolutions) and `ProjectiveResolution.homotopyEquiv` (homotopy equivalence).
-/

namespace Etingof

open CategoryTheory

universe u

variable {A : Type u} [Ring A] {M : ModuleCat.{u} A}

/-- **Problem 8.2.5(i)–(ii).** Any two projective resolutions of `M` admit a *morphism of
resolutions*: a chain map `f : P_• → Q_•` compatible with the augmentations to `M`. -/
theorem Problem_8_2_5_morphism_of_resolutions
    (P Q : ProjectiveResolution M) :
    ∃ f : P.complex ⟶ Q.complex, f ≫ Q.π = P.π :=
  ⟨ProjectiveResolution.lift (𝟙 M) P Q, by simp⟩

/-- **Problem 8.2.5(iii)–(v).** Any two projective resolutions of `M` are homotopy equivalent.
Applying an additive functor and taking homology, this shows the induced maps on `Tor_i` and
`Ext^i` are isomorphisms independent of the chosen morphism of resolutions, so `Tor_i` and
`Ext^i` do not depend on the resolution. -/
theorem Problem_8_2_5_independence
    (P Q : ProjectiveResolution M) :
    Nonempty (HomotopyEquiv P.complex Q.complex) :=
  ⟨ProjectiveResolution.homotopyEquiv P Q⟩

end Etingof
