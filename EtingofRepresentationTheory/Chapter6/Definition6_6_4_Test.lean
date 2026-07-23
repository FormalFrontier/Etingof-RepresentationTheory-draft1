import EtingofRepresentationTheory.Chapter6.Definition6_6_4

/-!
# Downstream import/`#check` test for Definition 6.6.4

This file imports `Chapter6/Definition6_6_4.lean` and pins the public signatures of the
reflection functor `F⁻ᵢ` at a source vertex: the canonical map `ψ : V_i → ⊕_{i→j} V_j`,
the cokernel-based vertex spaces, the functor `reflectionFunctorMinus` itself, and the
object/map computation theorems that downstream files (`Proposition6_6_6_source`,
`ReflectionFunctorInfrastructure`, `Corollary6_8_3`/`6_8_4`, ...) rely on.

Its purpose is to catch a regression in the source of Definition 6.6.4 even when cached
oleans would otherwise hide it from the aggregate build: because this file `import`s the
definition file and re-elaborates the endpoint statements, it forces a fresh check of their
public API. The specific regression this guards against is the loss of the
`Module k (⊕_{i→j} V_j)` / `HasQuotient` instances underneath the cokernel construction,
which broke fresh elaboration of `reflectionFunctorMinus`, `reflFunctorMinus_obj_eq`, and
`reflFunctorMinus_mapLinear_ne_eq`.

See issue #7524 (restore fresh-buildable reflection functor F⁻ of Definition 6.6.4).
-/

-- The public endpoints must remain importable under these names.
#check @Etingof.ArrowsOutOf
#check @Etingof.addCommGroupOfRing
#check @Etingof.QuiverRepresentation.sourceMap
#check @Etingof.reflFunctorMinus_objAt
#check @Etingof.reflFunctorMinus_acmAt
#check @Etingof.reflFunctorMinus_modAt
#check @Etingof.reflectionFunctorMinus
#check @Etingof.reflFunctorMinus_obj_ne
#check @Etingof.reflFunctorMinus_obj_eq
#check @Etingof.reflFunctorMinus_mkQ
#check @Etingof.reflFunctorMinus_mapLinear_ne_ne
#check @Etingof.reflFunctorMinus_mapLinear_ne_eq

-- Signature locks: each `example` fails to elaborate if the corresponding statement drifts.

/-- The canonical source map `ψ : ρ_i → ⊕_{i→j} ρ_j` is `k`-linear into the direct sum
built with the ambient (`AddCommMonoid`) instances on the summands. -/
noncomputable example
    {k : Type*} [CommRing k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) :=
  ρ.sourceMap i

/-- The reflection functor `F⁻ᵢ` sends a representation of `Q` to a representation of the
quiver `Q̄ᵢ` with the arrows at the source `i` reversed. -/
noncomputable example
    {k : Type*} [CommRing k] (Q : Type*) [DecidableEq Q] [Quiver Q]
    (i : Q) (hi : Etingof.IsSource Q i) (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i) :=
  Etingof.reflectionFunctorMinus Q i hi ρ

/-- At the source vertex `i`, the space `F⁻ᵢ(ρ)_i` is the cokernel of `ψ`. -/
example
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i =
    ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
      LinearMap.range (ρ.sourceMap i)) :=
  Etingof.reflFunctorMinus_obj_eq hi ρ

/-- At a vertex `v ≠ i`, the space `F⁻ᵢ(ρ)_v` is unchanged from `ρ_v`. -/
example
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v = ρ.obj v :=
  Etingof.reflFunctorMinus_obj_ne hi ρ v hv
