import EtingofRepresentationTheory.Chapter8.Definition8_2_3

/-!
# Downstream import/`#check` test for Definition 8.2.3

This file imports `Chapter8/Definition8_2_3.lean` and pins the public signatures of the
general-ring Tor construction: the balanced tensor product `M ⊗_A N` over a (possibly
non-commutative) ring `A`, the additive functor `- ⊗_A N`, its `Additive` instance (needed
so it can be left-derived), and the resulting Tor functor and groups.

Its purpose is to catch a regression in the source of Definition 8.2.3 even when cached oleans
would otherwise hide it from the aggregate build: because this file `import`s the definition
file and re-elaborates the endpoint statements, it forces a fresh check of their public API.

See issue #7510 (restore the additive tensor functor and Tor definition of §8.2).
-/

open CategoryTheory

universe u

-- The public endpoints must remain importable under these names.
#check @Etingof.balancedSubgroup
#check @Etingof.tensorOver
#check @Etingof.tensorRightMap
#check @Etingof.tensorRightFunctor
#check @Etingof.TorFunctor
#check @Etingof.Tor
#check @Etingof.torIsoHomologyTensorRight

-- Signature locks: each `example` fails to elaborate if the corresponding statement drifts.

/-- The tensor product `M ⊗_A N` is a type living in the same universe as its inputs. -/
example (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] : Type u :=
  Etingof.tensorOver A N M

/-- The tensor functor `- ⊗_A N` goes from right `A`-modules to abelian groups. -/
noncomputable example (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Etingof.tensorRightFunctor A N

/-- The tensor functor is additive, so it can be left-derived. -/
example (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] :
    (Etingof.tensorRightFunctor A N).Additive :=
  inferInstance

/-- The `n`-th Tor functor is a functor from right `A`-modules to abelian groups. -/
noncomputable example (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ) :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Etingof.TorFunctor A N n

/-- `Torₙᴬ(M, N)` is an abelian group. -/
noncomputable example (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) : AddCommGrpCat.{u} :=
  Etingof.Tor A N M n

/-- `Tor` computed from a chosen projective resolution agrees with the homology of `P• ⊗_A N`. -/
noncomputable example (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) (P : ProjectiveResolution M) (n : ℕ) :
    Etingof.Tor A N M n ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).obj
        (((Etingof.tensorRightFunctor A N).mapHomologicalComplex _).obj P.complex) :=
  Etingof.torIsoHomologyTensorRight A N M P n
