import Mathlib
import RepresentationTheory.AuxiliarySubgroupFunctions
import RepresentationTheory.Alignment.Attribute

noncomputable section

namespace RepresentationTheory.CyclicCharacterSpan

/-- The character of a simple complex representation lies in the rational span of the displayed auxiliary images of characters associated with cyclic subgroups. -/
@[source_ref "Chapter5/Corollary5.26.3" (role := primary)]
theorem simple_character_mem_rat_span_zpowers_auxiliary_images
    (G : Type) [Group G] [Fintype G]
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    V.character ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ (g : G) (W : FDRep ℂ ↥(Subgroup.zpowers g)),
        f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction
          (Subgroup.zpowers g) W.character} := by
  have hX_conj : ∀ H ∈ ({H : Subgroup G | ∃ g : G, H = Subgroup.zpowers g} : Set (Subgroup G)),
      ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈
        ({H : Subgroup G | ∃ g : G, H = Subgroup.zpowers g} : Set (Subgroup G)) := by
    rintro H ⟨a, rfl⟩ g
    exact ⟨g * a * g⁻¹, by rw [MonoidHom.map_zpowers]; rfl⟩
  have hcover : ∀ g : G, ∃ H ∈ ({H : Subgroup G | ∃ g : G, H = Subgroup.zpowers g} :
      Set (Subgroup G)), g ∈ H :=
    fun g => ⟨Subgroup.zpowers g, ⟨g, rfl⟩, Subgroup.mem_zpowers g⟩
  have artin :=
    (RepresentationTheory.AuxiliarySubgroupFunctions.auxiliary_cover_iff_character_mem_span
      G _ hX_conj).mp hcover V ‹_›
  apply Submodule.span_mono _ artin
  rintro f ⟨H, ⟨g, rfl⟩, W, rfl⟩
  exact ⟨g, W, rfl⟩

end RepresentationTheory.CyclicCharacterSpan
