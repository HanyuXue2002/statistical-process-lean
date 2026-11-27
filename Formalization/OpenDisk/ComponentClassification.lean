import Formalization.OpenDisk.ComponentGroup
import Formalization.OpenDisk.SymmetryComponentSpace
import Formalization.OpenDisk.ExcitationComponents

/-! # Component groups and the literal local-conjugacy quotient -/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
  [Nonempty Facet] (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)

include rep hrep in
theorem localSymmetry_componentZero_eq_range [Fintype d.ker] :
    AddSubgroup.pathComponentZero (localSymmetries facets d (P := CirclePaths.Phase)) =
      (localDerivative (P := CirclePaths.Phase) facets d).range := by
  ext F
  change Joined (0 : localSymmetries facets d (P := CirclePaths.Phase)) F ↔ _
  rw [localSymmetry_joined_zero_iff facets d rep hrep F]
  constructor
  · rintro ⟨γ, hγ, heq⟩
    exact ⟨⟨γ, hγ⟩, Subtype.ext heq⟩
  · rintro ⟨γ, heq⟩
    exact ⟨γ.val, γ.property, congrArg Subtype.val heq⟩

def symmetryAnomalyComponentEquiv [Fintype d.ker] :
    (localSymmetries facets d (P := CirclePaths.Phase) ⧸
      (localDerivative (P := CirclePaths.Phase) facets d).range) ≃+
      ComponentGroup (localSymmetries facets d (P := CirclePaths.Phase)) :=
  QuotientAddGroup.quotientAddEquivOfEq
    (localSymmetry_componentZero_eq_range facets d rep hrep).symm

include rep hrep in
theorem finite_symmetryAnomaly [Fintype (Configuration ι G)] [Fintype d.ker] :
    Finite (localSymmetries facets d (P := CirclePaths.Phase) ⧸
      (localDerivative (P := CirclePaths.Phase) facets d).range) := by
  letI := finite_localSymmetry_components facets d rep hrep
  letI := finite_componentGroup (X := localSymmetries facets d (P := CirclePaths.Phase))
  exact Finite.of_equiv _ (symmetryAnomalyComponentEquiv facets d rep hrep).symm.toEquiv

/-- The excitation component comparison is an isomorphism of abelian groups. -/
def jointExcitationComponentGroupEquiv (hcover : ∀ i, ∃ ρ, i ∈ facets ρ) :
    ComponentGroup (LocalJointPhase facets d (AddCircle (1 : ℝ))) ≃+
      ComponentGroup (ExcitationPhase facets d (AddCircle (1 : ℝ))) := by
  letI := typedExcitationKernel_pathConnectedSpace facets d rep hrep
  exact splitComponentGroupEquiv (localForgetExcitation facets d rep hrep)
    (excitationSection facets d hcover)
    (localForgetExcitation_section facets d rep hrep hcover)
    (continuous_localForgetExcitation facets d rep hrep)
    (continuous_excitationSection facets d hcover)

end OpenDisk
