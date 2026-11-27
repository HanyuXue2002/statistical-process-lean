import Formalization.OpenDisk.Excitation
import Formalization.OpenDisk.JointTopology
import Formalization.OpenDisk.SplitTopology

/-!
# The excitation forgetful map: quotient, product, fibers, and components

The target is the original operator-local phase-table subgroup. The section
comes from the proved local normal form, and the kernel is exactly the graph
of a local phase. Thus the comparison uses the literal spaces of the report.
-/

noncomputable section
set_option maxHeartbeats 800000
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P]
  [TopologicalSpace P] [IsTopologicalAddGroup P] [Nonempty Facet]
  (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)
  (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)

def typedExcitationKernelHomeomorph :
    (localForgetExcitation (P := P) facets d rep hrep).ker ≃ₜ
      (forgetExcitation d elementaryStep (markedFunctionSubgroup (P := P) facets) rep).ker := by
  have h : (localForgetExcitation (P := P) facets d rep hrep).ker =
      (forgetExcitation d elementaryStep (markedFunctionSubgroup (P := P) facets) rep).ker := by
    ext x
    constructor
    · intro hx; exact congrArg Subtype.val hx
    · intro hx; exact Subtype.ext hx
  exact Homeomorph.setCongr (congrArg SetLike.coe h)

def excitationKernelLocalPhaseHomeomorph :
    (localForgetExcitation (P := P) facets d rep hrep).ker ≃ₜ
      localFunctionSubgroup (G := G) facets P :=
  (typedExcitationKernelHomeomorph facets d rep hrep).trans
    (localPhaseExcitationKernelHomeomorph facets d rep hrep).symm

/-- The joint space is globally a product over full excitation statistics. -/
def jointExcitationProductHomeomorph :
    LocalJointPhase facets d P ≃ₜ
      ExcitationPhase facets d P × localFunctionSubgroup (G := G) facets P :=
  (splitContinuousAddEquiv (localForgetExcitation facets d rep hrep)
    (excitationSection facets d hcover)
    (localForgetExcitation_section facets d rep hrep hcover)
    (continuous_localForgetExcitation facets d rep hrep)
    (continuous_excitationSection facets d hcover)).toHomeomorph.trans
      ((Homeomorph.refl _).prodCongr (excitationKernelLocalPhaseHomeomorph facets d rep hrep))

/-- The exact quotient statement of Theorem 5.3 for the excitation projection. -/
def jointExcitationQuotientHomeomorph :
    (LocalJointPhase facets d P ⧸ (localForgetExcitation (P := P) facets d rep hrep).ker) ≃ₜ
      ExcitationPhase facets d P :=
  splitQuotientHomeomorph (X := LocalJointPhase facets d P) (Y := ExcitationPhase facets d P)
    (localForgetExcitation (P := P) facets d rep hrep)
    (excitationSection (P := P) facets d hcover)
    (localForgetExcitation_section facets d rep hrep hcover)
    (continuous_localForgetExcitation facets d rep hrep)
    (continuous_excitationSection facets d hcover)

theorem typedExcitationKernel_pathConnectedSpace :
    PathConnectedSpace (localForgetExcitation (P := AddCircle (1 : ℝ)) facets d rep hrep).ker := by
  letI := localFunctions_pathConnectedSpace (G := G) facets
  exact (excitationKernelLocalPhaseHomeomorph facets d rep hrep).symm.pathConnectedSpace

include hcover in
/-- Both directions of the path relation are preserved by the second forgetful map. -/
theorem joint_excitation_joined_iff
    (x y : LocalJointPhase facets d (AddCircle (1 : ℝ))) :
    Joined x y ↔ Joined (localForgetExcitation facets d rep hrep x)
      (localForgetExcitation facets d rep hrep y) := by
  letI := typedExcitationKernel_pathConnectedSpace facets d rep hrep
  exact split_joined_iff (localForgetExcitation facets d rep hrep)
    (excitationSection facets d hcover)
    (localForgetExcitation_section facets d rep hrep hcover)
    (continuous_localForgetExcitation facets d rep hrep)
    (continuous_excitationSection facets d hcover) x y

/-- The induced equivalence of genuine path-component spaces, with quotient topology. -/
def jointExcitationComponentHomeomorph :
    ZerothHomotopy (LocalJointPhase facets d (AddCircle (1 : ℝ))) ≃ₜ
      ZerothHomotopy (ExcitationPhase facets d (AddCircle (1 : ℝ))) := by
  letI := typedExcitationKernel_pathConnectedSpace facets d rep hrep
  exact splitComponentHomeomorph (localForgetExcitation facets d rep hrep)
    (excitationSection facets d hcover)
    (localForgetExcitation_section facets d rep hrep hcover)
    (continuous_localForgetExcitation facets d rep hrep)
    (continuous_excitationSection facets d hcover)

end OpenDisk
