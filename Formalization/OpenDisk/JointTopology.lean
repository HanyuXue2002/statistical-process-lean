import Formalization.OpenDisk.JointLocality
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Topology of the excitation kernel and its fibers

The kernel homeomorphism below is the literal phase-graph equivalence, with
the product/subspace topologies prescribed in the report.  Thus it also
proves path connectedness of every nonempty excitation fiber.
-/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]

def localFunctionHomeomorph (facets : Facet → Set ι) :
    localFunctionSubgroup (G := G) facets P ≃ₜ LocalPhaseSpace (G := G) facets P where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem localFunctions_pathConnectedSpace (facets : Facet → Set ι) :
    PathConnectedSpace (localFunctionSubgroup (G := G) facets (AddCircle (1 : ℝ))) :=
  ((localFunctionHomeomorph facets).trans (localPhaseHomeomorph facets)).symm.pathConnectedSpace

variable [Nonempty Facet] (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)

theorem continuous_localPhaseGraph :
    Continuous (localPhaseGraph (P := P) facets d) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk continuous_subtype_val
  apply continuous_pi
  intro e
  apply continuous_pi
  intro v
  exact ((continuous_apply (v + elementaryStep e)).comp continuous_subtype_val).sub
    ((continuous_apply v).comp continuous_subtype_val)

/-- Equation (5.6) as a homeomorphism, with the specified subspace topologies. -/
def localPhaseExcitationKernelHomeomorph : localFunctionSubgroup (G := G) facets P ≃ₜ
    (forgetExcitation d elementaryStep (markedFunctionSubgroup (P := P) facets) rep).ker where
  toEquiv := (localPhaseExcitationKernelEquiv facets d rep hrep).toEquiv
  continuous_toFun := (continuous_localPhaseGraph facets d).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _

include hrep in
theorem excitationKernel_pathConnectedSpace :
    PathConnectedSpace
      (forgetExcitation d elementaryStep
        (markedFunctionSubgroup (P := AddCircle (1 : ℝ)) facets) rep).ker := by
  letI := localFunctions_pathConnectedSpace (G := G) facets
  exact (localPhaseExcitationKernelHomeomorph facets d rep hrep).pathConnectedSpace

section Fibers
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [TopologicalSpace X] [IsTopologicalAddGroup X]

/-- Translation identifies a nonempty literal fiber with the kernel. -/
def additiveFiberHomeomorphKer (f : X →+ Y) (x : X) :
    {y : X // f y = f x} ≃ₜ f.ker := by
  refine { toFun := fun y => ⟨y.val - x, ?_⟩
           invFun := fun k => ⟨k.val + x, ?_⟩
           left_inv := ?_, right_inv := ?_
           continuous_toFun := ?_, continuous_invFun := ?_ }
  · change f (y.val - x) = 0
    rw [map_sub, y.property, sub_self]
  · rw [map_add, show f k.val = 0 from k.property, zero_add]
  · intro y; apply Subtype.ext; exact sub_add_cancel y.val x
  · intro k; apply Subtype.ext; exact add_sub_cancel_right k.val x
  · exact (continuous_subtype_val.sub continuous_const).subtype_mk _
  · exact (continuous_subtype_val.add continuous_const).subtype_mk _

theorem pathConnectedSpace_additiveFiber (f : X →+ Y) (x : X)
    [PathConnectedSpace f.ker] : PathConnectedSpace {y : X // f y = f x} :=
  (additiveFiberHomeomorphKer f x).symm.pathConnectedSpace

end Fibers

include hrep in
theorem excitationFiber_pathConnectedSpace
    (x : LocalJointPhase facets d (AddCircle (1 : ℝ))) :
    PathConnectedSpace {y : LocalJointPhase facets d (AddCircle (1 : ℝ)) //
      forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep y =
        forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x} := by
  letI := excitationKernel_pathConnectedSpace facets d rep hrep
  exact pathConnectedSpace_additiveFiber _ x

end OpenDisk
