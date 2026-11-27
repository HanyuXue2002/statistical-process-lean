import Formalization.OpenDisk.ComponentClassification
import Formalization.OpenDisk.LocalityClosed
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Ordinary connected components agree with the proved symmetry path components -/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk
variable {ι G B Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
  [Nonempty Facet] (facets : Facet → Set ι) (d : Configuration ι G →+ B)

theorem isClosed_localDerivative_range :
    IsClosed ((localDerivative (P := CirclePhase) facets d).range :
      Set (localSymmetries facets d (P := CirclePhase))) := by
  have h : IsCompact (Set.range (localDerivative (P := CirclePhase) facets d)) :=
    isCompact_range (continuous_localDerivative facets d)
  exact h.isClosed

variable (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)

include rep hrep in
theorem localSymmetry_mem_connectedComponent_zero_iff
    [Fintype (Configuration ι G)] [Fintype d.ker]
    (F : localSymmetries facets d (P := CirclePhase)) :
    F ∈ connectedComponent (0 : localSymmetries facets d (P := CirclePhase)) ↔
      F ∈ (localDerivative (P := CirclePhase) facets d).range := by
  let R := (localDerivative (P := CirclePhase) facets d).range
  letI : IsClosed (R : Set (localSymmetries facets d (P := CirclePhase))) :=
    isClosed_localDerivative_range facets d
  letI := finite_symmetryAnomaly facets d rep hrep
  letI : DiscreteTopology (localSymmetries facets d (P := CirclePhase) ⧸ R) := inferInstance
  constructor
  · intro hF
    have h := isPreconnected_connectedComponent.constant
      (show Continuous (QuotientAddGroup.mk' R) from continuous_quot_mk).continuousOn
      hF mem_connectedComponent
    apply (QuotientAddGroup.eq_zero_iff F).mp
    simpa only [map_zero] using h
  · intro hF
    apply pathComponent_subset_component (0 : localSymmetries facets d (P := CirclePhase))
    change F ∈ AddSubgroup.pathComponentZero (localSymmetries facets d (P := CirclePhase))
    rw [localSymmetry_componentZero_eq_range facets d rep hrep]
    exact hF

include rep hrep in
theorem localSymmetry_connected_iff_joined_zero
    [Fintype (Configuration ι G)] [Fintype d.ker]
    (F : localSymmetries facets d (P := CirclePhase)) :
    F ∈ connectedComponent (0 : localSymmetries facets d (P := CirclePhase)) ↔
      Joined (0 : localSymmetries facets d (P := CirclePhase)) F := by
  rw [localSymmetry_mem_connectedComponent_zero_iff facets d rep hrep]
  change F ∈ (localDerivative (P := CirclePhase) facets d).range ↔
    F ∈ AddSubgroup.pathComponentZero (localSymmetries facets d (P := CirclePhase))
  rw [localSymmetry_componentZero_eq_range facets d rep hrep]

end OpenDisk
