import Formalization.OpenDisk.JointTopology

set_option linter.style.header false

/-!
# The local phase group in anchored coordinates

The coordinate homeomorphism preserves addition.  Local phase groups are
closed in the full phase table space and compact for compact coefficients.
-/

noncomputable section

open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G P Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup P]
  [TopologicalSpace P] [IsTopologicalAddGroup P]

/-- The anchored parametrization preserves the full additive group structure. -/
def localFunctionCoordinatesEquiv (facets : Facet → Set ι) :
    localFunctionSubgroup (G := G) facets P ≃+ (AllowedConfiguration (G := G) facets → P) where
  toEquiv := ((localFunctionHomeomorph facets).trans (localPhaseHomeomorph facets)).toEquiv
  map_add' f g := by
    funext c
    exact congrFun (anchoredCoordinate_add f.val g.val) c.val

theorem continuous_localFunctionCoordinatesEquiv (facets : Facet → Set ι) :
    Continuous (localFunctionCoordinatesEquiv (G := G) (P := P) facets) :=
  ((localFunctionHomeomorph facets).trans (localPhaseHomeomorph facets)).continuous_toFun

theorem continuous_localFunctionCoordinatesEquiv_symm (facets : Facet → Set ι) :
    Continuous (localFunctionCoordinatesEquiv (G := G) (P := P) facets).symm :=
  ((localFunctionHomeomorph facets).trans (localPhaseHomeomorph facets)).continuous_invFun

theorem isClosed_localFunctionSubgroup [T2Space P] (facets : Facet → Set ι) :
    IsClosed (localFunctionSubgroup (G := G) facets P : Set (Configuration ι G → P)) := by
  have heq : (localFunctionSubgroup (G := G) facets P : Set (Configuration ι G → P)) =
      ⋂ c : {c : Configuration ι G // ∀ ρ, ¬∀ i ∈ c.support, i ∈ facets ρ},
        {f | anchoredCoordinate f c.val = 0} := by
    ext f
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h c => h c.val c.property, fun h c hc => h ⟨c, hc⟩⟩
  rw [heq]
  exact isClosed_iInter fun c =>
    isClosed_eq ((continuous_apply c.val).comp continuous_anchoredCoordinate) continuous_const

instance [CompactSpace P] (facets : Facet → Set ι) :
    CompactSpace (localFunctionSubgroup (G := G) facets P) :=
  ((localFunctionHomeomorph facets).trans (localPhaseHomeomorph facets)).symm.compactSpace

end OpenDisk
