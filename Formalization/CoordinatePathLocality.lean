import Formalization.CoordinateRestriction
import Formalization.PrimitiveQuotient

set_option linter.style.header false

/-!
# Coordinate locality of the canonical path and subdivision

These are the small wrappers needed in the forward comparison map (2.35).
The abstract facet API alone cannot know about the chosen coordinate order;
we therefore assume that every primitive facet map is literally coordinate
restriction to a subtype with its inherited order.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

section ReducedSubdivisionBoundary

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- Reduced-typed pointwise form of `∂ subdivision = ∂`. -/
theorem primitiveReducedBoundary_subdivision_apply
    (R : Path (Configuration ι G) (Configuration ι G)) :
    primitiveReducedBoundary (Configuration ι G) (subdivision R) =
      primitiveReducedBoundary (Configuration ι G) R := by
  apply Subtype.ext
  change primitiveBoundary (Configuration ι G) (subdivision R) =
    primitiveBoundary (Configuration ι G) R
  exact LinearMap.congr_fun primitiveBoundary_subdivision R

/-- Linear-map form of the reduced subdivision boundary identity. -/
theorem primitiveReducedBoundary_subdivision :
    (primitiveReducedBoundary (Configuration ι G)).comp subdivision =
      primitiveReducedBoundary (Configuration ι G) := by
  apply LinearMap.ext
  intro R
  exact primitiveReducedBoundary_subdivision_apply R

end ReducedSubdivisionBoundary

section FacetwiseCoordinateLocality

universe uF uB uBA

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- A locally-zero reduced primitive distribution has a locally-zero
canonical ordered path. -/
theorem canonicalPath_mem_locallyZeroPrimitivePath
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {u : RedDist (Configuration ι G)}
    (hu : u ∈ L.locallyZeroRedDist) :
    canonicalPath u ∈ L.locallyZeroPrimitivePath := by
  rw [FacetRestrictionData.locallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have huρ : L.restrictRedDist ρ u = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker (L.restrictRedDist σ))).1 hu ρ)
  change mapRedDist (L.primitiveRes ρ) u = 0 at huρ
  rw [hprimitive ρ] at huρ
  change mapPath (L.primitiveRes ρ) (L.primitiveRes ρ)
      (canonicalPath u) = 0
  rw [hprimitive ρ]
  exact LinearMap.mem_ker.mp
    (canonicalPath_mem_coordinateRestriction_ker
      (facets ρ) (LinearMap.mem_ker.mpr huρ))

/-- Ordered subdivision preserves facetwise local vanishing under literal
coordinate restrictions. -/
theorem subdivision_mem_locallyZeroPrimitivePath
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {R : Path (Configuration ι G) (Configuration ι G)}
    (hR : R ∈ L.locallyZeroPrimitivePath) :
    subdivision R ∈ L.locallyZeroPrimitivePath := by
  rw [FacetRestrictionData.locallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have hRρ : L.restrictPrimitivePath ρ R = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker (L.restrictPrimitivePath σ))).1 hR ρ)
  change mapPath (L.primitiveRes ρ) (L.primitiveRes ρ) R = 0 at hRρ
  change mapPath (L.primitiveRes ρ) (L.primitiveRes ρ)
      (subdivision R) = 0
  rw [hprimitive ρ] at hRρ ⊢
  have hnatural := LinearMap.congr_fun
    (subdivision_coordinateRestriction (facets ρ)) R
  change
    mapPath (coordinateRestriction (facets ρ))
        (coordinateRestriction (facets ρ)) (subdivision R) =
      subdivision
        (mapPath (coordinateRestriction (facets ρ))
          (coordinateRestriction (facets ρ)) R) at hnatural
  rw [hnatural, hRρ, map_zero]

end FacetwiseCoordinateLocality

end GeneralSphereT.PathAlgebra
