import Formalization.PrimitiveIdentityLift
import Formalization.ClosedPrimitiveImage

set_option linter.style.header false

/-!
# Equality in Lemma (2.26)

This module combines the easy primitive-lift inclusion with the hard
cell-type decomposition inclusion.  Both directions use the same literal
`closedLocallyZeroElementaryPrimitivePaths` source submodule.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/--
Complete equation (2.26): the physical identity subgroup is exactly the
`d_*`-image of the elementary, closed, facetwise locally-zero primitive paths.
-/
theorem mapDPath_closedLocallyZeroElementaryPrimitivePaths_eq_physicalIdentityPaths
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    Submodule.map (mapDPath d)
        (closedLocallyZeroElementaryPrimitivePaths L) =
      physicalIdentityPaths L := by
  apply le_antisymm
  · exact
      map_closedLocallyZeroElementaryPrimitivePaths_le_physicalIdentityPaths
        facets L hprimitive hcover
  · exact physicalIdentityPaths_le_mapDPath_closedPrimitive L hd

end GeneralSphereT.PathAlgebra
