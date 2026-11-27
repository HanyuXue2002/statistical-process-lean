import Formalization.Section4SimplicialBasepointLift
import Formalization.Section4TopologicalComparisons

set_option linter.style.header false

/-!
# Section 4: the concrete degree-zero comparison

The finite ordered simplicial-cochain model already supplies every algebraic
part of the based row: the left map is injective, both adjacent pairs are
exact, and the obstruction map is onto.  Consequently the only datum still
needed to pass from `Tau` to pointed mapping classes is the geometric cone
criterion identifying primitive restrictions with pointed null maps.

This file specializes the abstract first-isomorphism argument to the actual
groups attached to a finite ordered simplicial complex.  In particular, no
image identity, surjectivity hypothesis, or basepoint-lift hypothesis remains
in the public theorem.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.Section4

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)

/-- The based strict-section group occurring in the concrete row (4.3). -/
abbrev SimplicialBasedSections :=
  (simplicialBasepointRowData (G := G) M b n).BasedSections

/-- Proposition 4.3 for finite ordered simplicial cochains, after the pointed
cone criterion has identified the chosen subgroup `NullMaps` with the range
of primitive restriction. -/
def simplicialTheta
    (NullMaps : Submodule ℤ (SimplicialBasedSections (G := G) M b n))
    (hnull :
      LinearMap.range
          (simplicialBasepointRowData
            (G := G) M b n).basedRestriction =
        NullMaps) :
    Tau (fun σ : NonemptySimplex M => facesIn M n σ)
        (facetRestrictionData (G := G) M n) ≃ₗ[ℤ]
      PointedHomotopyClasses
        (SimplicialBasedSections (G := G) M b n) NullMaps := by
  exact theta
    (simplicialBasepointRowData (G := G) M b n)
    NullMaps
    (exact_restrictionClass_obstruction
      (fun σ : NonemptySimplex M => facesIn M n σ)
      (facetRestrictionData (G := G) M n)
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) M n))
    (obstruction_surjective
      (fun σ : NonemptySimplex M => facesIn M n σ)
      (facetRestrictionData (G := G) M n)
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) M n)
      (simplicialMapRedDist_surjective (G := G) M n))
    hnull

/-- Formula (4.14): the obstruction class of a based strict section is sent
to the quotient class represented by that same section. -/
@[simp]
theorem simplicialTheta_obstruction
    (NullMaps : Submodule ℤ (SimplicialBasedSections (G := G) M b n))
    (hnull :
      LinearMap.range
          (simplicialBasepointRowData
            (G := G) M b n).basedRestriction =
        NullMaps)
    (f : SimplicialBasedSections (G := G) M b n) :
    simplicialTheta (G := G) M b n NullMaps hnull
        ((simplicialBasepointRowData
          (G := G) M b n).basedObstruction
            (simplicialObstruction (G := G) M n) f) =
      NullMaps.mkQ f := by
  exact theta_obstruction
    (simplicialBasepointRowData (G := G) M b n)
    NullMaps
    (exact_restrictionClass_obstruction
      (fun σ : NonemptySimplex M => facesIn M n σ)
      (facetRestrictionData (G := G) M n)
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) M n))
    (obstruction_surjective
      (fun σ : NonemptySimplex M => facesIn M n σ)
      (facetRestrictionData (G := G) M n)
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) M n)
      (simplicialMapRedDist_surjective (G := G) M n))
    hnull f

end GeneralSphereT.SimplicialCochain
