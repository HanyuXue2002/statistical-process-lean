import Formalization.SimplicialRelativePrimitive
import Formalization.RelativeSectionComparison
import Mathlib.Combinatorics.Colex

set_option linter.style.header false

/-!
# Positive-degree relative primitive data for simplicial cochains

This is the final concrete packaging of the positive-degree construction.
For an active `(m+1)`-simplex, `normalizedPrimitiveSucc` is the chosen global
primitive.  On every facet which contains that simplex, the primitive is the
ordinary cone homotopy of the restricted physical coboundary.  The closed-star
comparison theorem proves that these choices are compatible.

The resulting `RelativePrimitiveSectionData` feeds directly into the abstract
comparison theorem, producing the objectwise equivalence without mentioning
the auxiliary path-lift package.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Use the vertex order to order simplex coordinates colexicographically.
This supplies the auxiliary coordinate order used by the elementary-path
model. -/
local instance simplexColexOrder (n : ℕ) :
    LinearOrder (Simplex K n) :=
  LinearOrder.lift'
    (fun η : Simplex K n => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

/-- The positive-degree global primitive restricts on every visible facet to
the simplex cone primitive of the restricted physical coboundary. -/
theorem restrictFacet_normalizedPrimitiveSucc
    (m : ℕ) (ρ : NonemptySimplex K) (η : Simplex K (m + 1))
    (hηρ : η.1 ⊆ ρ.1) (a : CoboundaryGroup (G := G) K (m + 1)) :
    coordinateRestriction (facesIn K (m + 1) ρ)
        (normalizedPrimitiveSucc K m η a) =
      simplexConeHomotopy K (forgetDimension K η) ρ hηρ
        (simplexApex K η) (simplexApex_mem_forgetDimension K η) (m + 1)
        (restrictCoboundary K (m + 1) ρ a) := by
  let η₀ := forgetDimension K η
  let v := simplexApex K η
  let hv : v ∈ η₀.1 := simplexApex_mem_forgetDimension K η
  let aStar := restrictClosedStar K η₀ (m + 2) a.1
  have hrestrict :
      restrictClosedStarToSimplex K η₀ ρ hηρ (m + 2) aStar =
        restrictCoboundary K (m + 1) ρ a := by
    ext τ
    rfl
  ext τ
  calc
    coordinateRestriction (facesIn K (m + 1) ρ)
          (normalizedPrimitiveSucc K m η a) τ =
        restrictClosedStarToSimplex K η₀ ρ hηρ (m + 1)
          (restrictClosedStar K η₀ (m + 1)
            (normalizedPrimitiveSucc K m η a)) τ := by
      rfl
    _ = restrictClosedStarToSimplex K η₀ ρ hηρ (m + 1)
          (coneHomotopy K η₀ v hv (m + 1) aStar) τ := by
      rw [restrictClosedStar_normalizedPrimitiveSucc]
    _ = simplexConeHomotopy K η₀ ρ hηρ v hv (m + 1)
          (restrictClosedStarToSimplex K η₀ ρ hηρ (m + 2) aStar) τ := by
      exact DFunLike.congr_fun
        (LinearMap.congr_fun
          (restrictClosedStarToSimplex_coneHomotopy
            (G := G) K η₀ ρ hηρ v hv (m + 1)) aStar) τ
    _ = simplexConeHomotopy K η₀ ρ hηρ v hv (m + 1)
          (restrictCoboundary K (m + 1) ρ a) τ := by
      rw [hrestrict]

/-- Concrete relative primitive sections in simplicial cochain degree
`m+1`. -/
def relativePrimitiveSectionDataSucc (m : ℕ) :
    RelativePrimitiveSectionData
      (fun σ : NonemptySimplex K => facesIn K (m + 1) σ)
      (facetRestrictionData (G := G) K (m + 1)) where
  globalPrimitive η a := normalizedPrimitiveSucc K m η a
  map_globalPrimitive η a := by
    apply Subtype.ext
    exact coboundary_normalizedPrimitiveSucc K m η a
  localPrimitive ρ η b :=
    simplexConeHomotopy K (forgetDimension K η.1) ρ η.2
      (simplexApex K η.1) (simplexApex_mem_forgetDimension K η.1)
      (m + 1) b
  restrict_globalPrimitive ρ η hηρ a := by
    exact restrictFacet_normalizedPrimitiveSucc K m ρ η hηρ a

/-- The actual positive-degree comparison equivalence for finite ordered
simplicial cochains. -/
def physicalPrimitiveComparisonEquivSucc (m : ℕ) :
    PhysicalQuotient (facetRestrictionData (G := G) K (m + 1)) ≃ₗ[ℤ]
      TPrime (facetRestrictionData (G := G) K (m + 1)) :=
  RelativePrimitiveSectionData.relativeSectionComparisonEquiv
    (fun σ : NonemptySimplex K => facesIn K (m + 1) σ)
    (facetRestrictionData (G := G) K (m + 1))
    (relativePrimitiveSectionDataSucc (G := G) K m)
    (facetRestrictionData_primitiveRes (G := G) K (m + 1))
    (facetRestrictionData_cover K (m + 1))
    (facetCoboundary_surjective (G := G) K (m + 1))

end GeneralSphereT.SimplicialCochain
