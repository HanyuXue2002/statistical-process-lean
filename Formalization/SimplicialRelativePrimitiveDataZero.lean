import Formalization.SimplicialRelativePrimitiveZero
import Formalization.RelativeSectionComparison
import Mathlib.Combinatorics.Colex

set_option linter.style.header false

/-!
# Degree-zero relative primitive data for simplicial cochains

The normalized global zero-cochain and the simplex cone homotopies form the
relative primitive sections required by the abstract comparison theorem.  The
closed-star normalization and cone naturality prove their compatibility on
every simplex containing the active vertex.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Colexicographic order on degree-zero simplex coordinates, used by the
elementary-path model. -/
local instance simplexZeroColexOrder : LinearOrder (Simplex K 0) :=
  LinearOrder.lift'
    (fun η : Simplex K 0 => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

/-- The normalized global zero-cochain restricts on every visible facet to
the local simplex cone primitive of the restricted coboundary. -/
theorem restrictFacet_normalizedPrimitiveZero
    (ρ : NonemptySimplex K) (η : Simplex K 0)
    (hηρ : η.1 ⊆ ρ.1) (a : CoboundaryGroup (G := G) K 0) :
    coordinateRestriction (facesIn K 0 ρ)
        (normalizedPrimitiveZero K η a) =
      simplexConeHomotopy K (forgetDimension K η) ρ hηρ
        (simplexApex K η) (simplexApex_mem_forgetDimension K η) 0
        (restrictCoboundary K 0 ρ a) := by
  let η₀ := forgetDimension K η
  let v := simplexApex K η
  let hv : v ∈ η₀.1 := simplexApex_mem_forgetDimension K η
  let aStar := restrictClosedStar K η₀ 1 a.1
  have hrestrict :
      restrictClosedStarToSimplex K η₀ ρ hηρ 1 aStar =
        restrictCoboundary K 0 ρ a := by
    ext τ
    rfl
  ext τ
  calc
    coordinateRestriction (facesIn K 0 ρ)
          (normalizedPrimitiveZero K η a) τ =
        restrictClosedStarToSimplex K η₀ ρ hηρ 0
          (restrictClosedStar K η₀ 0
            (normalizedPrimitiveZero K η a)) τ := by
      rfl
    _ = restrictClosedStarToSimplex K η₀ ρ hηρ 0
          (coneHomotopy K η₀ v hv 0 aStar) τ := by
      rw [restrictClosedStar_normalizedPrimitiveZero]
    _ = simplexConeHomotopy K η₀ ρ hηρ v hv 0
          (restrictClosedStarToSimplex K η₀ ρ hηρ 1 aStar) τ := by
      exact DFunLike.congr_fun
        (LinearMap.congr_fun
          (restrictClosedStarToSimplex_coneHomotopy
            (G := G) K η₀ ρ hηρ v hv 0) aStar) τ
    _ = simplexConeHomotopy K η₀ ρ hηρ v hv 0
          (restrictCoboundary K 0 ρ a) τ := by
      rw [hrestrict]

/-- Concrete relative primitive sections in simplicial cochain degree zero. -/
def relativePrimitiveSectionDataZero :
    RelativePrimitiveSectionData
      (fun σ : NonemptySimplex K => facesIn K 0 σ)
      (facetRestrictionData (G := G) K 0) where
  globalPrimitive η a := normalizedPrimitiveZero K η a
  map_globalPrimitive η a := by
    apply Subtype.ext
    exact coboundary_normalizedPrimitiveZero K η a
  localPrimitive ρ η b :=
    simplexConeHomotopy K (forgetDimension K η.1) ρ η.2
      (simplexApex K η.1) (simplexApex_mem_forgetDimension K η.1) 0 b
  restrict_globalPrimitive ρ η hηρ a := by
    exact restrictFacet_normalizedPrimitiveZero K ρ η hηρ a

/-- The concrete degree-zero comparison equivalence for finite ordered
simplicial cochains. -/
def physicalPrimitiveComparisonEquivZero :
    PhysicalQuotient (facetRestrictionData (G := G) K 0) ≃ₗ[ℤ]
      TPrime (facetRestrictionData (G := G) K 0) :=
  RelativePrimitiveSectionData.relativeSectionComparisonEquiv
    (fun σ : NonemptySimplex K => facesIn K 0 σ)
    (facetRestrictionData (G := G) K 0)
    (relativePrimitiveSectionDataZero (G := G) K)
    (facetRestrictionData_primitiveRes (G := G) K 0)
    (facetRestrictionData_cover K 0)
    (facetCoboundary_surjective (G := G) K 0)

end GeneralSphereT.SimplicialCochain
