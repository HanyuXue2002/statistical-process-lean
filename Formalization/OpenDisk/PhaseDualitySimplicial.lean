import Formalization.OpenDisk.PhaseDualityModelTopology
import Formalization.Section3PathFacetRefinement

set_option linter.style.header false

/-!
# Actual simplicial closed-SPT duality and the cone phase-table theorem

Here degree `n` means the report's `q = n + 1`.  The cochains, coboundary,
simplex restrictions and integral quotient are the existing concrete finite
ordered simplicial constructions.  No simplicial comparison is postulated.

The final cone theorem is a proved special case of Theorem 1.4(a).  General
contractible complexes, which need not be cones, are not silently identified
with cones.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.PhaseDuality

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (n : ℕ)

local instance simplicialFacetFintype : Fintype (NonemptySimplex K) := Fintype.ofFinite _

local instance simplicialFaceOrder : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The actual closed local phase tables on degree-`n` cochains. -/
abbrev simplicialClosedSPT :=
  closedSPT (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (coboundaryToRange_surjective K n)

/-- Actual facet-curvature tables, as a subgroup of the closed local tables. -/
abbrev simplicialFacetCurvaturePhases :=
  facetCurvaturePhases (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (facetRestrictionData (G := G) K n)
    (coboundaryToRange_surjective K n)

/-- The report's full-distribution `τ`, specialized to actual simplicial cochains. -/
abbrev simplicialFullTau :=
  FullTau (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (facetRestrictionData (G := G) K n)

/-- Proposition 2.1 on every finite ordered simplicial complex, using its
actual coboundary and its actual restrictions. -/
def simplicialClosedSPTQuotientEquiv :
    (simplicialClosedSPT (G := G) K n ⧸ simplicialFacetCurvaturePhases (G := G) K n) ≃ₗ[ℤ]
      (simplicialFullTau (G := G) K n →ₗ[ℤ] Phase) :=
  closedSPTQuotientEquiv _ _ _ (facetRestrictionData_primitiveRes (G := G) K n)
    (coboundaryToRange_surjective K n)

/-- The same canonical map is a homeomorphism for the required topologies. -/
def simplicialClosedSPTQuotientHomeomorph :
    (simplicialClosedSPT (G := G) K n ⧸ simplicialFacetCurvaturePhases (G := G) K n) ≃ₜ
      (simplicialFullTau (G := G) K n →ₗ[ℤ] Phase) :=
  closedSPTQuotientHomeomorph _ _ _ (facetRestrictionData_primitiveRes (G := G) K n)
    (coboundaryToRange_surjective K n)

theorem simplicialFullTau_eq_zero_of_cone {v : V} (hcone : IsConeAt K v)
    (x : simplicialFullTau (G := G) K n) : x = 0 := by
  letI : Nonempty (NonemptySimplex K) := ⟨coneApexSimplex K v⟩
  let e := fullTauEquivExistingTau
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (facetRestrictionData (G := G) K n)
    (coboundaryToRange_surjective K n)
  exact e.map_eq_zero_iff.mp (simplicialConeTau_eq_zero (G := G) K hcone n (e x))

/-- On a cone every closed local table belongs to the actual curvature-sum subgroup. -/
theorem simplicialClosedSPT_mem_facetCurvature_of_cone {v : V}
    (hcone : IsConeAt K v) (φ : simplicialClosedSPT (G := G) K n) :
    φ ∈ simplicialFacetCurvaturePhases (G := G) K n := by
  change closedSPTRestriction _ _ _ _ φ = 0
  apply LinearMap.ext
  intro x
  have hx : x = 0 := simplicialFullTau_eq_zero_of_cone K n hcone x
  simpa only [hx, map_zero, LinearMap.zero_apply]

/-- Literal phase-table decomposition on a cone, retaining the global phase. -/
theorem cone_closed_phase_table_decomposition {v : V} (hcone : IsConeAt K v)
    (φ : simplicialClosedSPT (G := G) K n) :
    ∃ k : ∀ σ : NonemptySimplex K, Configuration (facesIn K (n + 1) σ) G → Phase,
      ∀ c, φ.1.1 c = ∑ σ, k σ (restrictCochain K (n + 1) σ (coboundary K n c)) := by
  classical
  exact (mem_facetCurvaturePhases_iff _ _ _ (coboundaryToRange_surjective K n) φ).mp
    (simplicialClosedSPT_mem_facetCurvature_of_cone K n hcone φ)

/-- The complete closed local phase-table space on a cone is path connected. -/
theorem cone_closedSPT_pathConnectedSpace {v : V} (hcone : IsConeAt K v) :
    PathConnectedSpace (simplicialClosedSPT (G := G) K n) := by
  classical
  letI : PathConnectedSpace (simplicialFacetCurvaturePhases (G := G) K n) :=
    facetCurvaturePhases_pathConnectedSpace _ _ _
      (facetRestrictionData_primitiveRes (G := G) K n)
      (coboundaryToRange_surjective K n)
  have hs : Function.Surjective
      (Subtype.val : simplicialFacetCurvaturePhases (G := G) K n →
        simplicialClosedSPT (G := G) K n) := fun φ =>
      ⟨⟨φ, simplicialClosedSPT_mem_facetCurvature_of_cone K n hcone φ⟩, rfl⟩
  exact hs.pathConnectedSpace continuous_subtype_val

end OpenDisk.PhaseDuality
