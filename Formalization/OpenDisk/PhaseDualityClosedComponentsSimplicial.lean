import Formalization.OpenDisk.PhaseDualityAveragingSimplicial
import Formalization.OpenDisk.PhaseDualityClosedComponents

set_option linter.style.header false

/-!
# Connected components of actual finite simplicial closed-SPT phases

For every finite simplicial complex and finite abelian coefficient group,
the identity component is exactly the actual sum of facet-curvature phases.
Both ordinary and path connected components are covered, and the quotient
is a finite abelian group.  No sphere or contractibility hypothesis is used.
-/

noncomputable section

open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.PhaseDuality

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G] [Finite G]
variable (K : AbstractSimplicialComplex V) (n : ℕ)

local instance : Fintype (NonemptySimplex K) := Fintype.ofFinite _
local instance : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel
local instance finiteCochainComponents (m : ℕ) : Finite (Cochain K m G) :=
  Finite.of_equiv (Simplex K m → G) Finsupp.equivFunOnFinite.symm
local instance : Fintype (coboundaryToRange (G := G) K n).ker := Fintype.ofFinite _
local instance : Fintype (LinearMap.range (coboundary (G := G) K n)) := Fintype.ofFinite _

private theorem localClosedExtension (ρ : NonemptySimplex K)
    (z : Configuration (facesIn K n ρ) G)
    (hz : (facetRestrictionData (G := G) K n).localD ρ z = 0) :
    ∃ w : Cochain K n G, coboundaryToRange K n w = 0 ∧
      (facetRestrictionData (G := G) K n).primitiveRes ρ w = z := by
  obtain ⟨w, hw, hwr⟩ := simplicial_local_closed_extension K n ρ z hz
  exact ⟨w, Subtype.ext hw, hwr⟩

/-- The actual path component of zero consists precisely of local curvature sums. -/
theorem simplicialClosedSPT_joined_zero_iff (φ : simplicialClosedSPT (G := G) K n) :
    Joined (0 : simplicialClosedSPT (G := G) K n) φ ↔
      φ ∈ simplicialFacetCurvaturePhases (G := G) K n :=
  closedSPT_joined_zero_iff _ _ _ (facetRestrictionData_primitiveRes (G := G) K n)
    (coboundaryToRange_surjective K n) (localClosedExtension K n) φ

/-- The report's closed-SPT quotient is finite for every finite complex. -/
theorem finite_simplicialClosedSPT_quotient :
    Finite (simplicialClosedSPT (G := G) K n ⧸ simplicialFacetCurvaturePhases (G := G) K n) :=
  finite_closedSPT_quotient _ _ _ (facetRestrictionData_primitiveRes (G := G) K n)
    (coboundaryToRange_surjective K n) (localClosedExtension K n)

/-- Ordinary connected components give the same identity subgroup. -/
theorem simplicialClosedSPT_mem_connectedComponent_zero_iff
    (φ : simplicialClosedSPT (G := G) K n) :
    φ ∈ connectedComponent (0 : simplicialClosedSPT (G := G) K n) ↔
      φ ∈ simplicialFacetCurvaturePhases (G := G) K n :=
  closedSPT_mem_connectedComponent_zero_iff _ _ _
    (facetRestrictionData_primitiveRes (G := G) K n)
    (coboundaryToRange_surjective K n) (localClosedExtension K n) φ

end OpenDisk.PhaseDuality
