import Formalization.OpenDisk.PhaseDualityAveraging
import Formalization.OpenDisk.PhaseDualitySimplicial
import Formalization.SimplicialPhysicalPrimitiveComparison

set_option linter.style.header false

/-!
# Closed-shift averaging for actual finite simplicial cochains

The geometric input to finite averaging is proved here.  A closed local
cochain is first extended by zero, then corrected by the already constructed
global normalized primitive.  This works uniformly in degree zero and
positive degrees, including simplices with no cochain coordinates.
-/

noncomputable section

open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.PhaseDuality

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (n : ℕ)

local instance : Fintype (NonemptySimplex K) := Fintype.ofFinite _
local instance : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

theorem simplicialRelativePrimitive_local_zero (ρ : NonemptySimplex K)
    (i : facesIn K n ρ) :
    (simplicialRelativePrimitiveSectionData (G := G) K n).localPrimitive ρ i 0 = 0 := by
  cases n with
  | zero =>
      change simplexConeHomotopy K (forgetDimension K i.1) ρ i.2
        (simplexApex K i.1) (simplexApex_mem_forgetDimension K i.1) 0 0 = 0
      exact map_zero _
  | succ m =>
      change simplexConeHomotopy K (forgetDimension K i.1) ρ i.2
        (simplexApex K i.1) (simplexApex_mem_forgetDimension K i.1) (m + 1) 0 = 0
      exact map_zero _

/-- Every closed cochain on a simplex has an actual globally closed
extension, with no cohomology or contractibility assumption on `K`. -/
theorem simplicial_local_closed_extension (ρ : NonemptySimplex K)
    (z : Configuration (facesIn K n ρ) G) (hz : localCoboundary K n ρ z = 0) :
    ∃ w : Cochain K n G, coboundary K n w = 0 ∧ restrictCochain K n ρ w = z := by
  obtain ⟨w, hw, hwr⟩ := closed_extension_of_relativePrimitiveSections
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (facetRestrictionData (G := G) K n)
    (facetRestrictionData_primitiveRes (G := G) K n)
    (simplicialRelativePrimitiveSectionData (G := G) K n)
    (simplicialRelativePrimitive_local_zero K n) ρ z hz
  refine ⟨w, ?_, hwr⟩
  exact congrArg Subtype.val hw

section Finite

variable [Finite G]

local instance finiteCochain (m : ℕ) : Finite (Cochain K m G) :=
  Finite.of_equiv (Simplex K m → G) Finsupp.equivFunOnFinite.symm

local instance closedShiftFintype : Fintype (coboundaryToRange (G := G) K n).ker :=
  Fintype.ofFinite _

/-- For every finite simplicial complex and finite abelian coefficient
group, the order of the actual globally closed-shift group kills the
closed-SPT phase quotient. -/
theorem simplicialClosedSPT_card_smul_mem_facetCurvature
    (φ : simplicialClosedSPT (G := G) K n) :
    Fintype.card (coboundaryToRange (G := G) K n).ker • φ ∈
      simplicialFacetCurvaturePhases (G := G) K n := by
  apply closedSPT_card_smul_mem_facetCurvature
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (facetRestrictionData (G := G) K n)
    (facetRestrictionData_primitiveRes (G := G) K n)
    (coboundaryToRange_surjective K n)
  intro ρ z hz
  obtain ⟨w, hw, hwr⟩ := simplicial_local_closed_extension K n ρ z hz
  exact ⟨w, Subtype.ext hw, hwr⟩

end Finite

end OpenDisk.PhaseDuality
