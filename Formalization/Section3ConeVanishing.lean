import Formalization.Section3SimplicialBottomOperators
import Formalization.Section3PathFacetRefinement
import Formalization.Section3QuotientVanishing
import Formalization.SimplicialPhysicalPrimitiveComparison

set_option linter.style.header false

/-!
# Section 3: vanishing of `T` and `T'` on a simplicial cone

This module closes the proof.  Simultaneous replacement first moves every
apex label to apex-free labels modulo `E_id`.  The bottom-operator theorem then
kills the resulting path.  Facet refinement transfers this statement from the
apex-containing facet presentation to the global simplicial presentation used
in Section 2, and the verified comparison `T ≃ T'` gives the primitive
quotient conclusion.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- In the apex-facet presentation of a cone, every invariant elementary
path is already a physical identity. -/
theorem conePhysicalInvariantPaths_le_identity
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    physicalInvariantPaths (coneFacetRestrictionData (G := G) K v n) ≤
      physicalIdentityPaths (coneFacetRestrictionData (G := G) K v n) := by
  intro e he
  obtain ⟨ebot, hbotLabels, herror⟩ :=
    simultaneousApexReplacement_exists K hcone n e he
  have herrorInvariant : e - ebot ∈
      physicalInvariantPaths (coneFacetRestrictionData (G := G) K v n) :=
    physicalIdentityPaths_le_physicalInvariantPaths
      (coneFacetRestrictionData (G := G) K v n) herror
  have hbotInvariant : ebot ∈
      physicalInvariantPaths (coneFacetRestrictionData (G := G) K v n) := by
    have heq : ebot = e - (e - ebot) := by abel
    rw [heq]
    exact (physicalInvariantPaths
      (coneFacetRestrictionData (G := G) K v n)).sub_mem he herrorInvariant
  have hbotIdentity :=
    mem_physicalIdentityPaths_of_apexFree_labels
      K hcone n hbotInvariant hbotLabels
  have heq : e = (e - ebot) + ebot := by abel
  rw [heq]
  exact (physicalIdentityPaths
    (coneFacetRestrictionData (G := G) K v n)).add_mem herror hbotIdentity

/-- The same numerator-to-denominator inclusion for the global simplicial
facet presentation used by the Section 2 quotients. -/
theorem globalConePhysicalInvariantPaths_le_identity
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    physicalInvariantPaths (facetRestrictionData (G := G) K n) ≤
      physicalIdentityPaths (facetRestrictionData (G := G) K n) := by
  intro e he
  have heCone := globalPhysicalInvariantPaths_le_cone (G := G) K v n he
  have heIdentityCone :=
    conePhysicalInvariantPaths_le_identity (G := G) K hcone n heCone
  exact conePhysicalIdentityPaths_le_global (G := G) K hcone n heIdentityCone

/-- Representative form of `T(C_v M)=0`. -/
theorem isConeAtPhysicalQuotient_eq_zero
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (x : PhysicalQuotient (facetRestrictionData (G := G) K n)) :
    x = 0 :=
  physicalQuotient_eq_zero_of_invariant_le_identity
    (facetRestrictionData (G := G) K n)
    (globalConePhysicalInvariantPaths_le_identity (G := G) K hcone n) x

/-- Typeclass form of `T(C_v M)=0`. -/
theorem isConeAtPhysicalQuotient_subsingleton
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    Subsingleton (PhysicalQuotient (facetRestrictionData (G := G) K n)) :=
  physicalQuotient_subsingleton_of_invariant_le_identity
    (facetRestrictionData (G := G) K n)
    (globalConePhysicalInvariantPaths_le_identity (G := G) K hcone n)

/-- Representative form of `T'(C_v M)=0`, transported through the concrete
Section 2 comparison equivalence. -/
theorem isConeAtTPrime_eq_zero
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (x : TPrime (facetRestrictionData (G := G) K n)) :
    x = 0 := by
  let E := physicalPrimitiveComparisonEquiv (G := G) K n
  have hx : E.symm x = 0 :=
    isConeAtPhysicalQuotient_eq_zero (G := G) K hcone n (E.symm x)
  exact E.symm.map_eq_zero_iff.mp hx

/-- Typeclass form of `T'(C_v M)=0`. -/
theorem isConeAtTPrime_subsingleton
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    Subsingleton (TPrime (facetRestrictionData (G := G) K n)) :=
  ⟨fun x y =>
    (isConeAtTPrime_eq_zero (G := G) K hcone n x).trans
      (isConeAtTPrime_eq_zero (G := G) K hcone n y).symm⟩

end GeneralSphereT.SimplicialCochain
