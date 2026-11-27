import Formalization.Section4PointedConePairExtension
import Formalization.Section4SimplicialTransgression

set_option linter.style.header false

/-!
# Section 4: public comparisons from the literal pointed cone pair

This file connects the concrete relative-cohomology construction on
`X ∪ C_v{b} ⊆ C_vX` directly to the two comparison maps of Section 4.
There is no longer a separate fibrewise-lift or edge-compatibility input:
both are constructed from the single relative `range d = ker d` hypothesis.

For the transgression, surjectivity and the inclusion of the kernel in the
primitive boundaries are already consequences of cone vanishing.  The only
additional datum retained by the final equivalence is the contraction of a
primitive relation boundary, i.e. the specific paragraph (4.21).
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)

/-- Proposition 4.3 in the literal finite simplicial model, obtained from
the relative-cohomology vanishing of the pointed cone pair. -/
def thetaFromPointedConePairRelativeCohomology
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :=
  (pointedConeFiberwiseLiftDataOfRelativeCohomology
    (G := G) M b n hrel).thetaFromFiberwiseCone

/-- The concrete equality (4.6) produced by the same single hypothesis. -/
theorem coneCriterionFromPointedConePairRelativeCohomology
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    LinearMap.range
        (simplicialBasepointRowData
          (G := G) M b n).basedRestriction =
      (pointedConeFiberwiseLiftDataOfRelativeCohomology
        (G := G) M b n hrel).toPointedConeRelationExtensionData.toConeCriterionData.coneNullMaps :=
  (pointedConeFiberwiseLiftDataOfRelativeCohomology
    (G := G) M b n hrel).range_basedRestriction_eq_coneNullMaps

/-- The cycle extension in (4.15), with all cochain choices supplied by the
literal pointed cone pair. -/
def coneCycleExtensionFromPointedConePairRelativeCohomology
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    ConeCycleExtensionData (G := G) M n :=
  (pointedConeFiberwiseLiftDataOfRelativeCohomology
    (G := G) M b n hrel).toConeCycleExtensionData

/-- The extension-class map obtained from the pointed cone pair is onto;
this is the surjectivity paragraph of Proposition 4.5. -/
theorem coneExtensionClass_surjective_of_relativeCohomology
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    Function.Surjective
      ((coneCycleExtensionFromPointedConePairRelativeCohomology
        (G := G) M b n hrel).canonicalExtensionClass
          (X := M) (n := n)) :=
  (coneCycleExtensionFromPointedConePairRelativeCohomology
    (G := G) M b n hrel).canonicalExtensionClass_surjective

/-- A relatively zero extension class is already a primitive boundary;
this is the injectivity paragraph, discharged by exactness and
`T'(C_vM)=0`. -/
theorem coneExtensionClass_kernel_le_boundary_of_relativeCohomology
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    LinearMap.ker
        ((coneCycleExtensionFromPointedConePairRelativeCohomology
          (G := G) M b n hrel).canonicalExtensionClass
            (X := M) (n := n)) ≤
      BprimInZprim (facetRestrictionData (G := G) M n) :=
  (coneCycleExtensionFromPointedConePairRelativeCohomology
    (G := G) M b n hrel).canonicalExtensionClass_kernel_le_boundary

/-- Proposition 4.5 after the literal relative-cohomology extension and the
boundary contraction (4.21) have both been supplied. -/
def transgressionFromPointedConePairRelativeCohomology
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n)
    (N : ConeCycleExtensionData.ConeBoundaryNullData (G := G) M n
      (coneCycleExtensionFromPointedConePairRelativeCohomology
        (G := G) M b n hrel)) :=
  N.transgressionEquiv

end GeneralSphereT.SimplicialCochain
