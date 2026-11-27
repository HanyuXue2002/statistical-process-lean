import Formalization.Section4PointedConePairCohomologyShift
import Formalization.Section4ConcreteComparisons

set_option linter.style.header false

/-!
# Section 4: public comparisons from reduced cohomology

This file removes the last relative-cohomology parameter from the public
degree-zero comparison.  The hypothesis is now exactly the range--kernel
form of `H̃^n(M;G)=0`; the pointed cone-pair exactness used internally is
constructed by `Section4PointedConePairCohomologyShift`.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)

/-- Proposition 4.3 directly from `H̃^n(M;G)=0`, with no separately
supplied relative-cohomology hypothesis. -/
def thetaFromReducedCohomology
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :=
  thetaFromPointedConePairRelativeCohomology (G := G) M b n
    (pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

/-- Equation (4.6) directly from reduced cohomology vanishing. -/
theorem coneCriterionFromReducedCohomology
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    LinearMap.range
        (simplicialBasepointRowData (G := G) M b n).basedRestriction =
      (pointedConeFiberwiseLiftDataOfRelativeCohomology
        (G := G) M b n
        (pointedConePairRelativeCohomologyZero_of_reduced
          (G := G) M b n hred)).toPointedConeRelationExtensionData.toConeCriterionData.coneNullMaps :=
  coneCriterionFromPointedConePairRelativeCohomology
    (G := G) M b n
    (pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

/-- The cycle extension in (4.15), now constructed directly from reduced
cohomology vanishing. -/
def coneCycleExtensionFromReducedCohomology
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    ConeCycleExtensionData (G := G) M n :=
  coneCycleExtensionFromPointedConePairRelativeCohomology
    (G := G) M b n
    (pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

/-- Surjectivity of the canonical extension-class map, with the relative
exactness input discharged by reduced cohomology. -/
theorem coneExtensionClass_surjective_of_reducedCohomology
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    Function.Surjective
      ((coneCycleExtensionFromReducedCohomology
        (G := G) M b n hred).canonicalExtensionClass
          (X := M) (n := n)) :=
  coneExtensionClass_surjective_of_relativeCohomology
    (G := G) M b n
    (pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

/-- Kernel control for the extension-class map, under the same reduced
cohomology hypothesis. -/
theorem coneExtensionClass_kernel_le_boundary_of_reducedCohomology
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    LinearMap.ker
        ((coneCycleExtensionFromReducedCohomology
          (G := G) M b n hred).canonicalExtensionClass
            (X := M) (n := n)) ≤
      BprimInZprim (facetRestrictionData (G := G) M n) :=
  coneExtensionClass_kernel_le_boundary_of_relativeCohomology
    (G := G) M b n
    (pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

/-- Proposition 4.5 once the independent boundary contraction (4.21) is
provided; its cohomological extension input no longer appears separately. -/
def transgressionFromReducedCohomology
    (hred : ReducedCohomologyZeroAt (G := G) M b n)
    (N : ConeCycleExtensionData.ConeBoundaryNullData (G := G) M n
      (coneCycleExtensionFromReducedCohomology
        (G := G) M b n hred)) :=
  N.transgressionEquiv

end GeneralSphereT.SimplicialCochain
