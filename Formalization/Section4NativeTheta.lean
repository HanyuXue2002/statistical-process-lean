import Formalization.Section4NativeBasedDegreeZeroRow
import Formalization.Section4NativeConeCriterionEquality
import Formalization.Section4PointedConePairCohomologyShift
import Formalization.Section4PointedConePairExtension

set_option linter.style.header false

/-!
# Section 4: the native degree-zero comparison

This file combines the actual pointed degree-zero row with the completed
literal-cone criterion.  Under the reduced-cohomology hypothesis of (4.10),
the primitive image is exactly the subgroup of genuinely pointed
nullhomotopic maps.  The resulting quotient is therefore Mathlib's native
relative homotopy-class group, giving Proposition 4.3 without an abstract
`NullMaps` parameter.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.Section4
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

private abbrev LData
    (M : AbstractSimplicialComplex V) (q : ℕ) :=
  facetRestrictionData (G := G) M q

private abbrev TauData
    (M : AbstractSimplicialComplex V) (q : ℕ) :=
  Tau (fun σ : NonemptySimplex M ↦ facesIn M q σ) (LData (G := G) M q)

/-- The pointed cone extension data canonically selected from the reduced
cohomology vanishing in (4.10). -/
def nativePointedConeRelationExtensionDataOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b q) :
    PointedConeRelationExtensionData (G := G) M b q :=
  (pointedConeFiberwiseLiftDataOfRelativeCohomology
    (G := G) M b q
    (pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b q hred)).toPointedConeRelationExtensionData

/-- Native form of (4.6) under exactly the reduced-cohomology hypothesis
used in the manuscript. -/
theorem range_basedRprimToNativePointedMap_eq_null_of_reduced
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b q) :
    LinearMap.range (basedRprimToNativePointedMap M b q) =
      NativeNullMaps (orderedComplexBasepointSubcomplex M b)
        (F (AddCommGrpCat.of G) (q + 1)) :=
  PointedConeRelationExtensionData.range_basedRprimToNativePointedMap_eq_null
    M b q (nativePointedConeRelationExtensionDataOfReduced M b q hred)

/-- Proposition 4.3, now literally valued in genuine pointed simplicial
homotopy classes. -/
def nativeThetaOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b q) :
    TauData (G := G) M q ≃ₗ[ℤ]
      NativePointedHomotopyClasses M b (AddCommGrpCat.of G) (q + 1) :=
  (nativeThetaQuotientPrimitiveImage (G := G) M b q).trans
    ((Submodule.quotEquivOfEq
      (LinearMap.range (basedRprimToNativePointedMap M b q))
      (NativeNullMaps (orderedComplexBasepointSubcomplex M b)
        (F (AddCommGrpCat.of G) (q + 1)))
      (range_basedRprimToNativePointedMap_eq_null_of_reduced
        M b q hred)).trans
      (nativePointedQuotientEquiv M b (AddCommGrpCat.of G) (q + 1)))

/-- Formula (4.14): the comparison sends the obstruction represented by a
pointed map to that map's genuine pointed homotopy class. -/
@[simp]
theorem nativeThetaOfReduced_obstruction
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b q)
    (f : NativePointedMaps M b (AddCommGrpCat.of G) (q + 1)) :
    nativeThetaOfReduced M b q hred
        (nativePointedObstruction (G := G) M b q f) =
      f.homotopyClass := by
  rw [nativeThetaOfReduced, LinearEquiv.trans_apply,
    nativeThetaQuotientPrimitiveImage_obstruction,
    LinearEquiv.trans_apply]
  change nativePointedQuotientEquiv M b (AddCommGrpCat.of G) (q + 1)
      ((NativeNullMaps (orderedComplexBasepointSubcomplex M b)
        (F (AddCommGrpCat.of G) (q + 1))).mkQ f) =
    f.homotopyClass
  exact nativePointedQuotientEquiv_mkQ
    M b (AddCommGrpCat.of G) (q + 1) f

end GeneralSphereT.SimplicialCochain
