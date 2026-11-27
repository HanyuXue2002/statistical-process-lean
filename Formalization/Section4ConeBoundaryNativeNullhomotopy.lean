import Formalization.Section4GlobalRelationPathLocalZero
import Formalization.Section4GlobalRelationBoundaryCompatibility
import Formalization.Section4SimplicialConeExtension
import Formalization.Section4LiteralConeNativeCriterion

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the denominator boundary contracts on the cone pair

This is the complete native form of the paragraph (4.19)--(4.21).  A
denominator relation path on `M` is extended fibrewise to the literal cone.
Its genuine simplexwise relation-path map is strictly zero on the bottom,
and the explicit contraction of the standard Dold--Kan disk therefore gives
an actual relative nullhomotopy of its primitive boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

local instance (priority := 10000) coneBoundaryOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) coneBoundaryOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) coneBoundaryOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- Extend a denominator relation path to the literal cone using the
zero-normalized fibrewise cochain lift. -/
def extendedDenominatorRelationPath
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    LinearMap.ker
      (mapDNormalizedPath
        (coboundaryToRange (G := G) (simplicialCone M) q)) :=
  extendedRelationPath Q.zeroNormalized Q.zeroNormalized.lift
    Q.zeroNormalized_lift_zero Q.zeroNormalized_res_lift
      (relationPathKernel M q R)

/-- Restricting the extended path back to the bottom recovers the original
denominator path as a normalized kernel element. -/
theorem pullback_extendedDenominatorRelationPath
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    pullbackGlobalRelationPath (coneBottomInclusion M) q
        (extendedDenominatorRelationPath M q Q R) =
      relationPathKernel M q R := by
  apply Subtype.ext
  apply Subtype.ext
  change mapPath
      (coneBottomFacetHom (G := G) M q).primitiveMap
      (coneBottomFacetHom (G := G) M q).primitiveMap
      (extendedDenominatorRelationPath M q Q R).1.1 = R.1
  exact mapPath_res_res_extendedRelationPath
    Q.zeroNormalized Q.zeroNormalized.lift
      Q.zeroNormalized_lift_zero Q.zeroNormalized_res_lift
        (relationPathKernel M q R)

/-- The genuine simplexwise extended relation path is strictly zero on the
whole bottom copy of `M`. -/
theorem bottom_globalExtendedRelationPath_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    literalConeBottomMap M ≫
        globalRelationPathRestrictionMap (simplicialCone M) q
          (extendedDenominatorRelationPath M q Q R) = 0 := by
  rw [globalRelationPathRestrictionMap_pullback,
    pullback_extendedDenominatorRelationPath,
    relationPath_globalRestriction_eq_zero]

/-- The bottom of the literal cone, as a source subcomplex of that cone. -/
abbrev literalConeBottomSubcomplex
    (M : AbstractSimplicialComplex V) :
    (orderedComplexSSet (simplicialCone M)).Subcomplex :=
  SSet.Subcomplex.range (literalConeBottomMap M)

/-- Vanishing after precomposition with the bottom map gives strict
vanishing on its range subcomplex. -/
theorem literalConeBottomSubcomplex_globalExtendedRelationPath_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    (literalConeBottomSubcomplex M).ι ≫
        globalRelationPathRestrictionMap (simplicialCone M) q
          (extendedDenominatorRelationPath M q Q R) = 0 := by
  rw [← cancel_epi (SSet.Subcomplex.toRange (literalConeBottomMap M)),
    ← Category.assoc, SSet.Subcomplex.toRange_ι,
    bottom_globalExtendedRelationPath_eq_zero]
  rfl

/-- The actual relative cylinder nullhomotopy of the primitive boundary of
the extended denominator path. -/
def extendedDenominatorBoundaryRelativeNullhomotopy
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism (literalConeBottomSubcomplex M)
        (reducedFree (L (AddCommGrpCat.of G) (q + 1))))
      (relationBoundaryRelativeMap (literalConeBottomSubcomplex M)
        (d (AddCommGrpCat.of G) (q + 1))
        (globalRelationPathRelativeMap (simplicialCone M) q
          (literalConeBottomSubcomplex M)
          (extendedDenominatorRelationPath M q Q R)
          (literalConeBottomSubcomplex_globalExtendedRelationPath_eq_zero
            M q Q R))) :=
  globalRelationBoundaryRelativeNullhomotopy
    (simplicialCone M) q (literalConeBottomSubcomplex M)
      (extendedDenominatorRelationPath M q Q R)
      (literalConeBottomSubcomplex_globalExtendedRelationPath_eq_zero
        M q Q R)

/-- Class-level conclusion of the denominator contraction. -/
theorem extendedDenominatorBoundaryRelative_class_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    (relationBoundaryRelativeMap (literalConeBottomSubcomplex M)
      (d (AddCommGrpCat.of G) (q + 1))
      (globalRelationPathRelativeMap (simplicialCone M) q
        (literalConeBottomSubcomplex M)
        (extendedDenominatorRelationPath M q Q R)
        (literalConeBottomSubcomplex_globalExtendedRelationPath_eq_zero
          M q Q R))).homotopyClass = 0 :=
  globalRelationBoundaryRelative_homotopyClass_eq_zero
    (simplicialCone M) q (literalConeBottomSubcomplex M)
      (extendedDenominatorRelationPath M q Q R)
      (literalConeBottomSubcomplex_globalExtendedRelationPath_eq_zero
        M q Q R)

end GeneralSphereT.SimplicialCochain
