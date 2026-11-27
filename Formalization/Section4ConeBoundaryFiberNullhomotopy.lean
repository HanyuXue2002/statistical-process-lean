import Formalization.Section4ConeBoundaryNativeNullhomotopy
import Formalization.Section4RelationBoundaryFiberNullhomotopy

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the cone denominator contracts in `F`

This is the fibre-valued strengthening of the denominator paragraph
(4.19)--(4.21).  It packages the extended relation boundary as a native
relative map to `F(G,q+1)`, proves its composite with the fibre inclusion is
the genuine simplexwise primitive boundary, and supplies its actual relative
cylinder nullhomotopy in `F`.
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

local instance (priority := 10000) coneBoundaryFiberOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) coneBoundaryFiberOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) coneBoundaryFiberOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- The primitive boundary of the extended denominator relation path,
regarded as an actual relative map into the categorical fibre. -/
def extendedDenominatorBoundaryFiberRelativeMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    NativeRelativeMorphism (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1)) :=
  relationBoundaryFiberRelativeMap (literalConeBottomSubcomplex M)
    (d (AddCommGrpCat.of G) (q + 1))
    (globalRelationPathRelativeMap (simplicialCone M) q
      (literalConeBottomSubcomplex M)
      (extendedDenominatorRelationPath M q Q R)
      (literalConeBottomSubcomplex_globalExtendedRelationPath_eq_zero
        M q Q R))

/-- After the fibre inclusion, the preceding map is exactly the genuine
simplexwise evaluation of the extended primitive boundary. -/
theorem extendedDenominatorBoundaryFiberRelativeMap_comp_inclusion
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    (extendedDenominatorBoundaryFiberRelativeMap M q Q R).map ≫
        underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)) =
      globalCochainRestrictionMap (simplicialCone M) q
        (primitiveBoundaryOfRelationPath
          (coboundaryToRange (G := G) (simplicialCone M) q)
          (extendedDenominatorRelationPath M q Q R)).1 := by
  rw [extendedDenominatorBoundaryFiberRelativeMap,
    relationBoundaryFiberRelativeMap_comp_inclusion,
    globalRelationPathRelativeMap_boundary_map]

/-- The actual relative cylinder nullhomotopy stays inside `F`. -/
def extendedDenominatorBoundaryFiberRelativeNullhomotopy
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1)))
      (extendedDenominatorBoundaryFiberRelativeMap M q Q R) :=
  standardRelationBoundaryFiberRelativeNullhomotopy
    (literalConeBottomSubcomplex M) (AddCommGrpCat.of G) q
    (globalRelationPathRelativeMap (simplicialCone M) q
      (literalConeBottomSubcomplex M)
      (extendedDenominatorRelationPath M q Q R)
      (literalConeBottomSubcomplex_globalExtendedRelationPath_eq_zero
        M q Q R))

/-- Class-level form of the fibre-valued denominator contraction. -/
theorem extendedDenominatorBoundaryFiberRelative_class_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    (extendedDenominatorBoundaryFiberRelativeMap M q Q R).homotopyClass = 0 := by
  exact (extendedDenominatorBoundaryFiberRelativeNullhomotopy M q Q R).eq.symm.trans
    (homotopyClass_zero (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1)))

end GeneralSphereT.SimplicialCochain
