import Formalization.Section4SimplicialConeComparison
import Formalization.Section4PointedFiberwiseExtension
import Formalization.Section4CocycleExtension
import Formalization.Section4CochainExtensionByZero

set_option linter.style.header false

/-!
# Section 4: from relative cochains to the pointed cone criterion

`Section4SimplicialConeComparison` reduces (4.6) to an additive section on
primitive relations which vanishes on the whole basepoint cone edge.  This
file constructs that section from the actual fibrewise cochain lift of
Lemma 4.2.

The only extra local condition says that restricting a selected lifted
cochain to `C_v{b}` depends only on its restriction to `{b}`.  This is the
precise cochain-level form of doing the relative extension along
`M ∪ C_v{b}`.  Once this condition is supplied, all free-group, pointedness,
restriction, cone-vanishing, and quotient arguments are proved in Lean.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V)

local instance section4ConeExtensionOptionLinearOrder : LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- A fibrewise cochain lift from the bottom into the literal cone, together
with the local factorization which makes its induced relation section vanish
on the basepoint edge. -/
structure PointedConeFiberwiseLiftData (b : V) (n : ℕ) where
  fiberwise : FiberwiseCochainLift
    (coboundaryToRange (G := G) M n)
    (coboundaryToRange (G := G) (simplicialCone M) n)
    (coneBottomFacetHom (G := G) M n).primitiveMap
  edgeLift :
    Configuration (facesIn M n (basepointFacet M b)) G →
      Configuration
        (facesIn (simplicialCone M) n (coneBasepointEdgeFacet M b)) G
  edge_compat : ∀ c,
    (facetRestrictionData (G := G) (simplicialCone M) n).primitiveRes
        (coneBasepointEdgeFacet M b) (fiberwise.lift c) =
      edgeLift
        ((facetRestrictionData (G := G) M n).primitiveRes
          (basepointFacet M b) c)

namespace PointedConeFiberwiseLiftData

variable {b : V} {n : ℕ}
variable (E : PointedConeFiberwiseLiftData (G := G) M b n)

/-- The relation section induced by the fibrewise cochain lift lands in the
edge-pointed primitive relations. -/
def extendPointedRelation :
    LinearMap.ker
        (simplicialBasepointRowData (G := G) M b n).evalR →ₗ[ℤ]
      ConePointedRelations (G := G) M b n :=
  LinearMap.codRestrict (ConePointedRelations (G := G) M b n)
    (E.fiberwise.relationSection.comp
      (LinearMap.ker
        (simplicialBasepointRowData (G := G) M b n).evalR).subtype)
    fun r => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change
        mapRedDist
          ((facetRestrictionData (G := G) (simplicialCone M) n).primitiveRes
            (coneBasepointEdgeFacet M b))
          (E.fiberwise.relationSection r.1).1 = 0
      apply E.fiberwise.mapRedDist_relationSection_local_eq_zero
        ((facetRestrictionData (G := G) M n).primitiveRes
          (basepointFacet M b))
        ((facetRestrictionData (G := G) (simplicialCone M) n).primitiveRes
          (coneBasepointEdgeFacet M b))
        E.edgeLift E.edge_compat r.1
      exact congrArg Subtype.val r.2

/-- Bottom restriction of the pointed relation extension is the original
based relation. -/
theorem restrict_extendPointedRelation :
    (coneBottomPointedRelationRestriction (G := G) M b n).comp
        E.extendPointedRelation = LinearMap.id := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  apply Subtype.ext
  change
    mapRedDist (coneBottomFacetHom (G := G) M n).primitiveMap
        (E.fiberwise.relationSection r.1).1 = r.1.1
  exact E.fiberwise.mapRedDist_relationSection r.1

/-- Lemma 4.2, with the relative basepoint edge included, supplies exactly
the remaining input of the concrete cone criterion. -/
def toPointedConeRelationExtensionData :
    PointedConeRelationExtensionData (G := G) M b n where
  extendRelation := E.extendPointedRelation
  restrict_extend := E.restrict_extendPointedRelation

/-- Concrete equation (4.6), now derived directly from the fibrewise
relative cochain lift. -/
theorem range_basedRestriction_eq_coneNullMaps :
    LinearMap.range
        (simplicialBasepointRowData
          (G := G) M b n).basedRestriction =
      E.toPointedConeRelationExtensionData.toConeCriterionData.coneNullMaps :=
  E.toPointedConeRelationExtensionData.range_basedRestriction_eq_coneNullMaps

/-- Proposition 4.3 in the literal finite simplicial model, with the
relative-cochain extension as its sole mathematical input. -/
def thetaFromFiberwiseCone :
    Tau (fun σ : NonemptySimplex M => facesIn M n σ)
        (facetRestrictionData (G := G) M n) ≃ₗ[ℤ]
      GeneralSphereT.Section4.PointedHomotopyClasses
        (LinearMap.ker
          (simplicialBasepointRowData (G := G) M b n).evalM)
        E.toPointedConeRelationExtensionData.toConeCriterionData.coneNullMaps :=
  E.toPointedConeRelationExtensionData.thetaFromPointedCone

end PointedConeFiberwiseLiftData

end GeneralSphereT.SimplicialCochain
