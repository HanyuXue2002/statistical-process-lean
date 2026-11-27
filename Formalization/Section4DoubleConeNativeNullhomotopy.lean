import Formalization.Section4DoubleConePrimitiveGluing
import Formalization.Section4LiteralConeHomotopyDescent

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: native nullhomotopy from the two relative extensions

This file assembles the two algebraic extensions on the literal double cone.
A bottom-zero primitive relation on `C_vM` is first made into `r ∪ 0` on
`C_vM ∪_M C_wM`, then extended over `C_wC_vM`.  Evaluating the resulting
outer relation gives a literal relative extension and hence an actual native
relative nullhomotopy.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetRestrictionHom
open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

local instance (priority := 10000) doubleNativeOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) doubleNativeOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) doubleNativeOptionLinearOrder :
    LinearOrder (Option V) := @WithBot.linearOrder V inferInstance

local instance (priority := 10001) doubleNativeOptionOptionLE :
    LE (Option (Option V)) := @WithBot.instLE (Option V) inferInstance

local instance (priority := 10001) doubleNativeOptionOptionLT :
    LT (Option (Option V)) := @WithBot.instLT (Option V) inferInstance

local instance (priority := 10001) doubleNativeOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

variable (M : AbstractSimplicialComplex V)

/-- The ambient inner-face inclusion is the literal bottom inclusion of the
outer cone. -/
theorem doubleConeInnerInclusion_eq :
    OrderedSimplicialMap.comp (doubleConeBoundaryInclusion M)
        (doubleConeInnerBoundaryInclusion M) =
      coneBottomInclusion (simplicialCone M) := by
  rfl

/-- Pulling the outer primitive extension to the inner cone recovers the
original primitive relation. -/
theorem inner_pullback_outerConePrimitiveExtension (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n)) :
    mapRedDist
        ((coneBottomInclusion (simplicialCone M)).pullback
          (G := G) n).toAddMonoidHom
        (outerConePrimitiveExtension M n Q S r).1 = r.1 := by
  have hpull := OrderedSimplicialMap.pullback_comp
    (G := G) (doubleConeBoundaryInclusion M)
      (doubleConeInnerBoundaryInclusion M) n
  rw [doubleConeInnerInclusion_eq M] at hpull
  have hpullAdd :
      ((coneBottomInclusion (simplicialCone M)).pullback
          (G := G) n).toAddMonoidHom =
        ((doubleConeInnerBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom.comp
        ((doubleConeBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom := by
    exact congrArg LinearMap.toAddMonoidHom hpull
  rw [hpullAdd, ← PathAlgebra.mapRedDist_comp_apply,
    boundary_pullback_outerConePrimitiveExtension,
    inner_pullback_primitiveRelationCupZero]

/-- Pulling the outer primitive extension to the other cone gives zero when
the original relation is zero on its bottom. -/
theorem other_pullback_outerConePrimitiveExtension_eq_zero (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hr : coneBottomRprimRestriction (G := G) M n r = 0) :
    mapRedDist
        ((doubleConeOtherInclusion M).pullback
          (G := G) n).toAddMonoidHom
        (outerConePrimitiveExtension M n Q S r).1 = 0 := by
  have hpull := OrderedSimplicialMap.pullback_comp
    (G := G) (doubleConeBoundaryInclusion M)
      (doubleConeOtherBoundaryInclusion M) n
  have hpullAdd :
      ((doubleConeOtherInclusion M).pullback
          (G := G) n).toAddMonoidHom =
        ((doubleConeOtherBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom.comp
        ((doubleConeBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom := by
    exact congrArg LinearMap.toAddMonoidHom hpull
  rw [hpullAdd, ← PathAlgebra.mapRedDist_comp_apply,
    boundary_pullback_outerConePrimitiveExtension,
    other_pullback_primitiveRelationCupZero_eq_zero M n Q r hr]

/-- The preceding inner-face identity, bundled in `Rprim`. -/
theorem mapRprim_inner_outerConePrimitiveExtension (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n)) :
    mapRprim
        ((coneBottomInclusion (simplicialCone M)).toFacetRestrictionHom
          (G := G) n)
        (outerConePrimitiveExtension M n Q S r) = r := by
  apply Subtype.ext
  exact inner_pullback_outerConePrimitiveExtension M n Q S r

/-- The other-face identity, bundled in `Rprim`. -/
theorem mapRprim_other_outerConePrimitiveExtension_eq_zero (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hr : coneBottomRprimRestriction (G := G) M n r = 0) :
    mapRprim
        ((doubleConeOtherInclusion M).toFacetRestrictionHom
          (G := G) n)
        (outerConePrimitiveExtension M n Q S r) = 0 := by
  apply Subtype.ext
  exact other_pullback_outerConePrimitiveExtension_eq_zero M n Q S r hr

/-- Native evaluation of the relation obtained after both extensions. -/
def outerConePrimitiveNativeMap (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n)) :
    orderedComplexSSet (simplicialCone (simplicialCone M)) ⟶
      underlyingSSet (F (AddCommGrpCat.of G) (n + 1)) :=
  rprimToNativeFiberMap (simplicialCone (simplicialCone M)) n
    (outerConePrimitiveExtension M n Q S r)

/-- On the bottom (inner) cone, the outer native map is exactly the map
represented by the original relation. -/
theorem outerConePrimitiveNativeMap_bottom (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n)) :
    literalConeBottomMap (simplicialCone M) ≫
        outerConePrimitiveNativeMap M n Q S r =
      rprimToNativeFiberMap (simplicialCone M) n r := by
  rw [outerConePrimitiveNativeMap, rprimToNativeFiberMap_pullback,
    mapRprim_inner_outerConePrimitiveExtension]

/-- On the other cone face the outer native map is strictly zero. -/
theorem outerConePrimitiveNativeMap_other_eq_zero (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hr : coneBottomRprimRestriction (G := G) M n r = 0) :
    (doubleConeOtherInclusion M).toSSetMap ≫
        outerConePrimitiveNativeMap M n Q S r = 0 := by
  rw [outerConePrimitiveNativeMap, rprimToNativeFiberMap_pullback,
    mapRprim_other_outerConePrimitiveExtension_eq_zero M n Q S r hr,
    map_zero]

/-! ## Literal-cone geometry -/

/-- Coning the bottom inclusion of `M ⊆ C_vM` gives exactly the other
literal cone face inside `C_wC_vM`. -/
theorem coneBottom_literalConeCylinderQuotient_naturality :
    (literalConeBottomMap M ▷ Δ[1]) ≫
        literalConeCylinderQuotient (simplicialCone M) =
      literalConeCylinderQuotient M ≫
        (doubleConeOtherInclusion M).toSSetMap := by
  ext Delta z
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  change
    (if SSet.stdSimplex.asOrderHom z.2 i = 0 then none
      else some (some (z.1.1 i))) =
    doubleConeOtherOrderEmbedding
      (if SSet.stdSimplex.asOrderHom z.2 i = 0 then none
        else some (z.1.1 i))
  by_cases hi : SSet.stdSimplex.asOrderHom z.2 i = 0
  · simp [hi]
  · simp [hi]

/-- The apex of the outer literal cone factors through the apex of its
other cone face. -/
theorem doubleConeOtherInclusion_const_apex :
    SSet.const
        (X := orderedComplexSSet (simplicialCone M))
        (literalConeApex M) ≫
        (doubleConeOtherInclusion M).toSSetMap =
      SSet.const (literalConeApex (simplicialCone M)) := by
  rw [SSet.const_comp]
  congr 1

/-- A map on the outer literal cone which is prescribed on the inner face
and zero on the other face is a genuine literal relative extension for the
pair `(C_vM,M)`. -/
def literalRelativeExtensionOfOtherConeZero
    (A : SimplicialObject AddCommGrpCat.{u})
    (f : NativeRelativeMorphism (literalConeBottomSubcomplex M) A)
    (g : orderedComplexSSet (simplicialCone (simplicialCone M)) ⟶
      underlyingSSet A)
    (hbottom : literalConeBottomMap (simplicialCone M) ≫ g = f.map)
    (hother : (doubleConeOtherInclusion M).toSSetMap ≫ g = 0) :
    LiteralRelativeExtension (simplicialCone M)
      (literalConeBottomSubcomplex M) A f where
  map := g
  bottom := hbottom
  apex := by
    calc
      SSet.const (literalConeApex (simplicialCone M)) ≫ g =
          (SSet.const
              (X := orderedComplexSSet (simplicialCone M))
              (literalConeApex M) ≫
            (doubleConeOtherInclusion M).toSSetMap) ≫ g := by
              rw [doubleConeOtherInclusion_const_apex]
      _ = SSet.const
              (X := orderedComplexSSet (simplicialCone M))
              (literalConeApex M) ≫
            ((doubleConeOtherInclusion M).toSSetMap ≫ g) :=
        Category.assoc _ _ _
      _ = SSet.const
              (X := orderedComplexSSet (simplicialCone M))
              (literalConeApex M) ≫ 0 := by rw [hother]
      _ = 0 := by ext Delta x; rfl
  rel := by
    rw [cylinder_zeroBoundary]
    ext Delta z
    rcases z.1.2 with ⟨y, hy⟩
    have hnatDelta := congr_app
      (coneBottom_literalConeCylinderQuotient_naturality M) Delta
    have hnatFun := ConcreteCategory.congr_hom hnatDelta
    have hnatPoint := hnatFun (y, z.2)
    change
      (literalConeCylinderQuotient (simplicialCone M)).app Delta
          ((literalConeBottomMap M).app Delta y, z.2) =
        (doubleConeOtherInclusion M).toSSetMap.app Delta
          ((literalConeCylinderQuotient M).app Delta (y, z.2))
      at hnatPoint
    have hzeroDelta := congr_app hother Delta
    have hzeroFun := ConcreteCategory.congr_hom hzeroDelta
    have hzeroPoint := hzeroFun
      ((literalConeCylinderQuotient M).app Delta (y, z.2))
    change g.app Delta
        ((doubleConeOtherInclusion M).toSSetMap.app Delta
          ((literalConeCylinderQuotient M).app Delta (y, z.2))) = 0
      at hzeroPoint
    rw [← hnatPoint] at hzeroPoint
    change g.app Delta
      ((literalConeCylinderQuotient (simplicialCone M)).app Delta
        (z.1.1, z.2)) = 0
    rw [← hy]
    exact hzeroPoint

/-! ## The actual native relative nullhomotopy -/

/-- The two primitive extensions assemble into a literal relative extension
of the map represented by a bottom-zero relation. -/
def bottomZeroRprimLiteralRelativeExtension (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hr : coneBottomRprimRestriction (G := G) M n r = 0) :
    LiteralRelativeExtension (simplicialCone M)
      (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (n + 1))
      (bottomZeroRprimNativeRelativeMap M n r hr) :=
  literalRelativeExtensionOfOtherConeZero M
    (F (AddCommGrpCat.of G) (n + 1))
    (bottomZeroRprimNativeRelativeMap M n r hr)
    (outerConePrimitiveNativeMap M n Q S r)
    (by
      exact outerConePrimitiveNativeMap_bottom M n Q S r)
    (outerConePrimitiveNativeMap_other_eq_zero M n Q S r hr)

/-- Actual native relative homotopy from zero to the map represented by a
bottom-zero primitive relation. -/
def bottomZeroRprimNativeRelativeNullhomotopy (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hr : coneBottomRprimRestriction (G := G) M n r = 0) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 1)))
      (bottomZeroRprimNativeRelativeMap M n r hr) :=
  (bottomZeroRprimLiteralRelativeExtension M n Q S r hr).toRelativeHomotopy

/-- Class-level relative uniqueness supplied by the explicit double-cone
construction. -/
theorem bottomZeroRprimNativeRelative_class_eq_zero (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hr : coneBottomRprimRestriction (G := G) M n r = 0) :
    (bottomZeroRprimNativeRelativeMap M n r hr).homotopyClass = 0 := by
  exact (bottomZeroRprimNativeRelativeNullhomotopy M n Q S r hr).eq.symm.trans
    (homotopyClass_zero (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (n + 1)))

/-- Canonical form of relative uniqueness under the two reduced-cohomology
vanishing hypotheses used in the manuscript. -/
theorem bottomZeroRprimNativeRelative_class_eq_zero_of_reduced
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (r : Rprim (d := coboundaryToRange (G := G)
      (simplicialCone M) (n + 1)))
    (hr : coneBottomRprimRestriction (G := G) M (n + 1) r = 0) :
    (bottomZeroRprimNativeRelativeMap M (n + 1) r hr).homotopyClass = 0 :=
  bottomZeroRprimNativeRelative_class_eq_zero M (n + 1)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b (n + 1) hhigh)
    (doubleConeBoundaryFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b n hlow)
    r hr

/-! ## Killing primitive boundaries -/

/-- The concrete difference between the chosen extension and the canonical
denominator extension is relatively null under the two cohomology
vanishing hypotheses. -/
theorem denominatorExtensionDifferenceRelative_class_eq_zero_of_reduced
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap)
    (R : relationPaths
      (facetRestrictionData (G := G) M (n + 1))) :
    (denominatorExtensionDifferenceRelativeMap M (n + 1) E Q R).homotopyClass =
      0 := by
  change (bottomZeroRprimNativeRelativeMap M (n + 1)
      (denominatorExtensionDifference M (n + 1) E Q R) _).homotopyClass = 0
  exact bottomZeroRprimNativeRelative_class_eq_zero_of_reduced
    M b n hhigh hlow
    (denominatorExtensionDifference M (n + 1) E Q R)
    (coneBottom_denominatorExtensionDifference_eq_zero
      M (n + 1) E Q R)

/-- Hence the chosen native extension-class map kills every explicit
primitive relation-path boundary. -/
theorem nativeExtensionClass_relationPathBoundary_eq_zero_of_reduced
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap)
    (R : relationPaths
      (facetRestrictionData (G := G) M (n + 1))) :
    E.nativeExtensionClass (M := M) (q := n + 1)
        (relationPathBoundaryCycle M (n + 1) R) = 0 := by
  rw [nativeExtensionClass_relationPathBoundary_eq_difference]
  exact denominatorExtensionDifferenceRelative_class_eq_zero_of_reduced
    M b n hhigh hlow E Q R

/-- The whole primitive-boundary submodule lies in the kernel of the chosen
native extension-class map. -/
theorem BprimInZprim_le_ker_nativeExtensionClass_of_reduced
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap) :
    BprimInZprim (facetRestrictionData (G := G) M (n + 1)) ≤
      LinearMap.ker
        (E.nativeExtensionClass (M := M) (q := n + 1)) := by
  intro z hz
  rw [LinearMap.mem_ker]
  change (z : RedDist (Cochain M (n + 1) G)) ∈
      Bprim (facetRestrictionData (G := G) M (n + 1)) at hz
  rcases hz with ⟨R, hR, hboundary⟩
  let R' : relationPaths
      (facetRestrictionData (G := G) M (n + 1)) := ⟨R, hR⟩
  have hzEq : z = relationPathBoundaryCycle M (n + 1) R' := by
    apply Subtype.ext
    exact hboundary.symm
  rw [hzEq]
  exact nativeExtensionClass_relationPathBoundary_eq_zero_of_reduced
    M b n hhigh hlow E Q R'

/-- The native extension-class map therefore descends from primitive cycles
to the actual quotient `T'`. -/
def nativeTransgressionOfReduced
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap) :
    TPrime (facetRestrictionData (G := G) M (n + 1)) →ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 2)) :=
  (BprimInZprim (facetRestrictionData (G := G) M (n + 1))).liftQ
    (E.nativeExtensionClass (M := M) (q := n + 1))
    (BprimInZprim_le_ker_nativeExtensionClass_of_reduced
      M b n hhigh hlow E Q)

@[simp]
theorem nativeTransgressionOfReduced_mkQ
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap)
    (z : Zprim (facetRestrictionData (G := G) M (n + 1))) :
    nativeTransgressionOfReduced M b n hhigh hlow E Q
        ((BprimInZprim
          (facetRestrictionData (G := G) M (n + 1))).mkQ z) =
      E.nativeExtensionClass (M := M) (q := n + 1) z :=
  rfl

/-- Canonical native transgression: the same cohomological lift is used to
choose the cycle extension and in the denominator comparison. -/
def canonicalNativeTransgressionOfReduced
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    TPrime (facetRestrictionData (G := G) M (n + 1)) →ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 2)) :=
  let Q := coneBottomFiberwiseCochainLiftOfReducedCohomology
    (G := G) M b (n + 1) hhigh
  nativeTransgressionOfReduced M b n hhigh hlow
    (ConeCycleExtensionData.ofFiberwiseCochainLift
      (X := M) (n := n + 1) Q)
    Q

end GeneralSphereT.SimplicialCochain
