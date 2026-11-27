import Formalization.Section4GlobalRprimFiberMap
import Formalization.Section4ConeBoundaryFiberNullhomotopy
import Formalization.Section4SimplicialTransgression

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the native cone transgression

This file starts the direct comparison with the actual relative simplicial
homotopy group.  A chosen primitive-cycle extension on the literal cone is
evaluated in the genuine fibre `F`; its defining restriction equation and
the local-zero condition on primitive cycles make the resulting map vanish
strictly on the bottom copy of the original complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetRestrictionHom
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

local instance (priority := 10000) nativeTransgressionOptionLE :
    LE (Option V) := @WithBot.instLE V inferInstance

local instance (priority := 10000) nativeTransgressionOptionLT :
    LT (Option V) := @WithBot.instLT V inferInstance

local instance (priority := 10000) nativeTransgressionOptionLinearOrder :
    LinearOrder (Option V) := @WithBot.linearOrder V inferInstance

private abbrev LData (M : AbstractSimplicialComplex V) (q : ℕ) :=
  facetRestrictionData (G := G) M q

namespace ConeCycleExtensionData

variable (M : AbstractSimplicialComplex V) (q : ℕ)
variable (E : ConeCycleExtensionData (G := G) M q)

/-- The fibre-valued map represented by an extended primitive cycle,
bundled with its strict vanishing on the bottom subcomplex. -/
def nativeExtensionStrictMap :
    Zprim (LData (G := G) M q) →ₗ[ℤ]
      RelativeZeroMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1)) where
  toFun z := by
    let f := rprimToNativeFiberMap (simplicialCone M) q (E.extendCycle z)
    refine ⟨f, AddMonoidHom.mem_ker.mpr ?_⟩
    change (literalConeBottomSubcomplex M).ι ≫ f = 0
    have hbottom :
        literalConeBottomMap M ≫ f = 0 := by
      dsimp only [f]
      rw [rprimToNativeFiberMap_pullback]
      have hext := LinearMap.congr_fun E.restrict_extend z
      have hext' : mapRprim
          ((coneBottomInclusion M).toFacetRestrictionHom (G := G) q)
          (E.extendCycle z) =
            zprimToRprim (LData (G := G) M q) z := by
        change coneBottomRprimRestriction (G := G) M q
            (E.extendCycle z) =
          zprimToRprim (facetRestrictionData (G := G) M q) z
        exact hext
      rw [hext']
      exact zprimToRprim_nativeFiberMap_eq_zero M q z
    rw [← cancel_epi
      (SSet.Subcomplex.toRange (literalConeBottomMap M)),
      ← Category.assoc, SSet.Subcomplex.toRange_ι]
    exact hbottom
  map_add' z w := by
    apply Subtype.ext
    change rprimToNativeFiberMap (simplicialCone M) q
        (E.extendCycle (z + w)) =
      rprimToNativeFiberMap (simplicialCone M) q (E.extendCycle z) +
        rprimToNativeFiberMap (simplicialCone M) q (E.extendCycle w)
    rw [map_add, map_add]
  map_smul' n z := by
    apply Subtype.ext
    change rprimToNativeFiberMap (simplicialCone M) q
        (E.extendCycle (n • z)) =
      n • rprimToNativeFiberMap (simplicialCone M) q (E.extendCycle z)
    rw [map_smul, map_smul]

/-- The strict fibre-valued relative map represented by an extended
primitive cycle.  This is the map-level representative in (4.18), before
passing to native relative homotopy classes. -/
def nativeExtensionRelativeMap :
    Zprim (LData (G := G) M q) →ₗ[ℤ]
      NativeRelativeMorphism (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1)) :=
  (relativeMorphismAddEquiv (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1))).toIntLinearEquiv.toLinearMap.comp
    (E.nativeExtensionStrictMap (M := M) (q := q))

@[simp]
theorem nativeExtensionRelativeMap_map
    (z : Zprim (LData (G := G) M q)) :
    (E.nativeExtensionRelativeMap (M := M) (q := q) z).map =
      rprimToNativeFiberMap (simplicialCone M) q (E.extendCycle z) :=
  rfl

/-- The representative vanishes strictly on the literal bottom, not merely
up to homotopy. -/
theorem nativeExtensionRelativeMap_bottom_eq_zero
    (z : Zprim (LData (G := G) M q)) :
    (literalConeBottomSubcomplex M).ι ≫
        (E.nativeExtensionRelativeMap (M := M) (q := q) z).map = 0 := by
  calc
    (literalConeBottomSubcomplex M).ι ≫
          (E.nativeExtensionRelativeMap (M := M) (q := q) z).map =
        zeroBoundary (literalConeBottomSubcomplex M)
            (F (AddCommGrpCat.of G) (q + 1)) ≫
          (zeroSubcomplex (F (AddCommGrpCat.of G) (q + 1))).ι :=
      (E.nativeExtensionRelativeMap (M := M) (q := q) z).comm
    _ = 0 := zeroBoundary_comp_inclusion
      (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1))

/-- After the fibre inclusion, the native representative is literally the
simplexwise restriction map of the chosen primitive relation extension. -/
theorem nativeExtensionRelativeMap_comp_inclusion
    (z : Zprim (LData (G := G) M q)) :
    (E.nativeExtensionRelativeMap (M := M) (q := q) z).map ≫
        underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)) =
      globalCochainRestrictionMap (simplicialCone M) q
        (E.extendCycle z : RedDist (Cochain (simplicialCone M) q G)) := by
  exact rprimToNativeFiberMap_comp_inclusion
    (simplicialCone M) q (E.extendCycle z)

/-- The native relative homotopy class of the chosen cone extension. -/
def nativeExtensionClass :
    Zprim (LData (G := G) M q) →ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1)) :=
  (homotopyClassLinear (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1))).comp
    (E.nativeExtensionRelativeMap (M := M) (q := q))

@[simp]
theorem nativeExtensionClass_apply
    (z : Zprim (LData (G := G) M q)) :
    E.nativeExtensionClass (M := M) (q := q) z =
      (E.nativeExtensionRelativeMap (M := M) (q := q) z).homotopyClass :=
  rfl

end ConeCycleExtensionData

/-! ## The explicit denominator representative -/

/-- The primitive cycle represented by the boundary of a denominator
relation path. -/
def relationPathBoundaryCycle
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : relationPaths (LData (G := G) M q)) :
    Zprim (LData (G := G) M q) :=
  ⟨primitiveReducedBoundary (Cochain M q G) R.1,
    Bprim_le_Zprim (LData (G := G) M q) ⟨R.1, R.2, rfl⟩⟩

@[simp]
theorem relationPathBoundaryCycle_coe
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : relationPaths (LData (G := G) M q)) :
    (relationPathBoundaryCycle M q R : RedDist (Cochain M q G)) =
      primitiveReducedBoundary (Cochain M q G) R.1 :=
  rfl

/-- The extended relation boundary really is an extension of the original
boundary cycle at the primitive-relation level. -/
theorem coneBottom_extendedDenominatorPrimitiveBoundary
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    coneBottomRprimRestriction (G := G) M q
        (primitiveBoundaryOfRelationPath
          (coboundaryToRange (G := G) (simplicialCone M) q)
          (extendedDenominatorRelationPath M q Q R)) =
      zprimToRprim (LData (G := G) M q)
        (relationPathBoundaryCycle M q R) := by
  apply Subtype.ext
  exact mapRedDist_res_extendedPrimitiveBoundary
    Q.zeroNormalized Q.zeroNormalized.lift
      Q.zeroNormalized_lift_zero Q.zeroNormalized_res_lift
        (relationPathKernel M q R)

/-- The fibre-valued boundary map used in (4.21) is exactly the native
evaluation of its extended primitive boundary. -/
theorem extendedDenominatorBoundaryFiberRelativeMap_eq_rprim
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    (extendedDenominatorBoundaryFiberRelativeMap M q Q R).map =
      rprimToNativeFiberMap (simplicialCone M) q
        (primitiveBoundaryOfRelationPath
          (coboundaryToRange (G := G) (simplicialCone M) q)
          (extendedDenominatorRelationPath M q Q R)) := by
  apply (cancel_mono
    (underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)))).1
  rw [extendedDenominatorBoundaryFiberRelativeMap_comp_inclusion,
    rprimToNativeFiberMap_comp_inclusion]

/-- Every denominator path therefore has a concrete primitive-relation
extension whose actual native relative class is zero.  This is the precise
output of (4.19)--(4.21), separated from the later relative-uniqueness step
which compares it with the globally chosen additive cycle extension. -/
theorem exists_native_null_extension_of_relationPath
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    ∃ r : Rprim
        (d := coboundaryToRange (G := G) (simplicialCone M) q),
      coneBottomRprimRestriction (G := G) M q r =
          zprimToRprim (LData (G := G) M q)
            (relationPathBoundaryCycle M q R) ∧
      (extendedDenominatorBoundaryFiberRelativeMap M q Q R).map =
          rprimToNativeFiberMap (simplicialCone M) q r ∧
      (extendedDenominatorBoundaryFiberRelativeMap M q Q R).homotopyClass = 0 := by
  refine ⟨primitiveBoundaryOfRelationPath
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (extendedDenominatorRelationPath M q Q R), ?_, ?_, ?_⟩
  · exact coneBottom_extendedDenominatorPrimitiveBoundary M q Q R
  · exact extendedDenominatorBoundaryFiberRelativeMap_eq_rprim M q Q R
  · exact extendedDenominatorBoundaryFiberRelative_class_eq_zero M q Q R

/-! ## Comparison with the chosen additive extension -/

/-- The extended denominator boundary, with its codomain presented in the
same `Rprim` type used by the chosen cycle extension. -/
def extendedDenominatorPrimitiveRelation
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    Rprim (d := coboundaryToRange (G := G) (simplicialCone M) q) :=
  primitiveBoundaryOfRelationPath
    (coboundaryToRange (G := G) (simplicialCone M) q)
    (extendedDenominatorRelationPath M q Q R)

/-- The difference between the globally chosen additive cycle extension and
the concrete relation-boundary extension used in (4.21). -/
def denominatorExtensionDifference
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (E : ConeCycleExtensionData (G := G) M q)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    Rprim (d := coboundaryToRange (G := G) (simplicialCone M) q) :=
  E.extendCycle (relationPathBoundaryCycle M q R) -
    extendedDenominatorPrimitiveRelation M q Q R

/-- Both terms extend the same primitive boundary, so their difference is
strictly zero after primitive restriction to the bottom. -/
theorem coneBottom_denominatorExtensionDifference_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (E : ConeCycleExtensionData (G := G) M q)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    coneBottomRprimRestriction (G := G) M q
      (denominatorExtensionDifference M q E Q R) = 0 := by
  rw [denominatorExtensionDifference, map_sub,
    extendedDenominatorPrimitiveRelation]
  rw [coneBottom_extendedDenominatorPrimitiveBoundary]
  have hext := LinearMap.congr_fun E.restrict_extend
    (relationPathBoundaryCycle M q R)
  rw [show coneBottomRprimRestriction (G := G) M q
          (E.extendCycle (relationPathBoundaryCycle M q R)) =
        zprimToRprim (LData (G := G) M q)
          (relationPathBoundaryCycle M q R) by
    simpa using hext]
  exact sub_self _

/-- Evaluate a primitive cone relation whose primitive bottom restriction is
zero as an actual native relative map. -/
def bottomZeroRprimNativeRelativeMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) (simplicialCone M) q))
    (hr : coneBottomRprimRestriction (G := G) M q r = 0) :
    NativeRelativeMorphism (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1)) := by
  let f := rprimToNativeFiberMap (simplicialCone M) q r
  refine
    { map := f
      comm := ?_ }
  rw [zeroBoundary_comp_inclusion]
  have hbottom : literalConeBottomMap M ≫ f = 0 := by
    dsimp only [f]
    rw [rprimToNativeFiberMap_pullback]
    have hr' : mapRprim
        ((coneBottomInclusion M).toFacetRestrictionHom (G := G) q) r = 0 := by
      change coneBottomRprimRestriction (G := G) M q r = 0
      exact hr
    rw [hr', map_zero]
  rw [← cancel_epi
    (SSet.Subcomplex.toRange (literalConeBottomMap M)),
    ← Category.assoc, SSet.Subcomplex.toRange_ι]
  exact hbottom

@[simp]
theorem bottomZeroRprimNativeRelativeMap_map
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) (simplicialCone M) q))
    (hr : coneBottomRprimRestriction (G := G) M q r = 0) :
    (bottomZeroRprimNativeRelativeMap M q r hr).map =
      rprimToNativeFiberMap (simplicialCone M) q r :=
  rfl

/-- Native relative map carried by the preceding difference relation. -/
def denominatorExtensionDifferenceRelativeMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (E : ConeCycleExtensionData (G := G) M q)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    NativeRelativeMorphism (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1)) :=
  bottomZeroRprimNativeRelativeMap M q
    (denominatorExtensionDifference M q E Q R)
    (coneBottom_denominatorExtensionDifference_eq_zero M q E Q R)

/-- At map level, chosen extension minus the canonical denominator extension
is exactly the bottom-zero difference relation. -/
theorem nativeExtensionRelativeMap_sub_denominator
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (E : ConeCycleExtensionData (G := G) M q)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    E.nativeExtensionRelativeMap (M := M) (q := q)
          (relationPathBoundaryCycle M q R) -
        extendedDenominatorBoundaryFiberRelativeMap M q Q R =
      denominatorExtensionDifferenceRelativeMap M q E Q R := by
  apply SSet.RelativeMorphism.ext
  change
    rprimToNativeFiberMap (simplicialCone M) q
          (E.extendCycle (relationPathBoundaryCycle M q R)) -
        (extendedDenominatorBoundaryFiberRelativeMap M q Q R).map =
      rprimToNativeFiberMap (simplicialCone M) q
        (denominatorExtensionDifference M q E Q R)
  rw [extendedDenominatorBoundaryFiberRelativeMap_eq_rprim]
  rw [denominatorExtensionDifference,
    extendedDenominatorPrimitiveRelation]
  exact (map_sub (rprimToNativeFiberMap (simplicialCone M) q)
    (E.extendCycle (relationPathBoundaryCycle M q R))
    (primitiveBoundaryOfRelationPath
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (extendedDenominatorRelationPath M q Q R))).symm

/-- Consequently the chosen boundary class is precisely the class of the
bottom-zero difference.  Relative uniqueness is now isolated to proving
that this last, concrete native relative map is nullhomotopic. -/
theorem nativeExtensionClass_relationPathBoundary_eq_difference
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (E : ConeCycleExtensionData (G := G) M q)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M q)
      (coboundaryToRange (G := G) (simplicialCone M) q)
      (coneBottomFacetHom (G := G) M q).primitiveMap)
    (R : relationPaths (LData (G := G) M q)) :
    E.nativeExtensionClass (M := M) (q := q)
        (relationPathBoundaryCycle M q R) =
      (denominatorExtensionDifferenceRelativeMap M q E Q R).homotopyClass := by
  have h := congrArg SSet.RelativeMorphism.homotopyClass
    (nativeExtensionRelativeMap_sub_denominator M q E Q R)
  rw [homotopyClass_sub,
    extendedDenominatorBoundaryFiberRelative_class_eq_zero, sub_zero] at h
  exact h

end GeneralSphereT.SimplicialCochain
