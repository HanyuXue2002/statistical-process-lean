import Formalization.Section4NativeConeCriterionReverse
import Formalization.Section4BasedStrictNativeEquiv
import Formalization.Section4NativeConeCriterionForward

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the native literal-cone criterion

The reverse inclusion starts with a native relative null map.  Homotopy
extension supplies a strict map on the literal `Option` cone.  The
strict-section/native-map equivalence turns this into a strict section on
the cone, and `tau(C_v M) = 0` makes the primitive-relation restriction map
onto.  Pulling a chosen cone relation back to the bottom gives the required
based primitive relation.

Together with the forward construction from a pointed cone relation
extension, this proves the final equality of the two submodules.
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

local instance (priority := 10000) nativeConeEqualityOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) nativeConeEqualityOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) nativeConeEqualityOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- On a primitive relation, the unconditional strict-section/native-map
comparison is the direct genuine fibre evaluation. -/
theorem strictFSectionToNativeFiberMap_restrictionClass
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) M q)) :
    strictFSectionToNativeFiberMap M q
        (restrictionClass (facetRestrictionData (G := G) M q) r) =
      rprimToNativeFiberMap M q r := by
  apply (cancel_mono
    (underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)))).1
  rw [rprimToNativeFiberMap_comp_inclusion]
  change MapsKilledByD.toFiberMap (orderedComplexSSet M)
      (AddCommGrpCat.of G) (q + 1)
        (fCompatibleToNativeKilled M q
          (strictFSectionsNativeInput (G := G) M q)
          (rprimToFCompatible
            (facetRestrictionData (G := G) M q) r)) ≫
      underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)) = _
  rw [MapsKilledByD.toFiberMap_comp_inclusion]
  rfl

/-- Since the literal simplicial cone has trivial `tau`, every strict
section on it is represented by a primitive relation. -/
theorem literalCone_restrictionClass_surjective
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Surjective
      (restrictionClass
        (facetRestrictionData (G := G) (simplicialCone M) q)) := by
  let LC := facetRestrictionData (G := G) (simplicialCone M) q
  let facetsC := fun σ : NonemptySimplex (simplicialCone M) ↦
    facesIn (simplicialCone M) q σ
  have hexact : Function.Exact (restrictionClass LC)
      (simplicialObstruction (G := G) (simplicialCone M) q) := by
    exact exact_restrictionClass_obstruction facetsC LC
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) (simplicialCone M) q)
  intro x
  apply (hexact x).mp
  exact @Subsingleton.elim _
    (literalSimplicialConeTau_subsingleton (G := G) M q)
    (simplicialObstruction (G := G) (simplicialCone M) q x) 0

/-- Reverse inclusion in the native cone criterion: every genuinely
pointed-nullhomotopic map is represented by a based primitive relation. -/
theorem nativeNullMaps_le_range_basedRprimToNativePointedMap
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ) :
    NativeNullMaps (orderedComplexBasepointSubcomplex M b)
        (F (AddCommGrpCat.of G) (q + 1)) ≤
      LinearMap.range (basedRprimToNativePointedMap M b q) := by
  intro f hf
  rcases nonempty_literalPointedExtension_of_mem_nativeNullMaps
    M b (F (AddCommGrpCat.of G) (q + 1)) f hf with ⟨E⟩
  let LC := facetRestrictionData (G := G) (simplicialCone M) q
  let eC := strictFSectionsLinearEquivNativeFiberMaps
    (G := G) (simplicialCone M) q
  let xC : StrictFSections LC := eC.symm E.map
  have hxCmap : strictFSectionToNativeFiberMap
      (simplicialCone M) q xC = E.map := by
    exact eC.apply_symm_apply E.map
  rcases literalCone_restrictionClass_surjective (G := G) M q xC with
    ⟨rC, hrC⟩
  have hrCmap : rprimToNativeFiberMap (simplicialCone M) q rC = E.map := by
    calc
      rprimToNativeFiberMap (simplicialCone M) q rC =
          strictFSectionToNativeFiberMap (simplicialCone M) q
            (restrictionClass LC rC) :=
        (strictFSectionToNativeFiberMap_restrictionClass
          (G := G) (simplicialCone M) q rC).symm
      _ = strictFSectionToNativeFiberMap (simplicialCone M) q xC := by
        rw [hrC]
      _ = E.map := hxCmap
  let rBottom : Rprim (d := coboundaryToRange (G := G) M q) :=
    mapRprim (coneBottomFacetHom (G := G) M q) rC
  have hrBottomMap : rprimToNativeFiberMap M q rBottom = f.map := by
    calc
      rprimToNativeFiberMap M q rBottom =
          literalConeBottomMap M ≫
            rprimToNativeFiberMap (simplicialCone M) q rC := by
        exact (rprimToNativeFiberMap_pullback
          (G := G) (coneBottomInclusion M) q rC).symm
      _ = literalConeBottomMap M ≫ E.map := by rw [hrCmap]
      _ = f.map := E.bottom
  have hrBottomBased :
      evalRprim (facetRestrictionData (G := G) M q)
          (basepointFacet M b) rBottom = 0 := by
    apply (rprimToNativeFiberMap_basepoint_eq_zero_iff
      M b q rBottom).1
    calc
      (orderedComplexBasepointSubcomplex M b).ι ≫
          rprimToNativeFiberMap M q rBottom =
        (orderedComplexBasepointSubcomplex M b).ι ≫ f.map := by
          rw [hrBottomMap]
      _ = zeroBoundary (orderedComplexBasepointSubcomplex M b)
            (F (AddCommGrpCat.of G) (q + 1)) ≫
          (zeroSubcomplex (F (AddCommGrpCat.of G) (q + 1))).ι := f.comm
      _ = 0 := zeroBoundary_comp_inclusion
        (orderedComplexBasepointSubcomplex M b)
        (F (AddCommGrpCat.of G) (q + 1))
  let r : LinearMap.ker
      (simplicialBasepointRowData (G := G) M b q).evalR :=
    ⟨rBottom, hrBottomBased⟩
  refine ⟨r, ?_⟩
  apply SSet.RelativeMorphism.ext
  exact hrBottomMap

/-- Final native form of the cone criterion. -/
theorem PointedConeRelationExtensionData.range_basedRprimToNativePointedMap_eq_null
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (E : PointedConeRelationExtensionData (G := G) M b q) :
    LinearMap.range (basedRprimToNativePointedMap M b q) =
      NativeNullMaps (orderedComplexBasepointSubcomplex M b)
        (F (AddCommGrpCat.of G) (q + 1)) := by
  apply le_antisymm
  · exact E.range_basedRprimToNativePointedMap_le_null M b q
  · exact nativeNullMaps_le_range_basedRprimToNativePointedMap
      (G := G) M b q

end GeneralSphereT.SimplicialCochain
