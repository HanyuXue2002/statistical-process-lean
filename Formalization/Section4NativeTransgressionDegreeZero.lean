import Formalization.Section4NativeTransgressionEquiv

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the degree-zero native transgression

This file supplies the low-degree endpoint omitted by the positive-degree
indexing of `Section4NativeTransgressionEquiv`.  In the notation of the
paper this is exactly `q = 1`: primitive cycles are built from zero-cochains
and the target is `F(G,1)`.

The apparent second hypothesis `H~⁻¹(M;G)=0` is automatic once a vertex of
`M` has been chosen.  At cochain level this says that the degree-one relative
cohomology of the outer double-cone pair vanishes.  We prove that statement
directly and then reuse the existing two-stage primitive extension.
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

local instance (priority := 10000) nativeTrZeroOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance
local instance (priority := 10000) nativeTrZeroOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance
local instance (priority := 10000) nativeTrZeroOptionLinearOrder :
    LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
local instance (priority := 10001) nativeTrZeroOptionOptionLE :
    LE (Option (Option V)) := @WithBot.instLE (Option V) inferInstance
local instance (priority := 10001) nativeTrZeroOptionOptionLT :
    LT (Option (Option V)) := @WithBot.instLT (Option V) inferInstance
local instance (priority := 10001) nativeTrZeroOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

/-- A zero-cocycle on a literal cone which vanishes at the apex is zero. -/
theorem cone_zeroCochain_eq_zero_of_cocycle_of_apex
    (M : AbstractSimplicialComplex V)
    (c : Cochain (simplicialCone M) 0 G)
    (hc : coboundary (simplicialCone M) 0 c = 0)
    (hapex : c (basepointSimplex (simplicialCone M) none) = 0) :
    c = 0 := by
  ext sigma
  have hcard : sigma.1.card = 1 := by simpa using sigma.2.2
  obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hcard
  cases o with
  | none =>
      have hsigma : sigma = basepointSimplex (simplicialCone M) none := by
        apply Subtype.ext
        simpa [basepointSimplex] using ho
      rw [hsigma, hapex]
      rfl
  | some v =>
      let P := pointedConePairInclusion M v
      let u : Cochain (pointedConePair M v) 0 G := P.pullback 0 c
      have huCycle : coboundary (pointedConePair M v) 0 u = 0 := by
        have hnat := LinearMap.congr_fun
          (P.pullback_coboundary (G := G) 0) c
        simp only [LinearMap.comp_apply] at hnat
        rw [← hnat, hc, map_zero]
      have hedge := congrArg
        (fun z : Cochain (pointedConePair M v) 1 G =>
          z (pointedConePairEdgeSimplex M v)) huCycle
      rw [coboundary_pointedConePair_edge_apply] at hedge
      have hsigma : sigma =
          (coneBottomInclusion M).mapSimplex (basepointSimplex M v) := by
        apply Subtype.ext
        simpa [basepointSimplex, OrderedSimplicialMap.mapSimplex] using ho
      have hbottom :
          u ((pointedConePairBottomInclusion M v).mapSimplex
              (basepointSimplex M v)) = c sigma := by
        rw [hsigma]
        rfl
      have hapex' :
          u (basepointSimplex (pointedConePair M v) none) =
            c (basepointSimplex (simplicialCone M) none) := by
        rfl
      rw [hbottom, hapex', hapex, sub_zero] at hedge
      exact hedge

/-- The missing `H~⁻¹` shift is automatic for a nonempty complex.
Equivalently, the outer double-cone pair has zero relative cohomology in
degree one.  The chosen vertex is used only to connect the two cone apices
through a bottom vertex. -/
theorem doubleConeBoundaryRelativeCohomologyZero_degreeZero
    (M : AbstractSimplicialComplex V) (b : V) :
    (doubleConeBoundaryInclusion M).RelativeCohomologyZeroAtSucc
      (G := G) 0 := by
  let F := doubleConeBoundaryInclusion M
  let E := coneBottomInclusion (simplicialCone M)
  let J := doubleConeOtherInclusion M
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact F.relativeCoboundary_relativeCoboundary (G := G) 0 x
  · intro gamma hgammaKer
    rw [LinearMap.mem_ker] at hgammaKer
    have hgammaCycle :
        coboundary (simplicialCone (simplicialCone M)) 1 gamma.1 = 0 :=
      congrArg Subtype.val hgammaKer
    let a : Cochain (simplicialCone (simplicialCone M)) 0 G :=
      simplicialConeCocyclePrimitive (simplicialCone M) 0 gamma.1
    have hda : coboundary (simplicialCone (simplicialCone M)) 0 a =
        gamma.1 :=
      coboundary_simplicialConeCocyclePrimitive
        (G := G) (simplicialCone M) 0 gamma.1 hgammaCycle
    have hother : J.pullback 0 a = 0 := by
      exact doubleConeOther_pullback_outerPrimitive_eq_zero
        (G := G) M 0 gamma
    let c : Cochain (simplicialCone M) 0 G := E.pullback 0 a
    have hcCycle : coboundary (simplicialCone M) 0 c = 0 := by
      have hnat := LinearMap.congr_fun
        (E.pullback_coboundary (G := G) 0) a
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hda,
        doubleConeInner_pullback_relativeCochain_eq_zero
          (G := G) M 1 gamma]
    have hbottom :
        c ((coneBottomInclusion M).mapSimplex (basepointSimplex M b)) = 0 := by
      have hv := congrArg
        (fun z : Cochain (simplicialCone M) 0 G =>
          z ((coneBottomInclusion M).mapSimplex (basepointSimplex M b)))
        hother
      change a (J.mapSimplex
          ((coneBottomInclusion M).mapSimplex (basepointSimplex M b))) = 0 at hv
      change a (E.mapSimplex
          ((coneBottomInclusion M).mapSimplex (basepointSimplex M b))) = 0
      have heq : E.mapSimplex
            ((coneBottomInclusion M).mapSimplex (basepointSimplex M b)) =
          J.mapSimplex
            ((coneBottomInclusion M).mapSimplex (basepointSimplex M b)) := by
        change
          (coneBottomInclusion (simplicialCone M)).mapSimplex
                ((coneBottomInclusion M).mapSimplex
                  (basepointSimplex M b)) =
            (doubleConeOtherInclusion M).mapSimplex
                ((coneBottomInclusion M).mapSimplex
                  (basepointSimplex M b))
        calc
          _ = F.mapSimplex
                ((doubleConeInnerBoundaryInclusion M).mapSimplex
                  ((coneBottomInclusion M).mapSimplex
                    (basepointSimplex M b))) := by
              rw [← doubleConeInnerInclusion_eq M]
              exact OrderedSimplicialMap.mapSimplex_comp F
                (doubleConeInnerBoundaryInclusion M)
                ((coneBottomInclusion M).mapSimplex
                  (basepointSimplex M b))
          _ = F.mapSimplex
                ((doubleConeOtherBoundaryInclusion M).mapSimplex
                  ((coneBottomInclusion M).mapSimplex
                    (basepointSimplex M b))) := by
              exact congrArg F.mapSimplex
                (doubleConeFaces_mapSimplex_bottom_eq M 0
                  (basepointSimplex M b))
          _ = _ := by
              exact (OrderedSimplicialMap.mapSimplex_comp F
                (doubleConeOtherBoundaryInclusion M)
                ((coneBottomInclusion M).mapSimplex
                  (basepointSimplex M b))).symm
      rw [heq]
      exact hv
    let apex := basepointSimplex (simplicialCone M) none
    let cNorm : Cochain (simplicialCone M) 0 G :=
      c - constantCochain (simplicialCone M) (c apex)
    have hcNormCycle : coboundary (simplicialCone M) 0 cNorm = 0 := by
      simpa [cNorm] using hcCycle
    have hcNormApex : cNorm apex = 0 := by
      simp [cNorm]
    have hcNormZero : cNorm = 0 :=
      cone_zeroCochain_eq_zero_of_cocycle_of_apex
        (G := G) M cNorm hcNormCycle hcNormApex
    have hapex : c apex = 0 := by
      have hv := congrArg
        (fun z : Cochain (simplicialCone M) 0 G =>
          z ((coneBottomInclusion M).mapSimplex (basepointSimplex M b)))
        hcNormZero
      change c ((coneBottomInclusion M).mapSimplex
          (basepointSimplex M b)) - c apex = 0 at hv
      rw [hbottom, zero_sub] at hv
      exact neg_eq_zero.mp hv
    have hcZero : c = 0 :=
      cone_zeroCochain_eq_zero_of_cocycle_of_apex
        (G := G) M c hcCycle hapex
    have hboundary : F.pullback 0 a = 0 := by
      exact doubleConeBoundary_pullback_eq_zero_of_two_faces
        (G := G) M 0 a hcZero hother
    have haZero : a = 0 := by
      ext sigma
      have hcard : sigma.1.card = 1 := by simpa using sigma.2.2
      obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hcard
      let tau : Simplex (doubleConeBoundary M) 0 :=
        ⟨sigma.1, by
          rw [ho]
          exact (doubleConeBoundary M).singleton_mem o,
          sigma.2.2⟩
      have hv := congrArg
        (fun z : Cochain (doubleConeBoundary M) 0 G => z tau) hboundary
      change a (F.mapSimplex tau) = 0 at hv
      have hmap : F.mapSimplex tau = sigma := by
        apply Subtype.ext
        ext o
        simp [F, doubleConeBoundaryInclusion,
          OrderedSimplicialMap.mapSimplex]
        change o ∈ sigma.1 ↔ o ∈ sigma.1
        rfl
      rw [hmap] at hv
      exact hv
    have hgammaZero : gamma = 0 := by
      apply Subtype.ext
      rw [← hda, haZero, map_zero]
      rfl
    subst gamma
    exact ⟨0, by simp⟩

/-- The second fibrewise lift needed by the double-cone construction in
degree zero.  Unlike the positive-degree construction, it needs no reduced
cohomology hypothesis: the preceding theorem is the missing automatic
`H~⁻¹` statement. -/
def doubleConeBoundaryFiberwiseCochainLiftDegreeZero
    (M : AbstractSimplicialComplex V) (b : V) :=
  (doubleConeBoundaryInclusion M).fiberwiseCochainLiftOfRelativeCohomology
    0 (doubleConeBoundaryRelativeCohomologyZero_degreeZero
      (G := G) M b)

/-- Degree-zero relative uniqueness.  Only `H~⁰(M;G)=0` is needed: it
constructs the first cone extension, while the second extension is supplied
by the automatic degree-zero double-cone theorem above. -/
theorem bottomZeroRprimNativeRelative_class_eq_zero_degreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (r : Rprim (d := coboundaryToRange (G := G)
      (simplicialCone M) 0))
    (hr : coneBottomRprimRestriction (G := G) M 0 r = 0) :
    (bottomZeroRprimNativeRelativeMap M 0 r hr).homotopyClass = 0 :=
  bottomZeroRprimNativeRelative_class_eq_zero M 0
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b 0 hred)
    (doubleConeBoundaryFiberwiseCochainLiftDegreeZero
      (G := G) M b)
    r hr

/-- In degree zero every algebraic bottom-zero primitive relation is an
actual native relative nullhomotopy. -/
theorem coneRelativeNullMaps_le_nativeStrictNull_degreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    ConeRelativeNullMaps (G := G) M 0 ≤
      (StrictNullMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) 1)).comap
          (coneRelativeSectionToNativeStrict (G := G) M 0) := by
  rintro x ⟨r, rfl⟩
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  let hr : coneBottomRprimRestriction (G := G) M 0 r.1 = 0 := r.2
  let f := bottomZeroRprimNativeRelativeMap M 0 r.1 hr
  have hmap :
      RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
          (F (AddCommGrpCat.of G) 1)
          (coneRelativeSectionToNativeStrict (G := G) M 0
            (coneRelativeRestriction (G := G) M 0 r)) = f := by
    apply SSet.RelativeMorphism.ext
    change strictFSectionToNativeFiberMap (simplicialCone M) 0
        (restrictionClass
          (facetRestrictionData (G := G) (simplicialCone M) 0) r.1) =
      rprimToNativeFiberMap (simplicialCone M) 0 r.1
    exact strictFSectionToNativeFiberMap_restrictionClass_transgression
      (G := G) (simplicialCone M) 0 r.1
  change
    (RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) 1)
      (coneRelativeSectionToNativeStrict (G := G) M 0
        (coneRelativeRestriction (G := G) M 0 r))).homotopyClass = 0
  rw [hmap]
  exact bottomZeroRprimNativeRelative_class_eq_zero_degreeZero
    (G := G) M b hred r.1 hr

/-- In degree zero the algebraic cone-relative null subgroup is exactly the
subgroup of genuinely nullhomotopic native relative maps. -/
theorem coneRelativeNullMaps_eq_nativeStrictNull_comap_degreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    ConeRelativeNullMaps (G := G) M 0 =
      (StrictNullMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) 1)).comap
          (coneRelativeSectionToNativeStrict (G := G) M 0) := by
  apply le_antisymm
  · exact coneRelativeNullMaps_le_nativeStrictNull_degreeZero
      (G := G) M b hred
  · exact nativeStrictNull_le_coneRelativeNullMaps
      (G := G) M b 0

theorem coneRelativeNativeClass_ker_eq_degreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    LinearMap.ker (coneRelativeNativeClass (G := G) M 0) =
      ConeRelativeNullMaps (G := G) M 0 := by
  rw [coneRelativeNullMaps_eq_nativeStrictNull_comap_degreeZero
    (G := G) M b hred]
  rfl

/-- Degree-zero cone-relative quotient as the genuine native relative
homotopy-class group. -/
def coneRelativeQuotientLinearEquivNativeClassDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    (ConeRelativeSections (G := G) M 0 ⧸
      ConeRelativeNullMaps (G := G) M 0) ≃ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) 1) :=
  (Submodule.quotEquivOfEq
      (ConeRelativeNullMaps (G := G) M 0)
      (LinearMap.ker (coneRelativeNativeClass (G := G) M 0))
      (coneRelativeNativeClass_ker_eq_degreeZero
        (G := G) M b hred).symm).trans
    ((coneRelativeNativeClass (G := G) M 0).quotKerEquivOfSurjective
      (coneRelativeNativeClass_surjective (G := G) M 0))

@[simp]
theorem coneRelativeQuotientLinearEquivNativeClassDegreeZero_mkQ
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (x : ConeRelativeSections (G := G) M 0) :
    coneRelativeQuotientLinearEquivNativeClassDegreeZero
        (G := G) M b hred
        ((ConeRelativeNullMaps (G := G) M 0).mkQ x) =
      coneRelativeNativeClass (G := G) M 0 x := by
  simp [coneRelativeQuotientLinearEquivNativeClassDegreeZero]

/-! ## Killing primitive boundaries in degree zero -/

/-- The chosen cycle extension and the canonical denominator extension
differ by a genuinely null native relative map in degree zero. -/
theorem denominatorExtensionDifferenceRelative_class_eq_zero_degreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M 0)) :
    (denominatorExtensionDifferenceRelativeMap M 0 E Q R).homotopyClass =
      0 := by
  change (bottomZeroRprimNativeRelativeMap M 0
      (denominatorExtensionDifference M 0 E Q R) _).homotopyClass = 0
  exact bottomZeroRprimNativeRelative_class_eq_zero_degreeZero
    (G := G) M b hred
    (denominatorExtensionDifference M 0 E Q R)
    (coneBottom_denominatorExtensionDifference_eq_zero M 0 E Q R)

/-- Every explicit primitive relation-path boundary is killed by the
degree-zero native extension class. -/
theorem nativeExtensionClass_relationPathBoundary_eq_zero_degreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap)
    (R : relationPaths (facetRestrictionData (G := G) M 0)) :
    E.nativeExtensionClass (M := M) (q := 0)
        (relationPathBoundaryCycle M 0 R) = 0 := by
  rw [nativeExtensionClass_relationPathBoundary_eq_difference]
  exact denominatorExtensionDifferenceRelative_class_eq_zero_degreeZero
    (G := G) M b hred E Q R

theorem BprimInZprim_le_ker_nativeExtensionClass_degreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap) :
    BprimInZprim (facetRestrictionData (G := G) M 0) ≤
      LinearMap.ker (E.nativeExtensionClass (M := M) (q := 0)) := by
  intro z hz
  rw [LinearMap.mem_ker]
  change (z : RedDist (Cochain M 0 G)) ∈
      Bprim (facetRestrictionData (G := G) M 0) at hz
  rcases hz with ⟨R, hR, hboundary⟩
  let R' : relationPaths (facetRestrictionData (G := G) M 0) := ⟨R, hR⟩
  have hzEq : z = relationPathBoundaryCycle M 0 R' := by
    apply Subtype.ext
    exact hboundary.symm
  rw [hzEq]
  exact nativeExtensionClass_relationPathBoundary_eq_zero_degreeZero
    (G := G) M b hred E Q R'

/-- The degree-zero native transgression as a quotient-descended linear
map. -/
def nativeTransgressionDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap) :
    TPrime (facetRestrictionData (G := G) M 0) →ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) 1) :=
  (BprimInZprim (facetRestrictionData (G := G) M 0)).liftQ
    (E.nativeExtensionClass (M := M) (q := 0))
    (BprimInZprim_le_ker_nativeExtensionClass_degreeZero
      (G := G) M b hred E Q)

@[simp]
theorem nativeTransgressionDegreeZero_mkQ
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap)
    (z : Zprim (facetRestrictionData (G := G) M 0)) :
    nativeTransgressionDegreeZero (G := G) M b hred E Q
        ((BprimInZprim (facetRestrictionData (G := G) M 0)).mkQ z) =
      E.nativeExtensionClass (M := M) (q := 0) z :=
  rfl

/-! ## The degree-zero transgression equivalence -/

/-- Boundary-null datum for the algebraic transgression presentation in
degree zero. -/
def ConeCycleExtensionData.nativeConeBoundaryNullDataDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap) :
    ConeCycleExtensionData.ConeBoundaryNullData (G := G) M 0 E where
  boundaries_null := by
    intro z hz
    rw [LinearMap.mem_ker]
    let e := coneRelativeQuotientLinearEquivNativeClassDegreeZero
      (G := G) M b hred
    apply e.injective
    change e ((ConeRelativeNullMaps (G := G) M 0).mkQ
        (E.extensionSection (X := M) (n := 0) z)) = e 0
    calc
      _ = coneRelativeNativeClass (G := G) M 0
            (E.extensionSection (X := M) (n := 0) z) :=
        coneRelativeQuotientLinearEquivNativeClassDegreeZero_mkQ
          (G := G) M b hred _
      _ = E.nativeExtensionClass (M := M) (q := 0) z :=
        (E.nativeExtensionClass_eq_coneRelativeNativeClass M 0 z).symm
      _ = 0 := LinearMap.mem_ker.mp
        (BprimInZprim_le_ker_nativeExtensionClass_degreeZero
          (G := G) M b hred E Q hz)
      _ = e 0 := (map_zero e).symm

/-- The native transgression equivalence for the paper's endpoint `q=1`.
This version displays the cycle-extension choices; the canonical public
version below constructs them from `hred`. -/
def nativeTransgressionLinearEquivDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap) :
    TPrime (facetRestrictionData (G := G) M 0) ≃ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) 1) :=
  (ConeCycleExtensionData.nativeConeBoundaryNullDataDegreeZero
      (G := G) M b hred E Q).transgressionEquiv.trans
    (coneRelativeQuotientLinearEquivNativeClassDegreeZero
      (G := G) M b hred)

/-- Representative formula for the degree-zero native transgression. -/
@[simp]
theorem nativeTransgressionLinearEquivDegreeZero_mkQ
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap)
    (z : Zprim (facetRestrictionData (G := G) M 0)) :
    nativeTransgressionLinearEquivDegreeZero
        (G := G) M b hred E Q
        ((BprimInZprim (facetRestrictionData (G := G) M 0)).mkQ z) =
      E.nativeExtensionClass (M := M) (q := 0) z := by
  rw [nativeTransgressionLinearEquivDegreeZero, LinearEquiv.trans_apply,
    ConeCycleExtensionData.ConeBoundaryNullData.transgressionEquiv_mkQ]
  change coneRelativeQuotientLinearEquivNativeClassDegreeZero
      (G := G) M b hred
      ((ConeRelativeNullMaps (G := G) M 0).mkQ
        (E.extensionSection (X := M) (n := 0) z)) =
    E.nativeExtensionClass (M := M) (q := 0) z
  rw [coneRelativeQuotientLinearEquivNativeClassDegreeZero_mkQ,
    ← E.nativeExtensionClass_eq_coneRelativeNativeClass]

/-- The preceding equivalence has exactly the quotient-descended native
transgression as its underlying linear map. -/
theorem nativeTransgressionLinearEquivDegreeZero_toLinearMap
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (E : ConeCycleExtensionData (G := G) M 0)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M 0)
      (coboundaryToRange (G := G) (simplicialCone M) 0)
      (coneBottomFacetHom (G := G) M 0).primitiveMap) :
    (nativeTransgressionLinearEquivDegreeZero
      (G := G) M b hred E Q).toLinearMap =
        nativeTransgressionDegreeZero (G := G) M b hred E Q := by
  apply LinearMap.ext
  intro t
  obtain ⟨z, rfl⟩ :=
    (BprimInZprim
      (facetRestrictionData (G := G) M 0)).mkQ_surjective t
  change nativeTransgressionLinearEquivDegreeZero
      (G := G) M b hred E Q
      ((BprimInZprim (facetRestrictionData (G := G) M 0)).mkQ z) =
    nativeTransgressionDegreeZero (G := G) M b hred E Q
      ((BprimInZprim (facetRestrictionData (G := G) M 0)).mkQ z)
  rw [nativeTransgressionLinearEquivDegreeZero_mkQ,
    nativeTransgressionDegreeZero_mkQ]

/-- Canonical degree-zero native transgression map.  Both visible extension
choices are constructed from the single hypothesis `H~⁰(M;G)=0`. -/
def canonicalNativeTransgressionDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    TPrime (facetRestrictionData (G := G) M 0) →ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) 1) :=
  nativeTransgressionDegreeZero (G := G) M b hred
    (canonicalConeCycleExtensionDataOfReduced
      (G := G) M b 0 hred)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b 0 hred)

/-- Canonical public native transgression equivalence for the paper's
`q=1` case.  It exposes no auxiliary lift or extension choice. -/
def canonicalNativeTransgressionLinearEquivDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    TPrime (facetRestrictionData (G := G) M 0) ≃ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) 1) :=
  nativeTransgressionLinearEquivDegreeZero (G := G) M b hred
    (canonicalConeCycleExtensionDataOfReduced
      (G := G) M b 0 hred)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b 0 hred)

/-- Canonical degree-zero representative formula. -/
@[simp]
theorem canonicalNativeTransgressionLinearEquivDegreeZero_mkQ
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (z : Zprim (facetRestrictionData (G := G) M 0)) :
    canonicalNativeTransgressionLinearEquivDegreeZero
        (G := G) M b hred
        ((BprimInZprim (facetRestrictionData (G := G) M 0)).mkQ z) =
      (canonicalConeCycleExtensionDataOfReduced
        (G := G) M b 0 hred).nativeExtensionClass
          (M := M) (q := 0) z := by
  exact nativeTransgressionLinearEquivDegreeZero_mkQ
    (G := G) M b hred
    (canonicalConeCycleExtensionDataOfReduced
      (G := G) M b 0 hred)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b 0 hred) z

/-- The canonical equivalence has the canonical degree-zero native
transgression map as its underlying linear map. -/
theorem canonicalNativeTransgressionLinearEquivDegreeZero_toLinearMap
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    (canonicalNativeTransgressionLinearEquivDegreeZero
      (G := G) M b hred).toLinearMap =
        canonicalNativeTransgressionDegreeZero
          (G := G) M b hred := by
  exact nativeTransgressionLinearEquivDegreeZero_toLinearMap
    (G := G) M b hred
    (canonicalConeCycleExtensionDataOfReduced
      (G := G) M b 0 hred)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b 0 hred)

end GeneralSphereT.SimplicialCochain
