import Formalization.Section4DoubleConeNativeNullhomotopy
import Formalization.Section4LiteralRelativeConeCriterionReverse
import Formalization.Section4BasedStrictNativeEquiv

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the native transgression equivalence

This file identifies the algebraic cone-relative quotient used in the
formal transgression proof with the actual native relative homotopy-class
group.  It then packages the native transgression as a linear equivalence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

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

local instance (priority := 10000) nativeTrEquivOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance
local instance (priority := 10000) nativeTrEquivOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance
local instance (priority := 10000) nativeTrEquivOptionLinearOrder :
    LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
local instance (priority := 10001) nativeTrEquivOptionOptionLE :
    LE (Option (Option V)) := @WithBot.instLE (Option V) inferInstance
local instance (priority := 10001) nativeTrEquivOptionOptionLT :
    LT (Option (Option V)) := @WithBot.instLT (Option V) inferInstance
local instance (priority := 10001) nativeTrEquivOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

private abbrev LData (M : AbstractSimplicialComplex V) (q : ℕ) :=
  facetRestrictionData (G := G) M q

/-! ## Naturality of the strict-section/native-map equivalence -/

theorem strictFSectionToNativeFiberMap_naturality
    {W : Type u} [LinearOrder W] [Fintype W]
    {K : AbstractSimplicialComplex W}
    {M : AbstractSimplicialComplex V}
    (S : OrderedSimplicialMap K M) (q : ℕ)
    (x : StrictFSections (LData (G := G) M q)) :
    S.toSSetMap ≫ strictFSectionToNativeFiberMap M q x =
      strictFSectionToNativeFiberMap K q
        (mapStrictFSections (S.toFacetRestrictionHom (G := G) q) x) := by
  refine Submodule.Quotient.induction_on
    (p := locallyZeroInFCompatible (LData (G := G) M q)) x ?_
  intro a
  change S.toSSetMap ≫ strictFSectionToNativeFiberMap M q
        ((locallyZeroInFCompatible (LData (G := G) M q)).mkQ a) =
    strictFSectionToNativeFiberMap K q
      (mapStrictFSections (S.toFacetRestrictionHom (G := G) q)
        ((locallyZeroInFCompatible (LData (G := G) M q)).mkQ a))
  rw [mapStrictFSections_mkQ]
  apply (cancel_mono
    (underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)))).1
  change
    S.toSSetMap ≫
          MapsKilledByD.toFiberMap (orderedComplexSSet M)
            (AddCommGrpCat.of G) (q + 1)
            (fCompatibleToNativeKilled M q
              (strictFSectionsNativeInput (G := G) M q) a) ≫
          underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)) =
      MapsKilledByD.toFiberMap (orderedComplexSSet K)
          (AddCommGrpCat.of G) (q + 1)
          (fCompatibleToNativeKilled K q
            (strictFSectionsNativeInput (G := G) K q)
            (mapFCompatible (S.toFacetRestrictionHom (G := G) q) a)) ≫
        underlyingMap (Fι (AddCommGrpCat.of G) (q + 1))
  rw [MapsKilledByD.toFiberMap_comp_inclusion,
    MapsKilledByD.toFiberMap_comp_inclusion]
  change S.toSSetMap ≫ globalCochainRestrictionMap M q
      (a : RedDist (Cochain M q G)) =
    globalCochainRestrictionMap K q
      (mapRedDist (S.pullback (G := G) q).toAddMonoidHom
        (a : RedDist (Cochain M q G)))
  exact globalCochainRestrictionMap_pullback S q
    (a : RedDist (Cochain M q G))

theorem strictFSectionToNativeFiberMap_restrictionClass_transgression
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) M q)) :
    strictFSectionToNativeFiberMap M q
        (restrictionClass (LData (G := G) M q) r) =
      rprimToNativeFiberMap M q r := by
  rw [restrictionClass_apply]
  apply (cancel_mono
    (underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)))).1
  change
    MapsKilledByD.toFiberMap (orderedComplexSSet M)
          (AddCommGrpCat.of G) (q + 1)
          (fCompatibleToNativeKilled M q
            (strictFSectionsNativeInput (G := G) M q)
            (rprimToFCompatible (LData (G := G) M q) r)) ≫
        underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)) =
      rprimToNativeFiberMap M q r ≫
        underlyingMap (Fι (AddCommGrpCat.of G) (q + 1))
  rw [MapsKilledByD.toFiberMap_comp_inclusion,
    rprimToNativeFiberMap_comp_inclusion]
  rfl

/-! ## Strict relative sections versus actual native relative maps -/

def coneRelativeSectionToNativeStrict
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    ConeRelativeSections (G := G) M q →ₗ[ℤ]
      RelativeZeroMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1)) where
  toFun x := by
    refine ⟨strictFSectionToNativeFiberMap (simplicialCone M) q x.1, ?_⟩
    rw [AddMonoidHom.mem_ker]
    change (literalConeBottomSubcomplex M).ι ≫
        strictFSectionToNativeFiberMap (simplicialCone M) q x.1 = 0
    rw [← cancel_epi
      (SSet.Subcomplex.toRange (literalConeBottomMap M)),
      ← Category.assoc, SSet.Subcomplex.toRange_ι]
    rw [strictFSectionToNativeFiberMap_naturality
      (coneBottomInclusion M) q x.1]
    change strictFSectionToNativeFiberMap M q
      (coneBottomStrictFSectionsRestriction (G := G) M q x.1) = 0
    rw [x.2, map_zero]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (strictFSectionToNativeFiberMap (simplicialCone M) q)
      x.1 y.1
  map_smul' n x := by
    apply Subtype.ext
    exact map_smul (strictFSectionToNativeFiberMap (simplicialCone M) q)
      n x.1

@[simp]
theorem coneRelativeSectionToNativeStrict_coe
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (x : ConeRelativeSections (G := G) M q) :
    (coneRelativeSectionToNativeStrict (G := G) M q x :
        orderedComplexSSet (simplicialCone M) ⟶
          underlyingSSet (F (AddCommGrpCat.of G) (q + 1))) =
      strictFSectionToNativeFiberMap (simplicialCone M) q x.1 :=
  rfl

theorem coneRelativeSectionToNativeStrict_injective
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Injective (coneRelativeSectionToNativeStrict (G := G) M q) := by
  intro x y hxy
  apply Subtype.ext
  apply (strictFSectionsLinearEquivNativeFiberMaps
    (G := G) (simplicialCone M) q).injective
  exact congrArg Subtype.val hxy

theorem coneRelativeSectionToNativeStrict_surjective
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Surjective (coneRelativeSectionToNativeStrict (G := G) M q) := by
  intro f
  let e := strictFSectionsLinearEquivNativeFiberMaps
    (G := G) (simplicialCone M) q
  let x : StrictFSections (LData (G := G) (simplicialCone M) q) :=
    e.symm f.1
  have hxmap : strictFSectionToNativeFiberMap (simplicialCone M) q x = f.1 :=
    e.apply_symm_apply f.1
  have hbottomNative : literalConeBottomMap M ≫ f.1 = 0 := by
    have hf := AddMonoidHom.mem_ker.mp f.2
    change (literalConeBottomSubcomplex M).ι ≫ f.1 = 0 at hf
    calc
      literalConeBottomMap M ≫ f.1 =
          SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
            (literalConeBottomSubcomplex M).ι ≫ f.1 := by
              rw [← Category.assoc, SSet.Subcomplex.toRange_ι]
      _ = 0 := by rw [hf]; ext Delta z; rfl
  have hbottomSection :
      coneBottomStrictFSectionsRestriction (G := G) M q x = 0 := by
    apply (strictFSectionsLinearEquivNativeFiberMaps
      (G := G) M q).injective
    change strictFSectionToNativeFiberMap M q
        (mapStrictFSections
          ((coneBottomInclusion M).toFacetRestrictionHom (G := G) q) x) =
      strictFSectionToNativeFiberMap M q 0
    rw [map_zero, ← strictFSectionToNativeFiberMap_naturality
      (coneBottomInclusion M) q x, hxmap, hbottomNative]
  refine ⟨⟨x, hbottomSection⟩, ?_⟩
  apply Subtype.ext
  exact hxmap

def coneRelativeSectionsLinearEquivNativeStrict
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    ConeRelativeSections (G := G) M q ≃ₗ[ℤ]
      RelativeZeroMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1)) :=
  LinearEquiv.ofBijective (coneRelativeSectionToNativeStrict (G := G) M q)
    ⟨coneRelativeSectionToNativeStrict_injective (G := G) M q,
      coneRelativeSectionToNativeStrict_surjective (G := G) M q⟩

/-! ## Turning a native relative nullhomotopy into a two-face extension -/

def literalConeBottomSubcomplexVertex
    (M : AbstractSimplicialComplex V) (b : V) :
    (literalConeBottomSubcomplex M : SSet).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ⟨(literalConeBottomMap M).app _ (orderedComplexVertex M b),
    ⟨orderedComplexVertex M b, rfl⟩⟩

/-- For the pair `(C_vM,M)`, vanishing on the relative cone supplied by
the generic HEP is exactly strict vanishing on the other literal cone face. -/
theorem LiteralRelativeExtension.doubleConeOther_eq_zero
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism (literalConeBottomSubcomplex M) A}
    (E : LiteralRelativeExtension (simplicialCone M)
      (literalConeBottomSubcomplex M) A f) :
    (doubleConeOtherInclusion M).toSSetMap ≫ E.map = 0 := by
  have hline :
      (literalConeBottomSubcomplex M).ι ▷ Δ[1] ≫
          literalConeCylinderQuotient (simplicialCone M) ≫ E.map = 0 := by
    calc
      _ = fst (literalConeBottomSubcomplex M : SSet) Δ[1] ≫
          zeroBoundary (literalConeBottomSubcomplex M) A ≫
            (zeroSubcomplex A).ι := E.rel
      _ = 0 := cylinder_zeroBoundary (literalConeBottomSubcomplex M) A
  have hbottomLine :
      literalConeBottomMap M ▷ Δ[1] ≫
          literalConeCylinderQuotient (simplicialCone M) ≫ E.map = 0 := by
    calc
      _ = (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[1]) ≫
          ((literalConeBottomSubcomplex M).ι ▷ Δ[1]) ≫
            literalConeCylinderQuotient (simplicialCone M) ≫ E.map := by
              rw [← comp_whiskerRight_assoc,
                SSet.Subcomplex.toRange_ι]
      _ = 0 := by rw [hline]; ext Delta z; rfl
  have hquotient :
      literalConeCylinderQuotient M ≫
          (doubleConeOtherInclusion M).toSSetMap ≫ E.map = 0 := by
    rw [← Category.assoc,
      ← coneBottom_literalConeCylinderQuotient_naturality M]
    exact hbottomLine
  letI : Epi (literalConeCylinderQuotient M) :=
    literalConeCylinderQuotient_epi M b
  rw [← cancel_epi (literalConeCylinderQuotient M)]
  calc
    literalConeCylinderQuotient M ≫
          ((doubleConeOtherInclusion M).toSSetMap ≫ E.map) =
        literalConeCylinderQuotient M ≫
            (doubleConeOtherInclusion M).toSSetMap ≫ E.map := rfl
    _ = 0 := hquotient
    _ = literalConeCylinderQuotient M ≫ 0 := by
      ext Delta z
      rfl

/-- Every native-null strict cone-relative section is realized by the
difference of the two restrictions of one outer-cone map. -/
noncomputable def nativeNullConeRelativeLiteralExtension
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (x : ConeRelativeSections (G := G) M q)
    (hx : coneRelativeSectionToNativeStrict (G := G) M q x ∈
      StrictNullMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1))) :
    LiteralRelativeExtension (simplicialCone M)
      (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1))
      (RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1))
        (coneRelativeSectionToNativeStrict (G := G) M q x)) := by
  apply Classical.choice
  apply nonempty_literalRelativeExtension_of_mem_nativeNullMaps
    (simplicialCone M) (literalConeBottomSubcomplex M)
      (literalConeBottomSubcomplexVertex M b)
  change (RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1))
      (coneRelativeSectionToNativeStrict (G := G) M q x)) ∈
    NativeNullMaps (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1))
  exact hx

/-! ## Algebraic null relations versus native relative nullhomotopies -/

/-- Under the two reduced-cohomology hypotheses, every algebraic
bottom-zero primitive relation gives a genuinely nullhomotopic native
relative map. -/
theorem coneRelativeNullMaps_le_nativeStrictNull_of_reduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    ConeRelativeNullMaps (G := G) M (n + 1) ≤
      (StrictNullMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 2))).comap
          (coneRelativeSectionToNativeStrict (G := G) M (n + 1)) := by
  rintro x ⟨r, rfl⟩
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  let hr : coneBottomRprimRestriction (G := G) M (n + 1) r.1 = 0 := r.2
  let f := bottomZeroRprimNativeRelativeMap M (n + 1) r.1 hr
  have hmap :
      RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
          (F (AddCommGrpCat.of G) (n + 2))
          (coneRelativeSectionToNativeStrict (G := G) M (n + 1)
            (coneRelativeRestriction (G := G) M (n + 1) r)) = f := by
    apply SSet.RelativeMorphism.ext
    change strictFSectionToNativeFiberMap (simplicialCone M) (n + 1)
        (restrictionClass
          (LData (G := G) (simplicialCone M) (n + 1)) r.1) =
      rprimToNativeFiberMap (simplicialCone M) (n + 1) r.1
    exact strictFSectionToNativeFiberMap_restrictionClass_transgression
      (G := G) (simplicialCone M) (n + 1) r.1
  change
    (RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (n + 2))
      (coneRelativeSectionToNativeStrict (G := G) M (n + 1)
        (coneRelativeRestriction (G := G) M (n + 1) r))).homotopyClass = 0
  rw [hmap]
  exact bottomZeroRprimNativeRelative_class_eq_zero_of_reduced
    M b n hhigh hlow r.1 hr

/-- The two cone faces of the literal double cone have the same primitive
restriction on their common bottom. -/
theorem coneBottom_mapRprim_doubleConeFaces_eq
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G)
      (simplicialCone (simplicialCone M)) q)) :
    coneBottomRprimRestriction (G := G) M q
        (mapRprim
          ((coneBottomInclusion (simplicialCone M)).toFacetRestrictionHom
            (G := G) q) r) =
      coneBottomRprimRestriction (G := G) M q
        (mapRprim
          ((doubleConeOtherInclusion M).toFacetRestrictionHom
            (G := G) q) r) := by
  apply Subtype.ext
  change mapRedDist
      ((coneBottomInclusion M).pullback (G := G) q).toAddMonoidHom
        (mapRedDist
          ((coneBottomInclusion (simplicialCone M)).pullback
            (G := G) q).toAddMonoidHom r.1) =
    mapRedDist
      ((coneBottomInclusion M).pullback (G := G) q).toAddMonoidHom
        (mapRedDist
          ((doubleConeOtherInclusion M).pullback
            (G := G) q).toAddMonoidHom r.1)
  have hpull :
      ((coneBottomInclusion M).pullback (G := G) q).toAddMonoidHom.comp
          ((coneBottomInclusion (simplicialCone M)).pullback
            (G := G) q).toAddMonoidHom =
        ((coneBottomInclusion M).pullback (G := G) q).toAddMonoidHom.comp
          ((doubleConeOtherInclusion M).pullback
            (G := G) q).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro c
    change (coneBottomInclusion M).pullback (G := G) q
          ((coneBottomInclusion (simplicialCone M)).pullback q c) =
      (coneBottomInclusion M).pullback (G := G) q
          ((doubleConeOtherInclusion M).pullback q c)
    ext sigma
    simp only [OrderedSimplicialMap.pullback_apply]
    congr 1
    calc
      (coneBottomInclusion (simplicialCone M)).mapSimplex
            ((coneBottomInclusion M).mapSimplex sigma) =
          (doubleConeBoundaryInclusion M).mapSimplex
            ((doubleConeInnerBoundaryInclusion M).mapSimplex
              ((coneBottomInclusion M).mapSimplex sigma)) := by
        rw [← doubleConeInnerInclusion_eq M]
        exact OrderedSimplicialMap.mapSimplex_comp
          (doubleConeBoundaryInclusion M)
          (doubleConeInnerBoundaryInclusion M)
          ((coneBottomInclusion M).mapSimplex sigma)
      _ = (doubleConeBoundaryInclusion M).mapSimplex
            ((doubleConeOtherBoundaryInclusion M).mapSimplex
              ((coneBottomInclusion M).mapSimplex sigma)) := by
        exact congrArg (doubleConeBoundaryInclusion M).mapSimplex
          (doubleConeFaces_mapSimplex_bottom_eq M q sigma)
      _ = (doubleConeOtherInclusion M).mapSimplex
            ((coneBottomInclusion M).mapSimplex sigma) := by
        exact (OrderedSimplicialMap.mapSimplex_comp
          (doubleConeBoundaryInclusion M)
          (doubleConeOtherBoundaryInclusion M)
          ((coneBottomInclusion M).mapSimplex sigma)).symm
  rw [PathAlgebra.mapRedDist_comp_apply,
    PathAlgebra.mapRedDist_comp_apply, hpull]

/-- Conversely, an actual native relative nullhomotopy extends over the
outer literal cone.  Realizing that extension by one primitive relation and
subtracting its two face restrictions produces a bottom-zero primitive
relation representing the original strict section. -/
theorem nativeStrictNull_le_coneRelativeNullMaps
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ) :
    (StrictNullMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1))).comap
          (coneRelativeSectionToNativeStrict (G := G) M q) ≤
      ConeRelativeNullMaps (G := G) M q := by
  intro x hx
  let Eout := nativeNullConeRelativeLiteralExtension
    (G := G) M b q x hx
  let eOuter := strictFSectionsLinearEquivNativeFiberMaps
    (G := G) (simplicialCone (simplicialCone M)) q
  let y : StrictFSections
      (LData (G := G) (simplicialCone (simplicialCone M)) q) :=
    eOuter.symm Eout.map
  have hy : strictFSectionToNativeFiberMap
      (simplicialCone (simplicialCone M)) q y = Eout.map :=
    eOuter.apply_symm_apply Eout.map
  obtain ⟨r, hr⟩ := coneRestrictionClass_surjective
    (G := G) (simplicialCone M) q y
  have hrmap : rprimToNativeFiberMap
      (simplicialCone (simplicialCone M)) q r = Eout.map := by
    calc
      _ = strictFSectionToNativeFiberMap
            (simplicialCone (simplicialCone M)) q
            (restrictionClass
              (LData (G := G) (simplicialCone (simplicialCone M)) q) r) :=
          (strictFSectionToNativeFiberMap_restrictionClass_transgression
            (G := G) (simplicialCone (simplicialCone M)) q r).symm
      _ = strictFSectionToNativeFiberMap
            (simplicialCone (simplicialCone M)) q y := by rw [hr]
      _ = Eout.map := hy
  let rv : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) q) :=
    mapRprim
      ((coneBottomInclusion (simplicialCone M)).toFacetRestrictionHom
        (G := G) q) r
  let rw : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) q) :=
    mapRprim
      ((doubleConeOtherInclusion M).toFacetRestrictionHom
        (G := G) q) r
  have hrvMap : rprimToNativeFiberMap (simplicialCone M) q rv =
      strictFSectionToNativeFiberMap (simplicialCone M) q x.1 := by
    calc
      _ = (coneBottomInclusion (simplicialCone M)).toSSetMap ≫
            rprimToNativeFiberMap
              (simplicialCone (simplicialCone M)) q r :=
          (rprimToNativeFiberMap_pullback
            (G := G) (coneBottomInclusion (simplicialCone M)) q r).symm
      _ = (coneBottomInclusion (simplicialCone M)).toSSetMap ≫
            Eout.map := by rw [hrmap]
      _ = strictFSectionToNativeFiberMap (simplicialCone M) q x.1 :=
        Eout.bottom
  have hrwMap : rprimToNativeFiberMap (simplicialCone M) q rw = 0 := by
    calc
      _ = (doubleConeOtherInclusion M).toSSetMap ≫
            rprimToNativeFiberMap
              (simplicialCone (simplicialCone M)) q r :=
          (rprimToNativeFiberMap_pullback
            (G := G) (doubleConeOtherInclusion M) q r).symm
      _ = (doubleConeOtherInclusion M).toSSetMap ≫ Eout.map := by
        rw [hrmap]
      _ = 0 := Eout.doubleConeOther_eq_zero M b
  have hrvSection : restrictionClass
      (LData (G := G) (simplicialCone M) q) rv = x.1 := by
    apply (strictFSectionsLinearEquivNativeFiberMaps
      (G := G) (simplicialCone M) q).injective
    change strictFSectionToNativeFiberMap (simplicialCone M) q
        (restrictionClass (LData (G := G) (simplicialCone M) q) rv) =
      strictFSectionToNativeFiberMap (simplicialCone M) q x.1
    rw [strictFSectionToNativeFiberMap_restrictionClass_transgression]
    exact hrvMap
  have hrwSection : restrictionClass
      (LData (G := G) (simplicialCone M) q) rw = 0 := by
    apply (strictFSectionsLinearEquivNativeFiberMaps
      (G := G) (simplicialCone M) q).injective
    change strictFSectionToNativeFiberMap (simplicialCone M) q
        (restrictionClass (LData (G := G) (simplicialCone M) q) rw) =
      strictFSectionToNativeFiberMap (simplicialCone M) q 0
    rw [strictFSectionToNativeFiberMap_restrictionClass_transgression, map_zero]
    exact hrwMap
  let k : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) q) := rv - rw
  have hk : coneBottomRprimRestriction (G := G) M q k = 0 := by
    dsimp [k]
    rw [map_sub,
      coneBottom_mapRprim_doubleConeFaces_eq (G := G) M q r,
      sub_self]
  refine ⟨⟨k, hk⟩, ?_⟩
  apply Subtype.ext
  change restrictionClass (LData (G := G) (simplicialCone M) q) k = x.1
  calc
    _ = restrictionClass (LData (G := G) (simplicialCone M) q) rv -
          restrictionClass (LData (G := G) (simplicialCone M) q) rw := by
      exact map_sub
        (restrictionClass (LData (G := G) (simplicialCone M) q)) rv rw
    _ = x.1 := by rw [hrvSection, hrwSection, sub_zero]

/-- The algebraically presented and genuinely nullhomotopic relative maps
define exactly the same subgroup. -/
theorem coneRelativeNullMaps_eq_nativeStrictNull_comap_of_reduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    ConeRelativeNullMaps (G := G) M (n + 1) =
      (StrictNullMaps (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 2))).comap
          (coneRelativeSectionToNativeStrict (G := G) M (n + 1)) := by
  apply le_antisymm
  · exact coneRelativeNullMaps_le_nativeStrictNull_of_reduced
      (G := G) M b n hhigh hlow
  · exact nativeStrictNull_le_coneRelativeNullMaps
      (G := G) M b (n + 1)

/-- Pass a strict cone-relative section to its actual native relative
homotopy class. -/
def coneRelativeNativeClass
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    ConeRelativeSections (G := G) M q →ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1)) :=
  (strictHomotopyClassLinear (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1))).comp
    (coneRelativeSectionToNativeStrict (G := G) M q)

@[simp]
theorem coneRelativeNativeClass_apply
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (x : ConeRelativeSections (G := G) M q) :
    coneRelativeNativeClass (G := G) M q x =
      (RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (q + 1))
        (coneRelativeSectionToNativeStrict (G := G) M q x)).homotopyClass :=
  rfl

/-- The native extension class already constructed from a primitive cycle
is the native class of its algebraic cone-relative section. -/
theorem ConeCycleExtensionData.nativeExtensionClass_eq_coneRelativeNativeClass
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (E : ConeCycleExtensionData (G := G) M q)
    (z : Zprim (LData (G := G) M q)) :
    E.nativeExtensionClass (M := M) (q := q) z =
      coneRelativeNativeClass (G := G) M q
        (E.extensionSection (X := M) (n := q) z) := by
  change (E.nativeExtensionRelativeMap (M := M) (q := q) z).homotopyClass =
    (RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M)
      (F (AddCommGrpCat.of G) (q + 1))
      (coneRelativeSectionToNativeStrict (G := G) M q
        (E.extensionSection (X := M) (n := q) z))).homotopyClass
  congr 1

theorem coneRelativeNativeClass_surjective
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Surjective (coneRelativeNativeClass (G := G) M q) := by
  intro c
  obtain ⟨f, rfl⟩ := strictHomotopyClassLinear_surjective
    (literalConeBottomSubcomplex M)
    (F (AddCommGrpCat.of G) (q + 1)) c
  obtain ⟨x, rfl⟩ := coneRelativeSectionToNativeStrict_surjective
    (G := G) M q f
  exact ⟨x, rfl⟩

theorem coneRelativeNativeClass_ker_eq_of_reduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    LinearMap.ker (coneRelativeNativeClass (G := G) M (n + 1)) =
      ConeRelativeNullMaps (G := G) M (n + 1) := by
  rw [coneRelativeNullMaps_eq_nativeStrictNull_comap_of_reduced
    (G := G) M b n hhigh hlow]
  rfl

/-- The algebraic cone-relative quotient is canonically the genuine native
relative homotopy-class group. -/
def coneRelativeQuotientLinearEquivNativeClassOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    (ConeRelativeSections (G := G) M (n + 1) ⧸
      ConeRelativeNullMaps (G := G) M (n + 1)) ≃ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 2)) :=
  (Submodule.quotEquivOfEq
      (ConeRelativeNullMaps (G := G) M (n + 1))
      (LinearMap.ker (coneRelativeNativeClass (G := G) M (n + 1)))
      (coneRelativeNativeClass_ker_eq_of_reduced
        (G := G) M b n hhigh hlow).symm).trans
    ((coneRelativeNativeClass (G := G) M (n + 1)).quotKerEquivOfSurjective
      (coneRelativeNativeClass_surjective (G := G) M (n + 1)))

@[simp]
theorem coneRelativeQuotientLinearEquivNativeClassOfReduced_mkQ
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (x : ConeRelativeSections (G := G) M (n + 1)) :
    coneRelativeQuotientLinearEquivNativeClassOfReduced
        (G := G) M b n hhigh hlow
        ((ConeRelativeNullMaps (G := G) M (n + 1)).mkQ x) =
      coneRelativeNativeClass (G := G) M (n + 1) x := by
  simp [coneRelativeQuotientLinearEquivNativeClassOfReduced]

/-! ## The native transgression -/

/-- Native relative uniqueness turns the already-proved killing of
primitive boundaries into the algebraic boundary-null datum needed by the
canonical transgression equivalence. -/
def ConeCycleExtensionData.nativeConeBoundaryNullDataOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap) :
    ConeCycleExtensionData.ConeBoundaryNullData
      (G := G) M (n + 1) E where
  boundaries_null := by
    intro z hz
    rw [LinearMap.mem_ker]
    let e := coneRelativeQuotientLinearEquivNativeClassOfReduced
      (G := G) M b n hhigh hlow
    apply e.injective
    change e ((ConeRelativeNullMaps (G := G) M (n + 1)).mkQ
        (E.extensionSection (X := M) (n := n + 1) z)) = e 0
    calc
      _ = coneRelativeNativeClass (G := G) M (n + 1)
            (E.extensionSection (X := M) (n := n + 1) z) :=
        coneRelativeQuotientLinearEquivNativeClassOfReduced_mkQ
          (G := G) M b n hhigh hlow _
      _ = E.nativeExtensionClass (M := M) (q := n + 1) z :=
        (E.nativeExtensionClass_eq_coneRelativeNativeClass M (n + 1) z).symm
      _ = 0 := LinearMap.mem_ker.mp
        (BprimInZprim_le_ker_nativeExtensionClass_of_reduced
          M b n hhigh hlow E Q hz)
      _ = e 0 := (map_zero e).symm

/-- The fully native form of Proposition 4.5: the transgression from
`T'` to the genuine relative simplicial homotopy-class group is a linear
equivalence. -/
def nativeTransgressionLinearEquivOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap) :
    TPrime (LData (G := G) M (n + 1)) ≃ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 2)) :=
  (ConeCycleExtensionData.nativeConeBoundaryNullDataOfReduced
      (G := G) M b n hhigh hlow E Q).transgressionEquiv.trans
    (coneRelativeQuotientLinearEquivNativeClassOfReduced
      (G := G) M b n hhigh hlow)

/-- Formula (4.18) in the genuine native target. -/
@[simp]
theorem nativeTransgressionLinearEquivOfReduced_mkQ
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap)
    (z : Zprim (LData (G := G) M (n + 1))) :
    nativeTransgressionLinearEquivOfReduced
        (G := G) M b n hhigh hlow E Q
        ((BprimInZprim (LData (G := G) M (n + 1))).mkQ z) =
      E.nativeExtensionClass (M := M) (q := n + 1) z := by
  rw [nativeTransgressionLinearEquivOfReduced, LinearEquiv.trans_apply,
    ConeCycleExtensionData.ConeBoundaryNullData.transgressionEquiv_mkQ]
  change coneRelativeQuotientLinearEquivNativeClassOfReduced
      (G := G) M b n hhigh hlow
      ((ConeRelativeNullMaps (G := G) M (n + 1)).mkQ
        (E.extensionSection (X := M) (n := n + 1) z)) =
    E.nativeExtensionClass (M := M) (q := n + 1) z
  rw [coneRelativeQuotientLinearEquivNativeClassOfReduced_mkQ,
    ← E.nativeExtensionClass_eq_coneRelativeNativeClass]

/-- The preceding equivalence has as underlying linear map the native
transgression already defined by quotient descent. -/
theorem nativeTransgressionLinearEquivOfReduced_toLinearMap
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap) :
    (nativeTransgressionLinearEquivOfReduced
      (G := G) M b n hhigh hlow E Q).toLinearMap =
        nativeTransgressionOfReduced M b n hhigh hlow E Q := by
  apply LinearMap.ext
  intro t
  obtain ⟨z, rfl⟩ :=
    (BprimInZprim (LData (G := G) M (n + 1))).mkQ_surjective t
  change nativeTransgressionLinearEquivOfReduced
      (G := G) M b n hhigh hlow E Q
      ((BprimInZprim (LData (G := G) M (n + 1))).mkQ z) =
    nativeTransgressionOfReduced M b n hhigh hlow E Q
      ((BprimInZprim (LData (G := G) M (n + 1))).mkQ z)
  rw [nativeTransgressionLinearEquivOfReduced_mkQ,
    nativeTransgressionOfReduced_mkQ]

theorem nativeTransgressionOfReduced_injective
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap) :
    Function.Injective
      (nativeTransgressionOfReduced M b n hhigh hlow E Q) := by
  rw [← nativeTransgressionLinearEquivOfReduced_toLinearMap
    (G := G) M b n hhigh hlow E Q]
  exact (nativeTransgressionLinearEquivOfReduced
    (G := G) M b n hhigh hlow E Q).injective

theorem nativeTransgressionOfReduced_surjective
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (E : ConeCycleExtensionData (G := G) M (n + 1))
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M (n + 1))
      (coboundaryToRange (G := G) (simplicialCone M) (n + 1))
      (coneBottomFacetHom (G := G) M (n + 1)).primitiveMap) :
    Function.Surjective
      (nativeTransgressionOfReduced M b n hhigh hlow E Q) := by
  rw [← nativeTransgressionLinearEquivOfReduced_toLinearMap
    (G := G) M b n hhigh hlow E Q]
  exact (nativeTransgressionLinearEquivOfReduced
    (G := G) M b n hhigh hlow E Q).surjective

/-- The canonical additive cycle extension used by the public native
transgression. -/
def canonicalConeCycleExtensionDataOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b q) :
    ConeCycleExtensionData (G := G) M q :=
  ConeCycleExtensionData.ofFiberwiseCochainLift
    (X := M) (n := q)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b q hred)

/-- Canonical public native transgression equivalence, with all extension
choices constructed from the two reduced-cohomology hypotheses. -/
def canonicalNativeTransgressionLinearEquivOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    TPrime (LData (G := G) M (n + 1)) ≃ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M)
        (F (AddCommGrpCat.of G) (n + 2)) :=
  nativeTransgressionLinearEquivOfReduced (G := G) M b n hhigh hlow
    (canonicalConeCycleExtensionDataOfReduced
      (G := G) M b (n + 1) hhigh)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b (n + 1) hhigh)

@[simp]
theorem canonicalNativeTransgressionLinearEquivOfReduced_mkQ
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (z : Zprim (LData (G := G) M (n + 1))) :
    canonicalNativeTransgressionLinearEquivOfReduced
        (G := G) M b n hhigh hlow
        ((BprimInZprim (LData (G := G) M (n + 1))).mkQ z) =
      (canonicalConeCycleExtensionDataOfReduced
        (G := G) M b (n + 1) hhigh).nativeExtensionClass
          (M := M) (q := n + 1) z := by
  exact nativeTransgressionLinearEquivOfReduced_mkQ
    (G := G) M b n hhigh hlow
    (canonicalConeCycleExtensionDataOfReduced
      (G := G) M b (n + 1) hhigh)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b (n + 1) hhigh) z

/-- The canonical equivalence upgrades the previously defined canonical
native transgression linear map without changing representatives. -/
theorem canonicalNativeTransgressionLinearEquivOfReduced_toLinearMap
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    (canonicalNativeTransgressionLinearEquivOfReduced
      (G := G) M b n hhigh hlow).toLinearMap =
        canonicalNativeTransgressionOfReduced M b n hhigh hlow := by
  exact nativeTransgressionLinearEquivOfReduced_toLinearMap
    (G := G) M b n hhigh hlow
    (canonicalConeCycleExtensionDataOfReduced
      (G := G) M b (n + 1) hhigh)
    (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b (n + 1) hhigh)

end GeneralSphereT.SimplicialCochain
