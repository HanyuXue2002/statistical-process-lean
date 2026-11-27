import Formalization.Section4LiteralDoubleConeDifference

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: reverse exactness for the literal two-cone difference

The kernel of inner-minus-other consists exactly of pointed-null maps.
The proof corrects a kernel representative to the diagonal map and then
contracts that diagonal through the literal cone contraction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory Limits

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

universe u

variable {V : Type u} [LinearOrder V] [Fintype V]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) literalDoubleReverseOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance
local instance (priority := 10000) literalDoubleReverseOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance
local instance (priority := 10000) literalDoubleReverseOptionLinearOrder :
    LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
local instance (priority := 10001) literalDoubleReverseOptionOptionLE :
    LE (Option (Option V)) := @WithBot.instLE (Option V) inferInstance
local instance (priority := 10001) literalDoubleReverseOptionOptionLT :
    LT (Option (Option V)) := @WithBot.instLT (Option V) inferInstance
local instance (priority := 10001) literalDoubleReverseOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

variable (A : SimplicialObject AddCommGrpCat.{u})

theorem literalDoubleConeApex_comp_eq_zero
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.const (X := literalDoubleConeApexSubcomplex M)
        (orderedComplexVertex (doubleConeBoundary M)
          (none : Option (Option V))) ≫ f.map = 0 := by
  have hf : (literalDoubleConeApexSubcomplex M).ι ≫ f.map = 0 := by
    calc
      _ = zeroBoundary (literalDoubleConeApexSubcomplex M) A ≫
          (zeroSubcomplex A).ι := f.comm
      _ = 0 := zeroBoundary_comp_inclusion
        (literalDoubleConeApexSubcomplex M) A
  have hapexι : (literalDoubleConeApexSubcomplex M).ι =
      SSet.const (orderedComplexVertex (doubleConeBoundary M)
        (none : Option (Option V))) := by
    simpa only [literalDoubleConeApexSubcomplex,
      orderedComplexBasepointSubcomplex] using
      (SSet.Subcomplex.ofSimplex_ι
        (orderedComplexVertex (doubleConeBoundary M)
          (none : Option (Option V))))
  simpa only [hapexι] using hf

theorem literalDoubleConeApex_comp_eq_zero_from
    (X : SSet.{u})
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.const (X := X)
        (orderedComplexVertex (doubleConeBoundary M)
          (none : Option (Option V))) ≫ f.map = 0 := by
  let p : (literalDoubleConeApexSubcomplex M : SSet).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
    ⟨orderedComplexVertex (doubleConeBoundary M)
      (none : Option (Option V)), SSet.Subcomplex.mem_ofSimplex_obj _⟩
  have hp : SSet.const (X := X) p ≫
      (literalDoubleConeApexSubcomplex M).ι =
    SSet.const (orderedComplexVertex (doubleConeBoundary M)
      (none : Option (Option V))) := by
    rw [SSet.const_comp]
    congr 1
  have hf : (literalDoubleConeApexSubcomplex M).ι ≫ f.map = 0 := by
    calc
      _ = zeroBoundary (literalDoubleConeApexSubcomplex M) A ≫
          (zeroSubcomplex A).ι := f.comm
      _ = 0 := zeroBoundary_comp_inclusion
        (literalDoubleConeApexSubcomplex M) A
  calc
    _ = (SSet.const (X := X) p ≫
          (literalDoubleConeApexSubcomplex M).ι) ≫ f.map := by rw [hp]
    _ = SSet.const (X := X) p ≫
        ((literalDoubleConeApexSubcomplex M).ι ≫ f.map) :=
      Category.assoc _ _ _
    _ = 0 := by rw [hf]; ext Delta x; rfl

def literalDifferenceCorrectionInner
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    orderedComplexSSet (simplicialCone M) ⊗ Δ[1] ⟶
      underlyingSSet A :=
  H.h + fst (orderedComplexSSet (simplicialCone M)) Δ[1] ≫
    literalDoubleConeOtherMap M ≫ f.map

def literalDifferenceCorrectionOther
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    orderedComplexSSet (simplicialCone M) ⊗ Δ[1] ⟶
      underlyingSSet A :=
  fst (orderedComplexSSet (simplicialCone M)) Δ[1] ≫
    literalDoubleConeOtherMap M ≫ f.map

theorem literalConeBottom_whisker_relativeHomotopy_eq_zero
    {r s : NativeRelativeMorphism (literalConeBottomSubcomplex M) A}
    (H : SSet.RelativeMorphism.Homotopy r s) :
    (literalConeBottomMap M ▷ Δ[1]) ≫ H.h = 0 := by
  have hrel : ((literalConeBottomSubcomplex M).ι ▷ Δ[1]) ≫
      H.h = 0 := by
    rw [H.rel]
    exact cylinder_zeroBoundary (literalConeBottomSubcomplex M) A
  have hfactor := congrArg (fun k ↦ k ▷ Δ[1])
    (SSet.Subcomplex.toRange_ι (literalConeBottomMap M))
  simp only [comp_whiskerRight] at hfactor
  calc
    (literalConeBottomMap M ▷ Δ[1]) ≫ H.h =
        (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[1]) ≫
          ((literalConeBottomSubcomplex M).ι ▷ Δ[1]) ≫ H.h := by
            rw [← reassoc_of% hfactor]
    _ = 0 := by rw [hrel]; ext Delta x; rfl

theorem literalDifferenceCorrection_compatible
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    (literalConeBottomMap M ▷ Δ[1]) ≫
        literalDifferenceCorrectionInner M A f H =
      (literalConeBottomMap M ▷ Δ[1]) ≫
        literalDifferenceCorrectionOther M A f := by
  have hH := literalConeBottom_whisker_relativeHomotopy_eq_zero M A H
  rw [literalDifferenceCorrectionInner, literalDifferenceCorrectionOther,
    NativeRelativeHomotopyGroup.comp_addMap, hH, zero_add]

def literalDifferenceCorrectionCylinder
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    orderedComplexSSet (doubleConeBoundary M) ⊗ Δ[1] ⟶
      underlyingSSet A :=
  literalDoubleConeCylinderDesc M
    (literalDifferenceCorrectionInner M A f H)
    (literalDifferenceCorrectionOther M A f)
    (literalDifferenceCorrection_compatible M A f H)

@[reassoc]
theorem ι₀_literalDifferenceCorrectionOther
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.ι₀ ≫ literalDifferenceCorrectionOther M A f =
      literalDoubleConeOtherMap M ≫ f.map := by
  rw [literalDifferenceCorrectionOther, ← Category.assoc,
    SSet.ι₀_fst, Category.id_comp]

@[reassoc]
theorem ι₁_literalDifferenceCorrectionOther
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.ι₁ ≫ literalDifferenceCorrectionOther M A f =
      literalDoubleConeOtherMap M ≫ f.map := by
  rw [literalDifferenceCorrectionOther, ← Category.assoc,
    SSet.ι₁_fst, Category.id_comp]

@[reassoc]
theorem ι₀_literalDifferenceCorrectionInner
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    SSet.ι₀ ≫ literalDifferenceCorrectionInner M A f H =
      literalDoubleConeInnerMap M ≫ f.map := by
  have hc := ι₀_literalDifferenceCorrectionOther M A f
  change SSet.ι₀ ≫ fst (orderedComplexSSet (simplicialCone M)) Δ[1] ≫
      literalDoubleConeOtherMap M ≫ f.map = _ at hc
  rw [literalDifferenceCorrectionInner,
    NativeRelativeHomotopyGroup.comp_addMap, H.h₀, hc]
  change (literalDoubleConeInnerMap M ≫ f.map -
      literalDoubleConeOtherMap M ≫ f.map) +
    literalDoubleConeOtherMap M ≫ f.map = _
  exact sub_add_cancel _ _

@[reassoc]
theorem ι₁_literalDifferenceCorrectionInner
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    SSet.ι₁ ≫ literalDifferenceCorrectionInner M A f H =
      literalDoubleConeOtherMap M ≫ f.map := by
  have hc := ι₁_literalDifferenceCorrectionOther M A f
  change SSet.ι₁ ≫ fst (orderedComplexSSet (simplicialCone M)) Δ[1] ≫
      literalDoubleConeOtherMap M ≫ f.map = _ at hc
  rw [literalDifferenceCorrectionInner,
    NativeRelativeHomotopyGroup.comp_addMap, H.h₁, hc]
  change (literalTwoConeDifferenceMorphism M A 0).map +
    literalDoubleConeOtherMap M ≫ f.map = _
  have hz : literalTwoConeDifferenceMorphism M A 0 = 0 :=
    map_zero (literalTwoConeDifferenceMorphismLinear M A)
  rw [hz, relativeMorphism_zero_map, zero_add]

/-! ## The diagonal map and the correction homotopy -/

abbrev literalDiagonalConeMap
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A :=
  literalDoubleConeOtherMap M ≫ f.map

theorem literalDiagonalConeMap_apex_eq_zero {X : SSet.{u}}
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.const (X := X)
        (literalConeApex M) ≫ literalDiagonalConeMap M A f = 0 := by
  calc
    _ = SSet.const (X := X)
          (orderedComplexVertex (doubleConeBoundary M)
            (none : Option (Option V))) ≫ f.map := by
      rw [literalDiagonalConeMap,
        literalDoubleConeOtherMap_const_apex_assoc]
    _ = 0 := literalDoubleConeApex_comp_eq_zero_from M A X f

def literalDiagonalUnderlyingMap
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    orderedComplexSSet (doubleConeBoundary M) ⟶ underlyingSSet A :=
  literalDoubleConeDesc M (literalDiagonalConeMap M A f)
    (literalDiagonalConeMap M A f) rfl

def literalDiagonalMorphism
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A := by
  let Dzero : RelativeZeroMaps (literalDoubleConeApexSubcomplex M) A := by
    refine ⟨literalDiagonalUnderlyingMap M A f, ?_⟩
    change (literalDoubleConeApexSubcomplex M).ι ≫
      literalDiagonalUnderlyingMap M A f = 0
    have hapexι : (literalDoubleConeApexSubcomplex M).ι =
        SSet.const (orderedComplexVertex (doubleConeBoundary M)
          (none : Option (Option V))) := by
      simpa only [literalDoubleConeApexSubcomplex,
        orderedComplexBasepointSubcomplex] using
        (SSet.Subcomplex.ofSimplex_ι
          (orderedComplexVertex (doubleConeBoundary M)
            (none : Option (Option V))))
    rw [hapexι]
    calc
      _ = (SSet.const (X := literalDoubleConeApexSubcomplex M)
              (literalConeApex M) ≫ literalDoubleConeOtherMap M) ≫
            literalDiagonalUnderlyingMap M A f := by
        rw [literalDoubleConeOtherMap_const_apex]
      _ = SSet.const (X := literalDoubleConeApexSubcomplex M)
            (literalConeApex M) ≫ literalDiagonalConeMap M A f := by
        rw [Category.assoc, literalDiagonalUnderlyingMap,
          literalDoubleConeOtherMap_desc]
      _ = 0 := literalDiagonalConeMap_apex_eq_zero M A f
  exact RelativeZeroMaps.toRelativeMorphism
    (literalDoubleConeApexSubcomplex M) A Dzero

@[reassoc]
theorem literalDoubleConeInnerMap_diagonal
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    literalDoubleConeInnerMap M ≫ (literalDiagonalMorphism M A f).map =
      literalDiagonalConeMap M A f := by
  change literalDoubleConeInnerMap M ≫
      literalDiagonalUnderlyingMap M A f = _
  exact literalDoubleConeInnerMap_desc M _ _ rfl

@[reassoc]
theorem literalDoubleConeOtherMap_diagonal
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    literalDoubleConeOtherMap M ≫ (literalDiagonalMorphism M A f).map =
      literalDiagonalConeMap M A f := by
  change literalDoubleConeOtherMap M ≫
      literalDiagonalUnderlyingMap M A f = _
  exact literalDoubleConeOtherMap_desc M _ _ rfl

@[reassoc]
theorem ι₀_literalDifferenceCorrectionCylinder
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    SSet.ι₀ ≫ literalDifferenceCorrectionCylinder M A f H = f.map := by
  apply literalDoubleCone_hom_ext M
  · calc
      literalDoubleConeInnerMap M ≫ SSet.ι₀ ≫
          literalDifferenceCorrectionCylinder M A f H =
        SSet.ι₀ ≫ (literalDoubleConeInnerMap M ▷ Δ[1]) ≫
          literalDifferenceCorrectionCylinder M A f H := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ literalDifferenceCorrectionInner M A f H := by
        rw [literalDifferenceCorrectionCylinder,
          literalDoubleConeInnerMap_whisker_cylinderDesc]
      _ = literalDoubleConeInnerMap M ≫ f.map :=
        ι₀_literalDifferenceCorrectionInner M A f H
  · calc
      literalDoubleConeOtherMap M ≫ SSet.ι₀ ≫
          literalDifferenceCorrectionCylinder M A f H =
        SSet.ι₀ ≫ (literalDoubleConeOtherMap M ▷ Δ[1]) ≫
          literalDifferenceCorrectionCylinder M A f H := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ literalDifferenceCorrectionOther M A f := by
        rw [literalDifferenceCorrectionCylinder,
          literalDoubleConeOtherMap_whisker_cylinderDesc]
      _ = literalDoubleConeOtherMap M ≫ f.map :=
        ι₀_literalDifferenceCorrectionOther M A f

@[reassoc]
theorem ι₁_literalDifferenceCorrectionCylinder
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    SSet.ι₁ ≫ literalDifferenceCorrectionCylinder M A f H =
      (literalDiagonalMorphism M A f).map := by
  apply literalDoubleCone_hom_ext M
  · calc
      literalDoubleConeInnerMap M ≫ SSet.ι₁ ≫
          literalDifferenceCorrectionCylinder M A f H =
        SSet.ι₁ ≫ (literalDoubleConeInnerMap M ▷ Δ[1]) ≫
          literalDifferenceCorrectionCylinder M A f H := by
            rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ literalDifferenceCorrectionInner M A f H := by
        rw [literalDifferenceCorrectionCylinder,
          literalDoubleConeInnerMap_whisker_cylinderDesc]
      _ = literalDiagonalConeMap M A f :=
        ι₁_literalDifferenceCorrectionInner M A f H
      _ = literalDoubleConeInnerMap M ≫
          (literalDiagonalMorphism M A f).map :=
        (literalDoubleConeInnerMap_diagonal M A f).symm
  · calc
      literalDoubleConeOtherMap M ≫ SSet.ι₁ ≫
          literalDifferenceCorrectionCylinder M A f H =
        SSet.ι₁ ≫ (literalDoubleConeOtherMap M ▷ Δ[1]) ≫
          literalDifferenceCorrectionCylinder M A f H := by
            rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ literalDifferenceCorrectionOther M A f := by
        rw [literalDifferenceCorrectionCylinder,
          literalDoubleConeOtherMap_whisker_cylinderDesc]
      _ = literalDiagonalConeMap M A f :=
        ι₁_literalDifferenceCorrectionOther M A f
      _ = literalDoubleConeOtherMap M ≫
          (literalDiagonalMorphism M A f).map :=
        (literalDoubleConeOtherMap_diagonal M A f).symm

theorem literalDifferenceCorrectionCylinder_rel
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    ((literalDoubleConeApexSubcomplex M).ι ▷ Δ[1]) ≫
      literalDifferenceCorrectionCylinder M A f H = 0 := by
  have hu := literalDiagonalConeMap_apex_eq_zero
    (X := literalDoubleConeApexSubcomplex M) M A f
  have hother :
      (SSet.const (X := literalDoubleConeApexSubcomplex M)
          (literalConeApex M) ▷ Δ[1]) ≫
        literalDifferenceCorrectionOther M A f = 0 := by
    calc
      _ = fst (literalDoubleConeApexSubcomplex M : SSet) Δ[1] ≫
          SSet.const (literalConeApex M) ≫
          literalDiagonalConeMap M A f := by
        rw [literalDifferenceCorrectionOther, ← Category.assoc,
          whiskerRight_fst]
        simp only [Category.assoc]
      _ = fst (literalDoubleConeApexSubcomplex M : SSet) Δ[1] ≫
          (SSet.const (literalConeApex M) ≫
            literalDiagonalConeMap M A f) := rfl
      _ = 0 := by rw [hu]; ext Delta x; rfl
  have hapexFactor : (literalDoubleConeApexSubcomplex M).ι =
      SSet.const (X := literalDoubleConeApexSubcomplex M)
          (literalConeApex M) ≫ literalDoubleConeOtherMap M := by
    have hapexι : (literalDoubleConeApexSubcomplex M).ι =
        SSet.const (orderedComplexVertex (doubleConeBoundary M)
          (none : Option (Option V))) := by
      simpa only [literalDoubleConeApexSubcomplex,
        orderedComplexBasepointSubcomplex] using
        (SSet.Subcomplex.ofSimplex_ι
          (orderedComplexVertex (doubleConeBoundary M)
            (none : Option (Option V))))
    rw [hapexι, literalDoubleConeOtherMap_const_apex]
  calc
    _ = ((SSet.const (X := literalDoubleConeApexSubcomplex M)
            (literalConeApex M) ≫ literalDoubleConeOtherMap M) ▷ Δ[1]) ≫
          literalDifferenceCorrectionCylinder M A f H := by rw [hapexFactor]
    _ = (SSet.const (X := literalDoubleConeApexSubcomplex M)
            (literalConeApex M) ▷ Δ[1]) ≫
          (literalDoubleConeOtherMap M ▷ Δ[1]) ≫
          literalDifferenceCorrectionCylinder M A f H := by
            rw [comp_whiskerRight_assoc]
    _ = (SSet.const (X := literalDoubleConeApexSubcomplex M)
            (literalConeApex M) ▷ Δ[1]) ≫
          literalDifferenceCorrectionOther M A f := by
            rw [literalDifferenceCorrectionCylinder,
              literalDoubleConeOtherMap_whisker_cylinderDesc]
    _ = 0 := hother

def literalDifferenceCorrectionRelativeHomotopy
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
    (H : SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A 0)) :
    SSet.RelativeMorphism.Homotopy f (literalDiagonalMorphism M A f) where
  h := literalDifferenceCorrectionCylinder M A f H
  h₀ := ι₀_literalDifferenceCorrectionCylinder M A f H
  h₁ := ι₁_literalDifferenceCorrectionCylinder M A f H
  rel := by
    rw [literalDifferenceCorrectionCylinder_rel,
      cylinder_zeroBoundary]

/-! ## Pointed contraction of the diagonal -/

/-- The explicit literal-cone contraction fixes its apex throughout. -/
@[reassoc]
theorem literalConeApex_whisker_cylinderMap
    (X : SSet.{u}) :
    (SSet.const (X := X) (literalConeApex M) ▷ Δ[1]) ≫
        literalConeCylinderMap M =
      SSet.const (X := X ⊗ Δ[1]) (literalConeApex M) := by
  ext Delta z
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  change (if SSet.stdSimplex.asOrderHom z.2 i = 0
    then none else none) = none
  split <;> rfl

def literalDiagonalCylinder
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    orderedComplexSSet (doubleConeBoundary M) ⊗ Δ[1] ⟶
      underlyingSSet A :=
  literalDoubleConeCylinderDesc M
    (literalConeCylinderMap M ≫ literalDiagonalConeMap M A f)
    (literalConeCylinderMap M ≫ literalDiagonalConeMap M A f) rfl

@[reassoc]
theorem ι₀_literalDiagonalCylinder
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.ι₀ ≫ literalDiagonalCylinder M A f = 0 := by
  apply literalDoubleCone_hom_ext M
  · calc
      literalDoubleConeInnerMap M ≫ SSet.ι₀ ≫
          literalDiagonalCylinder M A f =
        SSet.ι₀ ≫ (literalDoubleConeInnerMap M ▷ Δ[1]) ≫
          literalDiagonalCylinder M A f := by rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ literalConeCylinderMap M ≫
          literalDiagonalConeMap M A f := by
        rw [literalDiagonalCylinder,
          literalDoubleConeInnerMap_whisker_cylinderDesc]
      _ = SSet.const (X := orderedComplexSSet (simplicialCone M))
          (literalConeApex M) ≫ literalDiagonalConeMap M A f := by
        rw [← Category.assoc, ι₀_literalConeCylinderMap]
      _ = 0 := literalDiagonalConeMap_apex_eq_zero M A f
      _ = literalDoubleConeInnerMap M ≫ 0 := by ext Delta x; rfl
  · calc
      literalDoubleConeOtherMap M ≫ SSet.ι₀ ≫
          literalDiagonalCylinder M A f =
        SSet.ι₀ ≫ (literalDoubleConeOtherMap M ▷ Δ[1]) ≫
          literalDiagonalCylinder M A f := by rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ literalConeCylinderMap M ≫
          literalDiagonalConeMap M A f := by
        rw [literalDiagonalCylinder,
          literalDoubleConeOtherMap_whisker_cylinderDesc]
      _ = SSet.const (X := orderedComplexSSet (simplicialCone M))
          (literalConeApex M) ≫ literalDiagonalConeMap M A f := by
        rw [← Category.assoc, ι₀_literalConeCylinderMap]
      _ = 0 := literalDiagonalConeMap_apex_eq_zero M A f
      _ = literalDoubleConeOtherMap M ≫ 0 := by ext Delta x; rfl

@[reassoc]
theorem ι₁_literalDiagonalCylinder
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.ι₁ ≫ literalDiagonalCylinder M A f =
      (literalDiagonalMorphism M A f).map := by
  apply literalDoubleCone_hom_ext M
  · calc
      literalDoubleConeInnerMap M ≫ SSet.ι₁ ≫
          literalDiagonalCylinder M A f =
        SSet.ι₁ ≫ (literalDoubleConeInnerMap M ▷ Δ[1]) ≫
          literalDiagonalCylinder M A f := by rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ literalConeCylinderMap M ≫
          literalDiagonalConeMap M A f := by
        rw [literalDiagonalCylinder,
          literalDoubleConeInnerMap_whisker_cylinderDesc]
      _ = literalDiagonalConeMap M A f := by
        rw [← Category.assoc, ι₁_literalConeCylinderMap,
          Category.id_comp]
      _ = literalDoubleConeInnerMap M ≫
          (literalDiagonalMorphism M A f).map :=
        (literalDoubleConeInnerMap_diagonal M A f).symm
  · calc
      literalDoubleConeOtherMap M ≫ SSet.ι₁ ≫
          literalDiagonalCylinder M A f =
        SSet.ι₁ ≫ (literalDoubleConeOtherMap M ▷ Δ[1]) ≫
          literalDiagonalCylinder M A f := by rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ literalConeCylinderMap M ≫
          literalDiagonalConeMap M A f := by
        rw [literalDiagonalCylinder,
          literalDoubleConeOtherMap_whisker_cylinderDesc]
      _ = literalDiagonalConeMap M A f := by
        rw [← Category.assoc, ι₁_literalConeCylinderMap,
          Category.id_comp]
      _ = literalDoubleConeOtherMap M ≫
          (literalDiagonalMorphism M A f).map :=
        (literalDoubleConeOtherMap_diagonal M A f).symm

theorem literalDiagonalCylinder_rel
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    ((literalDoubleConeApexSubcomplex M).ι ▷ Δ[1]) ≫
      literalDiagonalCylinder M A f = 0 := by
  have hapexFactor : (literalDoubleConeApexSubcomplex M).ι =
      SSet.const (X := literalDoubleConeApexSubcomplex M)
          (literalConeApex M) ≫ literalDoubleConeOtherMap M := by
    have hapexι : (literalDoubleConeApexSubcomplex M).ι =
        SSet.const (orderedComplexVertex (doubleConeBoundary M)
          (none : Option (Option V))) := by
      simpa only [literalDoubleConeApexSubcomplex,
        orderedComplexBasepointSubcomplex] using
        (SSet.Subcomplex.ofSimplex_ι
          (orderedComplexVertex (doubleConeBoundary M)
            (none : Option (Option V))))
    rw [hapexι, literalDoubleConeOtherMap_const_apex]
  calc
    _ = ((SSet.const (X := literalDoubleConeApexSubcomplex M)
            (literalConeApex M) ≫ literalDoubleConeOtherMap M) ▷ Δ[1]) ≫
          literalDiagonalCylinder M A f := by rw [hapexFactor]
    _ = (SSet.const (X := literalDoubleConeApexSubcomplex M)
            (literalConeApex M) ▷ Δ[1]) ≫
          (literalDoubleConeOtherMap M ▷ Δ[1]) ≫
          literalDiagonalCylinder M A f := by rw [comp_whiskerRight_assoc]
    _ = (SSet.const (X := literalDoubleConeApexSubcomplex M)
            (literalConeApex M) ▷ Δ[1]) ≫
          literalConeCylinderMap M ≫ literalDiagonalConeMap M A f := by
      rw [literalDiagonalCylinder,
        literalDoubleConeOtherMap_whisker_cylinderDesc]
    _ = SSet.const (X :=
          (literalDoubleConeApexSubcomplex M : SSet) ⊗ Δ[1])
          (literalConeApex M) ≫ literalDiagonalConeMap M A f := by
      rw [← Category.assoc, literalConeApex_whisker_cylinderMap]
    _ = 0 := literalDiagonalConeMap_apex_eq_zero M A f

def literalZeroToDiagonalRelativeHomotopy
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A)
      (literalDiagonalMorphism M A f) where
  h := literalDiagonalCylinder M A f
  h₀ := by
    rw [ι₀_literalDiagonalCylinder]
    rfl
  h₁ := ι₁_literalDiagonalCylinder M A f
  rel := by
    rw [literalDiagonalCylinder_rel, cylinder_zeroBoundary]

/-- A map whose two cone restrictions have the same relative homotopy
class is pointed-null on the literal double cone. -/
theorem literalTwoConeDifference_ker_le_nativeNullMaps :
    LinearMap.ker (literalTwoConeDifferenceLinear M A) ≤
      NativeNullMaps (literalDoubleConeApexSubcomplex M) A := by
  intro f hf
  have hclass :
      (literalTwoConeDifferenceMorphism M A f).homotopyClass =
        (literalTwoConeDifferenceMorphism M A 0).homotopyClass := by
    calc
      _ = literalTwoConeDifferenceLinear M A f := rfl
      _ = 0 := LinearMap.mem_ker.mp hf
      _ = literalTwoConeDifferenceLinear M A 0 :=
        (map_zero (literalTwoConeDifferenceLinear M A)).symm
      _ = _ := rfl
  rcases (homotopyClass_eq_iff (literalConeBottomSubcomplex M) A).mp
    hclass with ⟨H⟩
  let K : SSet.RelativeMorphism.Homotopy f
      (0 : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :=
    homotopyTrans (literalDoubleConeApexSubcomplex M) A
      (literalDifferenceCorrectionRelativeHomotopy M A f H)
      (homotopySymm (literalDoubleConeApexSubcomplex M) A
        (literalZeroToDiagonalRelativeHomotopy M A f))
  exact LinearMap.mem_ker.mpr <|
    K.eq.trans (homotopyClass_zero
      (literalDoubleConeApexSubcomplex M) A)

/-- Literal two-cone exactness: the kernel of inner-minus-other is exactly
the subgroup of pointed-null maps. -/
theorem literalTwoConeDifference_ker_eq_nativeNullMaps :
    LinearMap.ker (literalTwoConeDifferenceLinear M A) =
      NativeNullMaps (literalDoubleConeApexSubcomplex M) A :=
  le_antisymm
    (literalTwoConeDifference_ker_le_nativeNullMaps M A)
    (nativeNullMaps_le_literalTwoConeDifference_ker M A)

/-- Formula (4.25) in the literal model: a pointed map on the double cone
boundary is sent to its inner restriction minus its other restriction. -/
def literalTwoConeDifferenceEquiv :
    NativeHomotopyClass (literalDoubleConeApexSubcomplex M) A ≃ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M) A :=
  (quotientNativeNullEquiv (literalDoubleConeApexSubcomplex M) A).symm |>.trans
    ((Submodule.quotEquivOfEq
      (NativeNullMaps (literalDoubleConeApexSubcomplex M) A)
      (LinearMap.ker (literalTwoConeDifferenceLinear M A))
      (literalTwoConeDifference_ker_eq_nativeNullMaps M A).symm).trans
      ((literalTwoConeDifferenceLinear M A).quotKerEquivOfSurjective
        (literalTwoConeDifferenceLinear_surjective M A)))

@[simp]
theorem literalTwoConeDifferenceEquiv_homotopyClass
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    literalTwoConeDifferenceEquiv M A f.homotopyClass =
      (literalTwoConeDifferenceMorphism M A f).homotopyClass := by
  rw [literalTwoConeDifferenceEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply,
    ← quotientNativeNullEquiv_mkQ
      (literalDoubleConeApexSubcomplex M) A f,
    LinearEquiv.symm_apply_apply]
  have hmk : (NativeNullMaps (literalDoubleConeApexSubcomplex M) A).mkQ f =
      Submodule.Quotient.mk f := rfl
  rw [hmk, Submodule.quotEquivOfEq_mk]
  change ((literalTwoConeDifferenceLinear M A).quotKerEquivOfSurjective
      (literalTwoConeDifferenceLinear_surjective M A))
      ((LinearMap.ker (literalTwoConeDifferenceLinear M A)).mkQ f) =
    (literalTwoConeDifferenceMorphism M A f).homotopyClass
  have hkermk :
      (LinearMap.ker (literalTwoConeDifferenceLinear M A)).mkQ f =
        Submodule.Quotient.mk f := rfl
  rw [hkermk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end GeneralSphereT.SimplicialCochain
