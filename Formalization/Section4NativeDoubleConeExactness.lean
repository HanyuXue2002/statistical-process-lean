import Formalization.Section4NativeDoubleCone

set_option linter.style.header false

/-!
# Section 4: pointed null maps on the native double cone

This file puts the source-side notion of a pointed nullhomotopic suspension
map into the same native relative-homotopy model used by the two-cone
difference map.  It also proves the formal half of two-cone exactness: a
pointed nullhomotopy restricts to the two cone halves, and the difference of
those restrictions is a relative nullhomotopy on the cone pair.

The abstract proposition at the end of this file is retained only as a
compatibility interface for separating the two inclusions.  The public,
unconditional pointed result is proved in
`Section4NativeDoubleConeReverse`: it assumes exactly a chosen vertex of
`P`, which is necessary because the reverse inclusion is false when `P` is
empty.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory Limits

namespace GeneralSphereT.Section4
namespace NativeDoubleConeExactness

universe u

open UnderlyingSSet
open RelativeMapping
open NativeRelativeHomotopyGroup
open NativeSimplicialCone
open NativeDoubleCone

variable {X W : SSet.{u}}
variable (P : X.Subcomplex)
variable (A : SimplicialObject AddCommGrpCat.{u})

/-- Pointwise maximum on the simplicial interval.  It is the connection
used by the standard contraction of a cone towards its apex. -/
def intervalMax : Δ[1] ⊗ Δ[1] ⟶ Δ[1] where
  app Δ := ↾fun z ↦
    SSet.stdSimplex.objMk
      { toFun := fun i ↦
          max (((SSet.stdSimplex.objEquiv z.1).toOrderHom) i)
            (((SSet.stdSimplex.objEquiv z.2).toOrderHom) i)
        monotone' := fun _ _ hij ↦
          max_le_max
            ((SSet.stdSimplex.objEquiv z.1).toOrderHom.monotone hij)
            ((SSet.stdSimplex.objEquiv z.2).toOrderHom.monotone hij) }
  naturality _ _ θ := by
    ext z
    apply SSet.stdSimplex.objEquiv.injective
    ext i
    rfl

/-- If `P` contains a vertex, vanishing on the cone on `P` also forces the
cone apex to be sent to zero.  This is the precise place where the pointed
hypothesis rules out the empty-`P` counterexample. -/
theorem apex_comp_eq_zero_of_baseLine
    (p : (P : SSet).obj
      (Opposite.op (SimplexCategory.mk 0)))
    (f : cone X ⟶ underlyingSSet A)
    (hf : coneBaseLine P ≫ f = 0) :
    apexInclusion X ≫ f = 0 := by
  have hc : P.ι ≫ collapse X = collapse (P : SSet) :=
    SSet.stdSimplex.ext₀
  have htop :
      collapse (P : SSet) ≫ apexInclusion X =
        SSet.ι₁ ≫ coneBaseLine P := by
    calc
      collapse (P : SSet) ≫ apexInclusion X =
          (P.ι ≫ collapse X) ≫ apexInclusion X := by rw [hc]
      _ = P.ι ≫ (collapse X ≫ apexInclusion X) :=
        Category.assoc _ _ _
      _ = P.ι ≫ (SSet.ι₁ ≫ cylinderInclusion X) := by
        rw [end_glue]
      _ = P.ι ≫ SSet.ι₁ ≫ cylinderInclusion X :=
        (Category.assoc _ _ _).symm
      _ = SSet.ι₁ ≫ (P.ι ▷ Δ[1]) ≫ cylinderInclusion X := by
        rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ coneBaseLine P := rfl
  have hcollapse :
      collapse (P : SSet) ≫ apexInclusion X ≫ f = 0 := by
    rw [← Category.assoc, htop, Category.assoc, hf]
    ext Δ x
    rfl
  let baseSection : Δ[0] ⟶ (P : SSet) := SSet.const p
  have hsection : baseSection ≫ collapse (P : SSet) = 𝟙 Δ[0] :=
    SSet.stdSimplex.ext₀
  calc
    apexInclusion X ≫ f = 𝟙 Δ[0] ≫ (apexInclusion X ≫ f) :=
      (Category.id_comp _).symm
    _ = (baseSection ≫ collapse (P : SSet)) ≫
        (apexInclusion X ≫ f) := by rw [hsection]
    _ = baseSection ≫ (collapse (P : SSet) ≫ apexInclusion X ≫ f) := by
      simp only [Category.assoc]
    _ = baseSection ≫ 0 := by rw [hcollapse]
    _ = 0 := by ext Δ x; rfl

/-- The pointed subcomplex of the suspension: the two copies of the cone on
`P`. -/
abbrev pointedSuspensionBoundary :
    (suspension X).Subcomplex :=
  SSet.Subcomplex.range
      (coneBaseLine P ≫ lowerConeInclusion X) ⊔
    SSet.Subcomplex.range
      (coneBaseLine P ≫ upperConeInclusion X)

/-- A pointed suspension map, regarded as a strictly-zero relative map for
the pointed suspension pair. -/
def pointedSuspensionRelativeZeroMap
    (F : PointedSuspensionMaps P A) :
    RelativeZeroMaps (pointedSuspensionBoundary P) A := by
  refine ⟨F.1, ?_⟩
  change (pointedSuspensionBoundary P).ι ≫ F.1 = 0
  ext Δ x
  rcases x.2 with hx | hx
  · rcases hx with ⟨y, hy⟩
    change F.1.app Δ x.1 = 0
    rw [← hy]
    have hlow :
        coneBaseLine P ≫ lowerConeInclusion X ≫ F.1 = 0 :=
      LinearMap.mem_ker.mp F.2.1
    exact ConcreteCategory.congr_hom (congr_app hlow Δ) y
  · rcases hx with ⟨y, hy⟩
    change F.1.app Δ x.1 = 0
    rw [← hy]
    have hupp :
        coneBaseLine P ≫ upperConeInclusion X ≫ F.1 = 0 :=
      LinearMap.mem_ker.mp F.2.2
    exact ConcreteCategory.congr_hom (congr_app hupp Δ) y

/-- The identification of pointed maps with strict relative maps is
additive. -/
def pointedSuspensionRelativeZeroHom :
    PointedSuspensionMaps P A →+
      RelativeZeroMaps (pointedSuspensionBoundary P) A where
  toFun := pointedSuspensionRelativeZeroMap P A
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/-- A strict relative map for the pointed suspension pair is, conversely,
a pointed suspension map. -/
def relativeZeroMapToPointedSuspension
    (f : RelativeZeroMaps (pointedSuspensionBoundary P) A) :
    PointedSuspensionMaps P A := by
  refine ⟨f.1, ?_, ?_⟩
  · exact comp_eq_zero_of_range_le A
      (coneBaseLine P ≫ lowerConeInclusion X) le_sup_left f
  · exact comp_eq_zero_of_range_le A
      (coneBaseLine P ≫ upperConeInclusion X) le_sup_right f

/-- Pointed suspension maps are exactly the strict relative maps of the
pointed suspension pair. -/
def pointedSuspensionMapsEquivRelativeZeroMaps :
    PointedSuspensionMaps P A ≃+
      RelativeZeroMaps (pointedSuspensionBoundary P) A where
  toFun := pointedSuspensionRelativeZeroMap P A
  invFun := relativeZeroMapToPointedSuspension P A
  left_inv _ := by
    apply Subtype.ext
    rfl
  right_inv _ := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/-- The identification of pointed maps with strict relative maps as a
`ℤ`-linear map. -/
def pointedSuspensionRelativeZeroLinear :
    PointedSuspensionMaps P A →ₗ[ℤ]
      RelativeZeroMaps (pointedSuspensionBoundary P) A :=
  (pointedSuspensionRelativeZeroHom P A).toIntLinearMap

/-- The actual pointed homotopy class of a pointed suspension map. -/
def pointedSuspensionHomotopyClassLinear :
    PointedSuspensionMaps P A →ₗ[ℤ]
      NativeHomotopyClass (pointedSuspensionBoundary P) A :=
  (strictHomotopyClassLinear (pointedSuspensionBoundary P) A).comp
    (pointedSuspensionRelativeZeroLinear P A)

/-- Pointed suspension maps which are genuinely nullhomotopic relative to
the two copies of the cone on `P`. -/
abbrev PointedSuspensionNullMaps :
    Submodule ℤ (PointedSuspensionMaps P A) :=
  LinearMap.ker (pointedSuspensionHomotopyClassLinear P A)

@[simp]
theorem pointedSuspensionHomotopyClassLinear_apply
    (F : PointedSuspensionMaps P A) :
    pointedSuspensionHomotopyClassLinear P A F =
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A F)).homotopyClass :=
  rfl

/-! ## Restricting a pointed nullhomotopy to the cone pair -/

/-- A relative homotopy is zero after restriction along a map whose range
lies in the relative subcomplex. -/
theorem whisker_comp_relativeHomotopy_eq_zero_of_range_le
    {Y Z : SSet.{u}} {Q : Y.Subcomplex}
    (k : Z ⟶ Y) (hk : SSet.Subcomplex.range k ≤ Q)
    {f g : NativeRelativeMorphism Q A}
    (H : SSet.RelativeMorphism.Homotopy f g) :
    (k ▷ Δ[1]) ≫ H.h = 0 := by
  let klift : Z ⟶ (Q : SSet) := Q.lift k hk
  have hQ : Q.ι ▷ Δ[1] ≫ H.h = 0 := by
    rw [H.rel]
    exact cylinder_zeroBoundary Q A
  calc
    (k ▷ Δ[1]) ≫ H.h =
        ((klift ≫ Q.ι) ▷ Δ[1]) ≫ H.h := by
      rw [Q.lift_ι]
    _ = (klift ▷ Δ[1]) ≫ (Q.ι ▷ Δ[1]) ≫ H.h := by
      rw [comp_whiskerRight_assoc]
    _ = (klift ▷ Δ[1]) ≫ 0 := by rw [hQ]
    _ = 0 := by ext Δ x; rfl

/-- Restrict a pointed suspension homotopy to the lower and upper cones and
subtract.  The common equator cancels, while pointedness makes the two
copies of `P ⊗ Δ[1]` vanish separately. -/
def differenceHomotopy
    {F G : PointedSuspensionMaps P A}
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A G))) :
    SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A G)) where
  h :=
    ((lowerConeInclusion X ▷ Δ[1]) ≫ H.h) -
      ((upperConeInclusion X ▷ Δ[1]) ≫ H.h)
  h₀ := by
    rw [NativeRelativeHomotopyGroup.comp_subMap]
    have hlow :
        SSet.ι₀ ≫ (lowerConeInclusion X ▷ Δ[1]) ≫ H.h =
          lowerConeInclusion X ≫ F.1 := by
      calc
        _ = lowerConeInclusion X ≫ SSet.ι₀ ≫ H.h := by
          rw [SSet.ι₀_comp_assoc]
        _ = lowerConeInclusion X ≫ F.1 := by
          rw [H.h₀]
          rfl
    have hupp :
        SSet.ι₀ ≫ (upperConeInclusion X ▷ Δ[1]) ≫ H.h =
          upperConeInclusion X ≫ F.1 := by
      calc
        _ = upperConeInclusion X ≫ SSet.ι₀ ≫ H.h := by
          rw [SSet.ι₀_comp_assoc]
        _ = upperConeInclusion X ≫ F.1 := by
          rw [H.h₀]
          rfl
    rw [hlow, hupp]
    rfl
  h₁ := by
    rw [NativeRelativeHomotopyGroup.comp_subMap]
    have hlow :
        SSet.ι₁ ≫ (lowerConeInclusion X ▷ Δ[1]) ≫ H.h =
          lowerConeInclusion X ≫ G.1 := by
      calc
        _ = lowerConeInclusion X ≫ SSet.ι₁ ≫ H.h := by
          rw [SSet.ι₁_comp_assoc]
        _ = lowerConeInclusion X ≫ G.1 := by
          rw [H.h₁]
          rfl
    have hupp :
        SSet.ι₁ ≫ (upperConeInclusion X ▷ Δ[1]) ≫ H.h =
          upperConeInclusion X ≫ G.1 := by
      calc
        _ = upperConeInclusion X ≫ SSet.ι₁ ≫ H.h := by
          rw [SSet.ι₁_comp_assoc]
        _ = upperConeInclusion X ≫ G.1 := by
          rw [H.h₁]
          rfl
    rw [hlow, hupp]
    rfl
  rel := by
    let hdiff : (cone X ⊗ Δ[1]) ⟶ underlyingSSet A :=
      ((lowerConeInclusion X ▷ Δ[1]) ≫ H.h) -
        ((upperConeInclusion X ▷ Δ[1]) ≫ H.h)
    have hbottom :
        (bottomInclusion X ▷ Δ[1]) ≫ hdiff = 0 := by
      change (bottomInclusion X ▷ Δ[1]) ≫
          (((lowerConeInclusion X ▷ Δ[1]) ≫ H.h) -
            ((upperConeInclusion X ▷ Δ[1]) ≫ H.h)) = 0
      rw [NativeRelativeHomotopyGroup.comp_subMap]
      have heq :
          (bottomInclusion X ▷ Δ[1]) ≫
              (lowerConeInclusion X ▷ Δ[1]) ≫ H.h =
            (bottomInclusion X ▷ Δ[1]) ≫
              (upperConeInclusion X ▷ Δ[1]) ≫ H.h := by
        calc
          _ = ((bottomInclusion X ≫ lowerConeInclusion X) ▷ Δ[1]) ≫
              H.h := by rw [comp_whiskerRight_assoc]
          _ = ((bottomInclusion X ≫ upperConeInclusion X) ▷ Δ[1]) ≫
              H.h := by rw [equator_glue]
          _ = _ := by rw [comp_whiskerRight_assoc]
      rw [heq, sub_self]
    have hbase :
        (coneBaseLine P ▷ Δ[1]) ≫ hdiff = 0 := by
      change (coneBaseLine P ▷ Δ[1]) ≫
          (((lowerConeInclusion X ▷ Δ[1]) ≫ H.h) -
            ((upperConeInclusion X ▷ Δ[1]) ≫ H.h)) = 0
      rw [NativeRelativeHomotopyGroup.comp_subMap]
      have hlow :
          (coneBaseLine P ▷ Δ[1]) ≫
              (lowerConeInclusion X ▷ Δ[1]) ≫ H.h = 0 := by
        calc
          _ = ((coneBaseLine P ≫ lowerConeInclusion X) ▷ Δ[1]) ≫
              H.h := by rw [comp_whiskerRight_assoc]
          _ = 0 := whisker_comp_relativeHomotopy_eq_zero_of_range_le A
            (coneBaseLine P ≫ lowerConeInclusion X) le_sup_left H
      have hupp :
          (coneBaseLine P ▷ Δ[1]) ≫
              (upperConeInclusion X ▷ Δ[1]) ≫ H.h = 0 := by
        calc
          _ = ((coneBaseLine P ≫ upperConeInclusion X) ▷ Δ[1]) ≫
              H.h := by rw [comp_whiskerRight_assoc]
          _ = 0 := whisker_comp_relativeHomotopy_eq_zero_of_range_le A
            (coneBaseLine P ≫ upperConeInclusion X) le_sup_right H
      rw [hlow, hupp, sub_self]
    change (conePairBoundary P).ι ▷ Δ[1] ≫ hdiff =
      fst (conePairBoundary P : SSet) Δ[1] ≫
        zeroBoundary (conePairBoundary P) A ≫ (zeroSubcomplex A).ι
    rw [cylinder_zeroBoundary]
    ext Δ x
    rcases x.1.2 with hx | hx
    · rcases hx with ⟨y, hy⟩
      change hdiff.app Δ (x.1.1, x.2) = 0
      rw [← hy]
      have hbΔ := congr_app hbottom Δ
      have hbfun := ConcreteCategory.congr_hom hbΔ
      exact hbfun (y, x.2)
    · rcases hx with ⟨y, hy⟩
      change hdiff.app Δ (x.1.1, x.2) = 0
      rw [← hy]
      have hpΔ := congr_app hbase Δ
      have hpfun := ConcreteCategory.congr_hom hpΔ
      exact hpfun (y, x.2)

/-- The formal half of two-cone exactness: every genuinely pointed-null
suspension map has null lower-minus-upper cone difference. -/
theorem PointedSuspensionNullMaps_le_twoConeDifference_ker :
    PointedSuspensionNullMaps P A ≤
      LinearMap.ker (twoConeDifferenceLinear P A) := by
  intro F hF
  have hclass :
      pointedSuspensionHomotopyClassLinear P A F =
        pointedSuspensionHomotopyClassLinear P A 0 := by
    calc
      pointedSuspensionHomotopyClassLinear P A F = 0 :=
        LinearMap.mem_ker.mp hF
      _ = pointedSuspensionHomotopyClassLinear P A 0 :=
        (map_zero (pointedSuspensionHomotopyClassLinear P A)).symm
  change
    (RelativeZeroMaps.toRelativeMorphism
      (pointedSuspensionBoundary P) A
      (pointedSuspensionRelativeZeroMap P A F)).homotopyClass =
    (RelativeZeroMaps.toRelativeMorphism
      (pointedSuspensionBoundary P) A
      (pointedSuspensionRelativeZeroMap P A 0)).homotopyClass at hclass
  rcases (homotopyClass_eq_iff (pointedSuspensionBoundary P) A).mp hclass with
    ⟨H⟩
  have hd := (differenceHomotopy P A H).eq
  change twoConeDifferenceLinear P A F =
    twoConeDifferenceLinear P A 0 at hd
  exact LinearMap.mem_ker.mpr (by simpa using hd)

theorem mem_twoConeDifference_ker_of_pointed_null
    {F : PointedSuspensionMaps P A}
    (hF : F ∈ PointedSuspensionNullMaps P A) :
    F ∈ LinearMap.ker (twoConeDifferenceLinear P A) :=
  PointedSuspensionNullMaps_le_twoConeDifference_ker P A hF

/-! ## Compatibility interface for the reverse inclusion

The reverse inclusion is geometric.  It is false for an empty `P`: then a
nonzero constant suspension map has zero two-cone difference but need not
lie in the zero component of the mapping space.  The definitions below keep
the older conditional API available internally.  In the pointed
application one should instead import `Section4NativeDoubleConeReverse` and
use the theorems there with an actual vertex `p : P _`; that module proves
this property by the explicit cone contraction. -/

/-- Exact model-level content of the reverse half of two-cone/cofiber
exactness: a pointed suspension map with null relative difference admits an
actual pointed nullhomotopy. -/
def TwoConeKernelNullhomotopy : Prop :=
  ∀ F : PointedSuspensionMaps P A,
    twoConeDifferenceLinear P A F = 0 →
      Nonempty (SSet.RelativeMorphism.Homotopy
        (RelativeZeroMaps.toRelativeMorphism
          (pointedSuspensionBoundary P) A
          (pointedSuspensionRelativeZeroMap P A F))
        (RelativeZeroMaps.toRelativeMorphism
          (pointedSuspensionBoundary P) A
          (pointedSuspensionRelativeZeroMap P A 0)))

/-- The isolated cofiber assertion is exactly the missing reverse
submodule inclusion. -/
theorem twoConeKernelNullhomotopy_iff_reverse_inclusion :
    TwoConeKernelNullhomotopy P A ↔
      LinearMap.ker (twoConeDifferenceLinear P A) ≤
        PointedSuspensionNullMaps P A := by
  constructor
  · intro hcofiber F hF
    have hzero : twoConeDifferenceLinear P A F = 0 :=
      LinearMap.mem_ker.mp hF
    rcases hcofiber F hzero with ⟨H⟩
    apply LinearMap.mem_ker.mpr
    change
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A F)).homotopyClass = 0
    calc
      _ = (RelativeZeroMaps.toRelativeMorphism
          (pointedSuspensionBoundary P) A
          (pointedSuspensionRelativeZeroMap P A 0)).homotopyClass := H.eq
      _ = pointedSuspensionHomotopyClassLinear P A 0 := rfl
      _ = 0 := map_zero (pointedSuspensionHomotopyClassLinear P A)
  · intro hreverse F hF
    have hmem : F ∈ LinearMap.ker (twoConeDifferenceLinear P A) :=
      LinearMap.mem_ker.mpr hF
    have hnull := hreverse hmem
    have hclass :
        pointedSuspensionHomotopyClassLinear P A F =
          pointedSuspensionHomotopyClassLinear P A 0 := by
      calc
        pointedSuspensionHomotopyClassLinear P A F = 0 :=
          LinearMap.mem_ker.mp hnull
        _ = pointedSuspensionHomotopyClassLinear P A 0 :=
          (map_zero (pointedSuspensionHomotopyClassLinear P A)).symm
    change
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A F)).homotopyClass =
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A 0)).homotopyClass at hclass
    exact (homotopyClass_eq_iff (pointedSuspensionBoundary P) A).mp hclass

/-- Compatibility form of the full kernel identification, conditional on
an explicitly supplied cofiber-nullhomotopy assertion.  The public pointed
form takes a vertex of `P` instead. -/
theorem twoConeDifference_ker_eq_pointedSuspensionNullMaps
    (hcofiber : TwoConeKernelNullhomotopy P A) :
    LinearMap.ker (twoConeDifferenceLinear P A) =
      PointedSuspensionNullMaps P A := by
  apply le_antisymm
  · exact (twoConeKernelNullhomotopy_iff_reverse_inclusion P A).mp hcofiber
  · exact PointedSuspensionNullMaps_le_twoConeDifference_ker P A

/-- Compatibility form of the quotient comparison, conditional on an
explicit cofiber-nullhomotopy assertion.  The public pointed form takes a
vertex of `P` instead. -/
def quotientPointedSuspensionNullEquiv
    (hcofiber : TwoConeKernelNullhomotopy P A) :
    (PointedSuspensionMaps P A ⧸ PointedSuspensionNullMaps P A) ≃ₗ[ℤ]
      NativeHomotopyClass (conePairBoundary P) A :=
  (Submodule.quotEquivOfEq
      (PointedSuspensionNullMaps P A)
      (LinearMap.ker (twoConeDifferenceLinear P A))
      (twoConeDifference_ker_eq_pointedSuspensionNullMaps
        P A hcofiber).symm).trans
    (quotientTwoConeKernelEquiv P A)

@[simp]
theorem quotientPointedSuspensionNullEquiv_mkQ
    (hcofiber : TwoConeKernelNullhomotopy P A)
    (F : PointedSuspensionMaps P A) :
    quotientPointedSuspensionNullEquiv P A hcofiber
        ((PointedSuspensionNullMaps P A).mkQ F) =
      twoConeDifferenceLinear P A F := by
  have hmk : (PointedSuspensionNullMaps P A).mkQ F =
      Submodule.Quotient.mk F := rfl
  rw [hmk, quotientPointedSuspensionNullEquiv,
    LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  change quotientTwoConeKernelEquiv P A
      ((LinearMap.ker (twoConeDifferenceLinear P A)).mkQ F) =
    twoConeDifferenceLinear P A F
  exact quotientTwoConeKernelEquiv_mkQ P A F

end NativeDoubleConeExactness
end GeneralSphereT.Section4
