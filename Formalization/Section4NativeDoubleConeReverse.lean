import Formalization.Section4NativeDoubleConeExactness
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

set_option linter.style.header false

/-!
# Section 4: the reverse half of native two-cone exactness

This file proves the geometric assertion isolated in
`Section4NativeDoubleConeExactness`.  The only necessary hypothesis is that
the pointed subcomplex contains an actual vertex; without it the assertion
is false for the empty subcomplex.  Its final declarations are re-exported
in the `NativeDoubleConeExactness` namespace, so the completed public API
requires a vertex rather than an abstract cofiber hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory Limits

namespace GeneralSphereT.Section4
namespace NativeDoubleConeReverse

universe u

open UnderlyingSSet
open RelativeMapping
open NativeRelativeHomotopyGroup
open NativeSimplicialCone
open NativeDoubleCone
open NativeDoubleConeExactness

variable {X : SSet.{u}}

/-! ## The native categorical cone contracts to its apex -/

/-- Tensoring the defining pushout of the cone with the interval gives the
pushout of the tensor products. -/
def coneCylinderPushoutIso :
    pushout (SSet.ι₁ ▷ Δ[1]) (collapse X ▷ Δ[1]) ≅
      cone X ⊗ Δ[1] :=
  PreservesPushout.iso (tensorRight Δ[1])
    (SSet.ι₁ : X ⟶ X ⊗ Δ[1]) (collapse X)

/-- On a double interval, move towards the apex by taking the maximum of
the cone coordinate and the homotopy coordinate. -/
def coneCylinderMaxBranch :
    (X ⊗ Δ[1]) ⊗ Δ[1] ⟶ cone X :=
  (α_ X Δ[1] Δ[1]).hom ≫
    (X ◁ intervalMax) ≫ cylinderInclusion X

/-- The apex branch of the cone contraction. -/
def coneCylinderApexBranch :
    Δ[0] ⊗ Δ[1] ⟶ cone X :=
  fst Δ[0] Δ[1] ≫ apexInclusion X

/-- At the collapsed end of the cone cylinder, taking `max` stays at that
end. -/
theorem coneCylinderMax_at_top :
    (SSet.ι₁ ▷ Δ[1]) ≫ (α_ X Δ[1] Δ[1]).hom ≫
        (X ◁ intervalMax) =
      fst X Δ[1] ≫ SSet.ι₁ := by
  ext Δ z
  · rfl
  · change
      (intervalMax.app Δ).hom
          (((SSet.ι₁.app Δ).hom z.1).2, z.2) =
        ((SSet.ι₁.app Δ).hom z.1).2
    dsimp only [intervalMax]
    apply SSet.stdSimplex.objEquiv.injective
    ext i
    change
      (max
        (SSet.stdSimplex.asOrderHom
          ((SSet.ι₁.app Δ).hom z.1).2 i)
        (SSet.stdSimplex.asOrderHom z.2 i)).val =
      (SSet.stdSimplex.asOrderHom
        ((SSet.ι₁.app Δ).hom z.1).2 i).val
    have htop :
        SSet.stdSimplex.asOrderHom
          ((SSet.ι₁.app Δ).hom z.1).2 i = 1 :=
      SSet.ι₁_app_snd_apply z.1 i
    rw [htop]
    have ht :
        SSet.stdSimplex.asOrderHom z.2 i ≤ (1 : Fin 2) :=
      Fin.le_last _
    exact congrArg Fin.val (max_eq_left ht)

/-- The two branches defining the cone contraction agree along the
collapsed end. -/
theorem coneCylinderBranches_compatible :
    (SSet.ι₁ ▷ Δ[1]) ≫ coneCylinderMaxBranch (X := X) =
      (collapse X ▷ Δ[1]) ≫ coneCylinderApexBranch (X := X) := by
  calc
    (SSet.ι₁ ▷ Δ[1]) ≫ coneCylinderMaxBranch (X := X) =
        ((SSet.ι₁ ▷ Δ[1]) ≫ (α_ X Δ[1] Δ[1]).hom ≫
          (X ◁ intervalMax)) ≫ cylinderInclusion X := rfl
    _ = (fst X Δ[1] ≫ SSet.ι₁) ≫ cylinderInclusion X := by
      rw [coneCylinderMax_at_top]
    _ = fst X Δ[1] ≫ collapse X ≫ apexInclusion X := by
      rw [Category.assoc, end_glue]
    _ = ((collapse X ▷ Δ[1]) ≫ fst Δ[0] Δ[1]) ≫
        apexInclusion X := by
      rw [whiskerRight_fst]
      exact (Category.assoc _ _ _).symm
    _ = (collapse X ▷ Δ[1]) ≫
        (fst Δ[0] Δ[1] ≫ apexInclusion X) := by
      rw [Category.assoc]
    _ = (collapse X ▷ Δ[1]) ≫
        coneCylinderApexBranch (X := X) := rfl

/-- The actual contraction map of the native categorical cone. -/
def coneContractionMap : cone X ⊗ Δ[1] ⟶ cone X :=
  (coneCylinderPushoutIso (X := X)).inv ≫
    pushout.desc
      (coneCylinderMaxBranch (X := X))
      (coneCylinderApexBranch (X := X))
      coneCylinderBranches_compatible

@[reassoc]
theorem cylinderInclusion_whisker_coneContractionMap :
    (cylinderInclusion X ▷ Δ[1]) ≫ coneContractionMap (X := X) =
      coneCylinderMaxBranch (X := X) := by
  change (tensorRight Δ[1]).map
      (pushout.inl (SSet.ι₁ : X ⟶ X ⊗ Δ[1]) (collapse X)) ≫
      (coneCylinderPushoutIso (X := X)).inv ≫
      pushout.desc _ _ _ = _
  rw [coneCylinderPushoutIso,
    PreservesPushout.inl_iso_inv_assoc, pushout.inl_desc]

@[reassoc]
theorem apexInclusion_whisker_coneContractionMap :
    (apexInclusion X ▷ Δ[1]) ≫ coneContractionMap (X := X) =
      coneCylinderApexBranch (X := X) := by
  change (tensorRight Δ[1]).map
      (pushout.inr (SSet.ι₁ : X ⟶ X ⊗ Δ[1]) (collapse X)) ≫
      (coneCylinderPushoutIso (X := X)).inv ≫
      pushout.desc _ _ _ = _
  rw [coneCylinderPushoutIso,
    PreservesPushout.inr_iso_inv_assoc, pushout.inr_desc]

/-- At homotopy time zero, the maximum leaves the cone coordinate
unchanged. -/
theorem coneCylinderMax_at_zero :
    SSet.ι₀ ≫ (α_ X Δ[1] Δ[1]).hom ≫
        (X ◁ intervalMax) =
      𝟙 (X ⊗ Δ[1]) := by
  ext Δ z
  · rfl
  · change
      (intervalMax.app Δ).hom
          (z.2, ((SSet.ι₀.app Δ).hom z).2) = z.2
    dsimp only [intervalMax]
    apply SSet.stdSimplex.objEquiv.injective
    ext i
    change
      (max
        (SSet.stdSimplex.asOrderHom z.2 i)
        (SSet.stdSimplex.asOrderHom
          ((SSet.ι₀.app Δ).hom z).2 i)).val =
      (SSet.stdSimplex.asOrderHom z.2 i).val
    have hzero :
        SSet.stdSimplex.asOrderHom
          ((SSet.ι₀.app Δ).hom z).2 i = 0 :=
      SSet.ι₀_app_snd_apply z i
    rw [hzero]
    have hz : (0 : Fin 2) ≤ SSet.stdSimplex.asOrderHom z.2 i :=
      Fin.zero_le _
    exact congrArg Fin.val (max_eq_left hz)

/-- At homotopy time one, the maximum sends the cone coordinate to its
top endpoint. -/
theorem coneCylinderMax_at_one :
    SSet.ι₁ ≫ (α_ X Δ[1] Δ[1]).hom ≫
        (X ◁ intervalMax) =
      fst X Δ[1] ≫ SSet.ι₁ := by
  ext Δ z
  · rfl
  · change
      (intervalMax.app Δ).hom
          (z.2, ((SSet.ι₁.app Δ).hom z).2) =
        ((SSet.ι₁.app Δ).hom z.1).2
    dsimp only [intervalMax]
    apply SSet.stdSimplex.objEquiv.injective
    ext i
    change
      (max
        (SSet.stdSimplex.asOrderHom z.2 i)
        (SSet.stdSimplex.asOrderHom
          ((SSet.ι₁.app Δ).hom z).2 i)).val =
      (SSet.stdSimplex.asOrderHom
        ((SSet.ι₁.app Δ).hom z.1).2 i).val
    have htop₁ :
        SSet.stdSimplex.asOrderHom
          ((SSet.ι₁.app Δ).hom z).2 i = 1 :=
      SSet.ι₁_app_snd_apply z i
    have htop₂ :
        SSet.stdSimplex.asOrderHom
          ((SSet.ι₁.app Δ).hom z.1).2 i = 1 :=
      SSet.ι₁_app_snd_apply z.1 i
    rw [htop₁, htop₂]
    have hz : SSet.stdSimplex.asOrderHom z.2 i ≤ (1 : Fin 2) :=
      Fin.le_last _
    exact congrArg Fin.val (max_eq_right hz)

@[reassoc]
theorem ι₀_coneCylinderMaxBranch :
    SSet.ι₀ ≫ coneCylinderMaxBranch (X := X) =
      cylinderInclusion X := by
  calc
    SSet.ι₀ ≫ coneCylinderMaxBranch (X := X) =
        (SSet.ι₀ ≫ (α_ X Δ[1] Δ[1]).hom ≫
          (X ◁ intervalMax)) ≫ cylinderInclusion X := rfl
    _ = 𝟙 (X ⊗ Δ[1]) ≫ cylinderInclusion X := by
      rw [coneCylinderMax_at_zero]
    _ = cylinderInclusion X := Category.id_comp _

@[reassoc]
theorem ι₁_coneCylinderMaxBranch :
    SSet.ι₁ ≫ coneCylinderMaxBranch (X := X) =
      collapse (X ⊗ Δ[1]) ≫ apexInclusion X := by
  have hcollapse :
      fst X Δ[1] ≫ collapse X = collapse (X ⊗ Δ[1]) :=
    SSet.stdSimplex.ext₀
  calc
    SSet.ι₁ ≫ coneCylinderMaxBranch (X := X) =
        (SSet.ι₁ ≫ (α_ X Δ[1] Δ[1]).hom ≫
          (X ◁ intervalMax)) ≫ cylinderInclusion X := rfl
    _ = (fst X Δ[1] ≫ SSet.ι₁) ≫ cylinderInclusion X := by
      rw [coneCylinderMax_at_one]
    _ = fst X Δ[1] ≫ collapse X ≫ apexInclusion X := by
      rw [Category.assoc, end_glue]
    _ = collapse (X ⊗ Δ[1]) ≫ apexInclusion X := by
      rw [← Category.assoc, hcollapse]

@[reassoc]
theorem ι₀_coneCylinderApexBranch :
    SSet.ι₀ ≫ coneCylinderApexBranch (X := X) =
      apexInclusion X := by
  change SSet.ι₀ ≫ fst Δ[0] Δ[1] ≫ apexInclusion X = _
  rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]

@[reassoc]
theorem ι₁_coneCylinderApexBranch :
    SSet.ι₁ ≫ coneCylinderApexBranch (X := X) =
      apexInclusion X := by
  change SSet.ι₁ ≫ fst Δ[0] Δ[1] ≫ apexInclusion X = _
  rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- The zero endpoint of the cone contraction is the identity. -/
@[reassoc]
theorem ι₀_coneContractionMap :
    SSet.ι₀ ≫ coneContractionMap (X := X) = 𝟙 (cone X) := by
  apply pushout.hom_ext
  · calc
      cylinderInclusion X ≫ SSet.ι₀ ≫ coneContractionMap (X := X) =
          SSet.ι₀ ≫ (cylinderInclusion X ▷ Δ[1]) ≫
            coneContractionMap (X := X) := by
        rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ coneCylinderMaxBranch (X := X) := by
        rw [cylinderInclusion_whisker_coneContractionMap]
      _ = cylinderInclusion X := ι₀_coneCylinderMaxBranch
      _ = cylinderInclusion X ≫ 𝟙 (cone X) :=
        (Category.comp_id _).symm
  · calc
      apexInclusion X ≫ SSet.ι₀ ≫ coneContractionMap (X := X) =
          SSet.ι₀ ≫ (apexInclusion X ▷ Δ[1]) ≫
            coneContractionMap (X := X) := by
        rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ coneCylinderApexBranch (X := X) := by
        rw [apexInclusion_whisker_coneContractionMap]
      _ = apexInclusion X := ι₀_coneCylinderApexBranch
      _ = apexInclusion X ≫ 𝟙 (cone X) :=
        (Category.comp_id _).symm

/-- The one endpoint of the cone contraction is the constant apex map. -/
@[reassoc]
theorem ι₁_coneContractionMap :
    SSet.ι₁ ≫ coneContractionMap (X := X) =
      collapse (cone X) ≫ apexInclusion X := by
  apply pushout.hom_ext
  · have hcollapse :
        cylinderInclusion X ≫ collapse (cone X) =
          collapse (X ⊗ Δ[1]) :=
      SSet.stdSimplex.ext₀
    calc
      cylinderInclusion X ≫ SSet.ι₁ ≫ coneContractionMap (X := X) =
          SSet.ι₁ ≫ (cylinderInclusion X ▷ Δ[1]) ≫
            coneContractionMap (X := X) := by
        rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ coneCylinderMaxBranch (X := X) := by
        rw [cylinderInclusion_whisker_coneContractionMap]
      _ = collapse (X ⊗ Δ[1]) ≫ apexInclusion X :=
        ι₁_coneCylinderMaxBranch
      _ = cylinderInclusion X ≫
          (collapse (cone X) ≫ apexInclusion X) := by
        rw [← Category.assoc, hcollapse]
  · have hcollapse :
        apexInclusion X ≫ collapse (cone X) = 𝟙 Δ[0] :=
      SSet.stdSimplex.ext₀
    calc
      apexInclusion X ≫ SSet.ι₁ ≫ coneContractionMap (X := X) =
          SSet.ι₁ ≫ (apexInclusion X ▷ Δ[1]) ≫
            coneContractionMap (X := X) := by
        rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ coneCylinderApexBranch (X := X) := by
        rw [apexInclusion_whisker_coneContractionMap]
      _ = apexInclusion X := ι₁_coneCylinderApexBranch
      _ = apexInclusion X ≫
          (collapse (cone X) ≫ apexInclusion X) := by
        rw [← Category.assoc, hcollapse, Category.id_comp]

/-! ## Relative contraction of a cone map -/

variable (P : X.Subcomplex)

/-- The same maximum operation on the copy of `P ⊗ Δ[1]`. -/
def baseLineContractionMap :
    ((P : SSet) ⊗ Δ[1]) ⊗ Δ[1] ⟶ (P : SSet) ⊗ Δ[1] :=
  (α_ (P : SSet) Δ[1] Δ[1]).hom ≫
    ((P : SSet) ◁ intervalMax)

/-- The cone contraction preserves the whole cone on `P`, not merely its
bottom copy. -/
@[reassoc]
theorem coneBaseLine_whisker_coneContractionMap :
    (coneBaseLine P ▷ Δ[1]) ≫ coneContractionMap (X := X) =
      baseLineContractionMap P ≫ coneBaseLine P := by
  rw [coneBaseLine, comp_whiskerRight_assoc,
    cylinderInclusion_whisker_coneContractionMap]
  ext Δ z
  rfl

variable (A : SimplicialObject AddCommGrpCat.{u})

/-- Contract a cone map towards its apex. -/
def coneMapContraction
    (f : cone X ⟶ underlyingSSet A) :
    cone X ⊗ Δ[1] ⟶ underlyingSSet A :=
  coneContractionMap (X := X) ≫ f

@[reassoc]
theorem ι₀_coneMapContraction
    (f : cone X ⟶ underlyingSSet A) :
    SSet.ι₀ ≫ coneMapContraction A f = f := by
  rw [coneMapContraction, ← Category.assoc,
    ι₀_coneContractionMap, Category.id_comp]

@[reassoc]
theorem ι₁_coneMapContraction
    (f : cone X ⟶ underlyingSSet A)
    (hapex : apexInclusion X ≫ f = 0) :
    SSet.ι₁ ≫ coneMapContraction A f = 0 := by
  rw [coneMapContraction, ← Category.assoc,
    ι₁_coneContractionMap, Category.assoc, hapex]
  rw [← const_zeroVertex_eq_zeroMap (X := Δ[0]) A,
    collapse_comp_const,
    const_zeroVertex_eq_zeroMap (X := cone X)]

@[reassoc]
theorem coneBaseLine_coneMapContraction
    (f : cone X ⟶ underlyingSSet A)
    (hbase : coneBaseLine P ≫ f = 0) :
    (coneBaseLine P ▷ Δ[1]) ≫ coneMapContraction A f = 0 := by
  rw [coneMapContraction, ← Category.assoc,
    coneBaseLine_whisker_coneContractionMap, Category.assoc, hbase]
  ext Δ x
  rfl

/-! ## Gluing cylinder maps on a suspension -/

/-- Tensoring the suspension pushout with the interval gives the pushout
of the two tensor products. -/
def suspensionCylinderPushoutIso :
    pushout (bottomInclusion X ▷ Δ[1])
        (bottomInclusion X ▷ Δ[1]) ≅
      suspension X ⊗ Δ[1] :=
  PreservesPushout.iso (tensorRight Δ[1])
    (bottomInclusion X) (bottomInclusion X)

/-- Glue compatible cylinder maps on the lower and upper cones. -/
def suspensionCylinderDesc
    {Y : SSet.{u}}
    (hLower hUpper : cone X ⊗ Δ[1] ⟶ Y)
    (compat :
      (bottomInclusion X ▷ Δ[1]) ≫ hLower =
        (bottomInclusion X ▷ Δ[1]) ≫ hUpper) :
    suspension X ⊗ Δ[1] ⟶ Y :=
  (suspensionCylinderPushoutIso (X := X)).inv ≫
    pushout.desc hLower hUpper compat

@[reassoc]
theorem lowerConeInclusion_whisker_suspensionCylinderDesc
    {Y : SSet.{u}}
    (hLower hUpper : cone X ⊗ Δ[1] ⟶ Y)
    (compat :
      (bottomInclusion X ▷ Δ[1]) ≫ hLower =
        (bottomInclusion X ▷ Δ[1]) ≫ hUpper) :
    (lowerConeInclusion X ▷ Δ[1]) ≫
        suspensionCylinderDesc hLower hUpper compat = hLower := by
  change (tensorRight Δ[1]).map
      (pushout.inl (bottomInclusion X) (bottomInclusion X)) ≫
      (suspensionCylinderPushoutIso (X := X)).inv ≫
      pushout.desc _ _ _ = _
  rw [suspensionCylinderPushoutIso,
    PreservesPushout.inl_iso_inv_assoc, pushout.inl_desc]

@[reassoc]
theorem upperConeInclusion_whisker_suspensionCylinderDesc
    {Y : SSet.{u}}
    (hLower hUpper : cone X ⊗ Δ[1] ⟶ Y)
    (compat :
      (bottomInclusion X ▷ Δ[1]) ≫ hLower =
        (bottomInclusion X ▷ Δ[1]) ≫ hUpper) :
    (upperConeInclusion X ▷ Δ[1]) ≫
        suspensionCylinderDesc hLower hUpper compat = hUpper := by
  change (tensorRight Δ[1]).map
      (pushout.inr (bottomInclusion X) (bottomInclusion X)) ≫
      (suspensionCylinderPushoutIso (X := X)).inv ≫
      pushout.desc _ _ _ = _
  rw [suspensionCylinderPushoutIso,
    PreservesPushout.inr_iso_inv_assoc, pushout.inr_desc]

/-- Precomposition with the pointwise zero map is zero. -/
theorem comp_zeroUnderlying
    {Y Z : SSet.{u}} (k : Y ⟶ Z) :
    k ≫ (0 : Z ⟶ underlyingSSet A) = 0 := by
  ext Δ y
  rfl

/-- If both cone-cylinder branches vanish on the cone on `P`, their glued
suspension cylinder map is zero on the pointed suspension boundary. -/
theorem pointedBoundary_suspensionCylinderDesc_eq_zero
    (hLower hUpper : cone X ⊗ Δ[1] ⟶ underlyingSSet A)
    (compat :
      (bottomInclusion X ▷ Δ[1]) ≫ hLower =
        (bottomInclusion X ▷ Δ[1]) ≫ hUpper)
    (hLowerP : (coneBaseLine P ▷ Δ[1]) ≫ hLower = 0)
    (hUpperP : (coneBaseLine P ▷ Δ[1]) ≫ hUpper = 0) :
    (pointedSuspensionBoundary P).ι ▷ Δ[1] ≫
        suspensionCylinderDesc hLower hUpper compat = 0 := by
  let h := suspensionCylinderDesc hLower hUpper compat
  have hlower :
      ((coneBaseLine P ≫ lowerConeInclusion X) ▷ Δ[1]) ≫ h = 0 := by
    change ((coneBaseLine P ≫ lowerConeInclusion X) ▷ Δ[1]) ≫
      suspensionCylinderDesc hLower hUpper compat = 0
    rw [comp_whiskerRight_assoc,
      lowerConeInclusion_whisker_suspensionCylinderDesc,
      hLowerP]
  have hupper :
      ((coneBaseLine P ≫ upperConeInclusion X) ▷ Δ[1]) ≫ h = 0 := by
    change ((coneBaseLine P ≫ upperConeInclusion X) ▷ Δ[1]) ≫
      suspensionCylinderDesc hLower hUpper compat = 0
    rw [comp_whiskerRight_assoc,
      upperConeInclusion_whisker_suspensionCylinderDesc,
      hUpperP]
  ext Δ x
  rcases x.1.2 with hx | hx
  · rcases hx with ⟨y, hy⟩
    change h.app Δ (x.1.1, x.2) = 0
    rw [← hy]
    have hlowerΔ := congr_app hlower Δ
    have hlowerFun := ConcreteCategory.congr_hom hlowerΔ
    exact hlowerFun (y, x.2)
  · rcases hx with ⟨y, hy⟩
    change h.app Δ (x.1.1, x.2) = 0
    rw [← hy]
    have hupperΔ := congr_app hupper Δ
    have hupperFun := ConcreteCategory.congr_hom hupperΔ
    exact hupperFun (y, x.2)

/-! ## The diagonal suspension map is pointed-null -/

/-- Use the upper-cone restriction on both cone halves. -/
def diagonalSuspensionMap
    (F : PointedSuspensionMaps P A) :
    PointedSuspensionMaps P A := by
  let u : cone X ⟶ underlyingSSet A := upperConeInclusion X ≫ F.1
  let D : suspension X ⟶ underlyingSSet A :=
    pushout.desc u u rfl
  have hu : coneBaseLine P ≫ u = 0 :=
    LinearMap.mem_ker.mp F.2.2
  refine ⟨D, ?_, ?_⟩
  · change coneBaseLine P ≫ lowerConeInclusion X ≫ D = 0
    rw [pushout.inl_desc]
    exact hu
  · change coneBaseLine P ≫ upperConeInclusion X ≫ D = 0
    rw [pushout.inr_desc]
    exact hu

@[simp]
theorem lower_diagonalSuspensionMap
    (F : PointedSuspensionMaps P A) :
    lowerConeInclusion X ≫ (diagonalSuspensionMap P A F).1 =
      upperConeInclusion X ≫ F.1 := by
  exact pushout.inl_desc _ _ _

@[simp]
theorem upper_diagonalSuspensionMap
    (F : PointedSuspensionMaps P A) :
    upperConeInclusion X ≫ (diagonalSuspensionMap P A F).1 =
      upperConeInclusion X ≫ F.1 := by
  exact pushout.inr_desc _ _ _

/-- Cylinder map contracting the diagonal suspension map: use the same
cone contraction on both halves. -/
def diagonalSuspensionContraction
    (F : PointedSuspensionMaps P A) :
    suspension X ⊗ Δ[1] ⟶ underlyingSSet A :=
  let u := upperConeInclusion X ≫ F.1
  suspensionCylinderDesc
    (coneMapContraction A u) (coneMapContraction A u) rfl

@[reassoc]
theorem ι₀_diagonalSuspensionContraction
    (F : PointedSuspensionMaps P A) :
    SSet.ι₀ ≫ diagonalSuspensionContraction P A F =
      (diagonalSuspensionMap P A F).1 := by
  apply pushout.hom_ext
  · calc
      lowerConeInclusion X ≫ SSet.ι₀ ≫
          diagonalSuspensionContraction P A F =
        SSet.ι₀ ≫ (lowerConeInclusion X ▷ Δ[1]) ≫
          diagonalSuspensionContraction P A F := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ coneMapContraction A
          (upperConeInclusion X ≫ F.1) := by
            rw [diagonalSuspensionContraction,
              lowerConeInclusion_whisker_suspensionCylinderDesc]
      _ = upperConeInclusion X ≫ F.1 :=
        ι₀_coneMapContraction A _
      _ = lowerConeInclusion X ≫
          (diagonalSuspensionMap P A F).1 :=
        (lower_diagonalSuspensionMap P A F).symm
  · calc
      upperConeInclusion X ≫ SSet.ι₀ ≫
          diagonalSuspensionContraction P A F =
        SSet.ι₀ ≫ (upperConeInclusion X ▷ Δ[1]) ≫
          diagonalSuspensionContraction P A F := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ coneMapContraction A
          (upperConeInclusion X ≫ F.1) := by
            rw [diagonalSuspensionContraction,
              upperConeInclusion_whisker_suspensionCylinderDesc]
      _ = upperConeInclusion X ≫ F.1 :=
        ι₀_coneMapContraction A _
      _ = upperConeInclusion X ≫
          (diagonalSuspensionMap P A F).1 :=
        (upper_diagonalSuspensionMap P A F).symm

/-- The diagonal suspension contraction ends at the zero map when the
pointed subcomplex contains a vertex. -/
@[reassoc]
theorem ι₁_diagonalSuspensionContraction
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0)))
    (F : PointedSuspensionMaps P A) :
    SSet.ι₁ ≫ diagonalSuspensionContraction P A F = 0 := by
  let u : cone X ⟶ underlyingSSet A := upperConeInclusion X ≫ F.1
  have hu : coneBaseLine P ≫ u = 0 :=
    LinearMap.mem_ker.mp F.2.2
  have hapex : apexInclusion X ≫ u = 0 :=
    apex_comp_eq_zero_of_baseLine (P := P) (A := A) p u hu
  apply pushout.hom_ext
  · calc
      lowerConeInclusion X ≫ SSet.ι₁ ≫
          diagonalSuspensionContraction P A F =
        SSet.ι₁ ≫ (lowerConeInclusion X ▷ Δ[1]) ≫
          diagonalSuspensionContraction P A F := by
            rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ coneMapContraction A u := by
            rw [diagonalSuspensionContraction,
              lowerConeInclusion_whisker_suspensionCylinderDesc]
      _ = 0 := ι₁_coneMapContraction A u hapex
      _ = lowerConeInclusion X ≫
          (0 : suspension X ⟶ underlyingSSet A) :=
        (comp_zeroUnderlying A (lowerConeInclusion X)).symm
  · calc
      upperConeInclusion X ≫ SSet.ι₁ ≫
          diagonalSuspensionContraction P A F =
        SSet.ι₁ ≫ (upperConeInclusion X ▷ Δ[1]) ≫
          diagonalSuspensionContraction P A F := by
            rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ coneMapContraction A u := by
            rw [diagonalSuspensionContraction,
              upperConeInclusion_whisker_suspensionCylinderDesc]
      _ = 0 := ι₁_coneMapContraction A u hapex
      _ = upperConeInclusion X ≫
          (0 : suspension X ⟶ underlyingSSet A) :=
        (comp_zeroUnderlying A (upperConeInclusion X)).symm

/-- The diagonal suspension contraction is fixed at zero on the two copies
of the cone on `P`. -/
theorem pointedBoundary_diagonalSuspensionContraction_eq_zero
    (F : PointedSuspensionMaps P A) :
    (pointedSuspensionBoundary P).ι ▷ Δ[1] ≫
        diagonalSuspensionContraction P A F = 0 := by
  let u : cone X ⟶ underlyingSSet A := upperConeInclusion X ≫ F.1
  have hu : coneBaseLine P ≫ u = 0 :=
    LinearMap.mem_ker.mp F.2.2
  apply pointedBoundary_suspensionCylinderDesc_eq_zero P A
      (coneMapContraction A u) (coneMapContraction A u) rfl
  · exact coneBaseLine_coneMapContraction P A u hu
  · exact coneBaseLine_coneMapContraction P A u hu

/-- The diagonal suspension map admits an actual pointed relative
nullhomotopy. -/
def diagonalSuspensionRelativeNullhomotopy
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0)))
    (F : PointedSuspensionMaps P A) :
    SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A
          (diagonalSuspensionMap P A F)))
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A 0)) where
  h := diagonalSuspensionContraction P A F
  h₀ := ι₀_diagonalSuspensionContraction P A F
  h₁ := by
    change SSet.ι₁ ≫ diagonalSuspensionContraction P A F = 0
    exact ι₁_diagonalSuspensionContraction P A p F
  rel := by
    rw [pointedBoundary_diagonalSuspensionContraction_eq_zero,
      cylinder_zeroBoundary]

/-! ## Lifting a nullhomotopy of lower-minus-upper -/

/-- Add the fixed upper-cone map to a nullhomotopy of the cone
difference. -/
def differenceCorrectionLower
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    cone X ⊗ Δ[1] ⟶ underlyingSSet A :=
  H.h + fst (cone X) Δ[1] ≫ upperConeInclusion X ≫ F.1

/-- Keep the upper-cone map fixed during the correction homotopy. -/
def differenceCorrectionUpper
    (F : PointedSuspensionMaps P A) :
    cone X ⊗ Δ[1] ⟶ underlyingSSet A :=
  fst (cone X) Δ[1] ≫ upperConeInclusion X ≫ F.1

/-- The correction branches agree on the equator because the relative
difference homotopy is zero there. -/
theorem differenceCorrection_compatible
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    (bottomInclusion X ▷ Δ[1]) ≫ differenceCorrectionLower P A F H =
      (bottomInclusion X ▷ Δ[1]) ≫ differenceCorrectionUpper P A F := by
  have hH : (bottomInclusion X ▷ Δ[1]) ≫ H.h = 0 :=
    whisker_comp_relativeHomotopy_eq_zero_of_range_le A
      (bottomInclusion X) le_sup_left H
  rw [differenceCorrectionLower, differenceCorrectionUpper,
    comp_addMap, hH, zero_add]

/-- The corrected lower branch is zero on the cone on `P`. -/
theorem coneBaseLine_differenceCorrectionLower_eq_zero
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    (coneBaseLine P ▷ Δ[1]) ≫
      differenceCorrectionLower P A F H = 0 := by
  have hH : (coneBaseLine P ▷ Δ[1]) ≫ H.h = 0 :=
    whisker_comp_relativeHomotopy_eq_zero_of_range_le A
      (coneBaseLine P) le_sup_right H
  have hu : coneBaseLine P ≫ upperConeInclusion X ≫ F.1 = 0 :=
    LinearMap.mem_ker.mp F.2.2
  have hconst :
      (coneBaseLine P ▷ Δ[1]) ≫ fst (cone X) Δ[1] ≫
          upperConeInclusion X ≫ F.1 = 0 := by
    calc
      _ = fst ((P : SSet) ⊗ Δ[1]) Δ[1] ≫ coneBaseLine P ≫
          upperConeInclusion X ≫ F.1 := by
        rw [← Category.assoc, whiskerRight_fst]
        simp only [Category.assoc]
      _ = fst ((P : SSet) ⊗ Δ[1]) Δ[1] ≫
          (coneBaseLine P ≫ upperConeInclusion X ≫ F.1) := by
        rfl
      _ = 0 := by
        rw [hu]
        exact comp_zeroUnderlying A _
  rw [differenceCorrectionLower, comp_addMap, hH, hconst, zero_add]

/-- The fixed upper branch is zero on the cone on `P`. -/
theorem coneBaseLine_differenceCorrectionUpper_eq_zero
    (F : PointedSuspensionMaps P A) :
    (coneBaseLine P ▷ Δ[1]) ≫
      differenceCorrectionUpper P A F = 0 := by
  have hu : coneBaseLine P ≫ upperConeInclusion X ≫ F.1 = 0 :=
    LinearMap.mem_ker.mp F.2.2
  calc
    _ = fst ((P : SSet) ⊗ Δ[1]) Δ[1] ≫ coneBaseLine P ≫
        upperConeInclusion X ≫ F.1 := by
      rw [differenceCorrectionUpper, ← Category.assoc,
        whiskerRight_fst]
      simp only [Category.assoc]
    _ = fst ((P : SSet) ⊗ Δ[1]) Δ[1] ≫
        (coneBaseLine P ≫ upperConeInclusion X ≫ F.1) := by
      rfl
    _ = 0 := by
      rw [hu]
      exact comp_zeroUnderlying A _

/-- Glue the correction homotopy across the suspension. -/
def differenceCorrectionSuspension
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    suspension X ⊗ Δ[1] ⟶ underlyingSSet A :=
  suspensionCylinderDesc
    (differenceCorrectionLower P A F H)
    (differenceCorrectionUpper P A F)
    (differenceCorrection_compatible P A F H)

@[reassoc]
theorem ι₀_differenceCorrectionUpper
    (F : PointedSuspensionMaps P A) :
    SSet.ι₀ ≫ differenceCorrectionUpper P A F =
      upperConeInclusion X ≫ F.1 := by
  rw [differenceCorrectionUpper, ← Category.assoc,
    SSet.ι₀_fst, Category.id_comp]

@[reassoc]
theorem ι₁_differenceCorrectionUpper
    (F : PointedSuspensionMaps P A) :
    SSet.ι₁ ≫ differenceCorrectionUpper P A F =
      upperConeInclusion X ≫ F.1 := by
  rw [differenceCorrectionUpper, ← Category.assoc,
    SSet.ι₁_fst, Category.id_comp]

@[reassoc]
theorem ι₀_differenceCorrectionLower
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    SSet.ι₀ ≫ differenceCorrectionLower P A F H =
      lowerConeInclusion X ≫ F.1 := by
  have hconst := ι₀_differenceCorrectionUpper P A F
  change SSet.ι₀ ≫ fst (cone X) Δ[1] ≫
      upperConeInclusion X ≫ F.1 = _ at hconst
  rw [differenceCorrectionLower, comp_addMap, H.h₀, hconst]
  change (lowerConeInclusion X ≫ F.1 - upperConeInclusion X ≫ F.1) +
      upperConeInclusion X ≫ F.1 = lowerConeInclusion X ≫ F.1
  exact sub_add_cancel _ _

@[reassoc]
theorem ι₁_differenceCorrectionLower
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    SSet.ι₁ ≫ differenceCorrectionLower P A F H =
      upperConeInclusion X ≫ F.1 := by
  have hconst := ι₁_differenceCorrectionUpper P A F
  change SSet.ι₁ ≫ fst (cone X) Δ[1] ≫
      upperConeInclusion X ≫ F.1 = _ at hconst
  rw [differenceCorrectionLower, comp_addMap, H.h₁, hconst]
  change coneDifferenceLinear A
      (0 : suspension X ⟶ underlyingSSet A) +
        upperConeInclusion X ≫ F.1 = upperConeInclusion X ≫ F.1
  rw [map_zero, zero_add]

@[reassoc]
theorem ι₀_differenceCorrectionSuspension
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    SSet.ι₀ ≫ differenceCorrectionSuspension P A F H = F.1 := by
  apply pushout.hom_ext
  · calc
      lowerConeInclusion X ≫ SSet.ι₀ ≫
          differenceCorrectionSuspension P A F H =
        SSet.ι₀ ≫ (lowerConeInclusion X ▷ Δ[1]) ≫
          differenceCorrectionSuspension P A F H := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ differenceCorrectionLower P A F H := by
            rw [differenceCorrectionSuspension,
              lowerConeInclusion_whisker_suspensionCylinderDesc]
      _ = lowerConeInclusion X ≫ F.1 :=
        ι₀_differenceCorrectionLower P A F H
  · calc
      upperConeInclusion X ≫ SSet.ι₀ ≫
          differenceCorrectionSuspension P A F H =
        SSet.ι₀ ≫ (upperConeInclusion X ▷ Δ[1]) ≫
          differenceCorrectionSuspension P A F H := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ differenceCorrectionUpper P A F := by
            rw [differenceCorrectionSuspension,
              upperConeInclusion_whisker_suspensionCylinderDesc]
      _ = upperConeInclusion X ≫ F.1 :=
        ι₀_differenceCorrectionUpper P A F

@[reassoc]
theorem ι₁_differenceCorrectionSuspension
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    SSet.ι₁ ≫ differenceCorrectionSuspension P A F H =
      (diagonalSuspensionMap P A F).1 := by
  apply pushout.hom_ext
  · calc
      lowerConeInclusion X ≫ SSet.ι₁ ≫
          differenceCorrectionSuspension P A F H =
        SSet.ι₁ ≫ (lowerConeInclusion X ▷ Δ[1]) ≫
          differenceCorrectionSuspension P A F H := by
            rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ differenceCorrectionLower P A F H := by
            rw [differenceCorrectionSuspension,
              lowerConeInclusion_whisker_suspensionCylinderDesc]
      _ = upperConeInclusion X ≫ F.1 :=
        ι₁_differenceCorrectionLower P A F H
      _ = lowerConeInclusion X ≫
          (diagonalSuspensionMap P A F).1 :=
        (lower_diagonalSuspensionMap P A F).symm
  · calc
      upperConeInclusion X ≫ SSet.ι₁ ≫
          differenceCorrectionSuspension P A F H =
        SSet.ι₁ ≫ (upperConeInclusion X ▷ Δ[1]) ≫
          differenceCorrectionSuspension P A F H := by
            rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ differenceCorrectionUpper P A F := by
            rw [differenceCorrectionSuspension,
              upperConeInclusion_whisker_suspensionCylinderDesc]
      _ = upperConeInclusion X ≫ F.1 :=
        ι₁_differenceCorrectionUpper P A F
      _ = upperConeInclusion X ≫
          (diagonalSuspensionMap P A F).1 :=
        (upper_diagonalSuspensionMap P A F).symm

/-- The correction homotopy remains zero on the pointed suspension
boundary. -/
theorem pointedBoundary_differenceCorrectionSuspension_eq_zero
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    (pointedSuspensionBoundary P).ι ▷ Δ[1] ≫
      differenceCorrectionSuspension P A F H = 0 := by
  exact pointedBoundary_suspensionCylinderDesc_eq_zero P A
    (differenceCorrectionLower P A F H)
    (differenceCorrectionUpper P A F)
    (differenceCorrection_compatible P A F H)
    (coneBaseLine_differenceCorrectionLower_eq_zero P A F H)
    (coneBaseLine_differenceCorrectionUpper_eq_zero P A F)

/-- An actual relative nullhomotopy of lower-minus-upper lifts to an
actual pointed homotopy from `F` to its diagonal upper-cone part. -/
def differenceCorrectionRelativeHomotopy
    (F : PointedSuspensionMaps P A)
    (H : SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0))) :
    SSet.RelativeMorphism.Homotopy
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A F))
      (RelativeZeroMaps.toRelativeMorphism
        (pointedSuspensionBoundary P) A
        (pointedSuspensionRelativeZeroMap P A
          (diagonalSuspensionMap P A F))) where
  h := differenceCorrectionSuspension P A F H
  h₀ := ι₀_differenceCorrectionSuspension P A F H
  h₁ := ι₁_differenceCorrectionSuspension P A F H
  rel := by
    rw [pointedBoundary_differenceCorrectionSuspension_eq_zero,
      cylinder_zeroBoundary]

/-! ## Unconditional reverse exactness for a genuinely pointed pair -/

/-- If `P` contains a vertex, every element in the kernel of the native
two-cone difference admits an actual pointed nullhomotopy.  This supplies
the previously isolated cofiber assertion without any additional data. -/
theorem twoConeKernelNullhomotopy_of_vertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    TwoConeKernelNullhomotopy P A := by
  intro F hF
  have hclass :
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A F)).homotopyClass =
      (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
        (differenceRelativeZeroMap P A 0)).homotopyClass := by
    calc
      _ = twoConeDifferenceLinear P A F := rfl
      _ = 0 := hF
      _ = twoConeDifferenceLinear P A 0 :=
        (map_zero (twoConeDifferenceLinear P A)).symm
      _ = _ := rfl
  rcases (homotopyClass_eq_iff (conePairBoundary P) A).mp hclass with
    ⟨H⟩
  exact ⟨homotopyTrans (pointedSuspensionBoundary P) A
    (differenceCorrectionRelativeHomotopy P A F H)
    (diagonalSuspensionRelativeNullhomotopy P A p F)⟩

/-- The reverse kernel inclusion, with exactly the nonempty pointedness
hypothesis needed to exclude the empty-`P` counterexample. -/
theorem twoConeDifference_ker_le_pointedSuspensionNullMaps_of_vertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    LinearMap.ker (twoConeDifferenceLinear P A) ≤
      PointedSuspensionNullMaps P A :=
  (twoConeKernelNullhomotopy_iff_reverse_inclusion P A).mp
    (twoConeKernelNullhomotopy_of_vertex P A p)

/-- Full native two-cone kernel identification for a pointed pair. -/
theorem twoConeDifference_ker_eq_pointedSuspensionNullMaps_of_vertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    LinearMap.ker (twoConeDifferenceLinear P A) =
      PointedSuspensionNullMaps P A :=
  twoConeDifference_ker_eq_pointedSuspensionNullMaps P A
    (twoConeKernelNullhomotopy_of_vertex P A p)

/-- The quotient form of native two-cone exactness, now requiring only an
actual chosen vertex of `P` and no model-level assertion. -/
def quotientPointedSuspensionNullEquivOfVertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    (PointedSuspensionMaps P A ⧸ PointedSuspensionNullMaps P A) ≃ₗ[ℤ]
      NativeHomotopyClass (conePairBoundary P) A :=
  quotientPointedSuspensionNullEquiv P A
    (twoConeKernelNullhomotopy_of_vertex P A p)

@[simp]
theorem quotientPointedSuspensionNullEquivOfVertex_mkQ
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0)))
    (F : PointedSuspensionMaps P A) :
    quotientPointedSuspensionNullEquivOfVertex P A p
        ((PointedSuspensionNullMaps P A).mkQ F) =
      twoConeDifferenceLinear P A F :=
  quotientPointedSuspensionNullEquiv_mkQ P A
    (twoConeKernelNullhomotopy_of_vertex P A p) F

end NativeDoubleConeReverse
end GeneralSphereT.Section4

/-! ## Public two-cone exactness API

The constructions above live in `NativeDoubleConeReverse`.  These wrappers
put the completed theorems beside the forward exactness API.  In particular,
users provide the chosen point of the pointed subcomplex directly; no
`TwoConeKernelNullhomotopy` argument appears in the public endpoint. -/

namespace GeneralSphereT.Section4
namespace NativeDoubleConeExactness

universe u

open UnderlyingSSet
open RelativeMapping
open NativeRelativeHomotopyGroup
open NativeSimplicialCone
open NativeDoubleCone

variable {X : SSet.{u}}
variable (P : X.Subcomplex)
variable (A : SimplicialObject AddCommGrpCat.{u})

/-- The cofiber nullhomotopy theorem for a genuinely pointed pair.  The
vertex hypothesis is essential: the statement fails for the empty
subcomplex. -/
theorem twoConeKernelNullhomotopy_of_vertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    TwoConeKernelNullhomotopy P A :=
  NativeDoubleConeReverse.twoConeKernelNullhomotopy_of_vertex P A p

/-- The reverse kernel inclusion, requiring exactly a chosen vertex of the
pointed subcomplex. -/
theorem twoConeDifference_ker_le_pointedSuspensionNullMaps_of_vertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    LinearMap.ker (twoConeDifferenceLinear P A) ≤
      PointedSuspensionNullMaps P A :=
  NativeDoubleConeReverse.twoConeDifference_ker_le_pointedSuspensionNullMaps_of_vertex
    P A p

/-- Full native two-cone kernel identification for a genuinely pointed
pair. -/
theorem twoConeDifference_ker_eq_pointedSuspensionNullMaps_of_vertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    LinearMap.ker (twoConeDifferenceLinear P A) =
      PointedSuspensionNullMaps P A :=
  NativeDoubleConeReverse.twoConeDifference_ker_eq_pointedSuspensionNullMaps_of_vertex
    P A p

/-- The public quotient form of native two-cone exactness.  It asks for the
actual basepoint vertex rather than an abstract nullhomotopy interface. -/
def quotientPointedSuspensionNullEquivOfVertex
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0))) :
    (PointedSuspensionMaps P A ⧸ PointedSuspensionNullMaps P A) ≃ₗ[ℤ]
      NativeHomotopyClass (conePairBoundary P) A :=
  NativeDoubleConeReverse.quotientPointedSuspensionNullEquivOfVertex
    P A p

@[simp]
theorem quotientPointedSuspensionNullEquivOfVertex_mkQ
    (p : (P : SSet).obj (Opposite.op (SimplexCategory.mk 0)))
    (F : PointedSuspensionMaps P A) :
    quotientPointedSuspensionNullEquivOfVertex P A p
        ((PointedSuspensionNullMaps P A).mkQ F) =
      twoConeDifferenceLinear P A F :=
  NativeDoubleConeReverse.quotientPointedSuspensionNullEquivOfVertex_mkQ
    P A p F

end NativeDoubleConeExactness
end GeneralSphereT.Section4
