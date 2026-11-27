import Formalization.Section4DoubleConePrimitiveGluing
import Formalization.Section4LiteralRelativeConeCriterionReverse

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the literal two-cone difference

This file proves the two-cone difference theorem directly on the literal
double-cone boundary.  In contrast with the categorical suspension model,
the source is pointed only at the outer apex.  This is exactly the model
used by `nativeThetaOfReduced`, so no comparison of stronger relative
pointing conditions is needed.
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

local instance (priority := 10000) literalDoubleConeOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance
local instance (priority := 10000) literalDoubleConeOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance
local instance (priority := 10000) literalDoubleConeOptionLinearOrder :
    LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
local instance (priority := 10001) literalDoubleConeOptionOptionLE :
    LE (Option (Option V)) := @WithBot.instLE (Option V) inferInstance
local instance (priority := 10001) literalDoubleConeOptionOptionLT :
    LT (Option (Option V)) := @WithBot.instLT (Option V) inferInstance
local instance (priority := 10001) literalDoubleConeOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

/-! ## The literal boundary is the union of its two cone faces -/

abbrev literalDoubleConeInnerMap :
    orderedComplexSSet (simplicialCone M) ⟶
      orderedComplexSSet (doubleConeBoundary M) :=
  (doubleConeInnerBoundaryInclusion M).toSSetMap

abbrev literalDoubleConeOtherMap :
    orderedComplexSSet (simplicialCone M) ⟶
      orderedComplexSSet (doubleConeBoundary M) :=
  (doubleConeOtherBoundaryInclusion M).toSSetMap

abbrev literalDoubleConeEquatorMap :
    orderedComplexSSet M ⟶ orderedComplexSSet (doubleConeBoundary M) :=
  (doubleConeEquatorInclusion M).toSSetMap

@[reassoc]
theorem literalDoubleCone_inner_bottom :
    literalConeBottomMap M ≫ literalDoubleConeInnerMap M =
      literalDoubleConeEquatorMap M := by
  ext Delta x
  rfl

@[reassoc]
theorem literalDoubleCone_other_bottom :
    literalConeBottomMap M ≫ literalDoubleConeOtherMap M =
      literalDoubleConeEquatorMap M := by
  ext Delta x
  rfl

theorem orderedSimplicialMap_toSSetMap_mono
    {W : Type u} [LinearOrder W]
    {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (F : OrderedSimplicialMap K L) : Mono F.toSSetMap := by
  rw [NatTrans.mono_iff_mono_app]
  intro Delta
  rw [mono_iff_injective]
  intro x y h
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  have hi := congrArg (fun z => z.1 i) h
  exact F.toOrderEmbedding.injective hi

instance literalDoubleConeInnerMap_mono :
    Mono (literalDoubleConeInnerMap M) :=
  orderedSimplicialMap_toSSetMap_mono (doubleConeInnerBoundaryInclusion M)

instance literalDoubleConeOtherMap_mono :
    Mono (literalDoubleConeOtherMap M) :=
  orderedSimplicialMap_toSSetMap_mono (doubleConeOtherBoundaryInclusion M)

instance literalDoubleConeEquatorMap_mono :
    Mono (literalDoubleConeEquatorMap M) :=
  orderedSimplicialMap_toSSetMap_mono (doubleConeEquatorInclusion M)

/-- An ordered simplex of a literal cone which avoids the apex comes from
the bottom, including in degenerate dimensions. -/
theorem exists_orderedConeBottom_of_apex_not_mem
    {Delta : SimplexCategoryᵒᵖ}
    (x : (orderedComplexSSet (simplicialCone M)).obj Delta)
    (hx : (none : Option V) ∉ orderedSimplexSupport x.1) :
    ∃ y : (orderedComplexSSet M).obj Delta,
      (literalConeBottomMap M).app Delta y = x := by
  have hsome : ∀ i, ∃ v : V, x.1 i = some v := by
    intro i
    have hne : x.1 i ≠ none := by
      intro hi
      exact hx ((mem_orderedSimplexSupport x.1 none).2 ⟨i, hi⟩)
    rcases Option.ne_none_iff_exists.mp hne with ⟨v, hv⟩
    exact ⟨v, hv.symm⟩
  let yhom : Fin (Delta.unop.len + 1) →o V :=
    { toFun := fun i ↦ Classical.choose (hsome i)
      monotone' := by
        intro i j hij
        have hmono := x.1.monotone hij
        rw [Classical.choose_spec (hsome i),
          Classical.choose_spec (hsome j)] at hmono
        exact WithBot.coe_le_coe.mp hmono }
  have hbase : coneBaseVertices (orderedSimplexSupport x.1) =
      orderedSimplexSupport yhom := by
    ext v
    rw [mem_coneBaseVertices, mem_orderedSimplexSupport,
      mem_orderedSimplexSupport]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hs : x.1 i = some (yhom i) := by
        simpa [yhom] using Classical.choose_spec (hsome i)
      exact Option.some.inj (hs.symm.trans hi)
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hs : x.1 i = some (yhom i) := by
        simpa [yhom] using Classical.choose_spec (hsome i)
      exact hs.trans (congrArg some hi)
  have hy : orderedSimplexSupport yhom ∈ M := by
    rcases (mem_simplicialCone M (orderedSimplexSupport x.1)).mp x.2 with
      ⟨_hne, hzero | hmem⟩
    · have hyne : (orderedSimplexSupport yhom).Nonempty := by
        exact Finset.image_nonempty.mpr Finset.univ_nonempty
      exact (hyne.ne_empty (hbase.symm.trans hzero)).elim
    · simpa only [hbase] using hmem
  refine ⟨⟨yhom, hy⟩, ?_⟩
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  exact (Classical.choose_spec (hsome i)).symm

/-- The retraction from the other face is monotone on the whole nested
option order. -/
def doubleConeOtherRetractionOrderHom :
    Option (Option V) →o Option V where
  toFun := doubleConeOtherRetraction
  monotone' := by
    intro x y hxy
    cases x with
    | none => exact WithBot.LE.bot_le _
    | some x =>
        cases y with
        | none => exact (WithBot.not_coe_le_bot x hxy).elim
        | some y =>
            cases x with
            | none => exact WithBot.LE.bot_le _
            | some x =>
                cases y with
                | none => exact WithBot.coe_le_coe.mp hxy
                | some y =>
                    exact WithBot.coe_le_coe.mp hxy

/-- An ordered simplex of the outer cone which avoids the inner apex comes
from the other literal cone face. -/
theorem exists_orderedDoubleConeOther_of_inner_apex_not_mem
    {Delta : SimplexCategoryᵒᵖ}
    (x : (orderedComplexSSet (doubleConeBoundary M)).obj Delta)
    (hx : (some none : Option (Option V)) ∉
      orderedSimplexSupport x.1) :
    ∃ y : (orderedComplexSSet (simplicialCone M)).obj Delta,
      (literalDoubleConeOtherMap M).app Delta y = x := by
  let yhom : Fin (Delta.unop.len + 1) →o Option V :=
    (doubleConeOtherRetractionOrderHom (V := V)).comp x.1
  have hpoint : ∀ i,
      doubleConeOtherOrderEmbedding (yhom i) = x.1 i := by
    intro i
    change doubleConeOtherOrderEmbedding
      (doubleConeOtherRetraction (x.1 i)) = x.1 i
    cases hxi : x.1 i with
    | none => rfl
    | some o =>
        cases o with
        | none =>
            exfalso
            exact hx ((mem_orderedSimplexSupport x.1 (some none)).2 ⟨i, hxi⟩)
        | some v => rfl
  have hsupport :
      (orderedSimplexSupport yhom).map
          (doubleConeOtherOrderEmbedding (V := V)).toEmbedding =
        orderedSimplexSupport x.1 := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨a, ha, hao⟩
      rw [mem_orderedSimplexSupport] at ha
      rcases ha with ⟨i, hi⟩
      subst a
      have hao' : doubleConeOtherOrderEmbedding (yhom i) = o := hao
      rw [hpoint i] at hao'
      exact hao' ▸
        (mem_orderedSimplexSupport x.1 (x.1 i)).2 ⟨i, rfl⟩
    · intro ho
      rw [mem_orderedSimplexSupport] at ho
      rcases ho with ⟨i, rfl⟩
      exact Finset.mem_map.mpr
        ⟨yhom i, (mem_orderedSimplexSupport yhom (yhom i)).2 ⟨i, rfl⟩,
          hpoint i⟩
  have hyne : (orderedSimplexSupport yhom).Nonempty := by
    have hz : (orderedSimplexSupport x.1).Nonempty :=
      (doubleConeBoundary M).isRelLowerSet_faces x.2 |>.1
    have hm :
        ((orderedSimplexSupport yhom).map
          (doubleConeOtherOrderEmbedding (V := V)).toEmbedding).Nonempty :=
      hsupport.symm ▸ hz
    exact Finset.map_nonempty.mp hm
  have hbase :
      coneBaseVertices (orderedSimplexSupport yhom) =
        coneBaseVertices (coneBaseVertices (orderedSimplexSupport x.1)) := by
    ext v
    simp only [mem_coneBaseVertices]
    constructor
    · intro hv
      rw [mem_orderedSimplexSupport] at hv
      rcases hv with ⟨i, hi⟩
      have hp := hpoint i
      rw [hi] at hp
      exact (mem_orderedSimplexSupport x.1 (some (some v))).2
        ⟨i, hp.symm⟩
    · intro hv
      rw [mem_orderedSimplexSupport] at hv ⊢
      rcases hv with ⟨i, hi⟩
      have hp := hpoint i
      rw [hi] at hp
      have hyi : yhom i = some v := by
        cases h : yhom i with
        | none =>
            rw [h] at hp
            change (none : Option (Option V)) = some (some v) at hp
            cases hp
        | some w =>
            rw [h] at hp
            change some (some w) = some (some v) at hp
            exact Option.some.inj hp
      exact ⟨i, hyi⟩
  have hy : orderedSimplexSupport yhom ∈ simplicialCone M := by
    rw [mem_simplicialCone, hbase]
    refine ⟨hyne, ?_⟩
    rcases (mem_simplicialCone (simplicialCone M)
      (orderedSimplexSupport x.1)).mp x.2.1 |>.2 with hzero | hface
    · left
      rw [hzero]
      ext v
      simp [mem_coneBaseVertices]
    · exact (mem_simplicialCone M
        (coneBaseVertices (orderedSimplexSupport x.1))).mp hface |>.2
  refine ⟨⟨yhom, hy⟩, ?_⟩
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  exact hpoint i

abbrev literalDoubleConeInnerRange :
    (orderedComplexSSet (doubleConeBoundary M)).Subcomplex :=
  SSet.Subcomplex.range (literalDoubleConeInnerMap M)

abbrev literalDoubleConeOtherRange :
    (orderedComplexSSet (doubleConeBoundary M)).Subcomplex :=
  SSet.Subcomplex.range (literalDoubleConeOtherMap M)

abbrev literalDoubleConeEquatorRange :
    (orderedComplexSSet (doubleConeBoundary M)).Subcomplex :=
  SSet.Subcomplex.range (literalDoubleConeEquatorMap M)

theorem literalDoubleCone_face_ranges_sup_eq_top :
    literalDoubleConeInnerRange M ⊔ literalDoubleConeOtherRange M = ⊤ := by
  apply le_antisymm le_top
  intro Delta x _hx
  rcases x.2.2 with houter | hinner
  · left
    let x' : (orderedComplexSSet
        (simplicialCone (simplicialCone M))).obj Delta :=
      ⟨x.1, x.2.1⟩
    rcases exists_orderedConeBottom_of_apex_not_mem
      (simplicialCone M) x' houter with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    exact congrArg (fun z ↦ z.1 i) hy
  · right
    exact exists_orderedDoubleConeOther_of_inner_apex_not_mem M x hinner

theorem literalDoubleCone_equatorRange_le_innerRange :
    literalDoubleConeEquatorRange M ≤ literalDoubleConeInnerRange M := by
  intro Delta z hz
  rcases hz with ⟨x, rfl⟩
  exact ⟨(literalConeBottomMap M).app Delta x,
    congr_app (literalDoubleCone_inner_bottom M) Delta |>
      ConcreteCategory.congr_hom |>
      (fun h ↦ h x)⟩

theorem literalDoubleCone_equatorRange_le_otherRange :
    literalDoubleConeEquatorRange M ≤ literalDoubleConeOtherRange M := by
  intro Delta z hz
  rcases hz with ⟨x, rfl⟩
  exact ⟨(literalConeBottomMap M).app Delta x,
    congr_app (literalDoubleCone_other_bottom M) Delta |>
      ConcreteCategory.congr_hom |>
      (fun h ↦ h x)⟩

theorem literalDoubleCone_face_ranges_inf_eq_equator :
    literalDoubleConeInnerRange M ⊓ literalDoubleConeOtherRange M =
      literalDoubleConeEquatorRange M := by
  apply le_antisymm
  · intro Delta z hz
    rcases hz with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxapex : (none : Option V) ∉ orderedSimplexSupport x.1 := by
      intro hnone
      rw [mem_orderedSimplexSupport] at hnone
      rcases hnone with ⟨i, hi⟩
      have hxy := congrArg (fun w ↦ w.1 i) (hx.trans hy.symm)
      change some (x.1 i) =
        doubleConeOtherOrderEmbedding (y.1 i) at hxy
      rw [hi] at hxy
      cases hyi : y.1 i with
      | none => simp [hyi] at hxy
      | some v => simp [hyi] at hxy
    rcases exists_orderedConeBottom_of_apex_not_mem M x hxapex with
      ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have heq := congr_app (literalDoubleCone_inner_bottom M) Delta
    have heq' := ConcreteCategory.congr_hom heq w
    change (literalDoubleConeInnerMap M).app Delta
        ((literalConeBottomMap M).app Delta w) =
      (literalDoubleConeEquatorMap M).app Delta w at heq'
    calc
      (literalDoubleConeEquatorMap M).app Delta w =
          (literalDoubleConeInnerMap M).app Delta
            ((literalConeBottomMap M).app Delta w) := heq'.symm
      _ = (literalDoubleConeInnerMap M).app Delta x :=
        congrArg (fun a ↦ (literalDoubleConeInnerMap M).app Delta a) hw
      _ = z := hx
  · exact le_inf
      (literalDoubleCone_equatorRange_le_innerRange M)
      (literalDoubleCone_equatorRange_le_otherRange M)

def literalDoubleConeFaceBicartSq :
    SSet.Subcomplex.BicartSq
      (literalDoubleConeEquatorRange M)
      (literalDoubleConeInnerRange M)
      (literalDoubleConeOtherRange M)
      (⊤ : (orderedComplexSSet (doubleConeBoundary M)).Subcomplex) where
  sup_eq := literalDoubleCone_face_ranges_sup_eq_top M
  inf_eq := literalDoubleCone_face_ranges_inf_eq_equator M

/-! ## Gluing maps and cylinder maps on the literal boundary -/

@[reassoc]
theorem literalDoubleCone_equatorToInnerRange_inv :
    SSet.Subcomplex.toRange (literalDoubleConeEquatorMap M) ≫
        SSet.Subcomplex.homOfLE
          (literalDoubleCone_equatorRange_le_innerRange M) ≫
        inv (SSet.Subcomplex.toRange (literalDoubleConeInnerMap M)) =
      literalConeBottomMap M := by
  have hfactor :
      SSet.Subcomplex.toRange (literalDoubleConeEquatorMap M) ≫
          SSet.Subcomplex.homOfLE
            (literalDoubleCone_equatorRange_le_innerRange M) =
        literalConeBottomMap M ≫
          SSet.Subcomplex.toRange (literalDoubleConeInnerMap M) := by
    rw [← cancel_mono (literalDoubleConeInnerRange M).ι]
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι]
    exact literalDoubleCone_inner_bottom M
  rw [← Category.assoc, hfactor, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

@[reassoc]
theorem literalDoubleCone_equatorToOtherRange_inv :
    SSet.Subcomplex.toRange (literalDoubleConeEquatorMap M) ≫
        SSet.Subcomplex.homOfLE
          (literalDoubleCone_equatorRange_le_otherRange M) ≫
        inv (SSet.Subcomplex.toRange (literalDoubleConeOtherMap M)) =
      literalConeBottomMap M := by
  have hfactor :
      SSet.Subcomplex.toRange (literalDoubleConeEquatorMap M) ≫
          SSet.Subcomplex.homOfLE
            (literalDoubleCone_equatorRange_le_otherRange M) =
        literalConeBottomMap M ≫
          SSet.Subcomplex.toRange (literalDoubleConeOtherMap M) := by
    rw [← cancel_mono (literalDoubleConeOtherRange M).ι]
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι]
    exact literalDoubleCone_other_bottom M
  rw [← Category.assoc, hfactor, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

@[reassoc]
theorem literalDoubleCone_innerMap_top_inv :
    literalDoubleConeInnerMap M ≫
        (SSet.Subcomplex.topIso
          (orderedComplexSSet (doubleConeBoundary M))).inv =
      SSet.Subcomplex.toRange (literalDoubleConeInnerMap M) ≫
        SSet.Subcomplex.homOfLE
          (show literalDoubleConeInnerRange M ≤ ⊤ from le_top) := by
  rw [← cancel_mono
    ((⊤ : (orderedComplexSSet (doubleConeBoundary M)).Subcomplex).ι)]
  simp only [Category.assoc, SSet.Subcomplex.topIso_inv_ι,
    Category.comp_id, SSet.Subcomplex.homOfLE_ι,
    SSet.Subcomplex.toRange_ι]

@[reassoc]
theorem literalDoubleCone_otherMap_top_inv :
    literalDoubleConeOtherMap M ≫
        (SSet.Subcomplex.topIso
          (orderedComplexSSet (doubleConeBoundary M))).inv =
      SSet.Subcomplex.toRange (literalDoubleConeOtherMap M) ≫
        SSet.Subcomplex.homOfLE
          (show literalDoubleConeOtherRange M ≤ ⊤ from le_top) := by
  rw [← cancel_mono
    ((⊤ : (orderedComplexSSet (doubleConeBoundary M)).Subcomplex).ι)]
  simp only [Category.assoc, SSet.Subcomplex.topIso_inv_ι,
    Category.comp_id, SSet.Subcomplex.homOfLE_ι,
    SSet.Subcomplex.toRange_ι]

/-- Glue two maps on the literal cone faces which agree on the equator. -/
def literalDoubleConeDesc {Y : SSet.{u}}
    (fInner fOther : orderedComplexSSet (simplicialCone M) ⟶ Y)
    (compat : literalConeBottomMap M ≫ fInner =
      literalConeBottomMap M ≫ fOther) :
    orderedComplexSSet (doubleConeBoundary M) ⟶ Y := by
  let push := SSet.Subcomplex.BicartSq.isPushout
    (literalDoubleConeFaceBicartSq M)
  let fInner' :=
    inv (SSet.Subcomplex.toRange (literalDoubleConeInnerMap M)) ≫ fInner
  let fOther' :=
    inv (SSet.Subcomplex.toRange (literalDoubleConeOtherMap M)) ≫ fOther
  have hcompat :
      SSet.Subcomplex.homOfLE
          (literalDoubleCone_equatorRange_le_innerRange M) ≫ fInner' =
        SSet.Subcomplex.homOfLE
          (literalDoubleCone_equatorRange_le_otherRange M) ≫ fOther' := by
    rw [← cancel_epi
      (SSet.Subcomplex.toRange (literalDoubleConeEquatorMap M))]
    simp only [fInner', fOther']
    rw [literalDoubleCone_equatorToInnerRange_inv_assoc,
      literalDoubleCone_equatorToOtherRange_inv_assoc, compat]
  exact (SSet.Subcomplex.topIso
      (orderedComplexSSet (doubleConeBoundary M))).inv ≫
    push.desc fInner' fOther' hcompat

@[reassoc]
theorem literalDoubleConeInnerMap_desc {Y : SSet.{u}}
    (fInner fOther : orderedComplexSSet (simplicialCone M) ⟶ Y)
    (compat : literalConeBottomMap M ≫ fInner =
      literalConeBottomMap M ≫ fOther) :
    literalDoubleConeInnerMap M ≫
        literalDoubleConeDesc M fInner fOther compat = fInner := by
  rw [literalDoubleConeDesc,
    literalDoubleCone_innerMap_top_inv_assoc]
  rw [(SSet.Subcomplex.BicartSq.isPushout
    (literalDoubleConeFaceBicartSq M)).inl_desc]
  rw [IsIso.hom_inv_id_assoc]

@[reassoc]
theorem literalDoubleConeOtherMap_desc {Y : SSet.{u}}
    (fInner fOther : orderedComplexSSet (simplicialCone M) ⟶ Y)
    (compat : literalConeBottomMap M ≫ fInner =
      literalConeBottomMap M ≫ fOther) :
    literalDoubleConeOtherMap M ≫
        literalDoubleConeDesc M fInner fOther compat = fOther := by
  rw [literalDoubleConeDesc,
    literalDoubleCone_otherMap_top_inv_assoc]
  rw [(SSet.Subcomplex.BicartSq.isPushout
    (literalDoubleConeFaceBicartSq M)).inr_desc]
  rw [IsIso.hom_inv_id_assoc]

/-- Glue compatible cylinder maps on the two literal cone faces. -/
def literalDoubleConeCylinderDesc {Y : SSet.{u}}
    (hInner hOther :
      orderedComplexSSet (simplicialCone M) ⊗ Δ[1] ⟶ Y)
    (compat : (literalConeBottomMap M ▷ Δ[1]) ≫ hInner =
      (literalConeBottomMap M ▷ Δ[1]) ≫ hOther) :
    orderedComplexSSet (doubleConeBoundary M) ⊗ Δ[1] ⟶ Y := by
  let push := (SSet.Subcomplex.BicartSq.isPushout
    (literalDoubleConeFaceBicartSq M)).map (tensorRight Δ[1])
  let hInner' :=
    (inv (SSet.Subcomplex.toRange
      (literalDoubleConeInnerMap M)) ▷ Δ[1]) ≫ hInner
  let hOther' :=
    (inv (SSet.Subcomplex.toRange
      (literalDoubleConeOtherMap M)) ▷ Δ[1]) ≫ hOther
  have hcompat :
      (SSet.Subcomplex.homOfLE
          (literalDoubleCone_equatorRange_le_innerRange M) ▷ Δ[1]) ≫
          hInner' =
        (SSet.Subcomplex.homOfLE
          (literalDoubleCone_equatorRange_le_otherRange M) ▷ Δ[1]) ≫
          hOther' := by
    have hInnerFactor := congrArg (fun k ↦ k ▷ Δ[1])
      (literalDoubleCone_equatorToInnerRange_inv M)
    have hOtherFactor := congrArg (fun k ↦ k ▷ Δ[1])
      (literalDoubleCone_equatorToOtherRange_inv M)
    simp only [comp_whiskerRight] at hInnerFactor hOtherFactor
    rw [← cancel_epi
      (SSet.Subcomplex.toRange
        (literalDoubleConeEquatorMap M) ▷ Δ[1])]
    simp only [hInner', hOther']
    rw [reassoc_of% hInnerFactor, reassoc_of% hOtherFactor, compat]
  exact ((SSet.Subcomplex.topIso
      (orderedComplexSSet (doubleConeBoundary M))).inv ▷ Δ[1]) ≫
    push.desc hInner' hOther' hcompat

@[reassoc]
theorem literalDoubleConeInnerMap_whisker_cylinderDesc {Y : SSet.{u}}
    (hInner hOther :
      orderedComplexSSet (simplicialCone M) ⊗ Δ[1] ⟶ Y)
    (compat : (literalConeBottomMap M ▷ Δ[1]) ≫ hInner =
      (literalConeBottomMap M ▷ Δ[1]) ≫ hOther) :
    (literalDoubleConeInnerMap M ▷ Δ[1]) ≫
        literalDoubleConeCylinderDesc M hInner hOther compat = hInner := by
  have htop := congrArg (fun k ↦ k ▷ Δ[1])
    (literalDoubleCone_innerMap_top_inv M)
  simp only [comp_whiskerRight] at htop
  have hinv := congrArg (fun k ↦ k ▷ Δ[1])
    (IsIso.hom_inv_id
      (SSet.Subcomplex.toRange (literalDoubleConeInnerMap M)))
  simp only [comp_whiskerRight, id_whiskerRight] at hinv
  rw [literalDoubleConeCylinderDesc, reassoc_of% htop]
  change SSet.Subcomplex.toRange (literalDoubleConeInnerMap M) ▷ Δ[1] ≫
      (tensorRight Δ[1]).map
        (SSet.Subcomplex.homOfLE
          (show literalDoubleConeInnerRange M ≤ ⊤ from le_top)) ≫ _ = _
  rw [((SSet.Subcomplex.BicartSq.isPushout
    (literalDoubleConeFaceBicartSq M)).map
      (tensorRight Δ[1])).inl_desc]
  rw [reassoc_of% hinv]

@[reassoc]
theorem literalDoubleConeOtherMap_whisker_cylinderDesc {Y : SSet.{u}}
    (hInner hOther :
      orderedComplexSSet (simplicialCone M) ⊗ Δ[1] ⟶ Y)
    (compat : (literalConeBottomMap M ▷ Δ[1]) ≫ hInner =
      (literalConeBottomMap M ▷ Δ[1]) ≫ hOther) :
    (literalDoubleConeOtherMap M ▷ Δ[1]) ≫
        literalDoubleConeCylinderDesc M hInner hOther compat = hOther := by
  have htop := congrArg (fun k ↦ k ▷ Δ[1])
    (literalDoubleCone_otherMap_top_inv M)
  simp only [comp_whiskerRight] at htop
  have hinv := congrArg (fun k ↦ k ▷ Δ[1])
    (IsIso.hom_inv_id
      (SSet.Subcomplex.toRange (literalDoubleConeOtherMap M)))
  simp only [comp_whiskerRight, id_whiskerRight] at hinv
  rw [literalDoubleConeCylinderDesc, reassoc_of% htop]
  change SSet.Subcomplex.toRange (literalDoubleConeOtherMap M) ▷ Δ[1] ≫
      (tensorRight Δ[1]).map
        (SSet.Subcomplex.homOfLE
          (show literalDoubleConeOtherRange M ≤ ⊤ from le_top)) ≫ _ = _
  rw [((SSet.Subcomplex.BicartSq.isPushout
    (literalDoubleConeFaceBicartSq M)).map
      (tensorRight Δ[1])).inr_desc]
  rw [reassoc_of% hinv]

/-! ## The two-cone difference on pointed maps -/

abbrev literalDoubleConeApexSubcomplex :
    (orderedComplexSSet (doubleConeBoundary M)).Subcomplex :=
  orderedComplexBasepointSubcomplex (doubleConeBoundary M)
    (none : Option (Option V))

variable (A : SimplicialObject AddCommGrpCat.{u})

/-- Inner-face restriction minus other-face restriction, with its strict
zero boundary on the common bottom. -/
def literalTwoConeDifferenceRelativeZeroMap
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    RelativeZeroMaps (literalConeBottomSubcomplex M) A := by
  refine ⟨literalDoubleConeInnerMap M ≫ f.map -
    literalDoubleConeOtherMap M ≫ f.map, ?_⟩
  change (literalConeBottomSubcomplex M).ι ≫
      (literalDoubleConeInnerMap M ≫ f.map -
        literalDoubleConeOtherMap M ≫ f.map) = 0
  rw [← cancel_epi (SSet.Subcomplex.toRange (literalConeBottomMap M))]
  rw [← Category.assoc, SSet.Subcomplex.toRange_ι,
    NativeRelativeHomotopyGroup.comp_subMap]
  have hi : literalConeBottomMap M ≫
      literalDoubleConeInnerMap M ≫ f.map =
    literalDoubleConeEquatorMap M ≫ f.map := by
    rw [← Category.assoc, literalDoubleCone_inner_bottom]
  have ho : literalConeBottomMap M ≫
      literalDoubleConeOtherMap M ≫ f.map =
    literalDoubleConeEquatorMap M ≫ f.map := by
    rw [← Category.assoc, literalDoubleCone_other_bottom]
  rw [hi, ho, sub_self]
  ext Delta x
  rfl

/-- The actual relative morphism represented by the literal difference. -/
def literalTwoConeDifferenceMorphism
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    NativeRelativeMorphism (literalConeBottomSubcomplex M) A :=
  RelativeZeroMaps.toRelativeMorphism (literalConeBottomSubcomplex M) A
    (literalTwoConeDifferenceRelativeZeroMap M A f)

def literalTwoConeDifferenceHom :
    NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A →+
      NativeRelativeMorphism (literalConeBottomSubcomplex M) A where
  toFun := literalTwoConeDifferenceMorphism M A
  map_zero' := by
    apply SSet.RelativeMorphism.ext
    change literalDoubleConeInnerMap M ≫
        (0 : NativeRelativeMorphism
          (literalDoubleConeApexSubcomplex M) A).map -
      literalDoubleConeOtherMap M ≫
        (0 : NativeRelativeMorphism
          (literalDoubleConeApexSubcomplex M) A).map =
      (0 : NativeRelativeMorphism
        (literalConeBottomSubcomplex M) A).map
    rw [relativeMorphism_zero_map, relativeMorphism_zero_map]
    have hi : literalDoubleConeInnerMap M ≫
        (0 : orderedComplexSSet (doubleConeBoundary M) ⟶
          underlyingSSet A) = 0 := by ext Delta x; rfl
    have ho : literalDoubleConeOtherMap M ≫
        (0 : orderedComplexSSet (doubleConeBoundary M) ⟶
          underlyingSSet A) = 0 := by ext Delta x; rfl
    rw [hi, ho, sub_self]
  map_add' f g := by
    apply SSet.RelativeMorphism.ext
    change literalDoubleConeInnerMap M ≫ (f + g).map -
        literalDoubleConeOtherMap M ≫ (f + g).map =
      (literalDoubleConeInnerMap M ≫ f.map -
          literalDoubleConeOtherMap M ≫ f.map) +
        (literalDoubleConeInnerMap M ≫ g.map -
          literalDoubleConeOtherMap M ≫ g.map)
    rw [relativeMorphism_add_map,
      NativeRelativeHomotopyGroup.comp_addMap,
      NativeRelativeHomotopyGroup.comp_addMap]
    abel

def literalTwoConeDifferenceMorphismLinear :
    NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A →ₗ[ℤ]
      NativeRelativeMorphism (literalConeBottomSubcomplex M) A :=
  (literalTwoConeDifferenceHom M A).toIntLinearMap

/-- The literal two-cone difference with values in actual relative
homotopy classes. -/
def literalTwoConeDifferenceLinear :
    NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A →ₗ[ℤ]
      NativeHomotopyClass (literalConeBottomSubcomplex M) A :=
  (homotopyClassLinear (literalConeBottomSubcomplex M) A).comp
    (literalTwoConeDifferenceMorphismLinear M A)

@[simp]
theorem literalTwoConeDifferenceLinear_apply
    (f : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A) :
    literalTwoConeDifferenceLinear M A f =
      (literalTwoConeDifferenceMorphism M A f).homotopyClass :=
  rfl

/-! ## Surjectivity -/

theorem literalConeBottom_comp_eq_zero
    (f : RelativeZeroMaps (literalConeBottomSubcomplex M) A) :
    literalConeBottomMap M ≫ f.1 = 0 := by
  have hf : (literalConeBottomSubcomplex M).ι ≫ f.1 = 0 := f.2
  calc
    literalConeBottomMap M ≫ f.1 =
        SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
          (literalConeBottomSubcomplex M).ι ≫ f.1 := by
      rw [← Category.assoc, SSet.Subcomplex.toRange_ι]
    _ = SSet.Subcomplex.toRange (literalConeBottomMap M) ≫ 0 := by
      rw [hf]
    _ = 0 := by ext Delta x; rfl

@[reassoc]
theorem literalDoubleConeOtherMap_const_apex {X : SSet.{u}} :
    SSet.const (X := X)
        (literalConeApex M) ≫ literalDoubleConeOtherMap M =
      SSet.const (orderedComplexVertex (doubleConeBoundary M)
        (none : Option (Option V))) := by
  rw [SSet.const_comp]
  congr 1

theorem literalNormalizedDoubleCone_compat
    (f : RelativeZeroMaps (literalConeBottomSubcomplex M) A) :
    literalConeBottomMap M ≫ f.1 = literalConeBottomMap M ≫ 0 := by
  calc
    literalConeBottomMap M ≫ f.1 = 0 :=
      literalConeBottom_comp_eq_zero M A f
    _ = literalConeBottomMap M ≫ 0 := by ext Delta x; rfl

def literalNormalizedDoubleConeUnderlyingMap
    (f : RelativeZeroMaps (literalConeBottomSubcomplex M) A) :
    orderedComplexSSet (doubleConeBoundary M) ⟶ underlyingSSet A :=
  literalDoubleConeDesc M f.1 0
    (literalNormalizedDoubleCone_compat M A f)

/-- Put a bottom-relative map on the inner face and zero on the other
face.  The result is pointed at the outer apex. -/
def literalNormalizedDoubleConeMap
    (f : RelativeZeroMaps (literalConeBottomSubcomplex M) A) :
    NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A := by
  let F : orderedComplexSSet (doubleConeBoundary M) ⟶ underlyingSSet A :=
    literalNormalizedDoubleConeUnderlyingMap M A f
  let Fzero : RelativeZeroMaps (literalDoubleConeApexSubcomplex M) A := by
    refine ⟨F, ?_⟩
    change (literalDoubleConeApexSubcomplex M).ι ≫ F = 0
    have hapexι : (literalDoubleConeApexSubcomplex M).ι =
        SSet.const (orderedComplexVertex (doubleConeBoundary M)
          (none : Option (Option V))) := by
      simpa only [literalDoubleConeApexSubcomplex,
        orderedComplexBasepointSubcomplex] using
        (SSet.Subcomplex.ofSimplex_ι
          (orderedComplexVertex (doubleConeBoundary M)
            (none : Option (Option V))))
    have hother : literalDoubleConeOtherMap M ≫ F = 0 := by
      change literalDoubleConeOtherMap M ≫
        literalNormalizedDoubleConeUnderlyingMap M A f = 0
      exact literalDoubleConeOtherMap_desc M f.1 0
        (literalNormalizedDoubleCone_compat M A f)
    rw [hapexι]
    calc
      SSet.const (orderedComplexVertex (doubleConeBoundary M)
            (none : Option (Option V))) ≫ F =
          (SSet.const (X := literalDoubleConeApexSubcomplex M)
              (literalConeApex M) ≫
            literalDoubleConeOtherMap M) ≫ F := by
              exact (literalDoubleConeOtherMap_const_apex_assoc M F).symm
      _ = SSet.const (X := literalDoubleConeApexSubcomplex M)
          (literalConeApex M) ≫
          (literalDoubleConeOtherMap M ≫ F) :=
        Category.assoc _ _ _
      _ = SSet.const (X := literalDoubleConeApexSubcomplex M)
          (literalConeApex M) ≫ 0 := by
        rw [hother]
      _ = 0 := by ext Delta x; rfl
  exact RelativeZeroMaps.toRelativeMorphism
    (literalDoubleConeApexSubcomplex M) A Fzero

@[reassoc]
theorem literalDoubleConeInnerMap_normalized
    (f : RelativeZeroMaps (literalConeBottomSubcomplex M) A) :
    literalDoubleConeInnerMap M ≫
        (literalNormalizedDoubleConeMap M A f).map = f.1 := by
  change literalDoubleConeInnerMap M ≫
      literalNormalizedDoubleConeUnderlyingMap M A f = f.1
  exact literalDoubleConeInnerMap_desc M f.1 0
    (literalNormalizedDoubleCone_compat M A f)

@[reassoc]
theorem literalDoubleConeOtherMap_normalized
    (f : RelativeZeroMaps (literalConeBottomSubcomplex M) A) :
    literalDoubleConeOtherMap M ≫
        (literalNormalizedDoubleConeMap M A f).map = 0 := by
  change literalDoubleConeOtherMap M ≫
      literalNormalizedDoubleConeUnderlyingMap M A f = 0
  exact literalDoubleConeOtherMap_desc M f.1 0
    (literalNormalizedDoubleCone_compat M A f)

theorem literalTwoConeDifference_normalized
    (f : RelativeZeroMaps (literalConeBottomSubcomplex M) A) :
    literalTwoConeDifferenceMorphism M A
      (literalNormalizedDoubleConeMap M A f) =
        RelativeZeroMaps.toRelativeMorphism
          (literalConeBottomSubcomplex M) A f := by
  apply SSet.RelativeMorphism.ext
  change literalDoubleConeInnerMap M ≫
      (literalNormalizedDoubleConeMap M A f).map -
    literalDoubleConeOtherMap M ≫
      (literalNormalizedDoubleConeMap M A f).map = f.1
  rw [literalDoubleConeInnerMap_normalized,
    literalDoubleConeOtherMap_normalized, sub_zero]

theorem literalTwoConeDifferenceLinear_surjective :
    Function.Surjective (literalTwoConeDifferenceLinear M A) := by
  intro c
  rcases c.eq_homotopyClass with ⟨r, rfl⟩
  let f : RelativeZeroMaps (literalConeBottomSubcomplex M) A :=
    (RelativeZeroMaps.equivRelativeMorphism
      (literalConeBottomSubcomplex M) A).symm r
  refine ⟨literalNormalizedDoubleConeMap M A f, ?_⟩
  rw [literalTwoConeDifferenceLinear_apply,
    literalTwoConeDifference_normalized]
  change ((RelativeZeroMaps.equivRelativeMorphism
    (literalConeBottomSubcomplex M) A) f).homotopyClass =
      r.homotopyClass
  rw [(RelativeZeroMaps.equivRelativeMorphism
    (literalConeBottomSubcomplex M) A).apply_symm_apply]

/-! ## Restriction of pointed homotopies -/

/-- The two literal face inclusions are jointly epimorphic. -/
theorem literalDoubleCone_hom_ext {Y : SSet.{u}}
    {f g : orderedComplexSSet (doubleConeBoundary M) ⟶ Y}
    (hInner : literalDoubleConeInnerMap M ≫ f =
      literalDoubleConeInnerMap M ≫ g)
    (hOther : literalDoubleConeOtherMap M ≫ f =
      literalDoubleConeOtherMap M ≫ g) : f = g := by
  rw [← cancel_epi (SSet.Subcomplex.topIso
    (orderedComplexSSet (doubleConeBoundary M))).hom]
  apply (SSet.Subcomplex.BicartSq.isPushout
    (literalDoubleConeFaceBicartSq M)).hom_ext
  · rw [← cancel_epi
      (SSet.Subcomplex.toRange (literalDoubleConeInnerMap M))]
    calc
      _ = literalDoubleConeInnerMap M ≫ f := by
        simp only [SSet.Subcomplex.topIso_hom,
          SSet.Subcomplex.homOfLE_ι_assoc,
          SSet.Subcomplex.toRange_ι_assoc]
      _ = literalDoubleConeInnerMap M ≫ g := hInner
      _ = _ := by
        simp only [SSet.Subcomplex.topIso_hom,
          SSet.Subcomplex.homOfLE_ι_assoc,
          SSet.Subcomplex.toRange_ι_assoc]
  · rw [← cancel_epi
      (SSet.Subcomplex.toRange (literalDoubleConeOtherMap M))]
    calc
      _ = literalDoubleConeOtherMap M ≫ f := by
        simp only [SSet.Subcomplex.topIso_hom,
          SSet.Subcomplex.homOfLE_ι_assoc,
          SSet.Subcomplex.toRange_ι_assoc]
      _ = literalDoubleConeOtherMap M ≫ g := hOther
      _ = _ := by
        simp only [SSet.Subcomplex.topIso_hom,
          SSet.Subcomplex.homOfLE_ι_assoc,
          SSet.Subcomplex.toRange_ι_assoc]

/-- Restrict a pointed homotopy to the two cone faces and subtract. -/
def literalTwoConeDifferenceHomotopy
    {f g : NativeRelativeMorphism (literalDoubleConeApexSubcomplex M) A}
    (H : SSet.RelativeMorphism.Homotopy f g) :
    SSet.RelativeMorphism.Homotopy
      (literalTwoConeDifferenceMorphism M A f)
      (literalTwoConeDifferenceMorphism M A g) where
  h := ((literalDoubleConeInnerMap M ▷ Δ[1]) ≫ H.h) -
    ((literalDoubleConeOtherMap M ▷ Δ[1]) ≫ H.h)
  h₀ := by
    rw [NativeRelativeHomotopyGroup.comp_subMap]
    have hi : SSet.ι₀ ≫
        (literalDoubleConeInnerMap M ▷ Δ[1]) ≫ H.h =
      literalDoubleConeInnerMap M ≫ f.map := by
      calc
        _ = literalDoubleConeInnerMap M ≫ SSet.ι₀ ≫ H.h := by
          rw [SSet.ι₀_comp_assoc]
        _ = _ := by rw [H.h₀]
    have ho : SSet.ι₀ ≫
        (literalDoubleConeOtherMap M ▷ Δ[1]) ≫ H.h =
      literalDoubleConeOtherMap M ≫ f.map := by
      calc
        _ = literalDoubleConeOtherMap M ≫ SSet.ι₀ ≫ H.h := by
          rw [SSet.ι₀_comp_assoc]
        _ = _ := by rw [H.h₀]
    rw [hi, ho]
    rfl
  h₁ := by
    rw [NativeRelativeHomotopyGroup.comp_subMap]
    have hi : SSet.ι₁ ≫
        (literalDoubleConeInnerMap M ▷ Δ[1]) ≫ H.h =
      literalDoubleConeInnerMap M ≫ g.map := by
      calc
        _ = literalDoubleConeInnerMap M ≫ SSet.ι₁ ≫ H.h := by
          rw [SSet.ι₁_comp_assoc]
        _ = _ := by rw [H.h₁]
    have ho : SSet.ι₁ ≫
        (literalDoubleConeOtherMap M ▷ Δ[1]) ≫ H.h =
      literalDoubleConeOtherMap M ≫ g.map := by
      calc
        _ = literalDoubleConeOtherMap M ≫ SSet.ι₁ ≫ H.h := by
          rw [SSet.ι₁_comp_assoc]
        _ = _ := by rw [H.h₁]
    rw [hi, ho]
    rfl
  rel := by
    rw [cylinder_zeroBoundary]
    rw [← cancel_epi
      (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[1])]
    have hfactor := congrArg (fun k ↦ k ▷ Δ[1])
      (SSet.Subcomplex.toRange_ι (literalConeBottomMap M))
    simp only [comp_whiskerRight] at hfactor
    have heq :
        (literalConeBottomMap M ▷ Δ[1]) ≫
            (literalDoubleConeInnerMap M ▷ Δ[1]) ≫ H.h =
          (literalConeBottomMap M ▷ Δ[1]) ≫
            (literalDoubleConeOtherMap M ▷ Δ[1]) ≫ H.h := by
      calc
        _ = ((literalConeBottomMap M ≫
              literalDoubleConeInnerMap M) ▷ Δ[1]) ≫ H.h := by
          rw [comp_whiskerRight_assoc]
        _ = ((literalConeBottomMap M ≫
              literalDoubleConeOtherMap M) ▷ Δ[1]) ≫ H.h := by
          rw [literalDoubleCone_inner_bottom,
            literalDoubleCone_other_bottom]
        _ = _ := by rw [comp_whiskerRight_assoc]
    calc
      (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[1]) ≫
          ((literalConeBottomSubcomplex M).ι ▷ Δ[1]) ≫
          (((literalDoubleConeInnerMap M ▷ Δ[1]) ≫ H.h) -
            ((literalDoubleConeOtherMap M ▷ Δ[1]) ≫ H.h)) =
        (literalConeBottomMap M ▷ Δ[1]) ≫
          (((literalDoubleConeInnerMap M ▷ Δ[1]) ≫ H.h) -
            ((literalDoubleConeOtherMap M ▷ Δ[1]) ≫ H.h)) := by
              rw [reassoc_of% hfactor]
      _ = 0 := by
        rw [NativeRelativeHomotopyGroup.comp_subMap, heq, sub_self]
      _ = (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[1]) ≫
          0 := by ext Delta x; rfl

theorem nativeNullMaps_le_literalTwoConeDifference_ker :
    NativeNullMaps (literalDoubleConeApexSubcomplex M) A ≤
      LinearMap.ker (literalTwoConeDifferenceLinear M A) := by
  intro f hf
  have hclass : f.homotopyClass =
      (0 : NativeRelativeMorphism
        (literalDoubleConeApexSubcomplex M) A).homotopyClass := by
    calc
      f.homotopyClass = 0 := LinearMap.mem_ker.mp hf
      _ = (0 : NativeRelativeMorphism
          (literalDoubleConeApexSubcomplex M) A).homotopyClass :=
        (homotopyClass_zero (literalDoubleConeApexSubcomplex M) A).symm
  rcases (homotopyClass_eq_iff (literalDoubleConeApexSubcomplex M) A).mp
    hclass with ⟨H⟩
  have hd := (literalTwoConeDifferenceHomotopy M A H).eq
  change literalTwoConeDifferenceLinear M A f =
    literalTwoConeDifferenceLinear M A 0 at hd
  exact LinearMap.mem_ker.mpr
    (hd.trans (map_zero (literalTwoConeDifferenceLinear M A)))

end GeneralSphereT.SimplicialCochain
