import Formalization.Section4LiteralConeNativeCriterion
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

set_option linter.style.header false

/-!
# Section 4: the boundary of the pointed literal cone

The bottom of the literal cone and the cone line over the chosen basepoint
meet exactly in the bottom basepoint.  Hence a relative homotopy on the
bottom glues to the zero homotopy on that line.  This file packages the
resulting boundary path and the endpoint identities needed by homotopy
extension.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet

universe u

variable {V : Type u} [LinearOrder V] [Fintype V]
variable (M : AbstractSimplicialComplex V) (b : V)

local instance (priority := 10000) boundaryHEPOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance
local instance (priority := 10000) boundaryHEPOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance
local instance (priority := 10000) boundaryHEPOptionLinearOrder : LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

abbrev literalConeBottomRange :
    (orderedComplexSSet (simplicialCone M)).Subcomplex :=
  SSet.Subcomplex.range (literalConeBottomMap M)

abbrev literalConeBaseLineRange :
    (orderedComplexSSet (simplicialCone M)).Subcomplex :=
  SSet.Subcomplex.range (literalConeBaseLineMap M b)

def literalConeBottomBasepoint :
    (orderedComplexSSet (simplicialCone M)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  orderedComplexVertex (simplicialCone M) (some b)

abbrev literalConeBottomBasepointSubcomplex :
    (orderedComplexSSet (simplicialCone M)).Subcomplex :=
  SSet.Subcomplex.ofSimplex (literalConeBottomBasepoint M b)

omit [Fintype V] in
theorem literalConeBottomBasepoint_le_bottomRange :
    literalConeBottomBasepointSubcomplex M b ≤ literalConeBottomRange M := by
  rw [SSet.Subcomplex.ofSimplex_le_iff]
  refine ⟨orderedComplexVertex M b, ?_⟩
  simpa [literalConeBottomBasepoint, literalConeBottomMap] using
    (OrderedSimplicialMap.toSSetMap_vertex (coneBottomInclusion M) b)

omit [Fintype V] in
@[reassoc]
theorem ι₁_literalConeBaseLineMap :
    SSet.ι₁ ≫ literalConeBaseLineMap M b =
      SSet.const (literalConeBottomBasepoint M b) := by
  rw [literalConeBaseLineMap, ← Category.assoc, SSet.ι₁_comp,
    Category.assoc, ι₁_literalConeCylinderMap, Category.comp_id]
  have hι : (orderedComplexBasepointSubcomplex M b).ι =
      SSet.const (orderedComplexVertex M b) := by
    simpa only [orderedComplexBasepointSubcomplex] using
      (SSet.Subcomplex.ofSimplex_ι (orderedComplexVertex M b))
  rw [hι]
  ext Delta x
  apply Subtype.ext
  ext i
  rfl

omit [Fintype V] in
theorem literalConeBottomBasepoint_le_baseLineRange :
    literalConeBottomBasepointSubcomplex M b ≤ literalConeBaseLineRange M b := by
  rw [SSet.Subcomplex.ofSimplex_le_iff]
  let p : (orderedComplexBasepointSubcomplex M b : SSet).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
    ⟨orderedComplexVertex M b, SSet.Subcomplex.mem_ofSimplex_obj _⟩
  refine ⟨SSet.ι₁.app _ p, ?_⟩
  change (SSet.ι₁ ≫ literalConeBaseLineMap M b).app _ p = _
  rw [ι₁_literalConeBaseLineMap]
  rfl

omit [Fintype V] in
theorem literalCone_ranges_inf_eq_basepoint :
    literalConeBottomRange M ⊓ literalConeBaseLineRange M b =
      literalConeBottomBasepointSubcomplex M b := by
  apply le_antisymm
  · intro Delta z hz
    rcases hz with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    rw [SSet.Subcomplex.mem_ofSimplex_obj_iff]
    refine ⟨SimplexCategory.const _ _ 0, ?_⟩
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    have hι : (orderedComplexBasepointSubcomplex M b).ι =
        SSet.const (orderedComplexVertex M b) := by
      simpa only [orderedComplexBasepointSubcomplex] using
        (SSet.Subcomplex.ofSimplex_ι (orderedComplexVertex M b))
    have hb :
        (((orderedComplexBasepointSubcomplex M b).ι.app Delta y.1).1 i) = b := by
      rw [hι]
      rfl
    have hi := congrArg (fun w => w.1 i) (hx.trans hy.symm)
    change some (x.1 i) =
      (if SSet.stdSimplex.asOrderHom y.2 i = 0 then none
        else some
          (((orderedComplexBasepointSubcomplex M b).ι.app Delta y.1).1 i)) at hi
    rw [hb] at hi
    have ht : SSet.stdSimplex.asOrderHom y.2 i ≠ 0 := by
      intro ht
      rw [ht] at hi
      cases hi
    have hxb : x.1 i = b := by simpa [ht] using hi
    rw [← hx]
    change some b = some (x.1 i)
    rw [hxb]
  · exact le_inf
      (literalConeBottomBasepoint_le_bottomRange M b)
      (literalConeBottomBasepoint_le_baseLineRange M b)

omit [Fintype V] in
instance literalConeBottomMap_mono : Mono (literalConeBottomMap M) := by
  rw [NatTrans.mono_iff_mono_app]
  intro Delta
  rw [mono_iff_injective]
  intro x y h
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  have hi := congrArg (fun z => z.1 i) h
  exact Option.some.inj hi

omit [Fintype V] in
def basepointToLiteralConeBottomBasepoint :
    (orderedComplexBasepointSubcomplex M b : SSet) ⟶
      (literalConeBottomBasepointSubcomplex M b : SSet) :=
  SSet.Subcomplex.lift
    ((orderedComplexBasepointSubcomplex M b).ι ≫ literalConeBottomMap M)
    (by
      rw [← SSet.Subcomplex.image_eq_range]
      change (SSet.Subcomplex.ofSimplex (orderedComplexVertex M b)).image
          (literalConeBottomMap M) ≤ _
      rw [SSet.Subcomplex.image_ofSimplex]
      rw [show (literalConeBottomMap M).app _ (orderedComplexVertex M b) =
          literalConeBottomBasepoint M b by
        simpa [literalConeBottomBasepoint, literalConeBottomMap] using
          (OrderedSimplicialMap.toSSetMap_vertex (coneBottomInclusion M) b)])

omit [Fintype V] in
instance basepointToLiteralConeBottomBasepoint_epi :
    Epi (basepointToLiteralConeBottomBasepoint M b) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Delta
  rw [epi_iff_surjective]
  intro z
  have hz := z.2
  rw [SSet.Subcomplex.mem_ofSimplex_obj_iff] at hz
  rcases hz with ⟨f, hf⟩
  let x0 : (orderedComplexSSet M).obj Delta :=
    (orderedComplexSSet M).map f.op (orderedComplexVertex M b)
  have hx0 : x0 ∈ (orderedComplexBasepointSubcomplex M b).obj Delta := by
    rw [orderedComplexBasepointSubcomplex,
      SSet.Subcomplex.mem_ofSimplex_obj_iff]
    exact ⟨f, rfl⟩
  refine ⟨⟨x0, hx0⟩, ?_⟩
  apply Subtype.ext
  rw [← hf]
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  rfl

def literalConeBoundarySubcomplex :
    (orderedComplexSSet (simplicialCone M)).Subcomplex :=
  literalConeBottomRange M ⊔ literalConeBaseLineRange M b

omit [Fintype V] in
def literalConeBoundaryBicartSq :
    SSet.Subcomplex.BicartSq
      (literalConeBottomBasepointSubcomplex M b)
      (literalConeBottomRange M)
      (literalConeBaseLineRange M b)
      (literalConeBoundarySubcomplex M b) where
  sup_eq := rfl
  inf_eq := literalCone_ranges_inf_eq_basepoint M b

omit [Fintype V] in
noncomputable def bottomRangeHomotopy {Y : SSet.{u}}
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ Y) :
    (literalConeBottomRange M : SSet) ⊗ Δ[1] ⟶ Y :=
  inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) ▷ Δ[1] ≫ h

omit [Fintype V] in
theorem basepointToBottomRange_inv_toRange :
    basepointToLiteralConeBottomBasepoint M b ≫
        SSet.Subcomplex.homOfLE
          (literalConeBottomBasepoint_le_bottomRange M b) ≫
        inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) =
      (orderedComplexBasepointSubcomplex M b).ι := by
  have he :
      basepointToLiteralConeBottomBasepoint M b ≫
          SSet.Subcomplex.homOfLE
            (literalConeBottomBasepoint_le_bottomRange M b) =
        (orderedComplexBasepointSubcomplex M b).ι ≫
          SSet.Subcomplex.toRange (literalConeBottomMap M) := by
    rw [← cancel_mono (literalConeBottomRange M).ι]
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι]
    exact SSet.Subcomplex.lift_ι _ _
  rw [← Category.assoc, he, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

omit [Fintype V] in
instance whiskerRight_basepointToLiteralConeBottomBasepoint_epi
    (T : SSet.{u}) :
    Epi (basepointToLiteralConeBottomBasepoint M b ▷ T) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Delta
  rw [epi_iff_surjective]
  rintro ⟨z, t⟩
  have hepi := (NatTrans.epi_iff_epi_app
    (basepointToLiteralConeBottomBasepoint M b)).mp inferInstance Delta
  rw [epi_iff_surjective] at hepi
  rcases hepi z with ⟨x, rfl⟩
  exact ⟨(x, t), rfl⟩

omit [Fintype V] in
theorem bottomRangeHomotopy_zero_on_intersection
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0) :
    SSet.Subcomplex.homOfLE
          (literalConeBottomBasepoint_le_bottomRange M b) ▷ Δ[1] ≫
        bottomRangeHomotopy M h = 0 := by
  rw [← cancel_epi
    (basepointToLiteralConeBottomBasepoint M b ▷ Δ[1])]
  calc
    (basepointToLiteralConeBottomBasepoint M b ▷ Δ[1]) ≫
          (SSet.Subcomplex.homOfLE
              (literalConeBottomBasepoint_le_bottomRange M b) ▷ Δ[1]) ≫
          bottomRangeHomotopy M h =
        ((basepointToLiteralConeBottomBasepoint M b ≫
              SSet.Subcomplex.homOfLE
                (literalConeBottomBasepoint_le_bottomRange M b) ≫
              inv (SSet.Subcomplex.toRange (literalConeBottomMap M))) ▷ Δ[1]) ≫ h := by
          simp only [bottomRangeHomotopy, comp_whiskerRight_assoc,
            Category.assoc]
    _ = (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h := by
      rw [basepointToBottomRange_inv_toRange]
    _ = 0 := hrel
    _ = (basepointToLiteralConeBottomBasepoint M b ▷ Δ[1]) ≫ 0 := by
      rfl

omit [Fintype V] in
noncomputable def literalConeBoundaryHomotopy
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0) :
    (literalConeBoundarySubcomplex M b : SSet) ⊗ Δ[1] ⟶
      underlyingSSet A := by
  let sq := literalConeBoundaryBicartSq M b
  let push := (SSet.Subcomplex.BicartSq.isPushout sq).map
    (tensorRight Δ[1])
  exact push.desc (bottomRangeHomotopy M h) 0 (by
    calc
      _ = 0 := bottomRangeHomotopy_zero_on_intersection M b A h hrel
      _ = _ ≫ 0 := by ext Delta x; rfl)

omit [Fintype V] in
@[reassoc]
theorem literalConeBoundaryHomotopy_bottom
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0) :
    SSet.Subcomplex.homOfLE
          (show literalConeBottomRange M ≤ literalConeBoundarySubcomplex M b
            from le_sup_left) ▷ Δ[1] ≫
        literalConeBoundaryHomotopy M b A h hrel =
      bottomRangeHomotopy M h := by
  exact ((SSet.Subcomplex.BicartSq.isPushout
    (literalConeBoundaryBicartSq M b)).map
      (tensorRight Δ[1])).inl_desc _ _ _

omit [Fintype V] in
@[reassoc]
theorem literalConeBoundaryHomotopy_baseLine
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0) :
    SSet.Subcomplex.homOfLE
          (show literalConeBaseLineRange M b ≤ literalConeBoundarySubcomplex M b
            from le_sup_right) ▷ Δ[1] ≫
        literalConeBoundaryHomotopy M b A h hrel = 0 := by
  exact ((SSet.Subcomplex.BicartSq.isPushout
    (literalConeBoundaryBicartSq M b)).map
      (tensorRight Δ[1])).inr_desc _ _ _

omit [Fintype V] in
theorem bottomRangeHomotopy_initial
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (h₀ : SSet.ι₀ ≫ h = 0) :
    SSet.ι₀ ≫ bottomRangeHomotopy M h = 0 := by
  calc
    SSet.ι₀ ≫ bottomRangeHomotopy M h =
        (SSet.ι₀ ≫
          inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) ▷ Δ[1]) ≫ h := by
      rw [bottomRangeHomotopy, Category.assoc]
    _ = (inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) ≫
          SSet.ι₀) ≫ h := by rw [SSet.ι₀_comp]
    _ = inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) ≫
          (SSet.ι₀ ≫ h) := Category.assoc _ _ _
    _ = _ ≫ 0 := by rw [h₀]
    _ = 0 := by ext Delta x; rfl

omit [Fintype V] in
theorem bottomRangeHomotopy_terminal
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (f : orderedComplexSSet M ⟶ underlyingSSet A)
    (h₁ : SSet.ι₁ ≫ h = f) :
    SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
        SSet.ι₁ ≫ bottomRangeHomotopy M h = f := by
  calc
    SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
          SSet.ι₁ ≫ bottomRangeHomotopy M h =
        SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
          (SSet.ι₁ ≫
            inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) ▷ Δ[1]) ≫ h := by
              simp only [bottomRangeHomotopy, Category.assoc]
    _ = SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
          (inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) ≫
            SSet.ι₁) ≫ h := by rw [SSet.ι₁_comp]
    _ = SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
          inv (SSet.Subcomplex.toRange (literalConeBottomMap M)) ≫
          SSet.ι₁ ≫ h := by simp only [Category.assoc]
    _ = SSet.ι₁ ≫ h := by
      rw [IsIso.hom_inv_id_assoc]
    _ = f := h₁

omit [Fintype V] in
theorem literalConeBoundaryHomotopy_initial
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0)
    (h₀ : SSet.ι₀ ≫ h = 0) :
    SSet.ι₀ ≫ literalConeBoundaryHomotopy M b A h hrel = 0 := by
  let push := SSet.Subcomplex.BicartSq.isPushout
    (literalConeBoundaryBicartSq M b)
  apply push.hom_ext
  · calc
      _ = SSet.ι₀ ≫
          (SSet.Subcomplex.homOfLE
            (show literalConeBottomRange M ≤ literalConeBoundarySubcomplex M b
              from le_sup_left) ▷ Δ[1]) ≫
          literalConeBoundaryHomotopy M b A h hrel := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ bottomRangeHomotopy M h := by
        rw [literalConeBoundaryHomotopy_bottom]
      _ = 0 := bottomRangeHomotopy_initial M A h h₀
      _ = _ ≫ 0 := by ext Delta x; rfl
  · calc
      _ = SSet.ι₀ ≫
          (SSet.Subcomplex.homOfLE
            (show literalConeBaseLineRange M b ≤ literalConeBoundarySubcomplex M b
              from le_sup_right) ▷ Δ[1]) ≫
          literalConeBoundaryHomotopy M b A h hrel := by
            rw [SSet.ι₀_comp_assoc]
      _ = SSet.ι₀ ≫ 0 := by
        rw [literalConeBoundaryHomotopy_baseLine]
      _ = 0 := by ext Delta x; rfl
      _ = _ ≫ 0 := by ext Delta x; rfl

omit [Fintype V] in
theorem literalConeBottomMap_factor_boundary :
    SSet.Subcomplex.toRange (literalConeBottomMap M) ≫
        SSet.Subcomplex.homOfLE
          (show literalConeBottomRange M ≤ literalConeBoundarySubcomplex M b
            from le_sup_left) ≫
        (literalConeBoundarySubcomplex M b).ι =
      literalConeBottomMap M := by
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
    SSet.Subcomplex.toRange_ι]

omit [Fintype V] in
theorem literalConeBaseLineMap_factor_boundary :
    SSet.Subcomplex.toRange (literalConeBaseLineMap M b) ≫
        SSet.Subcomplex.homOfLE
          (show literalConeBaseLineRange M b ≤ literalConeBoundarySubcomplex M b
            from le_sup_right) ≫
        (literalConeBoundarySubcomplex M b).ι =
      literalConeBaseLineMap M b := by
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
    SSet.Subcomplex.toRange_ι]

/- The `Delta[0]` identifications needed to state the endpoint equations
without importing the later reverse-criterion module. -/
def boundaryDeltaZeroProjection (X : SSet.{u}) : X ⊗ Δ[0] ⟶ X :=
  fst X Δ[0]

def boundaryTensorDeltaZeroMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    X ⊗ Δ[0] ⟶ Y :=
  boundaryDeltaZeroProjection X ≫ f

@[reassoc]
theorem boundaryDeltaZeroProjection_comp_ι₀ (X : SSet.{u}) :
    boundaryDeltaZeroProjection X ≫ SSet.ι₀ =
      X ◁ SSet.stdSimplex.δ (1 : Fin 2) := by
  apply CartesianMonoidalCategory.hom_ext
  · ext Delta x
    rfl
  · rw [Category.assoc, SSet.ι₀_snd,
      CartesianMonoidalCategory.whiskerLeft_snd,
      SSet.stdSimplex.δ_one_eq_const]
    ext Delta x
    rfl

@[reassoc]
theorem boundaryDeltaZeroProjection_comp_ι₁ (X : SSet.{u}) :
    boundaryDeltaZeroProjection X ≫ SSet.ι₁ =
      X ◁ SSet.stdSimplex.δ (0 : Fin 2) := by
  apply CartesianMonoidalCategory.hom_ext
  · ext Delta x
    rfl
  · rw [Category.assoc, SSet.ι₁_snd,
      CartesianMonoidalCategory.whiskerLeft_snd,
      SSet.stdSimplex.δ_zero_eq_const]
    ext Delta x
    rfl

theorem boundaryTensorDeltaZeroMap_endpoint₀ {X Y : SSet.{u}}
    (h : X ⊗ Δ[1] ⟶ Y) :
    boundaryTensorDeltaZeroMap (SSet.ι₀ ≫ h) =
      X ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ h := by
  rw [boundaryTensorDeltaZeroMap, ← Category.assoc,
    boundaryDeltaZeroProjection_comp_ι₀]

theorem boundaryTensorDeltaZeroMap_endpoint₁ {X Y : SSet.{u}}
    (h : X ⊗ Δ[1] ⟶ Y) :
    boundaryTensorDeltaZeroMap (SSet.ι₁ ≫ h) =
      X ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ h := by
  rw [boundaryTensorDeltaZeroMap, ← Category.assoc,
    boundaryDeltaZeroProjection_comp_ι₁]

omit [Fintype V] in
theorem literalConeBoundaryHomotopy_hep_initial
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0)
    (h₀ : SSet.ι₀ ≫ h = 0) :
    (literalConeBoundarySubcomplex M b : SSet) ◁
          SSet.stdSimplex.δ (1 : Fin 2) ≫
        literalConeBoundaryHomotopy M b A h hrel = 0 := by
  rw [← boundaryTensorDeltaZeroMap_endpoint₀,
    literalConeBoundaryHomotopy_initial M b A h hrel h₀]
  ext Delta x
  rfl

omit [Fintype V] in
theorem literalConeBoundaryHomotopy_hep_terminal_bottom
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0)
    (f : orderedComplexSSet M ⟶ underlyingSSet A)
    (h₁ : SSet.ι₁ ≫ h = f) :
    SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[0] ≫
        (literalConeBottomRange M : SSet) ◁
          SSet.stdSimplex.δ (0 : Fin 2) ≫
        SSet.Subcomplex.homOfLE
          (show literalConeBottomRange M ≤ literalConeBoundarySubcomplex M b
            from le_sup_left) ▷ Δ[1] ≫
        literalConeBoundaryHomotopy M b A h hrel =
      boundaryTensorDeltaZeroMap f := by
  have hex :
      (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[0]) ≫
          (literalConeBottomRange M : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2) =
        orderedComplexSSet M ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫
          (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[1]) := by
    exact (whisker_exchange
      (SSet.Subcomplex.toRange (literalConeBottomMap M))
      (SSet.stdSimplex.δ (0 : Fin 2))).symm
  calc
    _ = orderedComplexSSet M ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫
          (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[1]) ≫
          (SSet.Subcomplex.homOfLE
            (show literalConeBottomRange M ≤ literalConeBoundarySubcomplex M b
              from le_sup_left) ▷ Δ[1]) ≫
          literalConeBoundaryHomotopy M b A h hrel := by
      simp only [← Category.assoc]
      rw [hex]
    _ = orderedComplexSSet M ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ h := by
      rw [literalConeBoundaryHomotopy_bottom]
      rw [bottomRangeHomotopy]
      rw [← comp_whiskerRight_assoc,
        IsIso.hom_inv_id, id_whiskerRight, Category.id_comp]
    _ = boundaryTensorDeltaZeroMap (SSet.ι₁ ≫ h) :=
      (boundaryTensorDeltaZeroMap_endpoint₁ h).symm
    _ = boundaryTensorDeltaZeroMap f := by rw [h₁]

omit [Fintype V] in
theorem literalConeBoundaryHomotopy_hep_terminal_baseLine
    (A : SimplicialObject AddCommGrpCat.{u})
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ underlyingSSet A)
    (hrel : (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ h = 0) :
    SSet.Subcomplex.toRange (literalConeBaseLineMap M b) ▷ Δ[0] ≫
        (literalConeBaseLineRange M b : SSet) ◁
          SSet.stdSimplex.δ (0 : Fin 2) ≫
        SSet.Subcomplex.homOfLE
          (show literalConeBaseLineRange M b ≤ literalConeBoundarySubcomplex M b
            from le_sup_right) ▷ Δ[1] ≫
        literalConeBoundaryHomotopy M b A h hrel = 0 := by
  calc
    _ = SSet.Subcomplex.toRange (literalConeBaseLineMap M b) ▷ Δ[0] ≫
          (literalConeBaseLineRange M b : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2) ≫ 0 := by
      rw [literalConeBoundaryHomotopy_baseLine]
    _ = 0 := by ext Delta x; rfl

end GeneralSphereT.SimplicialCochain
