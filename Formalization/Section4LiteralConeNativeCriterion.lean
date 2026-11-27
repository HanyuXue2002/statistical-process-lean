import Formalization.Section4LiteralConeSSetContraction
import Formalization.Section4SimplicialConeComparison
import Formalization.Section4NativeRelativeHomotopyGroup

set_option linter.style.header false

/-!
# Section 4: the native pointed cone criterion for the literal cone

This file uses the actual cylinder contraction of the `Option V` cone to
turn a pointed extension over that same literal cone into Mathlib's native
relative nullhomotopy class.  It is the direct topological bridge from the
cone employed by the finite cochain argument to
`SSet.RelativeMorphism.HomotopyClass`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.SimplicialCochain

universe u

open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

variable {V : Type u} [LinearOrder V] [Fintype V]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) literalCriterionOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) literalCriterionOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) literalCriterionOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- The bottom inclusion of the literal cone as an actual simplicial-set
map. -/
abbrev literalConeBottomMap :
    orderedComplexSSet M ⟶ orderedComplexSSet (simplicialCone M) :=
  (coneBottomInclusion M).toSSetMap

variable (b : V)

/-- The trajectory of the chosen source basepoint during the literal cone
contraction.  Its range is the simplicial basepoint cone `C_v{b}`. -/
def literalConeBaseLineMap :
    (orderedComplexBasepointSubcomplex M b : SSet) ⊗ Δ[1] ⟶
      orderedComplexSSet (simplicialCone M) :=
  ((orderedComplexBasepointSubcomplex M b).ι ≫
      literalConeBottomMap M) ▷ Δ[1] ≫
    literalConeCylinderMap M

variable (A : SimplicialObject AddCommGrpCat.{u})

/-- A pointed extension over the literal `Option V` cone.  Besides
restricting to `f` on the bottom, it is zero at the apex and along the whole
basepoint cone. -/
structure LiteralPointedExtension
    (f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A) : Type u where
  map : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A
  bottom : literalConeBottomMap M ≫ map = f.map
  apex : SSet.const (literalConeApex M) ≫ map =
    (0 : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A)
  baseLine : literalConeBaseLineMap M b ≫ map =
    (0 : (orderedComplexBasepointSubcomplex M b : SSet) ⊗ Δ[1] ⟶
      underlyingSSet A)

namespace LiteralPointedExtension

variable {M b A}
variable {f : NativeRelativeMorphism
  (orderedComplexBasepointSubcomplex M b) A}

/-- The source contraction, followed by a literal pointed extension,
produces a relative homotopy from zero to the bottom map. -/
def zeroToRelativeHomotopy (E : LiteralPointedExtension M b A f) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f where
  h := literalConeBottomMap M ▷ Δ[1] ≫
    literalConeCylinderMap M ≫ E.map
  h₀ := by
    have hc₀ : SSet.ι₀ ≫ (literalConeCylinderMap M ≫ E.map) = 0 := by
      calc
        _ = (SSet.ι₀ ≫ literalConeCylinderMap M) ≫ E.map :=
          (Category.assoc _ _ _).symm
        _ = SSet.const (literalConeApex M) ≫ E.map := by
          rw [ι₀_literalConeCylinderMap]
        _ = 0 := E.apex
    change SSet.ι₀ ≫ literalConeBottomMap M ▷ Δ[1] ≫
        literalConeCylinderMap M ≫ E.map =
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A).map
    calc
      _ = (SSet.ι₀ ≫ literalConeBottomMap M ▷ Δ[1]) ≫
          (literalConeCylinderMap M ≫ E.map) :=
        (Category.assoc _ _ _).symm
      _ = (literalConeBottomMap M ≫ SSet.ι₀) ≫
          (literalConeCylinderMap M ≫ E.map) := by
        rw [SSet.ι₀_comp]
      _ = literalConeBottomMap M ≫
          (SSet.ι₀ ≫ (literalConeCylinderMap M ≫ E.map)) :=
        Category.assoc _ _ _
      _ = literalConeBottomMap M ≫ 0 := by rw [hc₀]
      _ = 0 := by
        ext Δ x
        rfl
      _ = (0 : NativeRelativeMorphism
          (orderedComplexBasepointSubcomplex M b) A).map :=
        (relativeMorphism_zero_map
          (orderedComplexBasepointSubcomplex M b) A).symm
  h₁ := by
    have hc₁ : SSet.ι₁ ≫ (literalConeCylinderMap M ≫ E.map) =
        E.map := by
      calc
        _ = (SSet.ι₁ ≫ literalConeCylinderMap M) ≫ E.map :=
          (Category.assoc _ _ _).symm
        _ = 𝟙 _ ≫ E.map := by
          rw [ι₁_literalConeCylinderMap]
        _ = E.map := Category.id_comp _
    change SSet.ι₁ ≫ literalConeBottomMap M ▷ Δ[1] ≫
        literalConeCylinderMap M ≫ E.map = f.map
    calc
      _ = (SSet.ι₁ ≫ literalConeBottomMap M ▷ Δ[1]) ≫
          (literalConeCylinderMap M ≫ E.map) :=
        (Category.assoc _ _ _).symm
      _ = (literalConeBottomMap M ≫ SSet.ι₁) ≫
          (literalConeCylinderMap M ≫ E.map) := by
        rw [SSet.ι₁_comp]
      _ = literalConeBottomMap M ≫
          (SSet.ι₁ ≫ (literalConeCylinderMap M ≫ E.map)) :=
        Category.assoc _ _ _
      _ = literalConeBottomMap M ≫ E.map := by rw [hc₁]
      _ = f.map := E.bottom
  rel := by
    calc
      (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫
          (literalConeBottomMap M ▷ Δ[1] ≫
            literalConeCylinderMap M ≫ E.map) =
        literalConeBaseLineMap M b ≫ E.map := by
          rw [← comp_whiskerRight_assoc]
          rfl
      _ = 0 := E.baseLine
      _ = fst (orderedComplexBasepointSubcomplex M b : SSet) Δ[1] ≫
          zeroBoundary (orderedComplexBasepointSubcomplex M b) A ≫
            (zeroSubcomplex A).ι :=
        (cylinder_zeroBoundary
          (orderedComplexBasepointSubcomplex M b) A).symm

omit [Fintype V] in
/-- Native homotopy-class form of the literal pointed cone criterion. -/
theorem class_eq_zero (E : LiteralPointedExtension M b A f) :
    f.homotopyClass =
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A).homotopyClass :=
  E.zeroToRelativeHomotopy.eq.symm

end LiteralPointedExtension

end GeneralSphereT.SimplicialCochain
