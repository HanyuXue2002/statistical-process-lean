import Formalization.Section4NativeRelativeHomotopyGroup
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

set_option linter.style.header false

/-!
# Section 4: a categorical simplicial cone

Mathlib has products with `Δ[1]`, all colimits of simplicial sets, and
relative homotopies, but no named simplicial cone.  We define the cone on
`X` as the pushout which collapses the `1`-end of `X ⊗ Δ[1]` to
`Δ[0]`.  Its universal property identifies maps out of the cone with
nullhomotopies.  A relative version records the condition that the homotopy
is fixed on a source subcomplex.

Thus the cone criterion used in Section 4 is realized by an actual
simplicial set and Mathlib's actual `RelativeMorphism.Homotopy`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory Limits

namespace GeneralSphereT.Section4
namespace NativeSimplicialCone

universe u

open UnderlyingSSet
open RelativeMapping
open NativeRelativeHomotopyGroup

variable {X Y : SSet.{u}}

/-- The unique map from `X` to the terminal standard simplex `Δ[0]`. -/
def collapse (X : SSet.{u}) : X ⟶ Δ[0] :=
  SSet.stdSimplex.isTerminalObj₀.from X

/-- The simplicial cone on `X`, formed by collapsing the `1`-end of its
cylinder to a point. -/
abbrev cone (X : SSet.{u}) : SSet.{u} :=
  pushout (SSet.ι₁ : X ⟶ X ⊗ Δ[1]) (collapse X)

/-- Inclusion of the cylinder into the cone. -/
abbrev cylinderInclusion (X : SSet.{u}) : X ⊗ Δ[1] ⟶ cone X :=
  pushout.inl _ _

/-- Inclusion of the cone apex. -/
abbrev apexInclusion (X : SSet.{u}) : Δ[0] ⟶ cone X :=
  pushout.inr _ _

/-- Inclusion of the bottom of the cone. -/
def bottomInclusion (X : SSet.{u}) : X ⟶ cone X :=
  SSet.ι₀ ≫ cylinderInclusion X

/-- The collapsed end of the cylinder is the apex. -/
theorem end_glue (X : SSet.{u}) :
    SSet.ι₁ ≫ cylinderInclusion X =
      collapse X ≫ apexInclusion X :=
  pushout.condition

/-- Going first to the terminal simplex and then taking the constant map at
`y` is the constant map at `y`. -/
theorem collapse_comp_const (X : SSet.{u})
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    collapse X ≫ SSet.const (X := Δ[0]) y = SSet.const (X := X) y := by
  exact SSet.comp_const (collapse X) y

/-- A map out of the categorical cone extending `f` and carrying the apex
to `y`. -/
@[ext]
structure Extension (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) : Type u where
  map : cone X ⟶ Y
  bottom : bottomInclusion X ≫ map = f
  apex : apexInclusion X ≫ map = SSet.const (X := Δ[0]) y

namespace Extension

variable {f : X ⟶ Y}
variable {y : Y.obj (Opposite.op (SimplexCategory.mk 0))}

/-- A cone extension yields the corresponding actual simplicial
nullhomotopy. -/
def toHomotopy (E : Extension f y) :
    SSet.Homotopy f (SSet.const (X := X) y) where
  h := cylinderInclusion X ≫ E.map
  h₀ := by
    change SSet.ι₀ ≫ cylinderInclusion X ≫ E.map = f
    calc
      _ = (SSet.ι₀ ≫ cylinderInclusion X) ≫ E.map :=
        (Category.assoc _ _ _).symm
      _ = f := E.bottom
  h₁ := by
    change SSet.ι₁ ≫ cylinderInclusion X ≫ E.map =
      SSet.const (X := X) y
    calc
      _ = (SSet.ι₁ ≫ cylinderInclusion X) ≫ E.map :=
        (Category.assoc _ _ _).symm
      _ = (collapse X ≫ apexInclusion X) ≫ E.map := by
        rw [end_glue]
      _ = collapse X ≫ (apexInclusion X ≫ E.map) :=
        Category.assoc _ _ _
      _ = collapse X ≫ SSet.const (X := Δ[0]) y := by rw [E.apex]
      _ = SSet.const (X := X) y := collapse_comp_const X y
  rel := by
    ext Δ x
    exact False.elim (by simpa using x.1.property)

/-- An actual simplicial nullhomotopy descends through the cone pushout. -/
def ofHomotopy (H : SSet.Homotopy f (SSet.const (X := X) y)) :
    Extension f y where
  map := pushout.desc H.h (SSet.const (X := Δ[0]) y) (by
    rw [SSet.Homotopy.h₁ H, collapse_comp_const])
  bottom := by
    rw [bottomInclusion, Category.assoc, pushout.inl_desc,
      SSet.Homotopy.h₀ H]
  apex := by
    rw [pushout.inr_desc]

/-- Maps out of the categorical cone are equivalent to actual simplicial
nullhomotopies. -/
def equivHomotopy :
    Extension f y ≃ SSet.Homotopy f (SSet.const (X := X) y) where
  toFun := toHomotopy
  invFun := ofHomotopy
  left_inv E := by
    apply Extension.ext
    apply pushout.hom_ext
    · apply pushout.inl_desc
    · rw [E.apex]
      apply pushout.inr_desc
  right_inv H := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact pushout.inl_desc _ _ _

end Extension

/-! ## The relative pointed cone criterion -/

variable (P : X.Subcomplex)
variable (A : SimplicialObject AddCommGrpCat.{u})

/-- A genuine map from the categorical cone to a simplicial abelian target,
extending the native relative map `f`, sending the apex to zero, and fixed at
zero on `P` along the whole cylinder. -/
@[ext]
structure PointedExtension
    (f : NativeRelativeMorphism P A) : Type u extends
      Extension f.map (zeroVertex A) where
  rel : P.ι ▷ Δ[1] ≫ cylinderInclusion X ≫ toExtension.map =
    fst (P : SSet) Δ[1] ≫ zeroBoundary P A ≫ (zeroSubcomplex A).ι

namespace PointedExtension

variable {P A}
variable {f : NativeRelativeMorphism P A}

/-- A pointed cone extension gives a native relative nullhomotopy. -/
def toRelativeHomotopy (E : PointedExtension P A f) :
    SSet.RelativeMorphism.Homotopy f
      (0 : NativeRelativeMorphism P A) where
  h := cylinderInclusion X ≫ E.map
  h₀ := by
    calc
      _ = (SSet.ι₀ ≫ cylinderInclusion X) ≫ E.map :=
        (Category.assoc _ _ _).symm
      _ = f.map := E.bottom
  h₁ := by
    calc
      _ = (SSet.ι₁ ≫ cylinderInclusion X) ≫ E.map :=
        (Category.assoc _ _ _).symm
      _ = (collapse X ≫ apexInclusion X) ≫ E.map := by
        rw [end_glue]
      _ = collapse X ≫ (apexInclusion X ≫ E.map) :=
        Category.assoc _ _ _
      _ = collapse X ≫
          SSet.const (X := Δ[0]) (zeroVertex A) := by rw [E.apex]
      _ = SSet.const (X := X) (zeroVertex A) :=
        collapse_comp_const X (zeroVertex A)
      _ = (0 : X ⟶ underlyingSSet A) :=
        const_zeroVertex_eq_zeroMap (X := X) A
      _ = (0 : NativeRelativeMorphism P A).map :=
        (relativeMorphism_zero_map P A).symm
  rel := E.rel

/-- A native relative nullhomotopy descends through the categorical cone. -/
def ofRelativeHomotopy
    (H : SSet.RelativeMorphism.Homotopy f
      (0 : NativeRelativeMorphism P A)) :
    PointedExtension P A f where
  map := pushout.desc H.h (SSet.const (X := Δ[0]) (zeroVertex A)) (by
    calc
      SSet.ι₁ ≫ H.h = (0 : NativeRelativeMorphism P A).map := H.h₁
      _ = (0 : X ⟶ underlyingSSet A) := relativeMorphism_zero_map P A
      _ = SSet.const (X := X) (zeroVertex A) :=
        (const_zeroVertex_eq_zeroMap (X := X) A).symm
      _ = collapse X ≫
          SSet.const (X := Δ[0]) (zeroVertex A) :=
        (collapse_comp_const X (zeroVertex A)).symm)
  bottom := by
    rw [bottomInclusion, Category.assoc, pushout.inl_desc, H.h₀]
  apex := by
    rw [pushout.inr_desc]
  rel := by
    simpa only [pushout.inl_desc, Category.assoc] using H.rel

/-- The pointed cone criterion as an equivalence of actual data: extending
over the categorical cone, relative to `P`, is exactly giving a native
relative nullhomotopy. -/
def equivRelativeHomotopy :
    PointedExtension P A f ≃
      SSet.RelativeMorphism.Homotopy f
        (0 : NativeRelativeMorphism P A) where
  toFun := toRelativeHomotopy
  invFun := ofRelativeHomotopy
  left_inv E := by
    apply PointedExtension.ext
    apply pushout.hom_ext
    · apply pushout.inl_desc
    · rw [E.apex]
      apply pushout.inr_desc
  right_inv H := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact pushout.inl_desc _ _ _

/-- A pointed cone extension makes the represented native homotopy class
zero. -/
theorem class_eq_zero (E : PointedExtension P A f) :
    f.homotopyClass =
      (0 : NativeRelativeMorphism P A).homotopyClass :=
  E.toRelativeHomotopy.eq

end PointedExtension

end NativeSimplicialCone
end GeneralSphereT.Section4
