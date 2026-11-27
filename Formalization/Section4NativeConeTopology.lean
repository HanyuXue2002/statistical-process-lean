import Formalization.Section4RelativeMappingGroups
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

set_option linter.style.header false

/-!
# Section 4: native relative homotopies and cone fillings

Mathlib does not currently contain a named simplicial cone functor.  For the
cone criterion used in Section 4, however, the needed topological object is
already present: a pointed map extends over a cone precisely by giving a
homotopy from that map to the constant map, relative to the basepoint.

This file connects the strictly-zero relative maps used by the algebraic
proof with `SSet.RelativeMorphism` and its actual simplicial homotopies.  It
also proves the pointwise-difference construction for two cone fillings.  In
particular, these statements use Mathlib's native `HomotopyClass`; no
presentation by a chosen subgroup of "null maps" occurs here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.Section4
namespace NativeConeTopology

universe u

open UnderlyingSSet
open RelativeMapping

variable {X W : SSet.{u}} (P : X.Subcomplex)
variable (A : SimplicialObject AddCommGrpCat.{u})

/-- Mathlib's native relative maps from `(X,P)` to the underlying simplicial
set of `A`, with boundary fixed at zero. -/
abbrev NativeRelativeMorphism :=
  SSet.RelativeMorphism P (zeroSubcomplex A) (zeroBoundary P A)

/-- The native relative morphism represented by the constant zero map. -/
def zeroRelativeMorphism : NativeRelativeMorphism P A :=
  RelativeZeroMaps.toRelativeMorphism P A 0

@[simp]
theorem zeroRelativeMorphism_map :
    (zeroRelativeMorphism P A).map =
      (0 : X ⟶ underlyingSSet A) :=
  rfl

/-- Forget a native relative morphism to its underlying strictly-zero map. -/
def NativeRelativeMorphism.toRelativeZeroMap
    (f : NativeRelativeMorphism P A) : RelativeZeroMaps P A :=
  ⟨f.map, by
    change P.ι ≫ f.map = 0
    rw [f.comm, zeroBoundary_comp_inclusion]⟩

@[simp]
theorem NativeRelativeMorphism.toRelativeZeroMap_coe
    (f : NativeRelativeMorphism P A) :
    (f.toRelativeZeroMap P A : X ⟶ underlyingSSet A) = f.map :=
  rfl

/-- Strictly-zero maps and Mathlib's relative morphisms with zero boundary
are the same data. -/
def relativeZeroMapsEquiv :
    RelativeZeroMaps P A ≃ NativeRelativeMorphism P A where
  toFun := RelativeZeroMaps.toRelativeMorphism P A
  invFun := NativeRelativeMorphism.toRelativeZeroMap P A
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

@[simp]
theorem relativeZeroMapsEquiv_apply_map (f : RelativeZeroMaps P A) :
    (relativeZeroMapsEquiv P A f).map = f.1 :=
  rfl

@[simp]
theorem relativeZeroMapsEquiv_symm_apply_coe
    (f : NativeRelativeMorphism P A) :
    ((relativeZeroMapsEquiv P A).symm f : X ⟶ underlyingSSet A) = f.map :=
  rfl

/-! ## Pointwise operations on homotopies -/

@[simp]
theorem subMap_app_apply (f g : W ⟶ underlyingSSet A)
    (Δ : SimplexCategoryᵒᵖ) (x : W.obj Δ) :
    (f - g).app Δ x = f.app Δ x - g.app Δ x :=
  by
    rw [sub_eq_add_neg]
    change (addMap f (negMap g)).app Δ x = _
    simp only [addMap_app_apply, negMap_app_apply, sub_eq_add_neg]

/-- Precomposition distributes over pointwise subtraction. -/
theorem comp_subMap (k : W ⟶ X) (f g : X ⟶ underlyingSSet A) :
    k ≫ (f - g) = (k ≫ f) - (k ≫ g) := by
  rw [sub_eq_add_neg]
  change k ≫ addMap f (negMap g) =
    addMap (k ≫ f) (negMap (k ≫ g))
  ext Δ x
  rfl

@[simp]
theorem relativeZeroMapsEquiv_sub_map
    (f g : RelativeZeroMaps P A) :
    (relativeZeroMapsEquiv P A (f - g)).map =
      (relativeZeroMapsEquiv P A f).map -
        (relativeZeroMapsEquiv P A g).map :=
  rfl

/-- The constant zero boundary remains zero after projection off the
interval. -/
theorem cylinder_zeroBoundary :
    fst (P : SSet) Δ[1] ≫ zeroBoundary P A ≫ (zeroSubcomplex A).ι =
      (0 : (P : SSet) ⊗ Δ[1] ⟶ underlyingSSet A) := by
  rw [zeroBoundary_comp_inclusion]
  ext Δ x
  rfl

/-- Pointwise subtraction of two actual relative simplicial homotopies.

This is the basic topological operation behind the lower-cone-minus-upper-
cone convention in the two-cone argument. -/
def homotopySub
    {f₀ f₁ g₀ g₁ : RelativeZeroMaps P A}
    (Hf : SSet.RelativeMorphism.Homotopy
      (relativeZeroMapsEquiv P A f₀) (relativeZeroMapsEquiv P A f₁))
    (Hg : SSet.RelativeMorphism.Homotopy
      (relativeZeroMapsEquiv P A g₀) (relativeZeroMapsEquiv P A g₁)) :
    SSet.RelativeMorphism.Homotopy
      (relativeZeroMapsEquiv P A (f₀ - g₀))
      (relativeZeroMapsEquiv P A (f₁ - g₁)) where
  h := Hf.h - Hg.h
  h₀ := by
    rw [comp_subMap, Hf.h₀, Hg.h₀]
    rfl
  h₁ := by
    rw [comp_subMap, Hf.h₁, Hg.h₁]
    rfl
  rel := by
    rw [comp_subMap, Hf.rel, Hg.rel, sub_self,
      cylinder_zeroBoundary]

/-! ## The native cone criterion -/

/-- A pointed cone filling of `f`: an actual simplicial homotopy from `f`
to the constant zero map, fixed on `P` throughout. -/
abbrev PointedConeFilling (f : RelativeZeroMaps P A) :=
  SSet.RelativeMorphism.Homotopy
    (relativeZeroMapsEquiv P A f) (zeroRelativeMorphism P A)

/-- A cone filling makes the native relative homotopy class equal to the
zero class. -/
theorem PointedConeFilling.class_eq_zero
    {f : RelativeZeroMaps P A} (H : PointedConeFilling P A f) :
    (relativeZeroMapsEquiv P A f).homotopyClass =
      (zeroRelativeMorphism P A).homotopyClass :=
  H.eq

/-- Two pointed cone fillings can be subtracted pointwise.  The result is a
filling of the lower-cone-minus-upper-cone boundary map. -/
def PointedConeFilling.sub
    {f g : RelativeZeroMaps P A}
    (Hf : PointedConeFilling P A f)
    (Hg : PointedConeFilling P A g) :
    PointedConeFilling P A (f - g) := by
  have H := homotopySub P A Hf Hg
  simpa [PointedConeFilling, zeroRelativeMorphism,
    relativeZeroMapsEquiv] using H

/-- Native homotopy-class form of the two-cone difference: the difference
of two cone-fillable boundary maps represents the zero relative class. -/
theorem PointedConeFilling.sub_class_eq_zero
    {f g : RelativeZeroMaps P A}
    (Hf : PointedConeFilling P A f)
    (Hg : PointedConeFilling P A g) :
    (relativeZeroMapsEquiv P A (f - g)).homotopyClass =
      (zeroRelativeMorphism P A).homotopyClass :=
  (Hf.sub P A Hg).class_eq_zero P A

end NativeConeTopology
end GeneralSphereT.Section4
