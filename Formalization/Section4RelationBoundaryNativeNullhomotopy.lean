import Formalization.Section4RelationPathContraction
import Formalization.Section4DoldKanDiskNativeContraction
import Formalization.Section4NativeFiberMaps

set_option linter.style.header false

/-!
# Section 4: the native relative nullhomotopy of the relation boundary

The tensor-free relation-path object carries a genuine simplicial
contraction, obtained by contracting its increment label in the Dold--Kan
disk while keeping its base label fixed.  This file passes that contraction
to Mathlib's native relative cylinder homotopies and then postcomposes with
the primitive boundary map.  It is the topological conclusion used in
(4.21): every relative family of relation paths has relatively nullhomotopic
primitive boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.StandardModels

open GeneralSphereT.Section4
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

universe u

variable {A B : SimplicialObject AddCommGrpCat.{u}}

/-- Postcompose a native relative relation-path map with the genuine
primitive boundary morphism. -/
def relationBoundaryRelativeMap
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    NativeRelativeMorphism P (reducedFree A) where
  map := f.map ≫ underlyingMap (simplicialRelationBoundary d)
  comm := by
    calc
      P.ι ≫ f.map ≫ underlyingMap (simplicialRelationBoundary d) =
          zeroBoundary P (simplicialRelationPath d) ≫
            (zeroSubcomplex (simplicialRelationPath d)).ι ≫
              underlyingMap (simplicialRelationBoundary d) := by
        rw [← Category.assoc, f.comm, Category.assoc]
      _ = zeroBoundary P (reducedFree A) ≫
            (zeroSubcomplex (reducedFree A)).ι := by
        ext Δ x
        change 0 = 0
        rfl

@[simp]
theorem relationBoundaryRelativeMap_map
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    (relationBoundaryRelativeMap P d f).map =
      f.map ≫ underlyingMap (simplicialRelationBoundary d) :=
  rfl

/-- Native relative form of (4.21).  No tensor-product presentation is
needed: the path kernel and its contraction have already been constructed
directly. -/
def relationBoundaryRelativeNullhomotopy
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (H : SimplicialContraction A)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P (reducedFree A))
      (relationBoundaryRelativeMap P d f) where
  h :=
    (relativeMapUnderlyingContraction P
      (relationPathFirstFactorContraction d H) f).h ≫
        underlyingMap (simplicialRelationBoundary d)
  h₀ := by
    calc
      SSet.ι₀ ≫
          (relativeMapUnderlyingContraction P
            (relationPathFirstFactorContraction d H) f).h ≫
            underlyingMap (simplicialRelationBoundary d) =
          (0 : NativeRelativeMorphism P
            (simplicialRelationPath d)).map ≫
              underlyingMap (simplicialRelationBoundary d) := by
        rw [← Category.assoc, (relativeMapUnderlyingContraction P
          (relationPathFirstFactorContraction d H) f).h₀]
      _ = (0 : NativeRelativeMorphism P (reducedFree A)).map := by
        ext Δ x
        rfl
  h₁ := by
    rw [← Category.assoc, (relativeMapUnderlyingContraction P
      (relationPathFirstFactorContraction d H) f).h₁]
    rfl
  rel := by
    calc
      P.ι ▷ Δ[1] ≫
          ((relativeMapUnderlyingContraction P
            (relationPathFirstFactorContraction d H) f).h ≫
              underlyingMap (simplicialRelationBoundary d)) =
          (fst (P : SSet) Δ[1] ≫
            zeroBoundary P (simplicialRelationPath d) ≫
              (zeroSubcomplex (simplicialRelationPath d)).ι) ≫
                underlyingMap (simplicialRelationBoundary d) := by
        rw [← Category.assoc,
          (relativeMapUnderlyingContraction P
            (relationPathFirstFactorContraction d H) f).rel]
      _ = fst (P : SSet) Δ[1] ≫
            zeroBoundary P (reducedFree A) ≫
              (zeroSubcomplex (reducedFree A)).ι := by
        ext Δ x
        change 0 = 0
        rfl

/-- Homotopy-class consequence of the native relation-boundary
nullhomotopy. -/
theorem relationBoundaryRelative_class_eq_zero
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (H : SimplicialContraction A)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    (relationBoundaryRelativeMap P d f).homotopyClass =
      (0 : NativeRelativeMorphism P (reducedFree A)).homotopyClass :=
  (relationBoundaryRelativeNullhomotopy P d H f).eq.symm

/-- Standard Dold--Kan specialization of the native relative statement. -/
def standardRelationBoundaryRelativeNullhomotopy
    {X : SSet.{u}} (P : X.Subcomplex)
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P
      (simplicialRelationPath (d G (q + 1)))) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P (reducedFree (L G (q + 1))))
      (relationBoundaryRelativeMap P (d G (q + 1)) f) :=
  relationBoundaryRelativeNullhomotopy P (d G (q + 1))
    (DoldKanDiskContraction.standardDiskSimplicialContraction G q) f

end GeneralSphereT.StandardModels
