import Formalization.Section4SimplicialObjectCylinderHomotopy
import Formalization.Section4DoldKanDiskExtraDegeneracy

set_option linter.style.header false

/-!
# Section 4: native contractions of the Dold--Kan disk

The explicit extra degeneracy gives a combinatorial contraction of the
standard Dold--Kan disk.  We pass it through reduced linearization and the
forgetful functor, then use the prism construction to obtain actual
Mathlib cylinder homotopies of simplicial sets.  The cylinder maps preserve
zero, so these contractions are pointed relative homotopies at the zero
vertex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.StandardModels

universe u

open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.Section4.SimplicialObjectCylinderHomotopy
open DoldKanDiskContraction

variable {A : SimplicialObject AddCommGrpCat.{u}}

/-- The cylinder map underlying a combinatorial contraction of a simplicial
abelian group. -/
def underlyingCylinderMap
    (H : SimplicialContraction A) :
    underlyingSSet A ⊗ Δ[1] ⟶ underlyingSSet A :=
  cylinderMap (H.whiskerRight (forget AddCommGrpCat))

/-- Forgetting a zero natural transformation gives the pointwise zero map
of the underlying simplicial set. -/
theorem forget_map_zero_eq_zeroMap :
    ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
      (forget AddCommGrpCat)).map (0 : A ⟶ A) =
        (0 : underlyingSSet A ⟶ underlyingSSet A) := by
  ext Δ x
  rfl

/-- A combinatorial contraction of a simplicial abelian group gives an
actual cylinder contraction of its underlying simplicial set. -/
def underlyingCylinderContraction
    (H : SimplicialContraction A) :
    SSet.Homotopy
      (0 : underlyingSSet A ⟶ underlyingSSet A)
      (𝟙 (underlyingSSet A)) where
  h := underlyingCylinderMap H
  h₀ := by
    calc
      SSet.ι₀ ≫ underlyingCylinderMap H =
          ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
            (forget AddCommGrpCat)).map (0 : A ⟶ A) :=
        SSet.Homotopy.h₀
          (toCylinderHomotopy
            (H.whiskerRight (forget AddCommGrpCat)))
      _ = (0 : underlyingSSet A ⟶ underlyingSSet A) :=
        forget_map_zero_eq_zeroMap
  h₁ := by
    calc
      SSet.ι₁ ≫ underlyingCylinderMap H =
          ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
            (forget AddCommGrpCat)).map (𝟙 A) :=
        SSet.Homotopy.h₁
          (toCylinderHomotopy
            (H.whiskerRight (forget AddCommGrpCat)))
      _ = 𝟙 (underlyingSSet A) :=
        ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
          (forget AddCommGrpCat)).map_id A
  rel := by
    ext Δ x
    exact False.elim (by simpa using x.1.property)

/-- The identity of a simplicial abelian group as a native relative map at
its zero vertex. -/
def pointedIdentityRelativeMorphism :
    NativeRelativeMorphism (zeroSubcomplex A) A where
  map := 𝟙 (underlyingSSet A)
  comm := by
    rw [Category.comp_id, zeroBoundary_comp_inclusion,
      SSet.Subcomplex.ofSimplex_ι,
      const_zeroVertex_eq_zeroMap]

@[simp]
theorem pointedIdentityRelativeMorphism_map :
    (pointedIdentityRelativeMorphism (A := A)).map =
      𝟙 (underlyingSSet A) :=
  rfl

/-- The cylinder map associated to a simplicial-abelian contraction sends
the entire zero-vertex cylinder to zero. -/
theorem zeroSubcomplex_cylinder_comp_underlyingCylinderMap_eq_zero
    (H : SimplicialContraction A) :
    (zeroSubcomplex A).ι ▷ Δ[1] ≫ underlyingCylinderMap H =
      (0 : (zeroSubcomplex A : SSet) ⊗ Δ[1] ⟶
        underlyingSSet A) := by
  ext Δ z
  induction Δ using Opposite.rec with
  | _ Δ =>
    induction Δ using SimplexCategory.rec with
    | _ n =>
      change (cylinderApp
          (H.whiskerRight (forget AddCommGrpCat)) n).hom
        (((zeroSubcomplex A).ι.app (op ⦋n⦌)) z.1, z.2) =
          (0 : A.obj (op ⦋n⦌))
      have hzero :
          (zeroSubcomplex A).ι =
            (0 : (zeroSubcomplex A : SSet) ⟶ underlyingSSet A) := by
        rw [SSet.Subcomplex.ofSimplex_ι,
          const_zeroVertex_eq_zeroMap]
      have hz : ((zeroSubcomplex A).ι.app (op ⦋n⦌)) z.1 =
          (0 : A.obj (op ⦋n⦌)) := by
        rw [hzero]
        rfl
      rw [hz]
      change (cylinderApp
          (H.whiskerRight (forget AddCommGrpCat)) n).hom
        ((0 : A.obj (op ⦋n⦌)), z.2) =
          (0 : A.obj (op ⦋n⦌))
      obtain ⟨k, hk⟩ := SSet.stdSimplex.objMk₁_surjective z.2
      rw [← hk]
      rw [cylinderApp_apply_objMk₁]
      simp

/-- Pointed relative form of an underlying simplicial-abelian contraction. -/
def pointedUnderlyingRelativeContraction
    (H : SimplicialContraction A) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism (zeroSubcomplex A) A)
      (pointedIdentityRelativeMorphism (A := A)) where
  h := underlyingCylinderMap H
  h₀ := by
    calc
      SSet.ι₀ ≫ underlyingCylinderMap H =
          (0 : underlyingSSet A ⟶ underlyingSSet A) :=
        SSet.Homotopy.h₀ (underlyingCylinderContraction H)
      _ = (0 : NativeRelativeMorphism (zeroSubcomplex A) A).map :=
        (relativeMorphism_zero_map (zeroSubcomplex A) A).symm
  h₁ := by
    exact SSet.Homotopy.h₁ (underlyingCylinderContraction H)
  rel := by
    rw [zeroSubcomplex_cylinder_comp_underlyingCylinderMap_eq_zero H,
      cylinder_zeroBoundary]

/-! ## Contracting arbitrary relative maps into the target -/

variable {X : SSet.{u}} (P : X.Subcomplex)

/-- If the target simplicial abelian group has the chosen contraction, then
every map which is strictly zero on `P` contracts to zero relative to `P`.

This is the form used by (4.21): the contraction takes place in the target,
and the source pair is completely arbitrary. -/
def relativeMapUnderlyingContraction
    (H : SimplicialContraction A)
    (f : NativeRelativeMorphism P A) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P A) f where
  h := f.map ▷ Δ[1] ≫ underlyingCylinderMap H
  h₀ := by
    calc
      SSet.ι₀ ≫ f.map ▷ Δ[1] ≫ underlyingCylinderMap H =
          f.map ≫ SSet.ι₀ ≫ underlyingCylinderMap H := by
        rw [SSet.ι₀_comp_assoc]
      _ = f.map ≫ (0 : underlyingSSet A ⟶ underlyingSSet A) := by
        exact congrArg (fun k : underlyingSSet A ⟶ underlyingSSet A =>
          f.map ≫ k)
            (SSet.Homotopy.h₀ (underlyingCylinderContraction H))
      _ = (0 : X ⟶ underlyingSSet A) := by
        ext Δ x
        rfl
      _ = (0 : NativeRelativeMorphism P A).map :=
        (relativeMorphism_zero_map P A).symm
  h₁ := by
    calc
      SSet.ι₁ ≫ f.map ▷ Δ[1] ≫ underlyingCylinderMap H =
          f.map ≫ SSet.ι₁ ≫ underlyingCylinderMap H := by
        rw [SSet.ι₁_comp_assoc]
      _ = f.map ≫ 𝟙 (underlyingSSet A) := by
        exact congrArg (fun k : underlyingSSet A ⟶ underlyingSSet A =>
          f.map ≫ k)
            (SSet.Homotopy.h₁ (underlyingCylinderContraction H))
      _ = f.map := Category.comp_id _
  rel := by
    calc
      P.ι ▷ Δ[1] ≫
          (f.map ▷ Δ[1] ≫ underlyingCylinderMap H) =
          (P.ι ≫ f.map) ▷ Δ[1] ≫
            underlyingCylinderMap H := by
        rw [← comp_whiskerRight_assoc]
      _ = (zeroBoundary P A ≫ (zeroSubcomplex A).ι) ▷ Δ[1] ≫
            underlyingCylinderMap H := by
        rw [f.comm]
      _ = zeroBoundary P A ▷ Δ[1] ≫
            ((zeroSubcomplex A).ι ▷ Δ[1] ≫
              underlyingCylinderMap H) := by
        rw [comp_whiskerRight_assoc]
      _ = 0 := by
        rw [zeroSubcomplex_cylinder_comp_underlyingCylinderMap_eq_zero H]
        ext Δ x
        rfl
      _ = fst (P : SSet) Δ[1] ≫ zeroBoundary P A ≫
          (zeroSubcomplex A).ι :=
        (cylinder_zeroBoundary P A).symm

/-- Native homotopy-class consequence of target contractibility. -/
theorem relativeMapUnderlyingContraction_class_eq_zero
    (H : SimplicialContraction A)
    (f : NativeRelativeMorphism P A) :
    f.homotopyClass =
      (0 : NativeRelativeMorphism P A).homotopyClass :=
  (relativeMapUnderlyingContraction P H f).eq.symm

/-! ## The standard Dold--Kan disk -/

/-- Actual contraction of the underlying standard Dold--Kan disk. -/
def standardDiskNativeContraction
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    SSet.Homotopy
      (0 : underlyingSSet (L G (q + 1)) ⟶
        underlyingSSet (L G (q + 1)))
      (𝟙 (underlyingSSet (L G (q + 1)))) :=
  underlyingCylinderContraction
    (standardDiskSimplicialContraction G q)

/-- Actual contraction after reduced linearization. -/
def standardDiskReducedFreeNativeContraction
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    SSet.Homotopy
      (0 : underlyingSSet (reducedFree (L G (q + 1))) ⟶
        underlyingSSet (reducedFree (L G (q + 1))))
      (𝟙 (underlyingSSet (reducedFree (L G (q + 1))))) :=
  underlyingCylinderContraction
    (reducedFreeSimplicialContraction
      (standardDiskSimplicialContraction G q))

/-- Pointed native relative contraction of the reduced-free standard disk. -/
def standardDiskReducedFreePointedRelativeContraction
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (zeroSubcomplex (reducedFree (L G (q + 1))))
        (reducedFree (L G (q + 1))))
      (pointedIdentityRelativeMorphism
        (A := reducedFree (L G (q + 1)))) :=
  pointedUnderlyingRelativeContraction
    (reducedFreeSimplicialContraction
      (standardDiskSimplicialContraction G q))

/-- Every strictly relative map into the reduced-free Dold--Kan disk is
actually nullhomotopic relative to its source boundary. -/
def standardDiskReducedFreeRelativeMapContraction
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) f :=
  relativeMapUnderlyingContraction P
    (reducedFreeSimplicialContraction
      (standardDiskSimplicialContraction G q)) f

/-- Homotopy-class form of the preceding relative contraction. -/
theorem standardDiskReducedFreeRelativeMap_class_eq_zero
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) :
    f.homotopyClass =
      (0 : NativeRelativeMorphism
        P (reducedFree (L G (q + 1)))).homotopyClass :=
  (standardDiskReducedFreeRelativeMapContraction P G q f).eq.symm

end GeneralSphereT.StandardModels
