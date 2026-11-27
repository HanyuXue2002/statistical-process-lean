import Formalization.Section4RelationBoundaryNativeNullhomotopy

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the relation boundary contracts inside the actual fibre

The primitive boundary of a relation path is not merely a map to
`reducedFree A`: its composite with `reducedFreeMap d` is strictly zero.
It therefore factors through the categorical kernel of that map.  The
relation-path contraction postcomposes with this factorization, giving a
relative nullhomotopy which stays inside the fibre at every time.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.StandardModels

open GeneralSphereT.PathAlgebra
open GeneralSphereT.Section4
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

universe u

variable {A B : SimplicialObject AddCommGrpCat.{u}}

/-- A relation boundary is killed by the reduced-free image of `d`. -/
theorem simplicialRelationBoundary_comp_reducedFreeMap
    (d : A ⟶ B) :
    simplicialRelationBoundary d ≫ reducedFreeMap d = 0 := by
  ext Δ R
  change LinearMap.ker
    (mapDNormalizedPath (d.app Δ).hom) at R
  change mapRedDist (d.app Δ).hom
      (primitiveReducedBoundary (A.obj Δ) R.1.1) = 0
  have hboundary := LinearMap.congr_fun
    (mapRedDist_primitiveReducedBoundary (d.app Δ).hom) R.1.1
  change mapRedDist (d.app Δ).hom
      (primitiveReducedBoundary (A.obj Δ) R.1.1) =
    configurationReducedBoundary (d.app Δ).hom
      (mapDPath (d.app Δ).hom R.1.1) at hboundary
  have hpath : mapDPath (d.app Δ).hom R.1.1 = 0 :=
    congrArg Subtype.val R.2
  rw [hboundary, hpath, map_zero]

/-- The genuine primitive-boundary morphism with codomain the categorical
fibre of `reducedFreeMap d`. -/
def simplicialRelationBoundaryFiber (d : A ⟶ B) :
    simplicialRelationPath d ⟶ kernel (reducedFreeMap d) :=
  kernel.lift (reducedFreeMap d) (simplicialRelationBoundary d)
    (simplicialRelationBoundary_comp_reducedFreeMap d)

@[reassoc (attr := simp)]
theorem simplicialRelationBoundaryFiber_comp_ι (d : A ⟶ B) :
    simplicialRelationBoundaryFiber d ≫ kernel.ι (reducedFreeMap d) =
      simplicialRelationBoundary d :=
  kernel.lift_ι _ _ _

/-- Postcompose a native relative relation-path map with the boundary
factorization into the actual categorical fibre. -/
def relationBoundaryFiberRelativeMap
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    NativeRelativeMorphism P (kernel (reducedFreeMap d)) where
  map := f.map ≫ underlyingMap (simplicialRelationBoundaryFiber d)
  comm := by
    calc
      P.ι ≫ f.map ≫ underlyingMap (simplicialRelationBoundaryFiber d) =
          zeroBoundary P (simplicialRelationPath d) ≫
            (zeroSubcomplex (simplicialRelationPath d)).ι ≫
              underlyingMap (simplicialRelationBoundaryFiber d) := by
        rw [← Category.assoc, f.comm, Category.assoc]
      _ = zeroBoundary P (kernel (reducedFreeMap d)) ≫
            (zeroSubcomplex (kernel (reducedFreeMap d))).ι := by
        rw [← Category.assoc, zeroBoundary_comp_inclusion,
          zeroBoundary_comp_inclusion]
        ext Δ x
        exact map_zero
          ((simplicialRelationBoundaryFiber d).app Δ).hom

@[simp]
theorem relationBoundaryFiberRelativeMap_map
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    (relationBoundaryFiberRelativeMap P d f).map =
      f.map ≫ underlyingMap (simplicialRelationBoundaryFiber d) :=
  rfl

/-- After the fibre inclusion, the fibre-valued boundary is the ordinary
relation boundary. -/
theorem relationBoundaryFiberRelativeMap_comp_inclusion
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    (relationBoundaryFiberRelativeMap P d f).map ≫
        underlyingMap (kernel.ι (reducedFreeMap d)) =
      (relationBoundaryRelativeMap P d f).map := by
  rw [relationBoundaryFiberRelativeMap_map,
    relationBoundaryRelativeMap_map, Category.assoc]
  exact congrArg (fun k => f.map ≫ underlyingMap k)
    (simplicialRelationBoundaryFiber_comp_ι d)

/-- Native relative form of (4.21), now with the correct target: the whole
homotopy lies in the categorical fibre, not only in `reducedFree A`. -/
def relationBoundaryFiberRelativeNullhomotopy
    {X : SSet.{u}} (P : X.Subcomplex) (d : A ⟶ B)
    (H : SimplicialContraction A)
    (f : NativeRelativeMorphism P (simplicialRelationPath d)) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P (kernel (reducedFreeMap d)))
      (relationBoundaryFiberRelativeMap P d f) where
  h :=
    (relativeMapUnderlyingContraction P
      (relationPathFirstFactorContraction d H) f).h ≫
        underlyingMap (simplicialRelationBoundaryFiber d)
  h₀ := by
    calc
      SSet.ι₀ ≫
          (relativeMapUnderlyingContraction P
            (relationPathFirstFactorContraction d H) f).h ≫
            underlyingMap (simplicialRelationBoundaryFiber d) =
          (0 : NativeRelativeMorphism P
            (simplicialRelationPath d)).map ≫
              underlyingMap (simplicialRelationBoundaryFiber d) := by
        rw [← Category.assoc, (relativeMapUnderlyingContraction P
          (relationPathFirstFactorContraction d H) f).h₀]
      _ = (0 : NativeRelativeMorphism P
          (kernel (reducedFreeMap d))).map := by
        ext Δ x
        exact map_zero
          ((simplicialRelationBoundaryFiber d).app Δ).hom
  h₁ := by
    rw [← Category.assoc, (relativeMapUnderlyingContraction P
      (relationPathFirstFactorContraction d H) f).h₁]
    rfl
  rel := by
    calc
      P.ι ▷ Δ[1] ≫
          ((relativeMapUnderlyingContraction P
            (relationPathFirstFactorContraction d H) f).h ≫
              underlyingMap (simplicialRelationBoundaryFiber d)) =
          (fst (P : SSet) Δ[1] ≫
            zeroBoundary P (simplicialRelationPath d) ≫
              (zeroSubcomplex (simplicialRelationPath d)).ι) ≫
                underlyingMap (simplicialRelationBoundaryFiber d) := by
        rw [← Category.assoc,
          (relativeMapUnderlyingContraction P
            (relationPathFirstFactorContraction d H) f).rel]
      _ = fst (P : SSet) Δ[1] ≫
            zeroBoundary P (kernel (reducedFreeMap d)) ≫
              (zeroSubcomplex (kernel (reducedFreeMap d))).ι := by
        have hzero :
            (0 : (P : SSet) ⟶ underlyingSSet
              (simplicialRelationPath d)) ≫
                underlyingMap (simplicialRelationBoundaryFiber d) =
              (0 : (P : SSet) ⟶ underlyingSSet
                (kernel (reducedFreeMap d))) := by
          ext Δ x
          exact map_zero
            ((simplicialRelationBoundaryFiber d).app Δ).hom
        calc
          (fst (P : SSet) Δ[1] ≫
                zeroBoundary P (simplicialRelationPath d) ≫
                  (zeroSubcomplex (simplicialRelationPath d)).ι) ≫
              underlyingMap (simplicialRelationBoundaryFiber d) =
              fst (P : SSet) Δ[1] ≫
                ((zeroBoundary P (simplicialRelationPath d) ≫
                    (zeroSubcomplex (simplicialRelationPath d)).ι) ≫
                  underlyingMap (simplicialRelationBoundaryFiber d)) := by
            simp only [Category.assoc]
          _ = fst (P : SSet) Δ[1] ≫
                ((0 : (P : SSet) ⟶ underlyingSSet
                    (simplicialRelationPath d)) ≫
                  underlyingMap (simplicialRelationBoundaryFiber d)) := by
            rw [zeroBoundary_comp_inclusion]
          _ = fst (P : SSet) Δ[1] ≫
                (0 : (P : SSet) ⟶ underlyingSSet
                  (kernel (reducedFreeMap d))) := by rw [hzero]
          _ = fst (P : SSet) Δ[1] ≫
                (zeroBoundary P (kernel (reducedFreeMap d)) ≫
                  (zeroSubcomplex (kernel (reducedFreeMap d))).ι) := by
            rw [zeroBoundary_comp_inclusion]
          _ = (fst (P : SSet) Δ[1] ≫
                zeroBoundary P (kernel (reducedFreeMap d))) ≫
              (zeroSubcomplex (kernel (reducedFreeMap d))).ι := by
            rw [Category.assoc]

/-- Standard Dold--Kan specialization: the primitive boundary of every
relative relation path is relatively nullhomotopic inside `F(G,q+1)`. -/
def standardRelationBoundaryFiberRelativeNullhomotopy
    {X : SSet.{u}} (P : X.Subcomplex)
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P
      (simplicialRelationPath (d G (q + 1)))) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P (F G (q + 1)))
      (relationBoundaryFiberRelativeMap P (d G (q + 1)) f) :=
  relationBoundaryFiberRelativeNullhomotopy P (d G (q + 1))
    (DoldKanDiskContraction.standardDiskSimplicialContraction G q) f

/-- Class-level conclusion in the genuine fibre. -/
theorem standardRelationBoundaryFiberRelative_class_eq_zero
    {X : SSet.{u}} (P : X.Subcomplex)
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P
      (simplicialRelationPath (d G (q + 1)))) :
    (relationBoundaryFiberRelativeMap P (d G (q + 1)) f).homotopyClass = 0 := by
  exact (standardRelationBoundaryFiberRelativeNullhomotopy P G q f).eq.symm.trans
    (NativeRelativeHomotopyGroup.homotopyClass_zero P (F G (q + 1)))

end GeneralSphereT.StandardModels
