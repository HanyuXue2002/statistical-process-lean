import Formalization.Section4GlobalRelationPathMap
import Formalization.Section4RelationBoundaryNativeNullhomotopy
import Formalization.Section4BoundaryExtension

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: compatibility of global and simplexwise relation boundaries

The genuine simplicial relation-path map obtained by restricting a global
path has two a priori descriptions of its boundary: apply the simplicial
boundary morphism after restriction, or first take the global primitive
boundary and then restrict its distribution.  Naturality of reduced boundary
identifies these maps strictly.  We also package the relative form needed in
(4.21).
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- Restriction of a global relation boundary agrees strictly with the
genuine simplicial boundary of the restricted relation path. -/
theorem globalRelationPath_boundary_compatibility
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q))) :
    globalRelationPathRestrictionMap M q R ≫
        underlyingMap
          (simplicialRelationBoundary
            (d (AddCommGrpCat.of G) (q + 1))) =
      globalCochainRestrictionMap M q
        (primitiveBoundaryOfRelationPath
          (coboundaryToRange (G := G) M q) R).1 := by
  ext Δ x
  change primitiveReducedBoundary
      ((L (AddCommGrpCat.of G) (q + 1)).obj Δ)
      (mapNormalizedPath
        (cochainLValueHom M q Δ x)
        (cochainLValueHom M q Δ x) R.1).1 =
    mapRedDistFn (cochainLValue M q Δ x)
      (primitiveReducedBoundary (Cochain M q G) R.1.1)
  have h := LinearMap.congr_fun
    (reducedBoundary_natural
      (AddMonoidHom.id (Cochain M q G))
      (AddMonoidHom.id
        ((L (AddCommGrpCat.of G) (q + 1)).obj Δ))
      (cochainLValueHom M q Δ x)
      (cochainLValueHom M q Δ x) rfl) R.1.1
  rw [mapRedDist_eq_mapRedDistFn] at h
  exact h.symm

/-! ## Relative packaging -/

/-- A global relation path whose genuine restriction is zero on a source
subcomplex gives a native zero-boundary relative morphism. -/
def globalRelationPathRelativeMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (P : (orderedComplexSSet M).Subcomplex)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (hzero : P.ι ≫ globalRelationPathRestrictionMap M q R = 0) :
    NativeRelativeMorphism P
      (simplicialRelationPath (d (AddCommGrpCat.of G) (q + 1))) :=
  RelativeZeroMaps.toRelativeMorphism P _
    ⟨globalRelationPathRestrictionMap M q R,
      AddMonoidHom.mem_ker.mpr hzero⟩

@[simp]
theorem globalRelationPathRelativeMap_map
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (P : (orderedComplexSSet M).Subcomplex)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (hzero : P.ι ≫ globalRelationPathRestrictionMap M q R = 0) :
    (globalRelationPathRelativeMap M q P R hzero).map =
      globalRelationPathRestrictionMap M q R :=
  rfl

/-- The relative boundary map has the global primitive boundary as its
underlying genuine simplicial map. -/
theorem globalRelationPathRelativeMap_boundary_map
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (P : (orderedComplexSSet M).Subcomplex)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (hzero : P.ι ≫ globalRelationPathRestrictionMap M q R = 0) :
    (relationBoundaryRelativeMap P
      (d (AddCommGrpCat.of G) (q + 1))
      (globalRelationPathRelativeMap M q P R hzero)).map =
      globalCochainRestrictionMap M q
        (primitiveBoundaryOfRelationPath
          (coboundaryToRange (G := G) M q) R).1 := by
  exact globalRelationPath_boundary_compatibility M q R

/-- Consequently the genuine global primitive boundary is nullhomotopic
relative to every subcomplex on which the relation path vanishes. -/
def globalRelationBoundaryRelativeNullhomotopy
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (P : (orderedComplexSSet M).Subcomplex)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (hzero : P.ι ≫ globalRelationPathRestrictionMap M q R = 0) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P
        (reducedFree (L (AddCommGrpCat.of G) (q + 1))))
      (relationBoundaryRelativeMap P
        (d (AddCommGrpCat.of G) (q + 1))
        (globalRelationPathRelativeMap M q P R hzero)) :=
  standardRelationBoundaryRelativeNullhomotopy P
    (AddCommGrpCat.of G) q
    (globalRelationPathRelativeMap M q P R hzero)

/-- The class-level form of the preceding explicit nullhomotopy.  This is
the statement used when the transgression target is presented as the actual
native relative homotopy group. -/
theorem globalRelationBoundaryRelative_homotopyClass_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (P : (orderedComplexSSet M).Subcomplex)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (hzero : P.ι ≫ globalRelationPathRestrictionMap M q R = 0) :
    (relationBoundaryRelativeMap P
      (d (AddCommGrpCat.of G) (q + 1))
      (globalRelationPathRelativeMap M q P R hzero)).homotopyClass = 0 := by
  exact (globalRelationBoundaryRelativeNullhomotopy
    M q P R hzero).eq.symm.trans
      (NativeRelativeHomotopyGroup.homotopyClass_zero P
        (reducedFree (L (AddCommGrpCat.of G) (q + 1))))

end GeneralSphereT.SimplicialCochain
