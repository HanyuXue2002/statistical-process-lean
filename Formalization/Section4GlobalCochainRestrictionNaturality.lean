import Formalization.Section4CochainMapNaturality
import Formalization.Section4GlobalRelationPathMap

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: naturality of global distribution evaluation

The genuine simplicial map obtained by evaluating a distribution of global
cochains commutes with restriction along every ordered simplicial embedding.
This is the map-level bridge needed for bottom inclusions of literal cones and
for support-simplex arguments.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.StandardModels

universe u

variable {V W G : Type u}
variable [LinearOrder V] [LinearOrder W]
variable [Fintype V] [Fintype W]
variable [AddCommGroup G]
variable {K : AbstractSimplicialComplex V}
variable {M : AbstractSimplicialComplex W}

/-- Pointwise evaluation after an ordered pullback agrees with evaluation on
the image simplex. -/
theorem cochainLValue_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet K).obj Δ)
    (c : Cochain M q G) :
    cochainLValue K q Δ x (F.pullback q c) =
      cochainLValue M q Δ (F.toSSetMap.app Δ x) c := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cochainToLMap_pullback F q c) Δ) x
  exact h.symm

/-- Restricting a genuine map of global cochain distributions is the same as
first pushing the distribution forward by cochain pullback. -/
theorem globalCochainRestrictionMap_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ)
    (u : RedDist (Cochain M q G)) :
    F.toSSetMap ≫ globalCochainRestrictionMap M q u =
      globalCochainRestrictionMap K q
        (mapRedDist (F.pullback (G := G) q).toAddMonoidHom u) := by
  ext Δ x
  change mapRedDistFn
      (cochainLValue M q Δ (F.toSSetMap.app Δ x)) u =
    mapRedDistFn (cochainLValue K q Δ x)
      (mapRedDist (F.pullback q).toAddMonoidHom u)
  rw [mapRedDist_eq_mapRedDistFn, mapRedDistFn_comp_apply]
  congr 2
  funext c
  exact (cochainLValue_pullback F q Δ x c).symm

/-! ## Relation paths -/

/-- Pull back a global relation path along an ordered simplicial embedding.
The coboundary square supplies the proof that the pulled-back path is still
killed by `d_*`. -/
def pullbackGlobalRelationPath
    (F : OrderedSimplicialMap K M) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q))) :
    LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) K q)) := by
  refine ⟨mapNormalizedPath
    (F.pullback (G := G) q).toAddMonoidHom
    (F.pullback (G := G) q).toAddMonoidHom R.1, ?_⟩
  rw [LinearMap.mem_ker]
  calc
    mapDNormalizedPath (coboundaryToRange (G := G) K q)
        (mapNormalizedPath
          (F.pullback (G := G) q).toAddMonoidHom
          (F.pullback (G := G) q).toAddMonoidHom R.1) =
      mapNormalizedPath
        (F.pullback (G := G) q).toAddMonoidHom
        (F.pullbackCoboundary (G := G) q).toAddMonoidHom
        (mapDNormalizedPath (coboundaryToRange (G := G) M q) R.1) :=
      mapDNormalizedPath_mapNormalizedPath
        (coboundaryToRange (G := G) M q)
        (coboundaryToRange (G := G) K q)
        (F.pullback (G := G) q).toAddMonoidHom
        (F.pullback (G := G) q).toAddMonoidHom
        (F.pullbackCoboundary (G := G) q).toAddMonoidHom
        (F.toFacetRestrictionHom (G := G) q).commutes.symm R.1
    _ = 0 := by rw [R.2, map_zero]

@[simp]
theorem pullbackGlobalRelationPath_coe
    (F : OrderedSimplicialMap K M) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q))) :
    (pullbackGlobalRelationPath F q R).1 =
      mapNormalizedPath
        (F.pullback (G := G) q).toAddMonoidHom
        (F.pullback (G := G) q).toAddMonoidHom R.1 :=
  rfl

/-- The genuine relation-path map commutes strictly with ordered pullback.
In particular, this applies to the bottom inclusion of every literal cone. -/
theorem globalRelationPathRestrictionMap_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q))) :
    F.toSSetMap ≫ globalRelationPathRestrictionMap M q R =
      globalRelationPathRestrictionMap K q
        (pullbackGlobalRelationPath F q R) := by
  ext Δ x
  apply Subtype.ext
  change mapNormalizedPath
      (cochainLValueHom M q Δ (F.toSSetMap.app Δ x))
      (cochainLValueHom M q Δ (F.toSSetMap.app Δ x)) R.1 =
    mapNormalizedPath (cochainLValueHom K q Δ x)
      (cochainLValueHom K q Δ x)
      (mapNormalizedPath
        (F.pullback (G := G) q).toAddMonoidHom
        (F.pullback (G := G) q).toAddMonoidHom R.1)
  rw [mapNormalizedPath_comp_apply]
  have heval :
      (cochainLValueHom K q Δ x).comp
          (F.pullback (G := G) q).toAddMonoidHom =
        cochainLValueHom M q Δ (F.toSSetMap.app Δ x) := by
    apply AddMonoidHom.ext
    intro c
    exact cochainLValue_pullback F q Δ x c
  rw [heval]

end GeneralSphereT.SimplicialCochain
