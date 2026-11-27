import Formalization.Section4StrictFSectionsNativeKernel
import Formalization.Section4NativeFiberMaps
import Formalization.Section4SimplicialConeComparison

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: genuine fibre maps represented by global primitive relations

Every global primitive relation evaluates simplexwise to a map into
`reducedFree L` killed by `d_*`, hence factors through the categorical fibre
`F`.  This file records that factorization as a linear map and identifies
primitive cycles as its strict kernel.
-/

noncomputable section

open CategoryTheory Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetRestrictionHom
open GeneralSphereT.Section4
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

private abbrev LData (M : AbstractSimplicialComplex V) (q : ℕ) :=
  facetRestrictionData (G := G) M q

/-- A primitive relation, evaluated as a genuine map to `reducedFree L` and
bundled with the strict equation saying that `d_*` kills it. -/
def rprimToNativeKilled
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Rprim (d := coboundaryToRange (G := G) M q) →ₗ[ℤ]
      MapsKilledByD (orderedComplexSSet M) (AddCommGrpCat.of G) (q + 1) where
  toFun r :=
    ⟨globalCochainRestrictionMap M q (r : RedDist (Cochain M q G)),
      AddMonoidHom.mem_ker.mpr (by
        simpa only [rprimToFCompatible_coe] using
          fCompatible_globalRestriction_killed M q
            (rprimToFCompatible (LData (G := G) M q) r))⟩
  map_add' r s := by
    apply Subtype.ext
    exact map_add (globalCochainRestrictionLinear M q)
      (r : RedDist (Cochain M q G))
      (s : RedDist (Cochain M q G))
  map_smul' n r := by
    apply Subtype.ext
    exact map_smul (globalCochainRestrictionLinear M q) n
      (r : RedDist (Cochain M q G))

@[simp]
theorem rprimToNativeKilled_coe
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) M q)) :
    (rprimToNativeKilled M q r :
        orderedComplexSSet M ⟶
          underlyingSSet
            (reducedFree (L (AddCommGrpCat.of G) (q + 1)))) =
      globalCochainRestrictionMap M q
        (r : RedDist (Cochain M q G)) :=
  rfl

/-- The actual `F(G,q+1)`-valued map represented by a primitive relation. -/
def rprimToNativeFiberMap
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Rprim (d := coboundaryToRange (G := G) M q) →ₗ[ℤ]
      (orderedComplexSSet M ⟶
        underlyingSSet (F (AddCommGrpCat.of G) (q + 1))) :=
  (MapsKilledByD.addEquivFiberMaps
      (orderedComplexSSet M) (AddCommGrpCat.of G) (q + 1)).toIntLinearEquiv.toLinearMap.comp
    (rprimToNativeKilled M q)

@[simp]
theorem rprimToNativeFiberMap_comp_inclusion
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) M q)) :
    rprimToNativeFiberMap M q r ≫
        underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)) =
      globalCochainRestrictionMap M q
        (r : RedDist (Cochain M q G)) := by
  exact MapsKilledByD.toFiberMap_comp_inclusion
    (orderedComplexSSet M) (AddCommGrpCat.of G) (q + 1)
      (rprimToNativeKilled M q r)

/-- Genuine fibre evaluation commutes strictly with pullback along an
ordered simplicial embedding. -/
theorem rprimToNativeFiberMap_pullback
    {W : Type u} [LinearOrder W] [Fintype W]
    {K : AbstractSimplicialComplex W}
    {M : AbstractSimplicialComplex V}
    (S : OrderedSimplicialMap K M) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) M q)) :
    S.toSSetMap ≫ rprimToNativeFiberMap M q r =
      rprimToNativeFiberMap K q
        (mapRprim (S.toFacetRestrictionHom (G := G) q) r) := by
  apply (cancel_mono
    (underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)))).1
  rw [Category.assoc, rprimToNativeFiberMap_comp_inclusion,
    rprimToNativeFiberMap_comp_inclusion,
    globalCochainRestrictionMap_pullback]
  rfl

/-- A primitive cycle evaluates to the strict zero map, before passing to
homotopy classes. -/
theorem zprimToRprim_nativeFiberMap_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (z : Zprim (LData (G := G) M q)) :
    rprimToNativeFiberMap M q
        (zprimToRprim (LData (G := G) M q) z) = 0 := by
  have hlocal :
      rprimToFCompatible (LData (G := G) M q)
          (zprimToRprim (LData (G := G) M q) z) ∈
        locallyZeroInFCompatible (LData (G := G) M q) := by
    exact z.2.2
  have hzero : globalCochainRestrictionMap M q
      ((zprimToRprim (LData (G := G) M q) z :
          Rprim (d := coboundaryToRange (G := G) M q)) :
        RedDist (Cochain M q G)) = 0 :=
    (fCompatible_globalRestriction_kernel M q
      (rprimToFCompatible (LData (G := G) M q)
        (zprimToRprim (LData (G := G) M q) z))).2 hlocal
  have hkilled : rprimToNativeKilled M q
      (zprimToRprim (LData (G := G) M q) z) = 0 := by
    apply Subtype.ext
    exact hzero
  change (MapsKilledByD.addEquivFiberMaps
      (orderedComplexSSet M) (AddCommGrpCat.of G) (q + 1))
        (rprimToNativeKilled M q
          (zprimToRprim (LData (G := G) M q) z)) = 0
  rw [hkilled, map_zero]

end GeneralSphereT.SimplicialCochain
