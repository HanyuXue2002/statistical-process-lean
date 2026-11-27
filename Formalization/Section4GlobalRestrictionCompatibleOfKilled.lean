import Formalization.Section4NativeMapLocalDistributions

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Native vanishing implies algebraic facet compatibility

This is the converse local calculation to
`fCompatible_globalRestriction_killed`.  Evaluation of cocycles on the top
simplex of a full support simplex is injective.  Consequently, if the genuine
`L`-valued map defined by a global cochain distribution is killed by `d`, its
physical coboundary distribution vanishes after restriction to every facet.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.Section4
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

set_option maxHeartbeats 1000000 in
-- Unfolding the explicit Dold--Kan support equivalence is elaboration-heavy.
/-- On a full support simplex, a cocycle is determined by the value of its
genuine `K`-valued map on the top simplex. -/
theorem supportCocycleKValue_injective
    (M : AbstractSimplicialComplex V) (r : ℕ) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) :
    Function.Injective
      (cocycleKValueHom
        (nonDegenerateSimplexSupportComplex M x) r
        (Opposite.op (SimplexCategory.mk n))
        (nonDegenerateSimplexSupportTop M x) :
          LinearMap.ker (coboundary (G := G)
            (nonDegenerateSimplexSupportComplex M x) r) →
            (K (AddCommGrpCat.of G) r).obj
              (Opposite.op (SimplexCategory.mk n))) := by
  intro z z' h
  let N := nonDegenerateSimplexSupportComplex M x
  let X := orderedComplexSSet N
  let C := sphereComplex (AddCommGrpCat.of G) r
  have htop :
      (denormalizeNormalizedChainMap X
        (cocycleSphereChainMapSubtypeAddHom' N r z)).app
          (Opposite.op (SimplexCategory.mk n))
            (nonDegenerateSimplexSupportTopGenerator M x) =
      (denormalizeNormalizedChainMap X
        (cocycleSphereChainMapSubtypeAddHom' N r z')).app
          (Opposite.op (SimplexCategory.mk n))
            (nonDegenerateSimplexSupportTopGenerator M x) := by
    exact h
  have hden :
      denormalizeNormalizedChainMap X
          (cocycleSphereChainMapSubtypeAddHom' N r z) =
        denormalizeNormalizedChainMap X
          (cocycleSphereChainMapSubtypeAddHom' N r z') :=
    supportFreeMap_ext M x
      (CategoryTheory.Abelian.DoldKan.Γ.obj C) _ _ htop
  have hchain :
      cocycleSphereChainMapSubtypeAddHom' N r z =
        cocycleSphereChainMapSubtypeAddHom' N r z' :=
    (denormalizeNormalizedChainMap_bijective X C).1 hden
  apply Subtype.ext
  apply (cochainEquivNormalizedCochainHom N r).injective
  rw [← cancel_mono
    (HomologicalComplex.singleObjXSelf
      (ComplexShape.down ℕ) r (AddCommGrpCat.of G)).inv]
  have hr := HomologicalComplex.congr_hom hchain r
  change (cocycleSphereChainMap N r z.1
      (LinearMap.mem_ker.mp z.2)).f r =
    (cocycleSphereChainMap N r z'.1
      (LinearMap.mem_ker.mp z'.2)).f r at hr
  rw [cocycleSphereChainMap_f_self,
    cocycleSphereChainMap_f_self] at hr
  exact hr

/-- Identify cochains on a chosen facet with cochains on the full simplex
carried by its canonical nondegenerate representative. -/
def facetCochainToSupportEquiv
    (M : AbstractSimplicialComplex V) (r : ℕ)
    (σ : NonemptySimplex M) :
    Configuration (facesIn M r σ) G ≃+
      Cochain
        (nonDegenerateSimplexSupportComplex M
          (nonemptySimplexNonDegenerate M σ)) r G :=
  (facetToCanonicalEquiv (G := G) M r σ).trans
    (localCochainToStandardEquiv M
      (nonemptySimplexNonDegenerate M σ) r)

@[simp]
theorem facetCochainToSupportEquiv_apply
    (M : AbstractSimplicialComplex V) (r : ℕ)
    (σ : NonemptySimplex M)
    (a : Configuration (facesIn M r σ) G) :
    facetCochainToSupportEquiv M r σ a =
      localCochainToStandard M (nonemptySimplexNonDegenerate M σ) r
        (facetToCanonicalEquiv M r σ a) :=
  rfl

/-- The facet/support identification is literally pullback of extension by
zero along the support inclusion. -/
theorem facetCochainToSupportEquiv_eq_pullback
    (M : AbstractSimplicialComplex V) (r : ℕ)
    (σ : NonemptySimplex M)
    (a : Configuration (facesIn M r σ) G) :
    facetCochainToSupportEquiv M r σ a =
      (nonDegenerateSimplexSupportMap M
        (nonemptySimplexNonDegenerate M σ)).pullback r
          (coordinateExtension (facesIn M r σ) a) := by
  exact localCochainToStandard_restrictCochain M
    (nonemptySimplexNonDegenerate M σ) r
      (coordinateExtension (facesIn M r σ) a)

/-- The facet/support identification intertwines the local and ordinary
simplicial coboundaries. -/
theorem facetCochainToSupportEquiv_localCoboundary
    (M : AbstractSimplicialComplex V) (r : ℕ)
    (σ : NonemptySimplex M)
    (a : Configuration (facesIn M r σ) G) :
    facetCochainToSupportEquiv M (r + 1) σ
        (localCoboundary M r σ a) =
      coboundary
        (nonDegenerateSimplexSupportComplex M
          (nonemptySimplexNonDegenerate M σ)) r
        (facetCochainToSupportEquiv M r σ a) := by
  let x := nonemptySimplexNonDegenerate M σ
  let F := nonDegenerateSimplexSupportMap M x
  let c : Cochain M r G := coordinateExtension (facesIn M r σ) a
  rw [facetCochainToSupportEquiv_eq_pullback,
    facetCochainToSupportEquiv_eq_pullback]
  have hpull :
      F.pullback (r + 1)
          (coordinateExtension (facesIn M (r + 1) σ)
            (localCoboundary M r σ a)) =
        F.pullback (r + 1) (coboundary M r c) := by
    rw [← localCochainToStandard_restrictCochain M x (r + 1),
      ← localCochainToStandard_restrictCochain M x (r + 1)]
    congr 1
    change coordinateRestriction
        (facesIn M (r + 1) (nonDegenerateSimplexFacet M x))
          (coordinateExtension (facesIn M (r + 1) σ)
            (localCoboundary M r σ a)) =
      coordinateRestriction
        (facesIn M (r + 1) (nonDegenerateSimplexFacet M x))
          (coboundary M r c)
    rw [show nonDegenerateSimplexFacet M x = σ by
      exact nonemptySimplexNonDegenerate_facet M σ]
    rw [coordinateRestriction_coordinateExtension]
    have hcomm := DFunLike.congr_fun
      (restrictCochain_coboundary (G := G) M r σ) c
    change coordinateRestriction (facesIn M (r + 1) σ)
        (coboundary M r c) =
      localCoboundary M r σ
        (coordinateRestriction (facesIn M r σ) c) at hcomm
    rw [coordinateRestriction_coordinateExtension] at hcomm
    exact hcomm.symm
  rw [hpull]
  exact DFunLike.congr_fun
    ((nonDegenerateSimplexSupportMap M x).pullback_coboundary r) c

/-- Local coboundary, with its automatic cocycle witness retained. -/
def facetCoboundaryCocycleHom
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (σ : NonemptySimplex M) :
    Configuration (facesIn M q σ) G →+
      LinearMap.ker (coboundary (G := G)
        (nonDegenerateSimplexSupportComplex M
          (nonemptySimplexNonDegenerate M σ)) (q + 1)) :=
  (coboundaryToCocycle
      (nonDegenerateSimplexSupportComplex M
        (nonemptySimplexNonDegenerate M σ)) q).comp
    (facetCochainToSupportEquiv M q σ).toAddMonoidHom

/-- Forget a support cocycle and return to the corresponding local cochain
on the ambient facet. -/
def supportCocycleToFacetCochainHom
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (σ : NonemptySimplex M) :
    LinearMap.ker (coboundary (G := G)
        (nonDegenerateSimplexSupportComplex M
          (nonemptySimplexNonDegenerate M σ)) (q + 1)) →+
      Configuration (facesIn M (q + 1) σ) G :=
  (facetCochainToSupportEquiv M (q + 1) σ).symm.toAddMonoidHom.comp
    (LinearMap.ker (coboundary (G := G)
      (nonDegenerateSimplexSupportComplex M
        (nonemptySimplexNonDegenerate M σ)) (q + 1))).subtype.toAddMonoidHom

/-- Forgetting the support-cocycle witness after the preceding construction
is exactly the elementary local coboundary. -/
theorem supportCocycleToFacetCochainHom_comp_facetCoboundary
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (σ : NonemptySimplex M) :
    (supportCocycleToFacetCochainHom (G := G) M q σ).comp
        (facetCoboundaryCocycleHom M q σ) =
      (localCoboundary (G := G) M q σ).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  dsimp [supportCocycleToFacetCochainHom,
    facetCoboundaryCocycleHom]
  apply (facetCochainToSupportEquiv M (q + 1) σ).injective
  rw [(facetCochainToSupportEquiv M (q + 1) σ).apply_symm_apply]
  exact (facetCochainToSupportEquiv_localCoboundary M q σ a).symm

/-- The facet `L`-evaluation agrees with evaluation of the corresponding
cochain on the top simplex of its full support simplex. -/
theorem facetCochainLValueHom_eq_support
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (σ : NonemptySimplex M)
    (a : Configuration (facesIn M q σ) G) :
    facetCochainLValueHom M q σ a =
      cochainLValueHom
        (nonDegenerateSimplexSupportComplex M
          (nonemptySimplexNonDegenerate M σ)) q
        (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ)))
        (nonDegenerateSimplexSupportTop M
          (nonemptySimplexNonDegenerate M σ))
        (facetCochainToSupportEquiv M q σ a) := by
  rw [facetCochainLValueHom_apply,
    facetCochainToSupportEquiv_eq_pullback]
  let x := nonemptySimplexNonDegenerate M σ
  let F := nonDegenerateSimplexSupportMap M x
  let c : Cochain M q G := coordinateExtension (facesIn M q σ) a
  have h := cochainLValue_pullback F q
    (Opposite.op
      (SimplexCategory.mk (nonemptySimplexDimension σ)))
    (nonDegenerateSimplexSupportTop M x) c
  rw [nonDegenerateSimplexSupportMap_top] at h
  exact h.symm

/-- On the chosen top simplex, the genuine map `d` is the local coboundary,
followed by genuine `K`-evaluation. -/
theorem facetCochainLValue_d_eq_supportK
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (σ : NonemptySimplex M)
    (a : Configuration (facesIn M q σ) G) :
    ((d (AddCommGrpCat.of G) (q + 1)).app
      (Opposite.op
        (SimplexCategory.mk (nonemptySimplexDimension σ)))).hom
        (facetCochainLValueHom M q σ a) =
      cocycleKValueHom
        (nonDegenerateSimplexSupportComplex M
          (nonemptySimplexNonDegenerate M σ)) (q + 1)
        (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ)))
        (nonDegenerateSimplexSupportTop M
          (nonemptySimplexNonDegenerate M σ))
        (facetCoboundaryCocycleHom M q σ a) := by
  rw [facetCochainLValueHom_eq_support]
  exact cochainLValue_d_cocycle_apply
    (nonDegenerateSimplexSupportComplex M
      (nonemptySimplexNonDegenerate M σ)) q _ _
      (facetCochainToSupportEquiv M q σ a)

/-- If a native map is killed by `d_*`, then the local cochain distribution
classified by its value on any simplex has zero local-coboundary
pushforward. -/
theorem mapRedDist_localCoboundary_nativeMapLocalDistribution_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (f : MapsKilledByD (orderedComplexSSet M)
      (AddCommGrpCat.of G) (q + 1))
    (σ : NonemptySimplex M) :
    mapRedDist (localCoboundary (G := G) M q σ).toAddMonoidHom
        (nativeMapLocalDistribution M q f.1 σ) = 0 := by
  let Δ := Opposite.op
    (SimplexCategory.mk (nonemptySimplexDimension σ))
  let x := nonemptySimplexNonDegenerate M σ
  let N := nonDegenerateSimplexSupportComplex M x
  let kEval := cocycleKValueHom (G := G) N (q + 1) Δ
    (nonDegenerateSimplexSupportTop M x)
  let bCoc := facetCoboundaryCocycleHom (G := G) M q σ
  have hkill := MapsKilledByD.app_mem
    (orderedComplexSSet M) (AddCommGrpCat.of G) (q + 1) f Δ x.1
  rw [reducedFreeMap_app_apply] at hkill
  rw [← mapRedDist_facetCochainLValue_nativeMapLocalDistribution
    (G := G) M q f.1 σ] at hkill
  rw [GeneralSphereT.StandardModels.mapRedDist_comp_apply] at hkill
  have hcomp :
      kEval.comp bCoc =
        ((d (AddCommGrpCat.of G) (q + 1)).app Δ).hom.comp
          (facetCochainLValueHom (G := G) M q σ) := by
    apply AddMonoidHom.ext
    intro a
    exact (facetCochainLValue_d_eq_supportK M q σ a).symm
  have hkill' :
      mapRedDist
        (((d (AddCommGrpCat.of G) (q + 1)).app Δ).hom.comp
          (facetCochainLValueHom (G := G) M q σ))
        (nativeMapLocalDistribution M q f.1 σ) =
      (0 : RedDist
        ((K (AddCommGrpCat.of G) (q + 1)).obj Δ)) := by
    exact hkill
  rw [← hcomp] at hkill'
  have hkillNested :
      mapRedDist kEval
          (mapRedDist bCoc
            (nativeMapLocalDistribution M q f.1 σ)) = 0 := by
    rw [GeneralSphereT.StandardModels.mapRedDist_comp_apply]
    exact hkill'
  have hkInject : Function.Injective (mapRedDist kEval) := by
    rw [mapRedDist_eq_mapRedDistFn]
    exact mapRedDistFn_injective_of_injective kEval
      (supportCocycleKValue_injective M (q + 1) x)
  have hcoc : mapRedDist bCoc
      (nativeMapLocalDistribution M q f.1 σ) = 0 := by
    apply hkInject
    simpa using hkillNested
  rw [← supportCocycleToFacetCochainHom_comp_facetCoboundary
    (G := G) M q σ]
  rw [← GeneralSphereT.StandardModels.mapRedDist_comp_apply]
  rw [hcoc]
  exact map_zero _

end GeneralSphereT.SimplicialCochain
