import Formalization.CubeReduced
import Formalization.CubeKernel

set_option linter.style.header false

/-!
# The common coordinate-restriction kernel in reduced distributions

This file transfers the ambient cube-kernel calculation to the
augmentation-zero model.  The nonzero no-facet cubes form an honest subset
of the reduced cube basis, and they span exactly the common kernel of all
reduced coordinate restrictions.  The final equality also covers an empty
facet family; nonemptiness is needed only for the auxiliary ambient-index
constructor.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- Reduced distributions vanishing after restriction to every facet. -/
def reducedCoordinateCommonRestrictionKernel
    {Facet : Type*} (facets : Facet → Set ι) :
    Submodule ℤ (RedDist (Configuration ι G)) :=
  ⨅ ρ : Facet,
    LinearMap.ker (mapRedDist (coordinateRestriction (facets ρ)))

omit [LinearOrder ι] in
/-- Membership in the reduced common kernel is detected after forgetting the
augmentation-zero proof. -/
theorem mem_reducedCoordinateCommonRestrictionKernel_iff
    {Facet : Type*} (facets : Facet → Set ι)
    (u : RedDist (Configuration ι G)) :
    u ∈ reducedCoordinateCommonRestrictionKernel (G := G) facets ↔
      (u : Dist (Configuration ι G)) ∈
        coordinateCommonRestrictionKernel (G := G) facets := by
  rw [reducedCoordinateCommonRestrictionKernel,
    coordinateCommonRestrictionKernel]
  constructor
  · intro hu
    refine (Submodule.mem_iInf (fun ρ : Facet =>
      LinearMap.ker
        (mapDist (coordinateRestriction (facets ρ))))).2 fun ρ => ?_
    have huρ := (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker
        (mapRedDist (coordinateRestriction (facets σ))))).1 hu ρ
    rw [LinearMap.mem_ker] at huρ ⊢
    exact congrArg Subtype.val huρ
  · intro hu
    refine (Submodule.mem_iInf (fun ρ : Facet =>
      LinearMap.ker
        (mapRedDist (coordinateRestriction (facets ρ))))).2 fun ρ => ?_
    have huρ := (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker
        (mapDist (coordinateRestriction (facets σ))))).1 hu ρ
    rw [LinearMap.mem_ker] at huρ ⊢
    apply Subtype.ext
    exact huρ

omit [LinearOrder ι] in
/-- With at least one facet, an index contained in no facet cannot be zero. -/
theorem noFacetContainsCubeIndices_ne_zero
    {Facet : Type*} [Nonempty Facet] (facets : Facet → Set ι)
    {c : Configuration ι G}
    (hc : c ∈ noFacetContainsCubeIndices (G := G) facets) :
    c ≠ 0 := by
  intro hzero
  subst c
  let ρ : Facet := Classical.choice inferInstance
  exact hc ρ (by simp)

/-- A no-facet ambient cube, regarded canonically as a reduced distribution. -/
def noFacetReducedCubeDistribution
    {Facet : Type*} [Nonempty Facet] (facets : Facet → Set ι)
    (c : Configuration ι G)
    (hc : c ∈ noFacetContainsCubeIndices (G := G) facets) :
    RedDist (Configuration ι G) :=
  reducedCubeDistribution
    ⟨c, noFacetContainsCubeIndices_ne_zero facets hc⟩

@[simp]
theorem noFacetReducedCubeDistribution_coe
    {Facet : Type*} [Nonempty Facet] (facets : Facet → Set ι)
    (c : Configuration ι G)
    (hc : c ∈ noFacetContainsCubeIndices (G := G) facets) :
    ((noFacetReducedCubeDistribution facets c hc :
        RedDist (Configuration ι G)) : Dist (Configuration ι G)) =
      cubeDistribution c :=
  rfl

/-- Nonzero cube indices whose active support is contained in no facet. -/
def noFacetReducedCubeIndices
    {Facet : Type*} (facets : Facet → Set ι) :
    Set (NonzeroConfiguration ι G) :=
  {c | c.1 ∈ noFacetContainsCubeIndices (G := G) facets}

/-- The corresponding vectors in the nonzero cube basis. -/
def noFacetReducedCubeGenerators
    {Facet : Type*} (facets : Facet → Set ι) :
    Set (RedDist (Configuration ι G)) :=
  reducedCubeBasis (ι := ι) (G := G) ''
    noFacetReducedCubeIndices (G := G) facets

/-- Integral span of the reduced cubes contained in no facet. -/
def noFacetReducedCubeSpan
    {Facet : Type*} (facets : Facet → Set ι) :
    Submodule ℤ (RedDist (Configuration ι G)) :=
  Submodule.span ℤ (noFacetReducedCubeGenerators (G := G) facets)

/-- A no-facet reduced cube vanishes under every reduced restriction. -/
theorem noFacetReducedCubeGenerators_subset_commonKernel
    {Facet : Type*} (facets : Facet → Set ι) :
    noFacetReducedCubeGenerators (G := G) facets ⊆
      (reducedCoordinateCommonRestrictionKernel (G := G) facets :
        Set (RedDist (Configuration ι G))) := by
  rintro u ⟨c, hc, rfl⟩
  refine (Submodule.mem_iInf (fun ρ : Facet =>
    LinearMap.ker
      (mapRedDist (coordinateRestriction (facets ρ))))).2 fun ρ => ?_
  rw [reducedCubeBasis_apply, LinearMap.mem_ker]
  apply Subtype.ext
  change mapDist (coordinateRestriction (facets ρ))
      (cubeDistribution c.1) = 0
  exact mapDist_cubeDistribution_eq_zero_of_not_subset
    (facets ρ) c.1 (hc ρ)

/-- The easy inclusion: every no-facet reduced cube combination is locally
zero. -/
theorem noFacetReducedCubeSpan_le_commonKernel
    {Facet : Type*} (facets : Facet → Set ι) :
    noFacetReducedCubeSpan (G := G) facets ≤
      reducedCoordinateCommonRestrictionKernel (G := G) facets := by
  rw [noFacetReducedCubeSpan, Submodule.span_le]
  exact noFacetReducedCubeGenerators_subset_commonKernel (G := G) facets

/-- A reduced-basis coordinate is the same as the corresponding ambient
cube-basis coordinate after forgetting the augmentation-zero proof. -/
theorem reducedCube_repr_eq_cubeCoefficient
    (c : NonzeroConfiguration ι G)
    (u : RedDist (Configuration ι G)) :
    (reducedCubeBasis (ι := ι) (G := G)).repr u c =
      cubeCoefficient c.1 u.1 := by
  let left : RedDist (Configuration ι G) →ₗ[ℤ] ℤ :=
    (Finsupp.lapply c).comp
      (reducedCubeBasis (ι := ι) (G := G)).repr.toLinearMap
  let right : RedDist (Configuration ι G) →ₗ[ℤ] ℤ :=
    (cubeCoefficient c.1).comp (RedDist (Configuration ι G)).subtype
  have hmaps : left = right := by
    apply (reducedCubeBasis (ι := ι) (G := G)).ext
    intro c'
    simp only [left, right, LinearMap.comp_apply, Finsupp.lapply_apply,
      reducedCubeBasis_apply]
    have hrepr := congrArg
      (fun f : NonzeroConfiguration ι G →₀ ℤ => f c)
      ((reducedCubeBasis (ι := ι) (G := G)).repr_self c')
    by_cases h : c' = c
    · subst c'
      change
        (reducedCubeBasis (ι := ι) (G := G)).repr
            (reducedCubeDistribution c) c =
          cubeCoefficient c.1 (cubeDistribution c.1)
      have hrepr' :
          (reducedCubeBasis (ι := ι) (G := G)).repr
              (reducedCubeDistribution c) c = 1 := by
        simpa only [reducedCubeBasis_apply, Finsupp.single_eq_same] using hrepr
      rw [hrepr', cubeCoefficient_cubeDistribution_self]
    · have hval : c'.1 ≠ c.1 := by
        intro hv
        exact h (Subtype.ext hv)
      simpa [h, cubeCoefficient_cubeDistribution_ne _ _ hval] using hrepr
  exact LinearMap.congr_fun hmaps u

/-- The hard inclusion: local vanishing kills every reduced cube coefficient
whose support survives in at least one facet. -/
theorem reducedCoordinateCommonRestrictionKernel_le_noFacetReducedCubeSpan
    {Facet : Type*} (facets : Facet → Set ι) :
    reducedCoordinateCommonRestrictionKernel (G := G) facets ≤
      noFacetReducedCubeSpan (G := G) facets := by
  intro u hu
  rw [noFacetReducedCubeSpan, noFacetReducedCubeGenerators,
    Module.Basis.mem_span_image]
  intro c hcSupport
  change ∀ ρ : Facet, ¬∀ i ∈ c.1.support, i ∈ facets ρ
  intro ρ hcContained
  have huρ :
      u ∈ LinearMap.ker
        (mapRedDist (coordinateRestriction (facets ρ))) :=
    (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker
        (mapRedDist (coordinateRestriction (facets σ))))).1 hu ρ
  have hmapRed : mapRedDist (coordinateRestriction (facets ρ)) u = 0 :=
    LinearMap.mem_ker.mp huρ
  have hmapDist :
      mapDist (coordinateRestriction (facets ρ)) u.1 = 0 := by
    exact congrArg Subtype.val hmapRed
  have hcoefficient := LinearMap.congr_fun
    (cubeCoefficient_mapDist_coordinateRestriction
      (facets ρ) c.1 hcContained) u.1
  have hzero : cubeCoefficient c.1 u.1 = 0 := by
    simp only [LinearMap.comp_apply] at hcoefficient
    rw [hmapDist] at hcoefficient
    simpa only [LinearMap.map_zero] using hcoefficient.symm
  have hcoefficient_ne :
      (reducedCubeBasis (ι := ι) (G := G)).repr u c ≠ 0 :=
    Finsupp.mem_support_iff.mp hcSupport
  rw [reducedCube_repr_eq_cubeCoefficient] at hcoefficient_ne
  exact hcoefficient_ne hzero

/-- Exact reduced version of (2.20): the common local-zero subgroup is the
span of precisely the nonzero cube-basis vectors whose support lies in no
facet. -/
theorem reducedCoordinateCommonRestrictionKernel_eq_noFacetReducedCubeSpan
    {Facet : Type*} (facets : Facet → Set ι) :
    reducedCoordinateCommonRestrictionKernel (G := G) facets =
      noFacetReducedCubeSpan (G := G) facets := by
  apply le_antisymm
  · exact
      reducedCoordinateCommonRestrictionKernel_le_noFacetReducedCubeSpan
        facets
  · exact noFacetReducedCubeSpan_le_commonKernel facets

end GeneralSphereT.PathAlgebra
