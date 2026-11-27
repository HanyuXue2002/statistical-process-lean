import Formalization.CubeRestriction

set_option linter.style.header false

/-!
# Reverse inclusion for the common cube-restriction kernel

This file supplies the basis-coordinate argument completing the formalization
of (2.20).  Restriction preserves the coefficient of every
cube whose support survives.  Hence an element of the restriction kernel has
no surviving cube coefficient, which gives the reverse span inclusion.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- The coefficient of a distribution in the integral cube basis. -/
def cubeCoefficient (c : Configuration ι G) :
    Dist (Configuration ι G) →ₗ[ℤ] ℤ :=
  (Finsupp.lapply c :
      (Configuration ι G →₀ ℤ) →ₗ[ℤ] ℤ).comp
    (cubeBasis (ι := ι) (G := G)).repr.toLinearMap

@[simp]
theorem cubeCoefficient_cubeDistribution_self
    (c : Configuration ι G) :
    cubeCoefficient c (cubeDistribution c) = 1 := by
  simp only [cubeCoefficient, LinearMap.comp_apply, Finsupp.lapply_apply]
  rw [← cubeBasis_apply]
  have hrepr := congrArg
    (fun f : Configuration ι G →₀ ℤ => f c)
    ((cubeBasis (ι := ι) (G := G)).repr_self c)
  simpa using hrepr

theorem cubeCoefficient_cubeDistribution_ne
    (c c' : Configuration ι G) (h : c' ≠ c) :
    cubeCoefficient c (cubeDistribution c') = 0 := by
  simp only [cubeCoefficient, LinearMap.comp_apply, Finsupp.lapply_apply]
  rw [← cubeBasis_apply]
  have hrepr := congrArg
    (fun f : Configuration ι G →₀ ℤ => f c)
    ((cubeBasis (ι := ι) (G := G)).repr_self c')
  simpa [h] using hrepr

omit [LinearOrder ι] in
/-- Restriction is injective among configurations supported inside `S`. -/
theorem coordinateRestriction_injective_on_support (S : Set ι)
    {c c' : Configuration ι G}
    (hc : ∀ i ∈ c.support, i ∈ S)
    (hc' : ∀ i ∈ c'.support, i ∈ S)
    (h : coordinateRestriction S c = coordinateRestriction S c') :
    c = c' := by
  ext i
  by_cases hiS : i ∈ S
  · exact DFunLike.congr_fun h ⟨i, hiS⟩
  · have hci : c i = 0 := by
      by_contra hne
      exact hiS (hc i (Finsupp.mem_support_iff.mpr hne))
    have hci' : c' i = 0 := by
      by_contra hne
      exact hiS (hc' i (Finsupp.mem_support_iff.mpr hne))
    rw [hci, hci']

/-- On a surviving cube index, its cube coefficient commutes with restriction. -/
theorem cubeCoefficient_mapDist_coordinateRestriction (S : Set ι)
    (c : Configuration ι G) (hc : ∀ i ∈ c.support, i ∈ S) :
    (cubeCoefficient (coordinateRestriction S c)).comp
        (mapDist (coordinateRestriction S)) =
      cubeCoefficient c := by
  classical
  apply (cubeBasis (ι := ι) (G := G)).ext
  intro c'
  rw [cubeBasis_apply]
  simp only [LinearMap.comp_apply]
  by_cases hc' : ∀ i ∈ c'.support, i ∈ S
  · rw [mapDist_cubeDistribution_of_support_subset S c' hc']
    by_cases hcc' : c' = c
    · subst c'
      simp only [cubeCoefficient_cubeDistribution_self]
    · have hres :
          coordinateRestriction S c' ≠ coordinateRestriction S c := by
        intro h
        exact hcc' (coordinateRestriction_injective_on_support S hc' hc h)
      rw [cubeCoefficient_cubeDistribution_ne _ _ hres,
        cubeCoefficient_cubeDistribution_ne _ _ hcc']
  · have hcc' : c' ≠ c := by
      intro h
      subst c'
      exact hc' hc
    rw [mapDist_cubeDistribution_eq_zero_of_not_subset S c' hc']
    simp only [LinearMap.map_zero,
      cubeCoefficient_cubeDistribution_ne _ _ hcc']

/-- Cube indices having at least one active coordinate outside `S`. -/
def restrictionInvisibleCubeIndices (S : Set ι) :
    Set (Configuration ι G) :=
  {c | ¬∀ i ∈ c.support, i ∈ S}

/-- The span of the cube basis vectors deleted by restriction to `S`. -/
def restrictionInvisibleCubeSpan (S : Set ι) :
    Submodule ℤ (Dist (Configuration ι G)) :=
  Submodule.span ℤ
    (cubeBasis (ι := ι) (G := G) ''
      restrictionInvisibleCubeIndices (G := G) S)

/-- The already-proved vanishing behavior gives the easy kernel inclusion. -/
theorem restrictionInvisibleCubeSpan_le_ker (S : Set ι) :
    restrictionInvisibleCubeSpan (G := G) S ≤
      LinearMap.ker (mapDist (coordinateRestriction S)) := by
  rw [restrictionInvisibleCubeSpan, Submodule.span_le]
  rintro u ⟨c, hc, rfl⟩
  rw [cubeBasis_apply]
  change mapDist (coordinateRestriction S) (cubeDistribution c) = 0
  exact mapDist_cubeDistribution_eq_zero_of_not_subset S c hc

/--
The kernel of one coordinate restriction is exactly the span of cube basis
vectors with an active coordinate outside the restricted set.
-/
theorem ker_mapDist_coordinateRestriction_eq_cubeSpan (S : Set ι) :
    LinearMap.ker (mapDist (coordinateRestriction S)) =
      restrictionInvisibleCubeSpan (G := G) S := by
  apply le_antisymm
  · intro u hu
    rw [restrictionInvisibleCubeSpan, Module.Basis.mem_span_image]
    intro c hcSupport
    change ¬∀ i ∈ c.support, i ∈ S
    intro hc
    have hcoeff := LinearMap.congr_fun
      (cubeCoefficient_mapDist_coordinateRestriction S c hc) u
    have hzero : cubeCoefficient c u = 0 := by
      simp only [LinearMap.comp_apply] at hcoeff
      rw [LinearMap.mem_ker.mp hu] at hcoeff
      simpa only [LinearMap.map_zero] using hcoeff.symm
    unfold cubeCoefficient at hzero
    change (cubeBasis (ι := ι) (G := G)).repr u c = 0 at hzero
    exact (Finsupp.mem_support_iff.mp hcSupport) hzero
  · exact restrictionInvisibleCubeSpan_le_ker S

/-- Every element of the common kernel has only no-facet cube coefficients. -/
theorem coordinateCommonRestrictionKernel_le_noFacetCubeSpan
    {Facet : Type*} (facets : Facet → Set ι) :
    coordinateCommonRestrictionKernel (G := G) facets ≤
      noFacetCubeSpan (G := G) facets := by
  intro u hu
  rw [noFacetCubeSpan, noFacetCubeGenerators,
    Module.Basis.mem_span_image]
  intro c hcSupport
  change ∀ ρ : Facet, ¬∀ i ∈ c.support, i ∈ facets ρ
  intro ρ
  have huρ :
      u ∈ LinearMap.ker
        (mapDist (coordinateRestriction (facets ρ))) :=
    (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker
        (mapDist (coordinateRestriction (facets σ))))).mp hu ρ
  have huSpan :
      u ∈ restrictionInvisibleCubeSpan (G := G) (facets ρ) := by
    rw [← ker_mapDist_coordinateRestriction_eq_cubeSpan]
    exact huρ
  rw [restrictionInvisibleCubeSpan, Module.Basis.mem_span_image] at huSpan
  exact huSpan hcSupport

/--
Full basis decomposition of the common restriction kernel, i.e. the formal
version of (2.20).
-/
theorem coordinateCommonRestrictionKernel_eq_noFacetCubeSpan
    {Facet : Type*} (facets : Facet → Set ι) :
    coordinateCommonRestrictionKernel (G := G) facets =
      noFacetCubeSpan (G := G) facets := by
  apply le_antisymm
  · exact coordinateCommonRestrictionKernel_le_noFacetCubeSpan facets
  · exact noFacetCubeSpan_le_commonRestrictionKernel facets

end GeneralSphereT.PathAlgebra
