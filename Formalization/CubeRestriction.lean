import Formalization.CubeBasis
import Formalization.CoordinateRestriction

set_option linter.style.header false

/-!
# Coordinate restriction of Boolean cube distributions

This file isolates the algebra behind (2.20)--(2.21).  A coordinate
restriction sends a cube to the corresponding cube if all active coordinates
survive, and to zero as soon as one active coordinate is deleted.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

omit [LinearOrder ι] in
/-- Pushforward of distributions agrees with the induced group-ring map. -/
theorem distributionToRing_mapDist
    {κ H : Type*} [AddCommGroup H]
    (f : Configuration ι G →+ Configuration κ H)
    (u : Dist (Configuration ι G)) :
    distributionToRing (mapDist f u) =
      AddMonoidAlgebra.mapDomainRingHom ℤ f (distributionToRing u) := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add x n u _ _ ih =>
      simp only [map_add, mapDist_single, distributionToRing_single, ih]
      simp

omit [LinearOrder ι] in
/-- The group-ring expression whose coefficients are a pushed-forward cube. -/
theorem distributionToRing_mapDist_cubeDistribution
    {κ H : Type*} [AddCommGroup H]
    (f : Configuration ι G →+ Configuration κ H)
    (c : Configuration ι G) :
    distributionToRing (mapDist f (cubeDistribution c)) =
      AddMonoidAlgebra.mapDomainRingHom ℤ f (cube c) := by
  rw [distributionToRing_mapDist]
  congr 1

/-- Restricting every surviving coordinate factor gives the target cube. -/
theorem mapDomain_cube_of_support_subset (S : Set ι)
    (c : Configuration ι G) (hS : ∀ i ∈ c.support, i ∈ S) :
    AddMonoidAlgebra.mapDomainRingHom ℤ (coordinateRestriction S) (cube c) =
      cube (coordinateRestriction S c) := by
  classical
  let F : ι → ConfigurationRing S G := fun i =>
    if hi : i ∈ S then
      delta (Finsupp.single ⟨i, hi⟩ (c i)) - 1
    else
      1
  calc
    AddMonoidAlgebra.mapDomainRingHom ℤ (coordinateRestriction S) (cube c) =
        ∏ i ∈ c.support, F i := by
      rw [cube, cubeOn, map_prod]
      apply Finset.prod_congr rfl
      intro i hi
      have hiS : i ∈ S := hS i hi
      rw [map_sub, map_one]
      change
        AddMonoidAlgebra.mapDomain (coordinateRestriction S)
            (AddMonoidAlgebra.single (Finsupp.single i (c i)) 1) - 1 = F i
      rw [AddMonoidAlgebra.mapDomain_single,
        coordinateRestriction_single_mem S hiS]
      simp [F, hiS, delta]
    _ = ∏ i ∈ c.support.subtype (fun j => j ∈ S), F i.1 := by
      exact (Finset.prod_subtype_of_mem F hS).symm
    _ = cube (coordinateRestriction S c) := by
      rw [cube, cubeOn, support_coordinateRestriction]
      apply Finset.prod_congr rfl
      intro i hi
      simp [F, coordinateRestriction_apply]

omit [LinearOrder ι] in
/-- If restriction deletes an active coordinate, one difference factor becomes zero. -/
theorem mapDomain_cube_eq_zero_of_active_not_mem (S : Set ι)
    (c : Configuration ι G) {i : ι} (hic : i ∈ c.support) (hiS : i ∉ S) :
    AddMonoidAlgebra.mapDomainRingHom ℤ (coordinateRestriction S) (cube c) = 0 := by
  classical
  rw [cube, cubeOn, map_prod]
  apply Finset.prod_eq_zero hic
  rw [map_sub, map_one]
  change
    AddMonoidAlgebra.mapDomain (coordinateRestriction S)
        (AddMonoidAlgebra.single (Finsupp.single i (c i)) 1) - 1 = 0
  rw [AddMonoidAlgebra.mapDomain_single,
    coordinateRestriction_single_not_mem S hiS]
  change delta (0 : Configuration S G) - 1 = 0
  simp

/-- A cube supported inside `S` restricts to the corresponding cube on `S`. -/
theorem mapDist_cubeDistribution_of_support_subset (S : Set ι)
    (c : Configuration ι G) (hS : ∀ i ∈ c.support, i ∈ S) :
    mapDist (coordinateRestriction S) (cubeDistribution c) =
      cubeDistribution (coordinateRestriction S c) := by
  have hRing :
      distributionToRing
          (mapDist (coordinateRestriction S) (cubeDistribution c)) =
        distributionToRing
          (cubeDistribution (coordinateRestriction S c)) := by
    rw [distributionToRing_mapDist_cubeDistribution,
      mapDomain_cube_of_support_subset S c hS]
    exact (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm.apply_symm_apply _
  simpa only [coeff_distributionToRing] using
    congrArg AddMonoidAlgebra.coeff hRing

omit [LinearOrder ι] in
/-- A cube vanishes under restriction if any active coordinate is deleted. -/
theorem mapDist_cubeDistribution_eq_zero_of_active_not_mem (S : Set ι)
    (c : Configuration ι G) {i : ι} (hic : i ∈ c.support) (hiS : i ∉ S) :
    mapDist (coordinateRestriction S) (cubeDistribution c) = 0 := by
  have hRing :
      distributionToRing
          (mapDist (coordinateRestriction S) (cubeDistribution c)) =
        distributionToRing (0 : Dist (Configuration S G)) := by
    rw [distributionToRing_mapDist_cubeDistribution,
      mapDomain_cube_eq_zero_of_active_not_mem S c hic hiS]
    simp
  simpa only [coeff_distributionToRing] using
    congrArg AddMonoidAlgebra.coeff hRing

omit [LinearOrder ι] in
/-- Existential form used directly in locality arguments. -/
theorem mapDist_cubeDistribution_eq_zero_of_not_subset (S : Set ι)
    (c : Configuration ι G) (hS : ¬∀ i ∈ c.support, i ∈ S) :
    mapDist (coordinateRestriction S) (cubeDistribution c) = 0 := by
  push Not at hS
  obtain ⟨i, hic, hiS⟩ := hS
  exact mapDist_cubeDistribution_eq_zero_of_active_not_mem S c hic hiS

/-- Distributions that vanish after restriction to every member of a facet family. -/
def coordinateCommonRestrictionKernel
    {Facet : Type*} (facets : Facet → Set ι) :
    Submodule ℤ (Dist (Configuration ι G)) :=
  ⨅ ρ : Facet, LinearMap.ker (mapDist (coordinateRestriction (facets ρ)))

/-- Cube indices whose active support is contained in no facet of the family. -/
def noFacetContainsCubeIndices
    {Facet : Type*} (facets : Facet → Set ι) :
    Set (Configuration ι G) :=
  {c | ∀ ρ : Facet, ¬∀ i ∈ c.support, i ∈ facets ρ}

/-- Cube basis vectors whose active support is contained in no facet. -/
def noFacetCubeGenerators
    {Facet : Type*} (facets : Facet → Set ι) :
    Set (Dist (Configuration ι G)) :=
  cubeBasis (ι := ι) (G := G) '' noFacetContainsCubeIndices facets

/-- Integral combinations of cube vectors contained in no facet. -/
def noFacetCubeSpan
    {Facet : Type*} (facets : Facet → Set ι) :
    Submodule ℤ (Dist (Configuration ι G)) :=
  Submodule.span ℤ (noFacetCubeGenerators facets)

/-- Every no-facet cube generator vanishes under every facet restriction. -/
theorem noFacetCubeGenerators_subset_commonRestrictionKernel
    {Facet : Type*} (facets : Facet → Set ι) :
    noFacetCubeGenerators (G := G) facets ⊆
      (coordinateCommonRestrictionKernel (G := G) facets :
        Set (Dist (Configuration ι G))) := by
  rintro u ⟨c, hc, rfl⟩
  refine (Submodule.mem_iInf (fun ρ : Facet =>
    LinearMap.ker
      (mapDist (coordinateRestriction (facets ρ))))).2 fun ρ => ?_
  rw [cubeBasis_apply, LinearMap.mem_ker]
  exact mapDist_cubeDistribution_eq_zero_of_not_subset
    (facets ρ) c (hc ρ)

/--
The span of all cube vectors contained in no facet lies in the common kernel.
This is the locally-zero direction of (2.20), independent of basis-coordinate
bookkeeping for the reverse inclusion.
-/
theorem noFacetCubeSpan_le_commonRestrictionKernel
    {Facet : Type*} (facets : Facet → Set ι) :
    noFacetCubeSpan (G := G) facets ≤
      coordinateCommonRestrictionKernel (G := G) facets := by
  rw [noFacetCubeSpan, Submodule.span_le]
  exact noFacetCubeGenerators_subset_commonRestrictionKernel (G := G) facets

end GeneralSphereT.PathAlgebra
