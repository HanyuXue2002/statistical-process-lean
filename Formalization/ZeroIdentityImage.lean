import Formalization.DistributionDifferences
import Formalization.ReducedLocalKernel

set_option linter.style.header false

/-!
# The image of the locally-zero primitive distributions

This module proves the distribution-level content of Lemma 2.25.
The target is defined directly as the span of physical finite-difference
cubes.  A generator has a nonempty list of primitive increments, and on every
facet at least one increment restricts to zero.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

section ReducedFiniteDifferences

variable {X : Type*} [AddCommGroup X]

/-- Translation preserves the total coefficient of a finite distribution. -/
theorem augmentation_distributionTranslation (a : X) (u : Dist X) :
    augmentation X (distributionTranslation a u) = augmentation X u := by
  induction u using Finsupp.induction with
  | zero => simp
  | single_add x n u _ _ ih =>
      simp [ih]

/-- Every single finite difference has augmentation zero. -/
theorem augmentation_distributionDifference (a : X) (u : Dist X) :
    augmentation X (distributionDifference a u) = 0 := by
  rw [distributionDifference]
  simp [augmentation_distributionTranslation]

/-- A nonempty iterated finite difference has augmentation zero. -/
theorem augmentation_iteratedDistributionDifference_of_ne_nil
    (steps : List X) (hsteps : steps ≠ []) (u : Dist X) :
    augmentation X (iteratedDistributionDifference steps u) = 0 := by
  cases steps with
  | nil => exact (hsteps rfl).elim
  | cons a steps =>
      rw [iteratedDistributionDifference_cons, LinearMap.comp_apply]
      exact augmentation_distributionDifference a _

/-- A nonempty iterated difference, bundled in the augmentation kernel. -/
def reducedIteratedPointDifference
    (steps : List X) (hsteps : steps ≠ []) (a : X) : RedDist X :=
  ⟨iteratedDistributionDifference steps (Finsupp.single a 1),
    augmentation_iteratedDistributionDifference_of_ne_nil steps hsteps _⟩

@[simp]
theorem reducedIteratedPointDifference_coe
    (steps : List X) (hsteps : steps ≠ []) (a : X) :
    ((reducedIteratedPointDifference steps hsteps a : RedDist X) : Dist X) =
      iteratedDistributionDifference steps (Finsupp.single a 1) :=
  rfl

@[simp]
theorem distributionDifference_zero :
    distributionDifference (0 : X) = 0 := by
  ext x
  simp [distributionDifference]

/-- If one step is zero, the whole iterated finite difference vanishes. -/
theorem iteratedDistributionDifference_eq_zero_of_zero_mem
    (steps : List X) (hzero : 0 ∈ steps) (u : Dist X) :
    iteratedDistributionDifference steps u = 0 := by
  induction steps with
  | nil => simp at hzero
  | cons a steps ih =>
      simp only [List.mem_cons] at hzero
      rcases hzero with rfl | hzero
      · simp
      · rw [iteratedDistributionDifference_cons, LinearMap.comp_apply,
          ih hzero]
        simp

end ReducedFiniteDifferences

section PhysicalNonfaceCubes

variable {ι G B Facet : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]

/--
The physical cube with primitive increment list `rs` and physical base `a`.
The list is required to be nonempty exactly so that the result belongs to the
reduced distribution group.
-/
def physicalNonfaceCube
    (d : Configuration ι G →+ B)
    (rs : List (Configuration ι G)) (hrs : rs ≠ []) (a : B) :
    RedDist B :=
  reducedIteratedPointDifference (rs.map d) (by simpa using hrs) a

omit [LinearOrder ι] in
@[simp]
theorem physicalNonfaceCube_coe
    (d : Configuration ι G →+ B)
    (rs : List (Configuration ι G)) (hrs : rs ≠ []) (a : B) :
    ((physicalNonfaceCube d rs hrs a : RedDist B) : Dist B) =
      iteratedDistributionDifference (rs.map d) (Finsupp.single a 1) :=
  rfl

/--
Raw generators for `D_id`: on each facet, one increment in the nonempty list
becomes zero.  The witness may depend on the facet.
-/
def physicalNonfaceCubeGenerators
    (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    Set (RedDist B) :=
  {u | ∃ (rs : List (Configuration ι G)) (hrs : rs ≠ []) (a : B),
    (∀ ρ : Facet, ∃ r ∈ rs,
      coordinateRestriction (facets ρ) r = 0) ∧
    u = physicalNonfaceCube d rs hrs a}

/-- The physical subgroup `D_id`, defined without a bar-resolution model. -/
def physicalNonfaceCubeSpan
    (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    Submodule ℤ (RedDist B) :=
  Submodule.span ℤ (physicalNonfaceCubeGenerators facets d)

omit [LinearOrder ι] in
/-- The active one-coordinate increment list of a nonzero cube is nonempty. -/
theorem activeCoordinateIncrements_ne_nil
    (c : NonzeroConfiguration ι G) :
    activeCoordinateIncrements c.1 ≠ [] := by
  have hsupp : c.1.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr c.2
  intro hnil
  have : c.1.support.toList = [] := by
    exact List.map_eq_nil_iff.mp hnil
  exact hsupp.toList_ne_nil this

omit [LinearOrder ι] in
/-- A no-facet cube index supplies the required vanishing increment on every
facet. -/
theorem activeCoordinateIncrements_cover_facets
    (facets : Facet → Set ι) (c : NonzeroConfiguration ι G)
    (hc : c.1 ∈ noFacetContainsCubeIndices (G := G) facets) :
    ∀ ρ : Facet, ∃ r ∈ activeCoordinateIncrements c.1,
      coordinateRestriction (facets ρ) r = 0 := by
  intro ρ
  have hcρ := hc ρ
  push Not at hcρ
  obtain ⟨i, hic, hiρ⟩ := hcρ
  refine ⟨Finsupp.single i (c.1 i), ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨i, by simpa using hic, rfl⟩
  · exact coordinateRestriction_single_not_mem (facets ρ) hiρ (c.1 i)

/-- The image of every reduced no-facet cube is one of the physical
generators (with base zero). -/
theorem mapRedDist_noFacetReducedCube_mem_physicalNonfaceCubeSpan
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (c : NonzeroConfiguration ι G)
    (hc : c.1 ∈ noFacetContainsCubeIndices (G := G) facets) :
    mapRedDist d (reducedCubeDistribution c) ∈
      physicalNonfaceCubeSpan facets d := by
  apply Submodule.subset_span
  refine ⟨activeCoordinateIncrements c.1,
    activeCoordinateIncrements_ne_nil c, 0,
    activeCoordinateIncrements_cover_facets facets c hc, ?_⟩
  apply Subtype.ext
  rw [mapRedDist_coe, reducedCubeDistribution_coe,
    physicalNonfaceCube_coe,
    mapDist_cubeDistribution_eq_iteratedDistributionDifference]
  simp [activeCoordinateIncrements, List.map_map, Function.comp_def]

/-- The image of the common primitive restriction kernel is contained in the
physical nonface-cube span. -/
theorem map_reducedCoordinateCommonRestrictionKernel_le_physicalNonfaceCubeSpan
    (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    Submodule.map (mapRedDist d)
        (reducedCoordinateCommonRestrictionKernel (G := G) facets) ≤
      physicalNonfaceCubeSpan facets d := by
  rintro u ⟨v, hv, rfl⟩
  rw [reducedCoordinateCommonRestrictionKernel_eq_noFacetReducedCubeSpan]
    at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨c, hc, rfl⟩
      rw [reducedCubeBasis_apply]
      exact mapRedDist_noFacetReducedCube_mem_physicalNonfaceCubeSpan
        facets d c hc
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using Submodule.add_mem _ ihx ihy
  | smul n x hx ih =>
      simpa using Submodule.smul_mem _ n ih

omit [LinearOrder ι] in
/-- A physical nonface cube has a locally-zero primitive lift.  Surjectivity
is used only to lift its base point. -/
theorem physicalNonfaceCubeGenerators_subset_map_commonKernel
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (hd : Function.Surjective d) :
    physicalNonfaceCubeGenerators facets d ⊆
      (Submodule.map (mapRedDist d)
        (reducedCoordinateCommonRestrictionKernel (G := G) facets) :
          Set (RedDist B)) := by
  rintro u ⟨rs, hrs, a, hcover, rfl⟩
  obtain ⟨c, hc⟩ := hd a
  let v : RedDist (Configuration ι G) :=
    reducedIteratedPointDifference rs hrs c
  have hv : v ∈
      reducedCoordinateCommonRestrictionKernel (G := G) facets := by
    rw [reducedCoordinateCommonRestrictionKernel, Submodule.mem_iInf]
    intro ρ
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change mapDist (coordinateRestriction (facets ρ))
      (iteratedDistributionDifference rs (Finsupp.single c 1)) = 0
    rw [mapDist_iteratedDistributionDifference_apply]
    obtain ⟨r, hr, hρ⟩ := hcover ρ
    apply iteratedDistributionDifference_eq_zero_of_zero_mem
    exact List.mem_map.mpr ⟨r, hr, hρ⟩
  refine ⟨v, hv, ?_⟩
  apply Subtype.ext
  change mapDist d
      (iteratedDistributionDifference rs (Finsupp.single c 1)) =
    iteratedDistributionDifference (rs.map d) (Finsupp.single a 1)
  rw [mapDist_iteratedDistributionDifference_apply, mapDist_single, hc]

omit [LinearOrder ι] in
/-- Every physical generator, hence its span, lies in the image of the common
primitive restriction kernel. -/
theorem physicalNonfaceCubeSpan_le_map_reducedCoordinateCommonRestrictionKernel
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (hd : Function.Surjective d) :
    physicalNonfaceCubeSpan facets d ≤
      Submodule.map (mapRedDist d)
        (reducedCoordinateCommonRestrictionKernel (G := G) facets) := by
  rw [physicalNonfaceCubeSpan, Submodule.span_le]
  exact physicalNonfaceCubeGenerators_subset_map_commonKernel facets d hd

/--
Distribution-level Lemma 2.25: for a surjective coboundary map, the image of
the locally-zero primitive reduced distributions is exactly the span of the
physical nonface cubes.
-/
theorem map_reducedCoordinateCommonRestrictionKernel_eq_physicalNonfaceCubeSpan
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (hd : Function.Surjective d) :
    Submodule.map (mapRedDist d)
        (reducedCoordinateCommonRestrictionKernel (G := G) facets) =
      physicalNonfaceCubeSpan facets d := by
  apply le_antisymm
  · exact
      map_reducedCoordinateCommonRestrictionKernel_le_physicalNonfaceCubeSpan
        facets d
  · exact
      physicalNonfaceCubeSpan_le_map_reducedCoordinateCommonRestrictionKernel
        facets d hd

end PhysicalNonfaceCubes

end GeneralSphereT.PathAlgebra
