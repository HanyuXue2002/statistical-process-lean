import Formalization.TauQuotient
import Formalization.RelativeDistributionLift
import Formalization.Section3SquareStripLocality

set_option linter.style.header false

/-!
# Section 3: the simplex-local `tau` lemma

The local vanishing argument does not need paths or a bar resolution.  Its
only geometric input is a set-theoretic primitive section whose restriction
to every facet in the chosen carrier family depends only on the restricted
physical configuration.  Extending that section over free integral
distributions gives a locally-zero primitive lift.  The cube-kernel theorem
from Section 2 then says that its physical image is a locality identity.

This file first isolates that argument independently of simplicial cochains.
The simplicial closed-star construction is instantiated below.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

variable {C : Type*} [AddCommGroup C]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type*}
variable [∀ σ, AddCommGroup (CAt σ)] [∀ σ, AddCommGroup (BAt σ)]
variable {d : C →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-!
## A primitive section adapted to one carrier family
-/

/--
A set-theoretic section of `d` whose restriction to every facet is a
function of the restricted physical configuration.

No additivity is required.  This is exactly the input used in (2.22)--(2.24)
for one fixed nonempty simplex `ρ`.
-/
structure FacetwisePrimitiveSectionData where
  globalPrimitive : B → C
  map_globalPrimitive : ∀ a : B, d (globalPrimitive a) = a
  localPrimitive : ∀ σ : Facet, BAt σ → CAt σ
  restrict_globalPrimitive : ∀ (σ : Facet) (a : B),
    L.primitiveRes σ (globalPrimitive a) =
      localPrimitive σ (L.physicalRes σ a)

namespace FacetwisePrimitiveSectionData

variable (A : FacetwisePrimitiveSectionData L)

/-- Linear extension of the chosen primitive over augmentation-zero integral
distributions. -/
def distributionLift : RedDist B →ₗ[ℤ] RedDist C :=
  mapRedDistFn A.globalPrimitive

/-- The distribution lift is a right inverse to physical pushforward. -/
theorem mapRedDist_distributionLift (z : RedDist B) :
    mapRedDist d (distributionLift L A z) = z := by
  rw [mapRedDist_eq_mapRedDistFn]
  rw [distributionLift, mapRedDistFn_comp_apply]
  apply Subtype.ext
  have hfun : (d : C → B) ∘ A.globalPrimitive = id := by
    funext a
    exact A.map_globalPrimitive a
  rw [hfun]
  change mapDistFn id z.1 = z.1
  have hid : mapDistFn (id : B → B) = LinearMap.id := by
    ext a
    simp
  exact LinearMap.congr_fun hid z.1

/-- Restriction of the lifted distribution is obtained by applying the local
primitive section to the restricted physical distribution. -/
theorem restrict_distributionLift (σ : Facet) (z : RedDist B) :
    mapRedDist (L.primitiveRes σ) (distributionLift L A z) =
      mapRedDistFn (A.localPrimitive σ)
        (mapRedDist (L.physicalRes σ) z) := by
  rw [mapRedDist_eq_mapRedDistFn, mapRedDist_eq_mapRedDistFn]
  rw [distributionLift, mapRedDistFn_comp_apply,
    mapRedDistFn_comp_apply]
  apply Subtype.ext
  have hfun :
      (L.primitiveRes σ : C → CAt σ) ∘ A.globalPrimitive =
        A.localPrimitive σ ∘ (L.physicalRes σ : B → BAt σ) := by
    funext a
    exact A.restrict_globalPrimitive σ a
  rw [hfun]

/-- A physical distribution which vanishes on every selected facet has a
primitive lift which vanishes on every selected facet. -/
theorem distributionLift_mem_locallyZeroRedDist
    {z : RedDist B} (hz : z ∈ L.physicalInvariantDistributions) :
    distributionLift L A z ∈ L.locallyZeroRedDist := by
  rw [FacetRestrictionData.locallyZeroRedDist, Submodule.mem_iInf]
  intro σ
  rw [LinearMap.mem_ker]
  change mapRedDist (L.primitiveRes σ) (distributionLift L A z) = 0
  rw [restrict_distributionLift L A σ z]
  have hzσ : mapRedDist (L.physicalRes σ) z = 0 := by
    exact LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun τ : Facet =>
        LinearMap.ker (L.restrictPhysicalRedDist τ))).1 hz σ)
  rw [hzσ]
  simp

end FacetwisePrimitiveSectionData

/-!
## The elementary local-`tau` argument
-/

section CoordinateCarrier

open FacetwisePrimitiveSectionData

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable (facets : Facet → Set ι)
variable {BAt : Facet → Type*} [∀ σ, AddCommGroup (BAt σ)]
variable {d : Configuration ι G →+ B}
variable (L : FacetRestrictionData
  (CAt := fun σ => Configuration (facets σ) G)
  (BAt := BAt) (Facet := Facet) d)

/-!
### The elementary refinement

The ordinary `physicalNonfaceCubeSpan` permits arbitrary cochain increments.
For the cone-operator replacement we record the stronger subgroup in which
every increment is a nonzero one-coordinate label.  This is the precise
input accepted by `ellDistribution_elementaryCube_mem_physicalIdentityPaths`.
-/

/-- Local configuration cubes all of whose active labels are elementary. -/
def elementaryPhysicalNonfaceCubeGenerators
    (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    Set (RedDist B) :=
  {u | ∃ (rs : List (Configuration ι G)) (hrs : rs ≠ []) (a : B),
    (∀ r ∈ rs, IsElementaryLabel r) ∧
    (∀ σ : Facet, ∃ r ∈ rs,
      coordinateRestriction (facets σ) r = 0) ∧
    u = physicalNonfaceCube d rs hrs a}

/-- Span of elementary local configuration cubes. -/
def elementaryPhysicalNonfaceCubeSpan
    (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    Submodule ℤ (RedDist B) :=
  Submodule.span ℤ
    (elementaryPhysicalNonfaceCubeGenerators facets d)

omit [LinearOrder ι] in
/-- Every active-coordinate label in the cube basis is elementary. -/
theorem activeCoordinateIncrements_isElementary
    (c : NonzeroConfiguration ι G) :
    ∀ r ∈ activeCoordinateIncrements c.1, IsElementaryLabel r := by
  intro r hr
  rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
  refine ⟨i, c.1 i, ?_, rfl⟩
  exact Finsupp.mem_support_iff.mp (by simpa using hi)

omit [LinearOrder ι] in
/-- An elementary local cube is, in particular, an ordinary local cube. -/
theorem elementaryPhysicalNonfaceCubeSpan_le_physicalNonfaceCubeSpan :
    elementaryPhysicalNonfaceCubeSpan facets d ≤
      physicalNonfaceCubeSpan facets d := by
  rw [elementaryPhysicalNonfaceCubeSpan, Submodule.span_le]
  rintro u ⟨rs, hrs, a, _, hcover, rfl⟩
  apply Submodule.subset_span
  exact ⟨rs, hrs, a, hcover, rfl⟩

/-- Each no-facet cube-basis vector maps to an elementary physical local
cube, not merely to the larger arbitrary-increment denominator. -/
theorem mapRedDist_noFacetReducedCube_mem_elementaryPhysicalNonfaceCubeSpan
    (c : NonzeroConfiguration ι G)
    (hc : c.1 ∈ noFacetContainsCubeIndices (G := G) facets) :
    mapRedDist d (reducedCubeDistribution c) ∈
      elementaryPhysicalNonfaceCubeSpan facets d := by
  apply Submodule.subset_span
  refine ⟨activeCoordinateIncrements c.1,
    activeCoordinateIncrements_ne_nil c, 0,
    activeCoordinateIncrements_isElementary c,
    activeCoordinateIncrements_cover_facets facets c hc, ?_⟩
  apply Subtype.ext
  rw [mapRedDist_coe, reducedCubeDistribution_coe,
    physicalNonfaceCube_coe,
    mapDist_cubeDistribution_eq_iteratedDistributionDifference]
  simp [activeCoordinateIncrements, List.map_map, Function.comp_def]

/-- Strengthened form of the support decomposition: the whole common
restriction kernel maps into the elementary local-cube span. -/
theorem map_reducedCoordinateCommonRestrictionKernel_le_elementarySpan :
    Submodule.map (mapRedDist d)
        (reducedCoordinateCommonRestrictionKernel (G := G) facets) ≤
      elementaryPhysicalNonfaceCubeSpan facets d := by
  rintro u ⟨v, hv, rfl⟩
  rw [reducedCoordinateCommonRestrictionKernel_eq_noFacetReducedCubeSpan]
    at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨c, hc, rfl⟩
      rw [reducedCubeBasis_apply]
      exact
        mapRedDist_noFacetReducedCube_mem_elementaryPhysicalNonfaceCubeSpan
          facets (d := d) c hc
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using Submodule.add_mem _ ihx ihy
  | smul n x hx ih =>
      simpa using Submodule.smul_mem _ n ih

/-- Strong simplex-local statement: every invisible distribution is already
a sum of local cubes whose difference labels are all elementary. -/
theorem physicalInvariantDistributions_le_elementaryPhysicalNonfaceCubeSpan
    (A : FacetwisePrimitiveSectionData L)
    (hprimitive : ∀ σ : Facet,
      L.primitiveRes σ = coordinateRestriction (facets σ)) :
    L.physicalInvariantDistributions ≤
      elementaryPhysicalNonfaceCubeSpan facets d := by
  intro z hz
  let u : RedDist (Configuration ι G) := distributionLift L A z
  have huLocal : u ∈
      reducedCoordinateCommonRestrictionKernel (G := G) facets := by
    rw [reducedCoordinateCommonRestrictionKernel, Submodule.mem_iInf]
    intro σ
    rw [LinearMap.mem_ker]
    rw [← hprimitive σ]
    exact LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun τ : Facet =>
        LinearMap.ker (L.restrictRedDist τ))).1
          (distributionLift_mem_locallyZeroRedDist L A hz) σ)
  have huImage : mapRedDist d u ∈
      elementaryPhysicalNonfaceCubeSpan facets d :=
    map_reducedCoordinateCommonRestrictionKernel_le_elementarySpan
      facets (d := d) ⟨u, huLocal, rfl⟩
  rwa [mapRedDist_distributionLift L A z] at huImage

/-- Every locally invisible physical distribution is already a locality
identity whenever the carrier family admits compatible primitive sections.
-/
theorem physicalInvariantDistributions_le_physicalNonfaceCubeSpan
    (A : FacetwisePrimitiveSectionData L)
    (hprimitive : ∀ σ : Facet,
      L.primitiveRes σ = coordinateRestriction (facets σ)) :
    L.physicalInvariantDistributions ≤
      physicalNonfaceCubeSpan facets d := by
  exact
    (physicalInvariantDistributions_le_elementaryPhysicalNonfaceCubeSpan
      facets L A hprimitive).trans
        (elementaryPhysicalNonfaceCubeSpan_le_physicalNonfaceCubeSpan
          facets (d := d))

/-- For such a carrier family, the numerator and denominator defining
`tau` coincide. -/
theorem physicalInvariantDistributions_eq_physicalNonfaceCubeSpan
    (A : FacetwisePrimitiveSectionData L)
    (hprimitive : ∀ σ : Facet,
      L.primitiveRes σ = coordinateRestriction (facets σ)) :
    L.physicalInvariantDistributions =
      physicalNonfaceCubeSpan facets d := by
  apply le_antisymm
  · exact physicalInvariantDistributions_le_physicalNonfaceCubeSpan
      facets L A hprimitive
  · exact L.physicalNonfaceCubeSpan_le_physicalInvariantDistributions
      facets hprimitive

/-- The denominator, regarded inside the numerator, is the whole numerator.
-/
theorem physicalNonfaceCubeSpanInInvariantDistributions_eq_top
    (A : FacetwisePrimitiveSectionData L)
    (hprimitive : ∀ σ : Facet,
      L.primitiveRes σ = coordinateRestriction (facets σ)) :
    FacetRestrictionData.physicalNonfaceCubeSpanInInvariantDistributions
      facets L = ⊤ := by
  apply le_antisymm le_top
  intro z _
  change (z : RedDist B) ∈ physicalNonfaceCubeSpan facets d
  exact physicalInvariantDistributions_le_physicalNonfaceCubeSpan
    facets L A hprimitive z.property

/-- Simplex-local `tau` is trivial: every class is zero. -/
theorem tau_eq_zero
    (A : FacetwisePrimitiveSectionData L)
    (hprimitive : ∀ σ : Facet,
      L.primitiveRes σ = coordinateRestriction (facets σ))
    (x : FacetRestrictionData.Tau facets L) :
    x = 0 := by
  refine Submodule.Quotient.induction_on
    (p := FacetRestrictionData.physicalNonfaceCubeSpanInInvariantDistributions
      facets L) x ?_
  intro z
  apply (Submodule.Quotient.mk_eq_zero
    (FacetRestrictionData.physicalNonfaceCubeSpanInInvariantDistributions
      facets L)).2
  rw [physicalNonfaceCubeSpanInInvariantDistributions_eq_top
    facets L A hprimitive]
  simp

/-- Typeclass form of the same local vanishing statement. -/
theorem tau_subsingleton
    (A : FacetwisePrimitiveSectionData L)
    (hprimitive : ∀ σ : Facet,
      L.primitiveRes σ = coordinateRestriction (facets σ)) :
    Subsingleton (FacetRestrictionData.Tau facets L) :=
  ⟨fun x y => (tau_eq_zero facets L A hprimitive x).trans
    (tau_eq_zero facets L A hprimitive y).symm⟩

end CoordinateCarrier

end GeneralSphereT.PathAlgebra
