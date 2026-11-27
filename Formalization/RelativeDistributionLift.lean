import Formalization.RelativePrimitiveSection

set_option linter.style.header false

/-!
# The distribution-level relative primitive lift

The relative primitive sections act on generators of a free integral
distribution and therefore extend linearly even though the sections themselves
need not be additive.  This is the precise algebraic content of (2.22)--(2.23).
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

/-- Push a free integral distribution forward along an arbitrary set map. -/
def mapDistFn {X Y : Type*} (f : X → Y) : Dist X →ₗ[ℤ] Dist Y :=
  Finsupp.lmapDomain ℤ ℤ f

@[simp]
theorem mapDistFn_single {X Y : Type*} (f : X → Y) (x : X) (n : ℤ) :
    mapDistFn f (Finsupp.single x n) = Finsupp.single (f x) n := by
  simp [mapDistFn]

theorem augmentation_mapDistFn {X Y : Type*} (f : X → Y) :
    (augmentation Y).comp (mapDistFn f) = augmentation X := by
  ext x
  simp [augmentation, mapDistFn]

/-- Set-map pushforward restricted to augmentation-zero distributions. -/
def mapRedDistFn {X Y : Type*} (f : X → Y) :
    RedDist X →ₗ[ℤ] RedDist Y :=
  LinearMap.codRestrict (RedDist Y)
    ((mapDistFn f).comp (RedDist X).subtype) fun z => by
      rw [LinearMap.mem_ker]
      exact (LinearMap.congr_fun (augmentation_mapDistFn f) z.1).trans z.2

@[simp]
theorem mapRedDistFn_coe {X Y : Type*} (f : X → Y) (z : RedDist X) :
    ((mapRedDistFn f z : RedDist Y) : Dist Y) = mapDistFn f z.1 :=
  rfl

theorem mapDistFn_comp_apply {X Y Z : Type*}
    (f : X → Y) (g : Y → Z) (u : Dist X) :
    mapDistFn g (mapDistFn f u) = mapDistFn (g ∘ f) u := by
  have h : (mapDistFn g).comp (mapDistFn f) = mapDistFn (g ∘ f) := by
    ext x
    simp
  exact LinearMap.congr_fun h u

theorem mapRedDistFn_comp_apply {X Y Z : Type*}
    (f : X → Y) (g : Y → Z) (u : RedDist X) :
    mapRedDistFn g (mapRedDistFn f u) = mapRedDistFn (g ∘ f) u := by
  apply Subtype.ext
  exact mapDistFn_comp_apply f g u.1

theorem mapRedDist_eq_mapRedDistFn
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) :
    mapRedDist f = mapRedDistFn f := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  rfl

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

namespace RelativePrimitiveSectionData

variable (A : RelativePrimitiveSectionData facets L)

/-- The lift in (2.23), obtained by extending the chosen generator lift over
the free augmentation-zero distribution group. -/
def relativeDistributionLift (i : ι) :
    RedDist B →ₗ[ℤ] RedDist (Configuration ι G) :=
  mapRedDistFn (A.globalPrimitive i)

omit [LinearOrder ι] in
/-- The relative distribution lift is a right inverse to physical
pushforward. -/
theorem mapRedDist_relativeDistributionLift (i : ι) (z : RedDist B) :
    mapRedDist d (relativeDistributionLift facets L A i z) = z := by
  rw [mapRedDist_eq_mapRedDistFn]
  rw [relativeDistributionLift, mapRedDistFn_comp_apply]
  apply Subtype.ext
  have hfun : (d : Configuration ι G → B) ∘ A.globalPrimitive i = id := by
    funext a
    exact A.map_globalPrimitive i a
  rw [hfun]
  change mapDistFn id z.1 = z.1
  have hid : mapDistFn (id : B → B) = LinearMap.id := by
    ext a
    simp
  exact LinearMap.congr_fun hid z.1

omit [LinearOrder ι] in
/-- On a facet which sees `i`, restriction of the global lift is the lift of
the restricted distribution by the corresponding local section. -/
theorem restrict_relativeDistributionLift
    (ρ : Facet) (i : ι) (hi : i ∈ facets ρ) (z : RedDist B) :
    mapRedDist (coordinateRestriction (facets ρ))
        (relativeDistributionLift facets L A i z) =
      mapRedDistFn (A.localPrimitive ρ ⟨i, hi⟩)
        (mapRedDist (L.physicalRes ρ) z) := by
  rw [mapRedDist_eq_mapRedDistFn, mapRedDist_eq_mapRedDistFn]
  rw [relativeDistributionLift, mapRedDistFn_comp_apply,
    mapRedDistFn_comp_apply]
  apply Subtype.ext
  have hfun :
      (coordinateRestriction (facets ρ) :
          Configuration ι G → Configuration (facets ρ) G) ∘
          A.globalPrimitive i =
        A.localPrimitive ρ ⟨i, hi⟩ ∘ (L.physicalRes ρ : B → BAt ρ) := by
    funext a
    exact A.restrict_globalPrimitive ρ i hi a
  rw [hfun]

omit [LinearOrder ι] in
/-- Formula (2.22) implies the facetwise vanishing in (2.23). -/
theorem restrict_relativeDistributionLift_eq_zero
    (ρ : Facet) (i : ι) (hi : i ∈ facets ρ) (z : RedDist B)
    (hz : mapRedDist (L.physicalRes ρ) z = 0) :
    mapRedDist (coordinateRestriction (facets ρ))
        (relativeDistributionLift facets L A i z) = 0 := by
  rw [restrict_relativeDistributionLift facets L A ρ i hi z, hz]
  simp

end RelativePrimitiveSectionData

end GeneralSphereT.PathAlgebra
