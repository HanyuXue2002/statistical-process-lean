import Formalization.ClosedPrimitiveImage
import Formalization.CoordinatePathLocality
import Formalization.SubdivisionNaturality

set_option linter.style.header false

/-!
# The forward comparison map from the primitive quotient

For a primitive cycle `s`, the canonical ordered path `p_*(s)` is elementary.
After applying `d_*`, its physical boundary is `d_*s = 0`, and coordinate
naturality makes it locally zero.  This gives the linear numerator map

`Zprim L → physicalInvariantPaths L,  s ↦ d_* p_*(s)`.

To descend through the primitive denominator, write a primitive boundary as
`s = ∂W`.  The elementary closed word

`p_*(s) - subdivision(W)`

has the same physical image as `p_*(s)`: subdivision preserves boundary,
local vanishing, and the equation `d_*W = 0`.  The hard inclusion already
proved in `ClosedPrimitiveImage` therefore puts this image in `E_id`.  This
constructs the forward quotient map without any choice.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

open FacetRestrictionData

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

section NumeratorMap

variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- The unbundled formula `s ↦ d_* p_*(s)` on all reduced distributions. -/
def canonicalPhysicalPath :
    RedDist (Configuration ι G) →ₗ[ℤ] Path (Configuration ι G) B :=
  (mapDPath d).comp (canonicalPath (ι := ι) (G := G))

/-- The reduced physical boundary of `d_*p_*(s)` is exactly `d_*s`. -/
theorem configurationReducedBoundary_canonicalPhysicalPath
    (s : RedDist (Configuration ι G)) :
    configurationReducedBoundary d (canonicalPhysicalPath (d := d) s) =
      mapRedDist d s := by
  calc
    configurationReducedBoundary d
        (mapDPath d (canonicalPath (ι := ι) (G := G) s)) =
      mapRedDist d
        (primitiveReducedBoundary (Configuration ι G)
          (canonicalPath (ι := ι) (G := G) s)) := by
        exact (LinearMap.congr_fun
          (mapRedDist_primitiveReducedBoundary d)
          (canonicalPath (ι := ι) (G := G) s)).symm
    _ = mapRedDist d s := by
      have hcanonical :=
        LinearMap.congr_fun primitiveReducedBoundary_canonicalPath s
      change primitiveReducedBoundary (Configuration ι G)
        (canonicalPath (ι := ι) (G := G) s) = s at hcanonical
      rw [hcanonical]

/-- The canonical physical path of every `Zprim` element lies in `E_inv`. -/
theorem canonicalPhysicalPath_mem_physicalInvariantPaths
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (s : Zprim L) :
    canonicalPhysicalPath (d := d) (s : RedDist (Configuration ι G)) ∈
      physicalInvariantPaths L := by
  refine ⟨?_, ?_, ?_⟩
  · exact mapDPath_elementary_mem d
      (canonicalPath_mem (s : RedDist (Configuration ι G)))
  · change configurationReducedBoundary d
      (canonicalPhysicalPath (d := d)
        (s : RedDist (Configuration ι G))) = 0
    rw [configurationReducedBoundary_canonicalPhysicalPath]
    exact LinearMap.mem_ker.mp s.property.1
  · apply L.mapDPath_mem_locallyZeroPhysicalPath
    exact canonicalPath_mem_locallyZeroPrimitivePath
      facets L hprimitive s.property.2

/--
The forward comparison map on numerators, with membership in `E_inv` carried
in its codomain.
-/
def primitiveToPhysicalInvariant
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ)) :
    Zprim L →ₗ[ℤ] physicalInvariantPaths L :=
  LinearMap.codRestrict (physicalInvariantPaths L)
    ((canonicalPhysicalPath (d := d)).comp (Zprim L).subtype)
    (canonicalPhysicalPath_mem_physicalInvariantPaths facets L hprimitive)

@[simp]
theorem primitiveToPhysicalInvariant_coe
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (s : Zprim L) :
    ((primitiveToPhysicalInvariant facets L hprimitive s :
        physicalInvariantPaths L) : Path (Configuration ι G) B) =
      mapDPath d
        (canonicalPath (ι := ι) (G := G)
          (s : RedDist (Configuration ι G))) :=
  rfl

end NumeratorMap

section DenominatorCompatibility

variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- Subdivision of a relation path still has zero physical image. -/
theorem mapDPath_subdivision_eq_zero_of_eq_zero
    {W : Path (Configuration ι G) (Configuration ι G)}
    (hW : mapDPath d W = 0) :
    mapDPath d (subdivision W) = 0 := by
  calc
    mapDPath d (subdivision W) = subdivisionAlong d (mapDPath d W) :=
      LinearMap.congr_fun (mapDPath_subdivision d) W
    _ = 0 := by simp [hW]

/--
The primitive boundary denominator maps into the physical identity denominator.
This is the precise compatibility needed by `Submodule.mapQ`.
-/
theorem BprimInZprim_le_comap_primitiveToPhysicalInvariant
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    BprimInZprim L ≤
      (physicalIdentityPathsInInvariantPaths L).comap
        (primitiveToPhysicalInvariant facets L hprimitive) := by
  intro s hs
  change (s : RedDist (Configuration ι G)) ∈ Bprim L at hs
  rw [Bprim] at hs
  rcases hs with ⟨W, hWrelation, hboundary⟩
  have hW : W ∈
      LinearMap.ker (mapDPath d) ⊓ L.locallyZeroPrimitivePath := by
    rw [← relationPaths_eq L]
    exact hWrelation
  have hmapW : mapDPath d W = 0 := LinearMap.mem_ker.mp hW.1
  let V : Path (Configuration ι G) (Configuration ι G) :=
    canonicalPath (ι := ι) (G := G)
        (s : RedDist (Configuration ι G)) - subdivision W
  have hVelem : V ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G) := by
    apply (elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G)).sub_mem
    · exact canonicalPath_mem (s : RedDist (Configuration ι G))
    · exact subdivision_mem W
  have hVclosed :
      primitiveReducedBoundary (Configuration ι G) V = 0 := by
    change primitiveReducedBoundary (Configuration ι G)
      (canonicalPath (ι := ι) (G := G)
          (s : RedDist (Configuration ι G)) - subdivision W) = 0
    rw [map_sub]
    have hcanonical := LinearMap.congr_fun
      primitiveReducedBoundary_canonicalPath
        (s : RedDist (Configuration ι G))
    change primitiveReducedBoundary (Configuration ι G)
      (canonicalPath (ι := ι) (G := G)
        (s : RedDist (Configuration ι G))) =
          (s : RedDist (Configuration ι G)) at hcanonical
    rw [hcanonical, primitiveReducedBoundary_subdivision_apply, hboundary]
    exact sub_self _
  have hVlocal : V ∈ L.locallyZeroPrimitivePath := by
    apply L.locallyZeroPrimitivePath.sub_mem
    · exact canonicalPath_mem_locallyZeroPrimitivePath
        facets L hprimitive s.property.2
    · exact subdivision_mem_locallyZeroPrimitivePath
        facets L hprimitive hW.2
  have hmapSubdivision : mapDPath d (subdivision W) = 0 :=
    mapDPath_subdivision_eq_zero_of_eq_zero (d := d) hmapW
  have hmapV :
      mapDPath d V = mapDPath d
        (canonicalPath (ι := ι) (G := G)
          (s : RedDist (Configuration ι G))) := by
    simp [V, hmapSubdivision]
  have hidentity : mapDPath d V ∈ physicalIdentityPaths L :=
    mapDPath_mem_physicalIdentityPaths_of_closed_elementary_locallyZero
      facets L hprimitive hcover hVelem hVclosed hVlocal
  change
    (((primitiveToPhysicalInvariant facets L hprimitive s :
        physicalInvariantPaths L) : Path (Configuration ι G) B)) ∈
      physicalIdentityPaths L
  rw [primitiveToPhysicalInvariant_coe]
  rw [← hmapV]
  exact hidentity

/--
The forward comparison map on the strict quotients.  Its well-definedness is
exactly the preceding denominator-to-comap inclusion.
-/
def primitiveToPhysicalQuotient
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    TPrime L →ₗ[ℤ] PhysicalQuotient L :=
  (BprimInZprim L).mapQ
    (physicalIdentityPathsInInvariantPaths L)
    (primitiveToPhysicalInvariant facets L hprimitive)
    (BprimInZprim_le_comap_primitiveToPhysicalInvariant
      facets L hprimitive hcover)

/-- Representative computation for the forward quotient comparison map. -/
@[simp]
theorem primitiveToPhysicalQuotient_mkQ
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (s : Zprim L) :
    primitiveToPhysicalQuotient facets L hprimitive hcover
        ((BprimInZprim L).mkQ s) =
      (physicalIdentityPathsInInvariantPaths L).mkQ
        (primitiveToPhysicalInvariant facets L hprimitive s) := by
  simpa only [primitiveToPhysicalQuotient, Submodule.mkQ_apply] using
    (Submodule.mapQ_apply
      (p := BprimInZprim L)
      (q := physicalIdentityPathsInInvariantPaths L)
      (primitiveToPhysicalInvariant facets L hprimitive) s)

end DenominatorCompatibility

end GeneralSphereT.PathAlgebra
