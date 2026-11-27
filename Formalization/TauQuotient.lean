import Formalization.PrimitiveQuotient
import Formalization.ZeroIdentityImage

set_option linter.style.header false

/-!
# The physical distribution quotient `Tau`

This module packages the distribution-level numerator and denominator from
Section 2.  The numerator `D_inv` consists of reduced physical distributions
which vanish after restriction to every facet.  The already constructed span
of physical nonface cubes is `D_id`; its inclusion in `D_inv` follows directly
from the commuting restriction square.  Their typed quotient is `Tau`.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

namespace FacetRestrictionData

section PhysicalDistributionNumerator

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : C →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- Restriction of reduced physical distributions to one facet. -/
def restrictPhysicalRedDist (ρ : Facet) :
    RedDist B →ₗ[ℤ] RedDist (BAt ρ) :=
  mapRedDist (L.physicalRes ρ)

/-- The physical distribution numerator `D_inv`: reduced distributions which
vanish after restriction to every facet. -/
def physicalInvariantDistributions : Submodule ℤ (RedDist B) :=
  ⨅ ρ : Facet, LinearMap.ker (restrictPhysicalRedDist L ρ)

/-- Reduced-distribution pushforward commutes with facet restriction. -/
theorem restrictPhysicalRedDist_mapRedDist (ρ : Facet) :
    (restrictPhysicalRedDist L ρ).comp (mapRedDist d) =
      (mapRedDist (L.localD ρ)).comp (L.restrictRedDist ρ) := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  change mapDist (L.physicalRes ρ) (mapDist d u.1) =
    mapDist (L.localD ρ) (mapDist (L.primitiveRes ρ) u.1)
  have hmaps :
      (mapDist (L.physicalRes ρ)).comp (mapDist d) =
        (mapDist (L.localD ρ)).comp (mapDist (L.primitiveRes ρ)) := by
    apply LinearMap.ext
    intro v
    induction v using Finsupp.induction with
    | zero => simp
    | single_add c n v _ _ ih =>
        have hc : L.physicalRes ρ (d c) =
            L.localD ρ (L.primitiveRes ρ c) := by
          exact DFunLike.congr_fun (L.commutes ρ) c
        change mapDist (L.physicalRes ρ) (mapDist d v) =
          mapDist (L.localD ρ) (mapDist (L.primitiveRes ρ) v) at ih
        simp [hc, ih]
  exact LinearMap.congr_fun hmaps u.1

/-- The image of a facetwise-zero primitive reduced distribution is a
facetwise-zero physical reduced distribution. -/
theorem mapRedDist_mem_physicalInvariantDistributions
    {u : RedDist C} (hu : u ∈ L.locallyZeroRedDist) :
    mapRedDist d u ∈ physicalInvariantDistributions L := by
  rw [physicalInvariantDistributions, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have huρ : L.restrictRedDist ρ u = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker (L.restrictRedDist σ))).1 hu ρ)
  calc
    restrictPhysicalRedDist L ρ (mapRedDist d u) =
        mapRedDist (L.localD ρ) (L.restrictRedDist ρ u) :=
      LinearMap.congr_fun (restrictPhysicalRedDist_mapRedDist L ρ) u
    _ = 0 := by simp [huρ]

end PhysicalDistributionNumerator

section Tau

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uC} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

omit [LinearOrder ι] in
/-- Every physical nonface-cube generator vanishes after every physical
facet restriction. -/
theorem physicalNonfaceCubeGenerators_subset_physicalInvariantDistributions
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ)) :
    physicalNonfaceCubeGenerators facets d ⊆
      (physicalInvariantDistributions L : Set (RedDist B)) := by
  rintro u ⟨rs, hrs, a, hcover, rfl⟩
  change physicalNonfaceCube d rs hrs a ∈ physicalInvariantDistributions L
  rw [physicalInvariantDistributions, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change mapDist (L.physicalRes ρ)
      (iteratedDistributionDifference (rs.map d)
        (Finsupp.single a 1)) = 0
  rw [mapDist_iteratedDistributionDifference_apply]
  obtain ⟨r, hr, hρ⟩ := hcover ρ
  have hphysical : L.physicalRes ρ (d r) = 0 := by
    have hcomm : L.physicalRes ρ (d r) =
        L.localD ρ (L.primitiveRes ρ r) :=
      DFunLike.congr_fun (L.commutes ρ) r
    rw [hprimitive ρ, hρ, map_zero] at hcomm
    exact hcomm
  apply iteratedDistributionDifference_eq_zero_of_zero_mem
  exact List.mem_map.mpr
    ⟨d r, List.mem_map.mpr ⟨r, hr, rfl⟩, hphysical⟩

omit [LinearOrder ι] in
/-- The distribution identity denominator `D_id` is contained in the
physical locally-zero numerator `D_inv`. -/
theorem physicalNonfaceCubeSpan_le_physicalInvariantDistributions
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ)) :
    physicalNonfaceCubeSpan facets d ≤ physicalInvariantDistributions L := by
  rw [physicalNonfaceCubeSpan, Submodule.span_le]
  exact
    physicalNonfaceCubeGenerators_subset_physicalInvariantDistributions
      facets L hprimitive

/-- The physical identity denominator regarded inside `D_inv`. -/
def physicalNonfaceCubeSpanInInvariantDistributions :
    Submodule ℤ (physicalInvariantDistributions L) :=
  Submodule.comap (physicalInvariantDistributions L).subtype
    (physicalNonfaceCubeSpan facets d)

/-- The literal distribution quotient `tau = D_inv / D_id`. -/
abbrev Tau :=
  physicalInvariantDistributions L ⧸
    physicalNonfaceCubeSpanInInvariantDistributions facets L

end Tau

end FacetRestrictionData

end GeneralSphereT.PathAlgebra
