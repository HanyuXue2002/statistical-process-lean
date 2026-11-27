import Formalization.ReducedBoundary

set_option linter.style.header false

/-!
# The strict primitive quotient

This module isolates the algebra in (2.10)--(2.12).  A family of facets comes
with primitive and physical restriction maps, together with local coboundary
maps and their commuting squares.  Local vanishing is literally an infimum of
kernels.  We then construct `Rprim`, `Zprim`, `Bprim`, prove `Bprim ≤ Zprim`,
and form the quotient `TPrime`.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]

/--
Facetwise restriction data for a coboundary map `d : C → B`.

Primitive paths restrict both labels by `primitiveRes`; physical paths use
`primitiveRes` on increments and `physicalRes` on bases.  The last field is
the commuting square required for restriction to commute with `d_*`.
-/
structure FacetRestrictionData (d : C →+ B) where
  primitiveRes : ∀ ρ : Facet, C →+ CAt ρ
  physicalRes : ∀ ρ : Facet, B →+ BAt ρ
  localD : ∀ ρ : Facet, CAt ρ →+ BAt ρ
  commutes : ∀ ρ : Facet,
    (physicalRes ρ).comp d = (localD ρ).comp (primitiveRes ρ)

variable {d : C →+ B}

namespace FacetRestrictionData

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- Restriction of reduced primitive distributions to a facet. -/
def restrictRedDist (ρ : Facet) :
    RedDist C →ₗ[ℤ] RedDist (CAt ρ) :=
  mapRedDist (L.primitiveRes ρ)

/-- Restriction of primitive paths; increment and base use the same map. -/
def restrictPrimitivePath (ρ : Facet) :
    Path C C →ₗ[ℤ] Path (CAt ρ) (CAt ρ) :=
  mapPath (L.primitiveRes ρ) (L.primitiveRes ρ)

/-- Restriction of physical paths; the two labels have different types. -/
def restrictPhysicalPath (ρ : Facet) :
    Path C B →ₗ[ℤ] Path (CAt ρ) (BAt ρ) :=
  mapPath (L.primitiveRes ρ) (L.physicalRes ρ)

/-- `d_*` commutes with facet restriction on paths. -/
theorem restrictPhysicalPath_mapDPath (ρ : Facet) :
    (restrictPhysicalPath L ρ).comp (mapDPath d) =
      (mapDPath (L.localD ρ)).comp (restrictPrimitivePath L ρ) := by
  ext p
  have hp : L.physicalRes ρ (d p.2) =
      L.localD ρ (L.primitiveRes ρ p.2) :=
    DFunLike.congr_fun (L.commutes ρ) p.2
  simp [restrictPhysicalPath, restrictPrimitivePath, mapDPath,
    mapPath, rawMapPath, hp]

/-- Reduced primitive distributions that vanish on every facet. -/
def locallyZeroRedDist : Submodule ℤ (RedDist C) :=
  ⨅ ρ : Facet, LinearMap.ker (restrictRedDist L ρ)

/-- Primitive paths that vanish on every facet. -/
def locallyZeroPrimitivePath : Submodule ℤ (Path C C) :=
  ⨅ ρ : Facet, LinearMap.ker (restrictPrimitivePath L ρ)

/-- Physical paths that vanish on every facet. -/
def locallyZeroPhysicalPath : Submodule ℤ (Path C B) :=
  ⨅ ρ : Facet, LinearMap.ker (restrictPhysicalPath L ρ)

theorem mapDPath_mem_locallyZeroPhysicalPath
    {R : Path C C} (hR : R ∈ locallyZeroPrimitivePath L) :
    mapDPath d R ∈ locallyZeroPhysicalPath L := by
  rw [locallyZeroPhysicalPath]
  rw [Submodule.mem_iInf]
  intro ρ
  change restrictPhysicalPath L ρ (mapDPath d R) = 0
  have hρ : restrictPrimitivePath L ρ R = 0 := by
    exact (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker (restrictPrimitivePath L σ))).1 hR ρ
  calc
    restrictPhysicalPath L ρ (mapDPath d R) =
        mapDPath (L.localD ρ) (restrictPrimitivePath L ρ R) :=
      LinearMap.congr_fun (restrictPhysicalPath_mapDPath L ρ) R
    _ = 0 := by simp [hρ]

/-- Primitive configuration relations: reduced distributions killed by `d_*`. -/
def Rprim : Submodule ℤ (RedDist C) :=
  LinearMap.ker (mapRedDist d)

/-- Primitive cycles: relations which additionally vanish on every facet. -/
def Zprim : Submodule ℤ (RedDist C) :=
  Rprim (d := d) ⊓ locallyZeroRedDist L

/--
Relation paths used in the denominator of `T'`.  The normalization condition is
recorded literally, even though `mapDPath R = 0` already implies it.
-/
def relationPaths : Submodule ℤ (Path C C) :=
  NormalizedPath C C ⊓
    (LinearMap.ker (mapDPath d) ⊓ locallyZeroPrimitivePath L)

/-- The redundant normalization in the paper follows from `d_* R = 0`. -/
theorem ker_mapDPath_le_normalized :
    LinearMap.ker (mapDPath d) ≤ NormalizedPath C C := by
  intro R hR
  exact mapD_eq_zero_mem_primitiveNormalized d R hR

/-- The same relation-path submodule without the redundant normalization. -/
theorem relationPaths_eq :
    relationPaths L =
      LinearMap.ker (mapDPath d) ⊓ locallyZeroPrimitivePath L := by
  apply le_antisymm
  · exact fun _ h => h.2
  · intro R hR
    exact ⟨ker_mapDPath_le_normalized (d := d) hR.1, hR⟩

/-- Primitive boundaries: the image of relation paths under primitive boundary. -/
def Bprim : Submodule ℤ (RedDist C) :=
  Submodule.map (primitiveReducedBoundary C) (relationPaths L)

/-- Primitive boundary commutes with primitive facet restriction. -/
theorem restrictRedDist_primitiveReducedBoundary (ρ : Facet) :
    (restrictRedDist L ρ).comp (primitiveReducedBoundary C) =
      (primitiveReducedBoundary (CAt ρ)).comp
        (restrictPrimitivePath L ρ) := by
  exact reducedBoundary_natural (AddMonoidHom.id C)
    (AddMonoidHom.id (CAt ρ)) (L.primitiveRes ρ)
      (L.primitiveRes ρ) rfl

/-- The type-correct inclusion `Bprim ≤ Zprim` from (2.11). -/
theorem Bprim_le_Zprim : Bprim L ≤ Zprim L := by
  rintro u ⟨R, hR, rfl⟩
  refine ⟨?_, ?_⟩
  · change mapRedDist d (primitiveReducedBoundary C R) = 0
    have hdR : mapDPath d R = 0 := hR.2.1
    calc
      mapRedDist d (primitiveReducedBoundary C R) =
          configurationReducedBoundary d (mapDPath d R) :=
        LinearMap.congr_fun (mapRedDist_primitiveReducedBoundary d) R
      _ = 0 := by simp [hdR]
  · change primitiveReducedBoundary C R ∈ locallyZeroRedDist L
    refine (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker (restrictRedDist L σ))).2 fun ρ => ?_
    change restrictRedDist L ρ (primitiveReducedBoundary C R) = 0
    have hloc : restrictPrimitivePath L ρ R = 0 :=
      (Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker (restrictPrimitivePath L σ))).1 hR.2.2 ρ
    calc
      restrictRedDist L ρ (primitiveReducedBoundary C R) =
          primitiveReducedBoundary (CAt ρ)
            (restrictPrimitivePath L ρ R) :=
        LinearMap.congr_fun
          (restrictRedDist_primitiveReducedBoundary L ρ) R
      _ = 0 := by simp [hloc]

/-- The boundary subgroup regarded as a submodule of the cycle subtype. -/
def BprimInZprim : Submodule ℤ (Zprim L) :=
  Submodule.comap (Zprim L).subtype (Bprim L)

/-- The literal strict primitive quotient `T' = Zprim / Bprim`. -/
abbrev TPrime := Zprim L ⧸ BprimInZprim L

end FacetRestrictionData

end GeneralSphereT.PathAlgebra
