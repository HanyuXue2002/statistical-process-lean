import Formalization.OperatorCoefficients
import Formalization.PrimitiveQuotient

set_option linter.style.header false

/-!
# Local vanishing of fixed elementary-label coefficients

When an elementary path is grouped by its complete oriented label
`single i g`, local vanishing of the path implies local vanishing of that
label's base-coefficient distribution on every facet containing `i`.

The proof uses the verified singleton-fiber theorem for elementary labels.
Coordinate restriction is not globally injective, and no such claim is made.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uI uG uB uBA

variable {ι : Type uI} {G : Type uG}
variable [LinearOrder ι] [AddCommGroup G]

omit [LinearOrder ι] in
/-- A one-coordinate configuration is nonzero when its coefficient is. -/
theorem singleConfiguration_ne_zero (i : ι) {g : G} (hg : g ≠ 0) :
    Finsupp.single i g ≠ (0 : Configuration ι G) := by
  intro hz
  apply hg
  simpa using congrArg (fun c : Configuration ι G => c i) hz

/--
Distributions vanishing after restriction to every facet that contains `i`.
Facets not containing `i` are intentionally absent: they do not see the
chosen elementary label in the first place.
-/
def coordinateSupportRestrictionKernel {Facet : Type uF}
    (facets : Facet → Set ι) (i : ι) :
    Submodule ℤ (Dist (Configuration ι G)) :=
  ⨅ ρ : { ρ : Facet // i ∈ facets ρ },
    LinearMap.ker
      (mapDist (coordinateRestriction (facets ρ.1)))

section PrimitivePaths

variable {Facet : Type uF} (facets : Facet → Set ι)
variable {d : Configuration ι G →+ Configuration ι G}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := fun ρ => Configuration (facets ρ) G)
  (Facet := Facet) d)

/--
Facetwise coefficient vanishing for primitive paths.  Once `i` survives on
`ρ`, the singleton-fiber calculation identifies the coefficient after path
restriction with the pushed-forward original coefficient.
-/
theorem mapDist_pathCoefficient_eq_zero_of_locallyZeroPrimitivePath
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {p : Path (Configuration ι G) (Configuration ι G)}
    (helem : p ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G))
    (hlocal : p ∈ L.locallyZeroPrimitivePath)
    (i : ι) (g : G) (hg : g ≠ 0)
    (ρ : Facet) (hiρ : i ∈ facets ρ) :
    mapDist (coordinateRestriction (facets ρ))
        (pathCoefficient (Finsupp.single i g)
          (singleConfiguration_ne_zero i hg) p) = 0 := by
  have hpρ : L.restrictPrimitivePath ρ p = 0 :=
    (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker (L.restrictPrimitivePath σ))).1 hlocal ρ
  change
    mapPath (L.primitiveRes ρ) (L.primitiveRes ρ) p = 0 at hpρ
  rw [hprimitive ρ] at hpρ
  have hcoefficient :=
    pathCoefficient_coordinateRestriction_elementary
      (facets ρ) i hiρ g hg
        (coordinateRestriction (facets ρ)) helem
  simpa [hpρ] using hcoefficient.symm

/--
The fixed primitive coefficient distribution lies in the intersection of all
restriction kernels over facets that contain its active coordinate.
-/
theorem pathCoefficient_mem_coordinateSupportRestrictionKernel_of_locallyZeroPrimitivePath
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {p : Path (Configuration ι G) (Configuration ι G)}
    (helem : p ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G))
    (hlocal : p ∈ L.locallyZeroPrimitivePath)
    (i : ι) (g : G) (hg : g ≠ 0) :
    pathCoefficient (Finsupp.single i g)
        (singleConfiguration_ne_zero i hg) p ∈
      coordinateSupportRestrictionKernel (G := G) facets i := by
  rw [coordinateSupportRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  change
    mapDist (coordinateRestriction (facets ρ.1))
        (pathCoefficient (Finsupp.single i g)
          (singleConfiguration_ne_zero i hg) p) = 0
  exact mapDist_pathCoefficient_eq_zero_of_locallyZeroPrimitivePath
    facets L hprimitive helem hlocal i g hg ρ.1 ρ.2

end PrimitivePaths

section PhysicalPaths

variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/--
For physical paths, coefficient bases are pushed forward by the facet's
physical base map.  Only the increment map needs to be literal coordinate
restriction in order to invoke the elementary singleton-fiber theorem.
-/
theorem mapDist_pathCoefficient_eq_zero_of_locallyZeroPhysicalPath
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {p : Path (Configuration ι G) B}
    (helem : p ∈ elementaryPaths (ι := ι) (G := G) (X := B))
    (hlocal : p ∈ L.locallyZeroPhysicalPath)
    (i : ι) (g : G) (hg : g ≠ 0)
    (ρ : Facet) (hiρ : i ∈ facets ρ) :
    mapDist (L.physicalRes ρ)
        (pathCoefficient (Finsupp.single i g)
          (singleConfiguration_ne_zero i hg) p) = 0 := by
  have hpρ : L.restrictPhysicalPath ρ p = 0 :=
    (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker (L.restrictPhysicalPath σ))).1 hlocal ρ
  change mapPath (L.primitiveRes ρ) (L.physicalRes ρ) p = 0 at hpρ
  rw [hprimitive ρ] at hpρ
  have hcoefficient :=
    pathCoefficient_coordinateRestriction_elementary
      (facets ρ) i hiρ g hg (L.physicalRes ρ) helem
  simpa [hpρ] using hcoefficient.symm

/-- Kernel intersection for physical base-coefficient distributions. -/
def physicalCoordinateSupportRestrictionKernel (i : ι) :
    Submodule ℤ (Dist B) :=
  ⨅ ρ : { ρ : Facet // i ∈ facets ρ },
    LinearMap.ker (mapDist (L.physicalRes ρ.1))

/--
The fixed physical coefficient distribution lies in every visible-facet
kernel.
-/
theorem pathCoefficient_mem_physicalCoordinateSupportRestrictionKernel_of_locallyZero
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {p : Path (Configuration ι G) B}
    (helem : p ∈ elementaryPaths (ι := ι) (G := G) (X := B))
    (hlocal : p ∈ L.locallyZeroPhysicalPath)
    (i : ι) (g : G) (hg : g ≠ 0) :
    pathCoefficient (Finsupp.single i g)
        (singleConfiguration_ne_zero i hg) p ∈
      physicalCoordinateSupportRestrictionKernel facets L i := by
  rw [physicalCoordinateSupportRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  change
    mapDist (L.physicalRes ρ.1)
        (pathCoefficient (Finsupp.single i g)
          (singleConfiguration_ne_zero i hg) p) = 0
  exact mapDist_pathCoefficient_eq_zero_of_locallyZeroPhysicalPath
    facets L hprimitive helem hlocal i g hg ρ.1 ρ.2

end PhysicalPaths

end GeneralSphereT.PathAlgebra
