import Formalization.ExplicitFillingNaturality
import Formalization.ElementaryPaths
import Formalization.Subdivision
import Formalization.CellTypeLocalZero

set_option linter.style.header false

/-!
# A linear explicit filling map on elementary paths

The one-edge filling is extended linearly without making a choice of a span
presentation.  On a raw edge `(r,c)` we use the explicit filling precisely
when `r` has singleton support.  This rule kills the zero-increment generators and
hence descends to the path quotient.  Its restriction to the elementary path
submodule has the expected boundary and strict coordinate naturality.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- Filling assigned to one raw increment/base pair.  Singleton support makes
the active coordinate canonical, so no choice of an elementary presentation
is involved. -/
def elementaryIncrementCellFilling (r c : Config ι G) :
    PrimitiveCellChain₂ ι G :=
  if r.support.card = 1 then
    ∑ i ∈ r.support, explicitOrderedCellFilling c i (r i)
  else 0

@[simp]
theorem elementaryIncrementCellFilling_zero (c : Config ι G) :
    elementaryIncrementCellFilling 0 c = 0 := by
  simp [elementaryIncrementCellFilling]

@[simp]
theorem elementaryIncrementCellFilling_single (i : ι) {g : G}
    (hg : g ≠ 0) (c : Config ι G) :
    elementaryIncrementCellFilling (Finsupp.single i g) c =
      explicitOrderedCellFilling c i g := by
  classical
  simp [elementaryIncrementCellFilling, hg]

/-- Linear extension of the singleton-support rule to raw paths. -/
def rawExplicitFillingMap :
    RawPath (Config ι G) (Config ι G) →ₗ[ℤ] PrimitiveCellChain₂ ι G :=
  Finsupp.linearCombination ℤ fun p =>
    elementaryIncrementCellFilling p.1 p.2

@[simp]
theorem rawExplicitFillingMap_rawEdge (r c : Config ι G) :
    rawExplicitFillingMap (rawEdge r c) =
      elementaryIncrementCellFilling r c := by
  simp [rawExplicitFillingMap, rawEdge]

/-- The raw filling kills precisely the zero-increment relations needed for
the path quotient. -/
theorem zeroIncrement_le_rawExplicitFillingMap_ker :
    zeroIncrement (Config ι G) (Config ι G) ≤
      LinearMap.ker (rawExplicitFillingMap (ι := ι) (G := G)) := by
  rw [zeroIncrement, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  change rawExplicitFillingMap (rawEdge 0 c) = 0
  simp

/-- The honest linear filling map on the path quotient.  Its behavior away
from the elementary subgroup is auxiliary; all specifications below are on
elementary paths. -/
def explicitFillingMap :
    Path (Config ι G) (Config ι G) →ₗ[ℤ] PrimitiveCellChain₂ ι G :=
  (zeroIncrement (Config ι G) (Config ι G)).liftQ
    rawExplicitFillingMap zeroIncrement_le_rawExplicitFillingMap_ker

@[simp]
theorem explicitFillingMap_edge (r c : Config ι G) :
    explicitFillingMap (edge r c) = elementaryIncrementCellFilling r c := by
  simp [explicitFillingMap, edge]

/-- Required generator formula: the linear map extends the explicit one-edge
filling literally. -/
@[simp]
theorem explicitFillingMap_elementaryEdge (i : ι) {g : G}
    (hg : g ≠ 0) (c : Config ι G) :
    explicitFillingMap (edge (Finsupp.single i g) c) =
      explicitOrderedCellFilling c i g := by
  simp [hg]

/-- The same map with its elementary domain recorded in the type. -/
def explicitElementaryFillingMap :
    elementaryPaths (ι := ι) (G := G) (X := Config ι G) →ₗ[ℤ]
      PrimitiveCellChain₂ ι G :=
  (explicitFillingMap (ι := ι) (G := G)).comp
    (elementaryPaths (ι := ι) (G := G) (X := Config ι G)).subtype

@[simp]
theorem explicitElementaryFillingMap_coe
    (p : elementaryPaths (ι := ι) (G := G) (X := Config ι G)) :
    explicitElementaryFillingMap p = explicitFillingMap (p : Path _ _) :=
  rfl

/-- Boundary specification on the elementary span. -/
theorem primitiveCellBoundary₂_explicitFillingMap_of_mem
    {p : Path (Config ι G) (Config ι G)}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := Config ι G)) :
    primitiveCellBoundary₂ (explicitFillingMap p) =
      p - canonicalPath
        (primitiveReducedBoundary (Config ι G) p) := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (c : Config ι G),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) c} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, c, hg, rfl⟩
      rw [explicitFillingMap_elementaryEdge i hg c]
      rw [primitiveCellBoundary₂_explicitOrderedCellFilling_eq_loop]
      simp only [reducedBoundary_edge, AddMonoidHom.id_apply, map_sub,
        canonicalPath_redBracket]
      abel
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [map_add, ihp, ihq]
      abel
  | smul n p hp ih =>
      simp only [map_smul, ih, smul_sub]

/-- Typed elementary-submodule version of the boundary specification. -/
theorem primitiveCellBoundary₂_explicitElementaryFillingMap
    (p : elementaryPaths (ι := ι) (G := G) (X := Config ι G)) :
    primitiveCellBoundary₂ (explicitElementaryFillingMap p) =
      (p : Path (Config ι G) (Config ι G)) -
        canonicalPath
          (primitiveReducedBoundary (Config ι G)
            (p : Path (Config ι G) (Config ι G))) :=
  primitiveCellBoundary₂_explicitFillingMap_of_mem p.property

/-- Strict coordinate naturality of the linear filling map on every
elementary path. -/
theorem restrictPrimitiveCellChain₂_explicitFillingMap_of_mem
    (S : Set ι) {p : Path (Config ι G) (Config ι G)}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := Config ι G)) :
    restrictPrimitiveCellChain₂ S (explicitFillingMap p) =
      explicitFillingMap
        (mapPath (coordinateRestriction S) (coordinateRestriction S) p) := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (c : Config ι G),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) c} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, c, hg, rfl⟩
      by_cases hi : i ∈ S
      · rw [explicitFillingMap_elementaryEdge i hg c]
        rw [restrictPrimitiveCellChain₂_explicitOrderedCellFilling_mem
          S c hi g]
        rw [mapPath_edge, coordinateRestriction_single_mem S hi]
        rw [explicitFillingMap_elementaryEdge ⟨i, hi⟩ hg
          (coordinateRestriction S c)]
      · rw [explicitFillingMap_elementaryEdge i hg c]
        rw [restrictPrimitiveCellChain₂_explicitOrderedCellFilling_not_mem
          S c hi g]
        rw [mapPath_edge, coordinateRestriction_single_not_mem S hi]
        simp
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq]
  | smul n p hp ih => simp [ih]

/-- Coordinate-locally-zero primitive paths, stated directly as the common
kernel of coordinate-deletion maps. -/
def coordinateLocallyZeroPrimitivePath
    {Facet : Type*} (facets : Facet → Set ι) :
    Submodule ℤ (Path (Config ι G) (Config ι G)) :=
  ⨅ ρ : Facet,
    LinearMap.ker
      (mapPath (coordinateRestriction (facets ρ))
        (coordinateRestriction (facets ρ)))

/-- Naturality transports local vanishing of an elementary path to literal
facetwise vanishing of its explicit two-chain filling. -/
theorem explicitFillingMap_mem_locallyZeroPrimitiveCellChain₂
    {Facet : Type*} (facets : Facet → Set ι)
    {p : Path (Config ι G) (Config ι G)}
    (helem : p ∈ elementaryPaths (ι := ι) (G := G) (X := Config ι G))
    (hlocal : p ∈ coordinateLocallyZeroPrimitivePath (G := G) facets) :
    explicitFillingMap p ∈
      locallyZeroPrimitiveCellChain₂ (G := G) facets := by
  rw [locallyZeroPrimitiveCellChain₂, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  rw [restrictPrimitiveCellChain₂_explicitFillingMap_of_mem
    (facets ρ) helem]
  have hpρ :
      mapPath (coordinateRestriction (facets ρ))
          (coordinateRestriction (facets ρ)) p = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker
          (mapPath (coordinateRestriction (facets σ))
            (coordinateRestriction (facets σ))))).1 hlocal ρ)
  simp [hpρ]

/-- A closed, coordinate-locally-zero elementary path is the boundary of the
canonical explicit filling, and that filling is itself facetwise locally zero. -/
theorem explicitFillingMap_closed_locallyZero_spec
    {Facet : Type*} (facets : Facet → Set ι)
    {p : Path (Config ι G) (Config ι G)}
    (helem : p ∈ elementaryPaths (ι := ι) (G := G) (X := Config ι G))
    (hclosed : primitiveReducedBoundary (Config ι G) p = 0)
    (hlocal : p ∈ coordinateLocallyZeroPrimitivePath (G := G) facets) :
    explicitFillingMap p ∈
        locallyZeroPrimitiveCellChain₂ (G := G) facets ∧
      primitiveCellBoundary₂ (explicitFillingMap p) = p := by
  refine ⟨explicitFillingMap_mem_locallyZeroPrimitiveCellChain₂
    facets helem hlocal, ?_⟩
  simpa [hclosed] using primitiveCellBoundary₂_explicitFillingMap_of_mem helem

end GeneralSphereT.PathAlgebra
