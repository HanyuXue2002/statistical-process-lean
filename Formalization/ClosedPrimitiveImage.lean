import Formalization.ExplicitFillingMap
import Formalization.CellTypeBoundaryDecomposition
import Formalization.TransverseCellImage
import Formalization.TriangleCellImage
import Formalization.PrimitiveIdentityLift

set_option linter.style.header false

/-!
# Closed locally-zero primitive paths map to physical identities

This is the final assembly of the hard inclusion in (2.26).  The explicit
filling of a closed elementary primitive path is a facetwise locally-zero
two-chain.  Its finite complete-type boundary decomposition is then handled
one summand at a time:

* transverse squares use `TransverseCellImage` (with zero coefficients treated
  as genuinely degenerate cells);
* same-coordinate triangles use `TriangleCellImage`.

The only extra global assumption is that every coordinate occurs in a facet;
it is used exactly to supply a visible facet for the triangle argument.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

section ContributionBridges

variable {B : Type uB} [AddCommGroup B]

omit [LinearOrder ι] in
/-- The generic complete-type boundary agrees with the transverse contribution. -/
theorem cellTypeBoundary_transverse
    (i j : ι) (hij : i ≠ j) (g h : G) :
    cellTypeBoundary (.transverseSquare i j hij g h) =
      transverseCellTypePathContribution i j hij g h := by
  apply LinearMap.ext
  intro u
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add c n u _ _ ih =>
      simp only [map_add, ih]
      rw [cellTypeBoundary_single,
        transverseCellTypePathContribution_single]
      rfl

omit [LinearOrder ι] in
/-- The corresponding equality after applying the base-label map `d_*`. -/
theorem mappedCellTypeBoundary_transverse
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g h : G) :
    mappedCellTypeBoundary d (.transverseSquare i j hij g h) =
      physicalTransverseCellTypeContribution d i j hij g h := by
  rw [mappedCellTypeBoundary, physicalTransverseCellTypeContribution,
    cellTypeBoundary_transverse]

/-
The following two lemmas use the anticipated public interface of
`TriangleCellImage`:

* `triangleCellTypePathContribution`;
* `physicalTriangleCellTypeContribution`;
* `triangleCellTypePathContribution_single`.

They become active once that module is imported above.
-/

omit [LinearOrder ι] in
/-- The generic complete-type boundary agrees with the triangle contribution. -/
theorem cellTypeBoundary_triangle
    (i : ι) (g h : G) :
    cellTypeBoundary (.sameCoordinateTriangle i g h) =
      triangleCellTypePathContribution i g h := by
  apply LinearMap.ext
  intro u
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add c n u _ _ ih =>
      simp only [map_add, ih]
      rw [cellTypeBoundary_single, triangleCellTypePathContribution_single]
      rfl

omit [LinearOrder ι] in
/-- Triangle contribution equality after applying `d_*`. -/
theorem mappedCellTypeBoundary_triangle
    (d : Configuration ι G →+ B) (i : ι) (g h : G) :
    mappedCellTypeBoundary d (.sameCoordinateTriangle i g h) =
      physicalTriangleCellTypeContribution d i g h := by
  rw [mappedCellTypeBoundary, physicalTriangleCellTypeContribution,
    cellTypeBoundary_triangle]

omit [LinearOrder ι] in
/-- A transverse type with zero first coefficient contributes the zero path. -/
theorem mappedCellTypeBoundary_transverse_eq_zero_of_left
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (h : G)
    (u : Dist (Configuration ι G)) :
    mappedCellTypeBoundary d (.transverseSquare i j hij 0 h) u = 0 := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add c n u _ _ ih =>
      simp only [map_add, ih, add_zero]
      rw [mappedCellTypeBoundary_single]
      simp [primitiveCellBoundaryGenerator]

omit [LinearOrder ι] in
/-- A transverse type with zero second coefficient contributes the zero path. -/
theorem mappedCellTypeBoundary_transverse_eq_zero_of_right
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g : G)
    (u : Dist (Configuration ι G)) :
    mappedCellTypeBoundary d (.transverseSquare i j hij g 0) u = 0 := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add c n u _ _ ih =>
      simp only [map_add, ih, add_zero]
      rw [mappedCellTypeBoundary_single]
      simp [primitiveCellBoundaryGenerator]

end ContributionBridges

section FinalAssembly

variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

omit [LinearOrder ι] in
/-- Convert `L`'s primitive local-zero condition to literal coordinate deletion. -/
theorem mem_coordinateLocallyZeroPrimitivePath_of_mem_locallyZero
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {W : Path (Configuration ι G) (Configuration ι G)}
    (hlocal : W ∈ L.locallyZeroPrimitivePath) :
    W ∈ coordinateLocallyZeroPrimitivePath (G := G) facets := by
  rw [coordinateLocallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have hρ : L.restrictPrimitivePath ρ W = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker (L.restrictPrimitivePath σ))).1 hlocal ρ)
  change mapPath (L.primitiveRes ρ) (L.primitiveRes ρ) W = 0 at hρ
  simpa [hprimitive ρ] using hρ

/--
Element form of the hard inclusion in (2.26): every elementary, closed,
facetwise locally-zero primitive path maps to the full physical identity
submodule.
-/
theorem mapDPath_mem_physicalIdentityPaths_of_closed_elementary_locallyZero
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    {W : Path (Configuration ι G) (Configuration ι G)}
    (helem : W ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G))
    (hclosed : primitiveReducedBoundary (Configuration ι G) W = 0)
    (hlocal : W ∈ L.locallyZeroPrimitivePath) :
    mapDPath d W ∈ physicalIdentityPaths L := by
  have hcoordinate :
      W ∈ coordinateLocallyZeroPrimitivePath (G := G) facets :=
    mem_coordinateLocallyZeroPrimitivePath_of_mem_locallyZero
      facets L hprimitive hlocal
  let Z : PrimitiveCellChain₂ ι G := explicitFillingMap W
  have hZspec :
      Z ∈ locallyZeroPrimitiveCellChain₂ (G := G) facets ∧
        primitiveCellBoundary₂ Z = W := by
    simpa [Z] using explicitFillingMap_closed_locallyZero_spec
      facets helem hclosed hcoordinate
  rw [← hZspec.2]
  rw [mapDPath_primitiveCellBoundary₂_eq_sum_mappedCellTypeBoundary]
  apply Submodule.sum_mem
  intro τ hτ
  cases τ with
  | transverseSquare i j hij g h =>
      by_cases hg : g = 0
      · subst g
        rw [mappedCellTypeBoundary_transverse_eq_zero_of_left]
        exact (physicalIdentityPaths L).zero_mem
      · by_cases hh : h = 0
        · subst h
          rw [mappedCellTypeBoundary_transverse_eq_zero_of_right]
          exact (physicalIdentityPaths L).zero_mem
        · rw [mappedCellTypeBoundary_transverse]
          apply physicalTransverseCellTypeContribution_mem_physicalIdentityPaths
            facets L hprimitive i j hij g h hg hh
          exact
            transverseCellTypeCoefficient_mem_restrictionKernel_of_locallyZero
              facets hZspec.1 i j hij g h
  | sameCoordinateTriangle i g h =>
      rw [mappedCellTypeBoundary_triangle]
      apply physicalTriangleCellTypeContribution_mem_physicalIdentityPaths
        facets L hprimitive i (hcover i) g h
      exact triangleCellTypeCoefficient_mem_restrictionKernel_of_locallyZero
        facets hZspec.1 i g h

/-- Submodule form of the complete hard inclusion in (2.26). -/
theorem map_closedLocallyZeroElementaryPrimitivePaths_le_physicalIdentityPaths
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    Submodule.map (mapDPath d)
        (closedLocallyZeroElementaryPrimitivePaths L) ≤
      physicalIdentityPaths L := by
  rintro R ⟨W, hW, rfl⟩
  exact mapDPath_mem_physicalIdentityPaths_of_closed_elementary_locallyZero
    facets L hprimitive hcover hW.1 hW.2.1 hW.2.2

end FinalAssembly

end GeneralSphereT.PathAlgebra
