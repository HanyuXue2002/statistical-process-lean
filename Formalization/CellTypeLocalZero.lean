import Formalization.PrimitiveCellChains
import Formalization.ReducedLocalKernel

set_option linter.style.header false

/-!
# Local vanishing of complete primitive two-cell types

This module is the degree-two counterpart of `CoefficientLocalZero`.  A fixed
oriented two-cell type is kept visible while coordinate restriction acts only
on its base distribution.  Consequently, facetwise vanishing of an explicit
primitive two-chain forces each complete-type coefficient distribution into
the common restriction kernel over exactly the facets which see that type.

For a transverse square the visible facets contain both tagged coordinates;
for a same-coordinate triangle they contain its single tagged coordinate.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

section RestrictionFormulas

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- The surviving subtype tag of a transverse square. -/
def restrictedTransverseSquareType
    (S : Set ι) (i j : ι) (hij : i ≠ j)
    (hi : i ∈ S) (hj : j ∈ S) (g h : G) :
    PrimitiveCellType S G :=
  .transverseSquare ⟨i, hi⟩ ⟨j, hj⟩
    (fun hsub => hij (congrArg Subtype.val hsub)) g h

/-- The surviving subtype tag of a same-coordinate triangle. -/
def restrictedSameCoordinateTriangleType
    (S : Set ι) (i : ι) (hi : i ∈ S) (g h : G) :
    PrimitiveCellType S G :=
  .sameCoordinateTriangle ⟨i, hi⟩ g h

/-- Generator case of the exact transverse-square coefficient formula. -/
private theorem primitiveCellTypeCoefficient_restrict_transverse_single
    (S : Set ι) (i j : ι) (hij : i ≠ j)
    (hi : i ∈ S) (hj : j ∈ S) (g h : G)
    (cell : PrimitiveCellData ι G) (n : ℤ) :
    primitiveCellTypeCoefficient
        (restrictedTransverseSquareType S i j hij hi hj g h)
        (restrictPrimitiveCellChain₂ S (Finsupp.single cell n)) =
      mapDist (coordinateRestriction S)
        (primitiveCellTypeCoefficient
          (.transverseSquare i j hij g h)
          (Finsupp.single cell n)) := by
  classical
  rcases cell with ⟨σ, c⟩
  cases σ with
  | transverseSquare a b hab u v =>
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
        simp_all [restrictPrimitiveCellChain₂_single,
          restrictPrimitiveCellGenerator, primitiveCellGenerator,
          restrictedTransverseSquareType] <;>
        by_cases hai : a = i <;> by_cases hbj : b = j <;>
        by_cases hug : u = g <;> by_cases hvh : v = h <;>
        simp_all
  | sameCoordinateTriangle a u v =>
      by_cases ha : a ∈ S <;>
        simp_all [restrictPrimitiveCellChain₂_single,
          restrictPrimitiveCellGenerator, primitiveCellGenerator,
          restrictedTransverseSquareType]

/--
Exact coefficient formula for a fixed transverse square type.  Restriction of
the cell chain becomes pushforward of the corresponding base distribution.
-/
theorem primitiveCellTypeCoefficient_restrict_transverse
    (S : Set ι) (i j : ι) (hij : i ≠ j)
    (hi : i ∈ S) (hj : j ∈ S) (g h : G)
    (Z : PrimitiveCellChain₂ ι G) :
    primitiveCellTypeCoefficient
        (restrictedTransverseSquareType S i j hij hi hj g h)
        (restrictPrimitiveCellChain₂ S Z) =
      mapDist (coordinateRestriction S)
        (primitiveCellTypeCoefficient
          (.transverseSquare i j hij g h) Z) := by
  classical
  induction Z using Finsupp.induction with
  | zero => simp
  | single_add cell n Z _ _ ih =>
      simp only [map_add]
      rw [primitiveCellTypeCoefficient_restrict_transverse_single
        S i j hij hi hj g h cell n, ih]

/-- Generator case of the exact same-coordinate-triangle formula. -/
private theorem primitiveCellTypeCoefficient_restrict_triangle_single
    (S : Set ι) (i : ι) (hi : i ∈ S) (g h : G)
    (cell : PrimitiveCellData ι G) (n : ℤ) :
    primitiveCellTypeCoefficient
        (restrictedSameCoordinateTriangleType S i hi g h)
        (restrictPrimitiveCellChain₂ S (Finsupp.single cell n)) =
      mapDist (coordinateRestriction S)
        (primitiveCellTypeCoefficient
          (.sameCoordinateTriangle i g h)
          (Finsupp.single cell n)) := by
  classical
  rcases cell with ⟨σ, c⟩
  cases σ with
  | transverseSquare a b hab u v =>
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
        simp_all [restrictPrimitiveCellChain₂_single,
          restrictPrimitiveCellGenerator, primitiveCellGenerator,
          restrictedSameCoordinateTriangleType]
  | sameCoordinateTriangle a u v =>
      by_cases ha : a ∈ S <;>
        simp_all [restrictPrimitiveCellChain₂_single,
          restrictPrimitiveCellGenerator, primitiveCellGenerator,
          restrictedSameCoordinateTriangleType] <;>
        by_cases hai : a = i <;> by_cases hug : u = g <;>
        by_cases hvh : v = h <;> simp_all

/-- Exact coefficient formula for a fixed same-coordinate triangle type. -/
theorem primitiveCellTypeCoefficient_restrict_triangle
    (S : Set ι) (i : ι) (hi : i ∈ S) (g h : G)
    (Z : PrimitiveCellChain₂ ι G) :
    primitiveCellTypeCoefficient
        (restrictedSameCoordinateTriangleType S i hi g h)
        (restrictPrimitiveCellChain₂ S Z) =
      mapDist (coordinateRestriction S)
        (primitiveCellTypeCoefficient
          (.sameCoordinateTriangle i g h) Z) := by
  classical
  induction Z using Finsupp.induction with
  | zero => simp
  | single_add cell n Z _ _ ih =>
      simp only [map_add]
      rw [primitiveCellTypeCoefficient_restrict_triangle_single
        S i hi g h cell n, ih]

end RestrictionFormulas

section FacetwiseLocalZero

universe uF

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- Primitive two-chains vanishing after restriction to every facet. -/
def locallyZeroPrimitiveCellChain₂
    {Facet : Type uF} (facets : Facet → Set ι) :
    Submodule ℤ (PrimitiveCellChain₂ ι G) :=
  ⨅ ρ : Facet, LinearMap.ker (restrictPrimitiveCellChain₂ (facets ρ))

omit [LinearOrder ι] in
/-- Membership gives literal vanishing on each chosen facet. -/
theorem restrictPrimitiveCellChain₂_eq_zero_of_locallyZero
    {Facet : Type uF} (facets : Facet → Set ι)
    {Z : PrimitiveCellChain₂ ι G}
    (hZ : Z ∈ locallyZeroPrimitiveCellChain₂ (G := G) facets)
    (ρ : Facet) :
    restrictPrimitiveCellChain₂ (facets ρ) Z = 0 := by
  exact LinearMap.mem_ker.mp
    ((Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker (restrictPrimitiveCellChain₂ (facets σ)))).1 hZ ρ)

/--
The coefficient distribution of a fixed square vanishes on every facet that
contains both of its oriented coordinates.
-/
theorem mapDist_transverseCellTypeCoefficient_eq_zero_of_locallyZero
    {Facet : Type uF} (facets : Facet → Set ι)
    {Z : PrimitiveCellChain₂ ι G}
    (hZ : Z ∈ locallyZeroPrimitiveCellChain₂ (G := G) facets)
    (i j : ι) (hij : i ≠ j) (g h : G)
    (ρ : Facet) (hiρ : i ∈ facets ρ) (hjρ : j ∈ facets ρ) :
    mapDist (coordinateRestriction (facets ρ))
        (primitiveCellTypeCoefficient
          (.transverseSquare i j hij g h) Z) = 0 := by
  have hformula := primitiveCellTypeCoefficient_restrict_transverse
    (facets ρ) i j hij hiρ hjρ g h Z
  have hrestriction :=
    restrictPrimitiveCellChain₂_eq_zero_of_locallyZero facets hZ ρ
  simpa [hrestriction] using hformula.symm

/--
The coefficient distribution of a fixed same-coordinate triangle vanishes on
every facet that contains its oriented coordinate.
-/
theorem mapDist_triangleCellTypeCoefficient_eq_zero_of_locallyZero
    {Facet : Type uF} (facets : Facet → Set ι)
    {Z : PrimitiveCellChain₂ ι G}
    (hZ : Z ∈ locallyZeroPrimitiveCellChain₂ (G := G) facets)
    (i : ι) (g h : G)
    (ρ : Facet) (hiρ : i ∈ facets ρ) :
    mapDist (coordinateRestriction (facets ρ))
        (primitiveCellTypeCoefficient
          (.sameCoordinateTriangle i g h) Z) = 0 := by
  have hformula := primitiveCellTypeCoefficient_restrict_triangle
    (facets ρ) i hiρ g h Z
  have hrestriction :=
    restrictPrimitiveCellChain₂_eq_zero_of_locallyZero facets hZ ρ
  simpa [hrestriction] using hformula.symm

/-- Common restriction kernel over facets containing both `i` and `j`. -/
def transverseCellTypeRestrictionKernel
    {Facet : Type uF} (facets : Facet → Set ι) (i j : ι) :
    Submodule ℤ (Dist (Configuration ι G)) :=
  coordinateCommonRestrictionKernel (G := G)
    (fun ρ : { ρ : Facet // i ∈ facets ρ ∧ j ∈ facets ρ } =>
      facets ρ.1)

/-- Common restriction kernel over facets containing `i`. -/
def triangleCellTypeRestrictionKernel
    {Facet : Type uF} (facets : Facet → Set ι) (i : ι) :
    Submodule ℤ (Dist (Configuration ι G)) :=
  coordinateCommonRestrictionKernel (G := G)
    (fun ρ : { ρ : Facet // i ∈ facets ρ } => facets ρ.1)

/--
Collected square coefficients lie in the common kernel over all facets that
see both square coordinates.
-/
theorem transverseCellTypeCoefficient_mem_restrictionKernel_of_locallyZero
    {Facet : Type uF} (facets : Facet → Set ι)
    {Z : PrimitiveCellChain₂ ι G}
    (hZ : Z ∈ locallyZeroPrimitiveCellChain₂ (G := G) facets)
    (i j : ι) (hij : i ≠ j) (g h : G) :
    primitiveCellTypeCoefficient (.transverseSquare i j hij g h) Z ∈
      transverseCellTypeRestrictionKernel (G := G) facets i j := by
  rw [transverseCellTypeRestrictionKernel,
    coordinateCommonRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  exact mapDist_transverseCellTypeCoefficient_eq_zero_of_locallyZero
    facets hZ i j hij g h ρ.1 ρ.2.1 ρ.2.2

/--
Collected same-coordinate triangle coefficients lie in the common kernel over
all facets that see their coordinate.
-/
theorem triangleCellTypeCoefficient_mem_restrictionKernel_of_locallyZero
    {Facet : Type uF} (facets : Facet → Set ι)
    {Z : PrimitiveCellChain₂ ι G}
    (hZ : Z ∈ locallyZeroPrimitiveCellChain₂ (G := G) facets)
    (i : ι) (g h : G) :
    primitiveCellTypeCoefficient (.sameCoordinateTriangle i g h) Z ∈
      triangleCellTypeRestrictionKernel (G := G) facets i := by
  rw [triangleCellTypeRestrictionKernel,
    coordinateCommonRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  exact mapDist_triangleCellTypeCoefficient_eq_zero_of_locallyZero
    facets hZ i g h ρ.1 ρ.2

end FacetwiseLocalZero

end GeneralSphereT.PathAlgebra
