import Formalization.TransverseCellImage
import Formalization.CoordinateLocalityBridge

set_option linter.style.header false

/-!
# The physical image of one same-coordinate triangle type

This is the same-coordinate counterpart of `TransverseCellImage`.  A
coefficient distribution in the restriction kernel for a fixed triangle type
is decomposed in the cube basis.  On each no-facet cube, one active coordinate
transverse to the triangle coordinate is split off; equation (2.32) then turns
the resulting triangle difference into basic physical locality squares.

The argument allows `g = 0`, `h = 0`, or `g + h = 0`.  Only the transverse
coefficient split from the nonzero cube is required to be nonzero.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

section ListAlgebra

omit [LinearOrder ι] in
/-- Iterated base differences depend only on the permutation class of a list. -/
theorem iteratedBaseDifference_eq_of_perm
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    {rs ts : List (Configuration ι G)} (hrs : rs.Perm ts)
    (p : Path (Configuration ι G) B) :
    iteratedBaseDifference d rs p = iteratedBaseDifference d ts p := by
  induction hrs generalizing p with
  | nil => rfl
  | cons r _ ih =>
      simp only [iteratedBaseDifference_cons]
      exact ih (baseDifference (d r) p)
  | swap r s rs =>
      simp only [iteratedBaseDifference_cons]
      rw [baseDifference_commute_apply]
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ p).trans (ih₂ p)

/-- Active coordinates together with their nonzero coefficients. -/
def activeCoordinatePairs (c : Configuration ι G) : List (ι × G) :=
  c.support.toList.map fun i => (i, c i)

/-- Remove one chosen active coordinate/coefficient pair. -/
def remainingActiveCoordinatePairs
    (c : Configuration ι G) (j : ι) : List (ι × G) := by
  classical
  exact (activeCoordinatePairs c).erase (j, c j)

omit [LinearOrder ι] in
/-- Every pair in the active-coordinate list has nonzero coefficient. -/
theorem activeCoordinatePairs_coefficient_ne_zero
    (c : Configuration ι G) {p : ι × G}
    (hp : p ∈ activeCoordinatePairs c) : p.2 ≠ 0 := by
  rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
  exact Finsupp.mem_support_iff.mp (by simpa using hj)

/-- A chosen active pair followed by the remaining pairs permutes the full list. -/
theorem chosen_cons_remainingActiveCoordinatePairs_perm
    (c : Configuration ι G) {j : ι} (hj : j ∈ c.support) :
    ((j, c j) :: remainingActiveCoordinatePairs c j).Perm
      (activeCoordinatePairs c) := by
  classical
  apply (List.perm_cons_erase (l := activeCoordinatePairs c) (a := (j, c j)) ?_).symm
  unfold activeCoordinatePairs
  apply List.mem_map.mpr
  exact ⟨j, by simpa using hj, rfl⟩

/-- The corresponding one-coordinate increment lists are permutations. -/
theorem chosen_cons_remaining_increments_perm
    (c : Configuration ι G) {j : ι} (hj : j ∈ c.support) :
    (Finsupp.single j (c j) ::
        oneCoordinateIncrements (remainingActiveCoordinatePairs c j)).Perm
      (activeCoordinateIncrements c) := by
  have hperm :=
    (chosen_cons_remainingActiveCoordinatePairs_perm c hj).map
      (fun p : ι × G => Finsupp.single p.1 p.2)
  simpa [oneCoordinateIncrements, activeCoordinatePairs,
    activeCoordinateIncrements, List.map_map, Function.comp_def] using hperm

end ListAlgebra

section Contributions

/-- Primitive path contribution of one complete same-coordinate triangle type. -/
def triangleCellTypePathContribution (i : ι) (g h : G) :
    Dist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  Finsupp.linearCombination ℤ fun c =>
    primitiveCellBoundaryGenerator
      (.sameCoordinateTriangle i g h, c)

omit [LinearOrder ι] in
@[simp]
theorem triangleCellTypePathContribution_single
    (i : ι) (g h : G) (c : Configuration ι G) (n : ℤ) :
    triangleCellTypePathContribution i g h (Finsupp.single c n) =
      n • triangle (AddMonoidHom.id (Configuration ι G))
        (Finsupp.single i g) (Finsupp.single i h) c := by
  simp [triangleCellTypePathContribution, primitiveCellBoundaryGenerator]

/-- Apply `d_*` to the fixed primitive triangle-type contribution. -/
def physicalTriangleCellTypeContribution
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (i : ι) (g h : G) :
    Dist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) B :=
  (mapDPath d).comp (triangleCellTypePathContribution i g h)

omit [LinearOrder ι] in
@[simp]
theorem physicalTriangleCellTypeContribution_single
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (i : ι) (g h : G)
    (c : Configuration ι G) (n : ℤ) :
    physicalTriangleCellTypeContribution d i g h (Finsupp.single c n) =
      n • triangle d (Finsupp.single i g) (Finsupp.single i h) (d c) := by
  simp [physicalTriangleCellTypeContribution,
    triangleCellTypePathContribution, primitiveCellBoundaryGenerator,
    triangle]

omit [LinearOrder ι] in
/-- Translating a triangle only translates its base point. -/
theorem baseTranslation_triangle
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (u : B)
    (g h : Configuration ι G) (a : B) :
    baseTranslation u (triangle d g h a) = triangle d g h (a + u) := by
  simp [triangle, add_assoc, add_comm]

omit [LinearOrder ι] in
/-- Translation of coefficient bases becomes physical base translation. -/
theorem physicalTriangleCellTypeContribution_distributionTranslation
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (i : ι) (g h : G)
    (r : Configuration ι G) (u : Dist (Configuration ι G)) :
    physicalTriangleCellTypeContribution d i g h
        (distributionTranslation r u) =
      baseTranslation (d r) (physicalTriangleCellTypeContribution d i g h u) := by
  have hmaps :
      (physicalTriangleCellTypeContribution d i g h).comp
          (distributionTranslation r) =
        (baseTranslation (d r)).comp
          (physicalTriangleCellTypeContribution d i g h) := by
    ext c
    simp [baseTranslation_triangle, map_add, add_comm]
  exact LinearMap.congr_fun hmaps u

omit [LinearOrder ι] in
/-- One coefficient difference becomes one physical base difference. -/
theorem physicalTriangleCellTypeContribution_distributionDifference
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (i : ι) (g h : G)
    (r : Configuration ι G) (u : Dist (Configuration ι G)) :
    physicalTriangleCellTypeContribution d i g h
        (distributionDifference r u) =
      baseDifference (d r) (physicalTriangleCellTypeContribution d i g h u) := by
  rw [distributionDifference, baseDifference]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [physicalTriangleCellTypeContribution_distributionTranslation]

omit [LinearOrder ι] in
/-- Triangle contribution commutes with a complete string of differences. -/
theorem physicalTriangleCellTypeContribution_iteratedDistributionDifference
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (i : ι) (g h : G)
    (rs : List (Configuration ι G))
    (u : Dist (Configuration ι G)) :
    physicalTriangleCellTypeContribution d i g h
        (iteratedDistributionDifference rs u) =
      iteratedBaseDifference d rs
        (physicalTriangleCellTypeContribution d i g h u) := by
  induction rs generalizing u with
  | nil => rfl
  | cons r rs ih =>
      simp only [iteratedDistributionDifference_cons, LinearMap.comp_apply,
        iteratedBaseDifference_cons]
      rw [physicalTriangleCellTypeContribution_distributionDifference]
      rw [ih]
      rw [baseDifference_iteratedBaseDifference_commute]

omit [LinearOrder ι] in
/-- A cube contribution is the corresponding iterated difference of a triangle. -/
theorem physicalTriangleCellTypeContribution_cubeDistribution
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (i : ι) (g h : G)
    (c : Configuration ι G) :
    physicalTriangleCellTypeContribution d i g h (cubeDistribution c) =
      iteratedBaseDifference d (activeCoordinateIncrements c)
        (triangle d (Finsupp.single i g) (Finsupp.single i h) 0) := by
  rw [cubeDistribution_eq_iteratedDistributionDifference]
  rw [physicalTriangleCellTypeContribution_iteratedDistributionDifference]
  simp

/--
Exact factorization after splitting off a chosen active coordinate.  The
remaining differences may stay in their inherited list order.
-/
theorem physicalTriangleCellTypeContribution_cubeDistribution_factorization
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B) (i : ι) (g h : G)
    (c : Configuration ι G) {j : ι} (hj : j ∈ c.support) :
    physicalTriangleCellTypeContribution d i g h (cubeDistribution c) =
      iteratedBaseDifference d
        (oneCoordinateIncrements (remainingActiveCoordinatePairs c j))
        (baseDifference (d (Finsupp.single j (c j)))
          (triangle d (Finsupp.single i g) (Finsupp.single i h) 0)) := by
  rw [physicalTriangleCellTypeContribution_cubeDistribution]
  have hperm := chosen_cons_remaining_increments_perm c hj
  rw [iteratedBaseDifference_eq_of_perm d hperm.symm]
  rfl

end Contributions

section FacetBridge

variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/--
The no-visible-facet condition on a cube gives the common coordinate support
condition needed by the three terms of equation (2.32).
-/
theorem coordinateLocalityFamily_remainingActiveCoordinatePairs
    (i : ι) (c : Configuration ι G)
    (hc : c ∈ noFacetContainsCubeIndices (G := G)
      (fun ρ : { ρ : Facet // i ∈ facets ρ } => facets ρ.1))
    {j : ι} (hj : j ∈ c.support) :
    CoordinateLocalityFamily facets i
      ((j, c j) :: remainingActiveCoordinatePairs c j) := by
  classical
  have hpairperm := chosen_cons_remainingActiveCoordinatePairs_perm c hj
  constructor
  · intro p hp
    apply activeCoordinatePairs_coefficient_ne_zero c
    exact hpairperm.mem_iff.mp hp
  · intro ρ
    by_cases hiρ : i ∈ facets ρ
    · right
      have hcρ := hc ⟨ρ, hiρ⟩
      push Not at hcρ
      obtain ⟨k, hkc, hkρ⟩ := hcρ
      refine ⟨(k, c k), ?_, hkρ⟩
      apply hpairperm.mem_iff.mpr
      unfold activeCoordinatePairs
      apply List.mem_map.mpr
      exact ⟨k, by simpa using hkc, rfl⟩
    · exact Or.inl hiρ

/--
Every no-visible-facet cube contribution of the fixed triangle type is a
physical identity.  The visible-facet witness forces the cube to have an
active coordinate `j ≠ i`, which supplies the transverse difference in
(2.32).
-/
theorem physicalTriangleCellTypeContribution_cubeDistribution_mem
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (i : ι) (hvisible : ∃ ρ : Facet, i ∈ facets ρ)
    (g h : G) (c : Configuration ι G)
    (hc : c ∈ noFacetContainsCubeIndices (G := G)
      (fun ρ : { ρ : Facet // i ∈ facets ρ } => facets ρ.1)) :
    physicalTriangleCellTypeContribution d i g h (cubeDistribution c) ∈
      physicalIdentityPaths L := by
  obtain ⟨ρ0, hiρ0⟩ := hvisible
  have hcρ0 := hc ⟨ρ0, hiρ0⟩
  push Not at hcρ0
  obtain ⟨j, hjc, hjρ0⟩ := hcρ0
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hjρ0 hiρ0
  rw [physicalTriangleCellTypeContribution_cubeDistribution_factorization
    d i g h c hjc]
  exact
    iteratedBaseDifference_sameCoordinateTriangle_mem_physicalIdentityPaths_of_coordinateSupport
      facets L hprimitive i j hij g h (c j)
        (remainingActiveCoordinatePairs c j) 0
        (coordinateLocalityFamily_remainingActiveCoordinatePairs
          facets i c hc hjc)

/--
Same-coordinate part of the reverse inclusion in Lemma (2.26).  The
nonemptiness hypothesis says that the triangle coordinate is seen by at least
one facet; this is automatic for the simplicial facet family in the paper.
-/
theorem physicalTriangleCellTypeContribution_mem_physicalIdentityPaths
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (i : ι) (hvisible : ∃ ρ : Facet, i ∈ facets ρ)
    (g h : G) {u : Dist (Configuration ι G)}
    (hu : u ∈ triangleCellTypeRestrictionKernel (G := G) facets i) :
    physicalTriangleCellTypeContribution d i g h u ∈
      physicalIdentityPaths L := by
  rw [triangleCellTypeRestrictionKernel,
    coordinateCommonRestrictionKernel_eq_noFacetCubeSpan,
    noFacetCubeSpan] at hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨c, hc, rfl⟩
      rw [cubeBasis_apply]
      exact physicalTriangleCellTypeContribution_cubeDistribution_mem
        facets L hprimitive i hvisible g h c hc
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using (physicalIdentityPaths L).add_mem ihx ihy
  | smul n x hx ih =>
      simpa using (physicalIdentityPaths L).smul_mem n ih

end FacetBridge

end GeneralSphereT.PathAlgebra
