import Formalization.CellTypeLocalZero
import Formalization.DistributionDifferences
import Formalization.IteratedLocality

set_option linter.style.header false

/-!
# The physical image of one transverse primitive cell type

This module treats the cross-square part of the reverse inclusion in
Lemma (2.26).  A distribution of bases for one complete oriented transverse
cell type is sent linearly to its primitive square contribution and then by
`d_*` to physical paths.  Cube-basis decomposition turns every coefficient
distribution in the appropriate visible-facet kernel into basic physical
locality identities.

No global injectivity statement about coordinate restriction is used.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

section Contributions

/--
The primitive path contribution of the base distribution of one complete
oriented transverse-square type.
-/
def transverseCellTypePathContribution
    (i j : ι) (hij : i ≠ j) (g h : G) :
    Dist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  Finsupp.linearCombination ℤ fun c =>
    primitiveCellBoundaryGenerator
      (.transverseSquare i j hij g h, c)

omit [LinearOrder ι] in
@[simp]
theorem transverseCellTypePathContribution_single
    (i j : ι) (hij : i ≠ j) (g h : G)
    (c : Configuration ι G) (n : ℤ) :
    transverseCellTypePathContribution i j hij g h
        (Finsupp.single c n) =
      n • square (AddMonoidHom.id (Configuration ι G))
        (Finsupp.single i g) (Finsupp.single j h) c := by
  simp [transverseCellTypePathContribution,
    primitiveCellBoundaryGenerator]

/-- Apply the paper's base-label map `d_*` to that primitive contribution. -/
def physicalTransverseCellTypeContribution
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g h : G) :
    Dist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) B :=
  (mapDPath d).comp
    (transverseCellTypePathContribution i j hij g h)

omit [LinearOrder ι] in
@[simp]
theorem physicalTransverseCellTypeContribution_single
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g h : G)
    (c : Configuration ι G) (n : ℤ) :
    physicalTransverseCellTypeContribution d i j hij g h
        (Finsupp.single c n) =
      n • square d (Finsupp.single i g) (Finsupp.single j h) (d c) := by
  simp [physicalTransverseCellTypeContribution,
    transverseCellTypePathContribution, primitiveCellBoundaryGenerator,
    square]

omit [LinearOrder ι] in
/-- Translating coefficient bases translates the resulting physical square. -/
theorem physicalTransverseCellTypeContribution_distributionTranslation
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g h : G)
    (r : Configuration ι G) (u : Dist (Configuration ι G)) :
    physicalTransverseCellTypeContribution d i j hij g h
        (distributionTranslation r u) =
      baseTranslation (d r)
        (physicalTransverseCellTypeContribution d i j hij g h u) := by
  have hmaps :
      (physicalTransverseCellTypeContribution d i j hij g h).comp
          (distributionTranslation r) =
        (baseTranslation (d r)).comp
          (physicalTransverseCellTypeContribution d i j hij g h) := by
    ext c
    simp [baseTranslation_square, map_add, add_comm]
  exact LinearMap.congr_fun hmaps u

omit [LinearOrder ι] in
/-- Finite difference of base coefficients becomes finite base difference. -/
theorem physicalTransverseCellTypeContribution_distributionDifference
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g h : G)
    (r : Configuration ι G) (u : Dist (Configuration ι G)) :
    physicalTransverseCellTypeContribution d i j hij g h
        (distributionDifference r u) =
      baseDifference (d r)
        (physicalTransverseCellTypeContribution d i j hij g h u) := by
  rw [distributionDifference, baseDifference]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [physicalTransverseCellTypeContribution_distributionTranslation]

omit [LinearOrder ι] in
/-- Base-difference operators commute because base translations commute. -/
theorem baseDifference_commute_apply
    {B : Type uB} [AddCommGroup B]
    (a b : B) (p : Path (Configuration ι G) B) :
    baseDifference a (baseDifference b p) =
      baseDifference b (baseDifference a p) := by
  let hmaps :
      (baseDifference (I := Configuration ι G) a).comp
          (baseDifference (I := Configuration ι G) b) =
        (baseDifference (I := Configuration ι G) b).comp
          (baseDifference (I := Configuration ι G) a) := by
    ext q
    change
      baseDifference a (baseDifference b (edge q.1 q.2)) =
        baseDifference b (baseDifference a (edge q.1 q.2))
    simp only [baseDifference_edge, map_sub]
    have hab : q.2 + b + a = q.2 + a + b := by abel
    rw [hab]
    abel
  exact LinearMap.congr_fun hmaps p

omit [LinearOrder ι] in
/-- One base difference commutes through any finite string of them. -/
theorem baseDifference_iteratedBaseDifference_commute
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (r : Configuration ι G) (rs : List (Configuration ι G))
    (p : Path (Configuration ι G) B) :
    baseDifference (d r) (iteratedBaseDifference d rs p) =
      iteratedBaseDifference d rs (baseDifference (d r) p) := by
  induction rs generalizing p with
  | nil => rfl
  | cons s rs ih =>
      simp only [iteratedBaseDifference_cons]
      rw [ih]
      rw [baseDifference_commute_apply]

omit [LinearOrder ι] in
/--
The contribution map intertwines every finite list of distribution
differences with the paper's iterated physical base differences.
-/
theorem physicalTransverseCellTypeContribution_iteratedDistributionDifference
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g h : G)
    (rs : List (Configuration ι G))
    (u : Dist (Configuration ι G)) :
    physicalTransverseCellTypeContribution d i j hij g h
        (iteratedDistributionDifference rs u) =
      iteratedBaseDifference d rs
        (physicalTransverseCellTypeContribution d i j hij g h u) := by
  induction rs generalizing u with
  | nil => rfl
  | cons r rs ih =>
      simp only [iteratedDistributionDifference_cons, LinearMap.comp_apply,
        iteratedBaseDifference_cons]
      rw [physicalTransverseCellTypeContribution_distributionDifference]
      rw [ih]
      rw [baseDifference_iteratedBaseDifference_commute]

omit [LinearOrder ι] in
/-- A cube coefficient gives exactly one full basic physical locality square. -/
theorem physicalTransverseCellTypeContribution_cubeDistribution
    {B : Type uB} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (i j : ι) (hij : i ≠ j) (g h : G)
    (c : Configuration ι G) :
    physicalTransverseCellTypeContribution d i j hij g h
        (cubeDistribution c) =
      iteratedPhysicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h)
        (activeCoordinateIncrements c) 0 := by
  rw [cubeDistribution_eq_iteratedDistributionDifference]
  rw [physicalTransverseCellTypeContribution_iteratedDistributionDifference]
  simp [iteratedPhysicalLocalitySquare, physicalLocalitySquare]

end Contributions

section FacetBridge

variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

omit [LinearOrder ι] in
/--
A cube contained in no facet which sees both square coordinates supplies the
abstract `NoCommonFacetList`: a facet either deletes one square coordinate,
or it deletes one active coordinate of the cube.
-/
theorem noCommonFacetList_transverse_activeCoordinateIncrements
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (i j : ι) (g h : G) (c : Configuration ι G)
    (hc : c ∈ noFacetContainsCubeIndices (G := G)
      (fun ρ : { ρ : Facet // i ∈ facets ρ ∧ j ∈ facets ρ } =>
        facets ρ.1)) :
    NoCommonFacetList L.primitiveRes
      (Finsupp.single i g :: Finsupp.single j h ::
        activeCoordinateIncrements c) := by
  rw [noCommonFacetList_iff]
  intro ρ
  by_cases hiρ : i ∈ facets ρ
  · by_cases hjρ : j ∈ facets ρ
    · have hcρ := hc ⟨ρ, hiρ, hjρ⟩
      push Not at hcρ
      obtain ⟨k, hkc, hkρ⟩ := hcρ
      refine ⟨Finsupp.single k (c k), ?_, ?_⟩
      · apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        unfold activeCoordinateIncrements
        apply List.mem_map.mpr
        exact ⟨k, by simpa using hkc, rfl⟩
      · rw [hprimitive ρ]
        exact coordinateRestriction_single_not_mem (facets ρ) hkρ (c k)
    · refine ⟨Finsupp.single j h, by simp, ?_⟩
      rw [hprimitive ρ]
      exact coordinateRestriction_single_not_mem (facets ρ) hjρ h
  · refine ⟨Finsupp.single i g, by simp, ?_⟩
    rw [hprimitive ρ]
    exact coordinateRestriction_single_not_mem (facets ρ) hiρ g

omit [LinearOrder ι] in
/-- Every no-visible-facet cube contribution is a physical identity. -/
theorem physicalTransverseCellTypeContribution_cubeDistribution_mem
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (i j : ι) (hij : i ≠ j) (g h : G) (hg : g ≠ 0) (hh : h ≠ 0)
    (c : Configuration ι G)
    (hc : c ∈ noFacetContainsCubeIndices (G := G)
      (fun ρ : { ρ : Facet // i ∈ facets ρ ∧ j ∈ facets ρ } =>
        facets ρ.1)) :
    physicalTransverseCellTypeContribution d i j hij g h
        (cubeDistribution c) ∈ physicalIdentityPaths L := by
  rw [physicalTransverseCellTypeContribution_cubeDistribution]
  apply Submodule.subset_span
  refine ⟨i, g, j, h, activeCoordinateIncrements c, 0,
    hg, hh, ?_, rfl⟩
  exact noCommonFacetList_transverse_activeCoordinateIncrements
    facets L hprimitive i j g h c hc

/--
Cross-square part of the reverse inclusion in Lemma (2.26): a base
coefficient distribution locally invisible on every facet seeing the fixed
transverse cell type has physical contribution in `E_id`.
-/
theorem physicalTransverseCellTypeContribution_mem_physicalIdentityPaths
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (i j : ι) (hij : i ≠ j) (g h : G) (hg : g ≠ 0) (hh : h ≠ 0)
    {u : Dist (Configuration ι G)}
    (hu : u ∈ transverseCellTypeRestrictionKernel (G := G) facets i j) :
    physicalTransverseCellTypeContribution d i j hij g h u ∈
      physicalIdentityPaths L := by
  rw [transverseCellTypeRestrictionKernel,
    coordinateCommonRestrictionKernel_eq_noFacetCubeSpan,
    noFacetCubeSpan] at hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨c, hc, rfl⟩
      rw [cubeBasis_apply]
      exact physicalTransverseCellTypeContribution_cubeDistribution_mem
        facets L hprimitive i j hij g h hg hh c hc
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using (physicalIdentityPaths L).add_mem ihx ihy
  | smul n x hx ih =>
      simpa using (physicalIdentityPaths L).smul_mem n ih

end FacetBridge

end GeneralSphereT.PathAlgebra
