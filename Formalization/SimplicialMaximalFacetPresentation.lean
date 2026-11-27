import Formalization.Section3PathFacetRefinement
import Formalization.PrimitiveQuotientFunctoriality
import Mathlib.Order.Preorder.Finite

set_option linter.style.header false

/-!
# Maximal-facet presentation of the simplicial quotients

The concrete simplicial model initially indexes its locality conditions by
all nonempty simplices.  The paper uses only maximal simplices.  On a finite
complex these presentations coincide: every simplex lies in a maximal one,
and restriction to the smaller simplex factors through restriction to the
larger one.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [Finite ι] [AddCommGroup G]

/-- Restrict a configuration on `T` further to a subset `S`.  Keeping this
map explicit makes all path and distribution factorization statements below
ordinary functoriality of `mapPath` and `mapRedDist`. -/
def configurationRestrictionOfSubset {S T : Set ι} (hST : S ⊆ T) :
    Configuration T G →+ Configuration S G where
  toFun c := Finsupp.equivFunOnFinite.symm fun i => c ⟨i.1, hST i.2⟩
  map_zero' := by
    ext i
    simp
  map_add' c c' := by
    ext i
    simp

@[simp]
theorem configurationRestrictionOfSubset_apply {S T : Set ι}
    (hST : S ⊆ T) (c : Configuration T G) (i : S) :
    configurationRestrictionOfSubset hST c i = c ⟨i.1, hST i.2⟩ :=
  rfl

/-- Restricting first to `T` and then to `S ⊆ T` is direct restriction to
`S`. -/
theorem configurationRestrictionOfSubset_comp_coordinateRestriction
    {S T : Set ι} (hST : S ⊆ T) :
    (configurationRestrictionOfSubset (G := G) hST).comp
        (coordinateRestriction T) =
      coordinateRestriction S := by
  ext c i
  rfl

end GeneralSphereT.PathAlgebra

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- A simplex which is maximal among the faces of `K`. -/
def IsMaximalSimplex (σ : NonemptySimplex K) : Prop :=
  ∀ τ : NonemptySimplex K, σ.1 ⊆ τ.1 → τ.1 ⊆ σ.1

/-- The type of maximal nonempty simplices (facets) of `K`. -/
abbrev MaximalFacet := {σ : NonemptySimplex K // IsMaximalSimplex K σ}

omit [LinearOrder V] [Fintype V] in
/-- Every simplex in a finite simplicial complex is contained in a maximal
simplex. -/
theorem exists_maximalFacet_superset [Finite V] (σ : NonemptySimplex K) :
    ∃ μ : MaximalFacet K, σ.1 ⊆ μ.1.1 := by
  obtain ⟨τ, hστ, hτmax⟩ :=
    (Set.toFinite (K.faces : Set (Finset V))).exists_le_maximal σ.2
  have hτK : τ ∈ K := hτmax.1
  let τ' : NonemptySimplex K := ⟨τ, hτK⟩
  have hmax : IsMaximalSimplex K τ' := by
    intro υ hτυ
    exact hτmax.2 υ.2 hτυ
  exact ⟨⟨τ', hmax⟩, hστ⟩

/-- The restriction package obtained by indexing only by maximal facets. -/
def maximalFacetRestrictionData (n : ℕ) :
    FacetRestrictionData
      (CAt := fun μ : MaximalFacet K =>
        Configuration (facesIn K n μ.1) G)
      (BAt := fun μ : MaximalFacet K =>
        Configuration (facesIn K (n + 1) μ.1) G)
      (Facet := MaximalFacet K)
      (coboundaryToRange (G := G) K n) where
  primitiveRes μ := restrictCochain (G := G) K n μ.1
  physicalRes μ := restrictCoboundary (G := G) K n μ.1
  localD μ := (localCoboundary (G := G) K n μ.1).toAddMonoidHom
  commutes μ := by
    apply AddMonoidHom.ext
    intro c
    change restrictCochain (G := G) K (n + 1) μ.1
        (coboundary K n c) =
      localCoboundary K n μ.1 (restrictCochain K n μ.1 c)
    exact DFunLike.congr_fun
      (restrictCochain_coboundary (G := G) K n μ.1) c

@[simp]
theorem maximalFacetRestrictionData_primitiveRes (n : ℕ)
    (μ : MaximalFacet K) :
    (maximalFacetRestrictionData (G := G) K n).primitiveRes μ =
      coordinateRestriction (facesIn K n μ.1) :=
  rfl

omit [LinearOrder V] [Fintype V] in
/-- Maximal facets cover every degree-`n` cochain coordinate. -/
theorem maximalFacetRestrictionData_cover [Finite V] (n : ℕ) :
    ∀ η : Simplex K n,
      ∃ μ : MaximalFacet K, η ∈ facesIn K n μ.1 := by
  intro η
  obtain ⟨μ, hημ⟩ :=
    exists_maximalFacet_superset K ⟨η.1, η.2.1⟩
  exact ⟨μ, hημ⟩

omit [LinearOrder V] [Fintype V] in
/-- Face coordinates in a simplex remain face coordinates in every larger
simplex. -/
theorem facesIn_mono {n : ℕ} {σ τ : NonemptySimplex K}
    (hστ : σ.1 ⊆ τ.1) :
    facesIn K n σ ⊆ facesIn K n τ := by
  intro η hη
  exact hη.trans hστ

/-- The no-common-facet condition is unchanged when all nonempty simplices
are replaced by the cofinal family of maximal facets. -/
theorem noCommonFacetList_maximal_iff_all (n : ℕ)
    (increments : List (Cochain K n G)) :
    NoCommonFacetList
        (maximalFacetRestrictionData (G := G) K n).primitiveRes increments ↔
      NoCommonFacetList
        (facetRestrictionData (G := G) K n).primitiveRes increments := by
  rw [noCommonFacetList_iff, noCommonFacetList_iff]
  constructor
  · intro h σ
    obtain ⟨μ, hσμ⟩ := exists_maximalFacet_superset K σ
    obtain ⟨r, hr, hrzero⟩ := h μ
    refine ⟨r, hr, ?_⟩
    rw [facetRestrictionData_primitiveRes]
    have hrzero' :
        coordinateRestriction (facesIn K n μ.1) r = 0 := by
      rw [← maximalFacetRestrictionData_primitiveRes]
      exact hrzero
    exact coordinateRestriction_eq_zero_of_subset
      (facesIn_mono K hσμ) r hrzero'
  · intro h μ
    exact h μ.1

/-- Consequently the raw path generators of `E_id` are literally the same
set in the all-simplex and maximal-facet presentations. -/
theorem physicalLocalityIdentityGenerators_maximal_eq_all (n : ℕ) :
    physicalLocalityIdentityGenerators
        (maximalFacetRestrictionData (G := G) K n) =
      physicalLocalityIdentityGenerators
        (facetRestrictionData (G := G) K n) := by
  ext R
  constructor
  · rintro ⟨i, g, j, h, rs, a, hg, hh, hcommon, rfl⟩
    exact ⟨i, g, j, h, rs, a, hg, hh,
      (noCommonFacetList_maximal_iff_all K n _).1 hcommon, rfl⟩
  · rintro ⟨i, g, j, h, rs, a, hg, hh, hcommon, rfl⟩
    exact ⟨i, g, j, h, rs, a, hg, hh,
      (noCommonFacetList_maximal_iff_all K n _).2 hcommon, rfl⟩

/-- The physical identity denominator `E_id` is independent of whether one
checks every simplex or only maximal facets. -/
theorem physicalIdentityPaths_maximal_eq_all (n : ℕ) :
    physicalIdentityPaths (maximalFacetRestrictionData (G := G) K n) =
      physicalIdentityPaths (facetRestrictionData (G := G) K n) := by
  rw [physicalIdentityPaths, physicalIdentityPaths,
    physicalLocalityIdentityGenerators_maximal_eq_all]

section RestrictionFactorization

variable {n : ℕ} {σ : NonemptySimplex K} {μ : MaximalFacet K}
variable (hσμ : σ.1 ⊆ μ.1.1)

/-- Global primitive restriction to `σ` factors through any containing
maximal facet `μ`. -/
theorem primitiveRestriction_factor :
    (configurationRestrictionOfSubset (G := G)
      (facesIn_mono K hσμ)).comp
        ((maximalFacetRestrictionData (G := G) K n).primitiveRes μ) =
      (facetRestrictionData (G := G) K n).primitiveRes σ := by
  rw [maximalFacetRestrictionData_primitiveRes,
    facetRestrictionData_primitiveRes]
  exact configurationRestrictionOfSubset_comp_coordinateRestriction
    (G := G) (facesIn_mono K hσμ)

/-- Global physical restriction to `σ` factors through any containing
maximal facet `μ`. -/
theorem physicalRestriction_factor :
    (configurationRestrictionOfSubset (G := G)
      (facesIn_mono K hσμ :
        facesIn K (n + 1) σ ⊆ facesIn K (n + 1) μ.1)).comp
        ((maximalFacetRestrictionData (G := G) K n).physicalRes μ) =
      (facetRestrictionData (G := G) K n).physicalRes σ := by
  apply AddMonoidHom.ext
  intro a
  ext η
  rfl

/-- The corresponding primitive path restriction factors through `μ`. -/
theorem restrictPrimitivePath_factor
    (e : Path (Cochain K n G) (Cochain K n G)) :
    (facetRestrictionData (G := G) K n).restrictPrimitivePath σ e =
      mapPath
        (configurationRestrictionOfSubset (G := G)
          (facesIn_mono K hσμ : facesIn K n σ ⊆ facesIn K n μ.1))
        (configurationRestrictionOfSubset (G := G)
          (facesIn_mono K hσμ : facesIn K n σ ⊆ facesIn K n μ.1))
        ((maximalFacetRestrictionData (G := G) K n).restrictPrimitivePath μ e) := by
  symm
  change mapPath _ _ (mapPath _ _ e) = mapPath _ _ e
  rw [mapPath_comp_apply]
  rw [primitiveRestriction_factor (G := G) K hσμ]

/-- The corresponding physical path restriction factors through `μ`. -/
theorem restrictPhysicalPath_factor
    (e : Path (Cochain K n G) (CoboundaryGroup (G := G) K n)) :
    (facetRestrictionData (G := G) K n).restrictPhysicalPath σ e =
      mapPath
        (configurationRestrictionOfSubset (G := G)
          (facesIn_mono K hσμ : facesIn K n σ ⊆ facesIn K n μ.1))
        (configurationRestrictionOfSubset (G := G)
          (facesIn_mono K hσμ :
            facesIn K (n + 1) σ ⊆ facesIn K (n + 1) μ.1))
        ((maximalFacetRestrictionData (G := G) K n).restrictPhysicalPath μ e) := by
  symm
  change mapPath _ _ (mapPath _ _ e) = mapPath _ _ e
  rw [mapPath_comp_apply]
  rw [primitiveRestriction_factor (G := G) K hσμ,
    physicalRestriction_factor (G := G) K hσμ]

/-- Reduced primitive-distribution restriction also factors through `μ`. -/
theorem restrictRedDist_factor (u : RedDist (Cochain K n G)) :
    (facetRestrictionData (G := G) K n).restrictRedDist σ u =
      mapRedDist
        (configurationRestrictionOfSubset (G := G)
          (facesIn_mono K hσμ : facesIn K n σ ⊆ facesIn K n μ.1))
        ((maximalFacetRestrictionData (G := G) K n).restrictRedDist μ u) := by
  symm
  change mapRedDist _ (mapRedDist _ u) = mapRedDist _ u
  rw [mapRedDist_comp_apply]
  rw [primitiveRestriction_factor (G := G) K hσμ]

/-- Reduced physical-distribution restriction also factors through `μ`. -/
theorem restrictPhysicalRedDist_factor
    (u : RedDist (CoboundaryGroup (G := G) K n)) :
    (facetRestrictionData (G := G) K n).restrictPhysicalRedDist σ u =
      mapRedDist
        (configurationRestrictionOfSubset (G := G)
          (facesIn_mono K hσμ :
            facesIn K (n + 1) σ ⊆ facesIn K (n + 1) μ.1))
        ((maximalFacetRestrictionData (G := G) K n).restrictPhysicalRedDist μ u) := by
  symm
  change mapRedDist _ (mapRedDist _ u) = mapRedDist _ u
  rw [mapRedDist_comp_apply]
  rw [physicalRestriction_factor (G := G) K hσμ]

end RestrictionFactorization

/-- Primitive paths vanish on all simplices exactly when they vanish on all
maximal facets. -/
theorem locallyZeroPrimitivePath_maximal_eq_all (n : ℕ) :
    (maximalFacetRestrictionData (G := G) K n).locallyZeroPrimitivePath =
      (facetRestrictionData (G := G) K n).locallyZeroPrimitivePath := by
  apply le_antisymm
  · intro e he
    rw [locallyZeroPrimitivePath, Submodule.mem_iInf]
    intro σ
    obtain ⟨μ, hσμ⟩ := exists_maximalFacet_superset K σ
    have hμ :
        (maximalFacetRestrictionData (G := G) K n).restrictPrimitivePath μ e =
          0 := by
      exact (Submodule.mem_iInf (fun ν : MaximalFacet K =>
        LinearMap.ker
          ((maximalFacetRestrictionData (G := G) K n).restrictPrimitivePath ν))).1
        he μ
    rw [LinearMap.mem_ker, restrictPrimitivePath_factor
      (G := G) K hσμ, hμ]
    simp
  · intro e he
    rw [locallyZeroPrimitivePath, Submodule.mem_iInf]
    intro μ
    exact (Submodule.mem_iInf (fun σ : NonemptySimplex K =>
      LinearMap.ker
        ((facetRestrictionData (G := G) K n).restrictPrimitivePath σ))).1
      he μ.1

/-- Physical paths vanish on all simplices exactly when they vanish on all
maximal facets. -/
theorem locallyZeroPhysicalPath_maximal_eq_all (n : ℕ) :
    (maximalFacetRestrictionData (G := G) K n).locallyZeroPhysicalPath =
      (facetRestrictionData (G := G) K n).locallyZeroPhysicalPath := by
  apply le_antisymm
  · intro e he
    rw [locallyZeroPhysicalPath, Submodule.mem_iInf]
    intro σ
    obtain ⟨μ, hσμ⟩ := exists_maximalFacet_superset K σ
    have hμ :
        (maximalFacetRestrictionData (G := G) K n).restrictPhysicalPath μ e =
          0 := by
      exact (Submodule.mem_iInf (fun ν : MaximalFacet K =>
        LinearMap.ker
          ((maximalFacetRestrictionData (G := G) K n).restrictPhysicalPath ν))).1
        he μ
    rw [LinearMap.mem_ker, restrictPhysicalPath_factor
      (G := G) K hσμ, hμ]
    simp
  · intro e he
    rw [locallyZeroPhysicalPath, Submodule.mem_iInf]
    intro μ
    exact (Submodule.mem_iInf (fun σ : NonemptySimplex K =>
      LinearMap.ker
        ((facetRestrictionData (G := G) K n).restrictPhysicalPath σ))).1
      he μ.1

/-- Thus the physical numerator `E_inv` is unchanged by passing from all
simplices to maximal facets. -/
theorem physicalInvariantPaths_maximal_eq_all (n : ℕ) :
    physicalInvariantPaths (maximalFacetRestrictionData (G := G) K n) =
      physicalInvariantPaths (facetRestrictionData (G := G) K n) := by
  rw [physicalInvariantPaths, physicalInvariantPaths,
    locallyZeroPhysicalPath_maximal_eq_all]

/-- Reduced primitive distributions vanish on all simplices exactly when
they vanish on all maximal facets. -/
theorem locallyZeroRedDist_maximal_eq_all (n : ℕ) :
    (maximalFacetRestrictionData (G := G) K n).locallyZeroRedDist =
      (facetRestrictionData (G := G) K n).locallyZeroRedDist := by
  apply le_antisymm
  · intro u hu
    rw [locallyZeroRedDist, Submodule.mem_iInf]
    intro σ
    obtain ⟨μ, hσμ⟩ := exists_maximalFacet_superset K σ
    have hμ :
        (maximalFacetRestrictionData (G := G) K n).restrictRedDist μ u = 0 := by
      exact (Submodule.mem_iInf (fun ν : MaximalFacet K =>
        LinearMap.ker
          ((maximalFacetRestrictionData (G := G) K n).restrictRedDist ν))).1
        hu μ
    rw [LinearMap.mem_ker, restrictRedDist_factor
      (G := G) K hσμ, hμ]
    simp
  · intro u hu
    rw [locallyZeroRedDist, Submodule.mem_iInf]
    intro μ
    exact (Submodule.mem_iInf (fun σ : NonemptySimplex K =>
      LinearMap.ker
        ((facetRestrictionData (G := G) K n).restrictRedDist σ))).1
      hu μ.1

/-- The primitive numerator `Zprim` in the `T'` presentation is unchanged. -/
theorem Zprim_maximal_eq_all (n : ℕ) :
    Zprim (maximalFacetRestrictionData (G := G) K n) =
      Zprim (facetRestrictionData (G := G) K n) := by
  rw [Zprim, Zprim, locallyZeroRedDist_maximal_eq_all]

/-- The primitive relation-path submodule is unchanged. -/
theorem relationPaths_maximal_eq_all (n : ℕ) :
    relationPaths (maximalFacetRestrictionData (G := G) K n) =
      relationPaths (facetRestrictionData (G := G) K n) := by
  rw [relationPaths, relationPaths, locallyZeroPrimitivePath_maximal_eq_all]

/-- Hence the primitive denominator `Bprim` is unchanged as a submodule of
the common global reduced-distribution group. -/
theorem Bprim_maximal_eq_all (n : ℕ) :
    Bprim (maximalFacetRestrictionData (G := G) K n) =
      Bprim (facetRestrictionData (G := G) K n) := by
  rw [Bprim, Bprim, relationPaths_maximal_eq_all]

/-- The distribution numerator `D_inv` is likewise unchanged. -/
theorem physicalInvariantDistributions_maximal_eq_all (n : ℕ) :
    (maximalFacetRestrictionData (G := G) K n).physicalInvariantDistributions =
      (facetRestrictionData (G := G) K n).physicalInvariantDistributions := by
  apply le_antisymm
  · intro u hu
    rw [physicalInvariantDistributions, Submodule.mem_iInf]
    intro σ
    obtain ⟨μ, hσμ⟩ := exists_maximalFacet_superset K σ
    have hμ :
        (maximalFacetRestrictionData (G := G) K n).restrictPhysicalRedDist μ u =
          0 := by
      exact (Submodule.mem_iInf (fun ν : MaximalFacet K =>
        LinearMap.ker
          ((maximalFacetRestrictionData (G := G) K n).restrictPhysicalRedDist ν))).1
        hu μ
    rw [LinearMap.mem_ker, restrictPhysicalRedDist_factor
      (G := G) K hσμ, hμ]
    simp
  · intro u hu
    rw [physicalInvariantDistributions, Submodule.mem_iInf]
    intro μ
    exact (Submodule.mem_iInf (fun σ : NonemptySimplex K =>
      LinearMap.ker
        ((facetRestrictionData (G := G) K n).restrictPhysicalRedDist σ))).1
      hu μ.1

/-- The raw nonface-cube generators defining `D_id` are unchanged by the
same passage to maximal facets. -/
theorem physicalNonfaceCubeGenerators_maximal_eq_all (n : ℕ) :
    physicalNonfaceCubeGenerators
        (fun μ : MaximalFacet K => facesIn K n μ.1)
        (coboundaryToRange (G := G) K n) =
      physicalNonfaceCubeGenerators
        (fun σ : NonemptySimplex K => facesIn K n σ)
        (coboundaryToRange (G := G) K n) := by
  ext u
  constructor
  · rintro ⟨rs, hrs, a, hlocal, rfl⟩
    refine ⟨rs, hrs, a, ?_, rfl⟩
    intro σ
    obtain ⟨μ, hσμ⟩ := exists_maximalFacet_superset K σ
    obtain ⟨r, hr, hrzero⟩ := hlocal μ
    exact ⟨r, hr, coordinateRestriction_eq_zero_of_subset
      (facesIn_mono K hσμ) r hrzero⟩
  · rintro ⟨rs, hrs, a, hlocal, rfl⟩
    exact ⟨rs, hrs, a, fun μ => hlocal μ.1, rfl⟩

/-- Hence the distribution denominator `D_id` is literally the same
submodule in both presentations. -/
theorem physicalNonfaceCubeSpan_maximal_eq_all (n : ℕ) :
    physicalNonfaceCubeSpan
        (fun μ : MaximalFacet K => facesIn K n μ.1)
        (coboundaryToRange (G := G) K n) =
      physicalNonfaceCubeSpan
        (fun σ : NonemptySimplex K => facesIn K n σ)
        (coboundaryToRange (G := G) K n) := by
  rw [physicalNonfaceCubeSpan, physicalNonfaceCubeSpan,
    physicalNonfaceCubeGenerators_maximal_eq_all]

end GeneralSphereT.SimplicialCochain
