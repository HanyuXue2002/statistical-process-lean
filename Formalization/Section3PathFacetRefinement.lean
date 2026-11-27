import Formalization.Section3CarrierRefinement
import Formalization.Section3SimplicialConeReplacement

set_option linter.style.header false

/-!
# Section 3: refinement of facet families for physical paths

The cone replacement is most naturally carried out using only facets which
contain the apex.  The global simplicial quotient from Section 2 uses all
nonempty simplices as facets.  This file proves the two directions needed to
pass between those presentations:

* global facetwise vanishing implies vanishing on the apex subfamily;
* an identity for the apex family is a global identity, because every global
  simplex is contained in its apex extension.

The second statement is first proved for arbitrary coordinate facet
families.  It depends only on the primitive coordinate restrictions, not on
the physical restriction groups.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uL uBG uBL

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {GlobalFacet : Type uF} {LocalFacet : Type uL}
variable (globalFacets : GlobalFacet → Set ι)
variable (localFacets : LocalFacet → Set ι)
variable {GlobalBAt : GlobalFacet → Type uBG}
variable {LocalBAt : LocalFacet → Type uBL}
variable [∀ ρ, AddCommGroup (GlobalBAt ρ)]
variable [∀ ρ, AddCommGroup (LocalBAt ρ)]
variable {d : Configuration ι G →+ B}

variable (Lglobal : FacetRestrictionData
  (CAt := fun ρ => Configuration (globalFacets ρ) G)
  (BAt := GlobalBAt) (Facet := GlobalFacet) d)
variable (Llocal : FacetRestrictionData
  (CAt := fun ρ => Configuration (localFacets ρ) G)
  (BAt := LocalBAt) (Facet := LocalFacet) d)

omit [LinearOrder ι] in
/-- If every global facet is contained in a selected local facet, a
no-common-facet condition for the selected family also holds globally. -/
theorem noCommonFacetList_of_facet_refinement
    (hglobal : ∀ ρ : GlobalFacet,
      Lglobal.primitiveRes ρ = coordinateRestriction (globalFacets ρ))
    (hlocal : ∀ ρ : LocalFacet,
      Llocal.primitiveRes ρ = coordinateRestriction (localFacets ρ))
    (hrefine : ∀ ρ : GlobalFacet, ∃ lf : LocalFacet,
      globalFacets ρ ⊆ localFacets lf)
    (increments : List (Configuration ι G))
    (h : NoCommonFacetList Llocal.primitiveRes increments) :
    NoCommonFacetList Lglobal.primitiveRes increments := by
  rw [noCommonFacetList_iff] at h ⊢
  intro ρ
  obtain ⟨lf, hsubset⟩ := hrefine ρ
  obtain ⟨r, hr, hrzero⟩ := h lf
  refine ⟨r, hr, ?_⟩
  rw [hglobal ρ]
  have hrzero' : coordinateRestriction (localFacets lf) r = 0 := by
    rw [← hlocal lf]
    exact hrzero
  exact coordinateRestriction_eq_zero_of_subset hsubset r hrzero'

omit [LinearOrder ι] in
/-- Every locality generator for a cofinal selected facet family is also a
global locality generator. -/
theorem physicalLocalityIdentityGenerators_subset_of_facet_refinement
    (hglobal : ∀ ρ : GlobalFacet,
      Lglobal.primitiveRes ρ = coordinateRestriction (globalFacets ρ))
    (hlocal : ∀ ρ : LocalFacet,
      Llocal.primitiveRes ρ = coordinateRestriction (localFacets ρ))
    (hrefine : ∀ ρ : GlobalFacet, ∃ lf : LocalFacet,
      globalFacets ρ ⊆ localFacets lf) :
    physicalLocalityIdentityGenerators Llocal ⊆
      physicalLocalityIdentityGenerators Lglobal := by
  rintro R ⟨i, g, j, h, rs, a, hg, hh, hcommon, rfl⟩
  refine ⟨i, g, j, h, rs, a, hg, hh, ?_, rfl⟩
  exact noCommonFacetList_of_facet_refinement
    globalFacets localFacets Lglobal Llocal hglobal hlocal hrefine _ hcommon

omit [LinearOrder ι] in
/-- Path-level facet refinement: the physical identity denominator for a
cofinal selected family is contained in the global denominator. -/
theorem physicalIdentityPaths_le_of_facet_refinement
    (hglobal : ∀ ρ : GlobalFacet,
      Lglobal.primitiveRes ρ = coordinateRestriction (globalFacets ρ))
    (hlocal : ∀ ρ : LocalFacet,
      Llocal.primitiveRes ρ = coordinateRestriction (localFacets ρ))
    (hrefine : ∀ ρ : GlobalFacet, ∃ lf : LocalFacet,
      globalFacets ρ ⊆ localFacets lf) :
    physicalIdentityPaths Llocal ≤ physicalIdentityPaths Lglobal := by
  rw [physicalIdentityPaths, physicalIdentityPaths, Submodule.span_le]
  intro R hR
  apply Submodule.subset_span
  exact physicalLocalityIdentityGenerators_subset_of_facet_refinement
    globalFacets localFacets Lglobal Llocal hglobal hlocal hrefine hR

end GeneralSphereT.PathAlgebra

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Extend a global simplex by the apex.  On a cone this is an apex facet. -/
def apexExtensionFacet
    {v : V} (hcone : IsConeAt K v) (σ : NonemptySimplex K) :
    ConeFacet K v :=
  ⟨⟨insert v σ.1, hcone σ⟩, by
    intro x hx
    have hxv : x = v := by simpa [coneApexSimplex] using hx
    subst x
    simp⟩

omit [Fintype V] in
/-- Every cochain coordinate visible in `σ` remains visible after adjoining
the apex. -/
theorem facesIn_subset_apexExtensionFacet
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (σ : NonemptySimplex K) :
    facesIn K n σ ⊆
      carrierFacetSets K (coneApexSimplex K v) n
        (apexExtensionFacet K hcone σ) := by
  intro τ hτσ
  exact hτσ.trans (Finset.subset_insert v σ.1)

/-- Apex-facet identities are identities for the full simplicial facet
family used by the Section 2 quotient. -/
theorem conePhysicalIdentityPaths_le_global
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    physicalIdentityPaths (coneFacetRestrictionData (G := G) K v n) ≤
      physicalIdentityPaths (facetRestrictionData (G := G) K n) := by
  apply physicalIdentityPaths_le_of_facet_refinement
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (carrierFacetSets K (coneApexSimplex K v) n)
    (facetRestrictionData (G := G) K n)
    (coneFacetRestrictionData (G := G) K v n)
    (facetRestrictionData_primitiveRes (G := G) K n)
    (carrierFacetRestrictionData_primitiveRes
      (G := G) K (coneApexSimplex K v) n)
  intro σ
  exact ⟨apexExtensionFacet K hcone σ,
    facesIn_subset_apexExtensionFacet K hcone n σ⟩

/-- Global facetwise-zero physical paths are facetwise zero on the apex
subfamily. -/
theorem globalLocallyZeroPhysicalPath_le_cone
    (v : V) (n : ℕ) :
    (facetRestrictionData (G := G) K n).locallyZeroPhysicalPath ≤
      (coneFacetRestrictionData (G := G) K v n).locallyZeroPhysicalPath := by
  intro e he
  rw [locallyZeroPhysicalPath, Submodule.mem_iInf]
  intro ρ
  have hρ :=
    (Submodule.mem_iInf (fun σ : NonemptySimplex K =>
      LinearMap.ker
        ((facetRestrictionData (G := G) K n).restrictPhysicalPath σ))).1
      he ρ.1
  exact hρ

/-- Hence every element of the global numerator may be fed to the
apex-family replacement theorem. -/
theorem globalPhysicalInvariantPaths_le_cone
    (v : V) (n : ℕ) :
    physicalInvariantPaths (facetRestrictionData (G := G) K n) ≤
      physicalInvariantPaths (coneFacetRestrictionData (G := G) K v n) := by
  intro e he
  exact ⟨he.1, he.2.1,
    globalLocallyZeroPhysicalPath_le_cone (G := G) K v n he.2.2⟩

/-! ## The distribution-level cone consequence -/

/-- Global facetwise-zero reduced distributions are facetwise zero on the
apex subfamily. -/
theorem globalPhysicalInvariantDistributions_le_cone
    (v : V) (n : ℕ) :
    FacetRestrictionData.physicalInvariantDistributions
        (facetRestrictionData (G := G) K n) ≤
      FacetRestrictionData.physicalInvariantDistributions
        (coneFacetRestrictionData (G := G) K v n) := by
  intro z hz
  rw [physicalInvariantDistributions, Submodule.mem_iInf]
  intro ρ
  have hρ :=
    (Submodule.mem_iInf (fun σ : NonemptySimplex K =>
      LinearMap.ker
        ((facetRestrictionData (G := G) K n).restrictPhysicalRedDist σ))).1
      hz ρ.1
  exact hρ

/-- Elementary local cubes for the apex family belong to the global
distribution denominator. -/
theorem coneElementaryCubeSpan_le_global
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    elementaryPhysicalNonfaceCubeSpan
        (carrierFacetSets K (coneApexSimplex K v) n)
        (coboundaryToRange (G := G) K n) ≤
      physicalNonfaceCubeSpan
        (fun σ : NonemptySimplex K => facesIn K n σ)
        (coboundaryToRange (G := G) K n) := by
  apply elementaryPhysicalNonfaceCubeSpan_le_globalPhysicalNonfaceCubeSpan
  intro σ
  exact ⟨apexExtensionFacet K hcone σ,
    facesIn_subset_apexExtensionFacet K hcone n σ⟩

/-- On a cone, every globally invisible physical distribution is already a
global locality identity. -/
theorem globalPhysicalInvariantDistributions_le_nonfaceCubeSpan
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    (facetRestrictionData (G := G) K n).physicalInvariantDistributions ≤
      physicalNonfaceCubeSpan
        (fun σ : NonemptySimplex K => facesIn K n σ)
        (coboundaryToRange (G := G) K n) := by
  exact (globalPhysicalInvariantDistributions_le_cone (G := G) K v n).trans
    ((simplexLocalInvariant_le_elementarySpan
      (G := G) K n (coneApexSimplex K v)).trans
      (coneElementaryCubeSpan_le_global (G := G) K hcone n))

/-- The global simplicial `tau` quotient vanishes on a cone. -/
theorem simplicialConeTau_eq_zero
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (x : Tau (fun σ : NonemptySimplex K => facesIn K n σ)
      (facetRestrictionData (G := G) K n)) :
    x = 0 := by
  refine Submodule.Quotient.induction_on
    (p := physicalNonfaceCubeSpanInInvariantDistributions
      (fun σ : NonemptySimplex K => facesIn K n σ)
      (facetRestrictionData (G := G) K n)) x ?_
  intro z
  apply (Submodule.Quotient.mk_eq_zero
    (physicalNonfaceCubeSpanInInvariantDistributions
      (fun σ : NonemptySimplex K => facesIn K n σ)
      (facetRestrictionData (G := G) K n))).2
  change (z : RedDist (CoboundaryGroup (G := G) K n)) ∈
    physicalNonfaceCubeSpan
      (fun σ : NonemptySimplex K => facesIn K n σ)
      (coboundaryToRange (G := G) K n)
  exact globalPhysicalInvariantDistributions_le_nonfaceCubeSpan
    (G := G) K hcone n z.property

/-- Typeclass form of global `tau(C_v M)=0`. -/
theorem simplicialConeTau_subsingleton
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    Subsingleton
      (Tau (fun σ : NonemptySimplex K => facesIn K n σ)
        (facetRestrictionData (G := G) K n)) :=
  ⟨fun x y => (simplicialConeTau_eq_zero (G := G) K hcone n x).trans
    (simplicialConeTau_eq_zero (G := G) K hcone n y).symm⟩

end GeneralSphereT.SimplicialCochain
