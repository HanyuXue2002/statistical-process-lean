import Formalization.Section3SimplexLocalTau

set_option linter.style.header false

/-!
# Section 3: passing from a carrier family back to all facets

If every global facet is contained in some member of a selected carrier
family, then a cube which vanishes on the carrier family also vanishes on
every global facet.  This is the elementary observation used for a cone:
adjoin the apex to a bottom simplex to obtain a carrier simplex.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uL

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF} {LocalFacet : Type uL}

omit [LinearOrder ι] in
/-- Vanishing after restriction to a larger coordinate set implies vanishing
after restriction to every smaller coordinate set. -/
theorem coordinateRestriction_eq_zero_of_subset
    {S T : Set ι} (hST : S ⊆ T) (r : Configuration ι G)
    (hzero : coordinateRestriction T r = 0) :
    coordinateRestriction S r = 0 := by
  ext i
  have hiT : i.1 ∈ T := hST i.2
  have hvalue := congrArg (fun c : Configuration T G => c ⟨i.1, hiT⟩) hzero
  simpa using hvalue

variable (globalFacets : Facet → Set ι)
variable (localFacets : LocalFacet → Set ι)

omit [LinearOrder ι] in
/-- Every elementary cube local to the carrier family is also a global
elementary nonface cube when every global facet is contained in a carrier
facet. -/
theorem elementaryPhysicalNonfaceCubeSpan_mono_of_refinement
    (d : Configuration ι G →+ B)
    (hrefine : ∀ ρ : Facet, ∃ lf : LocalFacet,
      globalFacets ρ ⊆ localFacets lf) :
    elementaryPhysicalNonfaceCubeSpan localFacets d ≤
      elementaryPhysicalNonfaceCubeSpan globalFacets d := by
  rw [elementaryPhysicalNonfaceCubeSpan, Submodule.span_le]
  rintro z ⟨rs, hrs, a, helem, hlocal, rfl⟩
  apply Submodule.subset_span
  refine ⟨rs, hrs, a, helem, ?_, rfl⟩
  intro ρ
  obtain ⟨lf, hsubset⟩ := hrefine ρ
  obtain ⟨r, hr, hzero⟩ := hlocal lf
  exact ⟨r, hr,
    coordinateRestriction_eq_zero_of_subset hsubset r hzero⟩

omit [LinearOrder ι] in
/-- The same carrier span is contained in the ordinary global physical
nonface-cube denominator. -/
theorem elementaryPhysicalNonfaceCubeSpan_le_globalPhysicalNonfaceCubeSpan
    (d : Configuration ι G →+ B)
    (hrefine : ∀ ρ : Facet, ∃ lf : LocalFacet,
      globalFacets ρ ⊆ localFacets lf) :
    elementaryPhysicalNonfaceCubeSpan localFacets d ≤
      physicalNonfaceCubeSpan globalFacets d := by
  exact
    (elementaryPhysicalNonfaceCubeSpan_mono_of_refinement
      globalFacets localFacets d hrefine).trans
      (elementaryPhysicalNonfaceCubeSpan_le_physicalNonfaceCubeSpan
        globalFacets (d := d))

end GeneralSphereT.PathAlgebra
