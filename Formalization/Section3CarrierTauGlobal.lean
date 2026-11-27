import Formalization.Section3CarrierRefinement
import Formalization.Section3SimplicialLocalTau

set_option linter.style.header false

/-!
# Section 3: promoting carrier-local tau vanishing

The simplex-local theorem checks only simplices containing a fixed carrier.
This file gives the short comparison with the ordinary facet family.  If each
ordinary facet-coordinate set is contained in one carrier facet-coordinate
set, then every globally invisible distribution first becomes carrier-local,
is decomposed there into elementary cubes, and those cubes are also global
identities.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- A distribution invisible on every simplex is invisible on the subfamily
of simplices containing a fixed carrier. -/
theorem globalInvariantDistributions_le_carrierInvariant
    (n : ℕ) (ρ : NonemptySimplex K) :
    physicalInvariantDistributions (facetRestrictionData (G := G) K n) ≤
      physicalInvariantDistributions
        (carrierFacetRestrictionData (G := G) K ρ n) := by
  intro z hz
  rw [physicalInvariantDistributions, Submodule.mem_iInf]
  intro σ
  rw [LinearMap.mem_ker]
  have hzσ :
      z ∈ LinearMap.ker
        (restrictPhysicalRedDist (facetRestrictionData (G := G) K n) σ.1) :=
    (Submodule.mem_iInf (fun θ : NonemptySimplex K =>
      LinearMap.ker
        (restrictPhysicalRedDist (facetRestrictionData (G := G) K n) θ))).1
      hz σ.1
  exact hzσ

/-- If the carrier family refines all ordinary facets, the global
distribution numerator is contained in the global nonface-cube denominator.
-/
theorem globalInvariantDistributions_le_nonfaceCubeSpan_of_carrier
    (n : ℕ) (ρ : NonemptySimplex K)
    (hrefine : ∀ σ : NonemptySimplex K,
      ∃ lf : CarrierFacet K ρ,
        facesIn K n σ ⊆ carrierFacetSets K ρ n lf) :
    physicalInvariantDistributions (facetRestrictionData (G := G) K n) ≤
      physicalNonfaceCubeSpan (fun σ : NonemptySimplex K => facesIn K n σ)
        (coboundaryToRange (G := G) K n) := by
  exact
    (globalInvariantDistributions_le_carrierInvariant (G := G) K n ρ).trans
      ((simplexLocalInvariant_le_elementarySpan (G := G) K n ρ).trans
        (elementaryPhysicalNonfaceCubeSpan_le_globalPhysicalNonfaceCubeSpan
          (fun σ : NonemptySimplex K => facesIn K n σ)
          (carrierFacetSets K ρ n)
          (coboundaryToRange (G := G) K n) hrefine))

/-- Representative form: under the same carrier-refinement hypothesis every
class in the ordinary global `tau` quotient is zero. -/
theorem globalTau_eq_zero_of_carrier
    (n : ℕ) (ρ : NonemptySimplex K)
    (hrefine : ∀ σ : NonemptySimplex K,
      ∃ lf : CarrierFacet K ρ,
        facesIn K n σ ⊆ carrierFacetSets K ρ n lf)
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
  exact globalInvariantDistributions_le_nonfaceCubeSpan_of_carrier
    (G := G) K n ρ hrefine z.2

/-- Typeclass form of global tau vanishing. -/
theorem globalTau_subsingleton_of_carrier
    (n : ℕ) (ρ : NonemptySimplex K)
    (hrefine : ∀ σ : NonemptySimplex K,
      ∃ lf : CarrierFacet K ρ,
        facesIn K n σ ⊆ carrierFacetSets K ρ n lf) :
    Subsingleton
      (Tau (fun σ : NonemptySimplex K => facesIn K n σ)
        (facetRestrictionData (G := G) K n)) :=
  ⟨fun x y =>
    (globalTau_eq_zero_of_carrier (G := G) K n ρ hrefine x).trans
      (globalTau_eq_zero_of_carrier (G := G) K n ρ hrefine y).symm⟩

end GeneralSphereT.SimplicialCochain
