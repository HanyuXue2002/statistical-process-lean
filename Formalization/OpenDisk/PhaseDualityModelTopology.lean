import Formalization.OpenDisk.PhaseDualityModel
import Formalization.OpenDisk.PhaseDualityTopology

set_option linter.style.header false

/-!
# Topological phase duality and connected facet-curvature phases

The topologies below are the report's product/subspace/quotient topologies.
The literal closed local phase-table quotient is homeomorphic, and already
linearly equivalent, to the pointwise character group of the literal `τ`.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk.PhaseDuality

variable {ι G B Facet : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {BAt : Facet → Type*} [∀ ρ, AddCommGroup (BAt ρ)]
variable (facets : Facet → Set ι) (d : Configuration ι G →+ B)
variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G) (BAt := BAt) d)

theorem continuous_closedSPTCharacterEquiv (hd : Function.Surjective d) :
    Continuous (closedSPTCharacterEquiv facets d hd) := by
  apply Continuous.subtype_mk
  exact (closedPhaseCharacterHomeomorph d hd).continuous.comp continuous_subtype_val

theorem continuous_closedSPTCharacterEquiv_symm (hd : Function.Surjective d) :
    Continuous (closedSPTCharacterEquiv facets d hd).symm := by
  apply Continuous.subtype_mk
  exact (closedPhaseCharacterHomeomorph d hd).symm.continuous.comp continuous_subtype_val

def closedSPTCharacterHomeomorph (hd : Function.Surjective d) :
    closedSPT facets d hd ≃ₜ annihilator (identityDistributions facets d) where
  toEquiv := (closedSPTCharacterEquiv facets d hd).toEquiv
  continuous_toFun := continuous_closedSPTCharacterEquiv facets d hd
  continuous_invFun := continuous_closedSPTCharacterEquiv_symm facets d hd

instance closedSPTCompactSpace (hd : Function.Surjective d) :
    CompactSpace (closedSPT facets d hd) :=
  (closedSPTCharacterHomeomorph facets d hd).symm.compactSpace

theorem continuous_closedSPTRestriction (hd : Function.Surjective d) :
    Continuous (closedSPTRestriction facets d L hd) :=
  (continuous_restrictCharacter _ _).comp
    (continuous_closedSPTCharacterEquiv facets d hd)

/-- Proposition 2.1 with its actual product and quotient topologies.
The same underlying map is the algebraic equivalence
`closedSPTQuotientEquiv`. -/
def closedSPTQuotientHomeomorph
    (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) :
    (closedSPT facets d hd ⧸ facetCurvaturePhases facets d L hd) ≃ₜ
      (FullTau facets d L →ₗ[ℤ] Phase) := by
  let Q := facetCurvaturePhases facets d L hd
  letI : CompactSpace (closedSPT facets d hd ⧸ Q) :=
    Function.Surjective.compactSpace Q.mkQL.continuous Q.mkQ_surjective
  let e := closedSPTQuotientEquiv facets d L hprimitive hd
  apply Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
  apply Q.isQuotientMap_mkQL.continuous_iff.mpr
  convert continuous_closedSPTRestriction facets d L hd using 1
  funext x
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (closedSPTRestriction facets d L hd)
    (closedSPTRestriction_surjective facets d L hprimitive hd) x

section FacetCurvatureTopology

variable [Fintype Facet]
variable (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
variable (hd : Function.Surjective d)

/-- Build the literal full phase table from arbitrary facet-curvature tables. -/
def facetCurvatureSum (k : ∀ ρ, BAt ρ → Phase) :
    facetCurvaturePhases facets d L hd := by
  let f : Configuration ι G → Phase := fun c => ∑ ρ, k ρ (L.physicalRes ρ (d c))
  have hfclosed : f ∈ closedInvariant d := by
    intro z hz c
    simp [f, map_add, hz]
  have hflocal : DifferenceLocal facets f := by
    apply (differenceLocal_iff_facetSum facets f).mpr
    refine ⟨fun ρ x => k ρ (L.localD ρ x), fun c => ?_⟩
    apply Finset.sum_congr rfl
    intro ρ _
    have hc := DFunLike.congr_fun (L.commutes ρ) c
    simp only [AddMonoidHom.comp_apply, hprimitive] at hc
    exact congrArg (k ρ) hc
  let φ : closedSPT facets d hd :=
    ⟨⟨f, hfclosed⟩, (mem_closedSPT_iff facets d hd _).mpr hflocal⟩
  exact ⟨φ, (mem_facetCurvaturePhases_iff facets d L hd φ).mpr ⟨k, fun _ => rfl⟩⟩

theorem facetCurvatureSum_surjective :
    Function.Surjective (facetCurvatureSum facets d L hprimitive hd) := by
  intro φ
  obtain ⟨k, hk⟩ := (mem_facetCurvaturePhases_iff facets d L hd φ.1).mp φ.2
  refine ⟨k, ?_⟩
  ext c
  exact (hk c).symm

theorem continuous_facetCurvatureSum :
    Continuous (facetCurvatureSum facets d L hprimitive hd) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro c
  apply continuous_finsetSum
  intro ρ _
  exact (continuous_apply (L.physicalRes ρ (d c))).comp (continuous_apply ρ)

include hprimitive in
/-- The full facet-curvature subgroup is compact. -/
theorem facetCurvaturePhases_compactSpace :
    CompactSpace (facetCurvaturePhases facets d L hd) :=
  Function.Surjective.compactSpace
    (continuous_facetCurvatureSum facets d L hprimitive hd)
    (facetCurvatureSum_surjective facets d L hprimitive hd)

include hprimitive in
/-- The full facet-curvature subgroup is path connected, as asserted before
Proposition 2.1.  The global phase varies in its own circle coordinate. -/
theorem facetCurvaturePhases_pathConnectedSpace :
    PathConnectedSpace (facetCurvaturePhases facets d L hd) :=
  Function.Surjective.pathConnectedSpace
    (facetCurvatureSum_surjective facets d L hprimitive hd)
    (continuous_facetCurvatureSum facets d L hprimitive hd)

end FacetCurvatureTopology

end OpenDisk.PhaseDuality
