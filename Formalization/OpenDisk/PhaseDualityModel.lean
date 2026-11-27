import Formalization.OpenDisk.PhaseDuality
import Formalization.OpenDisk.Locality
import Formalization.TauQuotient

set_option linter.style.header false

/-!
# Proposition 2.1 in the actual cochain distribution model

`identityDistributions` is the literal integer span of the report's elementary
nonface cubes.  The locality bridge below proves that its annihilator is
exactly the full closed-invariant local phase-table space.  Formal marginal
kernels and the circle's injectivity then give the character quotient.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk.PhaseDuality

variable {ι G B Facet : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]

/-- Active elementary nonface cubes, in the full distribution group. -/
def elementaryIdentityGenerators (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) : Set (Distribution B) :=
  {u | ∃ (steps : List (ι × G)) (a : B),
    (∀ p ∈ steps, p.2 ≠ 0) ∧
    (∀ ρ, ∃ p ∈ steps, p.1 ∉ facets ρ) ∧
    u = iteratedDistributionDifference
      (steps.map fun p => d (Finsupp.single p.1 p.2)) (Finsupp.single a 1)}

/-- The report's actual subgroup `D_id`, retaining the full ambient `D`. -/
def identityDistributions (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) : Submodule ℤ (Distribution B) :=
  Submodule.span ℤ (elementaryIdentityGenerators facets d)

theorem pushforward_eq_mapDist {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) : pushforward f = mapDist f := by
  ext x
  simp

theorem evaluate_comp_coboundary (d : Configuration ι G →+ B) (f : B → Phase) :
    phasePairing (fun c => f (d c)) = (evaluate f).comp (mapDist d) := by
  ext c
  simp

/-- The locality axiom is literally the vanishing of all elementary
integer-cube evaluations; surjectivity only chooses a primitive of the base. -/
theorem differenceLocal_iff_annihilates_identity
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (hd : Function.Surjective d) (f : B → Phase) :
    DifferenceLocal facets (fun c => f (d c)) ↔
      evaluate f ∈ annihilator (identityDistributions facets d) := by
  change DifferenceLocal facets (fun c => f (d c)) ↔
    identityDistributions facets d ≤ LinearMap.ker (evaluate f)
  rw [identityDistributions, Submodule.span_le]
  constructor
  · intro h u hu
    rcases hu with ⟨steps, a, hactive, hfac, rfl⟩
    obtain ⟨c, rfl⟩ := hd a
    have hzero := h steps hactive hfac c
    rw [iteratedPhaseDifference_eq_pairing, evaluate_comp_coboundary,
      LinearMap.comp_apply, mapDist_iteratedDistributionDifference_apply,
      mapDist_single] at hzero
    apply LinearMap.mem_ker.mpr
    simpa only [List.map_map, Function.comp_def] using hzero
  · intro h steps hactive hfac c
    rw [iteratedPhaseDifference_eq_pairing, evaluate_comp_coboundary,
      LinearMap.comp_apply, mapDist_iteratedDistributionDifference_apply,
      mapDist_single]
    exact h ⟨steps, d c, hactive, hfac, by simp [List.map_map, Function.comp_def]⟩

/-- Elementary cubes suffice: their span is the image of the entire
primitive common formal-marginal kernel. -/
theorem identityDistributions_eq_map_commonKernel
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (hd : Function.Surjective d) :
    identityDistributions facets d =
      (coordinateCommonRestrictionKernel (G := G) facets).map (mapDist d) := by
  classical
  apply le_antisymm
  · rw [identityDistributions, Submodule.span_le]
    rintro u ⟨steps, a, hactive, hfac, rfl⟩
    obtain ⟨c, rfl⟩ := hd a
    refine ⟨iteratedDistributionDifference
      (steps.map fun p => Finsupp.single p.1 p.2) (Finsupp.single c 1),
      elementaryDifference_mem_commonKernel facets steps hfac _, ?_⟩
    simp [List.map_map, Function.comp_def]
  · rintro u ⟨v, hv, rfl⟩
    rw [coordinateCommonRestrictionKernel_eq_noFacetCubeSpan, noFacetCubeSpan] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with ⟨c, hc, rfl⟩
      rw [cubeBasis_apply, mapDist_cubeDistribution_eq_iteratedDistributionDifference]
      apply Submodule.subset_span
      refine ⟨c.support.toList.map (fun i => (i, c i)), 0, ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        exact Finsupp.mem_support_iff.mp (Finset.mem_toList.mp hi)
      · intro ρ
        have hcρ := hc ρ
        push Not at hcρ
        obtain ⟨i, hi, hρ⟩ := hcρ
        exact ⟨(i, c i), List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩, hρ⟩
      · simp [List.map_map, Function.comp_def]
    | zero => simp
    | add u v hu hv ihu ihv => simpa using Submodule.add_mem _ ihu ihv
    | smul n u hu ihu => simpa using Submodule.smul_mem _ n ihu

theorem commonKernel_le_reduced [Nonempty Facet] (facets : Facet → Set ι) :
    coordinateCommonRestrictionKernel (G := G) facets ≤
      RedDist (Configuration ι G) := by
  intro u hu
  let ρ : Facet := Classical.choice inferInstance
  have huρ := (Submodule.mem_iInf (fun σ => LinearMap.ker
    (mapDist (coordinateRestriction (facets σ))))).mp hu ρ
  have he := LinearMap.congr_fun
    (augmentation_mapDist (coordinateRestriction (G := G) (facets ρ))) u
  rw [LinearMap.comp_apply, LinearMap.mem_ker.mp huρ, map_zero] at he
  exact he.symm

/-- For a nonempty facet family, the full common kernel is already reduced. -/
theorem map_reduced_commonKernel_eq [Nonempty Facet] (facets : Facet → Set ι) :
    (reducedCoordinateCommonRestrictionKernel (G := G) facets).map
      (RedDist (Configuration ι G)).subtype =
        coordinateCommonRestrictionKernel (G := G) facets := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_reducedCoordinateCommonRestrictionKernel_iff facets v).mp hv
  · intro hu
    let v : RedDist (Configuration ι G) := ⟨u, commonKernel_le_reduced facets hu⟩
    exact ⟨v, (mem_reducedCoordinateCommonRestrictionKernel_iff facets v).mpr hu, rfl⟩

/-- The report's elementary full-distribution identities agree exactly with
the earlier project's (apparently larger) arbitrary-increment reduced span. -/
theorem identityDistributions_eq_map_reducedIdentity [Nonempty Facet]
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (hd : Function.Surjective d) :
    identityDistributions facets d =
      (physicalNonfaceCubeSpan facets d).map (RedDist B).subtype := by
  rw [identityDistributions_eq_map_commonKernel facets d hd,
    ← map_reducedCoordinateCommonRestrictionKernel_eq_physicalNonfaceCubeSpan facets d hd,
    ← Submodule.map_comp]
  have he : (RedDist B).subtype.comp (mapRedDist d) =
      (mapDist d).comp (RedDist (Configuration ι G)).subtype := rfl
  rw [he, Submodule.map_comp, map_reduced_commonKernel_eq]

section ActualMarginals

variable {BAt : Facet → Type*} [∀ ρ, AddCommGroup (BAt ρ)]
variable (facets : Facet → Set ι) (d : Configuration ι G →+ B)
variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G) (BAt := BAt) d)

/-- The full-distribution numerator `D_inv`, using actual formal marginals. -/
def invariantDistributions : Submodule ℤ (Distribution B) :=
  ⨅ ρ, LinearMap.ker (mapDist (L.physicalRes ρ))

theorem identityDistributions_le_invariantDistributions
    (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) :
    identityDistributions facets d ≤ invariantDistributions facets d L := by
  rw [identityDistributions_eq_map_commonKernel facets d hd]
  rintro u ⟨v, hv, rfl⟩
  rw [invariantDistributions, Submodule.mem_iInf]
  intro ρ
  change mapDist (L.physicalRes ρ) (mapDist d v) = 0
  have heq : (mapDist (L.physicalRes ρ)).comp (mapDist d) =
      (mapDist (L.localD ρ)).comp (mapDist (coordinateRestriction (facets ρ))) := by
    ext c
    have hc := DFunLike.congr_fun (L.commutes ρ) c
    simp only [AddMonoidHom.comp_apply, hprimitive] at hc
    simp [hc]
  have hvρ := (Submodule.mem_iInf (fun σ => LinearMap.ker
    (mapDist (coordinateRestriction (facets σ))))).mp hv ρ
  have he := LinearMap.congr_fun heq v
  simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp hvρ, map_zero] using he

/-- The full integral quotient in equation (2.1). -/
abbrev FullTau := IntegralQuotient (identityDistributions facets d)
  (invariantDistributions facets d L)

/-- Closed local phase tables.  Membership is identified with the report's
literal difference-locality axiom by the next theorem. -/
def closedSPT (hd : Function.Surjective d) :
    Submodule ℤ (closedInvariant d) :=
  (annihilator (identityDistributions facets d)).comap
    (closedPhaseCharacterEquiv d hd).toLinearMap

theorem mem_closedSPT_iff (hd : Function.Surjective d) (φ : closedInvariant d) :
    φ ∈ closedSPT facets d hd ↔ DifferenceLocal facets φ.1 := by
  have h := differenceLocal_iff_annihilates_identity facets d hd
    (closedPhaseTableEquiv d hd φ)
  have he : (fun c => closedPhaseTableEquiv d hd φ (d c)) = φ.1 := by
    funext c
    exact closedPhaseTableEquiv_apply_image d hd φ c
  rw [he] at h
  exact h.symm

/-- The complete lookup-table identification with characters annihilating
the literal elementary identity subgroup. -/
def closedSPTCharacterEquiv (hd : Function.Surjective d) :
    closedSPT facets d hd ≃ₗ[ℤ] annihilator (identityDistributions facets d) :=
  (closedPhaseCharacterEquiv d hd).ofSubmodule'
    (annihilator (identityDistributions facets d))

/-- Restriction evaluation on the actual integer quotient. -/
def closedSPTRestriction (hd : Function.Surjective d) :
    closedSPT facets d hd →ₗ[ℤ] (FullTau facets d L →ₗ[ℤ] Phase) :=
  (restrictCharacter (identityDistributions facets d)
    (invariantDistributions facets d L)).comp
      (closedSPTCharacterEquiv facets d hd).toLinearMap

theorem closedSPTRestriction_surjective
    (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) :
    Function.Surjective (closedSPTRestriction facets d L hd) :=
  (restrictCharacter_surjective _ _
    (identityDistributions_le_invariantDistributions facets d L hprimitive hd)).comp
      (closedSPTCharacterEquiv facets d hd).surjective

/-- The actual phase denominator.  The next result identifies it with
facet-curvature sums, so no normalized/global-phase quotient is introduced. -/
def facetCurvaturePhases (hd : Function.Surjective d) :
    Submodule ℤ (closedSPT facets d hd) :=
  LinearMap.ker (closedSPTRestriction facets d L hd)

/-- The kernel is exactly the actual finite sum of curvature-facet tables
from equation (1.13), including constant summands. -/
theorem mem_facetCurvaturePhases_iff [Fintype Facet]
    (hd : Function.Surjective d) (φ : closedSPT facets d hd) :
    φ ∈ facetCurvaturePhases facets d L hd ↔
      ∃ k : ∀ ρ, BAt ρ → Phase,
        ∀ c, φ.1.1 c = ∑ ρ, k ρ (L.physicalRes ρ (d c)) := by
  change closedSPTCharacterEquiv facets d hd φ ∈
    LinearMap.ker (restrictCharacter (identityDistributions facets d)
      (invariantDistributions facets d L)) ↔ _
  rw [ker_restrictCharacter]
  change evaluate (closedPhaseTableEquiv d hd φ.1) ∈
    annihilator (invariantDistributions facets d L) ↔ _
  have hN : invariantDistributions facets d L =
      ⨅ ρ, LinearMap.ker (pushforward (L.physicalRes ρ)) := by
    simp only [invariantDistributions, pushforward_eq_mapDist]
  rw [hN, evaluation_annihilates_marginals_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun c => ?_⟩
    have h := hk (d c)
    simpa only [closedPhaseTableEquiv_apply_image] using h
  · rintro ⟨k, hk⟩
    refine ⟨k, fun a => ?_⟩
    obtain ⟨c, rfl⟩ := hd a
    simpa only [closedPhaseTableEquiv_apply_image] using hk c

/-- Proposition 2.1 as an algebraic isomorphism for the complete cochain
model; topology is a separate statement. -/
def closedSPTQuotientEquiv
    (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) :
    (closedSPT facets d hd ⧸ facetCurvaturePhases facets d L hd) ≃ₗ[ℤ]
      (FullTau facets d L →ₗ[ℤ] Phase) :=
  (closedSPTRestriction facets d L hd).quotKerEquivOfSurjective
    (closedSPTRestriction_surjective facets d L hprimitive hd)

section ReducedComparison

variable [Nonempty Facet]

theorem invariantDistributions_le_reduced :
    invariantDistributions facets d L ≤ RedDist B := by
  intro u hu
  let ρ : Facet := Classical.choice inferInstance
  have huρ := (Submodule.mem_iInf (fun σ => LinearMap.ker
    (mapDist (L.physicalRes σ)))).mp hu ρ
  have he := LinearMap.congr_fun (augmentation_mapDist (L.physicalRes ρ)) u
  rw [LinearMap.comp_apply, LinearMap.mem_ker.mp huρ, map_zero] at he
  exact he.symm

/-- The full and reduced invariant numerators are canonically identical;
this reduction applies to distributions, never to physical phase tables. -/
def invariantReductionEquiv :
    invariantDistributions facets d L ≃ₗ[ℤ]
      FacetRestrictionData.physicalInvariantDistributions L where
  toFun u := ⟨⟨u.1, invariantDistributions_le_reduced facets d L u.2⟩, by
    rw [FacetRestrictionData.physicalInvariantDistributions, Submodule.mem_iInf]
    intro ρ
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact (Submodule.mem_iInf (fun σ => LinearMap.ker
      (mapDist (L.physicalRes σ)))).mp u.2 ρ⟩
  invFun u := ⟨u.1.1, by
    rw [invariantDistributions, Submodule.mem_iInf]
    intro ρ
    have h := (Submodule.mem_iInf (fun σ => LinearMap.ker
      (FacetRestrictionData.restrictPhysicalRedDist L σ))).mp u.2 ρ
    exact congrArg Subtype.val (LinearMap.mem_ker.mp h)⟩
  left_inv u := rfl
  right_inv u := rfl
  map_add' u v := rfl
  map_smul' n u := rfl

theorem identity_reduction_iff (hd : Function.Surjective d)
    (u : invariantDistributions facets d L) :
    u ∈ identitiesInInvariant (identityDistributions facets d)
      (invariantDistributions facets d L) ↔
    invariantReductionEquiv facets d L u ∈
      FacetRestrictionData.physicalNonfaceCubeSpanInInvariantDistributions facets L := by
  change u.1 ∈ identityDistributions facets d ↔
    (invariantReductionEquiv facets d L u).1 ∈ physicalNonfaceCubeSpan facets d
  rw [identityDistributions_eq_map_reducedIdentity facets d hd]
  constructor
  · rintro ⟨v, hv, he⟩
    have hv' : v = (invariantReductionEquiv facets d L u).1 := Subtype.ext he
    exact hv' ▸ hv
  · intro hu
    exact ⟨(invariantReductionEquiv facets d L u).1, hu, rfl⟩

/-- The new full-distribution quotient is the previously proved `Tau`,
with equality of the actual identity subgroup, not an assumed comparison. -/
def fullTauEquivExistingTau (hd : Function.Surjective d) :
    FullTau facets d L ≃ₗ[ℤ] FacetRestrictionData.Tau facets L :=
  Submodule.Quotient.equiv _ _ (invariantReductionEquiv facets d L) (by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (identity_reduction_iff facets d L hd v).mp hv
    · intro hu
      let v := (invariantReductionEquiv facets d L).symm u
      refine ⟨v, ?_, (invariantReductionEquiv facets d L).apply_symm_apply u⟩
      apply (identity_reduction_iff facets d L hd v).mpr
      simpa [v] using hu)

end ReducedComparison

end ActualMarginals

end OpenDisk.PhaseDuality
