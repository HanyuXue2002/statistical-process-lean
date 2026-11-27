import Formalization.OpenDisk.PhaseDualityAveraging
import Formalization.OpenDisk.PhaseDualityComponents
import Formalization.OpenDisk.CirclePaths
import Mathlib.Topology.Connected.TotallyDisconnected

set_option linter.style.header false

/-!
# The actual zero path component and finite closed-SPT quotient

Circle-covering path lifting and the finite closed-shift averaging theorem
identify the identity path component with facet-curvature phase sums.
Finite generation of integral distributions proves that there are only
finitely many such components.  No Lie-group classification is assumed.
-/

noncomputable section

open GeneralSphereT.PathAlgebra
open scoped unitInterval

namespace OpenDisk.PhaseDuality

section CharacterRoots

variable {X : Type*}

/-- A literal integral distribution gives a continuous additive phase equation. -/
def distributionEquation (u : Distribution X) : (X → Phase) →+ Phase :=
  ((LinearMap.applyₗ (R := ℤ) u).comp phaseTableEquiv.toLinearMap).toAddMonoidHom

theorem continuous_distributionEquation (u : Distribution X) :
    Continuous (distributionEquation u) := continuous_evaluate_distribution u

/-- Every based path in an actual distribution-annihilator has an `n`-th
root endpoint in the same annihilator. -/
theorem annihilator_root_of_path (J : Submodule ℤ (Distribution X))
    (n : ℕ) [NeZero n] (x : annihilator J) (p : Path (0 : annihilator J) x) :
    ∃ y : annihilator J, n • y = x := by
  let R := fun u : J => distributionEquation (u : Distribution X)
  let E := phaseTableEquiv (X := X)
  let β (t : unitInterval) : CirclePaths.equationSubgroup R :=
    ⟨E.symm (p t).1, by
      rw [CirclePaths.mem_equationSubgroup]
      intro u
      change E (E.symm (p t).1) u.1 = 0
      rw [E.apply_symm_apply]
      exact (p t).2 u.1 u.2⟩
  let q : Path (0 : CirclePaths.equationSubgroup R) (β 1) :=
    { toFun := β
      continuous_toFun :=
        (continuous_phaseTableEquiv_symm.comp
          (continuous_subtype_val.comp p.continuous)).subtype_mk _
      source' := by
        apply Subtype.ext
        change E.symm (p 0).1 = 0
        rw [p.source]
        exact E.symm.map_zero
      target' := rfl }
  obtain ⟨y, _hyPath, hy⟩ := CirclePaths.root_path R
    (fun u => continuous_distributionEquation u.1) n (β 1) q
  let χ : annihilator J := ⟨E y.1, by
    intro u hu
    exact (CirclePaths.mem_equationSubgroup R y.1).1 y.2 ⟨u, hu⟩⟩
  refine ⟨χ, ?_⟩
  apply Subtype.ext
  have hval := congrArg Subtype.val hy
  change n • y.1 = E.symm (p 1).1 at hval
  rw [p.target] at hval
  change n • E y.1 = x.1
  rw [← map_nsmul, hval, E.apply_symm_apply]

end CharacterRoots

section ClosedPhases

variable {ι G B Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable [Fintype Facet]
variable (facets : Facet → Set ι) (d : Configuration ι G →+ B)
variable {BAt : Facet → Type*} [∀ ρ, AddCommGroup (BAt ρ)]
variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G) (BAt := BAt) d)
variable [Fintype d.ker]
variable (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
variable (hd : Function.Surjective d)
variable (hExt : ∀ ρ (z : Configuration (facets ρ) G), L.localD ρ z = 0 →
  ∃ w : Configuration ι G, d w = 0 ∧ L.primitiveRes ρ w = z)

include hprimitive hExt

/-- The nontrivial implication in the identity-component assertion. -/
theorem closedSPT_path_endpoint_mem_facetCurvature
    (φ : closedSPT facets d hd) (p : Path (0 : closedSPT facets d hd) φ) :
    φ ∈ facetCurvaturePhases facets d L hd := by
  let E := closedSPTCharacterEquiv facets d hd
  let q : Path (0 : annihilator (identityDistributions facets d)) (E φ) :=
    { toFun := fun t => E (p t)
      continuous_toFun := (continuous_closedSPTCharacterEquiv facets d hd).comp p.continuous
      source' := by rw [p.source, map_zero]
      target' := by rw [p.target] }
  obtain ⟨y, hy⟩ := annihilator_root_of_path (identityDistributions facets d)
    (Fintype.card d.ker) (E φ) q
  have hbound := closedSPT_card_smul_mem_facetCurvature facets d L hprimitive hd hExt (E.symm y)
  have heq : Fintype.card d.ker • E.symm y = φ := by
    apply E.injective
    rw [map_nsmul, E.apply_symm_apply, hy]
  rwa [heq] at hbound

/-- The identity path component is exactly the actual local-curvature
phase subgroup, including the global phase. -/
theorem closedSPT_joined_zero_iff
    (φ : closedSPT facets d hd) :
    Joined (0 : closedSPT facets d hd) φ ↔ φ ∈ facetCurvaturePhases facets d L hd := by
  constructor
  · rintro ⟨p⟩
    exact closedSPT_path_endpoint_mem_facetCurvature facets d L hprimitive hd hExt φ p
  · intro hφ
    letI := facetCurvaturePhases_pathConnectedSpace facets d L hprimitive hd
    have h := (PathConnectedSpace.joined
      (0 : facetCurvaturePhases facets d L hd) ⟨φ, hφ⟩).map continuous_subtype_val
    exact h

/-- Any path has constant image in the actual phase quotient. -/
theorem closedSPT_path_quotient_eq
    {φ ψ : closedSPT facets d hd} (p : Path φ ψ) :
    (facetCurvaturePhases facets d L hd).mkQ φ =
      (facetCurvaturePhases facets d L hd).mkQ ψ := by
  let q : Path (0 : closedSPT facets d hd) (ψ - φ) := by
    simpa only [sub_self] using p.map
      (show Continuous (fun z : closedSPT facets d hd => z - φ) from
        continuous_id.sub continuous_const)
  have h := closedSPT_path_endpoint_mem_facetCurvature facets d L hprimitive hd hExt (ψ - φ) q
  have hz := (Submodule.Quotient.mk_eq_zero (facetCurvaturePhases facets d L hd)).mpr h
  change (facetCurvaturePhases facets d L hd).mkQ (ψ - φ) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

omit hprimitive hExt in
/-- Finitely many actual path components of the closed local table space. -/
theorem finite_closedSPT_components [Fintype B] :
    Finite (ZerothHomotopy (closedSPT facets d hd)) := by
  letI := finite_annihilator_components (identityDistributions facets d)
  exact finite_zerothHomotopy_of_surjective (closedSPTCharacterEquiv facets d hd).symm
    (continuous_closedSPTCharacterEquiv_symm facets d hd)
    (closedSPTCharacterEquiv facets d hd).symm.surjective

/-- The closed-SPT quotient is a genuinely finite group, proved from
finite integer phase tables and the actual path-component identification. -/
theorem finite_closedSPT_quotient [Fintype B] :
    Finite (closedSPT facets d hd ⧸ facetCurvaturePhases facets d L hd) := by
  letI := finite_closedSPT_components facets d hd
  let F : ZerothHomotopy (closedSPT facets d hd) →
      (closedSPT facets d hd ⧸ facetCurvaturePhases facets d L hd) :=
    ZerothHomotopy.lift (facetCurvaturePhases facets d L hd).mkQ
      (fun {_ _} p => closedSPT_path_quotient_eq facets d L hprimitive hd hExt p)
  apply Finite.of_surjective F
  intro x
  obtain ⟨φ, rfl⟩ := (facetCurvaturePhases facets d L hd).mkQ_surjective x
  exact ⟨ZerothHomotopy.mk φ, rfl⟩

/-- The ordinary connected component also equals the same subgroup.  This
follows from the proved finite Hausdorff character quotient, rather than an
unformalized assertion that connected compact groups are path connected. -/
theorem closedSPT_mem_connectedComponent_zero_iff [Fintype B]
    (φ : closedSPT facets d hd) :
    φ ∈ connectedComponent (0 : closedSPT facets d hd) ↔
      φ ∈ facetCurvaturePhases facets d L hd := by
  letI := finite_closedSPT_quotient facets d L hprimitive hd hExt
  letI : Finite (FullTau facets d L →ₗ[ℤ] Phase) :=
    Finite.of_equiv _ (closedSPTQuotientEquiv facets d L hprimitive hd).toEquiv
  letI : DiscreteTopology (FullTau facets d L →ₗ[ℤ] Phase) := inferInstance
  constructor
  · intro hφ
    have h := isPreconnected_connectedComponent.constant
      (continuous_closedSPTRestriction facets d L hd).continuousOn hφ mem_connectedComponent
    change closedSPTRestriction facets d L hd φ = 0
    simpa only [map_zero] using h
  · intro hφ
    exact pathComponent_subset_component _
      ((closedSPT_joined_zero_iff facets d L hprimitive hd hExt φ).mpr hφ)

end ClosedPhases

end OpenDisk.PhaseDuality
