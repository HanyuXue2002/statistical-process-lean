import Formalization.OpenDisk.StarLocality

set_option linter.style.header false

/-!
# Closed marked phases are simplex-curvature sums

This file identifies each literal marked-local, globally closed hopping row
with a closed local phase on the geometric closed star. Closed-star extension
is proved by the actual cone contraction, not assumed. The resulting local
curvature parametrization supplies paths in all such hopping rows.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]

variable (K : AbstractSimplicialComplex V) (n : ℕ)

local instance faceCoordinateOrder : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

local instance simplexFintype : Fintype (NonemptySimplex K) := Fintype.ofFinite _

abbrev simplicialFacets : NonemptySimplex K → Set (Simplex K n) := facesIn K n

abbrev CarrierFacets (η : Simplex K n) :=
  {σ : NonemptySimplex K // ∀ i ∈ ({η} : Finset (Simplex K n)), i ∈ facesIn K n σ}

local instance carrierFacetFintype (η : Simplex K n) : Fintype (CarrierFacets K n η) :=
  Fintype.ofFinite _

theorem carrierFacetContains (η : Simplex K n) (ρ : CarrierFacets K n η) :
    (forgetDimension K η).val ⊆ ρ.val.val :=
  ρ.property η (Finset.mem_singleton_self _)

def restrictedMarkedPhase (η : Simplex K n) (f : Cochain K n G → P) :
    ClosedStarCochain K (forgetDimension K η) n G → P :=
  fun c => f (extendCarrierClosedStar K (forgetDimension K η) n c)

/-- Marked locality implies dependence only on the actual closed-star coordinates. -/
theorem marked_phase_factor (η : Simplex K n) (f : Cochain K n G → P)
    (hf : MarkedLocal (simplicialFacets K n) {η} f) (c : Cochain K n G) :
    f c = restrictedMarkedPhase K n η f (restrictClosedStar K (forgetDimension K η) n c) := by
  obtain ⟨g, hg⟩ := (differenceLocal_iff_facetSum _ f).mp
    ((differenceLocal_iff_anchoredLocal _ f).mpr hf)
  unfold restrictedMarkedPhase
  rw [hg c, hg]
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply congrArg (g ρ)
  change restrictCochain K n ρ.val c = restrictCochain K n ρ.val
    (extendCarrierClosedStar K (forgetDimension K η) n
      (restrictClosedStar K (forgetDimension K η) n c))
  rw [restrictSimplex_extendStar K _ _ (carrierFacetContains K n η ρ),
    restrictSimplex_restrictStar]

theorem marked_phase_eq_of_star_eq (η : Simplex K n) (f : Cochain K n G → P)
    (hf : MarkedLocal (simplicialFacets K n) {η} f) (c c' : Cochain K n G)
    (heq : restrictClosedStar K (forgetDimension K η) n c =
      restrictClosedStar K (forgetDimension K η) n c') : f c = f c' := by
  rw [marked_phase_factor K n η f hf c, marked_phase_factor K n η f hf c', heq]

theorem restrictedMarkedPhase_starLocal (η : Simplex K n) (f : Cochain K n G → P)
    (hf : MarkedLocal (simplicialFacets K n) {η} f) :
    ConePhaseLocal.StarLocal K (forgetDimension K η)
      (fun ρ : CarrierFacets K n η => ρ.val) (carrierFacetContains K n η) n
      (restrictedMarkedPhase K n η f) := by
  obtain ⟨g, hg⟩ := (differenceLocal_iff_facetSum _ f).mp
    ((differenceLocal_iff_anchoredLocal _ f).mpr hf)
  refine ⟨g, fun c => ?_⟩
  unfold restrictedMarkedPhase
  rw [hg]
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply congrArg (g ρ)
  exact restrictSimplex_extendStar K _ _ (carrierFacetContains K n η ρ) n c

/-- Global closed invariance gives invariance under every closed star cochain,
because the required closed extension is constructed explicitly. -/
theorem restrictedMarkedPhase_closed (η : Simplex K n) (f : Cochain K n G → P)
    (hf : MarkedLocal (simplicialFacets K n) {η} f)
    (hclosed : phaseDerivative (coboundaryToRange K n) f = 0)
    (z : ConePhaseSimplicial.closedCochains (G := G) K (forgetDimension K η) n)
    (c : ClosedStarCochain K (forgetDimension K η) n G) :
    restrictedMarkedPhase K n η f (c + z) = restrictedMarkedPhase K n η f c := by
  obtain ⟨w, hwclosed, hwres⟩ := exists_global_closed_extension K (forgetDimension K η)
    (simplexApex K η) (simplexApex_mem K η) n z.val z.property
  let zw : (coboundaryToRange (G := G) K n).ker := ⟨w, Subtype.ext hwclosed⟩
  let ec := extendCarrierClosedStar K (forgetDimension K η) n c
  have hinv := congrArg (fun F : SymmetryPhase (coboundaryToRange K n) P => F zw ec) hclosed
  change f (ec + w) - f ec = 0 at hinv
  calc
    restrictedMarkedPhase K n η f (c + z) = f (ec + w) := by
      apply marked_phase_eq_of_star_eq K n η f hf
      simp only [map_add, restrictClosedStar_extendCarrierClosedStar, hwres, ec]
    _ = restrictedMarkedPhase K n η f c := sub_eq_zero.mp hinv

def globalMarkedCurvatureSum (η : Simplex K n)
    (k : ∀ ρ : CarrierFacets K n η, Configuration (facesIn K (n + 1) ρ.val) G → P)
    (c : Cochain K n G) : P :=
  ∑ ρ, k ρ (restrictCochain K (n + 1) ρ.val (coboundary K n c))

/-- Every globally closed marked row has a concrete simplex-curvature decomposition. -/
theorem exists_globalMarkedCurvatureSum (η : Simplex K n) (f : Cochain K n G → P)
    (hf : MarkedLocal (simplicialFacets K n) {η} f)
    (hclosed : phaseDerivative (coboundaryToRange K n) f = 0) :
    ∃ k, f = globalMarkedCurvatureSum K n η k := by
  obtain ⟨k, hk⟩ := ConePhaseLocal.exists_curvatureSum K (forgetDimension K η)
    (simplexApex K η) (simplexApex_mem K η)
    (fun ρ : CarrierFacets K n η => ρ.val) (carrierFacetContains K n η) n
    (restrictedMarkedPhase_starLocal K n η f hf)
    (restrictedMarkedPhase_closed K n η f hf hclosed)
  refine ⟨k, ?_⟩
  funext c
  rw [marked_phase_factor K n η f hf c, hk]
  unfold ConePhaseLocal.curvatureSum globalMarkedCurvatureSum
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply congrArg (k ρ)
  have hn := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) K (forgetDimension K η) n) c
  simp only [LinearMap.comp_apply] at hn
  rw [← hn, restrictSimplex_restrictStar]

theorem globalMarkedCurvatureSum_marked (η : Simplex K n)
    (k : ∀ ρ : CarrierFacets K n η, Configuration (facesIn K (n + 1) ρ.val) G → P) :
    MarkedLocal (simplicialFacets K n) {η} (globalMarkedCurvatureSum K n η k) := by
  apply (differenceLocal_iff_anchoredLocal _ _).mp
  apply (differenceLocal_iff_facetSum _ _).mpr
  refine ⟨fun ρ a => k ρ (localCoboundary K n ρ.val a), fun c => ?_⟩
  unfold globalMarkedCurvatureSum
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply congrArg (k ρ)
  exact DFunLike.congr_fun (restrictCochain_coboundary (G := G) K n ρ.val) c

theorem globalMarkedCurvatureSum_closed (η : Simplex K n)
    (k : ∀ ρ : CarrierFacets K n η, Configuration (facesIn K (n + 1) ρ.val) G → P) :
    phaseDerivative (coboundaryToRange K n) (globalMarkedCurvatureSum K n η k) = 0 := by
  ext z c
  have hz : coboundary K n (z : Cochain K n G) = 0 := congrArg Subtype.val z.property
  change globalMarkedCurvatureSum K n η k (c + z) - globalMarkedCurvatureSum K n η k c = 0
  simp only [globalMarkedCurvatureSum, map_add, hz, add_zero, sub_self]

end OpenDisk.StarLocality
