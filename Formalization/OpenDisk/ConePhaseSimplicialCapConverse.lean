import Formalization.OpenDisk.ConePhaseSimplicialLocalLiftZero
import Formalization.OpenDisk.ConePhaseCapConverse

/-!
# Actual relative primitives for the cap converse

The carrier-normalized simplicial primitives prove every relative support
condition required by the cap-locality converse. The only remaining input is
global cochain exactness: surjectivity of the previous differential onto the
closed boundary cochains. For degree zero this is surjectivity of global
constants onto closed zero-cochains. These inputs are stated explicitly.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace OpenDisk.ConePhaseSimplicialLocalLift

open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open ConePhaseLocalLift

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]
variable (K : AbstractSimplicialComplex V)

local instance simplexOrderConverse (n : ℕ) : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

local instance simplexSumOrderConverse (n : ℕ) :
    LinearOrder (Simplex K n ⊕ Simplex K (n + 1)) :=
  inferInstanceAs (LinearOrder (Simplex K n ⊕ₗ Simplex K (n + 1)))

local instance zeroSumOrderConverse : LinearOrder (Unit ⊕ Simplex K 0) :=
  inferInstanceAs (LinearOrder (Unit ⊕ₗ Simplex K 0))

def normalizedCarrierPrimitive (ρ : NonemptySimplex K) (n : ℕ)
    (a : CoboundaryGroup (G := G) K n) : Cochain K n G := by
  cases n with
  | zero => exact carrierNormalizedPrimitiveZero K ρ a
  | succ m => exact carrierNormalizedPrimitiveSucc K m ρ a

@[simp] theorem coboundary_normalizedCarrierPrimitive (ρ : NonemptySimplex K) (n : ℕ)
    (a : CoboundaryGroup (G := G) K n) :
    coboundary K n (normalizedCarrierPrimitive K ρ n a) = a.val := by
  cases n with
  | zero => exact coboundary_carrierNormalizedPrimitiveZero K ρ a
  | succ m => exact coboundary_carrierNormalizedPrimitiveSucc K m ρ a

theorem restrict_normalizedCarrierPrimitive (ρ σ : NonemptySimplex K)
    (hρσ : ρ.val ⊆ σ.val) (n : ℕ) (a : CoboundaryGroup (G := G) K n) :
    coordinateRestriction (facesIn K n σ) (normalizedCarrierPrimitive K ρ n a) =
      simplexConeHomotopy K ρ σ hρσ (carrierApex K ρ) (carrierApex_mem K ρ) n
        (coordinateRestriction (facesIn K (n + 1) σ) a.val) := by
  cases n with
  | zero => exact restrictFacet_carrierNormalizedPrimitiveZero K ρ σ hρσ a
  | succ m => exact restrictFacet_carrierNormalizedPrimitiveSucc K m ρ σ hρσ a

/-- Genuine simplicial relative primitives discharge the whole cap-lifting
interface once global closed cochains are exact. -/
theorem simplicial_relativeCapLifts (n : ℕ)
    (hexact : Function.Surjective (previousCoboundary (G := G) K n)) :
    RelativeCapLifts (coboundaryToRange (G := G) K (n + 1))
      (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
      (fun σ => facesIn K n σ) (previousCoboundary K n) := by
  classical
  intro z marks hmarks
  obtain ⟨w, hw⟩ := hexact z
  by_cases hcommon : ∃ σ : NonemptySimplex K, ∀ e ∈ marks, e ∈ facesIn K (n + 1) σ
  · obtain ⟨σ₀, hσ₀⟩ := hcommon
    let vertices := marks.biUnion (fun e => e.val)
    have hvne : vertices.Nonempty := by
      obtain ⟨e, he⟩ := hmarks
      obtain ⟨v, hv⟩ := simplex_nonempty K e
      exact ⟨v, Finset.mem_biUnion.mpr ⟨e, he, hv⟩⟩
    have hvsub : vertices ⊆ σ₀.val := by
      intro v hv
      obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
      exact hσ₀ e he hve
    have hvmem : vertices ∈ K := (K.isRelLowerSet_faces σ₀.property).2 hvsub hvne
    let ρ : NonemptySimplex K := ⟨vertices, hvmem⟩
    let a : CoboundaryGroup (G := G) K n := ⟨z.val, ⟨w, congrArg Subtype.val hw⟩⟩
    refine ⟨normalizedCarrierPrimitive K ρ n a, ?_, ?_⟩
    · apply Subtype.ext
      exact coboundary_normalizedCarrierPrimitive K ρ n a
    · intro σ hσ hzσ
      have hρσ : ρ.val ⊆ σ.val := by
        intro v hv
        obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
        exact hσ e he hve
      rw [restrict_normalizedCarrierPrimitive K ρ σ hρσ n a]
      change simplexConeHomotopy K ρ σ hρσ (carrierApex K ρ) (carrierApex_mem K ρ) n
        (coordinateRestriction (facesIn K (n + 1) σ) z.val) = 0
      rw [hzσ, map_zero]
  · refine ⟨w, hw, ?_⟩
    intro σ hσ _
    exact (hcommon ⟨σ, hσ⟩).elim

theorem simplicial_cap_local_iff_of_exact (n : ℕ)
    (hexact : Function.Surjective (previousCoboundary (G := G) K n))
    (F : SymmetryPhase (coboundaryToRange (G := G) K (n + 1)) P) :
    DifferenceLocal
      (capFacets (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
        (fun σ => facesIn K n σ))
      (capPhase (coboundaryToRange K (n + 1)) (previousCoboundary K n) F) ↔
    RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
      (coboundaryToRange (G := G) K (n + 1)) F :=
  capPhase_local_iff _ _ _ (simplex_mem_some_facesIn K (n + 1))
    (previousCoboundary K n) (previousCoboundary_column K n)
    (simplicial_relativeCapLifts K n hexact) F

/-- The augmented degree-zero relative lift uses the actual constant map. -/
theorem constant_relativeCapLifts
    (hconnected : Function.Surjective (constantDifferential (G := G) K)) :
    RelativeCapLifts (coboundaryToRange (G := G) K 0)
      (fun σ : NonemptySimplex K => facesIn K 0 σ)
      (fun _ => (Set.univ : Set Unit)) (constantDifferential K) := by
  classical
  intro z marks hmarks
  obtain ⟨w, hw⟩ := hconnected z
  refine ⟨w, hw, ?_⟩
  intro σ hσ hzσ
  obtain ⟨e, he⟩ := hmarks
  have heσ := hσ e he
  have hz := congrArg (fun c => c ⟨e, heσ⟩) hzσ
  change z.val e = 0 at hz
  have hwval : w Unit.unit = 0 := by
    have hh := congrArg (fun t => t.val e) hw
    exact hh.trans hz
  have hwzero : w = 0 := by
    apply Finsupp.ext
    intro u
    cases u
    exact hwval
  rw [hwzero, map_zero]

theorem simplicial_cap_local_zero_iff_of_connected
    (hconnected : Function.Surjective (constantDifferential (G := G) K))
    (F : SymmetryPhase (coboundaryToRange (G := G) K 0) P) :
    DifferenceLocal
      (capFacets (fun σ : NonemptySimplex K => facesIn K 0 σ)
        (fun _ => (Set.univ : Set Unit)))
      (capPhase (coboundaryToRange K 0) (constantDifferential K) F) ↔
    RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K 0 σ)
      (coboundaryToRange (G := G) K 0) F :=
  capPhase_local_iff _ _ _ (simplex_mem_some_facesIn K 0)
    (constantDifferential K) (fun _ _ hk _ => (hk (Set.mem_univ _)).elim)
    (constant_relativeCapLifts K hconnected) F

end OpenDisk.ConePhaseSimplicialLocalLift
