import Formalization.OpenDisk.SameStatistics
import Formalization.OpenDisk.ConditionalRange
import Formalization.OpenDisk.BulkPhase

/-!
# Actual encodings and hoppings for equal complete statistics

The local correction is derived from the proved joint kernel, while closed
invariance is derived from the two response equations. The displayed encoding
and hopping identities are equalities of actual complex coefficient vectors.
-/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk
open BulkPhaseHilbert

variable {I C : Type*} [Fintype I] [Fintype C]

def hilbertDiagonal (φ : I × C → CirclePhase) (ψ : EuclideanSpace ℂ (I × C)) :
    EuclideanSpace ℂ (I × C) := WithLp.toLp 2 (fun c => phaseWeight (φ c) * ψ c)

theorem conditional_realization_intertwines (φ₀ φ₁ : I × C → CirclePhase)
    (γ : C → CirclePhase) (ψ : EuclideanSpace ℂ C) :
    hilbertDiagonal (fun c => φ₁ c - φ₀ c + γ c.2)
      (conditionalLinear circleCharacter φ₀ ψ) =
      conditionalLinear circleCharacter φ₁
        (WithLp.toLp 2 (fun b => phaseWeight (γ b) * ψ b)) := by
  ext c
  change phaseWeight (φ₁ c - φ₀ c + γ c.2) *
    (normalization I * phaseWeight (φ₀ c) * ψ c.2) =
    normalization I * phaseWeight (φ₁ c) * (phaseWeight (γ c.2) * ψ c.2)
  have hp : phaseWeight (φ₁ c - φ₀ c + γ c.2) * phaseWeight (φ₀ c) =
      phaseWeight (φ₁ c) * phaseWeight (γ c.2) := by
    rw [← phaseWeight_add, ← phaseWeight_add]
    congr 1
    abel
  calc
    _ = normalization I *
      (phaseWeight (φ₁ c - φ₀ c + γ c.2) * phaseWeight (φ₀ c)) * ψ c.2 := by ring
    _ = _ := by rw [hp]; ring

section Bulk

variable {M B P ι G Facet : Type*} [AddCommGroup M] [AddCommGroup B]
  [AddCommGroup P] [LinearOrder ι] [AddCommGroup G] [Nonempty Facet]
  (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)

def cochainBulkSystem (r : M →+ Configuration ι G) (Z : AddSubgroup M)
    (hz : ∀ z : Z, d (r z) = 0) : BulkPhase.System M (Configuration ι G) where
  restriction := r
  bulkClosed := Z
  boundaryClosed := d.ker
  restriction_closed := hz

include hrep in
/-- Same complete statistics supplies the local boundary correction, and
the response equations prove that the resulting bulk correction is closed. -/
theorem same_statistics_bulk_correction
    (r : M →+ Configuration ι G) (Z : AddSubgroup M) (hz : ∀ z : Z, d (r z) = 0)
    (φ₀ φ₁ : M → P) (x y : LocalJointPhase facets d P)
    (hθ : forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x =
      forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep y)
    (h₀ : BulkPhase.HasResponse (cochainBulkSystem d r Z hz) φ₀
      (fun z v => phaseDerivative d x.val.1 z v))
    (h₁ : BulkPhase.HasResponse (cochainBulkSystem d r Z hz) φ₁
      (fun z v => phaseDerivative d y.val.1 z v)) :
    DifferenceLocal facets (y.val.1 - x.val.1) ∧
      BulkPhase.ClosedInvariant Z
        (BulkPhase.realizationCorrection r φ₀ φ₁ (y.val.1 - x.val.1)) := by
  refine ⟨(same_statistics_local_difference facets d rep hrep x y hθ).1, ?_⟩
  exact BulkPhase.realizationCorrection_closed (cochainBulkSystem d r Z hz)
    h₀ h₁ x.val.1 y.val.1 (y.val.1 - x.val.1) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)

include hrep in
/-- The actual bulk hopping has the same diagonal intertwiner as its encoding. -/
theorem same_statistics_bulk_hopping
    (r : M →+ Configuration ι G) (φ₀ φ₁ : M → CirclePhase)
    (x y : LocalJointPhase facets d CirclePhase)
    (hθ : forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x =
      forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep y)
    (e : ElementaryLabel ι G) (t : M) (ht : r t = elementaryStep e) (ψ : M → ℂ) :
    diagonalEquiv (BulkPhase.realizationCorrection r φ₀ φ₁ (y.val.1 - x.val.1))
      (hoppingEquiv (fun c => x.val.2 e (r c) + difference φ₀ t c) t ψ) =
    hoppingEquiv (fun c => y.val.2 e (r c) + difference φ₁ t c) t
      (diagonalEquiv (BulkPhase.realizationCorrection r φ₀ φ₁ (y.val.1 - x.val.1)) ψ) := by
  have hL := (same_statistics_local_difference facets d rep hrep x y hθ).2 e
  have heq : (fun c => y.val.2 e (r c) + difference φ₁ t c) =
      (fun c => x.val.2 e (r c) + difference φ₀ t c) +
        difference (BulkPhase.realizationCorrection r φ₀ φ₁ (y.val.1 - x.val.1)) t := by
    funext c
    have hh := congrFun hL (r c)
    simp only [Pi.sub_apply] at hh
    rw [sub_eq_iff_eq_add] at hh
    simp only [BulkPhase.realizationCorrection, difference, Pi.add_apply, Pi.sub_apply, map_add, ht]
    simp only [difference, Pi.sub_apply] at hh
    rw [hh]
    abel
  rw [heq]
  exact diagonal_hopping_intertwines _ _ _ _

end Bulk
end OpenDisk
