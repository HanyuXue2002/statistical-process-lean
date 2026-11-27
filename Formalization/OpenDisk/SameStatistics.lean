import Formalization.OpenDisk.JointLocality
import Formalization.OpenDisk.HoppingOperators

/-!
# Exact same-statistics realizations

Equality is equality of the complete excitation tables, not merely of their
path components. It forces a unique local phase difference and simultaneous
conjugacy of every hopping operator by that phase. The constant component is
retained because the two complete phase tables are retained.
-/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P] [Nonempty Facet]
  (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)

include hrep in
theorem same_statistics_local_difference (x y : LocalJointPhase facets d P)
    (h : forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x =
      forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep y) :
    DifferenceLocal facets (y.val.1 - x.val.1) ∧
      ∀ e, y.val.2 e - x.val.2 e = difference (y.val.1 - x.val.1) (elementaryStep e) := by
  have hz : forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep (y - x) = 0 := by
    rw [map_sub, h, sub_self]
  exact (local_excitation_kernel facets d rep hrep (y - x)).1 hz

include hrep in
/-- The physical full-table statement, including uniqueness of the local correction. -/
theorem same_statistics_unique_local_phase (x y : LocalJointPhase facets d P)
    (h : forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x =
      forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep y) :
    ∃! γ : Configuration ι G → P, DifferenceLocal facets γ ∧
      y.val.1 = x.val.1 + γ ∧
      ∀ e, y.val.2 e = x.val.2 e + difference γ (elementaryStep e) := by
  obtain ⟨hloc, hhop⟩ := same_statistics_local_difference facets d rep hrep x y h
  refine ⟨y.val.1 - x.val.1, ⟨hloc, ?_, ?_⟩, ?_⟩
  · abel
  · intro e; rw [← hhop e]; abel
  · intro γ hγ
    rw [hγ.2.1]
    abel

include hrep in
/-- All actual hopping matrices are intertwined by the same local diagonal. -/
theorem same_statistics_hopping_intertwines (x y : LocalJointPhase facets d CirclePhase)
    (h : forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x =
      forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep y)
    (e : ElementaryLabel ι G) (ψ : Configuration ι G → ℂ) :
    diagonalEquiv (y.val.1 - x.val.1) (hoppingEquiv (x.val.2 e) (elementaryStep e) ψ) =
      hoppingEquiv (y.val.2 e) (elementaryStep e) (diagonalEquiv (y.val.1 - x.val.1) ψ) := by
  have hh := (same_statistics_local_difference facets d rep hrep x y h).2 e
  have hy : y.val.2 e = x.val.2 e + difference (y.val.1 - x.val.1) (elementaryStep e) := by
    rw [← hh]; abel
  rw [hy]
  exact diagonal_hopping_intertwines _ _ _ _

include hrep in
/-- The same correction conjugates the literal embedded invariant subspaces. -/
theorem same_statistics_invariant_spaces (x y : LocalJointPhase facets d CirclePhase)
    (h : forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x =
      forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep y) :
    DifferenceLocal facets (y.val.1 - x.val.1) ∧
    diagonalEquiv (y.val.1 - x.val.1) ''
      (invariantSpace d (phaseDerivative d x.val.1) : Set (Configuration ι G → ℂ)) =
      (invariantSpace d (phaseDerivative d y.val.1) : Set (Configuration ι G → ℂ)) := by
  refine ⟨(same_statistics_local_difference facets d rep hrep x y h).1, ?_⟩
  rw [diagonal_image_invariantSpace]
  have hf : phaseDerivative d x.val.1 + phaseDerivative d (y.val.1 - x.val.1) =
      phaseDerivative d y.val.1 := by rw [map_sub]; abel
  rw [hf]

end OpenDisk
