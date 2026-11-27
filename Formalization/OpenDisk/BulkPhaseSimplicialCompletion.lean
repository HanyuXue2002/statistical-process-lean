import Formalization.OpenDisk.BulkPhaseLocalCompletion
import Formalization.OpenDisk.ConePhaseSimplicialCapConverse

/-!
# Canonical local completion with actual simplicial boundary cochains

All cap locality and relative-primitive hypotheses of the general completion
equivalence are instantiated here by the actual simplicial coboundary and
carrier-normalized cone primitives. The remaining inputs are exactly global
boundary cochain exactness and the closed restriction-extension property of
the actual bulk. The latter is independent of the phase table.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace OpenDisk.BulkPhaseSimplicialCompletion

open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open ConePhaseSimplicialLocalLift BulkPhaseDifferentialModel

variable {V G P I : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P] [AddCommGroup I]
  [TopologicalSpace P] [IsTopologicalAddGroup P]
variable (K : AbstractSimplicialComplex V)

local instance simplexOrderCompletion (n : ℕ) : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- Positive-cochain-degree form of Theorem 4.3 on local full phase tables.
Every geometric local primitive has been constructed, and only the stated
global cochain exactness and actual-side closed extensions are required. -/
def simplicialLocalCompletionPositive (n : ℕ)
    (hexact : Function.Surjective (previousCoboundary (G := G) K n))
    (H : AddSubgroup (I × Cochain K (n + 1) G))
    (hclosed : ∀ a : H, a.val.2 ∈ (coboundaryToRange K (n + 1)).ker)
    (hext : ∀ z : (coboundaryToRange (G := G) K (n + 1)).ker,
      ∃ a : H, a.val.2 = z.val)
    (actualLocal : AddSubgroup (I × Cochain K (n + 1) G → P)) :=
  localCompletionContinuousAddEquiv (coboundaryToRange K (n + 1))
    (previousCoboundary K n) hexact H hclosed hext actualLocal
    (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
    (fun σ => facesIn K n σ) (simplex_mem_some_facesIn K (n + 1))
    (previousCoboundary_column K n) (simplicial_relativeCapLifts K n hexact)

/-- Degree-zero form, using global constants as the augmented previous
differential. Its surjectivity is the explicit connectedness input. -/
def simplicialLocalCompletionZero
    (hconnected : Function.Surjective (constantDifferential (G := G) K))
    (H : AddSubgroup (I × Cochain K 0 G))
    (hclosed : ∀ a : H, a.val.2 ∈ (coboundaryToRange K 0).ker)
    (hext : ∀ z : (coboundaryToRange (G := G) K 0).ker, ∃ a : H, a.val.2 = z.val)
    (actualLocal : AddSubgroup (I × Cochain K 0 G → P)) :=
  localCompletionContinuousAddEquiv (coboundaryToRange K 0)
    (constantDifferential K) hconnected H hclosed hext actualLocal
    (fun σ : NonemptySimplex K => facesIn K 0 σ)
    (fun _ => (Set.univ : Set Unit)) (simplex_mem_some_facesIn K 0)
    (fun _ _ hk _ => (hk (Set.mem_univ _)).elim) (constant_relativeCapLifts K hconnected)

end OpenDisk.BulkPhaseSimplicialCompletion
