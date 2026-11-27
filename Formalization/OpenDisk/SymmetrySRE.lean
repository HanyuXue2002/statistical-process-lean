import Formalization.OpenDisk.SymmetryComponentSpace
import Formalization.OpenDisk.InvariantStates

/-! # The SRE criterion on the actual zero path component -/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [Nonempty Facet]

/-- Propositions 3.4 and 3.5 together: the trivial component is exactly SRE realizability. -/
theorem sre_iff_zero_component (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    [Fintype d.ker] (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)
    (F : localSymmetries facets d (P := CirclePhase)) :
    (∃ β : Configuration ι G → CirclePhase,
      DifferenceLocal facets β ∧ phaseState β ∈ invariantSpace d F.val) ↔
      Joined (0 : localSymmetries facets d (P := CirclePhase)) F := by
  rw [localSymmetry_joined_zero_iff facets d rep hrep F]
  constructor
  · rintro ⟨β, hβ, hinv⟩
    exact ⟨β, (differenceLocal_iff_anchoredLocal facets β).1 hβ,
      ((phaseState_mem_iff d F.val β).1 hinv).symm⟩
  · rintro ⟨β, hβ, heq⟩
    exact ⟨β, (differenceLocal_iff_anchoredLocal facets β).2 hβ,
      (phaseState_mem_iff d F.val β).2 heq.symm⟩

end OpenDisk
