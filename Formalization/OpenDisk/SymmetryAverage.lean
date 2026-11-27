import Formalization.OpenDisk.Symmetry
import Mathlib.Algebra.Group.Translate
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Integral averaging and the annihilator bound

The averaging identity used in Proposition 3.4 is proved inside the phase
group itself. In particular it does not divide circle-valued phases by the
order of the closed-shift group. The topological identification of the
identity component is not assumed or claimed by this algebraic file.
-/

noncomputable section
open scoped BigOperators

namespace OpenDisk

variable {C A P : Type*} [AddCommGroup C] [AddCommGroup A] [AddCommGroup P]
variable (d : C →+ A) [Fintype d.ker]

/-- The integral phase chosen in the averaging proof: minus the sum of all rows. -/
def averagePhase (F : SymmetryPhase d P) : C → P := fun v => -∑ z, F z v

theorem phaseDerivative_average (F : SymmetryPhase d P) :
    phaseDerivative d (averagePhase d F) = Fintype.card d.ker • F := by
  ext z v
  have hsum : (∑ w : d.ker, F (z + w) v) = ∑ w : d.ker, F w v :=
    Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun _ => rfl)
  simp only [F.property.2, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ] at hsum
  change -(∑ w : d.ker, F w (v + z)) - -(∑ w : d.ker, F w v) =
    Fintype.card d.ker • F z v
  rw [← hsum]
  abel

/-- Any additive local-function subgroup containing every row also contains
the integral averaged phase. -/
theorem averagePhase_mem (Loc : AddSubgroup (C → P)) (F : SymmetryPhase d P)
    (hrows : ∀ z, (fun v => F z v) ∈ Loc) : averagePhase d F ∈ Loc := by
  have hs : (∑ z : d.ker, fun v => F z v) ∈ Loc :=
    Loc.sum_mem (fun z _ => hrows z)
  have heq : averagePhase d F = -(∑ z : d.ker, fun v => F z v) := by
    funext v
    simp [averagePhase]
  rw [heq]
  exact Loc.neg_mem hs

/-- The exact finite-order bound used before the compact-group argument. -/
theorem card_nsmul_mem_localDerivative (Loc : AddSubgroup (C → P))
    (F : SymmetryPhase d P) (hrows : ∀ z, (fun v => F z v) ∈ Loc) :
    Fintype.card d.ker • F ∈ Loc.map (phaseDerivative d) := by
  exact ⟨averagePhase d F, averagePhase_mem d Loc F hrows, phaseDerivative_average d F⟩

end OpenDisk
