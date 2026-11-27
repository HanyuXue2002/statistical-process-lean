import Formalization.OpenDisk.SymmetryComponents
import Formalization.OpenDisk.JointTopology
import Formalization.OpenDisk.PhaseDualityComponents

/-!
# Literal local symmetry spaces and their path components

This file supplies the actual subgroup topology, proves both directions of
the zero-component criterion, and establishes finiteness of components from
integer equations on a finite table. Constants remain part of every phase table.
-/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P]

/-- Symmetry cocycles satisfying the report's intrinsic restriction locality. -/
def localSymmetries (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    AddSubgroup (SymmetryPhase d P) where
  carrier := {F | RestrictionSymmetryLocal facets d F}
  zero_mem' := by
    intro z steps hne ha hf v
    change iteratedPhaseDifference _ (0 : Configuration ι G → P) v = 0
    rw [← iteratedPhaseDiffHom_apply, map_zero]
    rfl
  add_mem' := by
    intro F H hF hH z steps hne ha hf v
    have h₁ := hF z steps hne ha hf v
    have h₂ := hH z steps hne ha hf v
    change iteratedPhaseDifference _ ((fun v => F z v) + (fun v => H z v)) v = 0
    rw [← iteratedPhaseDiffHom_apply, map_add]
    change iteratedPhaseDiffHom _ (fun v => F z v) v +
      iteratedPhaseDiffHom _ (fun v => H z v) v = 0
    rw [iteratedPhaseDiffHom_apply, iteratedPhaseDiffHom_apply, h₁, h₂, zero_add]
  neg_mem' := by
    intro F hF z steps hne ha hf v
    have h := hF z steps hne ha hf v
    change iteratedPhaseDifference _ (-(fun v => F z v)) v = 0
    rw [← iteratedPhaseDiffHom_apply, map_neg]
    change -(iteratedPhaseDiffHom _ (fun v => F z v) v) = 0
    rw [iteratedPhaseDiffHom_apply, h, neg_zero]

variable [Nonempty Facet]

def localDerivative (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    localFunctionSubgroup (G := G) facets P →+ localSymmetries facets d (P := P) where
  toFun γ := ⟨phaseDerivative d γ.val, local_phase_derivative_local facets d γ⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' γ δ := by apply Subtype.ext; exact map_add _ _ _

theorem continuous_localDerivative [TopologicalSpace P] [IsTopologicalAddGroup P]
    (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    Continuous (localDerivative (P := P) facets d) :=
  ((continuous_phaseDerivative d).comp continuous_subtype_val).subtype_mk _

/-- Proposition 3.4, expressed using paths in the literal local symmetry space. -/
theorem localSymmetry_joined_zero_iff (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) [Fintype d.ker]
    (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)
    (F : localSymmetries facets d (P := CirclePaths.Phase)) :
    Joined (0 : localSymmetries facets d (P := CirclePaths.Phase)) F ↔
      F.val ∈ (localFunctionSubgroup (G := G) facets CirclePaths.Phase).map
        (phaseDerivative d) := by
  constructor
  · rintro ⟨p⟩
    exact symmetry_path_endpoint_local facets d rep hrep F.val
      (p.map continuous_subtype_val) (fun t => (p t).property)
  · rintro ⟨γ, hγ, hF⟩
    let g : localFunctionSubgroup (G := G) facets CirclePaths.Phase := ⟨γ, hγ⟩
    letI := localFunctions_pathConnectedSpace (G := G) facets
    have hp := (PathConnectedSpace.joined (0 : localFunctionSubgroup (G := G)
      facets CirclePaths.Phase) g).map (continuous_localDerivative facets d)
    have hval : localDerivative facets d g = F := Subtype.ext hF
    simpa only [map_zero, hval] using hp

/-- The integer row of one literal locality constraint on a phase primitive. -/
def symmetryIntegerRow (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (e : SymmetryConstraint facets d) :
    PhaseDuality.Distribution (Configuration ι G) :=
  iteratedDistributionDifference
    ((e.z : Configuration ι G) :: e.steps.map (fun p => Finsupp.single p.1 p.2))
    (Finsupp.single e.base 1)

theorem symmetryIntegerRow_evaluate (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (e : SymmetryConstraint facets d)
    (β : Configuration ι G → CirclePaths.Phase) :
    PhaseDuality.evaluate β (symmetryIntegerRow facets d e) =
      symmetryPhaseEquation facets d e β := by
  change phasePairing β _ = _
  unfold symmetryIntegerRow
  rw [← iteratedPhaseDifference_eq_pairing]
  change iteratedPhaseDifference _ (phaseDifference e.z β) e.base = _
  simp only [symmetryPhaseEquation, AddMonoidHom.comp_apply, phaseEvalHom,
    iteratedPhaseDiffHom_apply, phaseDiffHom]
  rfl

theorem mem_symmetryIntegerPhases_iff [Fintype (Configuration ι G)]
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (β : Configuration ι G → CirclePaths.Phase) :
    β ∈ PhaseDuality.integerEquationPhases (symmetryIntegerRow facets d) ↔
      RestrictionSymmetryLocal facets d (phaseDerivative d β) := by
  rw [← mem_admissiblePhase_iff, CirclePaths.mem_equationSubgroup,
    PhaseDuality.mem_integerEquationPhases]
  simp only [symmetryIntegerRow_evaluate]

/-- The component set is genuinely finite; no Lie-group assertion is assumed. -/
theorem finite_localSymmetry_components [Fintype (Configuration ι G)]
    (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a) :
    Finite (ZerothHomotopy (localSymmetries facets d (P := CirclePaths.Phase))) := by
  letI := PhaseDuality.finite_integerEquationPhases_components (symmetryIntegerRow facets d)
  let f : PhaseDuality.integerEquationPhases (symmetryIntegerRow facets d) →
      localSymmetries facets d (P := CirclePaths.Phase) :=
    fun β => ⟨phaseDerivative d β.val, (mem_symmetryIntegerPhases_iff facets d β.val).1 β.property⟩
  apply PhaseDuality.finite_zerothHomotopy_of_surjective f
    (((continuous_phaseDerivative d).comp continuous_subtype_val).subtype_mk _)
  intro F
  refine ⟨⟨phaseSection d rep hrep F.val, ?_⟩, ?_⟩
  · rw [mem_symmetryIntegerPhases_iff, phaseDerivative_phaseSection]
    exact F.property
  · apply Subtype.ext
    exact phaseDerivative_phaseSection d rep hrep F.val

end OpenDisk
