import Formalization.OpenDisk.SymmetryLocality
import Formalization.OpenDisk.CirclePaths

/-!
# The zero path component of restriction-local symmetry

The main implication is proved by lifting circle paths through the n-fold
covering map. All locality equations are continuous additive equations, so
their zero values persist along the based lift. Integral averaging then
produces a local phase. This avoids assuming a compact-Lie classification.
-/

noncomputable section
open GeneralSphereT.PathAlgebra
open scoped unitInterval

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P]

def phaseDiffHom (s : Configuration ι G) :
    (Configuration ι G → P) →+ (Configuration ι G → P) where
  toFun := phaseDifference s
  map_zero' := by funext v; simp [phaseDifference]
  map_add' f g := by funext v; exact difference_add f g s v

def iteratedPhaseDiffHom : List (Configuration ι G) →
    (Configuration ι G → P) →+ (Configuration ι G → P)
  | [] => AddMonoidHom.id _
  | s :: steps => (iteratedPhaseDiffHom steps).comp (phaseDiffHom s)

theorem iteratedPhaseDiffHom_apply (steps : List (Configuration ι G))
    (f : Configuration ι G → P) :
    iteratedPhaseDiffHom steps f = iteratedPhaseDifference steps f := by
  induction steps generalizing f with
  | nil => rfl
  | cons s steps ih => exact ih _

def phaseEvalHom (v : Configuration ι G) : (Configuration ι G → P) →+ P where
  toFun f := f v
  map_zero' := rfl
  map_add' _ _ := rfl

section Continuity
variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_phaseDiffHom (s : Configuration ι G) :
    Continuous (phaseDiffHom (P := P) s) :=
  continuous_pi fun v => (continuous_apply (v + s)).sub (continuous_apply v)

theorem continuous_iteratedPhaseDiffHom (steps : List (Configuration ι G)) :
    Continuous (iteratedPhaseDiffHom (P := P) steps) := by
  induction steps with
  | nil => exact continuous_id
  | cons s steps ih => exact ih.comp (continuous_phaseDiffHom s)

end Continuity

/-- One of the literal equations (3.13), with all its applicability conditions. -/
structure SymmetryConstraint (facets : Facet → Set ι) (d : Configuration ι G →+ B) where
  z : d.ker
  steps : List (ι × G)
  nonempty_steps : steps ≠ []
  active : ∀ p ∈ steps, p.2 ≠ 0
  invisible : ∀ ρ, coordinateRestriction (facets ρ) (z : Configuration ι G) = 0 ∨
    ∃ p ∈ steps, p.1 ∉ facets ρ
  base : Configuration ι G

def symmetryPhaseEquation (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (e : SymmetryConstraint facets d) :
    (Configuration ι G → CirclePaths.Phase) →+ CirclePaths.Phase :=
  (phaseEvalHom e.base).comp
    ((iteratedPhaseDiffHom (e.steps.map (fun p => Finsupp.single p.1 p.2))).comp
      (phaseDiffHom e.z))

theorem continuous_symmetryPhaseEquation (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (e : SymmetryConstraint facets d) :
    Continuous (symmetryPhaseEquation facets d e) :=
  (continuous_apply e.base).comp
    ((continuous_iteratedPhaseDiffHom _).comp
      (continuous_phaseDiffHom (e.z : Configuration ι G)))

/-- The phase-coefficient space above the symmetry tables, defined by actual equations. -/
abbrev AdmissiblePhase (facets : Facet → Set ι) (d : Configuration ι G →+ B) :=
  CirclePaths.equationSubgroup (symmetryPhaseEquation facets d)

theorem mem_admissiblePhase_iff (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (β : Configuration ι G → CirclePaths.Phase) :
    β ∈ AdmissiblePhase facets d ↔ RestrictionSymmetryLocal facets d (phaseDerivative d β) := by
  rw [CirclePaths.mem_equationSubgroup]
  have heq (e : SymmetryConstraint facets d) :
      symmetryPhaseEquation facets d e β =
        iteratedPhaseDifference (e.steps.map (fun p => Finsupp.single p.1 p.2))
          (fun v => phaseDerivative d β e.z v) e.base := by
    simp only [symmetryPhaseEquation, AddMonoidHom.comp_apply, phaseEvalHom,
      iteratedPhaseDiffHom_apply, phaseDiffHom]
    rfl
  constructor
  · intro h z steps hne hactive hfac v
    exact (heq ⟨z, steps, hne, hactive, hfac, v⟩).symm.trans (h _)
  · intro h e
    rw [heq]
    exact h e.z e.steps e.nonempty_steps e.active e.invisible e.base

variable [Nonempty Facet]

/-- The difficult inclusion in Proposition 3.4: an endpoint connected to zero
through legal symmetry tables has a local phase primitive. -/
theorem symmetry_path_endpoint_local (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) [Fintype d.ker]
    (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)
    (F : SymmetryPhase d CirclePaths.Phase) (p : Path (0 : SymmetryPhase d CirclePaths.Phase) F)
    (hlocal : ∀ t, RestrictionSymmetryLocal facets d (p t)) :
    F ∈ (localFunctionSubgroup (G := G) facets CirclePaths.Phase).map (phaseDerivative d) := by
  let β (t : unitInterval) : AdmissiblePhase facets d :=
    ⟨phaseSection d rep hrep (p t), (mem_admissiblePhase_iff facets d _).2 (by
      rw [phaseDerivative_phaseSection]
      exact hlocal t)⟩
  let q : Path (0 : AdmissiblePhase facets d) (β 1) :=
    { toFun := β
      continuous_toFun :=
        ((continuous_phaseSection d rep hrep).comp p.continuous).subtype_mk _
      source' := by
        apply Subtype.ext
        change phaseSection d rep hrep (p 0) = 0
        rw [p.source, map_zero]
      target' := rfl }
  obtain ⟨y, _hyPath, hy⟩ := CirclePaths.root_path (symmetryPhaseEquation facets d)
    (continuous_symmetryPhaseEquation facets d) (Fintype.card d.ker) (β 1) q
  have hFy : RestrictionSymmetryLocal facets d (phaseDerivative d y.val) :=
    (mem_admissiblePhase_iff facets d y.val).1 y.property
  have hbound := restrictionSymmetry_card_bound facets d (phaseDerivative d y.val) hFy
  have heq : Fintype.card d.ker • phaseDerivative d y.val = F := by
    rw [← map_nsmul]
    have hval := congrArg Subtype.val hy
    change Fintype.card d.ker • y.val = phaseSection d rep hrep (p 1) at hval
    rw [hval, p.target, phaseDerivative_phaseSection]
  rwa [heq] at hbound

/-- The easy inclusion is also literal: every local phase gives a legal symmetry. -/
theorem local_phase_derivative_local (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (γ : localFunctionSubgroup (G := G) facets P) :
    RestrictionSymmetryLocal facets d (phaseDerivative d γ.val) :=
  joint_forgetSymmetry_local facets d (localPhaseGraph facets d γ)

end OpenDisk
