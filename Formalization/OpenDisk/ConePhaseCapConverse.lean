import Formalization.OpenDisk.ConePhaseLocalLift

/-!
# Recovering intrinsic symmetry locality from the canonical cap

The converse uses relative cochain primitives: a closed boundary cochain can
be lifted through the previous differential, with a lift invisible on every
facet containing the chosen marks whenever the boundary cochain is invisible
there. This is a condition on cochain maps only. A subsequent simplicial
instance obtains it from the actual carrier-normalized primitive and global
exactness of the boundary cochain complex.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace OpenDisk.ConePhaseLocalLift

open GeneralSphereT.PathAlgebra

variable {ι κ G A P Facet : Type*} [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup G] [AddCommGroup A] [AddCommGroup P]

local instance sumOrderConverse : LinearOrder (κ ⊕ ι) :=
  inferInstanceAs (LinearOrder (κ ⊕ₗ ι))

variable (d : Configuration ι G →+ A)

/-- The precise relative-primitive input, stated entirely at cochain level. -/
def RelativeCapLifts (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (D : Configuration κ G →+ d.ker) : Prop :=
  ∀ (z : d.ker) (marks : Finset ι), marks.Nonempty →
    ∃ w : Configuration κ G, D w = z ∧
      ∀ ρ, (∀ i ∈ marks, i ∈ facets ρ) →
        coordinateRestriction (facets ρ) (z : Configuration ι G) = 0 →
        coordinateRestriction (newFacets ρ) w = 0

theorem closedCapStep_invisible (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (D : Configuration κ G →+ d.ker) (w : Configuration κ G) (ρ : Facet)
    (hw : coordinateRestriction (newFacets ρ) w = 0)
    (hz : coordinateRestriction (facets ρ) (D w : Configuration ι G) = 0) :
    coordinateRestriction (capFacets facets newFacets ρ) (closedCapStep d D w) = 0 := by
  ext s
  rcases s with ⟨s, hs⟩
  cases s with
  | inl k =>
      have hk : k ∈ newFacets ρ := hs
      have heq := congrArg (fun c => c ⟨k, hk⟩) hw
      change w k = 0 at heq
      change newInclude w (Sum.inl k) + boundaryInclude (D w : Configuration ι G) (Sum.inl k) = 0
      simpa only [newInclude_inl, boundaryInclude_inl, add_zero] using heq
  | inr i =>
      have hi : i ∈ facets ρ := hs
      have heq := congrArg (fun c => c ⟨i, hi⟩) hz
      change (D w : Configuration ι G) i = 0 at heq
      change newInclude w (Sum.inr i) + boundaryInclude (D w : Configuration ι G) (Sum.inr i) = 0
      simpa only [newInclude_inr, boundaryInclude_inr, zero_add] using heq

/-- A local cap with relative cochain lifts has precisely the intrinsic
restriction locality required of a boundary symmetry table. -/
theorem restrictionLocal_of_capPhase_local
    (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (D : Configuration κ G →+ d.ker) (hrelative : RelativeCapLifts d facets newFacets D)
    (F : SymmetryPhase d P)
    (hcap : DifferenceLocal (capFacets facets newFacets) (capPhase d D F)) :
    RestrictionSymmetryLocal facets d F := by
  classical
  intro z steps hne hactive hfac v
  let marks := (steps.map Prod.fst).toFinset
  have hmarks : marks.Nonempty := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil steps hne
    exact ⟨p.1, List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩
  obtain ⟨w, hwz, hw⟩ := hrelative z marks hmarks
  let y := closedCapStep d D w
  let χ := capPhase d D F
  have hrow : (fun x => phaseDifference y χ (boundaryInclude (κ := κ) x)) =
      fun x => F z x := by
    funext x
    rw [capPhase_closed_difference, hwz, boundaryPart_boundaryInclude]
  have hpull := iterated_affine_pullback (boundaryInclude (κ := κ)) 0
    (steps.map (fun p => Finsupp.single p.1 p.2)) (phaseDifference y χ) v
  simp only [zero_add] at hpull
  rw [hrow] at hpull
  rw [hpull]
  change iteratedPhaseDifference
    (y :: (steps.map (fun p => Finsupp.single p.1 p.2)).map boundaryInclude) χ
    (boundaryInclude v) = 0
  apply ((differenceLocal_iff_anchoredLocal _ _).1 hcap).arbitrary_differences
  intro ρ
  by_cases hall : ∀ i ∈ marks, i ∈ facets ρ
  · have hzρ : coordinateRestriction (facets ρ) (z : Configuration ι G) = 0 := by
      rcases hfac ρ with hzρ | ⟨p, hp, hpρ⟩
      · exact hzρ
      · exact (hpρ (hall p.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)))).elim
    refine ⟨y, List.mem_cons_self, closedCapStep_invisible d facets newFacets D w ρ
      (hw ρ hall hzρ) ?_⟩
    simpa only [hwz] using hzρ
  · push_neg at hall
    obtain ⟨i, hi, hiρ⟩ := hall
    obtain ⟨p, hp, hpi⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    refine ⟨boundaryInclude (Finsupp.single p.1 p.2), List.mem_cons_of_mem _ ?_, ?_⟩
    · exact List.mem_map.mpr ⟨Finsupp.single p.1 p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, rfl⟩
    · rw [boundaryInclude_single]
      apply coordinateRestriction_single_not_mem
      change p.1 ∉ facets ρ
      simpa only [hpi] using hiρ

/-- Exact correspondence between intrinsic local symmetries and local
canonical caps, with all required cochain hypotheses exposed. -/
theorem capPhase_local_iff
    (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (D : Configuration κ G →+ d.ker)
    (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
    (hrelative : RelativeCapLifts d facets newFacets D) (F : SymmetryPhase d P) :
    DifferenceLocal (capFacets facets newFacets) (capPhase d D F) ↔
      RestrictionSymmetryLocal facets d F :=
  ⟨restrictionLocal_of_capPhase_local d facets newFacets D hrelative F,
    capPhase_local d facets newFacets hcover D hcolumns F⟩

end OpenDisk.ConePhaseLocalLift
