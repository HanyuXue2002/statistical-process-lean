import Formalization.OpenDisk.LocalityTopology

set_option linter.style.header false

/-!
# Marked locality and phase gradients

Marked locality is ordinary locality for the subfamily of facets containing
the specified marks.  Thus it includes the order-zero condition when no
facet contains all marks.  This matches the anchored-interaction description
in Section 5.3 of the open-disk report.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G A Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]

/-- Facets containing every prescribed carrier. -/
def markedFacets (facets : Facet → Set ι) (marks : Finset ι) :
    {ρ : Facet // ∀ i ∈ marks, i ∈ facets ρ} → Set ι := fun ρ => facets ρ.val

/-- All anchored interactions, together with the marks, fit in some facet. -/
def MarkedLocal (facets : Facet → Set ι) (marks : Finset ι)
    (f : Configuration ι G → A) : Prop := AnchoredLocal (markedFacets facets marks) f

/-- Marked anchored locality is the literal iterated-difference condition. -/
theorem markedLocal_iff_differences (facets : Facet → Set ι) (marks : Finset ι)
    (f : Configuration ι G → A) :
    MarkedLocal facets marks f ↔ DifferenceLocal (markedFacets facets marks) f :=
  (differenceLocal_iff_anchoredLocal _ _).symm

/-- Differentiating a local phase along a carrier produces locality marked by that carrier. -/
theorem DifferenceLocal.marked_difference {facets : Facet → Set ι}
    {f : Configuration ι G → A} (h : DifferenceLocal facets f)
    (i : ι) (g : G) (hg : g ≠ 0) :
    MarkedLocal facets {i} (phaseDifference (Finsupp.single i g) f) := by
  rw [markedLocal_iff_differences]
  intro steps hne hfac c
  change iteratedPhaseDifference
    (((i, g) :: steps).map (fun p => Finsupp.single p.1 p.2)) f c = 0
  apply h
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hg
    · exact hne p hp
  · intro ρ
    classical
    by_cases hi : i ∈ facets ρ
    · let ρ' : {ρ : Facet // ∀ j ∈ ({i} : Finset ι), j ∈ facets ρ} :=
        ⟨ρ, by simpa using hi⟩
      obtain ⟨p, hp, hpρ⟩ := hfac ρ'
      exact ⟨p, List.mem_cons_of_mem _ hp, hpρ⟩
    · exact ⟨(i, g), List.mem_cons_self, hi⟩

/-- If all elementary gradients are marked-local, the phase itself is local.
Nonemptiness retains the unrestricted constant phase, as in the report. -/
theorem differenceLocal_of_marked_gradients [Nonempty Facet]
    {facets : Facet → Set ι} {f : Configuration ι G → A}
    (h : ∀ (i : ι) (g : G), g ≠ 0 →
      MarkedLocal facets {i} (phaseDifference (Finsupp.single i g) f)) :
    DifferenceLocal facets f := by
  intro steps hne hfac c
  cases steps with
  | nil =>
      obtain ⟨ρ⟩ := ‹Nonempty Facet›
      simpa using hfac ρ
  | cons p steps =>
      have hmarked := (markedLocal_iff_differences facets {p.1} _).mp
        (h p.1 p.2 (hne p List.mem_cons_self))
      apply hmarked steps
      · intro q hq
        exact hne q (List.mem_cons_of_mem _ hq)
      · intro ρ
        obtain ⟨q, hq, hqρ⟩ := hfac ρ.val
        rcases List.mem_cons.mp hq with heq | hq
        · subst q
          exact (hqρ (ρ.property p.1 (Finset.mem_singleton_self _))).elim
        · exact ⟨q, hq, hqρ⟩

/-- Equation (5.9), including the constant anchored coordinate. -/
theorem marked_gradients_iff_local [Nonempty Facet]
    (facets : Facet → Set ι) (f : Configuration ι G → A) :
    (∀ (i : ι) (g : G), g ≠ 0 →
      MarkedLocal facets {i} (phaseDifference (Finsupp.single i g) f)) ↔
      DifferenceLocal facets f :=
  ⟨differenceLocal_of_marked_gradients, fun h i g hg => h.marked_difference i g hg⟩

end OpenDisk
