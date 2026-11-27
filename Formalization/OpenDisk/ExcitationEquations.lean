import Formalization.OpenDisk.Excitation

set_option linter.style.header false

/-!
# Literal excitation commutator equations

The cochain-pullback definition of the excitation subgroup is equivalent to
equation (5.2) evaluated on every physical configuration. This equivalence
uses only surjectivity of the coboundary onto its declared image.
-/

noncomputable section

open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {X ι G B P Facet : Type*} [AddCommGroup X] [LinearOrder ι]
  [AddCommGroup G] [AddCommGroup B] [AddCommGroup P]

/-- Iterated finite differences on an arbitrary physical configuration group. -/
def iteratedDifference : List X → (X → P) → X → P
  | [], f => f
  | s :: rs, f => iteratedDifference rs (difference f s)

theorem iteratedDifference_pullback (d : Configuration ι G →+ B)
    (rs : List (Configuration ι G)) (f : B → P) :
    iteratedPhaseDifference rs (f ∘ d) = iteratedDifference (rs.map d) f ∘ d := by
  induction rs generalizing f with
  | nil => rfl
  | cons r rs ih =>
      change iteratedPhaseDifference rs (phaseDifference r (f ∘ d)) =
        iteratedDifference (rs.map d) (difference f (d r)) ∘ d
      have hh : phaseDifference r (f ∘ d) = difference f (d r) ∘ d := by
        funext c
        exact difference_pullback d f r c
      rw [hh, ih]

/-- The binary commutator phase on actual excitation configurations. -/
def excitationCurvature (d : Configuration ι G →+ B)
    (θ : ElementaryLabel ι G → B → P) (e f : ElementaryLabel ι G) : B → P :=
  fun a => difference (θ f) (d (elementaryStep e)) a -
    difference (θ e) (d (elementaryStep f)) a

theorem excitationCurvature_pullback (d : Configuration ι G →+ B)
    (θ : ElementaryLabel ι G → B → P) (e f : ElementaryLabel ι G) :
    (fun c => phaseDifference (elementaryStep e) (excitationPullback d θ f) c -
      phaseDifference (elementaryStep f) (excitationPullback d θ e) c) =
      excitationCurvature d θ e f ∘ d := by
  funext c
  exact congrArg₂ (· - ·) (difference_pullback d (θ f) (elementaryStep e) c)
    (difference_pullback d (θ e) (elementaryStep f) c)

/-- The full literal equation (5.2), with arbitrary additional cochain shifts. -/
theorem excitation_mem_iff_equations (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (hd : Function.Surjective d)
    (θ : ElementaryLabel ι G → B → P) :
    θ ∈ excitationPhases facets d P ↔
      ∀ (e f : ElementaryLabel ι G) (rs : List (Configuration ι G)) (a : B),
        NoCommonFacetList (fun ρ => coordinateRestriction (G := G) (facets ρ))
          (elementaryStep e :: elementaryStep f :: rs) →
        iteratedDifference (rs.map d) (excitationCurvature d θ e f) a = 0 := by
  change TableOperatorLocal facets (excitationPullback d θ) ↔ _
  unfold TableOperatorLocal
  simp only [excitationCurvature_pullback, iteratedDifference_pullback, Function.comp_apply]
  constructor
  · intro h e f rs a hfac
    obtain ⟨c, rfl⟩ := hd a
    exact h e f rs c hfac
  · intro h e f rs c hfac
    exact h e f rs (d c) hfac

end OpenDisk
