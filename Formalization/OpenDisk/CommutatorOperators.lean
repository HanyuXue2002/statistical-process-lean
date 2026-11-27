import Formalization.OpenDisk.HoppingOperators
import Formalization.OpenDisk.NormalFormTableLocality

/-!
# Actual inverse words and the operator-locality equations

All inverses here are inverses of the actual linear operators. The based
square travels s, t, -s, -t, with the phases of the inverses retained.
Vanishing phase is equivalent to the identity matrix because the real-circle
character is faithful.
-/

noncomputable section

namespace OpenDisk

variable {C : Type*} [AddCommGroup C]

@[simp] theorem hoppingEquiv_symm_apply (L : C → CirclePhase) (s : C) (ψ : C → ℂ) (v : C) :
    (hoppingEquiv L s).symm ψ v = (phaseWeight (L v))⁻¹ * ψ (v + s) := rfl

/-- The actual based commutator square, including both true inverse phases. -/
theorem hopping_square_phase (L M : C → CirclePhase) (s t : C) (ψ : C → ℂ) :
    (hoppingEquiv M t).symm ((hoppingEquiv L s).symm
      (hoppingEquiv M t (hoppingEquiv L s ψ))) =
      diagonalEquiv (fun v => difference M s v - difference L t v) ψ := by
  funext v
  simp only [hoppingEquiv_symm_apply, hoppingEquiv_apply, diagonalEquiv_apply]
  rw [show v + t + s - t = v + s by abel, add_sub_cancel_right]
  simp only [difference, phaseWeight_sub]
  field_simp

theorem diagonal_eq_identity_iff (κ : C → CirclePhase) :
    (∀ ψ : C → ℂ, diagonalEquiv κ ψ = ψ) ↔ κ = 0 := by
  constructor
  · intro h
    funext v
    apply phaseWeight_injective
    have hv := congrFun (h (fun _ => 1)) v
    simpa only [diagonalEquiv_apply, mul_one, Pi.zero_apply, phaseWeight_zero] using hv
  · intro h ψ
    subst κ
    funext v
    simp [diagonalEquiv_apply]

/-- Conjugating a diagonal by any phase hopping only translates its table. -/
theorem hopping_conjugates_diagonal (L κ : C → CirclePhase) (s : C) (ψ : C → ℂ) :
    (hoppingEquiv L s).symm (diagonalEquiv κ (hoppingEquiv L s ψ)) =
      diagonalEquiv (fun v => κ (v + s)) ψ := by
  funext v
  simp only [hoppingEquiv_symm_apply, diagonalEquiv_apply, hoppingEquiv_apply,
    add_sub_cancel_right]
  field_simp

theorem hopping_diagonal_difference (L κ : C → CirclePhase) (s : C) (ψ : C → ℂ) :
    (diagonalEquiv κ).symm
      ((hoppingEquiv L s).symm (diagonalEquiv κ (hoppingEquiv L s ψ))) =
      diagonalEquiv (difference κ s) ψ := by
  rw [hopping_conjugates_diagonal]
  funext v
  change (phaseWeight (κ v))⁻¹ * (phaseWeight (κ (v + s)) * ψ v) =
    phaseWeight (κ (v + s) - κ v) * ψ v
  rw [phaseWeight_sub]
  field_simp

open GeneralSphereT.PathAlgebra
variable {ι G Facet : Type*} [LinearOrder ι] [AddCommGroup G]

/-- The report's finite-difference operator axiom is literally an identity-operator test. -/
theorem tableOperatorLocal_iff_diagonal_identity (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → CirclePhase) :
    TableOperatorLocal facets T ↔
      ∀ (e f : ElementaryLabel ι G) (rs : List (Configuration ι G)),
        NoCommonFacetList (fun ρ => coordinateRestriction (G := G) (facets ρ))
          (elementaryStep e :: elementaryStep f :: rs) →
        ∀ ψ : Configuration ι G → ℂ,
          diagonalEquiv (iteratedPhaseDifference rs
            (fun v => phaseDifference (elementaryStep e) (T f) v -
              phaseDifference (elementaryStep f) (T e) v)) ψ = ψ := by
  constructor
  · intro h e f rs hfac
    apply (diagonal_eq_identity_iff _).2
    funext c
    exact h e f rs c hfac
  · intro h e f rs c hfac
    exact congrFun ((diagonal_eq_identity_iff _).1 (h e f rs hfac)) c

end OpenDisk
