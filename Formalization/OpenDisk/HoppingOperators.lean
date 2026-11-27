import Formalization.OpenDisk.StateConjugacy
import Formalization.OpenDisk.Matching

/-!
# Literal hopping operators and matching

The linear map has matrix action `|v⟩ ↦ exp(2πi L(v)) |v+s⟩`.
Its preservation of the actual invariant subspace is equivalent to the phase
matching equation. This proves the operator content of Proposition 3.6.
-/

noncomputable section

namespace OpenDisk

variable {C A : Type*} [AddCommGroup C] [AddCommGroup A]

def hoppingEquiv (L : C → CirclePhase) (s : C) : (C → ℂ) ≃ₗ[ℂ] (C → ℂ) where
  toFun ψ w := phaseWeight (L (w - s)) * ψ (w - s)
  invFun ψ v := (phaseWeight (L v))⁻¹ * ψ (v + s)
  left_inv ψ := by funext v; simp [← mul_assoc]
  right_inv ψ := by funext w; simp [← mul_assoc]
  map_add' ψ χ := by funext w; exact mul_add _ _ _
  map_smul' k ψ := by funext w; change _ * (k * _) = k * (_ * _); ring

@[simp] theorem hoppingEquiv_apply (L : C → CirclePhase) (s : C) (ψ : C → ℂ) (w : C) :
    hoppingEquiv L s ψ w = phaseWeight (L (w - s)) * ψ (w - s) := rfl

/-- The literal intertwining equation for simultaneous diagonal conjugation. -/
theorem diagonal_hopping_intertwines (L γ : C → CirclePhase) (s : C) (ψ : C → ℂ) :
    diagonalEquiv γ (hoppingEquiv L s ψ) =
      hoppingEquiv (L + difference γ s) s (diagonalEquiv γ ψ) := by
  funext w
  simp only [diagonalEquiv_apply, hoppingEquiv_apply, Pi.add_apply]
  rw [← mul_assoc, ← mul_assoc, ← phaseWeight_add, ← phaseWeight_add]
  congr 1
  congr 1
  simp only [difference, sub_add_cancel]
  abel

theorem hopping_preserves_of_matching (d : C →+ A) (β L : C → CirclePhase) (s : C)
    (hL : Matching d β L s) (ψ : C → ℂ)
    (hψ : ψ ∈ invariantSpace d (phaseDerivative d β)) :
    hoppingEquiv L s ψ ∈ invariantSpace d (phaseDerivative d β) := by
  intro z w
  have h := hL z (w - s)
  have hz : w + z - s = (w - s) + z := by abel
  have hzs : w - s + s = w := sub_add_cancel _ _
  have hw : phaseWeight (L (w + z - s)) * phaseWeight
      (phaseDerivative d β z (w - s)) =
      phaseWeight (phaseDerivative d β z w) * phaseWeight (L (w - s)) := by
    rw [← phaseWeight_add, ← phaseWeight_add]
    apply congrArg phaseWeight
    simp only [difference, hzs] at h
    change L (w + z - s) + (β (w - s + z) - β (w - s)) =
      (β (w + z) - β w) + L (w - s)
    rw [hz]
    exact sub_eq_sub_iff_add_eq_add.mp h
  change phaseWeight (L (w + z - s)) * ψ (w + z - s) = _
  rw [hz, hψ z (w - s), ← mul_assoc]
  rw [← hz, hw, mul_assoc]
  rfl

/-- Preservation of the actual embedded invariant space is equivalent to matching. -/
theorem hopping_preserves_iff_matching (d : C →+ A) (β L : C → CirclePhase) (s : C) :
    (∀ ψ ∈ invariantSpace d (phaseDerivative d β),
      hoppingEquiv L s ψ ∈ invariantSpace d (phaseDerivative d β)) ↔ Matching d β L s := by
  constructor
  · intro h z v
    have hv := h (phaseState β) ((phaseState_mem_iff d _ β).2 rfl) z (v + s)
    have hz : v + s + z - s = v + z := by abel
    change phaseWeight (L (v + s + z - s)) * phaseWeight (β (v + s + z - s)) =
      phaseWeight (β (v + s + z) - β (v + s)) *
        (phaseWeight (L (v + s - s)) * phaseWeight (β (v + s - s))) at hv
    rw [hz, add_sub_cancel_right, ← phaseWeight_add, ← phaseWeight_add,
      ← phaseWeight_add] at hv
    have heq := phaseWeight_injective hv
    simp only [difference]
    apply sub_eq_sub_iff_add_eq_add.mpr
    calc
      L (v + z) + (β (v + z) - β v) = (L (v + z) + β (v + z)) - β v := by abel
      _ = ((β (v + s + z) - β (v + s)) + (L v + β v)) - β v := by rw [heq]
      _ = (β (v + s + z) - β (v + s)) + L v := by abel
  · intro h ψ hψ
    exact hopping_preserves_of_matching d β L s h ψ hψ

/-- Hopping shifts precisely the curvature label, including arbitrary amplitudes. -/
theorem hopping_configuration_formula (d : C →+ A) (β : C → CirclePhase)
    (θ : A → CirclePhase) (s : C) (a : A → ℂ) (w : C) :
    hoppingEquiv (θ ∘ d + difference β s) s
      (fun v => phaseWeight (β v) * a (d v)) w =
      phaseWeight (β w) * (phaseWeight (θ (d w - d s)) * a (d w - d s)) := by
  simp only [hoppingEquiv_apply, Pi.add_apply, Function.comp_apply,
    difference, sub_add_cancel, map_sub]
  have hphase : (θ (d w - d s) + (β w - β (w - s))) + β (w - s) =
      β w + θ (d w - d s) := by abel
  rw [← mul_assoc, ← phaseWeight_add, hphase, phaseWeight_add, mul_assoc]

end OpenDisk
