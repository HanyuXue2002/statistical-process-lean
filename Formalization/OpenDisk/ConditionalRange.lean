import Formalization.OpenDisk.HilbertOperators

/-!
# What a complete conditional encoding image determines

Equality of the literal Hilbert-space images is equivalent to a boundary-only
phase difference. This is the first step of the report's conditional window
discussion; it does not assume or assert its additional regional algebra claim.
-/

noncomputable section

namespace OpenDisk
open BulkPhaseHilbert

variable {I B : Type*} [Fintype I] [Fintype B] [Nonempty I]

abbrev circleCharacter := AddCircle.toCircle_addChar (T := (1 : ℝ))

theorem conditional_boundary_phase (φ : I × B → CirclePhase) (γ : B → CirclePhase)
    (a : EuclideanSpace ℂ B) :
    conditionalLinear circleCharacter (fun c => φ c + γ c.2) a =
      conditionalLinear circleCharacter φ
        (WithLp.toLp 2 (fun b => phaseWeight (γ b) * a b)) := by
  ext c
  change normalization I * phaseWeight (φ c + γ c.2) * a c.2 =
    normalization I * phaseWeight (φ c) * (phaseWeight (γ c.2) * a c.2)
  rw [phaseWeight_add]
  ring

/-- Sharing the entire conditional image determines exactly a boundary function. -/
theorem conditional_range_eq_iff (φ₀ φ₁ : I × B → CirclePhase) :
    LinearMap.range (conditionalLinear circleCharacter φ₁) =
      LinearMap.range (conditionalLinear circleCharacter φ₀) ↔
      ∃ γ : B → CirclePhase, ∀ c, φ₁ c - φ₀ c = γ c.2 := by
  constructor
  · intro hr
    let oneVector : EuclideanSpace ℂ B := WithLp.toLp 2 (fun _ => (1 : ℂ))
    have hm : conditionalLinear circleCharacter φ₁ oneVector ∈
        LinearMap.range (conditionalLinear circleCharacter φ₀) := by
      rw [← hr]
      exact ⟨oneVector, rfl⟩
    obtain ⟨a, ha⟩ := hm
    have hv (c : I × B) : phaseWeight (φ₀ c) * a c.2 = phaseWeight (φ₁ c) := by
      apply mul_left_cancel₀ (normalization_ne_zero I)
      have hh := congrArg (fun f : EuclideanSpace ℂ (I × B) => f c) ha
      change normalization I * phaseWeight (φ₀ c) * a c.2 =
        normalization I * phaseWeight (φ₁ c) * 1 at hh
      simpa only [mul_one, mul_assoc] using hh
    have hd (c : I × B) : phaseWeight (φ₁ c - φ₀ c) = a c.2 := by
      rw [phaseWeight_sub, ← hv c]
      field_simp
    let i₀ : I := Classical.choice inferInstance
    refine ⟨fun b => φ₁ (i₀, b) - φ₀ (i₀, b), fun c => ?_⟩
    apply phaseWeight_injective
    rw [hd c, hd (i₀, c.2)]
  · rintro ⟨γ, hγ⟩
    have hplus : φ₁ = fun c => φ₀ c + γ c.2 := by
      funext c
      rw [← hγ c]
      abel
    have hminus : φ₀ = fun c => φ₁ c + (-γ) c.2 := by
      funext c
      change φ₀ c = φ₁ c + -(γ c.2)
      rw [← hγ c]
      abel
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      refine ⟨WithLp.toLp 2 (fun b => phaseWeight (γ b) * a b), ?_⟩
      rw [hplus, conditional_boundary_phase]
    · rintro _ ⟨a, rfl⟩
      refine ⟨WithLp.toLp 2 (fun b => phaseWeight ((-γ) b) * a b), ?_⟩
      rw [hminus, conditional_boundary_phase]

end OpenDisk
