import Formalization.OpenDisk.InvariantStates

/-!
# Diagonal conjugacy of the actual embedded invariant spaces

This is equation (3.10) of the report. Equality is literal equality of
subspaces of the fixed complex coefficient space, not just an abstract
isomorphism of configuration labels.
-/

noncomputable section

namespace OpenDisk

variable {C A : Type*} [AddCommGroup C] [AddCommGroup A]

/-- The literal diagonal phase operator on complex coefficient vectors. -/
def diagonalEquiv (γ : C → CirclePhase) : (C → ℂ) ≃ₗ[ℂ] (C → ℂ) where
  toFun ψ v := phaseWeight (γ v) * ψ v
  invFun ψ v := (phaseWeight (γ v))⁻¹ * ψ v
  left_inv ψ := by funext v; simp [← mul_assoc]
  right_inv ψ := by funext v; simp [← mul_assoc]
  map_add' ψ χ := by funext v; exact mul_add _ _ _
  map_smul' k ψ := by funext v; change _ * (k * _) = k * (_ * _); ring

@[simp] theorem diagonalEquiv_apply (γ : C → CirclePhase) (ψ : C → ℂ) (v : C) :
    diagonalEquiv γ ψ v = phaseWeight (γ v) * ψ v := rfl

theorem diagonalEquiv_phaseState (γ β : C → CirclePhase) :
    diagonalEquiv γ (phaseState β) = phaseState (γ + β) := by
  funext v
  exact (phaseWeight_add (γ v) (β v)).symm

theorem diagonal_invariant_iff (d : C →+ A) (F : SymmetryPhase d CirclePhase)
    (γ : C → CirclePhase) (ψ : C → ℂ) :
    diagonalEquiv γ ψ ∈ invariantSpace d (F + phaseDerivative d γ) ↔
      ψ ∈ invariantSpace d F := by
  have hw (z : d.ker) (v : C) :
      phaseWeight ((F + phaseDerivative d γ) z v) * phaseWeight (γ v) =
        phaseWeight (γ (v + z)) * phaseWeight (F z v) := by
    rw [← phaseWeight_add, ← phaseWeight_add]
    apply congrArg phaseWeight
    change (F z v + (γ (v + z) - γ v)) + γ v = γ (v + z) + F z v
    abel
  constructor
  · intro h z v
    have hv := h z v
    change phaseWeight (γ (v + z)) * ψ (v + z) =
      phaseWeight ((F + phaseDerivative d γ) z v) * (phaseWeight (γ v) * ψ v) at hv
    rw [← mul_assoc, hw, mul_assoc] at hv
    exact mul_left_cancel₀ (phaseWeight_ne_zero _) hv
  · intro h z v
    change phaseWeight (γ (v + z)) * ψ (v + z) =
      phaseWeight ((F + phaseDerivative d γ) z v) * (phaseWeight (γ v) * ψ v)
    rw [← mul_assoc, hw, mul_assoc, h z v]

/-- Diagonal multiplication maps the whole invariant subspace as predicted. -/
theorem diagonal_image_invariantSpace (d : C →+ A) (F : SymmetryPhase d CirclePhase)
    (γ : C → CirclePhase) :
    diagonalEquiv γ '' (invariantSpace d F : Set (C → ℂ)) =
      (invariantSpace d (F + phaseDerivative d γ) : Set (C → ℂ)) := by
  ext ψ
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    exact (diagonal_invariant_iff d F γ χ).2 hχ
  · intro hψ
    refine ⟨(diagonalEquiv γ).symm ψ, ?_, (diagonalEquiv γ).apply_symm_apply ψ⟩
    apply (diagonal_invariant_iff d F γ _).1
    simpa using hψ

/-- Equality of embedded invariant spaces determines the full symmetry table. -/
theorem invariantSpace_injective (d : C →+ A) (hd : Function.Surjective d) :
    Function.Injective (invariantSpace d) := by
  intro F₀ F₁ h
  obtain ⟨β, hβ⟩ := phaseDerivative_surjective d hd F₀
  have hm : phaseState β ∈ invariantSpace d F₀ :=
    (phaseState_mem_iff d F₀ β).2 hβ.symm
  rw [h] at hm
  exact hβ.symm.trans ((phaseState_mem_iff d F₁ β).1 hm).symm

/-- Equation (3.10), retaining every global and configuration-dependent phase. -/
theorem diagonal_image_eq_iff (d : C →+ A) (hd : Function.Surjective d)
    (F₀ F₁ : SymmetryPhase d CirclePhase) (γ : C → CirclePhase) :
    diagonalEquiv γ '' (invariantSpace d F₀ : Set (C → ℂ)) =
      (invariantSpace d F₁ : Set (C → ℂ)) ↔
        F₁ - F₀ = phaseDerivative d γ := by
  rw [diagonal_image_invariantSpace]
  constructor
  · intro h
    have heq : invariantSpace d (F₀ + phaseDerivative d γ) = invariantSpace d F₁ :=
      SetLike.coe_injective h
    have hf := invariantSpace_injective d hd heq
    rw [← hf]
    abel
  · intro h
    have hf : F₀ + phaseDerivative d γ = F₁ := by rw [← h]; abel
    rw [hf]

end OpenDisk
