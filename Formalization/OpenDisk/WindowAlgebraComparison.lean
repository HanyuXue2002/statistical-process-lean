import Formalization.OpenDisk.HoppingAlgebra
import Formalization.OpenDisk.HoppingStarAlgebra

/-!
# Literal regional algebra equality constrains the comparison phase

The diagonal coefficient argument is over the complete configuration Hilbert
space. It passes from closed-word invariance to every diagonal of the generated
algebra, and compares two actual same-increment hoppings using the true inverse.
-/

noncomputable section
namespace OpenDisk.Window

variable {C E E₀ E₁ : Type*} [AddCommGroup C]
local instance comparisonDecidableEq : DecidableEq C := Classical.decEq _

theorem closedWordSpan_diagonal_coefficients (steps : E → HoppingStep C) (z : C)
    (hwords : ∀ word : List E, hoppingWordIncrement (word.map steps) = 0 →
      ∀ c, hoppingWordPhase (word.map steps) (c+z) = hoppingWordPhase (word.map steps) c)
    (A : CoefficientEnd C) (hA : A ∈ closedWordSpan steps) (c : C) :
    A (Pi.single (c+z) 1) (c+z) = A (Pi.single c 1) c := by
  classical
  induction hA using Submodule.span_induction with
  | mem A hA =>
      obtain ⟨word,hc,rfl⟩ := hA
      change hoppingWordEquiv (word.map steps) _ _ = hoppingWordEquiv (word.map steps) _ _
      rw [hoppingWord_closed _ hc,hoppingWord_closed _ hc]
      simp [diagonalEquiv_apply,hwords word hc c]
  | zero => simp
  | add A B hA hB ihA ihB =>
      change A _ _ + B _ _ = A _ _ + B _ _
      rw [ihA,ihB]
  | smul a A hA ih =>
      change a * A _ _ = a * A _ _
      rw [ih]

/-- Faithfulness of the circle character recovers equality of full phases,
not merely equality of their exponentials. -/
theorem algebra_diagonal_phase_invariant (steps : E → HoppingStep C) (z : C)
    (hwords : ∀ word : List E, hoppingWordIncrement (word.map steps) = 0 →
      ∀ c, hoppingWordPhase (word.map steps) (c+z) = hoppingWordPhase (word.map steps) c)
    (κ : C → CirclePhase)
    (hκ : (diagonalEquiv κ).toLinearMap ∈ hoppingAlgebra steps) (c : C) : κ (c+z) = κ c := by
  classical
  apply phaseWeight_injective
  have hh := closedWordSpan_diagonal_coefficients steps z hwords
    (diagonalEquiv κ).toLinearMap
    (diagonal_mem_closedWordSpan steps _ hκ (diagonalPart_diagonal κ)) c
  simpa [diagonalEquiv_apply] using hh

theorem inverse_hopping_product (L₀ L₁ : C → CirclePhase) (s : C) :
    (hoppingEquiv L₀ s).symm.toLinearMap * (hoppingEquiv L₁ s).toLinearMap =
      (diagonalEquiv (L₁-L₀)).toLinearMap := by
  ext ψ c
  change (phaseWeight (L₀ c))⁻¹ *
    (phaseWeight (L₁ (c+s-s)) * ψ (c+s-s)) = phaseWeight ((L₁-L₀) c) * ψ c
  rw [add_sub_cancel_right]
  simp only [Pi.sub_apply,phaseWeight_sub]
  field_simp

/-- Equality is in the literal full operator algebra. The two labels may
come from different complete legal-hop families. -/
theorem hopping_comparison_diagonal_mem
    (steps₀ : E₀ → HoppingStep C) (steps₁ : E₁ → HoppingStep C)
    (heq : actualHoppingAlgebra steps₀ = actualHoppingAlgebra steps₁)
    (e₀ : E₀) (e₁ : E₁) (hs : (steps₀ e₀).2 = (steps₁ e₁).2) :
    (diagonalEquiv ((steps₁ e₁).1-(steps₀ e₀).1)).toLinearMap ∈
      actualHoppingAlgebra steps₀ := by
  have h₀ : (hoppingEquiv (steps₀ e₀).1 (steps₀ e₀).2).symm.toLinearMap ∈
      actualHoppingAlgebra steps₀ := by
    rw [hopping_inverse]
    exact Algebra.subset_adjoin ⟨Sum.inr e₀,rfl⟩
  have h₁ : (hoppingEquiv (steps₁ e₁).1 (steps₁ e₁).2).toLinearMap ∈
      actualHoppingAlgebra steps₀ := by
    rw [heq]
    exact Algebra.subset_adjoin ⟨Sum.inl e₁,rfl⟩
  have hm := (actualHoppingAlgebra steps₀).mul_mem h₀ h₁
  rw [hs,inverse_hopping_product] at hm
  exact hm

theorem algebra_equality_comparison_invariant
    (steps₀ : E₀ → HoppingStep C) (steps₁ : E₁ → HoppingStep C)
    (heq : actualHoppingAlgebra steps₀ = actualHoppingAlgebra steps₁)
    (e₀ : E₀) (e₁ : E₁) (hs : (steps₀ e₀).2 = (steps₁ e₁).2) (z : C)
    (hwords : ∀ word : List (E₀ ⊕ E₀),
      hoppingWordIncrement (word.map (signedSteps steps₀)) = 0 →
      ∀ c, hoppingWordPhase (word.map (signedSteps steps₀)) (c+z) =
        hoppingWordPhase (word.map (signedSteps steps₀)) c) (c : C) :
    ((steps₁ e₁).1-(steps₀ e₀).1) (c+z) = ((steps₁ e₁).1-(steps₀ e₀).1) c :=
  algebra_diagonal_phase_invariant (signedSteps steps₀) z hwords _
    (hopping_comparison_diagonal_mem steps₀ steps₁ heq e₀ e₁ hs) c

section Matrix
variable [Fintype C] [DecidableEq C]

theorem hoppingStarAlgebra_eq_iff_actual
    (steps₀ : E₀ → HoppingStep C) (steps₁ : E₁ → HoppingStep C) :
    hoppingStarAlgebra steps₀ = hoppingStarAlgebra steps₁ ↔
      actualHoppingAlgebra steps₀ = actualHoppingAlgebra steps₁ := by
  constructor
  · intro h
    apply Subalgebra.map_injective LinearMap.toMatrixAlgEquiv'.injective
    rw [← hoppingStarAlgebra_eq_actual,← hoppingStarAlgebra_eq_actual,h]
  · intro h
    apply StarSubalgebra.toSubalgebra_injective
    rw [hoppingStarAlgebra_eq_actual,hoppingStarAlgebra_eq_actual,h]

/-- The comparison theorem applies to the full complex matrix star algebras
in the report, including actual adjoints, with no quotient or invariant-space restriction. -/
theorem starAlgebra_equality_comparison_invariant
    (steps₀ : E₀ → HoppingStep C) (steps₁ : E₁ → HoppingStep C)
    (heq : hoppingStarAlgebra steps₀ = hoppingStarAlgebra steps₁)
    (e₀ : E₀) (e₁ : E₁) (hs : (steps₀ e₀).2 = (steps₁ e₁).2) (z : C)
    (hwords : ∀ word : List (E₀ ⊕ E₀),
      hoppingWordIncrement (word.map (signedSteps steps₀)) = 0 →
      ∀ c, hoppingWordPhase (word.map (signedSteps steps₀)) (c+z) =
        hoppingWordPhase (word.map (signedSteps steps₀)) c) (c : C) :
    ((steps₁ e₁).1-(steps₀ e₀).1) (c+z) = ((steps₁ e₁).1-(steps₀ e₀).1) c :=
  algebra_equality_comparison_invariant steps₀ steps₁
    ((hoppingStarAlgebra_eq_iff_actual steps₀ steps₁).1 heq) e₀ e₁ hs z hwords c

end Matrix
end OpenDisk.Window
