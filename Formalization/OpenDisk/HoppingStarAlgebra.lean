import Formalization.OpenDisk.HoppingAlgebra
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # The full matrix star algebra and its closed-word diagonal span -/

noncomputable section
open scoped ComplexConjugate

namespace OpenDisk
variable {C E : Type*} [AddCommGroup C] [Fintype C] [DecidableEq C]

def hoppingMatrix (a : HoppingStep C) : Matrix C C ℂ :=
  LinearMap.toMatrixAlgEquiv' (hoppingEquiv a.1 a.2).toLinearMap

theorem hoppingMatrix_apply (a : HoppingStep C) (i j : C) :
    hoppingMatrix a i j = if i = j + a.2 then phaseWeight (a.1 j) else 0 := by
  classical
  by_cases h : i = j + a.2
  · subst i
    simp [hoppingMatrix, LinearMap.toMatrixAlgEquiv'_apply, hoppingEquiv_apply]
  · have hn : i - a.2 ≠ j := by
      intro hh
      apply h
      exact (sub_eq_iff_eq_add.mp hh)
    simp [hoppingMatrix, LinearMap.toMatrixAlgEquiv'_apply, hoppingEquiv_apply,
      Pi.single_apply, h, hn, Ne.symm hn]

theorem phaseWeight_conj (p : CirclePhase) : conj (phaseWeight p) = phaseWeight (-p) := by
  rw [phaseWeight_neg]
  exact (Circle.coe_inv_eq_conj (AddCircle.toCircle p)).symm

/-- The matrix adjoint is exactly the actual inverse hopping. -/
theorem hoppingMatrix_star (a : HoppingStep C) :
    star (hoppingMatrix a) = hoppingMatrix (inverseHoppingStep a) := by
  ext i j
  change conj (hoppingMatrix a j i) = _
  rw [hoppingMatrix_apply, hoppingMatrix_apply]
  change conj (if j = i + a.2 then phaseWeight (a.1 i) else 0) =
    if i = j + -a.2 then phaseWeight (-a.1 (j - a.2)) else 0
  by_cases h : j = i + a.2
  · subst j
    simp [phaseWeight_conj]
  · have hn : i ≠ j + -a.2 := by
      intro hh
      apply h
      rw [hh]
      abel
    simp [h, hn]

def hoppingStarAlgebra (steps : E → HoppingStep C) : StarSubalgebra ℂ (Matrix C C ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range (fun e => hoppingMatrix (steps e)))

/-- Passing to matrices identifies the inverse-generated algebra with the full star algebra. -/
theorem hoppingStarAlgebra_eq_actual (steps : E → HoppingStep C) :
    (hoppingStarAlgebra steps).toSubalgebra =
      (actualHoppingAlgebra steps).map LinearMap.toMatrixAlgEquiv'.toAlgHom := by
  rw [hoppingStarAlgebra, StarAlgebra.adjoin_toSubalgebra,
    actualHoppingAlgebra, hoppingAlgebra, AlgHom.map_adjoin, ← Set.range_comp]
  congr 1
  ext A
  change (A ∈ Set.range (fun e => hoppingMatrix (steps e)) ∨
    A ∈ star (Set.range (fun e => hoppingMatrix (steps e)))) ↔
    A ∈ Set.range (fun e => hoppingMatrix (signedSteps steps e))
  constructor
  · rintro (h | h)
    · obtain ⟨e, rfl⟩ := h
      exact ⟨Sum.inl e, rfl⟩
    · obtain ⟨e, he⟩ := Set.mem_star.mp h
      refine ⟨Sum.inr e, ?_⟩
      change hoppingMatrix (inverseHoppingStep (steps e)) = A
      change hoppingMatrix (steps e) = star A at he
      rw [← hoppingMatrix_star, he, star_star]
  · rintro ⟨e | e, rfl⟩
    · exact Or.inl ⟨e, rfl⟩
    · apply Or.inr
      apply Set.mem_star.mpr
      refine ⟨e, ?_⟩
      change hoppingMatrix (steps e) = star (hoppingMatrix (inverseHoppingStep (steps e)))
      rw [← hoppingMatrix_star, star_star]

theorem diagonalPart_matrix (A : CoefficientEnd C) :
    LinearMap.toMatrixAlgEquiv' (diagonalPart A) =
      Matrix.diagonal (fun v => LinearMap.toMatrixAlgEquiv' A v v) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrixAlgEquiv'_apply, diagonalPart, Matrix.diagonal]
    apply congrArg (fun f : C → ℂ => A f i)
    funext j
    simp [Pi.single_apply]
  · simp [LinearMap.toMatrixAlgEquiv'_apply, diagonalPart, Matrix.diagonal,
      Pi.single_apply, hij, Ne.symm hij]

def closedMatrixWordSpan (steps : E → HoppingStep C) : Submodule ℂ (Matrix C C ℂ) :=
  (closedWordSpan (signedSteps steps)).map LinearMap.toMatrixAlgEquiv'.toLinearMap

/-- Every actual diagonal in the full matrix star algebra lies in the span of
closed words made from the original hoppings and their true inverses. -/
theorem hoppingStarAlgebra_diagonal_span (steps : E → HoppingStep C) (A : Matrix C C ℂ)
    (hA : A ∈ hoppingStarAlgebra steps) (hdiag : Matrix.diagonal (fun v => A v v) = A) :
    A ∈ closedMatrixWordSpan steps := by
  have hm : A ∈ (actualHoppingAlgebra steps).map LinearMap.toMatrixAlgEquiv'.toAlgHom := by
    rw [← hoppingStarAlgebra_eq_actual]
    exact hA
  obtain ⟨B, hB, rfl⟩ := hm
  apply Submodule.mem_map.mpr
  refine ⟨B, ?_, rfl⟩
  apply diagonal_mem_closedWordSpan (signedSteps steps) B hB
  apply LinearMap.toMatrixAlgEquiv'.injective
  rw [diagonalPart_matrix]
  exact hdiag

end OpenDisk
