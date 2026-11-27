import Formalization.OpenDisk.CommutatorOperators

/-! # Actual hopping words, true inverses, and iterated commutators -/

noncomputable section
namespace OpenDisk

variable {C : Type*} [AddCommGroup C]

/-- Fusion retains the phase of the second hop at the translated configuration. -/
theorem hopping_fusion (L M : C → CirclePhase) (s t : C) (ψ : C → ℂ) :
    hoppingEquiv M t (hoppingEquiv L s ψ) =
      hoppingEquiv (fun v => L v + M (v + s)) (s + t) ψ := by
  funext v
  simp only [hoppingEquiv_apply, phaseWeight_add]
  rw [show v - t - s = v - (s + t) by abel,
    show v - (s + t) + s = v - t by abel]
  ring

/-- An inverse step uses the actual inverse phase, not the original phase at `-s`. -/
theorem hopping_inverse (L : C → CirclePhase) (s : C) :
    (hoppingEquiv L s).symm = hoppingEquiv (fun v => -L (v - s)) (-s) := by
  apply LinearEquiv.ext
  intro ψ
  funext v
  simp only [hoppingEquiv_symm_apply, hoppingEquiv_apply, sub_neg_eq_add,
    add_sub_cancel_right, phaseWeight_neg]

abbrev HoppingStep (C : Type*) := (C → CirclePhase) × C

def inverseHoppingStep (a : HoppingStep C) : HoppingStep C :=
  (fun v => -a.1 (v - a.2), -a.2)

def hoppingWordIncrement : List (HoppingStep C) → C
  | [] => 0
  | a :: word => a.2 + hoppingWordIncrement word

def hoppingWordPhase : List (HoppingStep C) → C → CirclePhase
  | [] => 0
  | a :: word => fun v => a.1 v + hoppingWordPhase word (v + a.2)

/-- Words are evaluated in chronological order; each letter is a genuine linear equivalence. -/
def hoppingWordEquiv : List (HoppingStep C) → (C → ℂ) ≃ₗ[ℂ] (C → ℂ)
  | [] => LinearEquiv.refl ℂ _
  | a :: word => (hoppingEquiv a.1 a.2).trans (hoppingWordEquiv word)

theorem hoppingWordEquiv_append (xs ys : List (HoppingStep C)) :
    hoppingWordEquiv (xs ++ ys) = (hoppingWordEquiv xs).trans (hoppingWordEquiv ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.cons_append, hoppingWordEquiv, ih]
      rfl

theorem hoppingWordEquiv_eq (word : List (HoppingStep C)) :
    hoppingWordEquiv word = hoppingEquiv (hoppingWordPhase word) (hoppingWordIncrement word) := by
  induction word with
  | nil =>
      apply LinearEquiv.ext
      intro ψ
      funext v
      simp [hoppingWordEquiv, hoppingWordPhase, hoppingWordIncrement, hoppingEquiv_apply]
  | cons a word ih =>
      apply LinearEquiv.ext
      intro ψ
      change hoppingWordEquiv word (hoppingEquiv a.1 a.2 ψ) = _
      rw [ih, hopping_fusion]
      rfl

/-- A closed word is diagonal, with its complete accumulated phase. -/
theorem hoppingWord_closed (word : List (HoppingStep C))
    (hword : hoppingWordIncrement word = 0) (ψ : C → ℂ) :
    hoppingWordEquiv word ψ = diagonalEquiv (hoppingWordPhase word) ψ := by
  rw [hoppingWordEquiv_eq, hword]
  funext v
  simp [hoppingEquiv_apply, diagonalEquiv_apply]

/-- The phase carried by any hopping word cancels in conjugating a diagonal. -/
theorem hoppingWord_conjugates_diagonal (word : List (HoppingStep C))
    (κ : C → CirclePhase) (ψ : C → ℂ) :
    (hoppingWordEquiv word).symm (diagonalEquiv κ (hoppingWordEquiv word ψ)) =
      diagonalEquiv (fun v => κ (v + hoppingWordIncrement word)) ψ := by
  rw [hoppingWordEquiv_eq]
  exact hopping_conjugates_diagonal _ _ _ _

/-- This convention has phase `Δ_s κ`; reversing the commutator changes its sign. -/
def differenceCommutator (W A : (C → ℂ) ≃ₗ[ℂ] (C → ℂ)) :
    (C → ℂ) ≃ₗ[ℂ] (C → ℂ) := ((W.trans A).trans W.symm).trans A.symm

theorem differenceCommutator_diagonal (word : List (HoppingStep C)) (κ : C → CirclePhase) :
    differenceCommutator (hoppingWordEquiv word) (diagonalEquiv κ) =
      diagonalEquiv (difference κ (hoppingWordIncrement word)) := by
  apply LinearEquiv.ext
  intro ψ
  change (diagonalEquiv κ).symm ((hoppingWordEquiv word).symm
    (diagonalEquiv κ (hoppingWordEquiv word ψ))) = _
  rw [hoppingWordEquiv_eq]
  exact hopping_diagonal_difference _ _ _ _

def iteratedWordCommutator : List (List (HoppingStep C)) →
    ((C → ℂ) ≃ₗ[ℂ] (C → ℂ)) → ((C → ℂ) ≃ₗ[ℂ] (C → ℂ))
  | [], A => A
  | word :: words, A => iteratedWordCommutator words (differenceCommutator (hoppingWordEquiv word) A)

def iteratedHoppingDifference : List C → (C → CirclePhase) → C → CirclePhase
  | [], κ => κ
  | s :: ss, κ => iteratedHoppingDifference ss (difference κ s)

theorem iteratedWordCommutator_diagonal (words : List (List (HoppingStep C)))
    (κ : C → CirclePhase) :
    iteratedWordCommutator words (diagonalEquiv κ) =
      diagonalEquiv (iteratedHoppingDifference (words.map hoppingWordIncrement) κ) := by
  induction words generalizing κ with
  | nil => rfl
  | cons word words ih =>
      simp only [iteratedWordCommutator, differenceCommutator_diagonal, ih, List.map_cons,
        iteratedHoppingDifference]

/-- Literal nested commutators with arbitrary actual hopping words test exactly the
finite-difference equation on their total increments. -/
theorem iteratedWordCommutator_identity_iff (words : List (List (HoppingStep C)))
    (κ : C → CirclePhase) :
    (∀ ψ, iteratedWordCommutator words (diagonalEquiv κ) ψ = ψ) ↔
      iteratedHoppingDifference (words.map hoppingWordIncrement) κ = 0 := by
  rw [iteratedWordCommutator_diagonal]
  exact diagonal_eq_identity_iff _

end OpenDisk
