import Formalization.FiniteSimplicialCochain

set_option linter.style.header false

/-!
# Incidence-sign cancellation for ordered simplices

The two possible orders of deleting distinct vertices have opposite total
incidence signs.  This is the elementary sign calculation behind both
`d² = 0` and the cone cochain contraction.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

variable {V : Type*} [LinearOrder V]

/-- Number of vertices of `s` strictly below `v`. -/
def lowerCount (s : Finset V) (v : V) : ℕ :=
  (s.filter fun w => w < v).card

theorem lowerCount_erase_of_lt
    {s : Finset V} {v w : V} (hv : v ∈ s) (hvw : v < w) :
    lowerCount (s.erase v) w + 1 = lowerCount s w := by
  classical
  rw [lowerCount, lowerCount, Finset.filter_erase]
  have hvf : v ∈ s.filter fun x => x < w := by simp [hv, hvw]
  rw [Finset.card_erase_of_mem hvf]
  exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨v, hvf⟩)

theorem lowerCount_erase_of_not_lt
    {s : Finset V} {v w : V} (hvw : ¬ v < w) :
    lowerCount (s.erase v) w = lowerCount s w := by
  classical
  rw [lowerCount, lowerCount, Finset.filter_erase]
  have hvf : v ∉ s.filter fun x => x < w := by simp [hvw]
  rw [Finset.erase_eq_of_notMem hvf]

theorem negOnePow_mul_negOnePow_succ (a b : ℕ) :
    (-1 : ℤ) ^ a * (-1 : ℤ) ^ b =
      -((-1 : ℤ) ^ a * (-1 : ℤ) ^ (b + 1)) := by
  rw [pow_succ]
  ring

theorem orderedDeletionSign
    {s : Finset V} {v w : V}
    (hv : v ∈ s) (hw : w ∈ s) (hvw : v ≠ w) :
    (-1 : ℤ) ^ lowerCount s v *
        (-1 : ℤ) ^ lowerCount (s.erase v) w =
      -((-1 : ℤ) ^ lowerCount s w *
        (-1 : ℤ) ^ lowerCount (s.erase w) v) := by
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · have h₁ := lowerCount_erase_of_not_lt
      (s := s) (v := w) (w := v) (not_lt_of_ge hvwlt.le)
    have h₂ := lowerCount_erase_of_lt (s := s) hv hvwlt
    rw [h₁, ← h₂, pow_succ]
    ring
  · have h₁ := lowerCount_erase_of_not_lt
      (s := s) (v := v) (w := w) (not_lt_of_ge hwvlt.le)
    have h₂ := lowerCount_erase_of_lt (s := s) hw hwvlt
    rw [h₁, ← h₂, pow_succ]
    ring

variable {G : Type*} [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

theorem incidenceSign_eq_lowerCount {n : ℕ}
    (τ : Simplex K (n + 1)) (v : V) :
    incidenceSign K τ v = (-1 : ℤ) ^ lowerCount τ.1 v :=
  rfl

/-- Deleting two distinct vertices in the two possible orders gives opposite
total incidence signs. -/
theorem incidenceSign_delete_delete
    {n : ℕ} (τ : Simplex K (n + 2))
    (v w : V) (hv : v ∈ τ.1) (hw : w ∈ τ.1) (hvw : v ≠ w) :
    incidenceSign K τ v *
        incidenceSign K (eraseVertex K τ v hv) w =
      -(incidenceSign K τ w *
        incidenceSign K (eraseVertex K τ w hw) v) := by
  change
    (-1 : ℤ) ^ lowerCount τ.1 v *
        (-1 : ℤ) ^ lowerCount (τ.1.erase v) w =
      -((-1 : ℤ) ^ lowerCount τ.1 w *
        (-1 : ℤ) ^ lowerCount (τ.1.erase w) v)
  exact orderedDeletionSign hv hw hvw

end GeneralSphereT.SimplicialCochain
