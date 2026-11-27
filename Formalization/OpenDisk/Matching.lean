import Formalization.OpenDisk.Symmetry

/-!
# Matching and excitation phase descent

The matching equation is equivalent to the residual hopping phase being a
function of curvature.  This proves the descent assertion in (5.4), without
silently assuming it.  The file also proves invariance of the literal square
phase under simultaneous diagonal conjugation.
-/

noncomputable section

namespace OpenDisk

variable {C A P : Type*} [AddCommGroup C] [AddCommGroup A] [AddCommGroup P]

/-- Matching, in the phase convention of equations (3.19) and (5.3). -/
def Matching (d : C →+ A) (β L : C → P) (s : C) : Prop :=
  ∀ (z : d.ker) v, difference L z v = difference (difference β z) s v

theorem matching_iff_closed_residual (d : C →+ A) (β L : C → P) (s : C) :
    Matching d β L s ↔ phaseDerivative d (L - difference β s) = 0 := by
  constructor
  · intro h
    ext z v
    change difference (L - difference β s) z v = 0
    rw [difference_sub, difference_comm, h, sub_self]
  · intro h z v
    have hv := congrArg (fun F : SymmetryPhase d P => F z v) h
    change difference (L - difference β s) z v = 0 at hv
    rw [difference_sub, difference_comm, sub_eq_zero] at hv
    exact hv

/-- The actual table `θ_s` exists precisely when the matching equation holds. -/
theorem matching_iff_descent (d : C →+ A) (hd : Function.Surjective d)
    (β L : C → P) (s : C) :
    Matching d β L s ↔ ∃ θ : A → P, ∀ v, θ (d v) = L v - difference β s v := by
  let rep := fun a => Classical.choose (hd a)
  have hr : ∀ a, d (rep a) = a := fun a => Classical.choose_spec (hd a)
  rw [matching_iff_closed_residual, phaseDerivative_eq_zero_iff d rep hr]
  constructor
  · rintro ⟨θ, hθ⟩
    exact ⟨θ, fun v => (congrFun hθ v).symm⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨θ, funext fun v => (hθ v).symm⟩

theorem descended_table_unique (d : C →+ A) (hd : Function.Surjective d)
    (β L : C → P) (s : C) (θ₀ θ₁ : A → P)
    (h₀ : ∀ v, θ₀ (d v) = L v - difference β s v)
    (h₁ : ∀ v, θ₁ (d v) = L v - difference β s v) : θ₀ = θ₁ := by
  funext a
  obtain ⟨v, rfl⟩ := hd a
  rw [h₀, h₁]

/-- Two joint data with exactly the same table have the stated phase difference.
Locality of this difference is a separate theorem, not an extra conclusion here. -/
theorem same_table_joint_difference (β₀ β₁ L₀ L₁ : C → P) (s : C)
    (h : L₀ - difference β₀ s = L₁ - difference β₁ s) :
    L₁ - L₀ = difference (β₁ - β₀) s := by
  funext v
  have hv := congrFun h v
  simp only [Pi.sub_apply] at hv ⊢
  rw [difference_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mpr (by simpa [sub_eq_add_neg, add_comm] using hv.symm)

/-- The square commutator phase with the report's order `[U(t), U(s)]`. -/
def squarePhase (L : C → C → P) (s t v : C) : P :=
  difference (L t) s v - difference (L s) t v

/-- Conjugating every hopping by the same diagonal phase preserves square phases. -/
theorem squarePhase_gauge_invariant (L : C → C → P) (β : C → P) (s t v : C) :
    squarePhase (fun r => L r + difference β r) s t v = squarePhase L s t v := by
  simp only [squarePhase, difference_add]
  rw [difference_comm β t s v]
  abel

/-- Pullback along a coboundary intertwines finite differences. -/
theorem difference_pullback (d : C →+ A) (f : A → P) (s v : C) :
    difference (f ∘ d) s v = difference f (d s) (d v) := by
  simp [difference, Function.comp_def]

/-- Matching is automatic for a phase table and any excitation table. -/
theorem matching_of_table (d : C →+ A) (β : C → P) (θ : A → P) (s : C) :
    Matching d β (θ ∘ d + difference β s) s := by
  intro z v
  rw [difference_add, difference_pullback]
  have hz : d z = 0 := z.property
  rw [hz, difference_zero, zero_add, difference_comm]

end OpenDisk
