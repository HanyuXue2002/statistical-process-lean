import Formalization.SimplicialConeContraction
import Formalization.SimplicialCoboundarySquare
import Formalization.CoordinateExtension

set_option linter.style.header false

/-!
# Section 3: replacing cone-apex cochains

On a simplicial closed star with chosen apex `v`, put

`bottom(t) = h (d t)`.

The cone identity and `d² = 0` imply that `bottom(t)` has the same
coboundary as `t`.  By construction it vanishes on every simplex containing
`v`.  For a cochain concentrated at one apex simplex, every coordinate which
survives the replacement contains the non-apex face of the original simplex.
This is the coordinate form of the support-nonincreasing assertion used in
the cone-operator replacement argument.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-! ## The closed-star differential squares to zero -/

/-- Extend a closed-star cochain by zero to all simplices of `K`.

This is only an auxiliary device for importing the already proved global
identity `d² = 0` into the closed star. -/
private def closedStarZeroExtension
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    ClosedStarCochain K η n G →ₗ[ℤ] Cochain K n G :=
  (coordinateExtension
    {τ : Simplex K n | τ.1 ∪ η.1 ∈ K}).toIntLinearMap

private theorem restrictClosedStar_closedStarZeroExtension
    (η : {s : Finset V // s ∈ K}) (n : ℕ)
    (c : ClosedStarCochain K η n G) :
    restrictClosedStar K η n (closedStarZeroExtension K η n c) = c := by
  ext τ
  exact coordinateExtension_apply_mem
    {σ : Simplex K n | σ.1 ∪ η.1 ∈ K} c τ.2

/-- The ordered coboundary on a closed star squares to zero. -/
@[simp]
theorem closedStarCoboundary_closedStarCoboundary
    (η : {s : Finset V // s ∈ K}) (n : ℕ)
    (c : ClosedStarCochain K η n G) :
    closedStarCoboundary K η (n + 1)
        (closedStarCoboundary K η n c) = 0 := by
  let e : Cochain K n G := closedStarZeroExtension K η n c
  have hre : restrictClosedStar K η n e = c :=
    restrictClosedStar_closedStarZeroExtension K η n c
  have h₁ := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) K η n) e
  have h₂ := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) K η (n + 1))
      (coboundary K n e)
  have h₁' :
      restrictClosedStar K η (n + 1) (coboundary K n e) =
        closedStarCoboundary K η n (restrictClosedStar K η n e) := by
    simpa only [LinearMap.comp_apply] using h₁
  have h₂' :
      restrictClosedStar K η (n + 2)
          (coboundary K (n + 1) (coboundary K n e)) =
        closedStarCoboundary K η (n + 1)
          (restrictClosedStar K η (n + 1) (coboundary K n e)) := by
    simpa only [LinearMap.comp_apply, Nat.add_assoc] using h₂
  calc
    closedStarCoboundary K η (n + 1)
        (closedStarCoboundary K η n c) =
      closedStarCoboundary K η (n + 1)
        (closedStarCoboundary K η n
          (restrictClosedStar K η n e)) := by rw [hre]
    _ = closedStarCoboundary K η (n + 1)
        (restrictClosedStar K η (n + 1) (coboundary K n e)) := by
          rw [h₁']
    _ = restrictClosedStar K η (n + 2)
        (coboundary K (n + 1) (coboundary K n e)) := by
          rw [h₂']
    _ = 0 := by rw [coboundary_coboundary]; simp

/-! ## The uniform bottom replacement -/

/-- Replace a cochain by the cone homotopy applied to its coboundary:
`bottom(t) = h (d t)`.

The definition is uniform in the cochain degree, including degree zero. -/
def coneBottomReplacement
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    ClosedStarCochain K η n G →ₗ[ℤ] ClosedStarCochain K η n G :=
  (coneHomotopy K η v hvη n).comp (closedStarCoboundary K η n)

@[simp]
theorem coneBottomReplacement_apply
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G) :
    coneBottomReplacement K η v hvη n t =
      coneHomotopy K η v hvη n (closedStarCoboundary K η n t) :=
  rfl

/-- `bottom(t)` and `t` have exactly the same configuration coboundary. -/
theorem closedStarCoboundary_coneBottomReplacement
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G) :
    closedStarCoboundary K η n
        (coneBottomReplacement K η v hvη n t) =
      closedStarCoboundary K η n t := by
  have hcontract := closedStar_contraction_positive K η v hvη n
    (closedStarCoboundary K η n t)
  rw [closedStarCoboundary_closedStarCoboundary K η n t] at hcontract
  simpa [coneBottomReplacement] using hcontract

/-- The replacement has no coordinate on a simplex containing the apex. -/
@[simp]
theorem coneBottomReplacement_apply_of_apex_mem
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G)
    (σ : ClosedStarSimplex K η n) (hvσ : v ∈ σ.1.1) :
    coneBottomReplacement K η v hvη n t σ = 0 := by
  exact coneHomotopy_apply_of_mem K η v hvη n
    (closedStarCoboundary K η n t) σ hvσ

/-- Equivalently, the finite coordinate support of the replacement is
disjoint from all simplices containing the apex. -/
theorem apex_not_mem_of_mem_coneBottomReplacement_support
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G)
    (σ : ClosedStarSimplex K η n)
    (hσ : σ ∈ (coneBottomReplacement K η v hvη n t).support) :
    v ∉ σ.1.1 := by
  intro hvσ
  exact Finsupp.mem_support_iff.mp hσ
    (coneBottomReplacement_apply_of_apex_mem K η v hvη n t σ hvσ)

/-! ## Coordinate support of one elementary apex cochain -/

/-- If `t` is concentrated on one simplex `τ` containing the apex, then
every simplex occurring in `bottom(t)` contains the base face `τ \ {v}`.

Together with `apex_not_mem_of_mem_coneBottomReplacement_support`, this says
that the replacement exchanges the apex for a bottom vertex and never
enlarges the carrier support (reverse inclusion of carrier stars). -/
theorem erase_apex_subset_of_mem_coneBottomReplacement_single_support
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (τ : ClosedStarSimplex K η n) (_hvτ : v ∈ τ.1.1) (g : G)
    (σ : ClosedStarSimplex K η n)
    (hσ : σ ∈
      (coneBottomReplacement K η v hvη n (Finsupp.single τ g)).support) :
    τ.1.1.erase v ⊆ σ.1.1 := by
  have hvσ : v ∉ σ.1.1 :=
    apex_not_mem_of_mem_coneBottomReplacement_support
      K η v hvη n _ σ hσ
  have hvalue :
      coneBottomReplacement K η v hvη n (Finsupp.single τ g) σ ≠ 0 :=
    Finsupp.mem_support_iff.mp hσ
  let I : ClosedStarSimplex K η (n + 1) :=
    insertClosedStarVertex K v hvη σ hvσ
  have hdne :
      closedStarCoboundary K η n (Finsupp.single τ g) I ≠ 0 := by
    intro hdzero
    apply hvalue
    rw [coneBottomReplacement_apply,
      coneHomotopy_apply_of_not_mem K η v hvη n _ σ hvσ]
    change incidenceSign K I.1 v •
      closedStarCoboundary K η n (Finsupp.single τ g) I = 0
    rw [hdzero, smul_zero]
  have hex : ∃ w : I.1.1,
      eraseClosedStarVertex K I w.1 w.2 = τ := by
    by_contra h
    push Not at h
    apply hdne
    rw [closedStarCoboundary_apply]
    apply Fintype.sum_eq_zero
    intro w
    simp [h w]
  rcases hex with ⟨w, hw⟩
  have hsets : (insert v σ.1.1).erase w.1 = τ.1.1 := by
    exact congrArg (fun x : ClosedStarSimplex K η n => x.1.1) hw
  intro x hx
  have hxdata : x ≠ v ∧ x ∈ τ.1.1 := Finset.mem_erase.mp hx
  have hxErase : x ∈ (insert v σ.1.1).erase w.1 := by
    rw [hsets]
    exact hxdata.2
  have hxInsert : x ∈ insert v σ.1.1 := Finset.mem_of_mem_erase hxErase
  rcases Finset.mem_insert.mp hxInsert with hxv | hxσ'
  · exact (hxdata.1 hxv).elim
  · exact hxσ'

/-- Combined coordinate statement for an elementary apex cochain. -/
theorem coneBottomReplacement_single_support_coordinate
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (τ : ClosedStarSimplex K η n) (hvτ : v ∈ τ.1.1) (g : G)
    (σ : ClosedStarSimplex K η n)
    (hσ : σ ∈
      (coneBottomReplacement K η v hvη n (Finsupp.single τ g)).support) :
    v ∉ σ.1.1 ∧ τ.1.1.erase v ⊆ σ.1.1 :=
  ⟨apex_not_mem_of_mem_coneBottomReplacement_support
      K η v hvη n _ σ hσ,
    erase_apex_subset_of_mem_coneBottomReplacement_single_support
      K η v hvη n τ hvτ g σ hσ⟩

end GeneralSphereT.SimplicialCochain
