import Formalization.OpenDisk.HoppingOperators
import Formalization.OpenDisk.BulkPhaseHilbert
import Mathlib.Tactic.Linarith

/-! # Hilbert space unitarity and normalized full-support states -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace OpenDisk
open BulkPhaseHilbert

variable {C P : Type*} [Fintype C] [AddCommGroup C] [AddCommGroup P]

theorem phaseTranslate_inner (χ : AddChar P Circle) (s : C) (L : C → P)
    (f g : EuclideanSpace ℂ C) :
    inner ℂ (phaseTranslateLinear χ s L f) (phaseTranslateLinear χ s L g) = inner ℂ f g := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  have heq (c : C) :
      conj (phaseTranslateLinear χ s L f c) * phaseTranslateLinear χ s L g c =
        conj (f (c - s)) * g (c - s) := by
    change conj ((χ (L (c - s)) : ℂ) * f (c - s)) *
      ((χ (L (c - s)) : ℂ) * g (c - s)) = _
    rw [map_mul]
    calc
      _ = (conj (χ (L (c - s)) : ℂ) * (χ (L (c - s)) : ℂ)) *
          (conj (f (c - s)) * g (c - s)) := by ring
      _ = _ := by rw [circle_conj_mul, one_mul]
  simp_rw [heq]
  exact (Equiv.subRight s).sum_comp (fun c => conj (f c) * g c)

/-- The phase-weighted hopping is an actual unitary operator on the finite Hilbert space. -/
def hoppingUnitary (χ : AddChar P Circle) (s : C) (L : C → P) :
    EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C := by
  let u := (phaseTranslateLinear χ s L).isometryOfInner (phaseTranslate_inner χ s L)
  apply LinearIsometryEquiv.ofSurjective u
  intro f
  refine ⟨WithLp.toLp 2 (fun c => (χ (L c) : ℂ)⁻¹ * f (c + s)), ?_⟩
  ext c
  change (χ (L (c - s)) : ℂ) * ((χ (L (c - s)) : ℂ)⁻¹ * f (c - s + s)) = f c
  rw [sub_add_cancel, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]

theorem uniformState_inner_self [Nonempty C] (χ : AddChar P Circle) (β : C → P) :
    inner ℂ (uniformState χ β) (uniformState χ β) = 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  have heq (c : C) : conj (uniformState χ β c) * uniformState χ β c =
      conj (normalization C) * normalization C := by
    change conj (normalization C * (χ (β c) : ℂ)) *
      (normalization C * (χ (β c) : ℂ)) = _
    rw [map_mul]
    calc
      _ = (conj (normalization C) * normalization C) *
          (conj (χ (β c) : ℂ) * (χ (β c) : ℂ)) := by ring
      _ = _ := by rw [circle_conj_mul, mul_one]
  simp_rw [heq]
  exact normalization_sum C

/-- The scalar used in the report has exactly unit Hilbert-space norm. -/
theorem uniformState_norm [Nonempty C] (χ : AddChar P Circle) (β : C → P) :
    ‖uniformState χ β‖ = 1 := by
  have h : ‖uniformState χ β‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), uniformState_inner_self]
    rfl
  nlinarith [norm_nonneg (uniformState χ β)]

theorem normalization_ne_zero (D : Type*) [Fintype D] [Nonempty D] :
    normalization D ≠ 0 := by
  have hn : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  simp only [normalization, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
  exact ne_of_gt (Real.sqrt_pos.2 hn)

/-- The normalized physical SRE state obeys the same exact invariant-space criterion. -/
theorem normalized_sre_mem_iff {A : Type*} [AddCommGroup A]
    (d : C →+ A) (F : SymmetryPhase d CirclePhase) (β : C → CirclePhase) :
    (uniformState (AddCircle.toCircle_addChar (T := 1)) β).ofLp ∈ invariantSpace d F ↔
      F = phaseDerivative d β :=
  normalized_phaseState_mem_iff d F β (normalization C) (normalization_ne_zero C)

end OpenDisk
