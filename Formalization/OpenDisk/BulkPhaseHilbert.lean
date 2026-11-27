import Formalization.OpenDisk.BulkPhase
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual conditional-sum isometry

For fixed cochain coordinates, restriction is the projection `I × B → B`,
where `I` comprises all internal coordinates. This module proves Proposition
4.2 in finite-dimensional complex Hilbert space, for any unit-modulus additive
character of the phase group. The paper's character is
`AddCircle.toCircle_addChar` with period one.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace OpenDisk.BulkPhaseHilbert

open scoped BigOperators ComplexConjugate

variable {I B P : Type*} [Fintype I] [Fintype B] [AddCommGroup P]

/-- The positive normalization of a uniform sum over `I`. -/
def normalization (I : Type*) [Fintype I] : ℂ :=
  ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℝ)

theorem normalization_sum (I : Type*) [Fintype I] [Nonempty I] :
    ∑ _ : I, conj (normalization I) * normalization I = 1 := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card I : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ Fintype.card I by positivity)
  have hreal : (Fintype.card I : ℝ) *
      ((Real.sqrt (Fintype.card I : ℝ))⁻¹ * (Real.sqrt (Fintype.card I : ℝ))⁻¹) = 1 := by
    calc
      _ = (Real.sqrt (Fintype.card I : ℝ) * Real.sqrt (Fintype.card I : ℝ)) *
          ((Real.sqrt (Fintype.card I : ℝ))⁻¹ * (Real.sqrt (Fintype.card I : ℝ))⁻¹) :=
        congrArg (fun x => x * ((Real.sqrt (Fintype.card I : ℝ))⁻¹ *
          (Real.sqrt (Fintype.card I : ℝ))⁻¹)) hsq.symm
      _ = 1 := by field_simp
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, normalization,
    Complex.conj_ofReal, Complex.ofReal_inv, Complex.ofReal_mul, map_inv₀,
    Complex.ofReal_natCast, Complex.ofReal_one] using
    congrArg Complex.ofReal hreal

theorem circle_conj_mul (z : Circle) : conj (z : ℂ) * z = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

/-- Conditional summation over every internal coordinate, written as its exact
coefficient function. -/
def conditionalLinear (χ : AddChar P Circle) (φ : I × B → P) :
    EuclideanSpace ℂ B →ₗ[ℂ] EuclideanSpace ℂ (I × B) where
  toFun f := WithLp.toLp 2 (fun c => normalization I * (χ (φ c) : ℂ) * f c.2)
  map_add' f g := by
    ext c
    change normalization I * (χ (φ c) : ℂ) * (f c.2 + g c.2) = _
    simp only [mul_add]
    rfl
  map_smul' a f := by
    ext c
    change normalization I * (χ (φ c) : ℂ) * (a * f c.2) =
      a * (normalization I * (χ (φ c) : ℂ) * f c.2)
    ring

@[simp] theorem conditionalLinear_apply (χ : AddChar P Circle) (φ : I × B → P)
    (f : EuclideanSpace ℂ B) (c : I × B) :
    conditionalLinear χ φ f c = normalization I * (χ (φ c) : ℂ) * f c.2 := rfl

theorem conditionalLinear_inner [Nonempty I] (χ : AddChar P Circle) (φ : I × B → P)
    (f g : EuclideanSpace ℂ B) :
    inner ℂ (conditionalLinear χ φ f) (conditionalLinear χ φ g) = inner ℂ f g := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', conditionalLinear_apply]
  have hpoint : ∀ c : I × B,
      conj (normalization I * (χ (φ c) : ℂ) * f c.2) *
          (normalization I * (χ (φ c) : ℂ) * g c.2) =
        (conj (normalization I) * normalization I) * (conj (f c.2) * g c.2) := by
    intro c
    simp only [map_mul]
    calc
      _ = (conj (normalization I) * normalization I) *
            (conj (χ (φ c) : ℂ) * (χ (φ c) : ℂ)) * (conj (f c.2) * g c.2) := by ring
      _ = _ := by rw [circle_conj_mul, mul_one]
  simp_rw [hpoint]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  have hn := normalization_sum I
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_assoc, mul_left_comm, one_mul] using
    congrArg (fun t : ℂ => t * ∑ b : B, conj (f b) * g b) hn

/-- The conditional-sum map is a genuine complex linear isometry. -/
def conditionalIsometry [Nonempty I] (χ : AddChar P Circle) (φ : I × B → P) :
    EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ (I × B) :=
  (conditionalLinear χ φ).isometryOfInner (conditionalLinear_inner χ φ)

section Translations

variable [AddCommGroup I] [AddCommGroup B]

/-- The unphased ket translation, acting on coefficient functions. -/
def translateLinear (y : I × B) : EuclideanSpace ℂ (I × B) →ₗ[ℂ] EuclideanSpace ℂ (I × B) where
  toFun f := WithLp.toLp 2 (fun c => f (c - y))
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `|b⟩ ↦ χ(L(b)) |b+s⟩`, with its exact phase retained. -/
def phaseTranslateLinear (χ : AddChar P Circle) (s : B) (L : B → P) :
    EuclideanSpace ℂ B →ₗ[ℂ] EuclideanSpace ℂ B where
  toFun f := WithLp.toLp 2 (fun b => (χ (L (b - s)) : ℂ) * f (b - s))
  map_add' _ _ := by ext; simp [mul_add]
  map_smul' a f := by
    ext b
    change (χ (L (b - s)) : ℂ) * (a * f.ofLp (b - s)) =
      a * ((χ (L (b - s)) : ℂ) * f.ofLp (b - s))
    ring

/-- Equation (4.3) as an equality of actual complex vectors. The hypothesis is
the single closed-translation response equation from (4.1). -/
theorem conditionalLinear_intertwines (χ : AddChar P Circle) (φ : I × B → P)
    (y : I × B) (F : B → P)
    (hresponse : ∀ c, φ (c + y) - φ c = -F c.2) (f : EuclideanSpace ℂ B) :
    translateLinear y (conditionalLinear χ φ f) =
      conditionalLinear χ φ (phaseTranslateLinear χ y.2 F f) := by
  ext c
  have h := hresponse (c - y)
  simp only [sub_add_cancel] at h
  rw [sub_eq_iff_eq_add] at h
  have heq : φ (c - y) = φ c + F (c - y).2 := by
    calc
      _ = F (c - y).2 + (-F (c - y).2 + φ (c - y)) := by abel
      _ = F (c - y).2 + φ c := by rw [h]
      _ = _ := add_comm _ _
  change normalization I * (χ (φ (c - y)) : ℂ) * f (c - y).2 =
    normalization I * (χ (φ c) : ℂ) * ((χ (F (c.2 - y.2)) : ℂ) * f (c.2 - y.2))
  rw [heq, χ.map_add_eq_mul, Circle.coe_mul]
  change normalization I * ((χ (φ c) : ℂ) * (χ (F (c.2 - y.2)) : ℂ)) *
      f (c.2 - y.2) = _
  ring

/-- Injectivity of the actual encoding identifies fixed vectors exactly. -/
theorem conditional_fixed_iff (χ : AddChar P Circle) (φ : I × B → P)
    (y : I × B) (F : B → P)
    (hresponse : ∀ c, φ (c + y) - φ c = -F c.2) (f : EuclideanSpace ℂ B) :
    translateLinear y (conditionalLinear χ φ f) = conditionalLinear χ φ f ↔
      phaseTranslateLinear χ y.2 F f = f := by
  rw [conditionalLinear_intertwines χ φ y F hresponse]
  exact (conditionalIsometry χ φ).injective.eq_iff

end Translations

/-- The normalized full-support state `Σ(φ)`. -/
def uniformState {D : Type*} [Fintype D] (χ : AddChar P Circle) (φ : D → P) :
    EuclideanSpace ℂ D := WithLp.toLp 2 (fun c => normalization D * (χ (φ c) : ℂ))

theorem normalization_prod : normalization (I × B) = normalization I * normalization B := by
  simp [normalization, Fintype.card_prod, Nat.cast_mul, Real.sqrt_mul,
    mul_comm, Complex.ofReal_mul]

/-- Equation (4.4), including its normalization and global phase. -/
theorem conditional_uniformState (χ : AddChar P Circle) (φ : I × B → P) (β : B → P) :
    conditionalLinear χ φ (uniformState χ β) =
      uniformState χ (fun c => φ c + β c.2) := by
  ext c
  change normalization I * (χ (φ c) : ℂ) *
      (normalization B * (χ (β c.2) : ℂ)) =
    normalization (I × B) * (χ (φ c + β c.2) : ℂ)
  rw [normalization_prod, χ.map_add_eq_mul, Circle.coe_mul]
  ring

end OpenDisk.BulkPhaseHilbert
