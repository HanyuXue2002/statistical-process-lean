import Formalization.OpenDisk.Symmetry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual complex amplitudes and invariant configuration spaces

The phase group is `ℝ/ℤ`, with its faithful exponential into the complex unit
circle.  We prove the SRE invariant-state criterion and the configuration-space
linear equivalence, hence its exact dimension (Propositions 3.2 and 3.5).
The unit-modulus phase vector is used first; a separate theorem shows that any
nonzero normalization gives exactly the same criterion.
-/

noncomputable section

namespace OpenDisk

abbrev CirclePhase := AddCircle (1 : ℝ)

/-- The actual complex phase `exp(2πi p)`, well-defined on `ℝ/ℤ`. -/
def phaseWeight (p : CirclePhase) : ℂ := AddCircle.toCircle p

@[simp] theorem phaseWeight_zero : phaseWeight 0 = 1 := by simp [phaseWeight]

theorem phaseWeight_add (p q : CirclePhase) :
    phaseWeight (p + q) = phaseWeight p * phaseWeight q := by
  simp [phaseWeight, AddCircle.toCircle_add]

theorem phaseWeight_neg (p : CirclePhase) : phaseWeight (-p) = (phaseWeight p)⁻¹ := by
  simp [phaseWeight, AddCircle.toCircle_neg]

theorem phaseWeight_sub (p q : CirclePhase) :
    phaseWeight (p - q) = phaseWeight p / phaseWeight q := by
  rw [sub_eq_add_neg, phaseWeight_add, phaseWeight_neg, div_eq_mul_inv]

@[simp] theorem phaseWeight_ne_zero (p : CirclePhase) : phaseWeight p ≠ 0 :=
  Circle.coe_ne_zero _

theorem phaseWeight_injective : Function.Injective phaseWeight := by
  intro p q h
  apply AddCircle.injective_toCircle one_ne_zero
  exact Subtype.ext h

@[simp] theorem norm_phaseWeight (p : CirclePhase) : ‖phaseWeight p‖ = 1 :=
  Circle.norm_coe _

variable {C A : Type*} [AddCommGroup C] [AddCommGroup A]

/-- The unit-modulus coefficient vector before the common scalar normalization. -/
def phaseState (β : C → CirclePhase) : C → ℂ := fun v => phaseWeight (β v)

/-- Literal coefficient equations for the invariant complex vector subspace. -/
def invariantSpace (d : C →+ A) (F : SymmetryPhase d CirclePhase) : Submodule ℂ (C → ℂ) where
  carrier := {ψ | ∀ (z : d.ker) v, ψ (v + z) = phaseWeight (F z v) * ψ v}
  zero_mem' := by simp
  add_mem' := by
    intro ψ χ hψ hχ z v
    simp only [Pi.add_apply, hψ z v, hχ z v, mul_add]
  smul_mem' := by
    intro k ψ hψ z v
    simp only [Pi.smul_apply, smul_eq_mul, hψ z v]
    ring

instance (d : C →+ A) (F : SymmetryPhase d CirclePhase) :
    CoeFun (invariantSpace d F) (fun _ => C → ℂ) := ⟨Subtype.val⟩

/-- Proposition 3.5, with faithful complex phases rather than formal symbols. -/
theorem phaseState_mem_iff (d : C →+ A) (F : SymmetryPhase d CirclePhase)
    (β : C → CirclePhase) :
    phaseState β ∈ invariantSpace d F ↔ F = phaseDerivative d β := by
  constructor
  · intro h
    ext z v
    have hv := h z v
    change phaseWeight (β (v + z)) = phaseWeight (F z v) * phaseWeight (β v) at hv
    have hh : F z v + β v = β (v + z) :=
      phaseWeight_injective (by rw [phaseWeight_add]; exact hv.symm)
    exact eq_sub_iff_add_eq.mpr hh
  · rintro rfl z v
    change phaseWeight (β (v + z)) = phaseWeight (β (v + z) - β v) * phaseWeight (β v)
    rw [phaseWeight_sub, div_mul_cancel₀ _ (phaseWeight_ne_zero _)]

/-- Multiplying by the physical normalization does not alter invariance. -/
theorem normalized_phaseState_mem_iff (d : C →+ A) (F : SymmetryPhase d CirclePhase)
    (β : C → CirclePhase) (r : ℂ) (hr : r ≠ 0) :
    r • phaseState β ∈ invariantSpace d F ↔ F = phaseDerivative d β := by
  rw [← phaseState_mem_iff d F β]
  constructor
  · intro h
    have hh := (invariantSpace d F).smul_mem r⁻¹ h
    simpa [smul_smul, hr] using hh
  · exact (invariantSpace d F).smul_mem r

/-- The SRE existence criterion, parameterized by the specified local-function locus.
This theorem does not identify that locus with a topological component. -/
theorem sre_criterion (d : C →+ A) (F : SymmetryPhase d CirclePhase)
    (localPhases : Set (C → CirclePhase)) :
    (∃ β ∈ localPhases, phaseState β ∈ invariantSpace d F) ↔
      ∃ β ∈ localPhases, F = phaseDerivative d β := by
  simp only [phaseState_mem_iff]

variable (d : C →+ A) (rep : A → C) (hrep : ∀ a, d (rep a) = a)

/-- Proposition 3.2: one independent complex coefficient per curvature fiber. -/
def configurationEquiv (β : C → CirclePhase) :
    (A → ℂ) ≃ₗ[ℂ] invariantSpace d (phaseDerivative d β) where
  toFun k := ⟨fun v => phaseWeight (β v) * k (d v), by
    intro z v
    change phaseWeight (β (v + z)) * k (d (v + z)) =
      phaseWeight (β (v + z) - β v) * (phaseWeight (β v) * k (d v))
    have hz : d z = 0 := z.property
    rw [map_add, hz, add_zero, phaseWeight_sub, ← mul_assoc,
      div_mul_cancel₀ _ (phaseWeight_ne_zero _)]⟩
  invFun ψ a := ψ (rep a) / phaseWeight (β (rep a))
  left_inv k := by
    funext a
    change (phaseWeight (β (rep a)) * k (d (rep a))) / phaseWeight (β (rep a)) = k a
    rw [hrep, mul_div_cancel_left₀ _ (phaseWeight_ne_zero _)]
  right_inv ψ := by
    apply Subtype.ext
    funext v
    have hv := ψ.property (fiberDisplacement d rep hrep v) (rep (d v))
    have hc : rep (d v) + ↑(fiberDisplacement d rep hrep v) = v := by
      change rep (d v) + (v - rep (d v)) = v
      abel
    simp only [phaseDerivative_apply, hc, phaseWeight_sub] at hv
    change phaseWeight (β v) * (ψ (rep (d v)) / phaseWeight (β (rep (d v)))) = ψ v
    rw [hv]
    ring
  map_add' k l := by
    apply Subtype.ext
    funext v
    exact mul_add _ _ _
  map_smul' k l := by
    apply Subtype.ext
    funext v
    change phaseWeight (β v) * (k * l (d v)) = k * (phaseWeight (β v) * l (d v))
    ring

include rep hrep in
/-- The exact dimension of the literal embedded invariant space. -/
theorem finrank_invariantSpace [Fintype A] (β : C → CirclePhase) :
    Module.finrank ℂ (invariantSpace d (phaseDerivative d β)) = Fintype.card A := by
  rw [← (configurationEquiv d rep hrep β).finrank_eq]
  exact Module.finrank_pi _

end OpenDisk
