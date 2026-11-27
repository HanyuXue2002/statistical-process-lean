import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel

/-!
# Cone primitives: the algebraic content of Lemma 3.7

This file works with an additive group of cochains `C`, its subgroup `Z` of closed
cochains, and an additive choice of base representative. A simplicial cone
contraction is expected to supply `Splitting`; no assertion about a particular
simplicial complex is made here. In the paper the base representative is `hₚ d c`.
The phase group can be `AddCircle (1 : ℝ)`; all results hold for any abelian group.
-/

namespace OpenDisk.ConePhase

variable {C P : Type*} [AddCommGroup C] [AddCommGroup P]

/-- Algebraic data furnished by a cone contraction. -/
structure Splitting (Z : AddSubgroup C) where
  base : C →+ C
  base_closed : ∀ z : Z, base z = 0
  remainder_closed : ∀ c, c - base c ∈ Z

/-- A differential and contracting map supply the splitting whenever `d h d = d`.
The concrete simplicial identity is proved in `ConePhaseSimplicial`. -/
def splittingOfDifferential {D : Type*} [AddCommGroup D]
    (d : C →+ D) (h : D →+ C) (hdh : ∀ c, d (h (d c)) = d c) : Splitting d.ker where
  base := h.comp d
  base_closed := by
    intro z
    change h (d z) = 0
    rw [show d z = 0 from z.property, map_zero]
  remainder_closed := by
    intro c
    change d (c - h (d c)) = 0
    rw [map_sub, hdh, sub_self]

namespace Splitting

variable {Z : AddSubgroup C} (S : Splitting Z)

/-- The closed part of a cochain. -/
def closedPart (c : C) : Z := ⟨c - S.base c, S.remainder_closed c⟩

@[simp] theorem coe_closedPart (c : C) : (S.closedPart c : C) = c - S.base c := rfl

theorem base_add_closed (c : C) (z : Z) : S.base (c + z) = S.base c := by
  simp [S.base_closed]

theorem base_add_closedPart (c : C) : S.base c + S.closedPart c = c := by
  simp [closedPart]

theorem closedPart_add_closed (c : C) (z : Z) :
    S.closedPart (c + z) = S.closedPart c + z := by
  apply Subtype.ext
  simp only [coe_closedPart, AddSubgroup.coe_add, S.base_add_closed]
  abel

@[simp] theorem base_idempotent (c : C) : S.base (S.base c) = S.base c := by
  have h := S.base_closed (S.closedPart c)
  exact (sub_eq_zero.mp (by simpa [closedPart] using h)).symm

@[simp] theorem closedPart_base (c : C) : S.closedPart (S.base c) = 0 := by
  apply Subtype.ext
  simp

/-- Every closed-invariant phase table factors through the canonical base slice. -/
theorem invariant_eq_base {f : C → P}
    (hf : ∀ (z : Z) c, f (c + z) = f c) (c : C) : f c = f (S.base c) := by
  simpa only [S.base_add_closedPart] using hf (S.closedPart c) (S.base c)

end Splitting

/-- The phase law for closed translations, retaining the complete phase. -/
def IsCocycle {Z : AddSubgroup C} (R : Z → C → P) : Prop :=
  (∀ c, R 0 c = 0) ∧
  ∀ z w c, R (z + w) c = R z c + R w (c + z)

/-- The cone primitive from the paper: evaluate on closed and base parts. -/
def primitive {Z : AddSubgroup C} (S : Splitting Z) (R : Z → C → P) (c : C) : P :=
  R (S.closedPart c) (S.base c)

theorem primitive_difference {Z : AddSubgroup C} (S : Splitting Z)
    {R : Z → C → P} (hR : IsCocycle R) (z : Z) (c : C) :
    primitive S R (c + z) - primitive S R c = R z c := by
  unfold primitive
  rw [S.base_add_closed, S.closedPart_add_closed, hR.2]
  rw [S.base_add_closedPart]
  abel

@[simp] theorem primitive_base {Z : AddSubgroup C} (S : Splitting Z)
    {R : Z → C → P} (hR : IsCocycle R) (c : C) :
    primitive S R (S.base c) = 0 := by
  simp [primitive, hR.1]

/-- A primitive is uniquely determined once its value on the base slice is zero. -/
theorem primitive_unique {Z : AddSubgroup C} (S : Splitting Z)
    {R : Z → C → P} {f : C → P}
    (hf : ∀ (z : Z) c, f (c + z) - f c = R z c)
    (hbase : ∀ c, f (S.base c) = 0) : f = primitive S R := by
  funext c
  have h := hf (S.closedPart c) (S.base c)
  simpa only [S.base_add_closedPart, hbase, sub_zero, primitive] using h

/-- Every other primitive differs from the canonical one by a closed-invariant table. -/
theorem primitive_difference_invariant {Z : AddSubgroup C} (S : Splitting Z)
    {R : Z → C → P} (hR : IsCocycle R) {f : C → P}
    (hf : ∀ (z : Z) c, f (c + z) - f c = R z c) (z : Z) (c : C) :
    (f (c + z) - primitive S R (c + z)) = (f c - primitive S R c) := by
  have h₁ := hf z c
  have h₂ := primitive_difference S hR z c
  rw [sub_eq_iff_eq_add] at h₁ h₂
  rw [h₁, h₂]
  abel

theorem primitive_add {Z : AddSubgroup C} (S : Splitting Z)
    (R T : Z → C → P) :
    primitive S (fun z c => R z c + T z c) = primitive S R + primitive S T := rfl

theorem primitive_neg {Z : AddSubgroup C} (S : Splitting Z) (R : Z → C → P) :
    primitive S (fun z c => -R z c) = -primitive S R := rfl

/-- Taking finite differences always gives a normalized translation cocycle. -/
theorem difference_isCocycle (Z : AddSubgroup C) (f : C → P) :
    IsCocycle (fun (z : Z) (c : C) => f (c + z) - f c) := by
  constructor
  · intro c
    simp
  · intro z w c
    simp only [AddSubgroup.coe_add]
    rw [← add_assoc]
    abel

end OpenDisk.ConePhase
