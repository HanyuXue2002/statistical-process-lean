import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# Strict symmetry phase tables

This file proves the phase-table content of Proposition 3.1 of
`open_disk_final_report.pdf`.  The coboundary is any additive map `d`; its
codomain consists of actual configurations and is assumed to be its image.
No normalization of constant phases is imposed.
-/

noncomputable section

namespace OpenDisk

variable {C A P : Type*} [AddCommGroup C] [AddCommGroup A] [AddCommGroup P]

/-- The literal finite difference of a phase table. -/
def difference (f : C → P) (s v : C) : P := f (v + s) - f v

@[simp] theorem difference_zero (f : C → P) (v : C) : difference f 0 v = 0 := by
  simp [difference]

theorem difference_comm (f : C → P) (s t v : C) :
    difference (difference f s) t v = difference (difference f t) s v := by
  simp only [difference]
  have h : v + t + s = v + s + t := by abel
  rw [h]
  abel

theorem difference_add (f g : C → P) (s v : C) :
    difference (f + g) s v = difference f s v + difference g s v := by
  simp only [difference, Pi.add_apply]
  abel

theorem difference_sub (f g : C → P) (s v : C) :
    difference (f - g) s v = difference f s v - difference g s v := by
  simp only [difference, Pi.sub_apply]
  abel

/-- Closed-shift tables satisfying the strict group law, including its unit. -/
def cocycles (d : C →+ A) (P : Type*) [AddCommGroup P] :
    AddSubgroup (d.ker → C → P) where
  carrier := {F | (∀ v, F 0 v = 0) ∧
    ∀ z w v, F (z + w) v = F z v + F w (v + z)}
  zero_mem' := by simp
  add_mem' := by
    intro F H hF hH
    constructor
    · intro v; simp [hF.1, hH.1]
    · intro z w v
      simp only [Pi.add_apply, hF.2, hH.2]
      abel
  neg_mem' := by
    intro F hF
    constructor
    · intro v; simp [hF.1]
    · intro z w v
      simp only [Pi.neg_apply, hF.2]
      abel

abbrev SymmetryPhase (d : C →+ A) (P : Type*) [AddCommGroup P] := cocycles d P

instance (d : C →+ A) : CoeFun (SymmetryPhase d P) (fun _ => d.ker → C → P) :=
  ⟨Subtype.val⟩

/-- `D_X` in (3.4), with values in strict cocycles. -/
def phaseDerivative (d : C →+ A) : (C → P) →+ SymmetryPhase d P where
  toFun f := ⟨fun z v => difference f z v, by
    constructor
    · intro v; simp
    · intro z w v
      simp only [difference, AddSubgroup.coe_add]
      have h : v + (↑z + ↑w) = v + ↑z + ↑w := by abel
      rw [h]
      abel⟩
  map_zero' := by ext z v; simp [difference]
  map_add' f g := by ext z v; exact difference_add f g z v

@[simp] theorem phaseDerivative_apply (d : C →+ A) (f : C → P) (z : d.ker) (v : C) :
    phaseDerivative d f z v = f (v + z) - f v := rfl

variable (d : C →+ A) (rep : A → C) (hrep : ∀ a, d (rep a) = a)

/-- The closed displacement from a chosen representative of a curvature fiber. -/
def fiberDisplacement (v : C) : d.ker :=
  ⟨v - rep (d v), by simp [AddMonoidHom.mem_ker, hrep]⟩

@[simp] theorem fiberDisplacement_add (v : C) (z : d.ker) :
    fiberDisplacement d rep hrep (v + z) = fiberDisplacement d rep hrep v + z := by
  apply Subtype.ext
  have hz : d z = 0 := z.property
  simp only [fiberDisplacement, map_add, hz, add_zero, AddSubgroup.coe_add]
  abel

/-- Formula (3.5). The representative is fixed before the phase table varies. -/
def phaseSection : SymmetryPhase d P →+ (C → P) where
  toFun F v := F (fiberDisplacement d rep hrep v) (rep (d v))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem phaseDerivative_phaseSection (F : SymmetryPhase d P) :
    phaseDerivative d (phaseSection d rep hrep F) = F := by
  ext z v
  change F (fiberDisplacement d rep hrep (v + z)) (rep (d (v + z))) -
    F (fiberDisplacement d rep hrep v) (rep (d v)) = F z v
  have hz : d z = 0 := z.property
  rw [fiberDisplacement_add, map_add, hz, add_zero, F.property.2]
  have hv : rep (d v) + ↑(fiberDisplacement d rep hrep v) = v := by
    change rep (d v) + (v - rep (d v)) = v
    abel
  rw [hv]
  abel

theorem phaseSection_at_rep (F : SymmetryPhase d P) (a : A) :
    phaseSection d rep hrep F (rep a) = 0 := by
  change F (fiberDisplacement d rep hrep (rep a)) (rep (d (rep a))) = 0
  have hzero : fiberDisplacement d rep hrep (rep a) = 0 := by
    apply Subtype.ext
    simp [fiberDisplacement, hrep]
  rw [hzero]
  exact F.property.1 _

theorem phaseDerivative_surjective (hd : Function.Surjective d) :
    Function.Surjective (phaseDerivative d : (C → P) →+ SymmetryPhase d P) := by
  let rep := fun a => Classical.choose (hd a)
  have hr : ∀ a, d (rep a) = a := fun a => Classical.choose_spec (hd a)
  intro F
  exact ⟨phaseSection d rep hr F, phaseDerivative_phaseSection d rep hr F⟩

include rep hrep in
/-- Zero derivative means precisely an arbitrary function of curvature.
This includes the constant functions, hence retains global phase. -/
theorem phaseDerivative_eq_zero_iff (f : C → P) :
    phaseDerivative d f = 0 ↔ ∃ g : A → P, f = g ∘ d := by
  constructor
  · intro hf
    refine ⟨fun a => f (rep a), ?_⟩
    funext v
    have h := congrArg (fun F : SymmetryPhase d P => F
      (fiberDisplacement d rep hrep v) (rep (d v))) hf
    change f (rep (d v) + (v - rep (d v))) - f (rep (d v)) = 0 at h
    have hv : rep (d v) + (v - rep (d v)) = v := by abel
    rw [hv, sub_eq_zero] at h
    exact h
  · rintro ⟨g, rfl⟩
    ext z v
    have hz : d z = 0 := z.property
    simp [Function.comp_def, hz]

include rep hrep in
/-- All primitives of the same symmetry differ by a curvature function, (3.6). -/
theorem same_symmetry_iff (f g : C → P) :
    phaseDerivative d f = phaseDerivative d g ↔
      ∃ h : A → P, f = g + h ∘ d := by
  rw [← sub_eq_zero, ← map_sub, phaseDerivative_eq_zero_iff d rep hrep]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, by rw [← hh]; abel⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, by abel⟩

/-- The full phase space splits into a strict symmetry table and fiber phases. -/
def phaseSplitting : (C → P) ≃+ SymmetryPhase d P × (A → P) where
  toFun f := (phaseDerivative d f, fun a => f (rep a))
  invFun x := phaseSection d rep hrep x.1 + x.2 ∘ d
  left_inv f := by
    funext v
    change (f (rep (d v) + (v - rep (d v))) - f (rep (d v))) + f (rep (d v)) = f v
    have hv : rep (d v) + (v - rep (d v)) = v := by abel
    rw [hv]
    abel
  right_inv x := by
    apply Prod.ext
    · change phaseDerivative d (phaseSection d rep hrep x.1 + x.2 ∘ d) = x.1
      rw [map_add, phaseDerivative_phaseSection,
        (phaseDerivative_eq_zero_iff d rep hrep _).2 ⟨x.2, rfl⟩, add_zero]
    · funext a
      change phaseSection d rep hrep x.1 (rep a) + x.2 (d (rep a)) = x.2 a
      rw [phaseSection_at_rep, hrep, zero_add]
  map_add' f g := by
    apply Prod.ext
    · exact map_add (phaseDerivative d) f g
    · rfl

section Topology
variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_phaseDerivative :
    Continuous (phaseDerivative d : (C → P) → SymmetryPhase d P) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun z => continuous_pi fun v =>
    (continuous_apply (v + z)).sub (continuous_apply v)

theorem continuous_phaseSection :
    Continuous (phaseSection d rep hrep : SymmetryPhase d P → (C → P)) := by
  exact continuous_pi fun v =>
    (continuous_apply (rep (d v))).comp
      ((continuous_apply (fiberDisplacement d rep hrep v)).comp continuous_subtype_val)

end Topology

end OpenDisk
