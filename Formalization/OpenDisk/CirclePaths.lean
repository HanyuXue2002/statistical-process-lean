import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Algebra.Rat

/-!
# Paths in circle-valued integer equation spaces

The component argument in the report need not assume a Lie-group theorem.
A path starting at zero in an intersection of kernels of continuous additive
equations has an n-th root path in the same intersection. This follows from
unique path lifting for the genuine circle covering map.
-/

noncomputable section

namespace OpenDisk.CirclePaths

open scoped unitInterval

abbrev Phase := AddCircle (1 : ℝ)

/-- A continuous path in the n-torsion of the circle is constant. -/
theorem eq_zero_of_nsmul_eq_zero (n : ℕ) [NeZero n]
    (f : C(unitInterval, Phase)) (hzero : f 0 = 0)
    (hn : ∀ t, n • f t = 0) : ∀ t, f t = 0 := by
  have cov := (AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) n).isCoveringMap
  have heq : (fun t => n • f t) = fun _ : unitInterval => n • (0 : Phase) := by
    funext t
    simp [hn t]
  have hh := cov.eq_of_comp_eq f.continuous continuous_const heq 0 hzero
  exact fun t => congrFun hh t

variable {ι J : Type*}

/-- An arbitrary family of literal additive equations on the phase entries. -/
def equationSubgroup (R : J → ((ι → Phase) →+ Phase)) : AddSubgroup (ι → Phase) :=
  ⨅ j, (R j).ker

theorem mem_equationSubgroup (R : J → ((ι → Phase) →+ Phase)) (x : ι → Phase) :
    x ∈ equationSubgroup R ↔ ∀ j, R j x = 0 := by
  simp [equationSubgroup]

/-- A based path in an integer-equation space has a based n-th root path.
No division operation on circle-valued phase tables is chosen globally. -/
theorem root_path (R : J → ((ι → Phase) →+ Phase))
    (hR : ∀ j, Continuous (R j)) (n : ℕ) [NeZero n]
    (x : equationSubgroup R) (p : Path (0 : equationSubgroup R) x) :
    ∃ (y : equationSubgroup R), Nonempty (Path (0 : equationSubgroup R) y) ∧ n • y = x := by
  let cov := (AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) n).isCoveringMap
  let α (i : ι) : C(unitInterval, Phase) :=
    ⟨fun t => (p t).val i, (continuous_apply i).comp (continuous_subtype_val.comp p.continuous)⟩
  have hα : ∀ i, α i 0 = n • (0 : Phase) := by
    intro i
    change (p 0).val i = _
    rw [p.source]
    simp
  let Γ (i : ι) : C(unitInterval, Phase) := cov.liftPath (α i) 0 (hα i)
  have hΓ0 : ∀ i, Γ i 0 = 0 := fun i => cov.liftPath_zero (α i) 0 (hα i)
  have hΓn : ∀ i t, n • Γ i t = (p t).val i := by
    intro i t
    exact congrFun (cov.liftPath_lifts (α i) 0 (hα i)) t
  let g (t : unitInterval) : ι → Phase := fun i => Γ i t
  have hg : Continuous g := continuous_pi fun i => (Γ i).continuous
  have hg0 : g 0 = 0 := funext hΓ0
  have hgn (t : unitInterval) : n • g t = (p t).val := funext fun i => hΓn i t
  have hmem (t : unitInterval) : g t ∈ equationSubgroup R := by
    rw [mem_equationSubgroup]
    intro j
    let f : C(unitInterval, Phase) := ⟨fun s => R j (g s), (hR j).comp hg⟩
    apply eq_zero_of_nsmul_eq_zero n f
    · change R j (g 0) = 0
      rw [hg0, map_zero]
    · intro s
      change n • R j (g s) = 0
      rw [← map_nsmul, hgn]
      exact (mem_equationSubgroup R _).1 (p s).property j
  let q : Path (0 : equationSubgroup R) ⟨g 1, hmem 1⟩ :=
    { toFun := fun t => ⟨g t, hmem t⟩
      continuous_toFun := hg.subtype_mk _
      source' := Subtype.ext hg0
      target' := rfl }
  refine ⟨⟨g 1, hmem 1⟩, ⟨q⟩, ?_⟩
  apply Subtype.ext
  change n • g 1 = x.val
  rw [hgn, p.target]

end OpenDisk.CirclePaths
