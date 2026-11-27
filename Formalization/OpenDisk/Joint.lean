import Formalization.OpenDisk.Matching

/-!
# Joint data and the two literal forgetful maps

Marked-local tables are supplied as additive subgroups, so that this file is
independent of how the finite simplicial coordinate system is presented.
Matching and descent are proved, not stipulated as properties of a purported
excitation map.  The kernel description is exact at the table level.
-/

noncomputable section

namespace OpenDisk

variable {C A P E : Type*} [AddCommGroup C] [AddCommGroup A] [AddCommGroup P]

/-- The actual subgroup of phase and hopping tables satisfying matching. -/
def jointPhases (d : C →+ A) (step : E → C) (Marked : E → AddSubgroup (C → P)) :
    AddSubgroup ((C → P) × (E → C → P)) where
  carrier := {x | (∀ e, x.2 e ∈ Marked e) ∧ ∀ e, Matching d x.1 (x.2 e) (step e)}
  zero_mem' := by
    constructor
    · intro e; exact (Marked e).zero_mem
    · intro e z v; simp [difference]
  add_mem' := by
    intro x y hx hy
    constructor
    · intro e; exact (Marked e).add_mem (hx.1 e) (hy.1 e)
    · intro e z v
      change difference (x.2 e + y.2 e) z v =
        difference (difference (x.1 + y.1) z) (step e) v
      rw [difference_add]
      have hh : difference (x.1 + y.1) z = difference x.1 z + difference y.1 z :=
        funext (difference_add x.1 y.1 z)
      rw [hh, difference_add, hx.2 e z v, hy.2 e z v]
  neg_mem' := by
    intro x hx
    constructor
    · intro e; exact (Marked e).neg_mem (hx.1 e)
    · intro e z v
      have h := hx.2 e z v
      change -x.2 e (v + z) - -x.2 e v =
        (-x.1 (v + step e + z) - -x.1 (v + step e)) -
          (-x.1 (v + z) - -x.1 v)
      simp only [difference] at h
      have hh := congrArg (fun a : P => -a) h
      calc
        _ = -(x.2 e (v + z) - x.2 e v) := by abel
        _ = -((x.1 (v + step e + z) - x.1 (v + step e)) -
          (x.1 (v + z) - x.1 v)) := hh
        _ = _ := by abel

abbrev JointPhase (d : C →+ A) (step : E → C) (Marked : E → AddSubgroup (C → P)) :=
  jointPhases d step Marked

variable (d : C →+ A) (step : E → C) (Marked : E → AddSubgroup (C → P))

/-- First forgetful map, with full global phase retained in its domain. -/
def forgetSymmetry : JointPhase d step Marked →+ SymmetryPhase d P where
  toFun x := phaseDerivative d x.1.1
  map_zero' := map_zero _
  map_add' x y := map_add _ x.1.1 y.1.1

variable (rep : A → C) (hrep : ∀ a, d (rep a) = a)

/-- Second forgetful map. It is evaluated on fixed representatives; the next
theorem proves independence of them on every actual cochain. -/
def forgetExcitation : JointPhase d step Marked →+ (E → A → P) where
  toFun x e a := x.1.2 e (rep a) - difference x.1.1 (step e) (rep a)
  map_zero' := by funext e a; simp [difference]
  map_add' x y := by
    funext e a
    change (x.1.2 e (rep a) + y.1.2 e (rep a)) -
      difference (x.1.1 + y.1.1) (step e) (rep a) =
      (x.1.2 e (rep a) - difference x.1.1 (step e) (rep a)) +
        (y.1.2 e (rep a) - difference y.1.1 (step e) (rep a))
    rw [difference_add]
    abel

include hrep in
/-- The literal representative formula in (5.4), valid on every fiber point. -/
theorem forgetExcitation_evaluate (x : JointPhase d step Marked) (e : E) (v : C) :
    forgetExcitation d step Marked rep x e (d v) =
      x.1.2 e v - difference x.1.1 (step e) v := by
  have hz := (matching_iff_closed_residual d x.1.1 (x.1.2 e) (step e)).1 (x.2.2 e)
  obtain ⟨f, hf⟩ := (phaseDerivative_eq_zero_iff d rep hrep _).1 hz
  have hv := congrFun hf v
  have hr := congrFun hf (rep (d v))
  change x.1.2 e v - difference x.1.1 (step e) v = f (d v) at hv
  change x.1.2 e (rep (d v)) - difference x.1.1 (step e) (rep (d v)) =
    f (d (rep (d v))) at hr
  change x.1.2 e (rep (d v)) - difference x.1.1 (step e) (rep (d v)) = _
  rw [hr, hrep, hv]

include hrep in
theorem forgetExcitation_eq_zero_iff (x : JointPhase d step Marked) :
    forgetExcitation d step Marked rep x = 0 ↔
      ∀ e, x.1.2 e = difference x.1.1 (step e) := by
  constructor
  · intro h e
    funext v
    have hv := congrFun (congrFun h e) (d v)
    rw [forgetExcitation_evaluate d step Marked rep hrep] at hv
    exact sub_eq_zero.mp hv
  · intro h
    funext e a
    change x.1.2 e (rep a) - difference x.1.1 (step e) (rep a) = 0
    rw [h, sub_self]

include hrep in
/-- Equal complete excitation tables determine all hopping differences exactly. -/
theorem equal_excitation_tables_iff (x y : JointPhase d step Marked) :
    forgetExcitation d step Marked rep x = forgetExcitation d step Marked rep y ↔
      ∀ e, x.1.2 e - y.1.2 e = difference (x.1.1 - y.1.1) (step e) := by
  rw [← sub_eq_zero, ← map_sub, forgetExcitation_eq_zero_iff d step Marked rep hrep]
  rfl

include rep hrep in
/-- The symmetry kernel keeps all curvature-dependent basis phases. -/
theorem forgetSymmetry_eq_zero_iff (x : JointPhase d step Marked) :
    forgetSymmetry d step Marked x = 0 ↔ ∃ f : A → P, x.1.1 = f ∘ d :=
  phaseDerivative_eq_zero_iff d rep hrep x.1.1

/-- If the symmetry vanishes, every matching hopping phase is closed invariant. -/
theorem closed_hopping_of_zero_symmetry (x : JointPhase d step Marked)
    (hx : forgetSymmetry d step Marked x = 0) (e : E) :
    phaseDerivative d (x.1.2 e) = 0 := by
  ext z v
  have hzero : difference x.1.1 z = 0 := by
    funext w
    exact congrArg (fun F : SymmetryPhase d P => F z w) hx
  change difference (x.1.2 e) z v = 0
  rw [x.2.2 e z v, hzero]
  simp [difference]

section Topology
variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_forgetSymmetry :
    Continuous (forgetSymmetry d step Marked : JointPhase d step Marked → _) :=
  (continuous_phaseDerivative d).comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_forgetExcitation :
    Continuous (forgetExcitation d step Marked rep : JointPhase d step Marked → _) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro a
  have hc : Continuous (fun x : JointPhase d step Marked => x.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hl : Continuous (fun x : JointPhase d step Marked => x.1.2 e) :=
    (continuous_apply e).comp (continuous_snd.comp continuous_subtype_val)
  exact ((continuous_apply (rep a)).comp hl).sub
    (((continuous_apply (rep a + step e)).comp hc).sub ((continuous_apply (rep a)).comp hc))

end Topology

end OpenDisk
