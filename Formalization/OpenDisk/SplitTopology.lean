import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.PathConnected
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

/-!
# Split continuous additive maps and their actual path components

A continuous additive section gives a global product decomposition. With a
path-connected kernel this identifies path components, including their
quotient topology. These are general tools; concrete sections are proved in
the excitation and completion modules.
-/

noncomputable section

namespace OpenDisk

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [TopologicalSpace X] [IsTopologicalAddGroup X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y]

def splitAddEquiv (f : X →+ Y) (s : Y →+ X) (hs : ∀ y, f (s y) = y) :
    X ≃+ Y × f.ker := by
  refine { toFun := fun x => (f x, ⟨x - s (f x), ?_⟩)
           invFun := fun y => s y.1 + y.2.val
           left_inv := ?_, right_inv := ?_, map_add' := ?_ }
  · change f (x - s (f x)) = 0
    rw [map_sub, hs, sub_self]
  · intro x; dsimp; abel
  · intro y
    apply Prod.ext
    · change f (s y.1 + y.2.val) = y.1
      rw [map_add, hs, show f y.2.val = 0 from y.2.property, add_zero]
    · apply Subtype.ext
      change (s y.1 + y.2.val) - s (f (s y.1 + y.2.val)) = y.2.val
      rw [map_add, hs, show f y.2.val = 0 from y.2.property, add_zero]
      abel
  · intro x y
    apply Prod.ext
    · exact map_add f x y
    · apply Subtype.ext
      change x + y - s (f (x + y)) = (x - s (f x)) + (y - s (f y))
      rw [map_add, map_add]
      abel

def splitContinuousAddEquiv (f : X →+ Y) (s : Y →+ X)
    (hs : ∀ y, f (s y) = y) (hf : Continuous f) (hc : Continuous s) :
    X ≃ₜ+ Y × f.ker where
  toAddEquiv := splitAddEquiv f s hs
  continuous_toFun := hf.prodMk ((continuous_id.sub (hc.comp hf)).subtype_mk _)
  continuous_invFun := (hc.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)

/-- A genuine quotient homeomorphism; continuity of the inverse follows from the section. -/
def splitQuotientHomeomorph (f : X →+ Y) (s : Y →+ X)
    (hs : ∀ y, f (s y) = y) (hf : Continuous f) (hc : Continuous s) :
    (X ⧸ f.ker) ≃ₜ Y where
  toEquiv := (QuotientAddGroup.quotientKerEquivOfRightInverse f s hs).toEquiv
  continuous_toFun := by
    apply continuous_quot_lift
    exact hf
  continuous_invFun := continuous_quot_mk.comp hc

/-- A split map with connected kernel detects the literal path relation. -/
theorem split_joined_iff (f : X →+ Y) (s : Y →+ X)
    (hs : ∀ y, f (s y) = y) (hf : Continuous f) (hc : Continuous s)
    [PathConnectedSpace f.ker] (x x' : X) :
    Joined x x' ↔ Joined (f x) (f x') := by
  constructor
  · exact fun h => h.map hf
  · intro h
    let E := splitContinuousAddEquiv f s hs hf hc
    have hh : Joined (E x) (E x') :=
      h.prod (PathConnectedSpace.joined (E x).2 (E x').2)
    have hh' := hh.map E.symm.continuous
    change Joined (E.symm (E x)) (E.symm (E x')) at hh'
    simpa only [E.symm_apply_apply] using hh'

/-- The induced bijection of actual path components. -/
def splitComponentEquiv (f : X →+ Y) (s : Y →+ X)
    (hs : ∀ y, f (s y) = y) (hf : Continuous f) (hc : Continuous s)
    [PathConnectedSpace f.ker] : ZerothHomotopy X ≃ ZerothHomotopy Y where
  toFun := ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun {_ _} p => ZerothHomotopy.sound (p.map hf))
  invFun := ZerothHomotopy.lift (fun y => ZerothHomotopy.mk (s y))
    (fun {_ _} p => ZerothHomotopy.sound (p.map hc))
  left_inv q := by
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective q
    apply Quotient.sound
    apply (split_joined_iff f s hs hf hc (s (f x)) x).2
    simpa only [hs] using Joined.refl (f x)
  right_inv q := by
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective q
    change ZerothHomotopy.mk (f (s y)) = ZerothHomotopy.mk y
    rw [hs]

def splitComponentHomeomorph (f : X →+ Y) (s : Y →+ X)
    (hs : ∀ y, f (s y) = y) (hf : Continuous f) (hc : Continuous s)
    [PathConnectedSpace f.ker] : ZerothHomotopy X ≃ₜ ZerothHomotopy Y where
  toEquiv := splitComponentEquiv f s hs hf hc
  continuous_toFun := by
    apply continuous_quot_lift
    exact ZerothHomotopy.isQuotientMap_mk.continuous.comp hf
  continuous_invFun := by
    apply continuous_quot_lift
    exact ZerothHomotopy.isQuotientMap_mk.continuous.comp hc

/-- The topological group's zero path component is pulled back exactly. -/
theorem split_pathComponentZero_comap (f : X →+ Y) (s : Y →+ X)
    (hs : ∀ y, f (s y) = y) (hf : Continuous f) (hc : Continuous s)
    [PathConnectedSpace f.ker] :
    (AddSubgroup.pathComponentZero Y).comap f = AddSubgroup.pathComponentZero X := by
  ext x
  change Joined (0 : Y) (f x) ↔ Joined (0 : X) x
  simpa only [map_zero] using (split_joined_iff f s hs hf hc 0 x).symm

end OpenDisk
