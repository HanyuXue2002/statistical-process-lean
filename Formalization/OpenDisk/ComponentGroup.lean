import Formalization.OpenDisk.SplitTopology

/-! # Path components as an actual quotient abelian group -/

noncomputable section

namespace OpenDisk

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

abbrev ComponentGroup (X : Type*) [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] := X ⧸ AddSubgroup.pathComponentZero X

theorem joined_iff_difference_mem (x y : X) :
    Joined x y ↔ x - y ∈ AddSubgroup.pathComponentZero X := by
  change Joined x y ↔ Joined (0 : X) (x - y)
  constructor
  · intro h
    have hh := h.symm.map (f := fun a : X => a - y) (continuous_id.sub continuous_const)
    simpa only [id_eq, sub_self] using hh
  · intro h
    have hh := h.map (continuous_id.add_const y)
    have hh' : Joined y x := by simpa only [id_eq, zero_add, sub_add_cancel] using hh
    exact hh'.symm

def componentGroupEquiv : ComponentGroup X ≃ ZerothHomotopy X where
  toFun := Quotient.lift (fun x => ZerothHomotopy.mk x) (by
    intro x y h
    have heq : (QuotientAddGroup.mk' (AddSubgroup.pathComponentZero X)) x =
        (QuotientAddGroup.mk' (AddSubgroup.pathComponentZero X)) y := Quotient.sound h
    exact Quotient.sound ((joined_iff_difference_mem x y).2
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)))
  invFun := ZerothHomotopy.lift (QuotientAddGroup.mk' (AddSubgroup.pathComponentZero X))
    (fun {_ _} p => QuotientAddGroup.eq_iff_sub_mem.mpr
      ((joined_iff_difference_mem _ _).1 ⟨p⟩))
  left_inv q := Quotient.inductionOn q (fun _ => rfl)
  right_inv q := ZerothHomotopy.rec (fun _ => rfl) q

def componentGroupHomeomorph : ComponentGroup X ≃ₜ ZerothHomotopy X where
  toEquiv := componentGroupEquiv
  continuous_toFun := by
    apply continuous_quot_lift
    exact ZerothHomotopy.isQuotientMap_mk.continuous
  continuous_invFun := by
    apply continuous_quot_lift
    exact continuous_quot_mk

theorem finite_componentGroup [Finite (ZerothHomotopy X)] : Finite (ComponentGroup X) :=
  Finite.of_equiv _ (componentGroupEquiv (X := X)).symm

/-- A continuous additive map induces an additive map on the actual path components. -/
def componentMap (f : X →+ Y) (hf : Continuous f) : ComponentGroup X →+ ComponentGroup Y :=
  QuotientAddGroup.lift (AddSubgroup.pathComponentZero X)
    ((QuotientAddGroup.mk' (AddSubgroup.pathComponentZero Y)).comp f) (by
      intro x hx
      apply (QuotientAddGroup.eq_zero_iff (f x)).mpr
      change Joined (0 : Y) (f x)
      have hh := hx.map hf
      simpa only [map_zero] using hh)

/-- The component identification preserves its abelian group law. -/
def splitComponentGroupEquiv (f : X →+ Y) (s : Y →+ X)
    (hs : ∀ y, f (s y) = y) (hf : Continuous f) (hc : Continuous s)
    [PathConnectedSpace f.ker] : ComponentGroup X ≃+ ComponentGroup Y where
  toFun := componentMap f hf
  invFun := componentMap s hc
  left_inv q := by
    refine Quotient.inductionOn q fun x => ?_
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply (joined_iff_difference_mem _ _).1
    apply (split_joined_iff f s hs hf hc _ _).2
    rw [hs]
  right_inv q := by
    refine Quotient.inductionOn q fun y => ?_
    change (QuotientAddGroup.mk' (AddSubgroup.pathComponentZero Y)) (f (s y)) = _
    rw [hs]
    rfl
  map_add' := map_add (componentMap f hf)

end OpenDisk
