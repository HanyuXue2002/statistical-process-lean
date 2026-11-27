import Formalization.OpenDisk.BulkPhaseLocalGluing
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! The unique local actual/cap split is a continuous additive equivalence
of full phase-table spaces, with their pointwise topologies. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace OpenDisk.BulkPhaseLocalGluing

open GeneralSphereT.PathAlgebra

variable {ι G P A C : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup P]
  [Fintype A] [Fintype C]
variable (actual : A → Set ι) (cap : C → Set ι) (S : Set ι)

def normalizedLocalPairs : AddSubgroup ((Configuration ι G → P) × (Configuration ι G → P)) where
  carrier := {x | AnchoredLocal actual x.1 ∧ AnchoredLocal cap x.2 ∧ ∀ c, x.2 (project S c) = 0}
  zero_mem' := ⟨(localFunctionSubgroup actual P).zero_mem,
    (localFunctionSubgroup cap P).zero_mem, fun _ => rfl⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨(localFunctionSubgroup actual P).add_mem hx.1 hy.1,
      (localFunctionSubgroup cap P).add_mem hx.2.1 hy.2.1,
      fun c => by change x.2 (project S c) + y.2 (project S c) = 0; rw [hx.2.2, hy.2.2, add_zero]⟩
  neg_mem' := by
    intro x hx
    exact ⟨(localFunctionSubgroup actual P).neg_mem hx.1,
      (localFunctionSubgroup cap P).neg_mem hx.2.1,
      fun c => by change -x.2 (project S c) = 0; rw [hx.2.2, neg_zero]⟩

variable (hactual : ∀ ρ, actual ρ ⊆ S)
  (hboundary : ∀ ρ, ∃ σ, cap ρ ∩ S ⊆ actual σ)

def localGluingAddEquiv :
    localFunctionSubgroup (G := G) (Sum.elim actual cap) P ≃+
      normalizedLocalPairs (G := G) (P := P) actual cap S where
  toFun f := ⟨(actualSlice S f.val, capSlice S f.val),
    (normalized_slices_local actual cap S hactual hboundary f.property).1,
    (normalized_slices_local actual cap S hactual hboundary f.property).2,
    capSlice_zero_slice S f.val⟩
  invFun x := ⟨x.val.1 + x.val.2,
    (local_union_iff actual cap _).2 ⟨x.val.1, x.val.2, x.property.1, x.property.2.1, rfl⟩⟩
  left_inv f := Subtype.ext (normalized_split S f.val).symm
  right_inv x := by
    apply Subtype.ext
    obtain ⟨ha, hc⟩ := normalized_split_unique actual S hactual (x.val.1 + x.val.2)
      x.val.1 x.val.2 x.property.1 x.property.2.2 rfl
    exact Prod.ext ha.symm hc.symm
  map_add' f g := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext c
      change (f.val c + g.val c) - (f.val (project S c) + g.val (project S c)) =
        (f.val c - f.val (project S c)) + (g.val c - g.val (project S c))
      abel

variable [TopologicalSpace P] [IsTopologicalAddGroup P]

def localGluingContinuousAddEquiv :
    localFunctionSubgroup (G := G) (Sum.elim actual cap) P ≃ₜ+
      normalizedLocalPairs (G := G) (P := P) actual cap S where
  toAddEquiv := localGluingAddEquiv actual cap S hactual hboundary
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_pi fun c => (continuous_apply (project S c)).comp continuous_subtype_val
    · exact continuous_pi fun c =>
        ((continuous_apply c).comp continuous_subtype_val).sub
          ((continuous_apply (project S c)).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).add
      (continuous_snd.comp continuous_subtype_val)

end OpenDisk.BulkPhaseLocalGluing
