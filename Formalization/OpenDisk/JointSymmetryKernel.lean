import Formalization.OpenDisk.Joint

/-!
# The symmetry kernel with all configuration-basis phases

This is the exact algebraic kernel before identifying a marked closed phase
with a closed SPT phase on its geometric star.  The latter identification
requires the surjectivity of restriction of closed cochains to that star.
-/

noncomputable section

namespace OpenDisk

variable {C A P E : Type*} [AddCommGroup C] [AddCommGroup A] [AddCommGroup P]

def closedMarkedHoppings (d : C →+ A) (Marked : E → AddSubgroup (C → P)) :
    AddSubgroup (E → C → P) where
  carrier := {L | (∀ e, L e ∈ Marked e) ∧ ∀ e, phaseDerivative d (L e) = 0}
  zero_mem' := ⟨fun e => (Marked e).zero_mem, fun e => map_zero _⟩
  add_mem' := by
    intro L K hL hK
    exact ⟨fun e => (Marked e).add_mem (hL.1 e) (hK.1 e),
      fun e => by change phaseDerivative d (L e + K e) = 0; rw [map_add, hL.2, hK.2, add_zero]⟩
  neg_mem' := by
    intro L hL
    exact ⟨fun e => (Marked e).neg_mem (hL.1 e),
      fun e => by change phaseDerivative d (-L e) = 0; rw [map_neg, hL.2, neg_zero]⟩

variable (d : C →+ A) (step : E → C) (Marked : E → AddSubgroup (C → P))

/-- Build every symmetry-kernel point from a fiber phase and closed marked hoppings. -/
def symmetryKernelDatum (f : A → P) (L : closedMarkedHoppings d Marked) :
    JointPhase d step Marked :=
  ⟨(f ∘ d, L.val), L.property.1, by
    intro e z v
    have hL := congrArg (fun F : SymmetryPhase d P => F z v) (L.property.2 e)
    change difference (L.val e) z v = 0 at hL
    have hβ : difference (f ∘ d) z = 0 := by
      funext w
      have hz : d z = 0 := z.property
      simp [difference, hz]
    rw [hβ]
    simpa [difference] using hL⟩

theorem symmetryKernelDatum_mem (f : A → P) (L : closedMarkedHoppings d Marked) :
    forgetSymmetry d step Marked (symmetryKernelDatum d step Marked f L) = 0 := by
  ext z v
  have hz : d z = 0 := z.property
  change f (d (v + z)) - f (d v) = 0
  simp [hz]

variable (rep : A → C) (hrep : ∀ a, d (rep a) = a)

/-- Formula (5.5) prior to the geometric star restriction isomorphism. -/
def symmetryKernelEquiv : (forgetSymmetry d step Marked).ker ≃+
    (A → P) × closedMarkedHoppings d Marked where
  toFun x := (fun a => x.val.val.1 (rep a),
    ⟨x.val.val.2, x.val.property.1, fun e => closed_hopping_of_zero_symmetry d step Marked
      x.val x.property e⟩)
  invFun y := ⟨symmetryKernelDatum d step Marked y.1 y.2,
    symmetryKernelDatum_mem d step Marked y.1 y.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · obtain ⟨f, hf⟩ := (forgetSymmetry_eq_zero_iff d step Marked rep hrep x.val).1 x.property
      change (fun a => x.val.val.1 (rep a)) ∘ d = x.val.val.1
      rw [hf]
      funext v
      simp [Function.comp_def, hrep]
    · rfl
  right_inv y := by
    apply Prod.ext
    · funext a
      change y.1 (d (rep a)) = y.1 a
      rw [hrep]
    · rfl
  map_add' x y := rfl

section Topology
variable [TopologicalSpace P] [IsTopologicalAddGroup P]

def symmetryKernelHomeomorph : (forgetSymmetry d step Marked).ker ≃ₜ
    (A → P) × closedMarkedHoppings d Marked where
  toEquiv := (symmetryKernelEquiv d step Marked rep hrep).toEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro a
      exact (continuous_apply (rep a)).comp
        ((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val)
    · exact ((continuous_snd.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_pi fun v => (continuous_apply (d v)).comp continuous_fst
    · exact continuous_subtype_val.comp continuous_snd

end Topology

end OpenDisk
