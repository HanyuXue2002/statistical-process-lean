import Formalization.OpenDisk.Joint
import Formalization.OpenDisk.NormalForm

/-!
# The excitation kernel is precisely the local phase graph

This file specializes the matching construction to literal elementary cochain
increments and anchored marked locality.  It proves equation (5.6), including
constant phases, from the elementary-gradient locality theorem.
-/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P]

theorem anchoredCoordinate_add (f g : Configuration ι G → P) :
    anchoredCoordinate (f + g) = anchoredCoordinate f + anchoredCoordinate g := by
  have hh : phasePairing (f + g) = phasePairing f + phasePairing g := by
    ext c
    simp
  funext c
  exact congrArg (fun T => T (cubeDistribution c)) hh

theorem anchoredCoordinate_neg (f : Configuration ι G → P) :
    anchoredCoordinate (-f) = -anchoredCoordinate f := by
  have hh : phasePairing (-f) = -phasePairing f := by
    ext c
    simp
  funext c
  exact congrArg (fun T => T (cubeDistribution c)) hh

/-- Local phases as their actual additive subgroup of the full phase table space. -/
def localFunctionSubgroup (facets : Facet → Set ι) (P : Type*) [AddCommGroup P] :
    AddSubgroup (Configuration ι G → P) where
  carrier := {f | AnchoredLocal facets f}
  zero_mem' := by intro c hc; simp [anchoredCoordinate, phasePairing]
  add_mem' := by
    intro f g hf hg c hc
    rw [anchoredCoordinate_add]
    change anchoredCoordinate f c + anchoredCoordinate g c = 0
    rw [hf c hc, hg c hc, zero_add]
  neg_mem' := by
    intro f hf c hc
    rw [anchoredCoordinate_neg]
    change -anchoredCoordinate f c = 0
    rw [hf c hc, neg_zero]

/-- The literal nonzero elementary increment labels; no fusion relations imposed. -/
def ElementaryLabel (ι G : Type*) [Zero G] := {p : ι × G // p.2 ≠ 0}

def elementaryStep (e : ElementaryLabel ι G) : Configuration ι G :=
  Finsupp.single e.1.1 e.1.2

def markedFunctionSubgroup (facets : Facet → Set ι) (e : ElementaryLabel ι G) :
    AddSubgroup (Configuration ι G → P) :=
  localFunctionSubgroup (markedFacets facets {e.1.1}) P

abbrev LocalJointPhase (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (P : Type*) [AddCommGroup P] :=
  JointPhase d elementaryStep (markedFunctionSubgroup (P := P) facets)

variable [Nonempty Facet] (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)

include hrep in
/-- Equation (5.6), as an exact membership theorem for the literal joint subgroup. -/
theorem local_excitation_kernel (x : LocalJointPhase facets d P) :
    forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x = 0 ↔
      DifferenceLocal facets x.1.1 ∧
        ∀ e, x.1.2 e = difference x.1.1 (elementaryStep e) := by
  rw [forgetExcitation_eq_zero_iff d elementaryStep (markedFunctionSubgroup facets) rep hrep]
  constructor
  · intro hx
    refine ⟨?_, hx⟩
    apply differenceLocal_of_marked_gradients
    intro i g hg
    let e : ElementaryLabel ι G := ⟨(i, g), hg⟩
    have he := x.2.1 e
    rw [hx e] at he
    exact he
  · exact And.right

/-- The full graph of a local phase is legal joint data with zero excitation table. -/
def localPhaseGraph : localFunctionSubgroup (G := G) facets P →+
    LocalJointPhase facets d P where
  toFun γ := ⟨(γ.1, fun e => difference γ.1 (elementaryStep e)), by
    constructor
    · intro e
      exact ((differenceLocal_iff_anchoredLocal facets γ.1).2 γ.2).marked_difference
        e.1.1 e.1.2 e.2
    · intro e z v
      exact difference_comm γ.1 (elementaryStep e) z v⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext e v; simp [difference]
  map_add' γ η := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext e v; exact difference_add γ.1 η.1 (elementaryStep e) v

theorem localPhaseGraph_excitation_zero (γ : localFunctionSubgroup (G := G) facets P) :
    forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep
      (localPhaseGraph facets d γ) = 0 := by
  funext e a
  change difference γ.1 (elementaryStep e) (rep a) -
    difference γ.1 (elementaryStep e) (rep a) = 0
  exact sub_self _

/-- The actual additive equivalence from local phases to the excitation kernel. -/
def localPhaseExcitationKernelEquiv : localFunctionSubgroup (G := G) facets P ≃+
    (forgetExcitation d elementaryStep (markedFunctionSubgroup (P := P) facets) rep).ker where
  toFun γ := ⟨localPhaseGraph facets d γ, localPhaseGraph_excitation_zero facets d rep γ⟩
  invFun x := ⟨x.1.1.1,
    (differenceLocal_iff_anchoredLocal facets _).1
      ((local_excitation_kernel facets d rep hrep x.1).1 x.2).1⟩
  left_inv γ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext e
      exact (((local_excitation_kernel facets d rep hrep x.1).1 x.2).2 e).symm
  map_add' γ η := by
    apply Subtype.ext
    exact map_add (localPhaseGraph facets d) γ η

end OpenDisk
