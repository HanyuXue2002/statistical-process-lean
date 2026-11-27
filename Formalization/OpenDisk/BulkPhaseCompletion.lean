import Formalization.OpenDisk.BulkPhase
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.FunProp

/-!
# Canonical completion with an exact slice inverse

This file proves the full-table algebraic equivalence underlying Theorem 4.3.
The actual coordinates are `I × B`, cap coordinates `U × B`, and glued
coordinates `I × B × U`. The interface explicitly requires closed extension
on both sides and the verified cone splitting with its zero-slice properties.
On the glued side, `Separated` means that the phase is a sum of an actual-side
and a cap-side phase. Every simplex-local function on a glued complex has this
property; this file does not identify the geometric simplex-local subgroups.
Thus the result is an exact equivalence of separated full phase tables, not an
unqualified replacement for all of the geometric assertions in Theorem 4.3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace OpenDisk.BulkPhaseCompletion

open BulkPhase

variable {I U B P : Type*} [AddCommGroup I] [AddCommGroup U]
  [AddCommGroup B] [AddCommGroup P]

/-- The cochain extension and cone-slice data required by the completion argument. -/
structure Model (I U B : Type*) [AddCommGroup I] [AddCommGroup U] [AddCommGroup B] where
  actualClosed : AddSubgroup (I × B)
  capClosed : AddSubgroup (U × B)
  boundaryClosed : AddSubgroup B
  actual_closed : ∀ a : actualClosed, a.val.2 ∈ boundaryClosed
  cap_closed : ∀ c : capClosed, c.val.2 ∈ boundaryClosed
  actual_extension : ∀ z : boundaryClosed, ∃ a : actualClosed, a.val.2 = z.val
  cap_extension : ∀ z : boundaryClosed, ∃ c : capClosed, c.val.2 = z.val
  splitting : ConePhase.Splitting capClosed
  base_new_zero : ∀ c, (splitting.base c).1 = 0
  base_zero_slice : ∀ b, splitting.base (0, b) = (0, b)

namespace Model

variable (G : Model I U B)

def actualSystem : System (I × B) B where
  restriction := AddMonoidHom.snd I B
  bulkClosed := G.actualClosed
  boundaryClosed := G.boundaryClosed
  restriction_closed := G.actual_closed

def capSystem : System (U × B) B where
  restriction := AddMonoidHom.snd U B
  bulkClosed := G.capClosed
  boundaryClosed := G.boundaryClosed
  restriction_closed := G.cap_closed

def actualLift (z : G.boundaryClosed) : G.actualClosed := (G.actual_extension z).choose
def capLift (z : G.boundaryClosed) : G.capClosed := (G.cap_extension z).choose

@[simp] theorem actualLift_snd (z : G.boundaryClosed) : (G.actualLift z).val.2 = z.val :=
  (G.actual_extension z).choose_spec
@[simp] theorem capLift_snd (z : G.boundaryClosed) : (G.capLift z).val.2 = z.val :=
  (G.cap_extension z).choose_spec

theorem actual_restriction_surjective : Function.Surjective G.actualSystem.restriction :=
  fun b => ⟨(0, b), rfl⟩

theorem actual_closedRestriction_surjective :
    Function.Surjective G.actualSystem.closedRestriction := by
  intro z
  refine ⟨G.actualLift z, Subtype.ext ?_⟩
  exact G.actualLift_snd z

end Model

/-- Side-separation of local functions is the only locality property used here. -/
def Separated (Ψ : I → B → U → P) : Prop :=
  ∃ (φ : I × B → P) (χ : U × B → P), ∀ i b u, Ψ i b u = φ (i, b) + χ (u, b)

/-- Closed invariance on the glued cochains, with equality at the shared boundary. -/
def GluedInvariant (G : Model I U B) (Ψ : I → B → U → P) : Prop :=
  ∀ (a : G.actualClosed) (z : G.capClosed), a.val.2 = z.val.2 →
    ∀ i b u, Ψ (i + a.val.1) (b + a.val.2) (u + z.val.1) = Ψ i b u

def actualSlice (Ψ : I → B → U → P) (m : I × B) : P := Ψ m.1 m.2 0
def capSlice (Ψ : I → B → U → P) (c : U × B) : P := Ψ 0 c.2 c.1 - Ψ 0 c.2 0

@[simp] theorem capSlice_zero (Ψ : I → B → U → P) (b : B) : capSlice Ψ (0, b) = 0 := by
  simp [capSlice]

theorem normalized_split {Ψ : I → B → U → P} (hΨ : Separated Ψ) (i : I) (b : B) (u : U) :
    Ψ i b u = actualSlice Ψ (i, b) + capSlice Ψ (u, b) := by
  obtain ⟨φ, χ, h⟩ := hΨ
  simp only [actualSlice, capSlice, h]
  abel

/-- Closed invariance forces cancellation of the two actual side differences. -/
theorem split_cancellation (G : Model I U B) {Ψ : I → B → U → P}
    (hsep : Separated Ψ) (hinv : GluedInvariant G Ψ)
    (a : G.actualClosed) (z : G.capClosed) (haz : a.val.2 = z.val.2)
    (i : I) (b : B) (u : U) :
    (actualSlice Ψ ((i, b) + a) - actualSlice Ψ (i, b)) +
      (capSlice Ψ ((u, b) + z) - capSlice Ψ (u, b)) = 0 := by
  have h := hinv a z haz i b u
  rw [normalized_split hsep, normalized_split hsep] at h
  have h' : actualSlice Ψ ((i, b) + a) + capSlice Ψ ((u, b) + z) =
      actualSlice Ψ (i, b) + capSlice Ψ (u, b) := by
    change actualSlice Ψ (i + a.val.1, b + a.val.2) +
      capSlice Ψ (u + z.val.1, b + z.val.2) = _
    simpa only [haz] using h
  rw [sub_add_sub_comm, h', sub_self]

/-- The recovered response is read from a fixed closed cap extension. -/
def recoveredResponse (G : Model I U B) (Ψ : I → B → U → P)
    (z : G.boundaryClosed) (b : B) : P :=
  capSlice Ψ (((0 : U), b) + (G.capLift z : U × B)) - capSlice Ψ (0, b)

theorem recovered_hasResponse (G : Model I U B) {Ψ : I → B → U → P}
    (hsep : Separated Ψ) (hinv : GluedInvariant G Ψ) :
    HasResponse G.actualSystem (actualSlice Ψ) (recoveredResponse G Ψ) := by
  intro a m
  have h := split_cancellation G hsep hinv a
    (G.capLift (G.actualSystem.closedRestriction a))
    (G.capLift_snd (G.actualSystem.closedRestriction a)).symm m.1 m.2 0
  exact eq_neg_of_add_eq_zero_left h

theorem recovered_isCocycle (G : Model I U B) {Ψ : I → B → U → P}
    (hsep : Separated Ψ) (hinv : GluedInvariant G Ψ) :
    ConePhase.IsCocycle (recoveredResponse G Ψ) :=
  response_isCocycle G.actualSystem G.actual_restriction_surjective
    G.actual_closedRestriction_surjective (recovered_hasResponse G hsep hinv)

theorem capSlice_difference (G : Model I U B) {Ψ : I → B → U → P}
    (hsep : Separated Ψ) (hinv : GluedInvariant G Ψ) (z : G.capClosed) (c : U × B) :
    capSlice Ψ (c + z) - capSlice Ψ c =
      recoveredResponse G Ψ (G.capSystem.closedRestriction z) c.2 := by
  let a := G.actualLift (G.capSystem.closedRestriction z)
  have haz : a.val.2 = z.val.2 := G.actualLift_snd _
  have h := split_cancellation G hsep hinv a z haz 0 c.2 c.1
  have hr := recovered_hasResponse G hsep hinv a (0, c.2)
  have heq : G.actualSystem.closedRestriction a = G.capSystem.closedRestriction z :=
    Subtype.ext haz
  rw [heq] at hr
  rw [hr] at h
  exact (neg_add_eq_zero.mp h).symm

/-- Closed invariance determines the normalized cap, with no remaining global phase. -/
theorem capSlice_eq_canonical (G : Model I U B) {Ψ : I → B → U → P}
    (hsep : Separated Ψ) (hinv : GluedInvariant G Ψ) :
    capSlice Ψ = canonicalCap G.capSystem G.splitting (recoveredResponse G Ψ) := by
  apply normalized_cap_unique
  · exact capSlice_difference G hsep hinv
  · intro c
    simp [capSlice, G.base_new_zero]

/-- The additive group of bulk phase/response pairs. -/
def bulkSubgroup (G : Model I U B) (P : Type*) [AddCommGroup P] :
    AddSubgroup (((I × B) → P) × (G.boundaryClosed → B → P)) where
  carrier := {t | HasResponse G.actualSystem t.1 t.2}
  zero_mem' := by intro a c; change (0 : P) - 0 = -0; simp
  add_mem' := by
    intro t s ht hs a c
    change (t.1 (c + a) + s.1 (c + a)) - (t.1 c + s.1 c) =
      -(t.2 _ _ + s.2 _ _)
    have ht' := ht a c
    have hs' := hs a c
    rw [sub_eq_iff_eq_add] at ht' hs'
    rw [ht', hs']
    abel
  neg_mem' := by
    intro t ht a c
    change -t.1 (c + a) - -t.1 c = -(-t.2 _ _)
    have ht' := ht a c
    rw [sub_eq_iff_eq_add] at ht'
    rw [ht']
    abel

/-- A bulk phase together with its uniquely determined full response. -/
abbrev BulkDatum (G : Model I U B) (P : Type*) [AddCommGroup P] := bulkSubgroup G P

/-- The additive group of separated, closed-invariant glued phase tables. -/
def completedSubgroup (G : Model I U B) (P : Type*) [AddCommGroup P] :
    AddSubgroup (I → B → U → P) where
  carrier := {Ψ | Separated Ψ ∧ GluedInvariant G Ψ}
  zero_mem' := ⟨⟨0, 0, fun _ _ _ => (add_zero 0).symm⟩, fun _ _ _ _ _ _ => rfl⟩
  add_mem' := by
    intro Ψ Ω hΨ hΩ
    constructor
    · obtain ⟨φ, χ, h⟩ := hΨ.1
      obtain ⟨φ', χ', h'⟩ := hΩ.1
      refine ⟨φ + φ', χ + χ', fun i b u => ?_⟩
      change Ψ i b u + Ω i b u = _
      rw [h, h']
      simp only [Pi.add_apply]
      abel
    · intro a z haz i b u
      exact congrArg₂ (· + ·) (hΨ.2 a z haz i b u) (hΩ.2 a z haz i b u)
  neg_mem' := by
    intro Ψ hΨ
    constructor
    · obtain ⟨φ, χ, h⟩ := hΨ.1
      exact ⟨-φ, -χ, fun i b u => by simp [h, add_comm]⟩
    · intro a z haz i b u
      exact congrArg Neg.neg (hΨ.2 a z haz i b u)

/-- A separated, closed-invariant full phase table on the glued coordinates. -/
abbrev CompletedDatum (G : Model I U B) (P : Type*) [AddCommGroup P] := completedSubgroup G P

def completeTable (G : Model I U B) (t : BulkDatum G P) (i : I) (b : B) (u : U) : P :=
  t.val.1 (i, b) + canonicalCap G.capSystem G.splitting t.val.2 (u, b)

theorem bulkDatum_isCocycle (G : Model I U B) (t : BulkDatum G P) :
    ConePhase.IsCocycle t.val.2 :=
  response_isCocycle G.actualSystem G.actual_restriction_surjective
    G.actual_closedRestriction_surjective t.property

theorem completeTable_cap_zero (G : Model I U B) (t : BulkDatum G P) (b : B) :
    canonicalCap G.capSystem G.splitting t.val.2 (0, b) = 0 := by
  have h := canonicalCap_base G.capSystem G.splitting (bulkDatum_isCocycle G t) (0, b)
  rwa [G.base_zero_slice] at h

def complete (G : Model I U B) (t : BulkDatum G P) : CompletedDatum G P := by
  refine ⟨completeTable G t, ?_, ?_⟩
  · exact ⟨t.val.1, canonicalCap G.capSystem G.splitting t.val.2, fun _ _ _ => rfl⟩
  · intro a z haz i b u
    have ha := t.property a (i, b)
    have hz := canonicalCap_difference G.capSystem G.splitting (bulkDatum_isCocycle G t) z (u, b)
    have heq : G.actualSystem.closedRestriction a = G.capSystem.closedRestriction z :=
      Subtype.ext haz
    rw [heq] at ha
    rw [sub_eq_iff_eq_add] at ha hz
    change t.val.1 ((i, b) + a) + canonicalCap G.capSystem G.splitting t.val.2
        (u + z.val.1, b + a.val.2) = _
    rw [haz]
    change t.val.1 ((i, b) + a) + canonicalCap G.capSystem G.splitting t.val.2
        ((u, b) + z) = _
    rw [ha, hz]
    change -t.val.2 _ b + t.val.1 (i, b) +
      (t.val.2 _ b + canonicalCap G.capSystem G.splitting t.val.2 (u, b)) = _
    unfold completeTable
    abel

def recover (G : Model I U B) (Ψ : CompletedDatum G P) : BulkDatum G P :=
  ⟨(actualSlice Ψ.val, recoveredResponse G Ψ.val), recovered_hasResponse G Ψ.property.1 Ψ.property.2⟩

theorem recover_complete_phase (G : Model I U B) (t : BulkDatum G P) :
    (recover G (complete G t)).val.1 = t.val.1 := by
  funext m
  change t.val.1 m + canonicalCap G.capSystem G.splitting t.val.2 (0, m.2) = t.val.1 m
  rw [completeTable_cap_zero, add_zero]

theorem recover_complete (G : Model I U B) (t : BulkDatum G P) : recover G (complete G t) = t := by
  apply Subtype.ext
  apply Prod.ext
  · exact recover_complete_phase G t
  · have hrec : HasResponse G.actualSystem (recover G (complete G t)).val.1
        (recover G (complete G t)).val.2 := (recover G (complete G t)).property
    rw [recover_complete_phase G t] at hrec
    exact response_unique G.actualSystem G.actual_restriction_surjective
      G.actual_closedRestriction_surjective hrec t.property

theorem complete_recover (G : Model I U B) (Ψ : CompletedDatum G P) : complete G (recover G Ψ) = Ψ := by
  apply Subtype.ext
  funext i b u
  change actualSlice Ψ.val (i, b) +
    canonicalCap G.capSystem G.splitting (recoveredResponse G Ψ.val) (u, b) = Ψ.val i b u
  rw [← capSlice_eq_canonical G Ψ.property.1 Ψ.property.2]
  exact (normalized_split Ψ.property.1 i b u).symm

/-- The full phase-table equivalence and its literal zero-new-coordinate inverse. -/
def completionEquiv (G : Model I U B) : BulkDatum G P ≃ CompletedDatum G P where
  toFun := complete G
  invFun := recover G
  left_inv := recover_complete G
  right_inv := complete_recover G

/-- Canonical completion is additive on the full phase tables. -/
def completionAddEquiv (G : Model I U B) : BulkDatum G P ≃+ CompletedDatum G P where
  toEquiv := completionEquiv G
  map_add' t s := by
    apply Subtype.ext
    funext i b u
    change (t.val.1 (i, b) + s.val.1 (i, b)) +
      (canonicalCap G.capSystem G.splitting t.val.2 (u, b) +
        canonicalCap G.capSystem G.splitting s.val.2 (u, b)) =
      (t.val.1 (i, b) + canonicalCap G.capSystem G.splitting t.val.2 (u, b)) +
        (s.val.1 (i, b) + canonicalCap G.capSystem G.splitting s.val.2 (u, b))
    abel

section Topology

variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_complete (G : Model I U B) : Continuous (complete (P := P) G) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro b
  apply continuous_pi
  intro u
  change Continuous (fun t : BulkDatum G P =>
    t.val.1 (i, b) +
      t.val.2 (G.capSystem.closedRestriction (G.splitting.closedPart (u, b)))
        (G.capSystem.restriction (G.splitting.base (u, b))))
  fun_prop

theorem continuous_recover (G : Model I U B) : Continuous (recover (P := P) G) := by
  have heval : ∀ (i : I) (b : B) (u : U),
      Continuous (fun Ψ : CompletedDatum G P => Ψ.val i b u) := by
    intro i b u
    exact (continuous_apply u).comp ((continuous_apply b).comp
      ((continuous_apply i).comp continuous_subtype_val))
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro m
    change Continuous (fun Ψ : CompletedDatum G P => Ψ.val m.1 m.2 0)
    exact heval m.1 m.2 0
  · apply continuous_pi
    intro z
    apply continuous_pi
    intro b
    change Continuous (fun Ψ : CompletedDatum G P =>
      (Ψ.val 0 (((0 : U), b) + (G.capLift z : U × B)).2
          (((0 : U), b) + (G.capLift z : U × B)).1 -
        Ψ.val 0 (((0 : U), b) + (G.capLift z : U × B)).2 0) -
      (Ψ.val 0 b 0 - Ψ.val 0 b 0))
    exact ((heval _ _ _).sub (heval _ _ _)).sub ((heval _ _ _).sub (heval _ _ _))

/-- The precise continuous additive full-table correspondence in the split model. -/
def completionContinuousAddEquiv (G : Model I U B) : BulkDatum G P ≃ₜ+ CompletedDatum G P where
  toAddEquiv := completionAddEquiv G
  continuous_toFun := continuous_complete G
  continuous_invFun := continuous_recover G

end Topology

end OpenDisk.BulkPhaseCompletion
