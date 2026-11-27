import Formalization.OpenDisk.BulkRealizations
import Formalization.OpenDisk.ComponentClassification

/-!
# The actual response map and its exact kernel

Admissible objects in this file are phase functions themselves, with their
literal locality and response equations. Ordinary and closed-cochain extension
are the explicit hypotheses needed to read a unique response. The response is
continuous and additive, and its kernel is exactly the local closed phases.
The local-function kernel equality (4.9) is proved independently of the separate
ball realization/surjectivity theorem.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace OpenDisk.BulkExactSequence
open GeneralSphereT.PathAlgebra BulkPhase

variable {M B P ι G Facet : Type*} [AddCommGroup M] [AddCommGroup B]
  [AddCommGroup P] [LinearOrder ι] [AddCommGroup G]
  (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (r : M →+ Configuration ι G) (Z : AddSubgroup M)
  (hz : ∀ z : Z, d (r z) = 0)
  (Loc : AddSubgroup (M → P))

abbrev system := cochainBulkSystem d r Z hz

def closedPhases : AddSubgroup (M → P) where
  carrier := {φ | ClosedInvariant Z φ}
  zero_mem' := by intro z c; rfl
  add_mem' := by intro φ ψ hφ hψ z c; exact congrArg₂ (· + ·) (hφ z c) (hψ z c)
  neg_mem' := by intro φ hφ z c; exact congrArg Neg.neg (hφ z c)

def closedLocal : AddSubgroup (M → P) := Loc ⊓ closedPhases Z

/-- Definition (4.1) on full local phase functions; the response is not extra data. -/
def admissible : AddSubgroup (M → P) where
  carrier := {φ | φ ∈ Loc ∧ ∃ F : localSymmetries facets d (P := P),
    HasResponse (system d r Z hz) φ (fun z c => F.val z c)}
  zero_mem' := ⟨Loc.zero_mem, 0, by intro z c; change (0 : P) - 0 = -0; simp⟩
  add_mem' := by
    rintro φ ψ ⟨hφ, F, hF⟩ ⟨hψ, H, hH⟩
    refine ⟨Loc.add_mem hφ hψ, F + H, ?_⟩
    intro z c
    change (φ (c + z) + ψ (c + z)) - (φ c + ψ c) =
      -(F.val _ _ + H.val _ _)
    rw [← sub_add_sub_comm, hF z c, hH z c, neg_add]
  neg_mem' := by
    rintro φ ⟨hφ, F, hF⟩
    refine ⟨Loc.neg_mem hφ, -F, ?_⟩
    intro z c
    change -φ (c + z) - -φ c = -(-F.val _ _)
    rw [neg_sub_neg, ← neg_sub, hF z c]

variable (hr : Function.Surjective r)
  (hclosed : Function.Surjective (system d r Z hz).closedRestriction)

def responseTable (φ : admissible facets d r Z hz Loc) : localSymmetries facets d (P := P) :=
  φ.property.2.choose

theorem responseTable_spec (φ : admissible facets d r Z hz Loc) :
    HasResponse (system d r Z hz) φ.val (fun z c => (responseTable facets d r Z hz Loc φ).val z c) :=
  φ.property.2.choose_spec

include hr hclosed in
theorem responseTable_unique (φ : admissible facets d r Z hz Loc)
    (F : localSymmetries facets d (P := P))
    (hF : HasResponse (system d r Z hz) φ.val (fun z c => F.val z c)) :
    responseTable facets d r Z hz Loc φ = F := by
  apply Subtype.ext
  apply Subtype.ext
  exact response_unique (system d r Z hz) hr hclosed (responseTable_spec _ _ _ _ _ _ φ) hF

/-- The response of an actual phase table, well-defined by closed extension. -/
def response : admissible facets d r Z hz Loc →+ localSymmetries facets d (P := P) where
  toFun := responseTable facets d r Z hz Loc
  map_zero' := responseTable_unique facets d r Z hz Loc hr hclosed 0 0
    (by intro z c; change (0 : P) - 0 = -0; simp)
  map_add' φ ψ := by
    apply responseTable_unique facets d r Z hz Loc hr hclosed
    intro z c
    change (φ.val (c + z) + ψ.val (c + z)) - (φ.val c + ψ.val c) = _
    rw [← sub_add_sub_comm, responseTable_spec _ _ _ _ _ _ φ z c,
      responseTable_spec _ _ _ _ _ _ ψ z c]
    exact (neg_add _ _).symm

theorem response_spec (φ : admissible facets d r Z hz Loc) :
    HasResponse (system d r Z hz) φ.val (fun z c => (response facets d r Z hz Loc hr hclosed φ).val z c) :=
  responseTable_spec _ _ _ _ _ _ φ

theorem response_eq_zero_iff (φ : admissible facets d r Z hz Loc) :
    response facets d r Z hz Loc hr hclosed φ = 0 ↔ ClosedInvariant Z φ.val := by
  constructor
  · intro h
    have hφ := response_spec facets d r Z hz Loc hr hclosed φ
    rw [h] at hφ
    exact (response_zero_iff (system d r Z hz) φ.val).1 hφ
  · intro h
    exact responseTable_unique facets d r Z hz Loc hr hclosed φ 0
      ((response_zero_iff (system d r Z hz) φ.val).2 h)

/-- Inclusion of the genuine closed local phase subgroup. -/
def closedInclusion : closedLocal Z Loc →+ admissible facets d r Z hz Loc where
  toFun φ := ⟨φ.val, φ.property.1, 0,
    (response_zero_iff (system d r Z hz) φ.val).2 φ.property.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem closedInclusion_injective : Function.Injective (closedInclusion facets d r Z hz Loc) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun t : admissible facets d r Z hz Loc => t.val) h

/-- Exactness at the middle term of (4.10), without a ball hypothesis. -/
theorem response_kernel :
    (response facets d r Z hz Loc hr hclosed).ker =
      (closedInclusion facets d r Z hz Loc).range := by
  ext φ
  constructor
  · intro h
    exact ⟨⟨φ.val, φ.property.1,
      (response_eq_zero_iff facets d r Z hz Loc hr hclosed φ).1 h⟩, rfl⟩
  · rintro ⟨ψ, rfl⟩
    exact (response_eq_zero_iff facets d r Z hz Loc hr hclosed _).2 ψ.property.2

/-- The kernel is the actual closed local phase group, with no quotient of constants. -/
def responseKernelEquiv :
    (response facets d r Z hz Loc hr hclosed).ker ≃+ closedLocal Z Loc where
  toFun φ := ⟨φ.val.val, φ.val.property.1,
    (response_eq_zero_iff facets d r Z hz Loc hr hclosed φ.val).1 φ.property⟩
  invFun φ := ⟨closedInclusion facets d r Z hz Loc φ,
    (response_eq_zero_iff facets d r Z hz Loc hr hclosed _).2 φ.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section Topology
variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_response : Continuous (response facets d r Z hz Loc hr hclosed) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro z
  apply continuous_pi
  intro c
  change Continuous (fun φ : admissible facets d r Z hz Loc =>
    (response facets d r Z hz Loc hr hclosed φ).val z c)
  obtain ⟨y, hy⟩ := hclosed z
  obtain ⟨v, hv⟩ := hr c
  have heq : (fun φ : admissible facets d r Z hz Loc =>
      (response facets d r Z hz Loc hr hclosed φ).val z c) =
      (fun φ => -(φ.val (v + y) - φ.val v)) := by
    funext φ
    have h := response_spec facets d r Z hz Loc hr hclosed φ y v
    change φ.val (v + y) - φ.val v =
      -(response facets d r Z hz Loc hr hclosed φ).val
        ((system d r Z hz).closedRestriction y) (r v) at h
    rw [hy, hv] at h
    exact (neg_eq_iff_eq_neg.mpr h).symm
  rw [heq]
  exact (((continuous_apply (v + y)).comp continuous_subtype_val).sub
    ((continuous_apply v).comp continuous_subtype_val)).neg

def responseKernelHomeomorph :
    (response facets d r Z hz Loc hr hclosed).ker ≃ₜ closedLocal Z Loc where
  toEquiv := (responseKernelEquiv facets d r Z hz Loc hr hclosed).toEquiv
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end Topology

variable [Nonempty Facet]
  (hpull : ∀ γ : localFunctionSubgroup (G := G) facets P, (fun c => γ.val (r c)) ∈ Loc)

def pullbackHom : (Configuration ι G → P) →+ (M → P) where
  toFun γ c := γ (r c)
  map_zero' := rfl
  map_add' _ _ := rfl

include hpull in
/-- The local-function part of (4.9), valid before taking component labels. -/
theorem response_local_iff_closed_correction (φ : admissible facets d r Z hz Loc) :
    response facets d r Z hz Loc hr hclosed φ ∈ (localDerivative (P := P) facets d).range ↔
      ∃ γ : localFunctionSubgroup (G := G) facets P,
        (fun c => φ.val c + γ.val (r c)) ∈ closedLocal Z Loc := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, Loc.add_mem φ.property.1 (hpull γ), ?_⟩
    apply (correction_closed_iff (system d r Z hz)
      (response_spec facets d r Z hz Loc hr hclosed φ) γ.val hr hclosed).2
    intro z c
    exact congrFun (congrFun (congrArg Subtype.val (congrArg Subtype.val hγ)) z) c
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z c
    exact (correction_closed_iff (system d r Z hz)
      (response_spec facets d r Z hz Loc hr hclosed φ) γ.val hr hclosed).1 hγ.2 z c

include hpull in
/-- Literal subgroup sum in (4.9), including all constant phases. -/
theorem response_local_iff_sum (φ : admissible facets d r Z hz Loc) :
    response facets d r Z hz Loc hr hclosed φ ∈ (localDerivative (P := P) facets d).range ↔
      φ.val ∈ closedLocal Z Loc ⊔
        (localFunctionSubgroup (G := G) facets P).map (pullbackHom r) := by
  rw [response_local_iff_closed_correction facets d r Z hz Loc hr hclosed hpull]
  constructor
  · rintro ⟨γ, hγ⟩
    apply AddSubgroup.mem_sup.mpr
    refine ⟨(fun c => φ.val c + γ.val (r c)), hγ,
      (fun c => -γ.val (r c)), ?_, ?_⟩
    · exact ⟨-γ.val, (localFunctionSubgroup (G := G) facets P).neg_mem γ.property, rfl⟩
    · funext c; simp
  · rintro h
    obtain ⟨κ, hκ, η, hη, heq⟩ := AddSubgroup.mem_sup.mp h
    obtain ⟨γ, hγ, rfl⟩ := hη
    refine ⟨⟨-γ, (localFunctionSubgroup (G := G) facets P).neg_mem hγ⟩, ?_⟩
    have hfun : (fun c => φ.val c + (-γ) (r c)) = κ := by
      rw [← heq]
      funext c
      change (κ c + γ (r c)) + -γ (r c) = κ c
      abel
    rw [hfun]
    exact hκ

end OpenDisk.BulkExactSequence
