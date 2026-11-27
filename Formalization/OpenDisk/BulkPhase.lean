import Formalization.OpenDisk.ConePhase

/-!
# Bulk response, canonical cap, and equality of full phase tables

The results here are algebraic theorems about genuine phase functions. They
separate the finite-difference arguments in Sections 4 and III of the report from
the geometric assertions about locality, triangulations, and cochain extension.
Those geometric assertions are not assumed to have been formalized by this file.

`System` records restriction and the subgroup of closed cochains. `HasResponse`
uses the paper's sign convention, `Δᵧ φ = - F(y|X, c|X)`. Surjectivity is explicitly
required exactly where ordinary or closed extension is used.
-/

namespace OpenDisk.BulkPhase

variable {M B C P : Type*} [AddCommGroup M] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup P]

/-- A restriction map which carries closed cochains to closed cochains. -/
structure System (M B : Type*) [AddCommGroup M] [AddCommGroup B] where
  restriction : M →+ B
  bulkClosed : AddSubgroup M
  boundaryClosed : AddSubgroup B
  restriction_closed : ∀ y : bulkClosed, restriction y ∈ boundaryClosed

namespace System

variable (S : System M B)

def closedRestriction : S.bulkClosed →+ S.boundaryClosed where
  toFun y := ⟨S.restriction y, S.restriction_closed y⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' y z := by apply Subtype.ext; simp

@[simp] theorem coe_closedRestriction (y : S.bulkClosed) :
    (S.closedRestriction y : B) = S.restriction y := rfl

end System

/-- Equation (4.1), with its negative finite-difference convention. -/
def HasResponse (S : System M B) (φ : M → P)
    (F : S.boundaryClosed → B → P) : Prop :=
  ∀ (y : S.bulkClosed) c,
    φ (c + y) - φ c = -F (S.closedRestriction y) (S.restriction c)

/-- Invariance means equality of full phases, including the global phase. -/
def ClosedInvariant (Z : AddSubgroup M) (φ : M → P) : Prop :=
  ∀ (y : Z) c, φ (c + y) = φ c

theorem response_unique (S : System M B)
    (hr : Function.Surjective S.restriction)
    (hz : Function.Surjective S.closedRestriction) {φ : M → P}
    {F G : S.boundaryClosed → B → P}
    (hF : HasResponse S φ F) (hG : HasResponse S φ G) : F = G := by
  funext z b
  obtain ⟨y, rfl⟩ := hz z
  obtain ⟨c, rfl⟩ := hr b
  exact neg_injective ((hF y c).symm.trans (hG y c))

/-- The boundary group law follows from finite differences and extension. -/
theorem response_isCocycle (S : System M B)
    (hr : Function.Surjective S.restriction)
    (hz : Function.Surjective S.closedRestriction) {φ : M → P}
    {F : S.boundaryClosed → B → P} (hF : HasResponse S φ F) :
    ConePhase.IsCocycle F := by
  constructor
  · intro b
    obtain ⟨c, rfl⟩ := hr b
    have h := hF 0 c
    simpa using h.symm
  · intro z w b
    obtain ⟨y, rfl⟩ := hz z
    obtain ⟨x, rfl⟩ := hz w
    obtain ⟨c, rfl⟩ := hr b
    have h₁ := hF (y + x) c
    have h₂ := hF y c
    have h₃ := hF x (c + y)
    simp only [map_add, AddSubgroup.coe_add, ← add_assoc] at h₁ h₃
    have h : -F (S.closedRestriction y + S.closedRestriction x) (S.restriction c) =
        -F (S.closedRestriction y) (S.restriction c) +
          -F (S.closedRestriction x) (S.restriction c + S.restriction y) := by
      rw [← h₁, ← h₂, ← h₃]
      abel
    exact neg_injective (by simpa [add_comm] using h)

theorem response_zero_iff (S : System M B) (φ : M → P) :
    HasResponse S φ 0 ↔ ClosedInvariant S.bulkClosed φ := by
  simp only [HasResponse, ClosedInvariant, Pi.zero_apply, neg_zero, sub_eq_zero]

/-- The exact kernel identity behind Theorem 4.5; locality is independent of this identity. -/
theorem correction_closed_iff (S : System M B) {φ : M → P}
    {F : S.boundaryClosed → B → P} (hF : HasResponse S φ F) (β : B → P)
    (hr : Function.Surjective S.restriction)
    (hz : Function.Surjective S.closedRestriction) :
    ClosedInvariant S.bulkClosed (fun c => φ c + β (S.restriction c)) ↔
      ∀ (z : S.boundaryClosed) b, β (b + z) - β b = F z b := by
  constructor
  · intro h z b
    obtain ⟨y, rfl⟩ := hz z
    obtain ⟨c, rfl⟩ := hr b
    have hc := h y c
    have hf := hF y c
    simp only [map_add, System.coe_closedRestriction] at hc ⊢
    rw [sub_eq_iff_eq_add] at hf
    rw [hf] at hc
    apply sub_eq_iff_eq_add.mpr
    apply add_left_cancel (a := φ c)
    calc
      φ c + β (S.restriction c + S.restriction y) =
          F (S.closedRestriction y) (S.restriction c) +
            (-F (S.closedRestriction y) (S.restriction c) + φ c +
              β (S.restriction c + S.restriction y)) := by abel
      _ = F (S.closedRestriction y) (S.restriction c) +
            (φ c + β (S.restriction c)) := by rw [hc]
      _ = φ c + (F (S.closedRestriction y) (S.restriction c) +
            β (S.restriction c)) := by abel
  · intro h y c
    have hf := hF y c
    have hb := h (S.closedRestriction y) (S.restriction c)
    simp only [map_add, System.coe_closedRestriction] at hb ⊢
    rw [sub_eq_iff_eq_add] at hf hb
    rw [hf, hb]
    abel

/-- A boundary cocycle restricts to a cocycle on cap cochains. -/
theorem pullback_isCocycle (T : System C B)
    {F : T.boundaryClosed → B → P} (hF : ConePhase.IsCocycle F) :
    ConePhase.IsCocycle
      (fun (y : T.bulkClosed) c => F (T.closedRestriction y) (T.restriction c)) := by
  constructor
  · intro c
    simpa using hF.1 (T.restriction c)
  · intro y z c
    simpa using hF.2 (T.closedRestriction y) (T.closedRestriction z) (T.restriction c)

/-- Formula (4.7). The splitting is supplied by the cone contraction. -/
def canonicalCap (T : System C B) (S : ConePhase.Splitting T.bulkClosed)
    (F : T.boundaryClosed → B → P) (c : C) : P :=
  F (T.closedRestriction (S.closedPart c)) (T.restriction (S.base c))

theorem canonicalCap_difference (T : System C B)
    (S : ConePhase.Splitting T.bulkClosed) {F : T.boundaryClosed → B → P}
    (hF : ConePhase.IsCocycle F) (y : T.bulkClosed) (c : C) :
    canonicalCap T S F (c + y) - canonicalCap T S F c =
      F (T.closedRestriction y) (T.restriction c) :=
  ConePhase.primitive_difference S (pullback_isCocycle T hF) y c

theorem canonicalCap_base (T : System C B)
    (S : ConePhase.Splitting T.bulkClosed) {F : T.boundaryClosed → B → P}
    (hF : ConePhase.IsCocycle F) (c : C) :
    canonicalCap T S F (S.base c) = 0 :=
  ConePhase.primitive_base S (pullback_isCocycle T hF) c

/-- Closed invariance of the completed full phase table, proved by cancellation. -/
theorem completion_invariant (A : System M B) (T : System C B)
    (S : ConePhase.Splitting T.bulkClosed) {φ : M → P}
    {F : B → B → P} (hφ : HasResponse A φ (fun y b => F y b))
    (hF : ConePhase.IsCocycle (fun (z : T.boundaryClosed) b => F z b))
    (y : A.bulkClosed) (z : T.bulkClosed)
    (hyz : A.restriction y = T.restriction z) (m : M) (c : C)
    (hmc : A.restriction m = T.restriction c) :
    φ (m + y) + canonicalCap T S (fun z b => F z b) (c + z) =
      φ m + canonicalCap T S (fun z b => F z b) c := by
  have h₁ := hφ y m
  have h₂ := canonicalCap_difference T S hF z c
  simp only [System.coe_closedRestriction] at h₁ h₂
  rw [← hyz, ← hmc] at h₂
  rw [sub_eq_iff_eq_add] at h₁ h₂
  rw [h₁, h₂]
  abel

/-- The zero-slice condition removes all ambiguity in a cap primitive. -/
theorem normalized_cap_unique (T : System C B)
    (S : ConePhase.Splitting T.bulkClosed) {F : T.boundaryClosed → B → P}
    {χ : C → P}
    (hχ : ∀ (z : T.bulkClosed) c,
      χ (c + z) - χ c = F (T.closedRestriction z) (T.restriction c))
    (hbase : ∀ c, χ (S.base c) = 0) : χ = canonicalCap T S F :=
  ConePhase.primitive_unique S hχ hbase

/-- The coefficient phase of the actual encoded state in equation (4.4). -/
def realizationPhase (r : M →+ B) (φ : M → P) (β : B → P) (c : M) : P :=
  φ c + β (r c)

/-- The actual hopping phase after conjugating a lifted boundary hopping by `φ`.
The bulk increment `t` includes the specified choice of boundary-coordinate lift. -/
def realizedHoppingPhase (r : M →+ B) (φ : M → P) (L : B → B → P)
    (t c : M) : P := L (r t) (r c) + φ (c + t) - φ c

/-- The phase relating two realizations of the same full statistics table. -/
def realizationCorrection (r : M →+ B) (φ₀ φ₁ : M → P) (γ : B → P) (c : M) : P :=
  φ₁ c - φ₀ c + γ (r c)

theorem realizationPhase_difference (r : M →+ B) (φ₀ φ₁ : M → P)
    (β₀ β₁ γ : B → P) (hγ : ∀ b, β₁ b - β₀ b = γ b) (c : M) :
    realizationPhase r φ₁ β₁ c - realizationPhase r φ₀ β₀ c =
      realizationCorrection r φ₀ φ₁ γ c := by
  unfold realizationPhase realizationCorrection
  rw [← hγ]
  abel

/-- Equality of the full hopping tables gives the precise conjugating phase,
not merely equality of a component label. -/
theorem realizedHoppingPhase_difference (r : M →+ B) (φ₀ φ₁ : M → P)
    (L₀ L₁ : B → B → P) (γ : B → P)
    (hL : ∀ s b, L₁ s b - L₀ s b = γ (b + s) - γ b) (t c : M) :
    realizedHoppingPhase r φ₁ L₁ t c - realizedHoppingPhase r φ₀ L₀ t c =
      realizationCorrection r φ₀ φ₁ γ (c + t) -
        realizationCorrection r φ₀ φ₁ γ c := by
  have h := hL (r t) (r c)
  rw [sub_eq_iff_eq_add] at h
  unfold realizedHoppingPhase realizationCorrection
  rw [h, map_add]
  abel

/-- The correction is closed if both boundary phases trivialize their responses.
Locality of this correction follows separately from locality of `φ₀`, `φ₁`, `γ`
and closure of the geometric local-function subgroup under boundary pullback. -/
theorem realizationCorrection_closed (S : System M B)
    {φ₀ φ₁ : M → P} {F₀ F₁ : S.boundaryClosed → B → P}
    (h₀ : HasResponse S φ₀ F₀) (h₁ : HasResponse S φ₁ F₁)
    (β₀ β₁ γ : B → P)
    (hβ₀ : ∀ (z : S.boundaryClosed) b, β₀ (b + z) - β₀ b = F₀ z b)
    (hβ₁ : ∀ (z : S.boundaryClosed) b, β₁ (b + z) - β₁ b = F₁ z b)
    (hγ : ∀ b, β₁ b - β₀ b = γ b) :
    ClosedInvariant S.bulkClosed (realizationCorrection S.restriction φ₀ φ₁ γ) := by
  intro y c
  have hφ₀ := h₀ y c
  have hφ₁ := h₁ y c
  have hb₀ := hβ₀ (S.closedRestriction y) (S.restriction c)
  have hb₁ := hβ₁ (S.closedRestriction y) (S.restriction c)
  rw [sub_eq_iff_eq_add] at hφ₀ hφ₁ hb₀ hb₁
  unfold realizationCorrection
  rw [← hγ, ← hγ, map_add, hφ₀, hφ₁]
  simp only [System.coe_closedRestriction] at hb₀ hb₁
  rw [hb₀, hb₁]
  abel

end OpenDisk.BulkPhase
