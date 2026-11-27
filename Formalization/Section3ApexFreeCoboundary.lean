import Formalization.Section3ConeOperatorReplacement

set_option linter.style.header false

/-!
# Section 3: apex-free primitives on a cone

Fix a vertex `v` in the simplex defining a closed star.  A cochain is
`apex-free` when it vanishes on every simplex containing `v`.  The cone
homotopy gives a canonical apex-free primitive of every coboundary:

`a \mapsto h a`.

Indeed, `d h a = a` for a coboundary `a`, while `h d c = c` for an
apex-free cochain `c`.  The latter statement uses `d h + h d = 1` in
positive degree.  In degree zero the contraction has one additional
constant term, which vanishes because an apex-free cochain is zero at the
apex.  Consequently the coboundary restricted to apex-free cochains is a
linear equivalence onto the full group of closed-star coboundaries.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Closed-star cochains which vanish on every simplex containing the
chosen cone apex. -/
def apexFreeCochains
    (η : {s : Finset V // s ∈ K}) (v : V) (n : ℕ) :
    Submodule ℤ (ClosedStarCochain K η n G) where
  carrier := {c | ∀ σ, v ∈ σ.1.1 → c σ = 0}
  zero_mem' := by
    intro σ _
    rfl
  add_mem' := by
    intro c c' hc hc' σ hvσ
    simp [hc σ hvσ, hc' σ hvσ]
  smul_mem' := by
    intro z c hc σ hvσ
    simp [hc σ hvσ]

omit [Fintype V] in
@[simp]
theorem mem_apexFreeCochains
    (η : {s : Finset V // s ∈ K}) (v : V) (n : ℕ)
    (c : ClosedStarCochain K η n G) :
    c ∈ apexFreeCochains (G := G) K η v n ↔
      ∀ σ, v ∈ σ.1.1 → c σ = 0 :=
  Iff.rfl

/-- The cone homotopy of an apex-free cochain is zero. -/
theorem coneHomotopy_eq_zero_of_apexFree
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (c : ClosedStarCochain K η (n + 1) G)
    (hc : c ∈ apexFreeCochains (G := G) K η v (n + 1)) :
    coneHomotopy K η v hvη n c = 0 := by
  ext σ
  by_cases hvσ : v ∈ σ.1.1
  · rw [coneHomotopy_apply_of_mem K η v hvη n c σ hvσ]
    rfl
  · rw [coneHomotopy_apply_of_not_mem K η v hvη n c σ hvσ]
    rw [hc (insertClosedStarVertex K v hvη σ hvσ) (by simp)]
    simp

/-- In positive degree the bottom replacement fixes every apex-free
cochain. -/
theorem coneBottomReplacement_eq_self_of_apexFree_succ
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (c : ClosedStarCochain K η (n + 1) G)
    (hc : c ∈ apexFreeCochains (G := G) K η v (n + 1)) :
    coneBottomReplacement K η v hvη (n + 1) c = c := by
  have hcontract := closedStar_contraction_positive K η v hvη n c
  have hh := coneHomotopy_eq_zero_of_apexFree K η v hvη n c hc
  rw [hh, map_zero, zero_add] at hcontract
  exact hcontract

/-- In degree zero the bottom replacement fixes every apex-free cochain.
The constant correction in the augmented cone contraction vanishes because
the cochain is zero at the apex. -/
theorem coneBottomReplacement_eq_self_of_apexFree_zero
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1)
    (c : ClosedStarCochain K η 0 G)
    (hc : c ∈ apexFreeCochains (G := G) K η v 0) :
    coneBottomReplacement K η v hvη 0 c = c := by
  have haug : closedStarAugmentation K η v hvη c = 0 := by
    exact hc (closedStarApex K η v hvη) (by simp)
  simpa [coneBottomReplacement, haug] using
    closedStar_contraction_zero K η v hvη c

/-- Uniform form: bottom replacement is the identity on apex-free
cochains in every degree. -/
theorem coneBottomReplacement_eq_self_of_apexFree
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (c : ClosedStarCochain K η n G)
    (hc : c ∈ apexFreeCochains (G := G) K η v n) :
    coneBottomReplacement K η v hvη n c = c := by
  cases n with
  | zero =>
      exact coneBottomReplacement_eq_self_of_apexFree_zero
        K η v hvη c hc
  | succ n =>
      exact coneBottomReplacement_eq_self_of_apexFree_succ
        K η v hvη n c hc

/-- Coboundary is injective when restricted to apex-free cochains. -/
theorem closedStarCoboundary_injective_on_apexFree
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    Set.InjOn (closedStarCoboundary (G := G) K η n)
      (apexFreeCochains (G := G) K η v n) := by
  intro c hc c' hc' hdc
  rw [← coneBottomReplacement_eq_self_of_apexFree K η v hvη n c hc,
    ← coneBottomReplacement_eq_self_of_apexFree K η v hvη n c' hc']
  exact congrArg (coneHomotopy K η v hvη n) hdc

/-- The closed-star physical coboundaries in cochain degree `n + 1`. -/
abbrev closedStarCoboundaryGroup
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :=
  LinearMap.range (closedStarCoboundary (G := G) K η n)

/-- Coboundary restricted to apex-free cochains, with codomain the full
group of closed-star coboundaries. -/
def apexFreeCoboundaryToRange
    (η : {s : Finset V // s ∈ K}) (v : V) (n : ℕ) :
    apexFreeCochains (G := G) K η v n →ₗ[ℤ]
      closedStarCoboundaryGroup (G := G) K η n :=
  LinearMap.codRestrict (closedStarCoboundary K η n).range
    ((closedStarCoboundary K η n).comp
      (apexFreeCochains (G := G) K η v n).subtype)
    fun c => ⟨c.1, rfl⟩

@[simp]
theorem apexFreeCoboundaryToRange_coe
    (η : {s : Finset V // s ∈ K}) (v : V) (n : ℕ)
    (c : apexFreeCochains (G := G) K η v n) :
    (apexFreeCoboundaryToRange K η v n c :
        ClosedStarCochain K η (n + 1) G) =
      closedStarCoboundary K η n c.1 :=
  rfl

/-- The canonical apex-free primitive of a closed-star coboundary is its
cone homotopy. -/
def conePrimitiveOfCoboundary
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    closedStarCoboundaryGroup (G := G) K η n →ₗ[ℤ]
      apexFreeCochains (G := G) K η v n :=
  LinearMap.codRestrict (apexFreeCochains (G := G) K η v n)
    ((coneHomotopy K η v hvη n).comp
      (closedStarCoboundary K η n).range.subtype)
    fun a σ hvσ => coneHomotopy_apply_of_mem K η v hvη n a.1 σ hvσ

@[simp]
theorem conePrimitiveOfCoboundary_coe
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (a : closedStarCoboundaryGroup (G := G) K η n) :
    (conePrimitiveOfCoboundary K η v hvη n a :
        ClosedStarCochain K η n G) =
      coneHomotopy K η v hvη n a.1 :=
  rfl

/-- `h` is a right inverse to the apex-free coboundary map on every
closed-star coboundary. -/
theorem apexFreeCoboundaryToRange_conePrimitiveOfCoboundary
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (a : closedStarCoboundaryGroup (G := G) K η n) :
    apexFreeCoboundaryToRange K η v n
        (conePrimitiveOfCoboundary K η v hvη n a) = a := by
  apply Subtype.ext
  rcases a.2 with ⟨c, hc⟩
  change closedStarCoboundary K η n
      (coneHomotopy K η v hvη n a.1) = a.1
  rw [← hc]
  exact closedStarCoboundary_coneBottomReplacement K η v hvη n c

/-- `h` is also a left inverse: an apex-free primitive is uniquely
recovered from its coboundary. -/
theorem conePrimitiveOfCoboundary_apexFreeCoboundaryToRange
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (c : apexFreeCochains (G := G) K η v n) :
    conePrimitiveOfCoboundary K η v hvη n
        (apexFreeCoboundaryToRange K η v n c) = c := by
  apply Subtype.ext
  exact coneBottomReplacement_eq_self_of_apexFree K η v hvη n c.1 c.2

/-- Coboundary identifies apex-free degree-`n` cochains with all physical
coboundaries in degree `n + 1`; the inverse is the cone homotopy. -/
def apexFreeCoboundaryLinearEquiv
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    apexFreeCochains (G := G) K η v n ≃ₗ[ℤ]
      closedStarCoboundaryGroup (G := G) K η n :=
  LinearEquiv.ofLinearMap
    (apexFreeCoboundaryToRange K η v n)
    (conePrimitiveOfCoboundary K η v hvη n)
    (by
      apply LinearMap.ext
      intro a
      exact apexFreeCoboundaryToRange_conePrimitiveOfCoboundary
        K η v hvη n a)
    (by
      apply LinearMap.ext
      intro c
      exact conePrimitiveOfCoboundary_apexFreeCoboundaryToRange
        K η v hvη n c)

@[simp]
theorem apexFreeCoboundaryLinearEquiv_apply
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (c : apexFreeCochains (G := G) K η v n) :
    apexFreeCoboundaryLinearEquiv K η v hvη n c =
      apexFreeCoboundaryToRange K η v n c :=
  rfl

@[simp]
theorem apexFreeCoboundaryLinearEquiv_symm_apply
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (a : closedStarCoboundaryGroup (G := G) K η n) :
    (apexFreeCoboundaryLinearEquiv K η v hvη n).symm a =
      conePrimitiveOfCoboundary K η v hvη n a :=
  rfl

end GeneralSphereT.SimplicialCochain
