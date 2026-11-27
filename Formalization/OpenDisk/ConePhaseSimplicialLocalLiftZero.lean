import Formalization.OpenDisk.ConePhaseSimplicialLocalLift

/-!
# Degree-zero local lift and the complete simplicial local-lift equivalence

In degree zero the augmented cone differential is the global constant
cochain, and the local primitive is evaluation at the marked vertex. The
constant correction in the actual cone contraction proves the required
matching identity. No connectedness of the global complex is assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace OpenDisk.ConePhaseSimplicialLocalLift

open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open ConePhaseLocalLift StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]
variable (K : AbstractSimplicialComplex V)

local instance simplexOrderZero (n : ℕ) : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

local instance zeroSumOrder : LinearOrder (Unit ⊕ Simplex K 0) :=
  inferInstanceAs (LinearOrder (Unit ⊕ₗ Simplex K 0))

def constantDifferential :
    Configuration Unit G →+ (coboundaryToRange (G := G) K 0).ker where
  toFun u := ⟨constantCochain K (u Unit.unit), by
    apply Subtype.ext
    exact coboundary_constantCochain K _⟩
  map_zero' := by apply Subtype.ext; ext v; rfl
  map_add' u v := by apply Subtype.ext; ext x; rfl

@[simp] theorem constantDifferential_coe (u : Configuration Unit G) :
    (constantDifferential K u : Cochain K 0 G) = constantCochain K (u Unit.unit) := rfl

def vertexPrimitive (e : Simplex K 0) : Cochain K 0 G →+ Configuration Unit G where
  toFun v := Finsupp.single Unit.unit (v e)
  map_zero' := by simp
  map_add' u v := by simp [Finsupp.single_add]

@[simp] theorem vertexPrimitive_apply (e : Simplex K 0) (v : Cochain K 0 G) :
    vertexPrimitive K e v Unit.unit = v e := by simp [vertexPrimitive]

/-- A closed zero-cochain is constant on every simplex containing the marked
vertex. This follows from the augmented closed-star contraction. -/
theorem closed_zero_constant_on_marked_simplex (e : Simplex K 0)
    (σ : NonemptySimplex K) (heσ : e ∈ facesIn K 0 σ)
    (z : Cochain K 0 G) (hz : coboundary K 0 z = 0) :
    restrictCochain K 0 σ (constantCochain K (z e)) = restrictCochain K 0 σ z := by
  obtain ⟨p, hep⟩ := Finset.card_eq_one.mp e.property.2
  have hp : p ∈ e.val := by rw [hep]; simp
  let η : NonemptySimplex K := ⟨e.val, e.property.1⟩
  have hs : closedStarCoboundary K η 0 (restrictClosedStar K η 0 z) = 0 := by
    have hh := LinearMap.congr_fun (restrictClosedStar_coboundary (G := G) K η 0) z
    simpa only [LinearMap.comp_apply, hz, map_zero] using hh.symm
  have ha : closedStarAugmentation K η p hp (restrictClosedStar K η 0 z) = z e := by
    change z (closedStarApex K η p hp).val = z e
    congr 1
    apply Subtype.ext
    exact hep.symm
  have hc : closedStarConstant K η (z e) = restrictClosedStar K η 0 z := by
    have hh := closedStar_contraction_zero K η p hp (restrictClosedStar K η 0 z)
    rw [hs, map_zero, ha] at hh
    exact (sub_eq_zero.mp hh.symm).symm
  calc
    restrictCochain K 0 σ (constantCochain K (z e)) =
        restrictClosedStarToSimplex K η σ heσ 0 (closedStarConstant K η (z e)) := by
      rw [← restrictSimplex_restrictStar K η σ heσ, restrictClosedStar_constantCochain]
    _ = restrictClosedStarToSimplex K η σ heσ 0 (restrictClosedStar K η 0 z) :=
      congrArg (restrictClosedStarToSimplex K η σ heσ 0) hc
    _ = restrictCochain K 0 σ z := restrictSimplex_restrictStar K η σ heσ 0 z

theorem vertexPrimitive_capSection_invisible (e : Simplex K 0)
    (σ : NonemptySimplex K) (heσ : e ∈ facesIn K 0 σ)
    (j : Simplex K 0) (hj : j ∉ facesIn K 0 σ) (a : G) :
    coordinateRestriction
      (capFacets (fun σ : NonemptySimplex K => facesIn K 0 σ) (fun _ => Set.univ) σ)
      (capSection (vertexPrimitive K e) (Finsupp.single j a)) = 0 := by
  have hje : j ≠ e := by intro h; subst j; exact hj heσ
  have hn : vertexPrimitive K e (Finsupp.single j a) = 0 := by
    apply Finsupp.ext
    intro k
    cases k
    simp [vertexPrimitive, Finsupp.single_eq_of_ne hje.symm]
  have hb : coordinateRestriction (facesIn K 0 σ) (Finsupp.single j a) = 0 :=
    coordinateRestriction_single_not_mem _ hj a
  have heq : capSection (vertexPrimitive K e) (Finsupp.single j a) =
      boundaryInclude (κ := Unit) (Finsupp.single j a) := by
    change newInclude (vertexPrimitive K e (Finsupp.single j a)) +
      boundaryInclude (κ := Unit) (Finsupp.single j a) = boundaryInclude (Finsupp.single j a)
    rw [hn, map_zero, zero_add]
  rw [heq]
  exact boundaryInclude_invisible _ _ σ _ hb

theorem vertexPrimitive_contracts_closed (e : Simplex K 0)
    (z : (coboundaryToRange (G := G) K 0).ker)
    (σ : NonemptySimplex K) (heσ : e ∈ facesIn K 0 σ) :
    coordinateRestriction (facesIn K 0 σ)
      (constantDifferential (G := G) K (vertexPrimitive K e z.val)).val =
      coordinateRestriction (facesIn K 0 σ) z.val := by
  change restrictCochain K 0 σ
    (constantCochain K (vertexPrimitive K e z.val Unit.unit)) = restrictCochain K 0 σ z.val
  rw [vertexPrimitive_apply]
  exact closed_zero_constant_on_marked_simplex K e σ heσ z.val (congrArg Subtype.val z.property)

/-- The reverse local-lift implication in cochain degree zero (`q=1`). -/
theorem exists_simplicial_localLift_zero
    (F : SymmetryPhase (coboundaryToRange (G := G) K 0) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K 0 σ)
      (coboundaryToRange (G := G) K 0) F)
    (e : Simplex K 0) (g : G) (hg : g ≠ 0) :
    ∃ L : Cochain K 0 G → P,
      MarkedLocal (fun σ : NonemptySimplex K => facesIn K 0 σ) {e} L ∧
      ∀ (z : (coboundaryToRange (G := G) K 0).ker) v,
        difference L z v = difference (fun v => F z v) (Finsupp.single e g) v := by
  exact exists_localLift (κ := Unit) (P := P) (coboundaryToRange K 0)
    (fun σ : NonemptySimplex K => facesIn K 0 σ) (fun _ => (Set.univ : Set Unit))
    (simplex_mem_some_facesIn K 0) (constantDifferential K)
    (fun _ _ hk _ => (hk (Set.mem_univ _)).elim) F hF (vertexPrimitive K e) e g hg
    (vertexPrimitive_capSection_invisible K e) (vertexPrimitive_contracts_closed K e)

/-- Theorem 3.8, reverse implication, for every cochain degree on every
finite ordered simplicial complex. The lift is constructed from the cap
phase and the actual local cone contraction. -/
theorem exists_simplicial_localLift (n : ℕ)
    (F : SymmetryPhase (coboundaryToRange (G := G) K n) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K n σ)
      (coboundaryToRange (G := G) K n) F)
    (e : Simplex K n) (g : G) (hg : g ≠ 0) :
    ∃ L : Cochain K n G → P,
      MarkedLocal (fun σ : NonemptySimplex K => facesIn K n σ) {e} L ∧
      ∀ (z : (coboundaryToRange (G := G) K n).ker) v,
        difference L z v = difference (fun v => F z v) (Finsupp.single e g) v := by
  cases n with
  | zero => exact exists_simplicial_localLift_zero K F hF e g hg
  | succ m => exact exists_simplicial_localLift_positive K m F hF e g hg

/-- The complete intrinsic restriction-locality / marked-local matching
equivalence on actual finite simplicial cochains. -/
theorem simplicial_restrictionLocal_iff_matching (n : ℕ)
    (F : SymmetryPhase (coboundaryToRange (G := G) K n) P) :
    RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K n σ)
      (coboundaryToRange (G := G) K n) F ↔
    ∀ e : ElementaryLabel (Simplex K n) G, ∃ L : Cochain K n G → P,
      MarkedLocal (fun σ : NonemptySimplex K => facesIn K n σ) {e.val.1} L ∧
      ∀ (z : (coboundaryToRange (G := G) K n).ker) v,
        difference L z v = difference (fun v => F z v) (elementaryStep e) v := by
  constructor
  · intro hF e
    exact exists_simplicial_localLift K n F hF e.val.1 e.val.2 e.property
  · exact restrictionSymmetryLocal_of_matching _ _ F

end OpenDisk.ConePhaseSimplicialLocalLift
