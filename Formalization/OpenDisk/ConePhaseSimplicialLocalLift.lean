import Formalization.OpenDisk.ConePhaseLocalLift
import Formalization.SimplicialFacetData
import Formalization.SimplicialCoboundarySquare
import Formalization.OpenDisk.StarLocality

/-!
# The local lift on actual simplicial cochains

The cap differential is the genuine simplicial coboundary, including its
`d² = 0` proof. Its columns obey the required facet support condition because
coboundary commutes with restriction. This module instantiates the explicit
cap construction using cochains on finite ordered simplicial complexes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace OpenDisk.ConePhaseSimplicialLocalLift

open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open ConePhaseLocalLift
open StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]
variable (K : AbstractSimplicialComplex V)

local instance simplexOrder (n : ℕ) : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

local instance simplexSumOrder (n : ℕ) :
    LinearOrder (Simplex K n ⊕ Simplex K (n + 1)) :=
  inferInstanceAs (LinearOrder (Simplex K n ⊕ₗ Simplex K (n + 1)))

/-- The previous simplicial coboundary, with codomain in the group of closed
boundary cochains. Closure is proved from the simplicial identity `d²=0`. -/
def previousCoboundary (n : ℕ) :
    Cochain K n G →+ (coboundaryToRange (G := G) K (n + 1)).ker where
  toFun u := ⟨coboundary K n u, by
    apply Subtype.ext
    exact coboundary_coboundary K n u⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' u v := by apply Subtype.ext; exact map_add _ u v

@[simp] theorem previousCoboundary_coe (n : ℕ) (u : Cochain K n G) :
    (previousCoboundary K n u : Cochain K (n + 1) G) = coboundary K n u := rfl

/-- Every elementary coboundary column is invisible on a simplex which
does not contain its input simplex. -/
theorem previousCoboundary_column (n : ℕ) (σ : NonemptySimplex K)
    (τ : Simplex K n) (hτ : τ ∉ facesIn K n σ) (g : G) :
    coordinateRestriction (facesIn K (n + 1) σ)
      (previousCoboundary K n (Finsupp.single τ g) : Cochain K (n + 1) G) = 0 := by
  change restrictCochain K (n + 1) σ (coboundary K n (Finsupp.single τ g)) = 0
  have hcomm := DFunLike.congr_fun (restrictCochain_coboundary (G := G) K n σ)
    (Finsupp.single τ g)
  change restrictCochain K (n + 1) σ (coboundary K n (Finsupp.single τ g)) =
    localCoboundary K n σ (restrictCochain K n σ (Finsupp.single τ g)) at hcomm
  rw [hcomm]
  change localCoboundary K n σ
    (coordinateRestriction (facesIn K n σ) (Finsupp.single τ g)) = 0
  rw [coordinateRestriction_single_not_mem _ hτ, map_zero]

/-- The actual simplicial cap table is local whenever the supplied symmetry
table obeys the intrinsic restriction-local axiom. -/
theorem simplicial_cap_local (n : ℕ)
    (F : SymmetryPhase (coboundaryToRange (G := G) K (n + 1)) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
      (coboundaryToRange (G := G) K (n + 1)) F) :
    DifferenceLocal
      (capFacets (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
        (fun σ => facesIn K n σ))
      (capPhase (coboundaryToRange K (n + 1)) (previousCoboundary K n) F) :=
  capPhase_local _ _ _ (simplex_mem_some_facesIn K (n + 1))
    (previousCoboundary K n) (previousCoboundary_column K n) F hF

theorem starPrimitive_capSection_invisible (n : ℕ) (e : Simplex K (n + 1))
    (p : V) (hp : p ∈ e.val) (σ : NonemptySimplex K)
    (heσ : e ∈ facesIn K (n + 1) σ)
    (j : Simplex K (n + 1)) (hj : j ∉ facesIn K (n + 1) σ) (a : G) :
    coordinateRestriction
      (capFacets (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
        (fun σ => facesIn K n σ) σ)
      (capSection (starPrimitiveExtension K ⟨e.val, e.property.1⟩ p hp n)
        (Finsupp.single j a)) = 0 := by
  have hb : restrictCochain K (n + 1) σ (Finsupp.single j a) = 0 :=
    coordinateRestriction_single_not_mem _ hj a
  have hn : restrictCochain K n σ
      (starPrimitiveExtension K ⟨e.val, e.property.1⟩ p hp n (Finsupp.single j a)) = 0 := by
    rw [restrictCochain_starPrimitiveExtension K ⟨e.val, e.property.1⟩ σ
      (show e.val ⊆ σ.val from heσ) p hp n, hb, map_zero]
  ext s
  rcases s with ⟨s, hs⟩
  cases s with
  | inl k =>
      have hk : k ∈ facesIn K n σ := hs
      have hz := congrArg (fun c => c ⟨k, hk⟩) hn
      change starPrimitiveExtension K ⟨e.val, e.property.1⟩ p hp n
        (Finsupp.single j a) k = 0 at hz
      change capSection _ (Finsupp.single j a) (Sum.inl k) = 0
      simpa [capSection] using hz
  | inr k =>
      have hk : k ∈ facesIn K (n + 1) σ := hs
      have hz := congrArg (fun c => c ⟨k, hk⟩) hb
      change (Finsupp.single j a : Cochain K (n + 1) G) k = 0 at hz
      change capSection _ (Finsupp.single j a) (Sum.inr k) = 0
      change newInclude (ι := Simplex K (n + 1))
        (starPrimitiveExtension K ⟨e.val, e.property.1⟩ p hp n
          (Finsupp.single j a)) (Sum.inr k) +
        boundaryInclude (κ := Simplex K n) (Finsupp.single j a) (Sum.inr k) = 0
      simpa only [Finsupp.add_apply, newInclude_inr, boundaryInclude_inr, zero_add] using hz

theorem starPrimitive_contracts_closed (n : ℕ) (e : Simplex K (n + 1))
    (p : V) (hp : p ∈ e.val)
    (z : (coboundaryToRange (G := G) K (n + 1)).ker)
    (σ : NonemptySimplex K) (heσ : e ∈ facesIn K (n + 1) σ) :
    coordinateRestriction (facesIn K (n + 1) σ)
      (previousCoboundary (G := G) K n
        (starPrimitiveExtension K ⟨e.val, e.property.1⟩ p hp n z.val)).val =
      coordinateRestriction (facesIn K (n + 1) σ) z.val := by
  have hz : coboundary K (n + 1) (z : Cochain K (n + 1) G) = 0 :=
    congrArg Subtype.val z.property
  exact restrictCochain_d_starPrimitiveExtension K ⟨e.val, e.property.1⟩ σ
    (show e.val ⊆ σ.val from heσ) p hp n z.val hz

/-- The reverse local-lift implication of Theorem 3.8 on every finite
ordered simplicial complex in positive cochain degree (`q ≥ 2`). All
contraction and facet-support hypotheses have been discharged by the
actual simplicial coboundary and closed-star cone homotopy. -/
theorem exists_simplicial_localLift_positive (n : ℕ)
    (F : SymmetryPhase (coboundaryToRange (G := G) K (n + 1)) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K (n + 1) σ)
      (coboundaryToRange (G := G) K (n + 1)) F)
    (e : Simplex K (n + 1)) (g : G) (hg : g ≠ 0) :
    ∃ L : Cochain K (n + 1) G → P,
      MarkedLocal (fun σ : NonemptySimplex K => facesIn K (n + 1) σ) {e} L ∧
      ∀ (z : (coboundaryToRange (G := G) K (n + 1)).ker) v,
        difference L z v = difference (fun v => F z v) (Finsupp.single e g) v := by
  have hne : e.val.Nonempty := Finset.card_pos.mp (by rw [e.property.2]; omega)
  obtain ⟨p, hp⟩ := hne
  exact exists_localLift _ _ _ (simplex_mem_some_facesIn K (n + 1))
    (previousCoboundary K n) (previousCoboundary_column K n) F hF
    (starPrimitiveExtension K ⟨e.val, e.property.1⟩ p hp n) e g hg
    (starPrimitive_capSection_invisible K n e p hp)
    (starPrimitive_contracts_closed K n e p hp)

end OpenDisk.ConePhaseSimplicialLocalLift
