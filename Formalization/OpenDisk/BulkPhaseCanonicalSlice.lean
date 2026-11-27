import Formalization.OpenDisk.BulkPhaseSimplicialGluing
import Formalization.OpenDisk.ConePhaseSimplicial

/-! The canonical cone primitive has exactly the zero-slice normalization
used by the simplicial local gluing inverse. This connects the actual cone
contraction to the actual new-vertex cochain coordinates. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace OpenDisk.BulkPhaseCanonicalSlice

open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open BulkPhaseSimplicialGluing ConePhaseSimplicial

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]
variable (K : AbstractSimplicialComplex V) (p : V)

local instance simplexOrder (n : ℕ) : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- Pull the actual canonical cone primitive back to the glued cochains. -/
def canonicalStarCap (η : NonemptySimplex K) (hp : p ∈ η.val) (n : ℕ)
    (R : closedCochains (G := G) K η n → ClosedStarCochain K η n G → P) :
    Cochain K n G → P := fun c =>
  conePrimitive K η p hp n R (restrictClosedStar K η n c)

/-- The geometric zero-new-coordinate slice agrees with the normalization
of the primitive obtained from the ordered cone contraction. -/
theorem canonicalStarCap_zero_slice (η : NonemptySimplex K) (hp : p ∈ η.val) (n : ℕ)
    {R : closedCochains (G := G) K η n → ClosedStarCochain K η n G → P}
    (hR : ConePhase.IsCocycle R) (c : Cochain K n G) :
    canonicalStarCap K p η hp n R (zeroNewCoordinates K p n c) = 0 := by
  apply conePrimitive_zero_slice K η p hp n hR
  intro τ hpτ
  change zeroNewCoordinates K p n c τ.val = 0
  exact zeroNewCoordinates_new K p n c τ.val hpτ

/-- The completed phase returns the entire actual phase, including its
global constant, when all new cone coordinates are put to zero. -/
theorem canonical_completion_actual_slice (η : NonemptySimplex K) (hp : p ∈ η.val) (n : ℕ)
    {R : closedCochains (G := G) K η n → ClosedStarCochain K η n G → P}
    (hR : ConePhase.IsCocycle R) (φ : Cochain K n G → P)
    (hφ : AnchoredLocal (actualFacets K p n) φ) (c : Cochain K n G) :
    (φ + canonicalStarCap K p η hp n R) (zeroNewCoordinates K p n c) = φ c := by
  rw [Pi.add_apply, canonicalStarCap_zero_slice K p η hp n hR, add_zero]
  exact BulkPhaseLocalGluing.local_eq_project (actualFacets K p n)
    (actualCoordinates K p n) (actualFacet_inside K p n) hφ c

end OpenDisk.BulkPhaseCanonicalSlice
