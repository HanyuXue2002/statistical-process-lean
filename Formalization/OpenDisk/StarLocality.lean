import Formalization.OpenDisk.ConePhaseLocal
import Formalization.OpenDisk.JointSymmetryKernel
import Formalization.OpenDisk.NormalForm
import Formalization.Section3SimplicialLocalTau

set_option linter.style.header false

/-!
# Closed extensions and marked phases on genuine simplicial stars

Closed cochains on a closed star extend to globally closed cochains: in
positive degree extend a cone primitive and take its coboundary; in degree
zero extend the constant apex value. The finite star contraction and all
restriction identities used here are concrete ordered simplicial maps.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]

variable (K : AbstractSimplicialComplex V)

theorem restrictSimplex_restrictStar (η σ : NonemptySimplex K) (hησ : η.val ⊆ σ.val)
    (n : ℕ) (c : Cochain K n G) :
    restrictClosedStarToSimplex K η σ hησ n (restrictClosedStar K η n c) =
      restrictCochain K n σ c := by
  ext τ
  rfl

theorem restrictSimplex_extendStar (η σ : NonemptySimplex K) (hησ : η.val ⊆ σ.val)
    (n : ℕ) (c : ClosedStarCochain K η n G) :
    restrictCochain K n σ (extendCarrierClosedStar K η n c) =
      restrictClosedStarToSimplex K η σ hησ n c := by
  rw [← restrictSimplex_restrictStar K η σ hησ,
    restrictClosedStar_extendCarrierClosedStar]

/-- The actual zero-extended cone primitive on a selected star. -/
def starPrimitiveExtension (η : NonemptySimplex K) (p : V) (hp : p ∈ η.val) (m : ℕ) :
    Cochain K (m + 1) G →+ Cochain K m G :=
  (extendCarrierClosedStar K η m).comp
    ((coneHomotopy K η p hp m).toAddMonoidHom.comp
      (restrictClosedStarAddHom K η (m + 1)))

/-- The selected extension is local on every simplex containing the carrier. -/
theorem restrictCochain_starPrimitiveExtension (η σ : NonemptySimplex K)
    (hησ : η.val ⊆ σ.val) (p : V) (hp : p ∈ η.val) (m : ℕ)
    (c : Cochain K (m + 1) G) :
    restrictCochain K m σ (starPrimitiveExtension K η p hp m c) =
      simplexConeHomotopy K η σ hησ p hp m (restrictCochain K (m + 1) σ c) := by
  change restrictCochain K m σ
    (extendCarrierClosedStar K η m (coneHomotopy K η p hp m
      (restrictClosedStar K η (m + 1) c))) = _
  rw [restrictSimplex_extendStar K η σ hησ]
  have hn := LinearMap.congr_fun
    (restrictClosedStarToSimplex_coneHomotopy K η σ hησ p hp m)
    (restrictClosedStar K η (m + 1) c)
  simpa only [LinearMap.comp_apply, restrictSimplex_restrictStar] using hn

/-- In positive degree, `d ext h` extends every closed star cochain. -/
theorem extend_closed_star_positive (η : NonemptySimplex K) (p : V) (hp : p ∈ η.val)
    (m : ℕ) (z : ClosedStarCochain K η (m + 1) G)
    (hz : closedStarCoboundary K η (m + 1) z = 0) :
    restrictClosedStar K η (m + 1)
      (coboundary K m (extendCarrierClosedStar K η m (coneHomotopy K η p hp m z))) = z := by
  have hn := LinearMap.congr_fun (restrictClosedStar_coboundary (G := G) K η m)
    (extendCarrierClosedStar K η m (coneHomotopy K η p hp m z))
  simp only [LinearMap.comp_apply, restrictClosedStar_extendCarrierClosedStar] at hn
  rw [hn]
  have hh := closedStar_contraction_positive K η p hp m z
  simpa only [hz, map_zero, add_zero] using hh

/-- The ordinary closed-star restriction is surjective on closed cochains,
including the degree-zero constant correction. -/
theorem exists_global_closed_extension (η : NonemptySimplex K) (p : V) (hp : p ∈ η.val)
    (n : ℕ) (z : ClosedStarCochain K η n G)
    (hz : closedStarCoboundary K η n z = 0) :
    ∃ c : Cochain K n G, coboundary K n c = 0 ∧ restrictClosedStar K η n c = z := by
  cases n with
  | zero =>
      refine ⟨constantCochain K (closedStarAugmentation K η p hp z),
        coboundary_constantCochain K _, ?_⟩
      rw [restrictClosedStar_constantCochain]
      have hh := closedStar_contraction_zero K η p hp z
      have heq : z - closedStarConstant K η (closedStarAugmentation K η p hp z) = 0 := by
        simpa only [hz, map_zero] using hh.symm
      exact (sub_eq_zero.mp heq).symm
  | succ m =>
      refine ⟨coboundary K m (extendCarrierClosedStar K η m (coneHomotopy K η p hp m z)),
        coboundary_coboundary K m _, extend_closed_star_positive K η p hp m z hz⟩

/-- On a globally closed input, the differential of the selected primitive
agrees with that input on the entire closed star. -/
theorem restrictStar_d_starPrimitiveExtension (η : NonemptySimplex K)
    (p : V) (hp : p ∈ η.val) (m : ℕ) (z : Cochain K (m + 1) G)
    (hz : coboundary K (m + 1) z = 0) :
    restrictClosedStar K η (m + 1) (coboundary K m (starPrimitiveExtension K η p hp m z)) =
      restrictClosedStar K η (m + 1) z := by
  apply extend_closed_star_positive
  change closedStarCoboundary K η (m + 1) (restrictClosedStar K η (m + 1) z) = 0
  have hh := LinearMap.congr_fun (restrictClosedStar_coboundary (G := G) K η (m + 1)) z
  simpa only [LinearMap.comp_apply, hz, map_zero] using hh.symm

theorem restrictCochain_d_starPrimitiveExtension (η σ : NonemptySimplex K)
    (hησ : η.val ⊆ σ.val) (p : V) (hp : p ∈ η.val) (m : ℕ)
    (z : Cochain K (m + 1) G) (hz : coboundary K (m + 1) z = 0) :
    restrictCochain K (m + 1) σ (coboundary K m (starPrimitiveExtension K η p hp m z)) =
      restrictCochain K (m + 1) σ z := by
  rw [← restrictSimplex_restrictStar K η σ hησ,
    restrictStar_d_starPrimitiveExtension K η p hp m z hz,
    restrictSimplex_restrictStar]

end OpenDisk.StarLocality
