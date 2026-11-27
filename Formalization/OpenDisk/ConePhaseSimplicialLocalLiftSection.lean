import Formalization.OpenDisk.ConePhaseSimplicialLocalLiftZero
import Formalization.OpenDisk.ConePhaseLocalLiftTopology

/-!
# A continuous additive selection of simplicial local lifts

The apex is the least vertex of the marked simplex and is fixed independently
of the phase table. In degree zero the primitive is evaluation at that vertex.
Thus the complete family of hopping lifts is an actual continuous additive map,
rather than a choice of witnesses depending on the symmetry table.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace OpenDisk.ConePhaseSimplicialLocalLift

open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open ConePhaseLocalLift StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]
variable (K : AbstractSimplicialComplex V)

local instance simplexOrderSection (n : ℕ) : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- Fix the local cochain contraction before supplying the symmetry table. -/
def simplicialLocalLiftHom (n : ℕ) (e : Simplex K n) (g : G) :
    SymmetryPhase (coboundaryToRange (G := G) K n) P →+ (Cochain K n G → P) := by
  cases n with
  | zero =>
      exact localLiftHom (coboundaryToRange K 0) (constantDifferential K)
        (vertexPrimitive K e) e g
  | succ m =>
      exact localLiftHom (coboundaryToRange K (m + 1)) (previousCoboundary K m)
        (starPrimitiveExtension K (forgetDimension K e) (simplexApex K e)
          (simplexApex_mem K e) m) e g

theorem simplicialLocalLiftHom_marked (n : ℕ) (e : Simplex K n) (g : G) (hg : g ≠ 0)
    (F : SymmetryPhase (coboundaryToRange (G := G) K n) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K n σ)
      (coboundaryToRange (G := G) K n) F) :
    MarkedLocal (fun σ : NonemptySimplex K => facesIn K n σ) {e}
      (simplicialLocalLiftHom K n e g F) := by
  cases n with
  | zero =>
      exact localLift_marked (coboundaryToRange K 0)
        (fun σ : NonemptySimplex K => facesIn K 0 σ) (fun _ => (Set.univ : Set Unit))
        (simplex_mem_some_facesIn K 0) (constantDifferential K)
        (fun _ _ hk _ => (hk (Set.mem_univ _)).elim) F hF (vertexPrimitive K e) e g hg
        (vertexPrimitive_capSection_invisible K e)
  | succ m =>
      exact localLift_marked _ _ _ (simplex_mem_some_facesIn K (m + 1))
        (previousCoboundary K m) (previousCoboundary_column K m) F hF
        (starPrimitiveExtension K (forgetDimension K e) (simplexApex K e)
          (simplexApex_mem K e) m) e g hg
        (starPrimitive_capSection_invisible K m e (simplexApex K e) (simplexApex_mem K e))

theorem simplicialLocalLiftHom_matches (n : ℕ) (e : Simplex K n) (g : G) (hg : g ≠ 0)
    (F : SymmetryPhase (coboundaryToRange (G := G) K n) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K n σ)
      (coboundaryToRange (G := G) K n) F)
    (z : (coboundaryToRange (G := G) K n).ker) (v : Cochain K n G) :
    difference (simplicialLocalLiftHom K n e g F) z v =
      difference (fun v => F z v) (Finsupp.single e g) v := by
  cases n with
  | zero =>
      exact localLift_matches (κ := Unit) (P := P) (coboundaryToRange K 0)
        (fun σ : NonemptySimplex K => facesIn K 0 σ) (fun _ => (Set.univ : Set Unit))
        (simplex_mem_some_facesIn K 0) (constantDifferential K)
        (fun _ _ hk _ => (hk (Set.mem_univ _)).elim) F hF (vertexPrimitive K e) e g hg
        (vertexPrimitive_contracts_closed K e) z v
  | succ m =>
      exact localLift_matches _ _ _ (simplex_mem_some_facesIn K (m + 1))
        (previousCoboundary K m) (previousCoboundary_column K m) F hF
        (starPrimitiveExtension K (forgetDimension K e) (simplexApex K e)
          (simplexApex_mem K e) m) e g hg
        (starPrimitive_contracts_closed K m e (simplexApex K e) (simplexApex_mem K e)) z v

theorem continuous_simplicialLocalLiftHom [TopologicalSpace P] [IsTopologicalAddGroup P]
    (n : ℕ) (e : Simplex K n) (g : G) :
    Continuous (simplicialLocalLiftHom (P := P) K n e g) := by
  cases n with
  | zero => exact continuous_localLiftHom _ _ _ _ _
  | succ m => exact continuous_localLiftHom _ _ _ _ _

/-- The full hopping family is selected by one continuous additive map. -/
def simplicialHoppingLiftHom (n : ℕ) :
    SymmetryPhase (coboundaryToRange (G := G) K n) P →+
      (ElementaryLabel (Simplex K n) G → Cochain K n G → P) where
  toFun F e := simplicialLocalLiftHom K n e.val.1 e.val.2 F
  map_zero' := by funext e; exact map_zero _
  map_add' F H := by funext e; exact map_add _ F H

theorem simplicialHoppingLift_marked (n : ℕ)
    (F : SymmetryPhase (coboundaryToRange (G := G) K n) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K n σ)
      (coboundaryToRange (G := G) K n) F)
    (e : ElementaryLabel (Simplex K n) G) :
    MarkedLocal (fun σ : NonemptySimplex K => facesIn K n σ) {e.val.1}
      (simplicialHoppingLiftHom K n F e) :=
  simplicialLocalLiftHom_marked K n e.val.1 e.val.2 e.property F hF

theorem simplicialHoppingLift_matches (n : ℕ)
    (F : SymmetryPhase (coboundaryToRange (G := G) K n) P)
    (hF : RestrictionSymmetryLocal (fun σ : NonemptySimplex K => facesIn K n σ)
      (coboundaryToRange (G := G) K n) F)
    (e : ElementaryLabel (Simplex K n) G)
    (z : (coboundaryToRange (G := G) K n).ker) (v : Cochain K n G) :
    difference (simplicialHoppingLiftHom K n F e) z v =
      difference (fun v => F z v) (elementaryStep e) v :=
  simplicialLocalLiftHom_matches K n e.val.1 e.val.2 e.property F hF z v

theorem continuous_simplicialHoppingLiftHom [TopologicalSpace P] [IsTopologicalAddGroup P]
    (n : ℕ) : Continuous (simplicialHoppingLiftHom (G := G) (P := P) K n) :=
  continuous_pi fun e => continuous_simplicialLocalLiftHom K n e.val.1 e.val.2

end OpenDisk.ConePhaseSimplicialLocalLift
