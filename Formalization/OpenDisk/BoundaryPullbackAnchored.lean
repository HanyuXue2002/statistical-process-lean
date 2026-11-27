import Formalization.OpenDisk.BoundaryPullbackLocality

/-!
# Boundary-only phases have no anchored interaction involving an interior coordinate

This proves the immediate first part of the interior-vertex branch of the
report's final window discussion.  It applies to the actual simplicial
restriction, without assuming that the boundary function itself is local.
-/

noncomputable section
namespace OpenDisk.BoundaryPullbackLocality
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

variable {V W G P : Type*} [LinearOrder V] [LinearOrder W]
  [Fintype V] [Fintype W] [AddCommGroup G] [AddCommGroup P]
  {K : AbstractSimplicialComplex V} {M : AbstractSimplicialComplex W}

local instance anchoredBoundaryOrder (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearOrder (Simplex K n) := by classical exact linearOrderOfSTO WellOrderingRel
local instance anchoredBulkOrder (M : AbstractSimplicialComplex W) (n : ℕ) :
    LinearOrder (Simplex M n) := by classical exact linearOrderOfSTO WellOrderingRel

theorem pullback_image_local (F : OrderedSimplicialMap K M) (n : ℕ)
    (f : Cochain K n G → P) :
    AnchoredLocal (fun _ : Unit => Set.range (F.mapSimplex (n := n)))
      (fun c => f (F.pullback n c)) := by
  have hf : AnchoredLocal (fun _ : Unit => (Set.univ : Set (Simplex K n))) f := by
    intro c hc
    exact (hc () (fun _ _ => Set.mem_univ _)).elim
  have hp := ConePhaseLocalLift.affine_pullback_local
    (fun _ : Unit => (Set.univ : Set (Simplex K n)))
    (fun _ : Unit => Set.range (F.mapSimplex (n := n))) (F.pullbackAddHom n) 0 hf
    (fun _ η hη g => ?_)
  · simpa only [zero_add,OrderedSimplicialMap.pullback,AddMonoidHom.coe_toIntLinearMap] using hp
  · ext τ
    change Finsupp.single η g (F.mapSimplex τ.val) = 0
    apply Finsupp.single_eq_of_ne
    intro heq
    exact hη ⟨τ.val,heq⟩

/-- Every anchored interaction containing a genuine interior cochain coordinate
vanishes for a phase that only depends on boundary restriction. In degree zero
this includes every actual triangle incident to an interior vertex. -/
theorem pullback_anchoredTable_zero_of_interior
    (F : OrderedSimplicialMap K M) (n : ℕ) (f : Cochain K n G → P)
    (s : Finset (Simplex M n)) (c : Cochain M n G) {η : Simplex M n}
    (hηs : η ∈ s) (hη : η ∉ Set.range (F.mapSimplex (n := n))) :
    anchoredTable (fun c => f (F.pullback n c)) s c = 0 := by
  classical
  by_cases hs : s ⊆ c.support
  · rw [anchoredTable_eq_coordinate _ s c hs]
    apply pullback_image_local F n f
    intro u hu
    apply hη
    apply hu η
    rw [support_coordinateTruncation c hs]
    exact hηs
  · obtain ⟨j,hjs,hjc⟩ := Finset.not_subset.mp hs
    exact anchoredTable_zero_coordinate _ s c hjs (Finsupp.notMem_support_iff.mp hjc)

end OpenDisk.BoundaryPullbackLocality
