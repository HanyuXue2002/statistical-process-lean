import Formalization.OpenDisk.BulkExactSequence
import Formalization.OpenDisk.BoundaryPullbackLocality
import Formalization.Section4PointedConePairCohomologyShift

/-!
# Response on actual simplicial bulk and boundary cochains

Restriction is the literal pullback along an ordered simplicial embedding.
Ordinary extension is constructed by zero extension. Closed extension is
constructed from reduced cochain exactness: subtract the basepoint constant
in degree zero, or extend a primitive and differentiate in positive degree.
Thus no extension or locality property is postulated by the response theorem.
The remaining geometric hypothesis is the explicitly named reduced-cohomology
vanishing condition, not a claimed theorem for arbitrary topological balls.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace OpenDisk.SimplicialBulkResponse
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

variable {V W G P : Type*} [LinearOrder V] [LinearOrder W]
  [Fintype V] [Fintype W] [AddCommGroup G] [AddCommGroup P]
  {K : AbstractSimplicialComplex V} {M : AbstractSimplicialComplex W}

local instance faceOrder (L : AbstractSimplicialComplex V) (n : ℕ) :
    LinearOrder (Simplex L n) := by classical exact linearOrderOfSTO WellOrderingRel
local instance bulkFaceOrder (L : AbstractSimplicialComplex W) (n : ℕ) :
    LinearOrder (Simplex L n) := by classical exact linearOrderOfSTO WellOrderingRel

theorem pullback_surjective (F : OrderedSimplicialMap K M) (n : ℕ) :
    Function.Surjective (F.pullbackAddHom (G := G) n) :=
  fun c => ⟨F.extendCochainByZero n c, F.pullback_extendCochainByZero n c⟩

theorem pullback_closed (F : OrderedSimplicialMap K M) (n : ℕ)
    (z : (coboundaryToRange (G := G) M n).ker) :
    coboundaryToRange K n (F.pullbackAddHom n z.val) = 0 := by
  apply Subtype.ext
  have hz : coboundary M n z.val = 0 := congrArg Subtype.val z.property
  have hn := DFunLike.congr_fun (F.pullback_coboundary (G := G) n) z.val
  change coboundary K n (F.pullback n z.val) = 0
  change F.pullback (n + 1) (coboundary M n z.val) =
    coboundary K n (F.pullback n z.val) at hn
  rw [← hn, hz, map_zero]

def system (F : OrderedSimplicialMap K M) (n : ℕ) :
    BulkPhase.System (Cochain M n G) (Cochain K n G) :=
  cochainBulkSystem (coboundaryToRange K n) (F.pullbackAddHom n)
    (coboundaryToRange M n).ker (pullback_closed F n)

/-- Degree-zero reduced exactness says precisely that a closed table is constant. -/
theorem closed_zero_eq_constant (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) K b 0)
    (z : Cochain K 0 G) (hz : coboundary K 0 z = 0) :
    z = constantCochain K (z (basepointSimplex K b)) := by
  let z' : BasedZeroCochain (G := G) K b :=
    ⟨z - constantCochain K (z (basepointSimplex K b)), by
      change z (basepointSimplex K b) - constantCochain K _ (basepointSimplex K b) = 0
      simp⟩
  have hk : z' ∈ LinearMap.ker (basedZeroCoboundary (G := G) K b) := by
    change coboundary K 0 (z - constantCochain K (z (basepointSimplex K b))) = 0
    exact (coboundary_sub_constantCochain K z (z (basepointSimplex K b))).trans hz
  change LinearMap.ker (basedZeroCoboundary (G := G) K b) = ⊥ at hred
  rw [hred] at hk
  have heq : z' = 0 := hk
  have hc : z - constantCochain K (z (basepointSimplex K b)) = 0 :=
    congrArg Subtype.val heq
  exact sub_eq_zero.mp hc

/-- Closed boundary cochains are actually extended; no chosen lift is assumed. -/
theorem closedRestriction_surjective (F : OrderedSimplicialMap K M) (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) K b n) :
    Function.Surjective (system (G := G) F n).closedRestriction := by
  intro z
  have hz : coboundary K n z.val = 0 := congrArg Subtype.val z.property
  cases n with
  | zero =>
      let y : (coboundaryToRange (G := G) M 0).ker :=
        ⟨constantCochain M (z.val (basepointSimplex K b)), by
          apply Subtype.ext; exact coboundary_constantCochain M _⟩
      refine ⟨y, Subtype.ext ?_⟩
      change F.pullback 0 y.val = z.val
      rw [closed_zero_eq_constant b hred z.val hz]
      ext σ
      rfl
  | succ m =>
      change LinearMap.range (coboundary (G := G) K m) =
        LinearMap.ker (coboundary (G := G) K (m + 1)) at hred
      have hm : z.val ∈ LinearMap.range (coboundary (G := G) K m) := by
        rw [hred]
        exact hz
      obtain ⟨u, hu⟩ := hm
      let y : (coboundaryToRange (G := G) M (m + 1)).ker :=
        ⟨coboundary M m (F.extendCochainByZero m u), by
          apply Subtype.ext; exact coboundary_coboundary M m _⟩
      refine ⟨y, Subtype.ext ?_⟩
      change F.pullback (m + 1) (coboundary M m (F.extendCochainByZero m u)) = z.val
      have hn := DFunLike.congr_fun (F.pullback_coboundary (G := G) m)
        (F.extendCochainByZero m u)
      change F.pullback (m + 1) (coboundary M m (F.extendCochainByZero m u)) =
        coboundary K m (F.pullback m (F.extendCochainByZero m u)) at hn
      rw [hn, F.pullback_extendCochainByZero, hu]

abbrev Admissible (F : OrderedSimplicialMap K M) (n : ℕ) :=
  BulkExactSequence.admissible (facesIn K n) (coboundaryToRange (G := G) K n)
    (F.pullbackAddHom n) (coboundaryToRange M n).ker (pullback_closed F n)
    (localFunctionSubgroup (G := G) (facesIn M n) P)

def response (F : OrderedSimplicialMap K M) (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) K b n) :
    Admissible (G := G) (P := P) F n →+
      localSymmetries (facesIn K n) (coboundaryToRange (G := G) K n) (P := P) :=
  BulkExactSequence.response _ _ _ _ _ _ (pullback_surjective F n)
    (closedRestriction_surjective F b n hred)

theorem continuous_response [TopologicalSpace P] [IsTopologicalAddGroup P]
    (F : OrderedSimplicialMap K M) (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) K b n) :
    Continuous (response (G := G) (P := P) F b n hred) :=
  BulkExactSequence.continuous_response _ _ _ _ _ _ (pullback_surjective F n)
    (closedRestriction_surjective F b n hred)

theorem response_eq_zero_iff (F : OrderedSimplicialMap K M) (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) K b n) (φ : Admissible (G := G) (P := P) F n) :
    response F b n hred φ = 0 ↔
      BulkPhase.ClosedInvariant (coboundaryToRange M n).ker φ.val :=
  BulkExactSequence.response_eq_zero_iff _ _ _ _ _ _ (pullback_surjective F n)
    (closedRestriction_surjective F b n hred) φ

/-- The genuine local pullback discharges the locality premise of the bulk kernel formula. -/
theorem response_local_iff_sum (F : OrderedSimplicialMap K M) (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) K b n) (φ : Admissible (G := G) (P := P) F n) :
    letI : Nonempty (NonemptySimplex K) := ⟨coneApexSimplex K b⟩
    response F b n hred φ ∈ (localDerivative (P := P) (facesIn K n)
      (coboundaryToRange K n)).range ↔
      φ.val ∈ BulkExactSequence.closedLocal (coboundaryToRange M n).ker
        (localFunctionSubgroup (G := G) (facesIn M n) P) ⊔
        (localFunctionSubgroup (G := G) (facesIn K n) P).map
          (BulkExactSequence.pullbackHom (F.pullbackAddHom n)) := by
  letI : Nonempty (NonemptySimplex K) := ⟨coneApexSimplex K b⟩
  exact BulkExactSequence.response_local_iff_sum _ _ _ _ _ _
    (pullback_surjective F n) (closedRestriction_surjective F b n hred)
    (fun γ => BoundaryPullbackLocality.pullback_local F n γ.property) φ

end OpenDisk.SimplicialBulkResponse
