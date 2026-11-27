import Formalization.OpenDisk.BulkRealizations
import Formalization.OpenDisk.ConePhaseLocalLift
import Formalization.SimplicialCochainPullback

/-!
# Actual simplicial boundary pullback preserves locality

The restriction is the literal cochain pullback of an injective ordered
simplicial map. Every boundary simplex maps into an actual bulk simplex, so
boundary-local phases pull back to bulk-local phases. This supplies the locality
part of the report's same-statistics realization corollary, separately from its
already proved closed-invariance calculation.
-/

noncomputable section

namespace OpenDisk.BoundaryPullbackLocality

open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

variable {V W G P : Type*} [LinearOrder V] [LinearOrder W]
  [Fintype V] [Fintype W] [AddCommGroup G] [AddCommGroup P]
  {K : AbstractSimplicialComplex V} {M : AbstractSimplicialComplex W}

local instance boundaryFaceOrder (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearOrder (Simplex K n) := by classical exact linearOrderOfSTO WellOrderingRel
local instance bulkFaceOrder (M : AbstractSimplicialComplex W) (n : ℕ) :
    LinearOrder (Simplex M n) := by classical exact linearOrderOfSTO WellOrderingRel

def mapFacet (F : OrderedSimplicialMap K M) (σ : {s : Finset V // s ∈ K}) :
    {s : Finset W // s ∈ M} :=
  ⟨σ.val.map F.toOrderEmbedding.toEmbedding, F.map_mem σ.property⟩

theorem pullback_local (F : OrderedSimplicialMap K M) (n : ℕ)
    {f : Cochain K n G → P} (hf : AnchoredLocal (facesIn K n) f) :
    AnchoredLocal (facesIn M n) (fun c => f (F.pullback n c)) := by
  have hp : AnchoredLocal (fun σ => facesIn M n (mapFacet F σ))
      (fun c => f (0 + F.pullbackAddHom n c)) := by
    apply ConePhaseLocalLift.affine_pullback_local (facesIn K n)
      (fun σ => facesIn M n (mapFacet F σ)) (F.pullbackAddHom n) 0 hf
    intro σ τ hτ g
    ext η
    change (Finsupp.single τ g) (F.mapSimplex η.val) = 0
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hτ
    change τ.val ⊆ σ.val.map F.toOrderEmbedding.toEmbedding
    rw [← heq]
    exact Finset.map_subset_map.mpr η.property
  simp only [zero_add] at hp
  intro c hc
  apply hp c
  intro σ hσ
  exact hc (mapFacet F σ) hσ

theorem pullback_differenceLocal (F : OrderedSimplicialMap K M) (n : ℕ)
    {f : Cochain K n G → P} (hf : DifferenceLocal (facesIn K n) f) :
    DifferenceLocal (facesIn M n) (fun c => f (F.pullback n c)) := by
  rw [differenceLocal_iff_anchoredLocal] at hf ⊢
  exact pullback_local F n hf

variable {B : Type*} [AddCommGroup B] [Nonempty {s : Finset V // s ∈ K}]

/-- The same-statistics correction is an actual local closed bulk phase.
No geometric locality of the boundary pullback is supplied as an assumption. -/
theorem same_statistics_local_closed_correction
    (F : OrderedSimplicialMap K M) (n : ℕ)
    (d : Cochain K n G →+ B) (rep : B → Cochain K n G)
    (hrep : ∀ a, d (rep a) = a)
    (Z : AddSubgroup (Cochain M n G)) (hz : ∀ z : Z, d (F.pullback n z) = 0)
    (φ₀ φ₁ : Cochain M n G → P)
    (hφ₀ : AnchoredLocal (facesIn M n) φ₀) (hφ₁ : AnchoredLocal (facesIn M n) φ₁)
    (x y : LocalJointPhase (facesIn K n) d P)
    (hθ : forgetExcitation d elementaryStep (markedFunctionSubgroup (facesIn K n)) rep x =
      forgetExcitation d elementaryStep (markedFunctionSubgroup (facesIn K n)) rep y)
    (h₀ : BulkPhase.HasResponse (cochainBulkSystem d (F.pullbackAddHom n) Z hz) φ₀
      (fun z v => phaseDerivative d x.val.1 z v))
    (h₁ : BulkPhase.HasResponse (cochainBulkSystem d (F.pullbackAddHom n) Z hz) φ₁
      (fun z v => phaseDerivative d y.val.1 z v)) :
    let k := BulkPhase.realizationCorrection (F.pullbackAddHom n) φ₀ φ₁ (y.val.1 - x.val.1)
    AnchoredLocal (facesIn M n) k ∧ BulkPhase.ClosedInvariant Z k := by
  have h := same_statistics_bulk_correction (facesIn K n) d rep hrep
    (F.pullbackAddHom n) Z hz φ₀ φ₁ x y hθ h₀ h₁
  refine ⟨?_, h.2⟩
  have hγ := pullback_local F n ((differenceLocal_iff_anchoredLocal _ _).1 h.1)
  exact (localFunctionSubgroup (G := G) (facesIn M n) P).add_mem
    ((localFunctionSubgroup (G := G) (facesIn M n) P).sub_mem hφ₁ hφ₀) hγ

end OpenDisk.BoundaryPullbackLocality
