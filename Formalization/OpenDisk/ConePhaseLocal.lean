import Formalization.OpenDisk.ConePhaseSimplicial

/-!
# Closed local phases on simplicial cones

This is the cone/closed-star case of the report's Theorem 1.4(a): a
closed-invariant sum of simplex-restriction phases is exactly a sum of
simplex-curvature phases. The proof uses the actual ordered cone contraction
and its compatibility with restriction to every simplex containing the apex.
It does not assert the corresponding theorem for arbitrary contractible
complexes.
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace OpenDisk.ConePhaseLocal

open scoped BigOperators
open GeneralSphereT.SimplicialCochain
open GeneralSphereT.PathAlgebra
open ConePhaseSimplicial

variable {V G P F : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P] [Fintype F]

variable (K : AbstractSimplicialComplex V)

/-- Literal simplex-restriction locality on a finite cover of the closed star. -/
def StarLocal (η : {s : Finset V // s ∈ K}) (σ : F → {s : Finset V // s ∈ K})
    (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ)
    (f : ClosedStarCochain K η n G → P) : Prop :=
  ∃ g : ∀ ρ, Configuration (facesIn K n (σ ρ)) G → P,
    ∀ c, f c = ∑ ρ, g ρ (restrictClosedStarToSimplex K η (σ ρ) (hησ ρ) n c)

/-- A sum of arbitrary local curvature tables; constant tables remain included. -/
def curvatureSum (η : {s : Finset V // s ∈ K}) (σ : F → {s : Finset V // s ∈ K})
    (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ)
    (k : ∀ ρ, Configuration (facesIn K (n + 1) (σ ρ)) G → P)
    (c : ClosedStarCochain K η n G) : P :=
  ∑ ρ, k ρ (restrictClosedStarToSimplex K η (σ ρ) (hησ ρ) (n + 1)
    (closedStarCoboundary K η n c))

/-- Restricting the closed-star differential is the ordinary local differential. -/
theorem restrictStar_coboundary (η σ : {s : Finset V // s ∈ K})
    (hησ : η.1 ⊆ σ.1) (n : ℕ) (c : ClosedStarCochain K η n G) :
    restrictClosedStarToSimplex K η σ hησ (n + 1) (closedStarCoboundary K η n c) =
      localCoboundary K n σ (restrictClosedStarToSimplex K η σ hησ n c) := by
  ext τ
  simp only [restrictClosedStarToSimplex_apply, closedStarCoboundary_apply,
    localCoboundary_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rfl

/-- Curvature sums are local phase tables in the original cochain coordinates. -/
theorem curvatureSum_local (η : {s : Finset V // s ∈ K})
    (σ : F → {s : Finset V // s ∈ K}) (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ)
    (k : ∀ ρ, Configuration (facesIn K (n + 1) (σ ρ)) G → P) :
    StarLocal K η σ hησ n (curvatureSum K η σ hησ n k) := by
  refine ⟨fun ρ a => k ρ (localCoboundary K n (σ ρ) a), fun c => ?_⟩
  unfold curvatureSum
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [restrictStar_coboundary]

/-- A curvature sum is invariant under every closed translation. -/
theorem curvatureSum_closed (η : {s : Finset V // s ∈ K})
    (σ : F → {s : Finset V // s ∈ K}) (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ)
    (k : ∀ ρ, Configuration (facesIn K (n + 1) (σ ρ)) G → P)
    (z : closedCochains (G := G) K η n) (c : ClosedStarCochain K η n G) :
    curvatureSum K η σ hησ n k (c + z) = curvatureSum K η σ hησ n k c := by
  have hz : closedStarCoboundary (G := G) K η n z.val = 0 := z.property
  simp only [curvatureSum, map_add, hz, add_zero]

/-- Every closed local phase has a concrete facet-curvature decomposition. -/
theorem exists_curvatureSum (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (σ : F → {s : Finset V // s ∈ K})
    (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ)
    {f : ClosedStarCochain K η n G → P} (hloc : StarLocal K η σ hησ n f)
    (hclosed : ∀ (z : closedCochains (G := G) K η n) c, f (c + z) = f c) :
    ∃ k, f = curvatureSum K η σ hησ n k := by
  obtain ⟨g, hg⟩ := hloc
  refine ⟨fun ρ a => g ρ (simplexConeHomotopy K η (σ ρ) (hησ ρ) p hp n a), ?_⟩
  funext c
  rw [(coneSplitting K η p hp n).invariant_eq_base hclosed c, hg]
  unfold curvatureSum
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply congrArg (g ρ)
  exact LinearMap.congr_fun
    (restrictClosedStarToSimplex_coneHomotopy K η (σ ρ) (hησ ρ) p hp n)
    (closedStarCoboundary K η n c)

/-- Exact full-table characterization on a cone, without quotienting constants. -/
theorem closed_local_iff_curvatureSum (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (σ : F → {s : Finset V // s ∈ K})
    (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ)
    (f : ClosedStarCochain K η n G → P) :
    (StarLocal K η σ hησ n f ∧
      ∀ (z : closedCochains (G := G) K η n) c, f (c + z) = f c) ↔
      ∃ k, f = curvatureSum K η σ hησ n k := by
  constructor
  · rintro ⟨hloc, hclosed⟩
    exact exists_curvatureSum K η p hp σ hησ n hloc hclosed
  · rintro ⟨k, rfl⟩
    exact ⟨curvatureSum_local K η σ hησ n k, curvatureSum_closed K η σ hησ n k⟩

section Topology

variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_curvatureSum (η : {s : Finset V // s ∈ K})
    (σ : F → {s : Finset V // s ∈ K}) (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ) :
    Continuous (curvatureSum (G := G) (P := P) K η σ hησ n) := by
  apply continuous_pi
  intro c
  unfold curvatureSum
  fun_prop

/-- In particular, the closed local full-phase space on a cone is path connected
for circle-valued phases. Constants are part of this connected space. -/
theorem closed_local_isPathConnected [PathConnectedSpace P]
    (η : {s : Finset V // s ∈ K}) (p : V) (hp : p ∈ η.1)
    (σ : F → {s : Finset V // s ∈ K}) (hησ : ∀ ρ, η.1 ⊆ (σ ρ).1) (n : ℕ) :
    IsPathConnected {f : ClosedStarCochain K η n G → P |
      StarLocal K η σ hησ n f ∧
        ∀ (z : closedCochains (G := G) K η n) c, f (c + z) = f c} := by
  have hset : {f : ClosedStarCochain K η n G → P |
      StarLocal K η σ hησ n f ∧
        ∀ (z : closedCochains (G := G) K η n) c, f (c + z) = f c} =
      Set.range (curvatureSum (G := G) (P := P) K η σ hησ n) := by
    ext f
    rw [Set.mem_setOf_eq, closed_local_iff_curvatureSum K η p hp σ hησ n f]
    exact ⟨fun ⟨k, h⟩ => ⟨k, h.symm⟩, fun ⟨k, h⟩ => ⟨k, h.symm⟩⟩
  rw [hset]
  exact isPathConnected_range (continuous_curvatureSum K η σ hησ n)

end Topology

end OpenDisk.ConePhaseLocal
