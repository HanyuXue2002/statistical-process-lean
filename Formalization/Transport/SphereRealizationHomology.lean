import Formalization.Section4NormalizedCochainBridge
import Formalization.Section4LiteralConeSSetContraction
import DifferentialGeometry.Topology.SimplicialSet.FiniteRealizationHomology
import DifferentialGeometry.Topology.LocalDegree.SphereVanishing
import DifferentialGeometry.Topology.LocalDegree.SphereGenerator
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! The geometric input is a homeomorphism from the realization of the
triangulation to the unit sphere. The facet coefficients record its orientation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial AlgebraicTopology
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain
private abbrev Z := ModuleCat.of ℤ ℤ
open DifferentialGeometry.LocalDegree DifferentialGeometry.Homology
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
local instance topoLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance topoLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance topoOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V)
private abbrev Y := orderedComplexSSet X
private abbrev CY := orderedComplexSSet (simplicialCone X)

private instance : (Y X).Finite := by
  letI : (Y X).HasDimensionLT (Fintype.card V) := ⟨fun n hn => by
    ext x
    simp only [SSet.mem_degenerate_iff_notMem_nonDegenerate,Set.top_eq_univ,Set.mem_univ,iff_true]
    intro hx
    have h := Fintype.card_le_of_injective x.val (mem_orderedComplexSSet_nonDegenerate_iff_injective X x |>.mp hx)
    change Fintype.card (Fin (n+1))≤Fintype.card V at h
    rw [Fintype.card_fin] at h
    omega⟩
  exact SSet.finite_of_hasDimensionLT (Y X) (Fintype.card V) (fun k _ => Finite.of_equiv (Simplex X k) (nonDegenerateSimplexEquiv X k).symm)

private def collapse : CY X ⟶ (Δ[0] : SSet.{0}) :=
  SSet.const (SSet.stdSimplex.const 0 0 (op ⦋0⦌))

private def conePointIso (n : ℕ) : (CY X).homology Z n ≅ (Δ[0] : SSet.{0}).homology Z n where
  hom := SSet.homologyMap (collapse X) Z n
  inv := SSet.homologyMap (SSet.const (literalConeApex X) : (Δ[0] : SSet.{0}) ⟶ _) Z n
  hom_inv_id := by
    rw [← SSet.homologyMap_comp,SSet.comp_const,← SSet.homologyMap_id]
    exact (literalConeContraction X).congr_homologyMap Z n
  inv_hom_id := by
    rw [← SSet.homologyMap_comp,← SSet.homologyMap_id]
    apply congrArg (fun f => SSet.homologyMap f Z n)
    ext

omit [Fintype V] in
theorem cone_vanish (n : ℕ) (h : n≠0) : IsZero ((CY X).homology Z n) :=
  (DifferentialGeometry.SSet.isZero_homology_stdSimplex 0 n h Z).of_iso (conePointIso X n)

omit [Fintype V] in
theorem cone_aug : IsIso ((CY X).homology₀ε Z) := by
  letI := DifferentialGeometry.SSet.isConnected_stdSimplex.{0} 0
  letI : IsIso (SSet.homologyMap (collapse X) Z 0) := (conePointIso X 0).isIso_hom
  rw [← DifferentialGeometry.SSet.homologyMap_homology₀ε (collapse X) Z]
  infer_instance

variable (d : ℕ) (realize : SSet.toTop.obj (Y X) ≃ₜ EuclideanSphere d)

def positiveHomology (n : ℕ) :
    (Y X).homology Z (n+1) ≅ reducedSingularHomology Z (TopCat.of (EuclideanSphere d)) (n+1) :=
  DifferentialGeometry.SSet.realizationHomologyIso Z (Y X) (n+1) ≪≫
    ((singularHomologyFunctor (ModuleCat ℤ) (n+1)).obj Z).mapIso (TopCat.isoOfHomeo realize) ≪≫
    (reducedSingularHomologySuccIso Z _ n).symm

include realize in
theorem bottom_aug (hd : 0<d) : IsIso ((Y X).homology₀ε Z) := by
  haveI : PathConnectedSpace (EuclideanSphere d) := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_sphere
    · exact Module.one_lt_rank_of_one_lt_finrank (by simpa using hd)
    · norm_num
  letI : PathConnectedSpace (SSet.toTop.obj (Y X)) := realize.symm.pathConnectedSpace
  let u : Y X ⟶ TopCat.toSSet.obj (SSet.toTop.obj (Y X)) := sSetTopAdj.unit.app (Y X)
  letI : QuasiIso (DifferentialGeometry.SSet.realizationChainMap (Y X) Z) :=
    DifferentialGeometry.SSet.quasiIso_realizationChainMap_of_finite Z _
  letI : IsIso (SSet.homologyMap u Z 0) :=
    (isoOfQuasiIsoAt (DifferentialGeometry.SSet.realizationChainMap (Y X) Z) 0).isIso_hom
  have eq := DifferentialGeometry.SSet.homologyMap_homology₀ε u Z
  exact eq ▸ (inferInstance : IsIso (SSet.homologyMap u Z 0 ≫ (TopCat.toSSet.obj (SSet.toTop.obj (Y X))).homology₀ε Z))

end GeneralSphereT.Transport.Prism
