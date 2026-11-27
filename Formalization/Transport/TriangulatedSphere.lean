import Formalization.Transport.SpatialHomologyCriterion
import Formalization.Transport.SpatialPairChains
import Formalization.Transport.OrientedSpherePrism
import Formalization.Transport.SphereRealizationHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! The geometric input is a homeomorphism from the realization of the
triangulation to the unit sphere. The facet coefficients record its orientation.
The relative cone sequence shifts positive homology by one. A unit coefficient
on a single facet makes the signed fundamental cycle primitive. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial AlgebraicTopology OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain SpatialPair
open DifferentialGeometry.LocalDegree DifferentialGeometry.Homology
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
local instance finalSphereLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance finalSphereLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance finalSphereOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V)
local instance finalSphereFacetFintype (k : ℕ) : Fintype (Simplex X k) := Fintype.ofFinite _
private abbrev CY := orderedComplexSSet (simplicialCone X)

variable (d : ℕ)
variable (realize : SSet.toTop.obj (orderedComplexSSet X) ≃ₜ
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)

private abbrev S := sequence (simplicialCone X) (literalConeBottomMap X)
private def shiftIso (n : ℕ) : (coneRelative X).homology (n+2) ≅ (orderedComplexSSet X).homology Z (n+1) :=
  (sequence_exact (simplicialCone X) (literalConeBottomMap X)).δIso (n+2) (n+1) (by simp)
    (cone_vanish X _ (by omega)) (cone_vanish X _ (by omega))

include realize in
private theorem low_vanish (hd : 0<d) (i : ℕ) (hi : i≤1) : IsZero ((coneRelative X).homology i) := by
  have := cone_aug X
  have := bottom_aug X d realize hd
  have : IsIso (homologyMap (S X).f 0) := by
    change IsIso (SSet.homologyMap (literalConeBottomMap X) Z 0)
    let j := literalConeBottomMap X
    have : IsIso (SSet.homologyMap j Z 0 ≫ (CY X).homology₀ε Z) := by
      rw [DifferentialGeometry.SSet.homologyMap_homology₀ε]
      infer_instance
    exact IsIso.of_isIso_comp_right (SSet.homologyMap j Z 0) ((CY X).homology₀ε Z)
  apply (exactAt_iff_isZero_homology _ _).mp
  refine (sequence_exact (simplicialCone X) (literalConeBottomMap X)).exactAt_X₃ i ?_ ?_
  · cases i with
    | zero => infer_instance
    | succ i => exact (cone_vanish X _ (by omega)).epi _
  · intro j hj
    have he : j=0 := by change j+1=i at hj; omega
    subst j
    infer_instance

include realize in
theorem orientation_of_triangulated_sphere (hd : 0<d) (hp : PureInDimension X d)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (σ : Simplex X d) (unit : coeff σ=1 ∨ coeff σ= -1) : IsRelativeHomologySphere X d coeff hz := by
  apply orientation_of_spatial_homology X d coeff hz hp σ unit
  · cases d with
    | zero => exact (Nat.lt_irrefl 0 hd).elim
    | succ n =>
      exact shiftIso X n ≪≫ positiveHomology X (n+1) realize n ≪≫
        (euclideanSphereTopReducedHomologyEquiv (n+1)).toIntLinearEquiv.toModuleIso
  · intro i hi
    by_cases small : i≤1
    · exact low_vanish X d realize hd i small
    · obtain ⟨n,rfl⟩ : ∃ n, i=n+2 := ⟨i-2,by omega⟩
      exact (isZero_euclideanSphere_reducedHomology Z d (n+1) (by omega)).of_iso
        (shiftIso X n ≪≫ positiveHomology X d realize n)

include realize in
theorem fundamentalClass_of_triangulation (b : V) (hd : 0<d) (hp : PureInDimension X d)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (signs : ∀ σ, coeff σ=1 ∨ coeff σ= -1) : IsRelativeHomologySphere X d coeff hz := by
  obtain ⟨μ,_⟩ := exists_maximalFacet_superset X ⟨{b},X.singleton_mem b⟩
  let σ : Simplex X d := ⟨μ.val.val,μ.val.property,hp μ⟩
  exact orientation_of_triangulated_sphere X d realize hd hp coeff hz σ (signs σ)

include realize in
/-- For any oriented pure triangulation of the geometric sphere, Eq. (2.8)
itself is an additive isomorphism on the vacuum orbit. The paper degree is
`q + 1`, so `q < d` expresses the full range from 1 through d. -/
def triangulatedSphereTriangleIso (b : V) (q : ℕ) (hq : q<d) (hp : PureInDimension X d)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (signs : ∀ σ, coeff σ=1 ∨ coeff σ= -1) :
    NormalizedEMCohomology G (q+1) d ≃+ TopMultiplierClasses (G:=G) X d q :=
  orientedTriangleIso X q d b hp hq coeff hz
    (fundamentalClass_of_triangulation X d realize b (by omega) hp coeff hz signs)

@[simp] theorem triangulatedSphereTriangleIso_mk (b : V) (q : ℕ) (hq : q<d) (hp : PureInDimension X d)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (signs : ∀ σ, coeff σ=1 ∨ coeff σ= -1) (ω : NormalizedCocycle G (q+1) d)
    (hc : ReducedCohomologyZeroAt (G:=G) X b q) :
    triangulatedSphereTriangleIso X d realize b q hq hp coeff hz signs (Quotient.mk _ ω)=Quotient.mk _
      (physicalPrismMultiplier X q d b hc ω.val ω.property.1 ω.property.2 coeff hz) := rfl

/-- On cocycles the representative has exactly the phase table of Eq. (2.8). -/
theorem triangulatedSphereTriangleIso_representative (b : V) (q : ℕ) (hq : q<d) (hp : PureInDimension X d)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (signs : ∀ σ, coeff σ=1 ∨ coeff σ= -1) (ω : NormalizedCocycle G (q+1) d) :
    ∃ m : SimplicialMultiplier (G:=G) X d q,
      triangulatedSphereTriangleIso X d realize b q hq hp coeff hz signs (Quotient.mk _ ω)=Quotient.mk _ m ∧
        ∀ t s a, m.value (t,s,a)=physicalPrism X q d ω.val coeff t s a := by
  have hs := fundamentalClass_of_triangulation X d realize b (by omega) hp coeff hz signs
  have hc := reducedExact_of_orientation (G:=G) X d coeff hz hs b q hq
  exact ⟨physicalPrismMultiplier X q d b hc ω.val ω.property.1 ω.property.2 coeff hz,rfl,fun _ _ _ => rfl⟩

include realize in
theorem triangulatedSphere_integralPrism_bijective (b : V) (q : ℕ) (hq : q<d) (hp : PureInDimension X d)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (signs : ∀ σ, coeff σ=1 ∨ coeff σ= -1) (hc : ReducedCohomologyZeroAt (G:=G) X b q) :
    Function.Bijective (integralPrism X q d b hc coeff hz) :=
  (prism_bijective_iff_integral X q d b hc coeff hz).mp
    (triangulatedSphereTriangleIso X d realize b q hq hp coeff hz signs).bijective

/-- On the integral side the same formula sends a process to its measured EM chain. -/
def triangulatedSphereIntegralIso (b : V) (q : ℕ) (hq : q<d) (hp : PureInDimension X d)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (signs : ∀ σ, coeff σ=1 ∨ coeff σ= -1) :
    IntegralProcesses (topFacetData (G:=G) X d q) ≃ₗ[ℤ] CycleClasses (G:=G) (q+1) d :=
  let hs := fundamentalClass_of_triangulation X d realize b (by omega) hp coeff hz signs
  let hc := reducedExact_of_orientation (G:=G) X d coeff hz hs b q hq
  LinearEquiv.ofBijective (integralPrism X q d b hc coeff hz)
    (triangulatedSphere_integralPrism_bijective X d realize b q hq hp coeff hz signs hc)

end GeneralSphereT.Transport.Prism
