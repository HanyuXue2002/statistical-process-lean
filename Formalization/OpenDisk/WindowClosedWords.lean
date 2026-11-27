import Formalization.OpenDisk.StarMarkedPhases
import Formalization.OpenDisk.NormalFormTableLocality
import Formalization.OpenDisk.ConePhaseLocalLift

/-!
# Closed hopping words in the conditional window argument

The path module retains actual inverse edges and same-coordinate fusion
defects.  A table is evaluated on translated paths, hence gives the complete
configuration-dependent phase of a word.  We use the proved explicit elementary
two-cell filling rather than discarding same-carrier closed operations.
-/

noncomputable section
open scoped BigOperators

namespace OpenDisk.Window
open GeneralSphereT.PathAlgebra

variable {ι G P B Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup P] [AddCommGroup B]

def pathPhase (T : ElementaryLabel ι G → Configuration ι G → P) :
    Path (Configuration ι G) (Configuration ι G) →ₗ[ℤ] (Configuration ι G → P) where
  toFun p c := operationCharacterOfTable T (baseTranslation c p)
  map_add' p q := by ext c; simp
  map_smul' a p := by ext c; simp

@[simp] theorem pathPhase_edge (T : ElementaryLabel ι G → Configuration ι G → P)
    (s b c : Configuration ι G) :
    pathPhase T (edge s b) c = extendElementaryTable T s (b + c) := by
  simp [pathPhase]

theorem pathPhase_difference (d : Configuration ι G →+ B)
    (β : Configuration ι G → P) (T : ElementaryLabel ι G → Configuration ι G → P)
    (hT : ∀ e, Matching d β (T e) (elementaryStep e))
    {p : Path (Configuration ι G) (Configuration ι G)}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := Configuration ι G))
    (z : d.ker) (c : Configuration ι G) :
    difference (pathPhase T p) z c =
      phasePairing (fun b => difference β z (b + c)) (primitiveBoundary _ p) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, g, b, hg, rfl⟩ := hp
      let e : ElementaryLabel ι G := ⟨(i, g), hg⟩
      have hs : Finsupp.single i g = elementaryStep e := rfl
      simp only [difference, pathPhase_edge, hs, extendElementaryTable_step]
      have he := hT e z (b + c)
      simpa [difference, primitiveBoundary, boundary_edge, bracket,
        add_assoc, add_left_comm, add_comm] using he
  | zero => simp [difference]
  | add p q hp hq ihp ihq =>
      simp only [map_add, difference_add, ihp, ihq]
  | smul a p hp ih =>
      simp only [map_smul, RingHom.id_apply, difference, Pi.smul_apply,
        smul_sub] at ih ⊢
      simpa only [smul_sub] using congrArg (fun x => a • x) ih

theorem pathPhase_closed (d : Configuration ι G →+ B)
    (β : Configuration ι G → P) (T : ElementaryLabel ι G → Configuration ι G → P)
    (hT : ∀ e, Matching d β (T e) (elementaryStep e))
    {p : Path (Configuration ι G) (Configuration ι G)}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := Configuration ι G))
    (hc : primitiveBoundary _ p = 0) : phaseDerivative d (pathPhase T p) = 0 := by
  ext z c
  change difference (pathPhase T p) z c = 0
  rw [pathPhase_difference d β T hT hp, hc, map_zero]

/-- Translation of the input changes facet tables but does not change locality. -/
theorem translate_local (facets : Facet → Set ι) {f : Configuration ι G → P}
    (hf : AnchoredLocal facets f) (b : Configuration ι G) :
    AnchoredLocal facets (fun c => f (b + c)) := by
  apply ConePhaseLocalLift.affine_pullback_local facets facets
    (AddMonoidHom.id (Configuration ι G)) b hf
  intro ρ i hi g
  exact coordinateRestriction_single_not_mem _ hi g

theorem single_operation_marked (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → P)
    (hT : ∀ e, MarkedLocal facets {e.val.1} (T e)) (i : ι) (g : G) :
    MarkedLocal facets {i} (extendElementaryTable T (Finsupp.single i g)) := by
  by_cases hg : g = 0
  · subst g
    rw [Finsupp.single_zero, extendElementaryTable_zero]
    exact (localFunctionSubgroup (G := G) (markedFacets facets {i}) P).zero_mem
  · exact (show extendElementaryTable T (elementaryStep ⟨(i,g),hg⟩) = T ⟨(i,g),hg⟩
      from extendElementaryTable_step _ _) ▸ hT ⟨(i,g),hg⟩

theorem marked_local {facets : Facet → Set ι} {marks : Finset ι}
    {f : Configuration ι G → P} (hf : MarkedLocal facets marks f) :
    AnchoredLocal facets f := by
  intro c hc
  apply hf c
  intro ρ hρ
  exact hc ρ.val hρ

theorem difference_local (facets : Facet → Set ι) {f : Configuration ι G → P}
    (hf : AnchoredLocal facets f) (s : Configuration ι G) :
    AnchoredLocal facets (phaseDifference s f) := by
  have ht := translate_local facets hf s
  have heq : phaseDifference s f = (fun c => f (s + c)) - f := by
    funext c; simp [phaseDifference, add_comm]
  rw [heq]
  exact (localFunctionSubgroup (G := G) facets P).sub_mem ht hf

theorem derivative_marked (facets : Facet → Set ι) {f : Configuration ι G → P}
    (hf : AnchoredLocal facets f) (i : ι) (g : G) :
    MarkedLocal facets {i} (phaseDifference (Finsupp.single i g) f) := by
  by_cases hg : g = 0
  · subst g
    have heq : phaseDifference (Finsupp.single i 0) f = 0 := by
      funext c; simp [phaseDifference]
    rw [heq]
    exact (localFunctionSubgroup (G := G) (markedFacets facets {i}) P).zero_mem
  · exact ((differenceLocal_iff_anchoredLocal facets f).2 hf).marked_difference i g hg

def cellCarrier : PrimitiveCellType ι G → ι
  | .transverseSquare i _ _ _ _ => i
  | .sameCoordinateTriangle i _ _ => i

def cellPhase (T : ElementaryLabel ι G → Configuration ι G → P)
    (τ : PrimitiveCellType ι G) (c : Configuration ι G) : P :=
  operationCharacterOfTable T (primitiveCellBoundaryGenerator (τ,c))

theorem pathPhase_cell (T : ElementaryLabel ι G → Configuration ι G → P)
    (τ : PrimitiveCellType ι G) (b : Configuration ι G) :
    pathPhase T (primitiveCellBoundaryGenerator (τ,b)) = fun c => cellPhase T τ (b+c) := by
  funext c
  cases τ <;> simp [pathPhase, cellPhase, primitiveCellBoundaryGenerator,
    baseTranslation_square, baseTranslation_triangle]

theorem cellPhase_marked (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → P)
    (hT : ∀ e, MarkedLocal facets {e.val.1} (T e)) (τ : PrimitiveCellType ι G) :
    MarkedLocal facets {cellCarrier τ} (cellPhase T τ) := by
  cases τ with
  | transverseSquare i j hij g h =>
      have heq : cellPhase T (.transverseSquare i j hij g h) =
          phaseDifference (Finsupp.single i g) (extendElementaryTable T (Finsupp.single j h)) -
          phaseDifference (Finsupp.single j h) (extendElementaryTable T (Finsupp.single i g)) := by
        funext c
        simpa [cellPhase, primitiveCellBoundaryGenerator, operationPhase, phaseDifference] using
          operationCharacter_square (operationCharacterOfTable T)
            (Finsupp.single i g) (Finsupp.single j h) c
      rw [heq]
      exact (localFunctionSubgroup (G := G) (markedFacets facets {i}) P).sub_mem
        (derivative_marked facets (marked_local (single_operation_marked facets T hT j h)) i g)
        (difference_local (markedFacets facets {i}) (single_operation_marked facets T hT i g) _)
  | sameCoordinateTriangle i g h =>
      have heq : cellPhase T (.sameCoordinateTriangle i g h) =
          extendElementaryTable T (Finsupp.single i g) +
          (fun c => extendElementaryTable T (Finsupp.single i h) (Finsupp.single i g + c)) -
          extendElementaryTable T (Finsupp.single i (g+h)) := by
        funext c
        simp [cellPhase, primitiveCellBoundaryGenerator, triangle, Finsupp.single_add,
          add_comm]
      rw [heq]
      exact (localFunctionSubgroup (G := G) (markedFacets facets {i}) P).sub_mem
        ((localFunctionSubgroup (G := G) (markedFacets facets {i}) P).add_mem
          (single_operation_marked facets T hT i g)
          (translate_local _ (single_operation_marked facets T hT i h) _))
        (single_operation_marked facets T hT i (g+h))

theorem single_edge_elementary (i : ι) (g : G) (b : Configuration ι G) :
    edge (Finsupp.single i g) b ∈
      elementaryPaths (ι := ι) (G := G) (X := Configuration ι G) := by
  by_cases hg : g = 0
  · simp [hg]
  · exact elementaryEdge_mem i hg b

theorem cell_boundary_elementary (τ : PrimitiveCellType ι G) (b : Configuration ι G) :
    primitiveCellBoundaryGenerator (τ,b) ∈
      elementaryPaths (ι := ι) (G := G) (X := Configuration ι G) := by
  let E := elementaryPaths (ι := ι) (G := G) (X := Configuration ι G)
  cases τ with
  | transverseSquare i j hij g h =>
      exact E.sub_mem (E.sub_mem (E.add_mem (single_edge_elementary i g b)
        (single_edge_elementary j h _)) (single_edge_elementary i g _))
        (single_edge_elementary j h b)
  | sameCoordinateTriangle i g h =>
      change edge (Finsupp.single i g) b + edge (Finsupp.single i h) _ -
        edge (Finsupp.single i g + Finsupp.single i h) b ∈ E
      rw [← Finsupp.single_add]
      exact E.sub_mem (E.add_mem (single_edge_elementary i g b)
        (single_edge_elementary i h _)) (single_edge_elementary i (g+h) b)

theorem cellPhase_closed (d : Configuration ι G →+ B) (β : Configuration ι G → P)
    (T : ElementaryLabel ι G → Configuration ι G → P)
    (hT : ∀ e, Matching d β (T e) (elementaryStep e)) (τ : PrimitiveCellType ι G) :
    phaseDerivative d (cellPhase T τ) = 0 := by
  have heq : pathPhase T (primitiveCellBoundaryGenerator (τ,0)) = cellPhase T τ := by
    rw [pathPhase_cell]; simp
  rw [← heq]
  exact pathPhase_closed d β T hT (cell_boundary_elementary τ 0)
    (primitiveBoundary_primitiveCellBoundaryGenerator _)

section Simplicial

open GeneralSphereT.SimplicialCochain StarLocality

variable {V : Type*} [LinearOrder V] [Fintype V]
  (K : AbstractSimplicialComplex V) (n : ℕ)

local instance windowFaceOrder : LinearOrder (Simplex K n) := by
  classical exact linearOrderOfSTO WellOrderingRel
local instance windowFacetFintype : Fintype (NonemptySimplex K) := Fintype.ofFinite _
local instance windowCarrierFintype (η : Simplex K n) : Fintype (CarrierFacets K n η) :=
  Fintype.ofFinite _

/-- Finite sums of actual simplex-curvature functions, with constants retained. -/
def curvatureLocalSubgroup : AddSubgroup (Cochain K n G → P) :=
  AddSubgroup.closure {f | ∃ (σ : NonemptySimplex K)
    (g : Configuration (facesIn K (n+1) σ) G → P),
      f = fun c => g (restrictCochain K (n+1) σ (coboundary K n c))}

theorem curvature_term_mem (σ : NonemptySimplex K)
    (g : Configuration (facesIn K (n+1) σ) G → P) :
    (fun c => g (restrictCochain K (n+1) σ (coboundary K n c))) ∈
      curvatureLocalSubgroup (G := G) K n :=
  AddSubgroup.subset_closure ⟨σ,g,rfl⟩

theorem translated_marked_closed_mem (η : Simplex K n) (f : Cochain K n G → P)
    (hf : MarkedLocal (facesIn K n) {η} f)
    (hc : phaseDerivative (coboundaryToRange K n) f = 0) (b : Cochain K n G) :
    (fun c => f (b+c)) ∈ curvatureLocalSubgroup (G := G) K n := by
  obtain ⟨k,rfl⟩ := exists_globalMarkedCurvatureSum K n η f hf hc
  have heq : (fun c => globalMarkedCurvatureSum K n η k (b+c)) =
      ∑ ρ : CarrierFacets K n η,
        (fun c => k ρ (restrictCochain K (n+1) ρ.val (coboundary K n b) +
          restrictCochain K (n+1) ρ.val (coboundary K n c))) := by
    funext c
    simp only [globalMarkedCurvatureSum, map_add, Finset.sum_apply]
  rw [heq]
  apply AddSubgroup.sum_mem
  intro ρ hρ
  exact curvature_term_mem K n ρ.val
    (fun a => k ρ (restrictCochain K (n+1) ρ.val (coboundary K n b) + a))

theorem cell_pathPhase_curvatureLocal
    (β : Cochain K n G → P) (T : ElementaryLabel (Simplex K n) G → Cochain K n G → P)
    (hmarked : ∀ e, MarkedLocal (facesIn K n) {e.val.1} (T e))
    (hmatch : ∀ e, Matching (coboundaryToRange K n) β (T e) (elementaryStep e))
    (τ : PrimitiveCellType (Simplex K n) G) (b : Cochain K n G) :
    pathPhase T (primitiveCellBoundaryGenerator (τ,b)) ∈
      curvatureLocalSubgroup (G := G) K n := by
  rw [pathPhase_cell]
  exact translated_marked_closed_mem K n (cellCarrier τ) (cellPhase T τ)
    (cellPhase_marked _ T hmarked τ) (cellPhase_closed _ β T hmatch τ) b

/-- The complete phase of every closed elementary operation chain is a sum of
simplex-curvature functions.  Both same-coordinate triangles and transverse
squares occur in the explicit filling, so no inverse or fusion phase is lost. -/
theorem closed_pathPhase_curvatureLocal
    (β : Cochain K n G → P) (T : ElementaryLabel (Simplex K n) G → Cochain K n G → P)
    (hmarked : ∀ e, MarkedLocal (facesIn K n) {e.val.1} (T e))
    (hmatch : ∀ e, Matching (coboundaryToRange K n) β (T e) (elementaryStep e))
    {p : Path (Cochain K n G) (Cochain K n G)}
    (hp : p ∈ elementaryPaths (ι := Simplex K n) (G := G) (X := Cochain K n G))
    (hc : primitiveBoundary _ p = 0) :
    pathPhase T p ∈ curvatureLocalSubgroup (G := G) K n := by
  have hred : primitiveReducedBoundary _ p = 0 := Subtype.ext hc
  have hfill := primitiveCellBoundary₂_explicitFillingMap_of_mem hp
  simp only [hred,map_zero,sub_zero] at hfill
  rw [← hfill]
  generalize explicitFillingMap p = z
  induction z using Finsupp.induction with
  | zero => simp
  | single_add cell a z _ _ ih =>
      rw [map_add,map_add]
      apply AddSubgroup.add_mem _ _ ih
      rw [primitiveCellBoundary₂_single_data,map_smul]
      exact AddSubgroup.zsmul_mem _
        (cell_pathPhase_curvatureLocal K n β T hmarked hmatch cell.1 cell.2) a

end Simplicial

end OpenDisk.Window
