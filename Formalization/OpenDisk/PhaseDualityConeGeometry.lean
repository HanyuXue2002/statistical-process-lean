import Formalization.OpenDisk.PhaseDualitySimplicialContraction
import Formalization.Section4LiteralConeSSetContraction

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Actual cone and double-cone geometric instances

The literal ordered cone carries the concrete cylinder deformation
contraction used by the general theorem.  A double cone over a cone is
also proved to be a cone at the original base apex, so its closed local
phase tables admit the required curvature decomposition.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.PhaseDuality

universe u
variable {V : Type u} [LinearOrder V]

local instance (priority := 10000) coneGeometryOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance
local instance (priority := 10000) coneGeometryOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance
local instance (priority := 10000) coneGeometryOptionOrder : LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance
local instance (priority := 10001) coneGeometryOptionOptionLE : LE (Option (Option V)) :=
  @WithBot.instLE (Option V) inferInstance
local instance (priority := 10001) coneGeometryOptionOptionLT : LT (Option (Option V)) :=
  @WithBot.instLT (Option V) inferInstance
local instance (priority := 10001) coneGeometryOptionOptionOrder :
    LinearOrder (Option (Option V)) := @WithBot.linearOrder (Option V) inferInstance

variable (K : AbstractSimplicialComplex V)

/-- The actual literal-cone cylinder homotopy is fixed on its apex. -/
def literalConeSimplicialContraction :
    SimplicialContraction (orderedComplexBasepointSubcomplex (simplicialCone K) none) where
  retraction := SSet.const
    ⟨literalConeApex K, SSet.Subcomplex.mem_ofSimplex_obj (literalConeApex K)⟩
  homotopy :=
    { h := literalConeCylinderMap K
      h₀ := by
        change SSet.ι₀ ≫ literalConeCylinderMap K = SSet.const _ ≫ _
        rw [SSet.const_comp]
        exact ι₀_literalConeCylinderMap K
      h₁ := ι₁_literalConeCylinderMap K
      rel := (literalConeContraction K).rel }
  fixed := by
    change (orderedComplexBasepointSubcomplex (simplicialCone K) none).ι ▷ Δ[1] ≫
      literalConeCylinderMap K =
        fst (orderedComplexBasepointSubcomplex (simplicialCone K) none).toSSet Δ[1] ≫
          (orderedComplexBasepointSubcomplex (simplicialCone K) none).ι
    rw [show (orderedComplexBasepointSubcomplex (simplicialCone K) none).ι =
      SSet.const (literalConeApex K) from SSet.Subcomplex.ofSimplex_ι _]
    ext Δ x
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    change (if SSet.stdSimplex.asOrderHom x.2 i = 0 then none else none) = none
    simp

theorem coneBaseVertices_insert_some (s : Finset (Option V)) (b : V) :
    coneBaseVertices (insert (some b) s) = insert b (coneBaseVertices s) := by
  ext x
  simp only [mem_coneBaseVertices, Finset.mem_insert, Option.some.injEq]

/-- Coning preserves an existing cone vertex in the embedded base. -/
theorem simplicialCone_isConeAt_base {b : V} (hb : IsConeAt K b) :
    IsConeAt (simplicialCone K) (some b) := by
  intro s
  have hs := s.2
  change insert (some b) s.1 ∈ simplicialCone K
  rw [mem_simplicialCone] at hs ⊢
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  rw [coneBaseVertices_insert_some]
  right
  rcases hs.2 with hzero | hface
  · rw [hzero]
    exact K.singleton_mem b
  · exact hb ⟨_, hface⟩

/-- A suspension/double-cone boundary of a cone is still a cone at the
original base apex.  The two suspension vertices remain distinct. -/
theorem doubleConeBoundary_isConeAt_base [Fintype V] {b : V} (hb : IsConeAt K b) :
    IsConeAt (doubleConeBoundary K) (some (some b)) := by
  intro s
  have hs := s.2
  change insert (some (some b)) s.1 ∈ doubleConeBoundary K
  rw [mem_doubleConeBoundary] at hs ⊢
  refine ⟨simplicialCone_isConeAt_base (simplicialCone K)
    (simplicialCone_isConeAt_base K hb) ⟨_, hs.1⟩, ?_⟩
  simpa only [Finset.mem_insert, Option.some.injEq, reduceCtorEq, false_or] using hs.2

variable [Fintype V] {G : Type u} [AddCommGroup G]

local instance : Fintype (NonemptySimplex (doubleConeBoundary K)) := Fintype.ofFinite _
local instance faceOrder (n : ℕ) : LinearOrder (Simplex (doubleConeBoundary K) n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- Concrete constructive-disk instance needed by the response argument:
the double cone over any cone has no closed-SPT obstruction. -/
theorem doubleCone_closedSPT_mem_facetCurvature_of_base_cone {b : V}
    (hb : IsConeAt K b) (n : ℕ)
    (φ : simplicialClosedSPT (G := G) (doubleConeBoundary K) n) :
    φ ∈ simplicialFacetCurvaturePhases (G := G) (doubleConeBoundary K) n :=
  simplicialClosedSPT_mem_facetCurvature_of_cone (doubleConeBoundary K) n
    (doubleConeBoundary_isConeAt_base K hb) φ

end OpenDisk.PhaseDuality
