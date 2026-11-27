import Formalization.OpenDisk.PhaseDualityNative

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Closed local phases on a genuinely simplicially contracted source

A literal cylinder contraction onto the basepoint is geometric input,
independent of the coefficient group and of the phase tables.  Every based
map to a simplicial abelian group then has an actual native nullhomotopy.
The unconditional reverse cone criterion and the actual degree-zero exact
row imply `τ = 0`, hence every closed local phase is a facet-curvature sum.

This constructive form does not identify geometric realization
contractibility with a one-step simplicial contraction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain
open GeneralSphereT.Section4 GeneralSphereT.StandardModels
open GeneralSphereT.Section4.UnderlyingSSet GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

namespace OpenDisk.PhaseDuality

universe u

/-- A genuine simplicial deformation contraction onto a source subcomplex.
The data are a source retraction and a literal cylinder homotopy, fixed on
the subcomplex.  No assertion about target maps or phase groups occurs. -/
structure SimplicialContraction {X : SSet.{u}} (P : X.Subcomplex) where
  retraction : X ⟶ (P : SSet)
  homotopy : SSet.Homotopy (retraction ≫ P.ι) (𝟙 X)
  fixed : (P.ι ▷ Δ[1]) ≫ homotopy.h = fst (P : SSet) Δ[1] ≫ P.ι

variable {X : SSet.{u}} {P : X.Subcomplex}

/-- Compose the actual source contraction with a relative map. -/
def SimplicialContraction.nullhomotopy (E : SimplicialContraction P)
    (A : SimplicialObject AddCommGrpCat.{u}) (f : NativeRelativeMorphism P A) :
    SSet.RelativeMorphism.Homotopy (0 : NativeRelativeMorphism P A) f where
  h := E.homotopy.h ≫ f.map
  h₀ := by
    rw [← Category.assoc, E.homotopy.h₀, Category.assoc, f.comm,
      zeroBoundary_comp_inclusion]
    ext Δ x
    rfl
  h₁ := by rw [← Category.assoc, E.homotopy.h₁, Category.id_comp]
  rel := by
    rw [← Category.assoc, E.fixed, Category.assoc, f.comm]

theorem SimplicialContraction.mem_nativeNullMaps (E : SimplicialContraction P)
    (A : SimplicialObject AddCommGrpCat.{u}) (f : NativeRelativeMorphism P A) :
    f ∈ NativeNullMaps P A := by
  change f.homotopyClass = 0
  have h := (homotopyClass_eq_iff P A).mpr ⟨E.nullhomotopy A f⟩
  exact h.symm

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (b : V) (n : ℕ)

local instance : Fintype (NonemptySimplex K) := Fintype.ofFinite _
local instance : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- A literal based simplicial contraction kills the actual integral
obstruction group.  No reduced-cohomology assumption is needed. -/
theorem simplicialFullTau_eq_zero_of_contraction
    (E : SimplicialContraction (orderedComplexBasepointSubcomplex K b))
    (x : simplicialFullTau (G := G) K n) : x = 0 := by
  letI : Nonempty (NonemptySimplex K) := ⟨coneApexSimplex K b⟩
  let e := fullTauEquivExistingTau
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (facetRestrictionData (G := G) K n)
    (coboundaryToRange_surjective K n)
  apply e.map_eq_zero_iff.mp
  obtain ⟨f, hf⟩ := nativePointedObstruction_surjective (G := G) K b n (e x)
  have hnull := E.mem_nativeNullMaps (F (AddCommGrpCat.of G) (n + 1)) f
  have hrange := nativeNullMaps_le_range_basedRprimToNativePointedMap (G := G) K b n hnull
  have hzero := (exact_basedRprimToNativePointedMap_nativePointedObstruction
    (G := G) K b n f).mpr hrange
  exact hf.symm.trans hzero

/-- Constructive contractible-source form of Theorem 1.4(a), in the original
closed local phase-table model. -/
theorem simplicialClosedSPT_mem_facetCurvature_of_contraction
    (E : SimplicialContraction (orderedComplexBasepointSubcomplex K b))
    (φ : simplicialClosedSPT (G := G) K n) :
    φ ∈ simplicialFacetCurvaturePhases (G := G) K n := by
  change closedSPTRestriction _ _ _ _ φ = 0
  apply LinearMap.ext
  intro x
  have hx := simplicialFullTau_eq_zero_of_contraction K b n E x
  simp only [hx, map_zero, LinearMap.zero_apply]

/-- The resulting phase-table decomposition keeps the global phase. -/
theorem contracted_closed_phase_table_decomposition
    (E : SimplicialContraction (orderedComplexBasepointSubcomplex K b))
    (φ : simplicialClosedSPT (G := G) K n) :
    ∃ k : ∀ σ : NonemptySimplex K, Configuration (facesIn K (n + 1) σ) G → Phase,
      ∀ c, φ.1.1 c = ∑ σ, k σ (restrictCochain K (n + 1) σ (coboundary K n c)) := by
  classical
  exact (mem_facetCurvaturePhases_iff _ _ _ (coboundaryToRange_surjective K n) φ).mp
    (simplicialClosedSPT_mem_facetCurvature_of_contraction K b n E φ)

end OpenDisk.PhaseDuality
