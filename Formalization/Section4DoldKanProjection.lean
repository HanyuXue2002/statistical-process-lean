import Formalization.Section4DoldKanModels

set_option linter.style.header false

/-!
# Section 4: components of the Dold--Kan disk projection

The defining chain map from the two-term disk to the one-term sphere is the
identity in the top degree and zero elsewhere.  These component formulas are
kept separate so that the explicit Gamma-coordinate comparison can use them
without unfolding Mathlib's `mkHomToSingle` constructor repeatedly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category

namespace GeneralSphereT.StandardModels

universe u

/-- In the top degree, the disk-to-sphere map is the canonical identity
between the two displayed copies of `G`. -/
theorem diskToSphere_top_component (G : AddCommGrpCat.{u}) (k : ℕ) :
    (diskToSphere G (k + 1)).f (k + 1) ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) (k + 1) G).hom =
      (HomologicalComplex.doubleXIso₀ (𝟙 G)
        (ComplexShape.down_mk (k + 1) k rfl)).hom := by
  change (diskToSphereSucc G k).f (k + 1) ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (k + 1) G).hom = _
  unfold diskToSphereSucc
  rw [HomologicalComplex.mkHomToSingle_f]
  simp

end GeneralSphereT.StandardModels
