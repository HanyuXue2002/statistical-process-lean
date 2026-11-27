import Formalization.Section4ReducedFreeHomologyShift
import Formalization.OpenDisk.PhaseDuality
import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-! Actual circle-valued cohomology of the reduced free chains of K(G,q).
The coefficient functor is additive Hom into the divisible real circle. -/
noncomputable section
open CategoryTheory GeneralSphereT.StandardModels OpenDisk.PhaseDuality
namespace GeneralSphereT.Transport

abbrev phaseDual := preadditiveYonedaObj (AddCommGrpCat.of Phase)

abbrev phaseCohomology (A : SimplicialObject AddCommGrpCat.{0}) (n : ℕ) :=
  (((AlgebraicTopology.AlternatingFaceMapComplex.obj (reducedFree A)).sc n).op.map phaseDual).homology

/-- Universal coefficients, with the same integral homology model used in the
sphere calculations and without a freeness or finite-generation assumption. -/
def phaseCohomologyIso (A : SimplicialObject AddCommGrpCat.{0}) (n : ℕ) :
    phaseCohomology A n ≅ phaseDual.obj (Opposite.op (ReducedIntegralHomology A n)) :=
  let S := (AlgebraicTopology.AlternatingFaceMapComplex.obj (reducedFree A)).sc n
  S.op.mapHomologyIso phaseDual ≪≫ phaseDual.mapIso S.homologyOpIso

/-- The cohomological endpoint of the standard fibre homotopy shift. -/
def standardFiberPhaseCohomologyIso (G : AddCommGrpCat.{0}) (q d : ℕ) :
    phaseCohomology (K G (q+1)) (d+2) ≅
      phaseDual.obj (Opposite.op (SimplicialAbelianHomotopy (F G (q+1)) (d+1))) :=
  phaseCohomologyIso _ _ ≪≫ phaseDual.mapIso (standardFiberHomotopyReducedHomologyIso G q (d+1)).op

end GeneralSphereT.Transport

