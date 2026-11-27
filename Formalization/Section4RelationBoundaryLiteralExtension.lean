import Formalization.Section4ExtraDegeneracyLiteralDescent
import Formalization.Section4RelationBoundaryNativeNullhomotopy

set_option linter.style.header false

/-!
# Section 4: literal-cone extension of a relation boundary

The standard relation boundary takes values in the reduced-free Dold--Kan
disk.  The extra-degeneracy descent theorem therefore upgrades its native
relative nullhomotopy to an actual extension across the literal `Option`
cone.  This is the form of (4.21) needed by the algebraic null subgroup.
-/

noncomputable section

open CategoryTheory Opposite Simplicial

namespace GeneralSphereT.StandardModels

open GeneralSphereT.SimplicialCochain
open GeneralSphereT.Section4
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.Section4.ExtraDegeneracyLiteralDescent
open DoldKanDiskContraction

universe u

variable {V : Type u} [LinearOrder V] [Fintype V]
variable (M : AbstractSimplicialComplex V)
variable (P : (orderedComplexSSet M).Subcomplex)

/-- The primitive boundary of any relative family of standard relation
paths extends over the literal simplicial cone and remains zero on the cone
over `P`. -/
def standardRelationBoundaryLiteralExtension
    (b : V) (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P
      (simplicialRelationPath (d G (q + 1)))) :
    LiteralRelativeExtension M P (reducedFree (L G (q + 1)))
      (relationBoundaryRelativeMap P (d G (q + 1)) f) :=
  standardDiskReducedFreeExtraDegeneracyLiteralExtension M P b G q
    (relationBoundaryRelativeMap P (d G (q + 1)) f)

end GeneralSphereT.StandardModels
