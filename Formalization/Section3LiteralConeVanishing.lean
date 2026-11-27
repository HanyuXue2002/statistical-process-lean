import Formalization.Section3ConeVanishing
import Formalization.Section3SimplicialConeModel
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.Order.WithBot

set_option linter.style.header false

/-!
# Section 3: the final `T'` statement for the literal cone

`Section3SimplicialConeModel` constructs the literal cone on vertices
`Option V` and states the global `tau` and `T` conclusions.  The remaining
primitive quotient conclusion is the direct specialization of the abstract
`IsConeAt` theorem through the Section 2 equivalence `T ≃ T'`.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- Order the new apex below every old vertex, matching the literal cone
model and the paper's orientation convention. -/
local instance literalConeOptionLinearOrder : LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- Representative form of `T'(C_v M)=0` for the literal simplicial cone. -/
theorem simplicialConeTPrime_eq_zero
    (M : AbstractSimplicialComplex V) (n : ℕ)
    (x : TPrime
      (facetRestrictionData (G := G) (simplicialCone M) n)) :
    x = 0 :=
  isConeAtTPrime_eq_zero (G := G) (simplicialCone M)
    (simplicialCone_isConeAt M) n x

/-- Typeclass form of `T'(C_v M)=0`. -/
theorem simplicialConeTPrime_subsingleton
    (M : AbstractSimplicialComplex V) (n : ℕ) :
    Subsingleton
      (TPrime (facetRestrictionData (G := G) (simplicialCone M) n)) :=
  isConeAtTPrime_subsingleton (G := G) (simplicialCone M)
    (simplicialCone_isConeAt M) n

end GeneralSphereT.SimplicialCochain
