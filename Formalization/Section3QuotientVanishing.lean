import Formalization.IteratedLocality

set_option linter.style.header false

/-!
# Section 3: quotient-level vanishing

The cone argument is carried out on representatives: it proves that every
element of the physical numerator `E_inv` lies in the identity denominator
`E_id`.  This file records the short final passage from that inclusion to the
literal quotient `T = E_inv / E_id`.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

omit [LinearOrder ι] in
/-- Representative form of quotient vanishing: if every invariant path is
an identity, then every class in `T` is zero. -/
theorem physicalQuotient_eq_zero_of_invariant_le_identity
    (hvanish : physicalInvariantPaths L ≤ physicalIdentityPaths L)
    (x : PhysicalQuotient L) :
    x = 0 := by
  refine Submodule.Quotient.induction_on
    (p := physicalIdentityPathsInInvariantPaths L) x ?_
  intro e
  apply (Submodule.Quotient.mk_eq_zero
    (physicalIdentityPathsInInvariantPaths L)).2
  exact hvanish e.2

omit [LinearOrder ι] in
/-- Typeclass form of the same statement. -/
theorem physicalQuotient_subsingleton_of_invariant_le_identity
    (hvanish : physicalInvariantPaths L ≤ physicalIdentityPaths L) :
    Subsingleton (PhysicalQuotient L) :=
  ⟨fun x y =>
    (physicalQuotient_eq_zero_of_invariant_le_identity L hvanish x).trans
      (physicalQuotient_eq_zero_of_invariant_le_identity L hvanish y).symm⟩

end GeneralSphereT.PathAlgebra
