import Formalization.Transport.PrismGauge

/-! The forward direction of the sphere assertion, on the normalized simplicial
cochain model: the map is the signed integral of the given representative. -/
noncomputable section
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality
variable {G : Type} [AddCommGroup G]

abbrev NormalizedCocycle (G : Type) [AddCommGroup G] (q d : ℕ) :=
  {ω : EM G q (d+2) → Phase // ClosedOnEM ω ∧ NormalizedOnEM ω}

def cocycleSetoid (G : Type) [AddCommGroup G] (q d : ℕ) : Setoid (NormalizedCocycle G q d) where
  r ω η := ∃ θ : EM G q (d+1) → Phase, NormalizedOnEM θ ∧ η.val-ω.val=phaseDifferential θ
  iseqv := {
    refl := by
      intro ω
      exact ⟨0,fun _ _ => rfl,by ext; simp [phaseDifferential]⟩
    symm := by
      rintro ω η ⟨θ,hn,he⟩
      refine ⟨-θ,fun i x => by simp [hn i x],?_⟩
      calc
        ω.val-η.val = -(η.val-ω.val) := by abel
        _ = phaseDifferential (-θ) := by rw [he]; ext x; simp [phaseDifferential,Finset.sum_neg_distrib]
    trans := by
      rintro ω η ξ ⟨θ,hθ,eθ⟩ ⟨φ,hφ,eφ⟩
      refine ⟨θ+φ,fun i x => by simp [hθ i x,hφ i x],?_⟩
      calc
        ξ.val-ω.val = (η.val-ω.val)+(ξ.val-η.val) := by abel
        _ = phaseDifferential (θ+φ) := by
          rw [eθ,eφ]
          ext x
          simp [phaseDifferential,smul_add,Finset.sum_add_distrib]
  }

/-- Normalized simplicial circle-valued cohomology in degree d+2, written in
coordinates directly on the simplices of the Eilenberg--Mac Lane space. -/
abbrev NormalizedEMCohomology (G : Type) [AddCommGroup G] (q d : ℕ) := Quotient (cocycleSetoid G q d)

variable {V : Type} [LinearOrder V] [Fintype V] (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance : Fintype (Simplex X d) := Fintype.ofFinite _

/-- The actual map in the claim of classification. Its well-definedness includes
simultaneous, normalized, top-facet locality for both the multiplier and its gauge. -/
def prismClass (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    NormalizedEMCohomology G (q+1) d → Quotient (localEquivalence (topFacetData (G:=G) X d q)) :=
  Quotient.lift (fun ω : NormalizedCocycle G (q+1) d => Quotient.mk _
    (physicalPrismMultiplier X q d b hred ω.val ω.property.1 ω.property.2 coeff hz)) (by
      rintro ω η ⟨θ,hn,he⟩
      apply Quotient.sound
      apply (classCharacter_eq_iff _ _ _).mpr
      exact prism_equivalent_of_coboundary X q d ω.val η.val θ hn he coeff hz)

@[simp] theorem prismClass_mk (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) (ω : NormalizedCocycle G (q+1) d) :
    prismClass X q d b hred coeff hz (Quotient.mk _ ω) = Quotient.mk _
      (physicalPrismMultiplier X q d b hred ω.val ω.property.1 ω.property.2 coeff hz) := rfl

def zeroCocycle : NormalizedCocycle G (q+1) d :=
  ⟨0,fun _ => by simp,fun _ _ => rfl⟩

theorem prism_zero (coeff : Simplex X d → ℤ) (t s : Cochain X q G) (a : State (G:=G) X q) :
    physicalPrism X q d 0 coeff t s a=0 := by
  let η : EM G (q+1) (d+2) → Phase := 0
  simpa only [sub_self] using physicalPrism_sub X q d η η coeff t s a

/-- The vanishing cohomology class strictly multiplies after one choice of local basis. -/
theorem strictifies_of_cohomology_zero (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (ω : NormalizedCocycle G (q+1) d)
    (h : (Quotient.mk _ ω : NormalizedEMCohomology G (q+1) d)=Quotient.mk _ (zeroCocycle q d)) :
    Equivalent (topFacetData (G:=G) X d q) (fun x => physicalPrism X q d ω.val coeff x.1 x.2.1 x.2.2) (fun _ => 0) := by
  have E := congrArg (prismClass X q d b hred coeff hz) h
  rw [prismClass_mk,prismClass_mk] at E
  have e := (classCharacter_eq_iff _ _ _).mp (Quotient.exact E)
  change Equivalent (topFacetData (G:=G) X d q) (fun x => physicalPrism X q d ω.val coeff x.1 x.2.1 x.2.2)
    (fun x => physicalPrism X q d 0 coeff x.1 x.2.1 x.2.2) at e
  simp only [prism_zero] at e
  exact e

end GeneralSphereT.Transport.Prism
