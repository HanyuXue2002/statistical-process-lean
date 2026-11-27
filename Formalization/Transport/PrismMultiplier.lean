import Formalization.Transport.ConePrism
import Formalization.Transport.PrismNormalization
import Formalization.Transport.PrismLocality
import Formalization.Transport.NormalizedTables
import Formalization.Transport.Simplicial

noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra OpenDisk.PhaseDuality
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance : Fintype (Simplex X d) := Fintype.ofFinite _

abbrev State := LinearMap.range (coboundary (G:=G) X q)
def liftState (a : State (G:=G) X q) := (facetCoboundary_surjective X q a).choose
theorem liftState_spec (a : State (G:=G) X q) : coboundary X q (liftState X q a)=a.val :=
  congrArg Subtype.val (facetCoboundary_surjective X q a).choose_spec

private def part (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ) (σ : Simplex X d)
    (x : Triangle (Cochain X q G) (State (G:=G) X q)) : Phase :=
  let v := liftState X q x.2.2
  coeff σ • facetValue X q d ω σ v (v+x.2.1) (v+x.2.1+x.1)

private theorem physical_sum (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ)
    (t s : Cochain X q G) (a : State (G:=G) X q) :
    physicalPrism X q d ω coeff t s a = ∑ σ, part X q d ω coeff σ (t,s,a) := by
  unfold physicalPrism affineMultiplier orientedFacets
  simp only [map_sum,map_smul,triangle,extend_gen,part,facetValue,smul_neg,Finset.sum_neg_distrib]
  rfl

theorem physicalPrism_localTable (ω : EM G (q+1) (d+2) → Phase) (hn : NormalizedOnEM ω) (coeff : Simplex X d → ℤ) :
    ∃ g, ∀ x : Triangle (Cochain X q G) (State (G:=G) X q), physicalPrism X q d ω coeff x.1 x.2.1 x.2.2 =
      evaluate g (triangleRead (topFacetData (G:=G) X d q) x) := by
  classical
  let L := topFacetData (G:=G) X d q
  let P := fun (x : Triangle (Cochain X q G) (State (G:=G) X q)) => physicalPrism X q d ω coeff x.1 x.2.1 x.2.2
  let R := fun σ (x : Triangle (Cochain X q G) (State (G:=G) X q)) =>
    (L.primitiveRes σ x.1,L.primitiveRes σ x.2.1,L.physicalRes σ x.2.2)
  let B := part X q d ω coeff
  have eq (σ : Simplex X d) (x y) (h : R σ x=R σ y) : B σ x=B σ y := by
    apply congrArg (coeff σ • ·)
    apply facetValue_physical
    · exact congrArg (fun z => z.2.1) h
    · exact congrArg Prod.fst h
    · rw [liftState_spec,liftState_spec]
      exact congrArg (fun z => z.2.2) h
  let f := fun σ t s a => if h : ∃ x, R σ x=(t,s,a) then B σ h.choose else 0
  apply normalized_two L P _ _ f
  · intro t s a
    change physicalPrism X q d ω coeff t s a = _
    rw [physical_sum]
    apply Finset.sum_congr rfl
    intro σ _
    have h : ∃ x, R σ x=R σ (t,s,a) := ⟨_,rfl⟩
    change B σ (t,s,a) = if he : ∃ x, R σ x=R σ (t,s,a) then B σ he.choose else 0
    rw [dif_pos h]
    exact (eq σ h.choose (t,s,a) h.choose_spec).symm
  · intro s a
    change physicalPrism _ _ _ _ _ 0 s a=0
    rw [physical_sum]
    apply Finset.sum_eq_zero
    intro σ _
    simp only [part,facetValue,add_zero]
    rw [pullCochain_degenerate _ (affineField_normalized X) ω hn (triangle_repeated_right _ _ _),neg_zero,smul_zero]
  · intro t a
    change physicalPrism _ _ _ _ _ t 0 a=0
    rw [physical_sum]
    apply Finset.sum_eq_zero
    intro σ _
    simp only [part,facetValue,add_zero]
    rw [pullCochain_degenerate _ (affineField_normalized X) ω hn (triangle_repeated_left _ _ _),neg_zero,smul_zero]

/-- Formula (2.8), with its given orientation and sign, satisfies all three
transport axioms on a spatial cycle whose closed moves extend across its cone. -/
def physicalPrismMultiplier (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (ω : EM G (q+1) (d+2) → Phase) (hc : ClosedOnEM ω) (hn : NormalizedOnEM ω)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    SimplicialMultiplier (G:=G) X d q where
  value x := physicalPrism X q d ω coeff x.1 x.2.1 x.2.2
  localTable := physicalPrism_localTable X q d ω hn coeff
  assoc := physicalPrism_assoc X q d ω coeff hc hz
  zz := fun s t a hs ht => physicalPrism_zz X q d b hred ω hc coeff hz s t a
    (congrArg Subtype.val hs) (congrArg Subtype.val ht)

end GeneralSphereT.Transport.Prism
