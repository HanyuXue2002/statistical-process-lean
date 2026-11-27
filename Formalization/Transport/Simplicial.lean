import Formalization.Transport.Presentation
import Formalization.Transport.WordSeparation
import Formalization.Transport.VacuumSplitting
import Formalization.SimplicialFacetData

/-! Multipliers on the vacuum orbit of an actual ordered simplicial complex.
Only simplices of the specified top dimension are used in the locality test. -/
noncomputable section
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (d n : ℕ)

def topFacetData : FacetRestrictionData
    (CAt := fun σ : Simplex K d => Configuration (facesIn K n ⟨σ.val,σ.property.1⟩) G)
    (BAt := fun σ : Simplex K d => Configuration (facesIn K (n+1) ⟨σ.val,σ.property.1⟩) G)
    (Facet := Simplex K d) (coboundaryToRange (G := G) K n) where
  primitiveRes σ := restrictCochain K n ⟨σ.val,σ.property.1⟩
  physicalRes σ := restrictCoboundary K n ⟨σ.val,σ.property.1⟩
  localD σ := (localCoboundary K n ⟨σ.val,σ.property.1⟩).toAddMonoidHom
  commutes σ := (facetRestrictionData (G := G) K n).commutes ⟨σ.val,σ.property.1⟩

local instance topFacetFintype : Fintype (Simplex K d) := Fintype.ofFinite _
local instance finiteCochain [Finite G] (m : ℕ) : Finite (Cochain K m G) :=
  Finite.of_equiv (Simplex K m → G) Finsupp.equivFunOnFinite.symm

abbrev SimplicialMultiplier := Multiplier (topFacetData (G := G) K d n)

def simplicialMultiplierClassification :=
  multiplierClassification (topFacetData (G := G) K d n)

/-- The finite family consists of single hopping words with their inverse steps
read at the forward source. A single family separates all local basis classes. -/
theorem simplicialFiniteSeparatingWords [Finite G] :
    ∃ words : Finset (Word (Cochain K n G)),
      (∀ w ∈ words, Statistical (L := topFacetData (G:=G) K d n) w) ∧
      ∀ c c' : SimplicialMultiplier (G:=G) K d n,
        Equivalent (topFacetData K d n) c.value c'.value ↔
        ∀ w ∈ words, (w.foldl (hop c 0) (0,0)).2 = (w.foldl (hop c' 0) (0,0)).2 :=
  finite_separating_words (facetCoboundary_surjective K n)

theorem simplicialVacuumSplitting (m : SimplicialMultiplier (G:=G) K d n) :
    ∃ h : Cochain K n G → LinearMap.range (coboundary (G:=G) K n) → Phase,
      ∀ t s a, m.value (t,s,a) =
        h s a + h t (a + coboundaryToRange K n s) - h (s+t) a :=
  exists_global_primitive m (facetCoboundary_surjective K n)

end GeneralSphereT.Transport

