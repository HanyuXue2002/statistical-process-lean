import Formalization.Transport.Simplicial

/-! Every statistical word gives the same scalar on the entire vacuum orbit. -/
noncomputable section
namespace GeneralSphereT.Transport
open OpenDisk.PhaseDuality GeneralSphereT.PathAlgebra
variable {C B F : Type*} [AddCommGroup C] [AddCommGroup B] [Fintype F]
variable {S A : F → Type*} [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B} {L : FacetRestrictionData (Facet:=F) (CAt:=S) (BAt:=A) d}

private theorem triangle_shift (f : TwoSlot S A → Phase) (a : B) (x : Triangle C B) :
    evaluate f (triangleRead L (x.1,x.2.1,a+x.2.2)) =
    evaluate (fun k : TwoSlot S A => f ⟨k.1,k.2.1,k.2.2.1,L.physicalRes k.1 a+k.2.2.2⟩) (triangleRead L x) := by
  classical
  simp only [triangleRead,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

def shiftMultiplier (c : Multiplier L) (a : B) : Multiplier L where
  value := shiftTable a c.value
  localTable := by
    obtain ⟨f,hf⟩ := c.localTable
    exact ⟨_,fun x => (hf _).trans (triangle_shift (L:=L) f a x)⟩
  assoc := fun r t s b => by simpa only [shiftTable,add_assoc] using c.assoc r t s (a+b)
  zz := fun s t b hs ht => c.zz s t (a+b) hs ht

private theorem commutator_edge (c : Multiplier L) (r : C) :
    ∃ g : OneSlot S A → Phase, ∀ s a, c.value (s,r,a)-c.value (r,s,a)=evaluate g (edgeRead L s a) := by
  classical
  obtain ⟨f,hf⟩ := c.localTable
  let g := fun k : OneSlot S A => if L.primitiveRes k.1 r=0 then 0 else
    f ⟨k.1,k.2.1,L.primitiveRes k.1 r,k.2.2⟩-f ⟨k.1,L.primitiveRes k.1 r,k.2.1,k.2.2⟩
  refine ⟨g,fun s a => ?_⟩
  rw [hf,hf]
  simp only [triangleRead,edgeRead,map_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : L.primitiveRes i s=0 <;> by_cases hr : L.primitiveRes i r=0 <;> simp [g,hs,hr]

theorem equivalent_translate (c : Multiplier L) (r : C) :
    Equivalent L c.value (shiftMultiplier c (d r)).value := by
  obtain ⟨g,hg⟩ := commutator_edge c r
  refine ⟨g,fun t s a => ?_⟩
  change c.value (t,s,d r+a)-c.value (t,s,a)=_
  rw [add_comm (d r) a,c.translated,hg,hg,hg]

/-- A rephasing-invariant closed word acts by its vacuum phase in every source sector. -/
theorem statistical_source_independent (hd : Function.Surjective d) (w : Word C) (hw : Statistical (L:=L) w)
    (c : Multiplier L) (a : B) : (w.foldl (hop c a) (0,0)).2=(w.foldl (hop c 0) (0,0)).2 := by
  obtain ⟨r,rfl⟩ := hd a
  have h := hw.2 c (shiftMultiplier c (d r)) (equivalent_translate c r) 0
  have e : hop (shiftMultiplier c (d r)) 0 = hop c (d r) := by
    funext st step
    simp [hop,shiftMultiplier,shiftTable]
  rwa [e,eq_comm] at h

open GeneralSphereT.SimplicialCochain
local instance familyFacetFintype {V : Type} [LinearOrder V] [Fintype V] (X : AbstractSimplicialComplex V) (d : ℕ) : Fintype (Simplex X d) := Fintype.ofFinite _

/-- One finite family works on every chosen initial configuration and each
of its measured phases is independent of that choice. -/
theorem finite_statistics_on_vacuum_orbit {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G] [Finite G]
    (X : AbstractSimplicialComplex V) (d n : ℕ) :
    ∃ words : Finset (Word (Cochain X n G)),
      (∀ w ∈ words, Statistical (L:=topFacetData (G:=G) X d n) w) ∧
      (∀ w ∈ words, ∀ (m : SimplicialMultiplier (G:=G) X d n) a,
        (w.foldl (hop m a) (0,0)).2=(w.foldl (hop m 0) (0,0)).2) ∧
      ∀ (c c' : SimplicialMultiplier (G:=G) X d n) a, Equivalent (topFacetData X d n) c.value c'.value ↔
        ∀ w ∈ words, (w.foldl (hop c a) (0,0)).2=(w.foldl (hop c' a) (0,0)).2 := by
  obtain ⟨W,hW,hsep⟩ := simplicialFiniteSeparatingWords (G:=G) X d n
  have inv (w) (hw : w ∈ W) := statistical_source_independent (facetCoboundary_surjective X n) w (hW w hw)
  refine ⟨W,hW,inv,fun c c' a => ?_⟩
  rw [hsep]
  constructor <;> intro h w hw
  · rw [inv w hw c a,inv w hw c' a]; exact h w hw
  · rw [← inv w hw c a,← inv w hw c' a]; exact h w hw

end GeneralSphereT.Transport
