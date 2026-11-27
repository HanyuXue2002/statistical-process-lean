import Formalization.Transport.CycleFactor
import Formalization.Transport.PrimitiveRealization
import Formalization.Transport.Presentation

/-! The transport quotient and the strict primitive process group. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra GeneralSphereT.PathAlgebra.FacetRestrictionData OpenDisk.PhaseDuality
variable {I G B F : Type*} [LinearOrder I] [Fintype I] [AddCommGroup G] [AddCommGroup B]
variable [Fintype F] {facets : F → Set I}
variable {A : F → Type*} [∀ i, AddCommGroup (A i)]
variable {d : Configuration I G →+ B}
variable (L : FacetRestrictionData (Facet:=F) (CAt:=fun i => Configuration (facets i) G) (BAt:=A) d)
variable (hres : ∀ i, L.primitiveRes i = coordinateRestriction (facets i))
variable (D : RelativePrimitiveSectionData facets L)

def Represents (m : Multiplier L) (χ : TPrime L →ₗ[ℤ] Phase) :=
  ∃ h : Configuration I G → B → Phase, m.value = curvature (d:=d) h ∧
    ∀ z : Zprim L, χ ((BprimInZprim L).mkQ z) = evaluate (fun v => h v 0) z.val.val

private theorem zero_primitive {m : Multiplier L} {h : Configuration I G → B → Phase}
    (hm : m.value = curvature (d:=d) h) (a : B) : h 0 a = 0 := by
  have e := m.zero_left 0 a
  rw [hm] at e
  simpa [curvature] using e

include hres D in
theorem equivalent_of_represents {m m' : Multiplier L} {χ : TPrime L →ₗ[ℤ] Phase}
    (hm : Represents L m χ) (hm' : Represents L m' χ) : Equivalent L m.value m'.value := by
  classical
  obtain ⟨h,hh,hχ⟩ := hm
  obtain ⟨h',hh',hχ'⟩ := hm'
  let β := potentialCharacter (fun v => h' v 0) - potentialCharacter (fun v => h v 0)
  have hz (z : Zprim L) : β z.val = 0 := sub_eq_zero.mpr ((hχ' z).symm.trans (hχ z))
  obtain ⟨k,u,hu⟩ := cycle_factor L β hz
  have hv (v : Configuration I G) : h' v 0 - h v 0 = k (d v) + ∑ i, u i (L.primitiveRes i v) := by
    simpa [β,zero_primitive L hh 0,zero_primitive L hh' 0] using hu v
  obtain ⟨o,ho⟩ := vacuum_local L m
  obtain ⟨o',ho'⟩ := vacuum_local L m'
  let l (s : Configuration I G) (a : B) := h' s a - h s a - (k (a+d s)-k a)
  have l0 (a : B) : l 0 a = 0 := by simp [l,zero_primitive L hh,zero_primitive L hh']
  let f (i : F) (s v : Configuration (facets i) G) := o' i s v - o i s v + (u i (v+s)-u i v)
  have hl (s v : Configuration I G) : l s (d v) = ∑ i, f i (coordinateRestriction (facets i) s)
      (coordinateRestriction (facets i) v) := by
    have a := ho s v
    have b := ho' s v
    rw [hh] at a
    rw [hh'] at b
    have e := hv (v+s)
    have e₀ := hv v
    simp only [curvature,zero_add,hres,map_add] at a b e e₀
    simp only [f,l,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    linear_combination (norm := abel) b - a + e - e₀
  obtain ⟨g,hg⟩ := joint_local_descent facets L D (fun _ (_ : Unit) => ())
    (fun s _ a => l s a) (fun _ => l0) (fun i s _ v => f i s v) (fun s _ v => hl s v)
  obtain ⟨localPhase,hlocal⟩ := normalized_one L l l0 (fun i s a => g i s () a)
    (fun s a => by simpa [hres] using hg s () a)
  refine ⟨localPhase,fun t s a => ?_⟩
  rw [← hlocal,← hlocal,← hlocal,hh,hh']
  simp only [curvature,l,map_add,add_assoc]
  abel

/-- A physical potential and single-facet terms are invisible to primitive cycles. -/
theorem vanish_on_cycles {h : Configuration I G → Phase} (k : B → Phase)
    (u : ∀ i, Configuration (facets i) G → Phase)
    (eq : ∀ v, h v = k (d v) + ∑ i, u i (L.primitiveRes i v)) (z : Zprim L) :
    evaluate h z.val.val = 0 := by
  have factor : potentialCharacter h =
      (potentialCharacter k).comp (mapRedDist d) +
        ∑ i, (potentialCharacter (u i)).comp (restrictRedDist L i) := by
    apply extReduced
    intro v
    simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.comp_apply,restrictRedDist,
      mapRedDist_redBracket,potentialCharacter_bracket,eq,map_zero,Finset.sum_sub_distrib]
    abel
  have hz i : restrictRedDist L i z.val = 0 :=
    (Submodule.mem_iInf (fun i => LinearMap.ker (restrictRedDist L i))).mp z.property.2 i
  change potentialCharacter h z.val = 0
  simp [factor,LinearMap.sum_apply,hz, (show mapRedDist d z.val = 0 from z.property.1)]

theorem uniqueness_of_represents (hd : Function.Surjective d)
    (hcover : ∀ v : Configuration I G, (∀ i, L.primitiveRes i v = 0) → v = 0)
    {m n : Multiplier L} {χ χ' : TPrime L →ₗ[ℤ] Phase}
    (hm : Represents L m χ) (hn : Represents L n χ')
    (he : Equivalent L m.value n.value) : χ = χ' := by
  classical
  obtain ⟨h,hh,hχ⟩ := hm
  obtain ⟨h',hh',hχ'⟩ := hn
  obtain ⟨f,hf⟩ := he
  let l (s : Configuration I G) (a : B) := evaluate f (edgeRead L s a)
  let j (s : Configuration I G) (a : B) := h' s a - h s a - l s a
  have hj (s t : Configuration I G) (a : B) : j s a + j t (a+d s) = j (s+t) a := by
    have e := hf t s a
    rw [hh,hh'] at e
    simp only [j,l,curvature] at *
    linear_combination (norm := abel) e
  obtain ⟨k,ψ,hk⟩ := cocycle_potential hd j hj
  let proj := LinearMap.pi (fun i => (L.primitiveRes i).toIntLinearMap)
  have hker : ψ ∈ annihilator (LinearMap.ker proj) := by
    intro x hx
    rw [hcover x (fun i => congrFun (LinearMap.mem_ker.mp hx) i),map_zero]
  obtain ⟨g,hg⟩ := (annihilates_marginals_iff (fun i => (L.primitiveRes i).toIntLinearMap) ψ).mp
    (fun x hx => hker x (by
      apply LinearMap.mem_ker.mpr
      funext i
      exact (Submodule.mem_iInf _).mp hx i))
  let w (i : F) (x : Configuration (facets i) G) : Phase := if x=0 then 0 else f ⟨i,x,0⟩
  have hw (v : Configuration I G) : l v 0 = ∑ i, w i (L.primitiveRes i v) := by
    simp only [l,edgeRead,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases e : L.primitiveRes i v = 0 <;> simp [w,e]
  have E (v : Configuration I G) : h' v 0 - h v 0 =
      k (d v) + ∑ i, (w i (L.primitiveRes i v) + g i (L.primitiveRes i v)) := by
    have e := hk v
    change h' v 0 - h v 0 - l v 0 = _ at e
    rw [hw,hg] at e
    change h' v 0 - h v 0 - ∑ i, w i (L.primitiveRes i v) = k (d v) + ∑ i, g i (L.primitiveRes i v) at e
    rw [Finset.sum_add_distrib]
    rw [sub_eq_iff_eq_add.mp e]
    abel
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (BprimInZprim L) x
  rw [hχ,hχ']
  have eq := vanish_on_cycles L k (fun i x => w i x + g i x) E z
  change phaseTableEquiv ((fun v => h' v 0) - (fun v => h v 0)) z.val.val = 0 at eq
  rw [map_sub,LinearMap.sub_apply,sub_eq_zero] at eq
  exact eq.symm

private theorem existsRepresentingCharacter (hd : Function.Surjective d) (m : Multiplier L) :
    ∃ χ, Represents L m χ := by
  obtain ⟨h,χ,hh,hχ⟩ := exists_primitive_character L m hd
  exact ⟨χ,h,funext (fun ⟨t,s,a⟩ => hh t s a),hχ⟩

/-- Every equivalence class of multipliers on the vacuum orbit corresponds to
one and only one character on the literal primitive quotient. -/
def primitiveClassification (hd : Function.Surjective d)
    (hcover : ∀ v : Configuration I G, (∀ i, L.primitiveRes i v=0) → v=0) :
    Quotient (localEquivalence L) ≃ (TPrime L →ₗ[ℤ] Phase) := by
  classical
  let character := fun m => (existsRepresentingCharacter L hd m).choose
  have hcharacter (m) : Represents L m (character m) := (existsRepresentingCharacter L hd m).choose_spec
  have compat (m n : Multiplier L) : character m = character n ↔
      localEquivalence L m n := by
    change _ ↔ classCharacter L m = classCharacter L n
    rw [classCharacter_eq_iff]
    constructor
    · intro h
      exact equivalent_of_represents L hres D (h ▸ hcharacter m) (hcharacter n)
    · exact uniqueness_of_represents L hd hcover (hcharacter m) (hcharacter n)
  refine Equiv.ofBijective (Quotient.lift character (fun _ _ h => (compat _ _).mpr h)) ⟨?_,?_⟩
  · intro x y
    induction x using Quotient.inductionOn with | _ m =>
      induction y using Quotient.inductionOn with | _ n =>
        exact fun h => Quotient.sound ((compat m n).mp h)
  · intro χ
    obtain ⟨m,h,hm,hχ⟩ := realize_primitive_character facets L hres D χ
    refine ⟨Quotient.mk _ m,?_⟩
    exact uniqueness_of_represents L hd hcover (hcharacter m) ⟨h,hm,hχ⟩
      ((classCharacter_eq_iff L m m).mp rfl)

theorem primitiveClassification_mk (hd : Function.Surjective d)
    (hcover : ∀ v : Configuration I G, (∀ i, L.primitiveRes i v=0) → v=0)
    (m : Multiplier L) (χ : TPrime L →ₗ[ℤ] Phase) (hm : Represents L m χ) :
    primitiveClassification L hres D hd hcover (Quotient.mk _ m)=χ :=
  uniqueness_of_represents L hd hcover (existsRepresentingCharacter L hd m).choose_spec hm
    ((classCharacter_eq_iff L m m).mp rfl)

end GeneralSphereT.Transport

