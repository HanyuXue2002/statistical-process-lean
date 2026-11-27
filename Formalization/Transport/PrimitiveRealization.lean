import Formalization.Transport.LocalDescent
import Formalization.Transport.PrimitiveComparison
import Formalization.Transport.NormalizedTables

/-! Realizing every character of the strict primitive quotient by a transport
multiplier, using the relative primitive sections of the simplicial model. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra GeneralSphereT.PathAlgebra.FacetRestrictionData OpenDisk.PhaseDuality

variable {I G B F : Type*} [LinearOrder I] [Fintype I] [AddCommGroup G] [AddCommGroup B]
variable [Fintype F] (facets : F → Set I)
variable {A : F → Type*} [∀ i, AddCommGroup (A i)]
variable {d : Configuration I G →+ B}
variable (L : FacetRestrictionData (Facet:=F) (CAt:=fun i => Configuration (facets i) G) (BAt:=A) d)
variable (hres : ∀ i, L.primitiveRes i = coordinateRestriction (facets i))
variable (D : RelativePrimitiveSectionData facets L)

theorem extReduced {X : Type*} [AddCommGroup X] {f g : RedDist X →ₗ[ℤ] Phase}
    (h : ∀ x, f (redBracket x) = g (redBracket x)) : f = g := by
  let π := Finsupp.linearCombination ℤ (redBracket (X:=X))
  have pair : f.comp π = g.comp π := by ext x; simpa [π] using h x
  have projection : (RedDist X).subtype.comp π =
      LinearMap.id - (Finsupp.lsingle (R:=ℤ) (M:=ℤ) (0:X)).comp (augmentation X) := by
    ext x y
    simp [π,redBracket,bracket,augmentation]
  apply LinearMap.ext
  intro x
  have hx : π x.val = x := by
    apply Subtype.ext
    have e := LinearMap.congr_fun projection x.val
    simpa only [LinearMap.comp_apply,Submodule.subtype_apply,LinearMap.sub_apply,LinearMap.id_apply,
      (show augmentation X x.val=0 from x.property),map_zero,sub_zero] using e
  simpa only [LinearMap.comp_apply,hx] using LinearMap.congr_fun pair x.val

include D hres in
theorem realize_primitive_character (χ : TPrime L →ₗ[ℤ] Phase) :
    ∃ (m : Multiplier L) (h : Configuration I G → B → Phase),
      m.value = curvature (d:=d) h ∧
      ∀ z : Zprim L, χ ((BprimInZprim L).mkQ z) = evaluate (fun v => h v 0) z.val.val := by
  classical
  obtain ⟨β,hβ⟩ := restrictCharacter_surjective _ _ (Bprim_le_Zprim L) χ
  obtain ⟨H,O,ho⟩ := (annihilates_primitive_iff L β.val).mp β.property
  let h (s : Configuration I G) (a : B) := H (edge s a)
  let o (i : F) (s v : Configuration (facets i) G) := O i (edge s v)
  let p := curvature (d:=d) h
  have h0 (a : B) : h 0 a = 0 := by simp [h]
  have h₁ (s : Configuration I G) (a : B) : p (0,s,a) = 0 := by simp [p,curvature,h0]
  have h₂ (t : Configuration I G) (a : B) : p (t,0,a) = 0 := by simp [p,curvature,h0]
  let f (i : F) (t s v : Configuration (facets i) G) :=
    o i s v + o i t (v+s) - o i (s+t) v
  have hf (t s v : Configuration I G) : p (t,s,d v) =
      ∑ i, f i (coordinateRestriction (facets i) t) (coordinateRestriction (facets i) s)
        (coordinateRestriction (facets i) v) := by
    have a := ho s v
    have b := ho t (v+s)
    have c := ho (s+t) v
    simp only [hres,map_add,add_assoc] at a b c
    simp only [p,curvature,h,f,o,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    linear_combination (norm := abel) -a - b + c
  obtain ⟨g,hg⟩ := joint_local_descent facets L D
    (fun i => coordinateRestriction (facets i) (G:=G)) (fun t s a => p (t,s,a)) h₁ f hf
  obtain ⟨g₂,hg₂⟩ := normalized_two L p h₁ h₂ g (by simpa only [hres] using hg)
  let m : Multiplier L := ⟨p,⟨g₂,hg₂⟩,curvature_assoc h,curvature_zz h⟩
  refine ⟨m,h,rfl,fun z => ?_⟩
  have atZero (v : Configuration I G) : h v 0 =
      β.val (redBracket v) + ∑ i, o i (L.primitiveRes i v) 0 := by
    have hv := ho v 0
    simp only [zero_add,map_zero,redBracket_zero] at hv
    change _ = H (edge v 0) - _ at hv
    simp only [h,o]
    linear_combination (norm := abel) -hv
  let u (i : F) := potentialCharacter (fun v => o i v 0)
  have comp : potentialCharacter (fun v => h v 0) =
      β.val + ∑ i, (u i).comp (restrictRedDist L i) := by
    apply extReduced
    intro v
    simp [potentialCharacter_bracket,atZero,h0,restrictRedDist,u,o,LinearMap.sum_apply]
  have hz i : restrictRedDist L i z.val = 0 :=
    (Submodule.mem_iInf (fun i => LinearMap.ker (restrictRedDist L i))).mp z.property.2 i
  rw [← hβ]
  change β.val z.val = potentialCharacter (fun v => h v 0) z.val
  rw [comp]
  simp [LinearMap.sum_apply,hz]

end GeneralSphereT.Transport

