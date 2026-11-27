import Formalization.Transport.Multiplier

/-! Exact character classification from the integer matrices of the transport laws. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open OpenDisk.PhaseDuality GeneralSphereT.PathAlgebra
variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {F : Type*} [Fintype F] {S A : F → Type*}
variable [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B}
variable (L : FacetRestrictionData (Facet := F) (CAt := S) (BAt := A) d)

local notation "Chain" => Distribution (Triangle C B)
def faceMap : Chain →ₗ[ℤ] Distribution (TwoSlot S A) :=
  Finsupp.linearCombination ℤ (triangleRead L)

def gen (t s : C) (a : B) : Chain := Finsupp.single (t,s,a) 1

def assocRow (r t s : C) (a : B) : Chain :=
  gen t s a + gen r (s+t) a - gen r t (a+d s) - gen (t+r) s a

def zzRow (w z : C) (a : B) : Chain := gen w z a - gen z w a

inductive Relation : Chain → Prop
  | marginal {x} (h : faceMap L x = 0) : Relation x
  | tetra (r t s : C) (a : B) : Relation (assocRow (d:=d) r t s a)
  | closed (w z : C) (a : B) (hw : d w = 0) (hz : d z = 0) :
      Relation (zzRow w z a)

def relations := Submodule.span ℤ {x | Relation L x}

private def slotEdge (i : F) (s : S i) (a : A i) : Distribution (OneSlot S A) := by
  classical
  exact if s=0 then 0 else Finsupp.single ⟨i,s,a⟩ 1

private def slotBoundary : Distribution (TwoSlot S A) →ₗ[ℤ] Distribution (OneSlot S A) :=
  Finsupp.linearCombination ℤ fun ⟨i,t,s,a⟩ =>
    slotEdge i s a + slotEdge i t (a+L.localD i s) - slotEdge i (s+t) a

private theorem readBoundary_fac : (slotBoundary L).comp (faceMap L) = readBoundary L := by
  classical
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  rcases x with ⟨t,s,a⟩
  change slotBoundary L (faceMap L (gen t s a)) = readBoundary L (gen t s a)
  simp only [gen,faceMap,readBoundary,Finsupp.linearCombination_single,one_smul,
    triangleRead,map_sum,edgeRead,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := DFunLike.congr_fun (L.commutes i) s
  change L.physicalRes i (d s) = L.localD i (L.primitiveRes i s) at h
  by_cases ht : L.primitiveRes i t = 0 <;> by_cases hs : L.primitiveRes i s = 0 <;>
    simp [ht,hs,slotBoundary,slotEdge,h,map_add]

theorem relations_le_kernel : relations L ≤ LinearMap.ker (readBoundary L) := by
  apply Submodule.span_le.mpr
  intro x hx
  change Relation L x at hx
  change readBoundary L x = 0
  cases hx with
  | marginal h => rw [← readBoundary_fac,LinearMap.comp_apply,h,map_zero]
  | tetra r t s a =>
    simp [assocRow,gen,readBoundary,add_comm,add_left_comm]
    abel
  | closed w z a hw hz => simp [zzRow,gen,readBoundary,hw,hz,add_comm]

abbrev IntegralProcesses := IntegralQuotient (relations L) (LinearMap.ker (readBoundary L))

theorem character_iff (c : Triangle C B → Phase) :
    evaluate c ∈ annihilator (relations L) ↔ ∃ m : Multiplier L, m.value = c := by
  classical
  constructor
  · intro h
    have each {x} (hx : Relation L x) := h x (Submodule.subset_span hx)
    have localK : evaluate c ∈ annihilator (LinearMap.ker (faceMap L)) :=
      fun x hx => each (.marginal hx)
    obtain ⟨ψ,hψ⟩ := (annihilates_kernel_iff _ _).mp localK
    refine ⟨⟨c,⟨phaseTableEquiv.symm ψ,?_⟩,?_,?_⟩,rfl⟩
    · intro x
      have e := LinearMap.congr_fun hψ (Finsupp.single x 1)
      have eqv : evaluate (phaseTableEquiv.symm ψ) = ψ := phaseTableEquiv.apply_symm_apply ψ
      simpa [eqv,faceMap] using e.symm
    · intro r t s a
      have e := each (.tetra r t s a)
      simp only [assocRow,gen,map_sub,map_add,evaluate_single,one_zsmul] at e
      linear_combination (norm := abel) e
    · intro z w a hz hw
      have e := each (.closed w z a hw hz)
      simpa [zzRow,gen,sub_eq_zero] using e
  · rintro ⟨m,rfl⟩
    change relations L ≤ LinearMap.ker (evaluate m.value)
    apply Submodule.span_le.mpr
    intro x hx
    change Relation L x at hx
    change evaluate m.value x = 0
    cases hx with
    | marginal h =>
      obtain ⟨f,hf⟩ := m.localTable
      have fact : (evaluate f).comp (faceMap L) = evaluate m.value := by
        ext k
        simpa [faceMap] using (hf k).symm
      rw [← fact,LinearMap.comp_apply,h,map_zero]
    | tetra r t s a =>
      simp only [assocRow,gen,map_sub,map_add,evaluate_single,one_zsmul]
      linear_combination (norm := abel) m.assoc r t s a
    | closed w z a hw hz => simp [zzRow,gen,m.zz z w a hz hw]

def classCharacter (m : Multiplier L) : IntegralProcesses L →ₗ[ℤ] Phase :=
  restrictCharacter _ _ ⟨evaluate m.value,(character_iff L _).mpr ⟨m,rfl⟩⟩

theorem classCharacter_eq_iff (m n : Multiplier L) :
    classCharacter L m = classCharacter L n ↔ Equivalent L m.value n.value := by
  rw [equivalent_iff]
  constructor
  · intro h x hx
    exact (LinearMap.congr_fun h ((identitiesInInvariant _ _).mkQ ⟨x,hx⟩)).symm
  · intro h
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
    exact (h y.1 y.2).symm

theorem classCharacter_surjective : Function.Surjective (classCharacter L) := by
  intro ψ
  obtain ⟨χ,h⟩ := restrictCharacter_surjective _ _ (relations_le_kernel L) ψ
  let c := phaseTableEquiv.symm χ.1
  have hc : evaluate c = χ.1 := phaseTableEquiv.apply_symm_apply _
  obtain ⟨m,hm⟩ := (character_iff L c).mp (hc ▸ χ.2)
  refine ⟨m,?_⟩
  rw [← h]
  apply congrArg (restrictCharacter _ _)
  apply Subtype.ext
  change evaluate m.value = χ.1
  rw [hm,hc]

def localEquivalence : Setoid (Multiplier L) :=
  Setoid.ker (classCharacter L)

/-- The setoid defining this quotient is precisely one simultaneous local basis change. -/
def multiplierClassification :
    Quotient (localEquivalence L) ≃ (IntegralProcesses L →ₗ[ℤ] Phase) :=
  Equiv.ofBijective (Quotient.lift (classCharacter L) (fun _ _ h => h))
    ⟨by
        intro a b
        induction a using Quotient.inductionOn with | _ m =>
          induction b using Quotient.inductionOn with | _ n =>
            exact fun e => Quotient.sound e,
     fun χ => by
       obtain ⟨m,hm⟩ := classCharacter_surjective L χ
       exact ⟨Quotient.mk _ m,hm⟩⟩

def zeroMultiplier : Multiplier L where
  value := fun _ => 0
  localTable := ⟨0,fun _ => by simp [evaluate]⟩
  assoc := by simp
  zz := by simp

@[simp] theorem classCharacter_zero : classCharacter L (zeroMultiplier L) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
  change evaluate (fun _ => 0) y.val = 0
  change phaseTableEquiv (0 : Triangle C B → Phase) y.val = 0
  rw [map_zero,LinearMap.zero_apply]

theorem simultaneous_strictification_iff (m : Multiplier L) :
    Equivalent L m.value (fun _ => 0) ↔ classCharacter L m = 0 := by
  rw [← classCharacter_zero L]
  exact (classCharacter_eq_iff L m (zeroMultiplier L)).symm

end GeneralSphereT.Transport

