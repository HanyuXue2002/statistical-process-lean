import Formalization.Transport.MeasuredCycles
import Formalization.Transport.PrismClass
import Formalization.Transport.PhaseSeparation

noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.StandardModels OpenDisk.PhaseDuality
variable {G : Type} [AddCommGroup G] (q d : ℕ)

def Nondeg {p : ℕ} (a : EM G q (p+1)) : Prop :=
  ∀ (i : Fin (p+1)) (b : EM G q p), (K (AddCommGrpCat.of G) q).σ i b ≠ a

private def keep {E : Type} (P : E → Prop) : Distribution E →ₗ[ℤ] Distribution {a // P a} := by
  classical
  exact Finsupp.linearCombination ℤ fun a => if h : P a then Finsupp.single ⟨a,h⟩ 1 else 0

private theorem keep_at {E : Type} (P : E → Prop) (x : Distribution E) (a : {a // P a}) :
    keep P x a=x a.val := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add _ _ ha hb => simp [ha,hb]
  | single k n =>
    by_cases h : P k
    · by_cases e : k=a.val
      · subst k
        simp [keep,h]
      · have e' : (⟨k,h⟩ : Subtype P)≠a := fun he => e (congrArg Subtype.val he)
        simp [keep,h,e,e',Finsupp.single_apply]
    · have e : k≠a.val := fun he => h (he ▸ a.property)
      simp [keep,h,e,Finsupp.single_apply]

def normalBoundary : Distribution (EM G q (d+2)) →ₗ[ℤ] Distribution {a : EM G q (d+1) // Nondeg q a} :=
  (keep (Nondeg q)).comp emBoundary

theorem normalBoundary_at (x : Distribution (EM G q (d+2))) (a : {a : EM G q (d+1) // Nondeg q a}) :
    normalBoundary q d x a=emBoundary x a.val := keep_at (Nondeg q) _ a

theorem normalBoundary_zero_of_coefficients (x : Distribution (EM G q (d+2)))
    (h : ∀ a, Nondeg q a → emBoundary x a=0) : normalBoundary q d x=0 := by
  ext a
  exact (keep_at (Nondeg q) (emBoundary x) a).trans (h a.val a.property)

abbrev emCycles := LinearMap.ker (normalBoundary (G:=G) q d)

/-- Quotient by ordinary boundaries and by all degenerate simplices. -/
def emRelations : Submodule ℤ (Distribution (EM G q (d+2))) :=
  LinearMap.range emBoundary ⊔ Submodule.span ℤ {x | ∃ (i : Fin (d+2)) (a : EM G q (d+1)),
    x=Finsupp.single ((K (AddCommGrpCat.of G) q).σ i a) 1}

abbrev CycleClasses := (emCycles (G:=G) q d).map (emRelations (G:=G) q d).mkQ

def emClass : emCycles (G:=G) q d →ₗ[ℤ] CycleClasses (G:=G) q d :=
  ((emRelations q d).mkQ.comp (emCycles q d).subtype).codRestrict _ (fun z => ⟨z.val,z.property,rfl⟩)

theorem emClass_surj : Function.Surjective (emClass (G:=G) q d) := by
  rintro ⟨z,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem annihilates_emRelations (ω : EM G q (d+2) → Phase) :
    evaluate ω ∈ annihilator (emRelations q d) ↔ ClosedOnEM ω ∧ NormalizedOnEM ω := by
  change emRelations q d ≤ LinearMap.ker (evaluate ω) ↔ _
  rw [emRelations,sup_le_iff,Submodule.span_le]
  constructor
  · rintro ⟨hd,hn⟩
    constructor
    · intro x
      have he := hd (show emBoundary (Finsupp.single x 1) ∈ LinearMap.range emBoundary from ⟨_,rfl⟩)
      change evaluate ω (emBoundary (Finsupp.single x 1))=0 at he
      simpa [emBoundary] using he
    · intro i a
      have he := hn (show Finsupp.single ((K (AddCommGrpCat.of G) q).σ i a) 1 ∈ _ from ⟨i,a,rfl⟩)
      simpa [LinearMap.mem_ker] using he
  · rintro ⟨hc,hn⟩
    constructor
    · rintro _ ⟨w,rfl⟩
      change evaluate ω (emBoundary w)=0
      have he := LinearMap.congr_fun (evaluate_emBoundary ω) w
      have hz : phaseDifferential ω=0 := funext hc
      change evaluate ω (emBoundary w)=evaluate (phaseDifferential ω) w at he
      rw [he,hz]
      exact LinearMap.congr_fun (phaseTableEquiv (X:=EM G q (d+3))).map_zero w
    · rintro _ ⟨i,a,rfl⟩
      simpa [LinearMap.mem_ker] using hn i a

def cocycleCharacter (ω : NormalizedCocycle G q d) : CycleClasses (G:=G) q d →ₗ[ℤ] Phase :=
  ((emRelations q d).liftQ (evaluate ω.val) ((annihilates_emRelations q d ω.val).mpr ω.property)).comp
    (CycleClasses (G:=G) q d).subtype

theorem character_evaluation (ω : NormalizedCocycle G q d) (x : emCycles (G:=G) q d) :
    cocycleCharacter q d ω (emClass q d x)=evaluate ω.val x.val := rfl

private def extendNormalized (φ : Distribution {a : EM G q (d+1) // Nondeg q a} →ₗ[ℤ] Phase) :
    EM G q (d+1) → Phase := phaseTableEquiv.symm (φ.comp (keep (Nondeg q)))

private theorem extendNormalized_normal (φ : Distribution {a : EM G q (d+1) // Nondeg q a} →ₗ[ℤ] Phase) :
    NormalizedOnEM (extendNormalized q d φ) := by
  classical
  intro i b
  have h : ¬Nondeg q ((K (AddCommGrpCat.of G) q).σ i b) := fun e => e i b rfl
  change φ (keep (Nondeg q) (Finsupp.single _ 1))=0
  simp [keep,h]

private theorem eval_extend (φ : Distribution {a : EM G q (d+1) // Nondeg q a} →ₗ[ℤ] Phase) :
    evaluate (extendNormalized q d φ)=φ.comp (keep (Nondeg q)) := phaseTableEquiv.apply_symm_apply _

private theorem factoring_normalized (θ : EM G q (d+1) → Phase) (hn : NormalizedOnEM θ) :
    (evaluate (fun a : {a : EM G q (d+1) // Nondeg q a} => θ a.val)).comp (keep (Nondeg q))=evaluate θ := by
  classical
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  change evaluate _ (keep (Nondeg q) (Finsupp.single a 1))=evaluate θ (Finsupp.single a 1)
  by_cases h : Nondeg q a
  · simp [keep,h]
  · simp only [Nondeg,not_forall,not_not] at h
    obtain ⟨i,b,rfl⟩ := h
    have he : ¬Nondeg q ((K (AddCommGrpCat.of G) q).σ i b) := fun e => e i b rfl
    simp [keep,he,hn i b]

theorem cocycleCharacter_eq_iff (ω η : NormalizedCocycle G q d) :
    cocycleCharacter q d ω=cocycleCharacter q d η ↔ (cocycleSetoid G q d).r ω η := by
  let χ := evaluate η.val - evaluate ω.val
  have eqv : χ=evaluate (η.val-ω.val) := (phaseTableEquiv.map_sub _ _).symm
  constructor
  · intro h
    have ann : χ ∈ annihilator (emCycles q d) := by
      intro x hx
      have e := LinearMap.congr_fun h (emClass q d ⟨x,hx⟩)
      rw [character_evaluation,character_evaluation] at e
      exact sub_eq_zero.mpr e.symm
    obtain ⟨φ,hφ⟩ := (annihilates_kernel_iff (normalBoundary q d) χ).mp ann
    refine ⟨extendNormalized q d φ,extendNormalized_normal q d φ,phaseTableEquiv.injective ?_⟩
    change evaluate (η.val-ω.val)=evaluate (phaseDifferential _)
    rw [← eqv,← hφ,← evaluate_emBoundary,eval_extend]
    rfl
  · rintro ⟨θ,hn,he⟩
    ext z
    obtain ⟨w,rfl⟩ := emClass_surj q d z
    rw [character_evaluation,character_evaluation]
    have e := LinearMap.congr_fun (evaluate_emBoundary θ) w.val
    rw [← he,← eqv] at e
    have hf := LinearMap.congr_fun (factoring_normalized q d θ hn) (emBoundary w.val)
    change _ = evaluate θ (emBoundary w.val) at hf
    have hw : keep (Nondeg q) (emBoundary w.val)=0 := w.property
    simp only [LinearMap.comp_apply,hw,map_zero] at hf
    change evaluate θ (emBoundary w.val)=evaluate η.val w.val-evaluate ω.val w.val at e
    exact (sub_eq_zero.mp (e.symm.trans hf.symm)).symm

/-- Universal coefficients in the very same simplex coordinates as the triangle integral. -/
def normalizedCharacterEquiv : NormalizedEMCohomology G q d ≃ (CycleClasses (G:=G) q d →ₗ[ℤ] Phase) :=
  Equiv.ofBijective (Quotient.lift (cocycleCharacter q d) (fun a b h => (cocycleCharacter_eq_iff q d a b).mpr h)) ⟨by
    intro x y
    induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y =>
        exact fun h => Quotient.sound ((cocycleCharacter_eq_iff q d x y).mp h),
    by
      intro χ
      obtain ⟨φ,hφ⟩ := extend_character (CycleClasses (G:=G) q d) χ
      let ψ := φ.comp (emRelations q d).mkQ
      let ω := phaseTableEquiv.symm ψ
      have hω : evaluate ω=ψ := phaseTableEquiv.apply_symm_apply _
      have hann : evaluate ω ∈ annihilator (emRelations q d) := by
        intro x hx
        rw [hω]
        change φ ((emRelations q d).mkQ x)=0
        rw [show (emRelations (G:=G) q d).mkQ x=0 from (Submodule.Quotient.mk_eq_zero _).mpr hx,map_zero]
      let W : NormalizedCocycle G q d := ⟨ω,(annihilates_emRelations q d ω).mp hann⟩
      refine ⟨Quotient.mk _ W,?_⟩
      change cocycleCharacter q d W=χ
      ext z
      obtain ⟨x,rfl⟩ := emClass_surj q d z
      exact (character_evaluation q d W x).trans ((LinearMap.congr_fun hω x.val).trans (LinearMap.congr_fun hφ (emClass q d x)))
  ⟩

end GeneralSphereT.Transport.Prism
