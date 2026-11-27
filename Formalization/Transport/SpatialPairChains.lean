import Formalization.Transport.RelativeCochainExact
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-! The relative complex used in the prism proof is the quotient of the
ordinary simplicial chains by the chains on the boundary, in every degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial
namespace GeneralSphereT.Transport.SpatialPair
open RelativeChains
abbrev Z := ModuleCat.of ℤ ℤ
variable (Y : SSet.{0})
def gen {n : ℕ} (x : Y _⦋n⦌) := Y.ιChainComplex (R:=Z) x 1

theorem gen_ext {n : ℕ} {B : ModuleCat ℤ} {f g : (Y.chainComplex Z).X n ⟶ B}
    (h : ∀ x, f (gen Y x)=g (gen Y x)) : f=g := by
  apply SSet.chainComplex_hom_ext
  intro x
  apply ModuleCat.hom_ext
  exact LinearMap.ext_ring (h x)

def desc {n : ℕ} {B : ModuleCat ℤ} (t : Y _⦋n⦌ → B) : (Y.chainComplex Z).X n ⟶ B :=
  Sigma.desc (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ B (t x)))

theorem desc_gen {n : ℕ} {B : ModuleCat ℤ} (t : Y _⦋n⦌ → B) (x : Y _⦋n⦌) : desc Y t (gen Y x)=t x := by
  have e : Y.ιChainComplex (R:=Z) x ≫ desc Y t=ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ B (t x)) := Sigma.ι_desc _ _
  exact (ConcreteCategory.congr_hom e 1).trans (LinearMap.toSpanSingleton_apply_one _ _ _)

theorem gen_boundary (n : ℕ) (x : Y _⦋n+1⦌) :
    (Y.chainComplex Z).d (n+1) n (gen Y x)=∑ i : Fin (n+2), (-1:ℤ)^i.val • gen Y (Y.δ i x) := by
  let ev : (Z ⟶ (Y.chainComplex Z).X n) →+ (Y.chainComplex Z).X n :=
    { toFun := fun f => f 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h := congrArg ev (Y.ιChainComplex_d Z x)
  rw [map_sum] at h
  exact h.trans (Finset.sum_congr rfl (fun i _ => ev.map_zsmul _ _))

variable {Y} {A : SSet.{0}} (j : A ⟶ Y)
theorem map_gen {n : ℕ} (a : A _⦋n⦌) :
    (SSet.chainComplexMap j Z).f n (gen A a)=gen Y (j.app _ a) :=
  ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f A Y j Z a) 1

private abbrev P := SSet.Subcomplex.range j
abbrev chains := altChains.obj (relFree (P j))
variable {V : Type} [LinearOrder V] (X : AbstractSimplicialComplex V)

def project (j : A ⟶ GeneralSphereT.SimplicialCochain.orderedComplexSSet X) :
    (GeneralSphereT.SimplicialCochain.orderedComplexSSet X).chainComplex Z ⟶ chains j where
  f _ := desc _ (B:=ModuleCat.of ℤ _) (symbol (P j))
  comm' i k h := by
    obtain rfl : i=k+1 := h.symm
    apply gen_ext
    intro x
    change (chains j).d (k+1) k (desc _ _ (gen _ x))=desc _ _ (((GeneralSphereT.SimplicialCochain.orderedComplexSSet X).chainComplex Z).d (k+1) k (gen _ x))
    rw [desc_gen,Prism.relative_d_symbol,gen_boundary,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    let Y := GeneralSphereT.SimplicialCochain.orderedComplexSSet X
    let a := Y.δ i x
    let f := desc Y (B:=ModuleCat.of ℤ (level (P j) (op ⦋k⦌))) (symbol (P j))
    exact ((f.hom.toAddMonoidHom.map_zsmul ((-1:ℤ)^i.val) (gen Y a)).trans (congrArg
      (fun t : level (P j) (op ⦋k⦌) => (-1:ℤ)^i.val • t)
      (desc_gen Y (B:=ModuleCat.of ℤ (level (P j) (op ⦋k⦌))) (symbol (P j)) a))).symm

variable (j : A ⟶ GeneralSphereT.SimplicialCochain.orderedComplexSSet X)
abbrev space := GeneralSphereT.SimplicialCochain.orderedComplexSSet X

def sequence : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (SSet.chainComplexMap j Z) (project X j) (by
    ext n : 1
    apply gen_ext
    intro a
    change desc _ _ ((SSet.chainComplexMap j Z).f n (gen A a))=0
    rw [map_gen,desc_gen,symbol_boundary _ _ (show j.app _ a ∈ (P j).obj _ from ⟨a,rfl⟩)])

private def sectionAt (n : ℕ) : (chains j).X n ⟶ ((space X).chainComplex Z).X n :=
  ModuleCat.ofHom (Finsupp.linearCombination ℤ (fun x : {x : space X _⦋n⦌ // x ∉ (P j).obj _} => gen _ x.val))

private def retractAt (n : ℕ) := by
  classical
  exact desc (space X) (B:=(A.chainComplex Z).X n) (fun y : space X _⦋n⦌ =>
  if h : y ∈ (P j).obj _ then gen A (Classical.choose (show ∃ a, j.app _ a=y from h)) else 0)

private theorem section_symbol (n : ℕ) (y : space X _⦋n⦌) (h : y ∉ (P j).obj _) :
    sectionAt X j n (symbol (P j) y)=gen _ y := by
  classical
  change Finsupp.linearCombination ℤ _ (symbol (P j) y)=_
  simp only [symbol,dite_eq_right h,Finsupp.linearCombination_single,one_smul]

private theorem retraction_on (n : ℕ) (a : A _⦋n⦌) [Mono j] :
    retractAt X j n (gen _ (j.app _ a))=gen A a := by
  classical
  let h : j.app _ a ∈ (P j).obj _ := ⟨a,rfl⟩
  unfold retractAt
  rw [desc_gen,dite_eq_left h]
  exact congrArg (gen A) ((injective_of_mono (j.app _)) (Classical.choose_spec (show ∃ a',j.app _ a'=j.app _ a from h)))

theorem sequence_exact [Mono j] : (sequence X j).ShortExact := by
  classical
  rw [shortExact_iff_degreewise_shortExact]
  intro n
  apply ShortComplex.Splitting.shortExact
  refine { r := retractAt X j n, s := sectionAt X j n, f_r := ?_, s_g := ?_, id := ?_ }
  · apply gen_ext
    intro a
    change retractAt X j n ((SSet.chainComplexMap j Z).f n (gen _ a))=gen _ a
    rw [map_gen,retraction_on]
  · apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    have hy := (section_symbol X j n x.val x.property).trans rfl
    have eq := (congrArg ((project X j).f n) hy).trans (desc_gen (space X) (B:=ModuleCat.of ℤ _) (symbol (P j)) x.val)
    change (project X j).f n (sectionAt X j n (Finsupp.single x 1))=Finsupp.single x 1
    simpa only [symbol,dite_eq_right x.property] using eq
  · apply gen_ext
    intro y
    change (SSet.chainComplexMap j Z).f n (retractAt X j n (gen _ y))+sectionAt X j n (desc _ _ (gen _ y))=gen _ y
    rw [desc_gen]
    by_cases h : y ∈ (P j).obj _
    · obtain ⟨a,rfl⟩ := h
      rw [retraction_on,map_gen,symbol_boundary _ _ (show j.app _ a ∈ (P j).obj _ from ⟨a,rfl⟩),map_zero,add_zero]
    · rw [section_symbol X j n y h,retractAt,desc_gen,dite_eq_right h,map_zero,zero_add]

end GeneralSphereT.Transport.SpatialPair
