import Formalization.Transport.RelativeCylinder

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open GeneralSphereT.Section4 GeneralSphereT.Section4.RelativeMapping GeneralSphereT.Section4.NativeRelativeHomotopyGroup
namespace GeneralSphereT.Transport.RelativeChains
universe u
variable {X : SSet.{u}} (P : X.Subcomplex)

private def interval (X : SSet.{u}) : SSet.Homotopy (X:=X) SSet.ι₀ SSet.ι₁ where
  h := 𝟙 _
  h₀ := Category.comp_id _
  h₁ := Category.comp_id _
  rel := by
    apply NatTrans.ext
    funext Δ
    apply ConcreteCategory.hom_ext
    intro x
    exact x.1.property.elim

private abbrev H (X : SSet.{u}) := (interval X).toSimplicialObjectHomotopy

private def prismOp {n : ℕ} (i : Fin (n+1)) :
    (relFree P).obj (op ⦋n⦌) ⟶ (relFree (cylinderSub P)).obj (op ⦋n+1⦌) :=
  liftLevel P (B:=AddCommGrpCat.of (level (cylinderSub P) (op ⦋n+1⦌)))
    (fun x => symbol (cylinderSub P) ((H X).h i x))

private theorem prismOp_symbol {n : ℕ} (i : Fin (n+1)) (x : X _⦋n⦌) :
    prismOp P i (symbol P x)=symbol (cylinderSub P) ((H X).h i x) := by
  apply lift_symbol (B:=AddCommGrpCat.of (level (cylinderSub P) (op ⦋n+1⦌)))
  intro y hy
  apply symbol_boundary
  change (SSet.yonedaEquiv.symm y).app _ (SSet.prodStdSimplex.nonDegenerateEquiv₁ i).val.1 ∈ P.obj _
  rw [SSet.prodStdSimplex.nonDegenerateEquiv₁_fst,SSet.yonedaEquiv_symm_app_objEquiv_symm]
  exact P.map (SimplexCategory.σ i).op hy

private theorem delta_symbol {n : ℕ} (i : Fin (n+2)) (x : X _⦋n+1⦌) :
    (relFree P).δ i (symbol P x)=symbol P (X.δ i x) := restriction_symbol P _ x
private theorem sigma_symbol {n : ℕ} (i : Fin (n+1)) (x : X _⦋n⦌) :
    (relFree P).σ i (symbol P x)=symbol P (X.σ i x) := restriction_symbol P _ x
private theorem first_symbol {Δ} (x : X.obj Δ) :
    (end₀ P).app Δ (symbol P x)=symbol (cylinderSub P) (SSet.ι₀.app Δ x) := relMap_symbol P _ _ _ x
private theorem last_symbol {Δ} (x : X.obj Δ) :
    (end₁ P).app Δ (symbol P x)=symbol (cylinderSub P) (SSet.ι₁.app Δ x) := relMap_symbol P _ _ _ x

private def intervalHomotopy : SimplicialObject.Homotopy (end₀ P) (end₁ P) where
  h := prismOp P
  h_zero_comp_δ_zero n := by
    apply level_ext (Δ:=op ⦋n⦌) P
    intro x
    have lhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n)+1⦌) => (relFree (cylinderSub P)).δ (n:=n) 0 y)
      (prismOp_symbol P (n:=n) 0 x)).trans (delta_symbol (cylinderSub P) (n:=n) 0 ((H X).h (n:=n) 0 x)))
    have rhs := (last_symbol P (Δ:=op ⦋n⦌) x)
    have de := ConcreteCategory.congr_hom ((H X).h_zero_comp_δ_zero n) x
    have e := congrArg (fun y : (X ⊗ Δ[1]) _⦋n⦌ => symbol (cylinderSub P) (Δ:=op ⦋n⦌) y) de
    exact lhs.trans (e.trans rhs.symm)
  h_last_comp_δ_last n := by
    apply level_ext (Δ:=op ⦋n⦌) P
    intro x
    have lhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n)+1⦌) => (relFree (cylinderSub P)).δ (n:=n) (Fin.last (n+1)) y)
      (prismOp_symbol P (n:=n) (Fin.last n) x)).trans (delta_symbol (cylinderSub P) (n:=n) (Fin.last (n+1)) ((H X).h (n:=n) (Fin.last n) x)))
    have rhs := (first_symbol P (Δ:=op ⦋n⦌) x)
    have de := ConcreteCategory.congr_hom ((H X).h_last_comp_δ_last n) x
    have e := congrArg (fun y : (X ⊗ Δ[1]) _⦋n⦌ => symbol (cylinderSub P) (Δ:=op ⦋n⦌) y) de
    exact lhs.trans (e.trans rhs.symm)
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    apply level_ext (Δ:=op ⦋n+1⦌) P
    intro x
    have lhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n+1)+1⦌) => (relFree (cylinderSub P)).δ (n:=n+1) i.castSucc y)
      (prismOp_symbol P (n:=n+1) j.succ x)).trans (delta_symbol (cylinderSub P) (n:=n+1) i.castSucc ((H X).h (n:=n+1) j.succ x)))
    have rhs := ((congrArg (fun y : level P (op ⦋n⦌) => prismOp P j y)
      (delta_symbol P (n:=n) i x)).trans (prismOp_symbol P j (X.δ i x)))
    have de := ConcreteCategory.congr_hom ((H X).h_succ_comp_δ_castSucc_of_lt i j hij) x
    have e := congrArg (fun y : (X ⊗ Δ[1]) _⦋n+1⦌ => symbol (cylinderSub P) (Δ:=op ⦋n+1⦌) y) de
    exact lhs.trans (e.trans rhs.symm)
  h_succ_comp_δ_castSucc_succ {n} j := by
    apply level_ext (Δ:=op ⦋n+1⦌) P
    intro x
    have lhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n+1)+1⦌) => (relFree (cylinderSub P)).δ (n:=n+1) j.castSucc.succ y)
      (prismOp_symbol P (n:=n+1) j.succ x)).trans (delta_symbol (cylinderSub P) (n:=n+1) j.castSucc.succ ((H X).h (n:=n+1) j.succ x)))
    have rhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n+1)+1⦌) => (relFree (cylinderSub P)).δ (n:=n+1) j.castSucc.succ y)
      (prismOp_symbol P (n:=n+1) j.castSucc x)).trans (delta_symbol (cylinderSub P) (n:=n+1) j.castSucc.succ ((H X).h (n:=n+1) j.castSucc x)))
    have de := ConcreteCategory.congr_hom ((H X).h_succ_comp_δ_castSucc_succ j) x
    have e := congrArg (fun y : (X ⊗ Δ[1]) _⦋n+1⦌ => symbol (cylinderSub P) (Δ:=op ⦋n+1⦌) y) de
    exact lhs.trans (e.trans rhs.symm)
  h_castSucc_comp_δ_succ_of_lt {n} i j hij := by
    apply level_ext (Δ:=op ⦋n+1⦌) P
    intro x
    have lhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n+1)+1⦌) => (relFree (cylinderSub P)).δ (n:=n+1) i.succ y)
      (prismOp_symbol P (n:=n+1) j.castSucc x)).trans (delta_symbol (cylinderSub P) (n:=n+1) i.succ ((H X).h (n:=n+1) j.castSucc x)))
    have rhs := ((congrArg (fun y : level P (op ⦋n⦌) => prismOp P j y)
      (delta_symbol P (n:=n) i x)).trans (prismOp_symbol P j (X.δ i x)))
    have de := ConcreteCategory.congr_hom ((H X).h_castSucc_comp_δ_succ_of_lt i j hij) x
    have e := congrArg (fun y : (X ⊗ Δ[1]) _⦋n+1⦌ => symbol (cylinderSub P) (Δ:=op ⦋n+1⦌) y) de
    exact lhs.trans (e.trans rhs.symm)
  h_comp_σ_castSucc_of_le {n} i j hij := by
    apply level_ext (Δ:=op ⦋n⦌) P
    intro x
    have lhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n)+1⦌) => (relFree (cylinderSub P)).σ (n:=n+1) i.castSucc y)
      (prismOp_symbol P (n:=n) j x)).trans (sigma_symbol (cylinderSub P) (n:=n+1) i.castSucc ((H X).h (n:=n) j x)))
    have rhs := ((congrArg (fun y : level P (op ⦋n+1⦌) => prismOp P j.succ y)
      (sigma_symbol P (n:=n) i x)).trans (prismOp_symbol P j.succ (X.σ i x)))
    have de := ConcreteCategory.congr_hom ((H X).h_comp_σ_castSucc_of_le i j hij) x
    have e := congrArg (fun y : (X ⊗ Δ[1]) _⦋n+2⦌ => symbol (cylinderSub P) (Δ:=op ⦋n+2⦌) y) de
    exact lhs.trans (e.trans rhs.symm)
  h_comp_σ_succ_of_lt {n} i j hij := by
    apply level_ext (Δ:=op ⦋n⦌) P
    intro x
    have lhs := ((congrArg (fun y : level (cylinderSub P) (op ⦋(n)+1⦌) => (relFree (cylinderSub P)).σ (n:=n+1) i.succ y)
      (prismOp_symbol P (n:=n) j x)).trans (sigma_symbol (cylinderSub P) (n:=n+1) i.succ ((H X).h (n:=n) j x)))
    have rhs := ((congrArg (fun y : level P (op ⦋n+1⦌) => prismOp P j.castSucc y)
      (sigma_symbol P (n:=n) i x)).trans (prismOp_symbol P j.castSucc (X.σ i x)))
    have de := ConcreteCategory.congr_hom ((H X).h_comp_σ_succ_of_lt i j hij) x
    have e := congrArg (fun y : (X ⊗ Δ[1]) _⦋n+2⦌ => symbol (cylinderSub P) (Δ:=op ⦋n+2⦌) y) de
    exact lhs.trans (e.trans rhs.symm)

variable (A : SimplicialObject AddCommGrpCat.{u})

private def cylinderMap {f g : NativeRelativeMorphism P A} (J : SSet.RelativeMorphism.Homotopy f g) :
    NativeRelativeMorphism (cylinderSub P) A where
  map := J.h
  comm := by
    rw [zeroBoundary_comp_inclusion]
    ext Δ x
    have h := J.rel.trans (cylinder_zeroBoundary P A)
    let y : ((P : SSet) ⊗ Δ[1]).obj Δ := (⟨x.val.1,x.property⟩,x.val.2)
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h Δ) y

/-- Linearizing a homotopy which is constant on the boundary produces a
chain homotopy on the relative normalized chains. -/
def chainHomotopyOfNative {f g : NativeRelativeMorphism P A} (J : SSet.RelativeMorphism.Homotopy f g) :
    Homotopy (Moore.map (linearize P A f)) (Moore.map (linearize P A g)) := by
  let k := linearize _ A (cylinderMap P A J)
  have a : end₀ P ≫ k=linearize P A f := by
    ext1 Δ
    apply level_ext P
    intro x
    change k.app Δ ((end₀ P).app Δ (symbol P x))=_
    rw [first_symbol,linearize_symbol]
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app J.h₀ Δ) x).trans (linearize_symbol P A f x).symm
  have b : end₁ P ≫ k=linearize P A g := by
    ext1 Δ
    apply level_ext P
    intro x
    change k.app Δ ((end₁ P).app Δ (symbol P x))=_
    rw [last_symbol,linearize_symbol]
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app J.h₁ Δ) x).trans (linearize_symbol P A g x).symm
  rw [← a,← b]
  exact OpenDisk.NormalizedMaps.normalizedMooreHomotopy ((intervalHomotopy P).postcomp k)

theorem native_homotopy_iff {f g : NativeRelativeMorphism P A} :
    Nonempty (SSet.RelativeMorphism.Homotopy f g) ↔
    Nonempty (Homotopy (Moore.map (linearize P A f)) (Moore.map (linearize P A g))) :=
  ⟨Nonempty.map (chainHomotopyOfNative P A),fun ⟨h⟩ => native_of_chain_homotopy P A h⟩

end GeneralSphereT.Transport.RelativeChains

