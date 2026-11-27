import Formalization.Transport.RelativeFree
import Formalization.Transport.MooreCylinder
import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open GeneralSphereT.Section4 GeneralSphereT.Section4.RelativeMapping GeneralSphereT.Section4.NativeRelativeHomotopyGroup
namespace GeneralSphereT.Transport.RelativeChains
universe u
variable {X : SSet.{u}} (P : X.Subcomplex)

def cylinderSub : (X ⊗ Δ[1]).Subcomplex where
  obj Δ := {x | x.1 ∈ P.obj Δ}
  map θ := fun _ hx => P.map θ hx

def end₀ : relFree P ⟶ relFree (cylinderSub P) := relMap P _ SSet.ι₀ (fun _ _ h => h)
def end₁ : relFree P ⟶ relFree (cylinderSub P) := relMap P _ SSet.ι₁ (fun _ _ h => h)
def project : relFree (cylinderSub P) ⟶ relFree P := relMap _ P (fst X Δ[1]) (fun _ _ h => h)

theorem end₀_project : end₀ P ≫ project P = 𝟙 _ := by
  ext1 Δ
  apply level_ext P
  intro x
  exact ((congrArg ((project P).app Δ) (relMap_symbol P _ SSet.ι₀ _ x)).trans (relMap_symbol _ P (fst X Δ[1]) _ _))

theorem end₁_project : end₁ P ≫ project P = 𝟙 _ := by
  ext1 Δ
  apply level_ext P
  intro x
  exact ((congrArg ((project P).app Δ) (relMap_symbol P _ SSet.ι₁ _ x)).trans (relMap_symbol _ P (fst X Δ[1]) _ _))

/-- The time label is tested only on the first vertex of the simplex. -/
private def atZero (n : ℕ) (x : (X ⊗ Δ[1]) _⦋n⦌) : level P (op ⦋n⦌) :=
  if SSet.stdSimplex.asOrderHom x.2 0 = 0 then symbol P x.1 else 0

private def grade (n : ℕ) : (relFree (cylinderSub P)).obj (op ⦋n⦌) ⟶ (relFree P).obj (op ⦋n⦌) :=
  liftLevel (cylinderSub P) (B:=AddCommGrpCat.of (level P (op ⦋n⦌))) (atZero P n)

private theorem grade_symbol (n : ℕ) (x : (X ⊗ Δ[1]) _⦋n⦌) :
    grade P n (symbol (cylinderSub P) x)=atZero P n x := by
  apply lift_symbol (B:=AddCommGrpCat.of (level P (op ⦋n⦌)))
  intro y hy
  simp [atZero,symbol_boundary P y.1 (show y.1 ∈ P.obj _ from hy)]

private theorem grade_first (n : ℕ) : (end₀ P).app (op ⦋n⦌) ≫ grade P n=𝟙 _ := by
  apply level_ext P
  intro x
  change grade P n ((relMap P _ SSet.ι₀ _).app _ (symbol P x))=symbol P x
  rw [relMap_symbol,grade_symbol]
  exact if_pos (show SSet.stdSimplex.asOrderHom (SSet.ι₀.app _ x).2 0 = 0 from rfl)

private theorem grade_last (n : ℕ) : (end₁ P).app (op ⦋n⦌) ≫ grade P n=0 := by
  apply level_ext P
  intro x
  change grade P n ((relMap P _ SSet.ι₁ _).app _ (symbol P x))=0
  rw [relMap_symbol,grade_symbol]
  exact if_neg (show ¬SSet.stdSimplex.asOrderHom (SSet.ι₁.app _ x).2 0 = 0 from (by change (1 : Fin 2) ≠ 0; decide))

variable (A : SimplicialObject AddCommGrpCat.{u})

private def cylinderHomotopy {f g : NativeRelativeMorphism P A} (k : relFree (cylinderSub P) ⟶ A)
    (hk₀ : end₀ P ≫ k=linearize P A f) (hk₁ : end₁ P ≫ k=linearize P A g) :
    SSet.RelativeMorphism.Homotopy f g where
  h := (onSymbols _ A k).map
  h₀ := by
    ext Δ x
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hk₀ Δ) (symbol P x)
    change k.app Δ ((end₀ P).app Δ (symbol P x))=_ at h
    exact (congrArg (k.app Δ) (relMap_symbol P _ SSet.ι₀ _ x).symm).trans (h.trans (linearize_symbol P A f x))
  h₁ := by
    ext Δ x
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hk₁ Δ) (symbol P x)
    change k.app Δ ((end₁ P).app Δ (symbol P x))=_ at h
    exact (congrArg (k.app Δ) (relMap_symbol P _ SSet.ι₁ _ x).symm).trans (h.trans (linearize_symbol P A g x))
  rel := by
    rw [cylinder_zeroBoundary]
    ext Δ x
    exact zero_on_boundary _ A (onSymbols _ A k) (x.1.val,x.2) x.1.property

/-- Chain homotopy relative to a subcomplex gives an actual simplicial homotopy
constant there, including for the pair (CX,X). -/
theorem native_of_chain_homotopy {f g : NativeRelativeMorphism P A}
    (H : Homotopy (Moore.map (linearize P A f)) (Moore.map (linearize P A g))) :
    Nonempty (SSet.RelativeMorphism.Homotopy f g) := by
  obtain ⟨k,h₀,h₁⟩ := extend_on_cylinder (end₀ P) (end₁ P) (project P) (end₀_project P) (end₁_project P)
    (grade P) (grade_first P) (grade_last P) H
  exact ⟨cylinderHomotopy P A k h₀ h₁⟩

end GeneralSphereT.Transport.RelativeChains
