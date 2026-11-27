import Formalization.Transport.ProjectedChains
import Formalization.Transport.LiftedPrismChains

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.PathAlgebra GeneralSphereT.StandardModels OpenDisk.PhaseDuality RelativeChains
variable (A : SimplicialObject AddCommGrpCat.{0})

def rawBoundary (n : ℕ) : Distribution (A _⦋n+1⦌) →ₗ[ℤ] Distribution (A _⦋n⦌) :=
  Finsupp.linearCombination ℤ fun x => ∑ i : Fin (n+2), ((-1:ℤ)^i.val) • Finsupp.single (A.δ i x) 1

theorem altDifferential_apply (n : ℕ) (z : A _⦋n+1⦌) :
    (AlternatingFaceMapComplex.obj A).d (n+1) n z=∑ i : Fin (n+2), ((-1:ℤ)^i.val) • A.δ i z := by
  let ev : (A _⦋n+1⦌ ⟶ A _⦋n⦌) →+ A _⦋n⦌ := { toFun := fun f => f z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  rw [AlternatingFaceMapComplex.obj_d_eq]
  change ev _=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ev.map_zsmul _ _

theorem reduce_boundary (n : ℕ) (z : Distribution (A _⦋n+1⦌)) :
    (AlternatingFaceMapComplex.obj (reducedFree A)).d (n+1) n (reduceDist z)=reduceDist (rawBoundary A n z) := by
  let d := ((AlternatingFaceMapComplex.obj (reducedFree A)).d (n+1) n).hom.toIntLinearMap
  have eq : d.comp reduceDist=reduceDist.comp (rawBoundary A n) := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change d (reduceDist (Finsupp.single x 1))=reduceDist (rawBoundary A n (Finsupp.single x 1))
    simp only [reduceDist,rawBoundary,Finsupp.linearCombination_single,one_smul,map_sum,map_smul]
    rw [show d (redBracket x)=_ from altDifferential_apply (reducedFree A) n (redBracket x)]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun y : RedDist (A _⦋n⦌) => (-1:ℤ)^i.val • y) (mapRedDist_redBracket (A.δ i).hom x)
  exact LinearMap.congr_fun eq z

theorem project_boundary (n : ℕ) (z : Distribution (A _⦋n+1⦌)) :
    (target (reducedFree A)).d (n+1) n (simplexProjection A (n+1) z)=simplexProjection A n (rawBoundary A n z) := by
  have he := ConcreteCategory.congr_hom ((PInftyToNormalizedMooreComplex (reducedFree A)).comm (n+1) n) (reduceDist z)
  exact he.trans (congrArg (mooreProjection A n) (reduce_boundary A n z))

theorem rawBoundary_as_sum (n : ℕ) (z : Distribution (A _⦋n+1⦌)) :
    rawBoundary A n z=∑ i : Fin (n+2), ((-1:ℤ)^i.val) • mapDistFn (A.δ i) z := by
  have eq : rawBoundary A n=∑ i : Fin (n+2), ((-1:ℤ)^i.val) • mapDistFn (A.δ i) := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp [rawBoundary]
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply] using LinearMap.congr_fun eq z

theorem reduced_boundary_val (n : ℕ) (z : RedDist (A _⦋n+1⦌)) :
    ((AlternatingFaceMapComplex.obj (reducedFree A)).d (n+1) n z : RedDist (A _⦋n⦌)).val=rawBoundary A n z.val := by
  rw [altDifferential_apply,rawBoundary_as_sum]
  change (RedDist _).subtype _=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rfl

theorem included_boundary (n : ℕ) (z : (target (reducedFree A)).X (n+1)) :
    rawBoundary A n (mooreInclusion A (n+1) z).val=
      (mooreInclusion A n ((target (reducedFree A)).d (n+1) n z)).val := by
  have e := ConcreteCategory.congr_hom ((inclusionOfMooreComplexMap (reducedFree A)).comm (n+1) n) z
  exact (reduced_boundary_val A n _).symm.trans (congrArg Subtype.val e)

end GeneralSphereT.Transport.Prism

