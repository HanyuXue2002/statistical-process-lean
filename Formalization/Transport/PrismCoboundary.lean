import Formalization.Transport.PrismEvaluation

/-! Changing the EM cocycle by a coboundary changes the triangle integral
by the three oriented edge integrals of the very same cochain. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality GeneralSphereT.SimplicialCochain GeneralSphereT.StandardModels
variable {G : Type} [AddCommGroup G] {Y : Type*} {q p : ℕ}

def phaseDifferential (θ : EM G q p → Phase) (x : EM G q (p+1)) : Phase :=
  ∑ j : Fin (p+2), ((-1:ℤ)^j.val) • θ ((K (AddCommGrpCat.of G) q).δ j x)

theorem pullCochain_d (field : (Fin (q+1) → Y) → G) (θ : EM G (q+1) p → Phase) :
    pullCochain field (phaseDifferential θ) = (pullCochain field θ).comp boundary := by
  have each (k : ℕ) (x : Fin (k+1) → Y) :
      pullCochain field (phaseDifferential θ) (gen (List.ofFn x)) =
        pullCochain field θ (boundary (gen (List.ofFn x))) := by
    rw [boundary_gen,faces_ofFn,map_sum]
    by_cases h : k = p+1
    · subst k
      simp only [pullCochain,gen,phaseDifferential,map_smul,evaluate_single,one_zsmul,homogeneous_ofFn]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun a => ((-1:ℤ)^i.val) • θ a) (classifyingValue_face field x (Fin.succAboveOrderEmb i))
    · have h' : k+1 ≠ p+2 := by omega
      simp only [pullCochain,gen,map_smul,evaluate_single,one_zsmul,homogeneous_ofFn_other _ _ h',
        homogeneous_ofFn_other _ _ h,smul_zero,Finset.sum_const_zero]
  apply Finsupp.lhom_ext'
  intro xs
  apply LinearMap.ext_ring
  change pullCochain field (phaseDifferential θ) (gen xs) = pullCochain field θ (boundary (gen xs))
  cases xs with
  | nil => rw [boundary_gen]; simp [pullCochain,homogeneous,faces,gen]
  | cons y ys => simpa only [List.ofFn_get] using each ys.length (y::ys).get

variable {V : Type*} [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q d : ℕ)

def affineEdge (θ : EM G (q+1) (d+1) → Phase) (z : Chains V) (s v : Cochain X q G) : Phase :=
  -pullCochain (affineField X q) θ (segment (fun x => (v,x)) (fun x => (v+s,x)) z)

theorem affineMultiplier_of_coboundary (θ : EM G (q+1) (d+1) → Phase) (z : Chains V) (hz : boundary z=0)
    (t s v : Cochain X q G) :
    affineMultiplier X q d (phaseDifferential θ) z t s v =
      affineEdge X q d θ z s v + affineEdge X q d θ z t (v+s) - affineEdge X q d θ z (s+t) v := by
  unfold affineMultiplier affineEdge
  rw [pullCochain_d,temporal_coboundary _ _ hz]
  simp only [add_assoc]
  rfl

end GeneralSphereT.Transport.Prism

