import Formalization.Transport.PrismChains

noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality
variable {Y : Type*}

theorem faces_ofFn {n : ℕ} (x : Fin (n+1) → Y) :
    faces (List.ofFn x) = ∑ j : Fin (n+1), ((-1:ℤ)^j.val) • gen (List.ofFn (fun i => x (j.succAbove i))) := by
  induction n with
  | zero => simp [List.ofFn_succ,faces]
  | succ n ih =>
    rw [List.ofFn_succ (f:=x),faces,ih,Fin.sum_univ_succ (fun j : Fin (n+2) =>
      ((-1:ℤ)^j.val) • gen (List.ofFn (fun i => x (j.succAbove i))))]
    simp only [Fin.val_zero,pow_zero,one_smul,Fin.zero_succAbove,Fin.val_succ,pow_succ,mul_neg,
      mul_one,neg_smul,Finset.sum_neg_distrib,map_sum,map_smul,sub_eq_add_neg]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    rw [cons_gen,List.ofFn_succ (f:=fun i => x (j.succ.succAbove i))]
    simp [Fin.succ_succAbove_zero]

/-- Extend a homogeneous cochain by zero in the other degrees. -/
def homogeneous {n : ℕ} (f : (Fin n → Y) → Phase) (xs : List Y) : Phase :=
  if h : xs.length = n then f (fun i => xs.get (i.cast h.symm)) else 0

@[simp] theorem homogeneous_ofFn {n : ℕ} (f : (Fin n → Y) → Phase) (x : Fin n → Y) :
    homogeneous f (List.ofFn x) = f x := by simp [homogeneous]

theorem homogeneous_ofFn_other {n k : ℕ} (f : (Fin n → Y) → Phase) (x : Fin k → Y)
    (hne : k ≠ n) : homogeneous f (List.ofFn x) = 0 := by simp [homogeneous,hne]

/-- The usual alternating face equation implies closedness on the entire
augmented list chain group, with no conditions in the other degrees. -/
theorem homogeneous_closed {n : ℕ} (f : (Fin n → Y) → Phase)
    (hc : ∀ x : Fin (n+1) → Y, ∑ j : Fin (n+1), ((-1:ℤ)^j.val) • f (fun i => x (j.succAbove i)) = 0) :
    (evaluate (homogeneous f)).comp boundary = 0 := by
  apply Finsupp.lhom_ext'
  intro xs
  apply LinearMap.ext_ring
  change evaluate (homogeneous f) (boundary (gen xs)) = 0
  cases xs with
  | nil => simp [faces]
  | cons y ys =>
    let x : Fin (ys.length+1) → Y := (y::ys).get
    have eq : List.ofFn x = y::ys := List.ofFn_get _
    rw [← eq,boundary_gen,faces_ofFn,map_sum]
    by_cases h : ys.length = n
    · subst n
      simpa [gen] using hc x
    · apply Finset.sum_eq_zero
      intro j _
      simp [gen,homogeneous_ofFn_other f _ h]

end GeneralSphereT.Transport.Prism

