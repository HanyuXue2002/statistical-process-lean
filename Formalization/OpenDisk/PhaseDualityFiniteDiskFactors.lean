import Formalization.Section4CochainDoldKanChainMaps
import Mathlib.Algebra.Homology.Homotopy

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Finite disk factorization of actual chain nullhomotopies

Every bounded chain nullhomotopy is a finite sum of maps which factor
through the actual two-term identity disk complexes.  This supplies the
concrete input needed to reflect chain homotopy into native simplicial
homotopy using the already constructed Dold--Kan disk contractions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open GeneralSphereT.SimplicialCochain GeneralSphereT.StandardModels
open scoped BigOperators

namespace OpenDisk.DiskFactors

universe u
variable (C A : ChainComplex AddCommGrpCat.{u} ℕ)

/-- The disk has a canonical map to `A`, identity on the upper degree. -/
def diskOut (n : ℕ) : diskComplex (A.X (n + 1)) (n + 1) ⟶ A :=
  mkHomFromDouble (ComplexShape.down_mk (n + 1) n rfl) (by omega)
    (𝟙 _) (A.d (n + 1) n) (by simp) (by intro k hk; simp)

/-- Any degreewise homomorphism extends to a map into the identity disk. -/
def diskInto (B : AddCommGrpCat.{u}) (n : ℕ) (h : C.X n ⟶ B) :
    C ⟶ HomologicalComplex.double (𝟙 B) (ComplexShape.down_mk (n + 1) n rfl) where
  f i := if hi : i = n + 1 then
    (C.XIsoOfEq hi).hom ≫ C.d (n + 1) n ≫ h ≫
      (doubleXIso₀ (𝟙 B) (ComplexShape.down_mk (n + 1) n rfl)).inv ≫
        eqToHom (by rw [hi])
    else if hi' : i = n then
      (C.XIsoOfEq hi').hom ≫ h ≫
        (doubleXIso₁ (𝟙 B) (ComplexShape.down_mk (n + 1) n rfl) (by omega)).inv ≫
          eqToHom (by rw [hi'])
    else 0
  comm' i j hij := by
    have hrel : j + 1 = i := by simpa only [ComplexShape.down_Rel] using hij
    by_cases hi : i = n + 1
    · subst i
      have hj : j = n := by omega
      subst j
      simp [diskComplex, double_d]
      <;> rfl
    · rw [double_d_eq_zero₀ _ _ _ _ hi, comp_zero]
      by_cases hj : j = n + 1
      · subst j
        simp
        change 0 = C.d i (n + 1) ≫ C.d (n + 1) n ≫ h ≫ _
        rw [← Category.assoc, C.d_comp_d, zero_comp, zero_comp]
      · have hj' : j ≠ n := by omega
        simp [hj, hj']

/-- One elementary summand of a chain nullhomotopy, with its actual disk factorization. -/
def factor (n : ℕ) (h : C.X n ⟶ A.X (n + 1)) : C ⟶ A :=
  diskInto C (A.X (n + 1)) n h ≫ diskOut A n

theorem factor_bottom (n : ℕ) (h : C.X n ⟶ A.X (n + 1)) :
    (factor C A n h).f n = h ≫ A.d (n + 1) n := by
  simp [factor, diskInto, diskOut, Category.assoc]

theorem factor_top (n : ℕ) (h : C.X n ⟶ A.X (n + 1)) :
    (factor C A n h).f (n + 1) = C.d (n + 1) n ≫ h := by
  simp [factor, diskInto, diskOut, Category.assoc]

theorem factor_other (n m : ℕ) (h : C.X n ⟶ A.X (n + 1))
    (hm : m ≠ n) (hm' : m ≠ n + 1) : (factor C A n h).f m = 0 := by
  simp [factor, diskInto, hm, hm']

variable {C A}

theorem factor_zero (h : ∀ n, C.X n ⟶ A.X (n + 1)) (k : ℕ) :
    (factor C A k (h k)).f 0 = if k = 0 then h 0 ≫ A.d 1 0 else 0 := by
  by_cases hk : k = 0
  · subst k; simp [factor_bottom]
  · rw [factor_other C A k 0 _ (Ne.symm hk) (by omega), if_neg hk]

theorem factor_succ (h : ∀ n, C.X n ⟶ A.X (n + 1)) (k m : ℕ) :
    (factor C A k (h k)).f (m + 1) =
      (if k = m then C.d (m + 1) m ≫ h m else 0) +
        (if k = m + 1 then h (m + 1) ≫ A.d (m + 2) (m + 1) else 0) := by
  by_cases hk : k = m
  · subst k; simp [factor_top]
  · by_cases hk' : k = m + 1
    · subst k; simp [factor_bottom]
    · rw [factor_other C A k (m + 1) _ (Ne.symm hk') (by omega)]
      simp [hk, hk']

theorem sum_f {ι : Type*} (s : Finset ι) (f : ι → (C ⟶ A)) (m : ℕ) :
    (∑ i ∈ s, f i).f m = ∑ i ∈ s, (f i).f m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, HomologicalComplex.add_f_apply]

/-- A genuinely bounded nullhomotopy gives a finite sum of genuine disk factors. -/
theorem eq_sum_factors_of_nullhomotopy {f : C ⟶ A} (H : Homotopy f 0)
    (N : ℕ) (hbound : ∀ m, N ≤ m → H.hom m (m + 1) = 0) :
    f = ∑ k ∈ Finset.range N, factor C A k (H.hom k (k + 1)) := by
  classical
  apply HomologicalComplex.hom_ext
  intro m
  rw [sum_f]
  have hf := H.comm m
  cases m with
  | zero =>
      simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        HomologicalComplex.zero_f_apply, add_zero, zero_add] at hf
      simp_rw [factor_zero]
      rw [hf]
      by_cases hn : 0 < N
      · simp [hn]
      · have hz := hbound 0 (by omega)
        simp [hn, hz]
  | succ m =>
      simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        HomologicalComplex.zero_f_apply, add_zero] at hf
      simp_rw [factor_succ]
      rw [Finset.sum_add_distrib, hf]
      by_cases hm : m < N <;> by_cases hm' : m + 1 < N
      · simp [hm, hm']
      · simp [hm, hm', hbound (m + 1) (by omega)]
      · omega
      · simp [hm, hm', hbound m (by omega), hbound (m + 1) (by omega)]

section FiniteSimplicialSource

variable {V : Type u} [LinearOrder V] [Fintype V]
variable (K : AbstractSimplicialComplex V)

/-- There are no normalized chains above the actual finite vertex bound. -/
theorem normalized_hom_eq_zero_of_large (m : ℕ) (hm : Fintype.card V ≤ m)
    {B : AddCommGrpCat.{u}}
    (h : ((orderedComplexSSet K).normalizedChainComplex integralCoefficients).X m ⟶ B) :
    h = 0 := by
  apply (orderedComplexSSet K).normalizedChainComplex_hom_ext
  intro x hx
  have s := nonDegenerateSimplexEquiv K m ⟨x, hx⟩
  have hcard := Finset.card_le_univ s.1
  have hs := s.2.2
  omega

/-- Every chain nullhomotopy from the actual finite normalized source has
the finite disk factorization, without any extra boundedness hypothesis. -/
theorem normalized_eq_sum_factors_of_nullhomotopy
    {f : (orderedComplexSSet K).normalizedChainComplex integralCoefficients ⟶ A}
    (H : Homotopy f 0) :
    f = ∑ k ∈ Finset.range (Fintype.card V), factor _ A k (H.hom k (k + 1)) :=
  eq_sum_factors_of_nullhomotopy H _
    (fun m hm => normalized_hom_eq_zero_of_large K m hm _)

end FiniteSimplicialSource
end OpenDisk.DiskFactors
