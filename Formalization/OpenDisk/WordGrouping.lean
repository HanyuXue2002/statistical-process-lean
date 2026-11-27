import Formalization.OpenDisk.WordOperators
import Init.Data.List.Nat.Basic

/-!
# Sorting actual hopping words without losing inverse or fusion phases

The alphabet can contain several operators with the same carrier and increment.
No representative is substituted for any letter. Adjacent swaps change the
full word phase by their actual square defect. Carrier blocks retain all of
their phases. This proves the grouping step used by the regional-algebra argument.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace OpenDisk
variable {C E : Type*} [AddCommGroup C]

theorem hoppingWordIncrement_append (xs ys : List (HoppingStep C)) :
    hoppingWordIncrement (xs ++ ys) = hoppingWordIncrement xs + hoppingWordIncrement ys := by
  induction xs with
  | nil => simp [hoppingWordIncrement]
  | cons a xs ih => simp [hoppingWordIncrement, ih, add_assoc]

theorem hoppingWordIncrement_eq_sum (xs : List (HoppingStep C)) :
    hoppingWordIncrement xs = (xs.map Prod.snd).sum := by
  induction xs <;> simp_all [hoppingWordIncrement]

theorem hoppingWordIncrement_perm {xs ys : List (HoppingStep C)} (h : xs.Perm ys) :
    hoppingWordIncrement xs = hoppingWordIncrement ys := by
  simp only [hoppingWordIncrement_eq_sum]
  exact (h.map Prod.snd).sum_eq

theorem hoppingWordPhase_append (xs ys : List (HoppingStep C)) (v : C) :
    hoppingWordPhase (xs ++ ys) v = hoppingWordPhase xs v +
      hoppingWordPhase ys (v + hoppingWordIncrement xs) := by
  induction xs generalizing v with
  | nil => simp [hoppingWordPhase, hoppingWordIncrement]
  | cons a xs ih => simp [hoppingWordPhase, hoppingWordIncrement, ih, add_assoc]

def hoppingSwapPhase (a b : HoppingStep C) : C → CirclePhase :=
  fun v => difference b.1 a.2 v - difference a.1 b.2 v

/-- Permuting letters changes the full phase only by translated square defects. -/
theorem hoppingWordPhase_sub_mem_of_perm (steps : E → HoppingStep C)
    (Good : AddSubgroup (C → CirclePhase))
    (htranslate : ∀ f ∈ Good, ∀ s : C, (fun v => f (v + s)) ∈ Good)
    (hswap : ∀ a b, hoppingSwapPhase (steps a) (steps b) ∈ Good)
    {xs ys : List E} (hperm : xs.Perm ys) :
    hoppingWordPhase (xs.map steps) - hoppingWordPhase (ys.map steps) ∈ Good := by
  induction hperm with
  | nil => simpa using Good.zero_mem
  | @cons a xs ys h ih =>
      have heq : hoppingWordPhase ((a :: xs).map steps) - hoppingWordPhase ((a :: ys).map steps) =
          (fun v => (hoppingWordPhase (xs.map steps) - hoppingWordPhase (ys.map steps))
            (v + (steps a).2)) := by
        funext v
        simp only [List.map_cons, hoppingWordPhase, Pi.sub_apply]
        abel
      rw [heq]
      exact htranslate _ ih _
  | swap a b word =>
      have heq : hoppingWordPhase ((b :: a :: word).map steps) -
          hoppingWordPhase ((a :: b :: word).map steps) =
          hoppingSwapPhase (steps b) (steps a) := by
        funext v
        simp only [List.map_cons, hoppingWordPhase, Pi.sub_apply, hoppingSwapPhase, difference]
        rw [show v + (steps b).2 + (steps a).2 = v + (steps a).2 + (steps b).2 by abel]
        abel
      rw [heq]
      exact hswap b a
  | @trans xs ys zs h₁ h₂ ih₁ ih₂ =>
      have heq : hoppingWordPhase (xs.map steps) - hoppingWordPhase (zs.map steps) =
          (hoppingWordPhase (xs.map steps) - hoppingWordPhase (ys.map steps)) +
          (hoppingWordPhase (ys.map steps) - hoppingWordPhase (zs.map steps)) := by abel
      rw [heq]
      exact Good.add_mem ih₁ ih₂

section Coordinates
open GeneralSphereT.PathAlgebra
variable {ι G : Type*} [AddCommGroup G] [DecidableEq ι]

def wordCoordinateProjection (i : ι) : Configuration ι G →+ Configuration ι G where
  toFun c := Finsupp.single i (c i)
  map_zero' := by simp
  map_add' x y := by simp [Finsupp.single_add]

theorem hoppingWordIncrement_filter_carrier (steps : E → HoppingStep (Configuration ι G))
    (carrier : E → ι) (amount : E → G)
    (hstep : ∀ e, (steps e).2 = Finsupp.single (carrier e) (amount e))
    (i : ι) (word : List E) :
    wordCoordinateProjection i (hoppingWordIncrement (word.map steps)) =
      hoppingWordIncrement ((word.filter (fun e => decide (carrier e = i))).map steps) := by
  classical
  induction word with
  | nil => simp [hoppingWordIncrement]
  | cons a word ih =>
      simp only [List.map_cons, hoppingWordIncrement, map_add, ih]
      by_cases ha : carrier a = i
      · simp [ha, List.filter_cons, hoppingWordIncrement, hstep, wordCoordinateProjection]
      · simp [ha, List.filter_cons, hoppingWordIncrement, hstep, wordCoordinateProjection, Ne.symm ha]

/-- The complete sorting argument: square defects and same-carrier closed blocks
suffice for every closed word, without forgetting any of its phase data. -/
theorem closed_hoppingWordPhase_mem (steps : E → HoppingStep (Configuration ι G))
    (carrier : E → ι) (amount : E → G)
    (hstep : ∀ e, (steps e).2 = Finsupp.single (carrier e) (amount e))
    (Good : AddSubgroup (Configuration ι G → CirclePhase))
    (htranslate : ∀ f ∈ Good, ∀ s, (fun v => f (v + s)) ∈ Good)
    (hswap : ∀ a b, hoppingSwapPhase (steps a) (steps b) ∈ Good)
    (hblock : ∀ (i : ι) (word : List E), (∀ e ∈ word, carrier e = i) →
      hoppingWordIncrement (word.map steps) = 0 → hoppingWordPhase (word.map steps) ∈ Good)
    (word : List E) (hclosed : hoppingWordIncrement (word.map steps) = 0) :
    hoppingWordPhase (word.map steps) ∈ Good := by
  classical
  suffices h : ∀ n (word : List E), word.length = n →
      hoppingWordIncrement (word.map steps) = 0 → hoppingWordPhase (word.map steps) ∈ Good from
    h word.length word rfl hclosed
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro word hlen hc
      cases word with
      | nil => exact Good.zero_mem
      | cons a tail =>
          let p : E → Bool := fun e => decide (carrier e = carrier a)
          let block := (a :: tail).filter p
          let rest := (a :: tail).filter (fun e => !p e)
          have hperm : (block ++ rest).Perm (a :: tail) := List.filter_append_perm p _
          have hb : hoppingWordIncrement (block.map steps) = 0 := by
            rw [← hoppingWordIncrement_filter_carrier steps carrier amount hstep (carrier a) (a :: tail), hc, map_zero]
          have hr : hoppingWordIncrement (rest.map steps) = 0 := by
            have hh := hoppingWordIncrement_perm (hperm.map steps)
            rw [List.map_append, hoppingWordIncrement_append, hb, hc, zero_add] at hh
            exact hh
          have hlenr : rest.length < n := by
            rw [← hlen]
            apply List.length_filter_lt_length_iff_exists.mpr
            exact ⟨a, List.mem_cons_self, by simp [p]⟩
          have hrest := ih rest.length hlenr rest rfl hr
          have hblock' : hoppingWordPhase (block.map steps) ∈ Good := by
            apply hblock (carrier a) block _ hb
            intro e he
            exact of_decide_eq_true (List.mem_filter.mp he).2
          have hparts : hoppingWordPhase ((block ++ rest).map steps) ∈ Good := by
            have heq : hoppingWordPhase ((block ++ rest).map steps) =
                hoppingWordPhase (block.map steps) + hoppingWordPhase (rest.map steps) := by
              funext v
              rw [List.map_append, hoppingWordPhase_append, hb, add_zero]
              rfl
            rw [heq]
            exact Good.add_mem hblock' hrest
          have hd := hoppingWordPhase_sub_mem_of_perm steps Good htranslate hswap hperm
          have hfinal := Good.sub_mem hparts hd
          convert hfinal using 1 <;> abel

end Coordinates
end OpenDisk
