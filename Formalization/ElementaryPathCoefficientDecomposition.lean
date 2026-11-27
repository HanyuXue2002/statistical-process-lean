import Formalization.OperatorCoefficients
import Formalization.Section3SquareStripLocality

set_option linter.style.header false

/-!
# Grouping an elementary path by its complete nonzero label

An elementary path is a finite sum of edges with nonzero one-coordinate
labels.  This module collects all bases carrying the same complete oriented
label into the coefficient distribution extracted by `pathCoefficient`, and
then reconstructs the path by a finite sum over labels.

The auxiliary `totalPathCoefficient` is canonically zero at the zero label.
It lets the reconstruction be stated over an ordinary `Finset` without
making the summand depend on a chosen proof that each label is nonzero.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

section EdgeDistribution

variable {I X : Type*} [AddCommGroup I]

local instance decompositionDecidableEqI : DecidableEq I := Classical.decEq I

/-- Turn a distribution of bases into the path with one fixed edge label. -/
def edgeDistribution (r : I) : Dist X →ₗ[ℤ] Path I X :=
  Finsupp.linearCombination ℤ fun x => edge r x

@[simp]
theorem edgeDistribution_single (r : I) (x : X) (z : ℤ) :
    edgeDistribution r (Finsupp.single x z) = z • edge r x := by
  simp [edgeDistribution]

@[simp]
theorem edgeDistribution_single_one (r : I) (x : X) :
    edgeDistribution r (Finsupp.single x 1) = edge r x := by
  simp

/-- The fixed-label extractor, extended canonically by zero at the forbidden
zero label. -/
def totalPathCoefficient (r : I) : Path I X →ₗ[ℤ] Dist X :=
  if hr : r ≠ 0 then pathCoefficient r hr else 0

@[simp]
theorem totalPathCoefficient_of_ne (r : I) (hr : r ≠ 0) :
    totalPathCoefficient (X := X) r = pathCoefficient r hr := by
  simp [totalPathCoefficient, hr]

@[simp]
theorem totalPathCoefficient_zero :
    totalPathCoefficient (X := X) (0 : I) = 0 := by
  simp [totalPathCoefficient]

@[simp]
theorem totalPathCoefficient_edge_self (r : I) (hr : r ≠ 0) (x : X) :
    totalPathCoefficient r (edge r x) = Finsupp.single x 1 := by
  rw [totalPathCoefficient_of_ne r hr]
  simp

@[simp]
theorem totalPathCoefficient_edge_of_ne
    (r : I) (hr : r ≠ 0) {s : I} (hsr : s ≠ r) (x : X) :
    totalPathCoefficient r (edge s x) = 0 := by
  rw [totalPathCoefficient_of_ne r hr]
  exact pathCoefficient_edge_of_ne r hr hsr x

end EdgeDistribution

section ElementaryDecomposition

variable {ι G X : Type*}
variable [LinearOrder ι] [AddCommGroup G]

/--
Every elementary path has finite complete-label support.  All labels in the
chosen support are nonzero and elementary; outside it every nonzero-label
coefficient distribution vanishes; summing the collected distributions
reconstructs the original path.

The support need not be minimal.  This makes the statement stable under
addition and scalar multiplication while retaining exactly the information
needed for simultaneous label replacement.
-/
theorem elementaryPath_exists_label_decomposition
    (p : Path (Configuration ι G) X)
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := X)) :
    ∃ S : Finset (Configuration ι G),
      (∀ r ∈ S, r ≠ 0 ∧ IsElementaryLabel r) ∧
      (∀ (r : Configuration ι G) (hr : r ≠ 0), r ∉ S →
        pathCoefficient r hr p = 0) ∧
      p = ∑ r ∈ S,
        edgeDistribution r (totalPathCoefficient r p) := by
  classical
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (x : X),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) x} at hp
  induction hp using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨i, g, x, hg, rfl⟩
      let r : Configuration ι G := Finsupp.single i g
      have hr : r ≠ 0 := by simp [r, hg]
      refine ⟨{r}, ?_, ?_, ?_⟩
      · intro s hs
        have hsr : s = r := Finset.mem_singleton.mp hs
        subst s
        exact ⟨hr, ⟨i, g, hg, rfl⟩⟩
      · intro s hs hsnot
        have hrs : r ≠ s := by
          intro hrs
          apply hsnot
          simp [hrs]
        exact pathCoefficient_edge_of_ne s hs hrs x
      · simp [r, hr]
  | zero =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · simp
      · intro r hr hrnot
        simp
      · simp
  | add p q hp hq ihp ihq =>
      rcases ihp with ⟨S, hSelem, hSzero, hSrec⟩
      rcases ihq with ⟨T, hTelem, hTzero, hTrec⟩
      have hUelem :
          ∀ r ∈ S ∪ T, r ≠ 0 ∧ IsElementaryLabel r := by
        intro r hr
        rcases Finset.mem_union.mp hr with hrS | hrT
        · exact hSelem r hrS
        · exact hTelem r hrT
      refine ⟨S ∪ T, hUelem, ?_, ?_⟩
      · intro r hr hrnot
        have hrS : r ∉ S := fun h => hrnot (Finset.mem_union_left T h)
        have hrT : r ∉ T := fun h => hrnot (Finset.mem_union_right S h)
        rw [map_add, hSzero r hr hrS, hTzero r hr hrT, add_zero]
      · have hsumP :
            (∑ r ∈ S,
                edgeDistribution r (totalPathCoefficient r p)) =
              ∑ r ∈ S ∪ T,
                edgeDistribution r (totalPathCoefficient r p) := by
          apply Finset.sum_subset (Finset.subset_union_left)
          intro r hrU hrS
          have hr : r ≠ 0 := (hUelem r hrU).1
          rw [totalPathCoefficient_of_ne r hr, hSzero r hr hrS]
          simp
        have hsumQ :
            (∑ r ∈ T,
                edgeDistribution r (totalPathCoefficient r q)) =
              ∑ r ∈ S ∪ T,
                edgeDistribution r (totalPathCoefficient r q) := by
          apply Finset.sum_subset (Finset.subset_union_right)
          intro r hrU hrT
          have hr : r ≠ 0 := (hUelem r hrU).1
          rw [totalPathCoefficient_of_ne r hr, hTzero r hr hrT]
          simp
        calc
          p + q =
              (∑ r ∈ S,
                edgeDistribution r (totalPathCoefficient r p)) +
              ∑ r ∈ T,
                edgeDistribution r (totalPathCoefficient r q) := by
            rw [← hSrec, ← hTrec]
          _ =
              (∑ r ∈ S ∪ T,
                edgeDistribution r (totalPathCoefficient r p)) +
              ∑ r ∈ S ∪ T,
                edgeDistribution r (totalPathCoefficient r q) := by
            rw [hsumP, hsumQ]
          _ = ∑ r ∈ S ∪ T,
              (edgeDistribution r (totalPathCoefficient r p) +
                edgeDistribution r (totalPathCoefficient r q)) := by
            rw [Finset.sum_add_distrib]
          _ = ∑ r ∈ S ∪ T,
              edgeDistribution r (totalPathCoefficient r (p + q)) := by
            apply Finset.sum_congr rfl
            intro r hr
            simp
  | smul z p hp ih =>
      rcases ih with ⟨S, hSelem, hSzero, hSrec⟩
      refine ⟨S, hSelem, ?_, ?_⟩
      · intro r hr hrS
        rw [map_smul, hSzero r hr hrS, smul_zero]
      · calc
          z • p = z • ∑ r ∈ S,
              edgeDistribution r (totalPathCoefficient r p) := by
            rw [← hSrec]
          _ = ∑ r ∈ S,
              z • edgeDistribution r (totalPathCoefficient r p) := by
            rw [Finset.smul_sum]
          _ = ∑ r ∈ S,
              edgeDistribution r (totalPathCoefficient r (z • p)) := by
            apply Finset.sum_congr rfl
            intro r hr
            simp

/-- A proof-relevant presentation of the same decomposition, with the
original `pathCoefficient` appearing literally in the sum.  The nonzero proof
is part of the returned support data, so no choice of proofs or labels is
hidden in the construction. -/
theorem elementaryPath_exists_pathCoefficient_decomposition
    (p : Path (Configuration ι G) X)
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := X)) :
    ∃ (S : Finset (Configuration ι G))
        (hS : ∀ r ∈ S, r ≠ 0 ∧ IsElementaryLabel r),
      (∀ (r : Configuration ι G) (hr : r ≠ 0), r ∉ S →
        pathCoefficient r hr p = 0) ∧
      p = ∑ r : S,
        edgeDistribution r.1
          (pathCoefficient r.1 (hS r.1 r.2).1 p) := by
  obtain ⟨S, hS, hzero, hrec⟩ :=
    elementaryPath_exists_label_decomposition p hp
  refine ⟨S, hS, hzero, ?_⟩
  calc
    p = ∑ r ∈ S,
        edgeDistribution r (totalPathCoefficient r p) := hrec
    _ = ∑ r : S,
        edgeDistribution r.1 (totalPathCoefficient r.1 p) := by
      exact (Finset.sum_coe_sort S fun r =>
        edgeDistribution r (totalPathCoefficient r p)).symm
    _ = ∑ r : S,
        edgeDistribution r.1
          (pathCoefficient r.1 (hS r.1 r.2).1 p) := by
      apply Fintype.sum_congr
      intro r
      rw [totalPathCoefficient_of_ne r.1 (hS r.1 r.2).1]

end ElementaryDecomposition

end GeneralSphereT.PathAlgebra
