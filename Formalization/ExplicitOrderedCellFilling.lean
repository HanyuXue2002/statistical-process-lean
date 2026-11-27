import Formalization.PrimitiveCellChains
import Formalization.OrderedFilling

set_option linter.style.header false

/-!
# An explicit two-chain filling the ordered elementary-edge loop

The span-membership theorem in `OrderedFilling` is sharpened here to one
explicit primitive two-chain.  Its triangle combines the old and new pieces
in coordinate `i`; one transverse square moves the new edge leftward across
each later nonzero coordinate of `c`.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- The square cell which moves the new `i`-edge past coordinate `j`.  It is
zero unless `i < j`; in the nonzero case its orientation is `(j,i)`. -/
def orderedSquareCell (c : Config ι G) (i : ι) (g : G) (j : ι) :
    PrimitiveCellChain₂ ι G :=
  if hij : i < j then
    primitiveCellGenerator
      (.transverseSquare j i (ne_of_gt hij) (c j) g)
      (coordinatePrefix c j)
  else 0

/-- The explicit primitive two-chain filling the comparison loop for one
elementary edge. -/
def explicitOrderedCellFilling (c : Config ι G) (i : ι) (g : G) :
    PrimitiveCellChain₂ ι G :=
  primitiveCellGenerator (.sameCoordinateTriangle i (c i) g)
      (coordinatePrefix c i) +
    ∑ j ∈ c.support, orderedSquareCell c i g j

/-- Path expression which is visibly the boundary of
`explicitOrderedCellFilling`. -/
def explicitOrderedCellBoundary (c : Config ι G) (i : ι) (g : G) :
    Path (Config ι G) (Config ι G) :=
  triangle (AddMonoidHom.id (Config ι G))
      (Finsupp.single i (c i)) (Finsupp.single i g)
      (coordinatePrefix c i) +
    ∑ j ∈ c.support,
      if i < j then
        square (AddMonoidHom.id (Config ι G))
          (Finsupp.single j (c j)) (Finsupp.single i g)
          (coordinatePrefix c j)
      else 0

/-- Taking the explicit degree-two boundary merely forgets the cell tags. -/
theorem primitiveCellBoundary₂_explicitOrderedCellFilling
    (c : Config ι G) (i : ι) (g : G) :
    primitiveCellBoundary₂ (explicitOrderedCellFilling c i g) =
      explicitOrderedCellBoundary c i g := by
  classical
  simp only [explicitOrderedCellFilling, explicitOrderedCellBoundary, map_add,
    map_sum, primitiveCellBoundary₂_primitiveCellGenerator]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold orderedSquareCell
  by_cases hij : i < j
  · simp [hij, primitiveCellBoundaryGenerator]
  · simp [hij]

/-- Finite-set version of the same boundary expression.  It is useful because
the proof can remove the largest coordinate exactly as the ordered path does. -/
def explicitOrderedCellBoundaryOn (s : Finset ι) (c : Config ι G)
    (i : ι) (g : G) (x : Config ι G) :
    Path (Config ι G) (Config ι G) :=
  triangle (AddMonoidHom.id (Config ι G))
      (Finsupp.single i (c i)) (Finsupp.single i g)
      (x + prefixSum s (fun k => Finsupp.single k (c k)) i) +
    ∑ j ∈ s,
      if i < j then
        square (AddMonoidHom.id (Config ι G))
          (Finsupp.single j (c j)) (Finsupp.single i g)
          (x + prefixSum s (fun k => Finsupp.single k (c k)) j)
      else 0

theorem prefixSum_insert_max_self {a : ι} {s : Finset ι}
    (hmax : ∀ j ∈ s, j < a) (c : Config ι G) :
    prefixSum (insert a s) (fun k => Finsupp.single k (c k)) a =
      coordinateSumOn s c := by
  classical
  have ha : a ∉ s := by
    intro ha
    exact (lt_irrefl a) (hmax a ha)
  have hfilter : (insert a s).filter (fun j => j < a) = s := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hj, hja⟩
      rcases hj with rfl | hj
      · exact (lt_irrefl _ hja).elim
      · exact hj
    · intro hj
      exact ⟨Or.inr hj, hmax j hj⟩
  simp [prefixSum, coordinateSumOn, hfilter]

theorem prefixSum_insert_max_of_mem {a : ι} {s : Finset ι}
    (hmax : ∀ j ∈ s, j < a) (c : Config ι G)
    {j : ι} (hj : j ∈ s) :
    prefixSum (insert a s) (fun k => Finsupp.single k (c k)) j =
      prefixSum s (fun k => Finsupp.single k (c k)) j := by
  classical
  have haj : ¬a < j := not_lt_of_ge (hmax j hj).le
  have hfilter : (insert a s).filter (fun k => k < j) =
      s.filter (fun k => k < j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hk, hkj⟩
      rcases hk with rfl | hk
      · exact (haj hkj).elim
      · exact ⟨hk, hkj⟩
    · rintro ⟨hk, hkj⟩
      exact ⟨Or.inr hk, hkj⟩
  simp [prefixSum, hfilter]

/-- The explicit finite-set boundary is exactly the loop obtained by inserting
the new elementary edge. -/
theorem edgeInsertionLoopOn_eq_explicitOrderedCellBoundaryOn
    (s : Finset ι) {i : ι} (hi : i ∈ s)
    (c : Config ι G) (g : G) (x : Config ι G) :
    edgeInsertionLoopOn s c i g x =
      explicitOrderedCellBoundaryOn s c i g x := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp at hi
  | @insert a s hmax ih =>
      have ha : a ∉ s := by
        intro ha
        exact (lt_irrefl a) (hmax a ha)
      rcases Finset.mem_insert.mp hi with hia | hi
      · subst a
        have hpath := orderedPathOn_insert_max
          (c := c) (x := x) hmax
        have hpath' := orderedPathOn_insert_max
          (c := c + Finsupp.single i g) (x := x) hmax
        have hloop :
            edgeInsertionLoopOn (insert i s) c i g x =
              triangle (AddMonoidHom.id (Config ι G))
                (Finsupp.single i (c i)) (Finsupp.single i g)
                (x + coordinateSumOn s c) := by
          rw [edgeInsertionLoopOn, hpath, hpath']
          rw [coordinateSumOn_insert ha]
          rw [orderedPathOn_add_single_of_not_mem ha]
          rw [coordinateSumOn_add_single_of_not_mem ha]
          simp only [triangle, AddMonoidHom.id_apply]
          simp
          abel_nf
        rw [hloop]
        unfold explicitOrderedCellBoundaryOn
        rw [prefixSum_insert_max_self hmax]
        rw [Finset.sum_insert ha]
        have hsquares :
            (∑ j ∈ s,
                if i < j then
                  square (AddMonoidHom.id (Config ι G))
                    (Finsupp.single j (c j)) (Finsupp.single i g)
                    (x + prefixSum (insert i s)
                      (fun k => Finsupp.single k (c k)) j)
                else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hji : ¬i < j := not_lt_of_ge (hmax j hj).le
          simp [hji]
        rw [hsquares]
        simp
      · have hia : i < a := hmax i hi
        have hpath := orderedPathOn_insert_max
          (c := c) (x := x) hmax
        have hpath' := orderedPathOn_insert_max
          (c := c + Finsupp.single i g) (x := x) hmax
        have hloop :
            edgeInsertionLoopOn (insert a s) c i g x =
              edgeInsertionLoopOn s c i g x +
                square (AddMonoidHom.id (Config ι G))
                  (Finsupp.single a (c a)) (Finsupp.single i g)
                  (x + coordinateSumOn s c) := by
          rw [edgeInsertionLoopOn, hpath, hpath']
          rw [coordinateSumOn_insert ha]
          rw [coordinateSumOn_add_single_of_mem hi]
          have hai : a ≠ i := ne_of_gt hia
          simp only [edgeInsertionLoopOn, square, AddMonoidHom.id_apply]
          simp [hai]
          abel_nf
        rw [hloop, ih hi]
        unfold explicitOrderedCellBoundaryOn
        rw [Finset.sum_insert ha]
        rw [prefixSum_insert_max_self hmax]
        simp only [hia, ↓reduceIte]
        have hprefix_i := prefixSum_insert_max_of_mem hmax c hi
        rw [hprefix_i]
        have hsquares :
            (∑ j ∈ s,
                if i < j then
                  square (AddMonoidHom.id (Config ι G))
                    (Finsupp.single j (c j)) (Finsupp.single i g)
                    (x + prefixSum (insert a s)
                      (fun k => Finsupp.single k (c k)) j)
                else 0) =
              ∑ j ∈ s,
                if i < j then
                  square (AddMonoidHom.id (Config ι G))
                    (Finsupp.single j (c j)) (Finsupp.single i g)
                    (x + prefixSum s
                      (fun k => Finsupp.single k (c k)) j)
                else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [prefixSum_insert_max_of_mem hmax c hj]
        rw [hsquares]
        abel_nf

/-- Main explicit milestone: the displayed primitive two-chain has precisely
the ordered elementary-edge comparison loop as its boundary. -/
theorem primitiveCellBoundary₂_explicitOrderedCellFilling_eq_loop
    (c : Config ι G) (i : ι) (g : G) :
    primitiveCellBoundary₂ (explicitOrderedCellFilling c i g) =
      orderedPath c 0 + edge (Finsupp.single i g) c -
        orderedPath (c + Finsupp.single i g) 0 := by
  classical
  rw [primitiveCellBoundary₂_explicitOrderedCellFilling]
  let s : Finset ι := insert i c.support
  have hci : c.support ⊆ s := Finset.subset_insert i c.support
  have hcgi : (c + Finsupp.single i g).support ⊆ s :=
    support_add_single_subset_insert c i g
  have hloop := edgeInsertionLoopOn_eq_explicitOrderedCellBoundaryOn
    (s := s) (i := i) (Finset.mem_insert_self i c.support) c g 0
  rw [edgeInsertionLoopOn,
    orderedPathOn_eq_orderedPath hci,
    coordinateSumOn_eq_of_support_subset hci,
    orderedPathOn_eq_orderedPath hcgi] at hloop
  have hexplicit :
      explicitOrderedCellBoundaryOn s c i g 0 =
        explicitOrderedCellBoundary c i g := by
    unfold explicitOrderedCellBoundaryOn explicitOrderedCellBoundary
    rw [prefixSum_eq_coordinatePrefix_of_support_subset hci]
    have hsquares :
        (∑ j ∈ s,
            if i < j then
              square (AddMonoidHom.id (Config ι G))
                (Finsupp.single j (c j)) (Finsupp.single i g)
                (prefixSum s (fun k => Finsupp.single k (c k)) j)
            else 0) =
          ∑ j ∈ c.support,
            if i < j then
              square (AddMonoidHom.id (Config ι G))
                (Finsupp.single j (c j)) (Finsupp.single i g)
                (coordinatePrefix c j)
            else 0 := by
      have hprefix :
          (∑ j ∈ s,
              if i < j then
                square (AddMonoidHom.id (Config ι G))
                  (Finsupp.single j (c j)) (Finsupp.single i g)
                  (prefixSum s (fun k => Finsupp.single k (c k)) j)
              else 0) =
            ∑ j ∈ s,
              if i < j then
                square (AddMonoidHom.id (Config ι G))
                  (Finsupp.single j (c j)) (Finsupp.single i g)
                  (coordinatePrefix c j)
              else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [prefixSum_eq_coordinatePrefix_of_support_subset hci]
      rw [hprefix]
      symm
      apply Finset.sum_subset hci
      intro j hjs hjSupport
      have hji : j = i := by
        change j ∈ insert i c.support at hjs
        rcases Finset.mem_insert.mp hjs with hji | hjc
        · exact hji
        · exact (hjSupport hjc).elim
      subst j
      simp
    simp only [zero_add]
    rw [hsquares]
  calc
    explicitOrderedCellBoundary c i g =
        explicitOrderedCellBoundaryOn s c i g 0 := hexplicit.symm
    _ = orderedPath c 0 + edge (Finsupp.single i g) c -
        orderedPath (c + Finsupp.single i g) 0 := by
      simpa using hloop.symm

end GeneralSphereT.PathAlgebra
