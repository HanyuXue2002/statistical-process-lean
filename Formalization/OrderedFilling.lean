import Formalization.Cells
import Formalization.CoordinateRestriction

set_option linter.style.header false

/-!
# Filling the loop created by one elementary edge

This file isolates the algebra behind (2.28)--(2.31).  We do not
introduce a formal type of two-chains: `primitiveCellBoundaries` is the span
of the path boundaries of the two kinds of primitive cells.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

abbrev Config (ι G : Type*) [Zero G] := Configuration ι G

/-- The primitive cell boundaries: transverse squares and one-coordinate
triangles. -/
def primitiveCellBoundaryGenerators :
    Set (Path (Config ι G) (Config ι G)) :=
  {z | ∃ (i j : ι) (g h : G) (c : Config ι G),
      i ≠ j ∧
        z = square (AddMonoidHom.id (Config ι G))
          (Finsupp.single i g) (Finsupp.single j h) c} ∪
  {z | ∃ (i : ι) (g h : G) (c : Config ι G),
      z = triangle (AddMonoidHom.id (Config ι G))
        (Finsupp.single i g) (Finsupp.single i h) c}

/-- The submodule spanned by boundaries of primitive squares and triangles. -/
def primitiveCellBoundaries :
    Submodule ℤ (Path (Config ι G) (Config ι G)) :=
  Submodule.span ℤ (primitiveCellBoundaryGenerators (ι := ι) (G := G))

omit [LinearOrder ι] in
theorem square_mem_primitiveCellBoundaries {i j : ι} (hij : i ≠ j)
    (g h : G) (c : Config ι G) :
    square (AddMonoidHom.id (Config ι G))
        (Finsupp.single i g) (Finsupp.single j h) c ∈
      primitiveCellBoundaries (ι := ι) (G := G) := by
  apply Submodule.subset_span
  exact Or.inl ⟨i, j, g, h, c, hij, rfl⟩

omit [LinearOrder ι] in
theorem triangle_mem_primitiveCellBoundaries (i : ι) (g h : G)
    (c : Config ι G) :
    triangle (AddMonoidHom.id (Config ι G))
        (Finsupp.single i g) (Finsupp.single i h) c ∈
      primitiveCellBoundaries (ι := ι) (G := G) := by
  apply Submodule.subset_span
  exact Or.inr ⟨i, g, h, c, rfl⟩

/-- Ordered coordinate path using an arbitrary finite set of coordinates.
Coordinates on which `c` is zero contribute zero in `Path`. -/
def orderedPathOn (s : Finset ι) (c x : Config ι G) :
    Path (Config ι G) (Config ι G) :=
  ∑ j ∈ s,
    edge (Finsupp.single j (c j))
      (x + prefixSum s (fun k => Finsupp.single k (c k)) j)

/-- The configuration represented by the coordinate steps over `s`. -/
def coordinateSumOn (s : Finset ι) (c : Config ι G) : Config ι G :=
  ∑ j ∈ s, Finsupp.single j (c j)

theorem coordinateSumOn_insert {a : ι} {s : Finset ι} (ha : a ∉ s)
    (c : Config ι G) :
    coordinateSumOn (insert a s) c =
      coordinateSumOn s c + Finsupp.single a (c a) := by
  simp [coordinateSumOn, ha, add_comm]

/-- Splitting off the largest coordinate of an ordered path. -/
theorem orderedPathOn_insert_max {a : ι} {s : Finset ι}
    (hmax : ∀ b ∈ s, b < a) (c x : Config ι G) :
    orderedPathOn (insert a s) c x =
      orderedPathOn s c x +
        edge (Finsupp.single a (c a)) (x + coordinateSumOn s c) := by
  classical
  have ha : a ∉ s := by
    intro ha
    exact (lt_irrefl a) (hmax a ha)
  have hprefix_a :
      prefixSum (insert a s) (fun k => Finsupp.single k (c k)) a =
        coordinateSumOn s c := by
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
  have hprefix_old (j : ι) (hj : j ∈ s) :
      prefixSum (insert a s) (fun k => Finsupp.single k (c k)) j =
        prefixSum s (fun k => Finsupp.single k (c k)) j := by
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
  rw [orderedPathOn, Finset.sum_insert ha]
  rw [hprefix_a]
  have hold :
      (∑ j ∈ s,
          edge (Finsupp.single j (c j))
            (x + prefixSum (insert a s)
              (fun k => Finsupp.single k (c k)) j)) =
        orderedPathOn s c x := by
    rw [orderedPathOn]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hprefix_old j hj]
  rw [hold]
  abel_nf

/-- Adding a single coordinate outside `s` does not change the path over `s`. -/
theorem orderedPathOn_add_single_of_not_mem {a : ι} {s : Finset ι}
    (ha : a ∉ s) (c x : Config ι G) (g : G) :
    orderedPathOn s (c + Finsupp.single a g) x = orderedPathOn s c x := by
  classical
  unfold orderedPathOn
  apply Finset.sum_congr rfl
  intro j hj
  have hja : j ≠ a := by
    intro h
    exact ha (h ▸ hj)
  have hcj : (c + Finsupp.single a g) j = c j := by
    simp [hja]
  have hprefix :
      prefixSum s
          (fun k => Finsupp.single k ((c + Finsupp.single a g) k)) j =
        prefixSum s (fun k => Finsupp.single k (c k)) j := by
    unfold prefixSum
    apply Finset.sum_congr rfl
    intro k hk
    have hka : k ≠ a := by
      intro h
      exact ha (h ▸ (Finset.mem_filter.mp hk).1)
    simp [hka]
  rw [hcj, hprefix]

@[simp]
theorem coordinateSumOn_apply (s : Finset ι) (c : Config ι G) (j : ι) :
    coordinateSumOn s c j = if j ∈ s then c j else 0 := by
  classical
  simp [coordinateSumOn, Finsupp.single_apply]

theorem coordinateSumOn_add_single_of_mem {i : ι} {s : Finset ι}
    (hi : i ∈ s) (c : Config ι G) (g : G) :
    coordinateSumOn s (c + Finsupp.single i g) =
      coordinateSumOn s c + Finsupp.single i g := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [coordinateSumOn_apply, hji]

theorem coordinateSumOn_add_single_of_not_mem {i : ι} {s : Finset ι}
    (hi : i ∉ s) (c : Config ι G) (g : G) :
    coordinateSumOn s (c + Finsupp.single i g) = coordinateSumOn s c := by
  classical
  ext j
  by_cases hjs : j ∈ s
  · have hji : j ≠ i := by
      intro h
      exact hi (h ▸ hjs)
    simp [coordinateSumOn_apply, hjs, hji]
  · simp [coordinateSumOn_apply, hjs]

/-- The closed path obtained by appending one elementary edge and comparing
with the ordered path of the resulting configuration. -/
def edgeInsertionLoopOn (s : Finset ι) (c : Config ι G)
    (i : ι) (g : G) (x : Config ι G) :
    Path (Config ι G) (Config ι G) :=
  orderedPathOn s c x +
      edge (Finsupp.single i g) (x + coordinateSumOn s c) -
    orderedPathOn s (c + Finsupp.single i g) x

/-- The comparison loop over any finite coordinate set is generated by
transverse squares and one-coordinate triangles. -/
theorem edgeInsertionLoopOn_mem (s : Finset ι) {i : ι} (hi : i ∈ s)
    (c : Config ι G) (g : G) (x : Config ι G) :
    edgeInsertionLoopOn s c i g x ∈
      primitiveCellBoundaries (ι := ι) (G := G) := by
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
        exact triangle_mem_primitiveCellBoundaries i (c i) g
          (x + coordinateSumOn s c)
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
        rw [hloop]
        exact (primitiveCellBoundaries (ι := ι) (G := G)).add_mem
          (ih hi)
          (square_mem_primitiveCellBoundaries (ne_of_gt hia) (c a) g
            (x + coordinateSumOn s c))

theorem prefixSum_eq_coordinatePrefix_of_support_subset {s : Finset ι}
    {c : Config ι G} (hc : c.support ⊆ s) (j : ι) :
    prefixSum s (fun k => Finsupp.single k (c k)) j =
      coordinatePrefix c j := by
  classical
  ext k
  by_cases hks : k ∈ s
  · simp [prefixSum, coordinatePrefix_apply, hks,
      Finsupp.single_apply]
  · have hck : c k = 0 := by
      by_contra hne
      exact hks (hc (Finsupp.mem_support_iff.mpr hne))
    simp [prefixSum, coordinatePrefix_apply, hks, hck,
      Finsupp.single_apply]

/-- Adding zero coordinate terms to the indexing set does not change an
ordered path. -/
theorem orderedPathOn_eq_orderedPath {s : Finset ι} {c x : Config ι G}
    (hc : c.support ⊆ s) : orderedPathOn s c x = orderedPath c x := by
  classical
  rw [orderedPathOn, orderedPath]
  have hprefix (j : ι) :
      prefixSum s (fun k => Finsupp.single k (c k)) j =
        coordinatePrefix c j :=
    prefixSum_eq_coordinatePrefix_of_support_subset hc j
  simp_rw [hprefix]
  symm
  apply Finset.sum_subset hc
  intro j hjs hjc
  have hcj : c j = 0 := by
    by_contra hne
    exact hjc (Finsupp.mem_support_iff.mpr hne)
  simp [hcj]

theorem coordinateSumOn_eq_of_support_subset {s : Finset ι}
    {c : Config ι G} (hc : c.support ⊆ s) : coordinateSumOn s c = c := by
  classical
  ext j
  by_cases hjs : j ∈ s
  · simp [coordinateSumOn_apply, hjs]
  · have hcj : c j = 0 := by
      by_contra hne
      exact hjs (hc (Finsupp.mem_support_iff.mpr hne))
    simp [coordinateSumOn_apply, hjs, hcj]

theorem support_add_single_subset_insert (c : Config ι G) (i : ι) (g : G) :
    (c + Finsupp.single i g).support ⊆ insert i c.support := by
  classical
  intro j hj
  by_cases hji : j = i
  · simp [hji]
  · have hcj : c j ≠ 0 := by
      intro hcj
      have : (c + Finsupp.single i g) j = 0 := by
        simp [hcj, hji]
      exact (Finsupp.mem_support_iff.mp hj) this
    exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hcj)

/-- First independent milestone for (2.28)--(2.31): appending any elementary
edge to the canonical ordered path differs from the new canonical ordered
path by a span of primitive square and triangle boundaries. -/
theorem elementary_edge_ordered_loop_mem (c : Config ι G) (i : ι) (g : G) :
    orderedPath c 0 + edge (Finsupp.single i g) c -
        orderedPath (c + Finsupp.single i g) 0 ∈
      primitiveCellBoundaries (ι := ι) (G := G) := by
  classical
  let s : Finset ι := insert i c.support
  have hci : c.support ⊆ s := Finset.subset_insert i c.support
  have hcgi : (c + Finsupp.single i g).support ⊆ s :=
    support_add_single_subset_insert c i g
  have hmem := edgeInsertionLoopOn_mem (s := s)
    (i := i) (Finset.mem_insert_self i c.support) c g 0
  rw [edgeInsertionLoopOn,
    orderedPathOn_eq_orderedPath hci,
    coordinateSumOn_eq_of_support_subset hci,
    orderedPathOn_eq_orderedPath hcgi] at hmem
  simpa using hmem

omit [LinearOrder ι] in
/-- Every primitive cell boundary is a closed primitive path. -/
theorem primitiveCellBoundaries_le_boundary_ker :
    primitiveCellBoundaries (ι := ι) (G := G) ≤
      LinearMap.ker (primitiveBoundary (Config ι G)) := by
  rw [primitiveCellBoundaries, Submodule.span_le]
  rintro z (hz | hz)
  · rcases hz with ⟨i, j, g, h, c, hij, rfl⟩
    simp
  · rcases hz with ⟨i, g, h, c, rfl⟩
    simp

end GeneralSphereT.PathAlgebra
