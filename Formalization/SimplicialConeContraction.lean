import Formalization.SimplicialIncidenceSign

set_option linter.style.header false

/-!
# Cochain contraction of a simplicial closed star

For a nonempty simplex `η`, choose a vertex `v ∈ η`.  The closed star of `η`
is a cone with apex `v`.  This file proves the cochain contraction directly
from the ordered Finset incidence formulas used in `FiniteSimplicialCochain`.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Degree-`n` simplices in the closed star of `η`. -/
abbrev ClosedStarSimplex (η : {s : Finset V // s ∈ K}) (n : ℕ) :=
  {τ : Simplex K n // τ.1 ∪ η.1 ∈ K}

/-- Cochains on the closed star of `η`. -/
abbrev ClosedStarCochain (η : {s : Finset V // s ∈ K}) (n : ℕ)
    (G : Type*) [AddCommGroup G] :=
  GeneralSphereT.PathAlgebra.Configuration (ClosedStarSimplex K η n) G

/-- The ordered sign associated to a vertex in an arbitrary finite vertex set. -/
def orderedSign (s : Finset V) (v : V) : ℤ :=
  (-1 : ℤ) ^ (s.filter fun w => w < v).card

omit [Fintype V] in
theorem orderedSign_insert_self (s : Finset V) (v : V) :
    orderedSign (insert v s) v = orderedSign s v := by
  simp [orderedSign, Finset.filter_insert]

omit [Fintype V] in
theorem orderedSign_insert_of_lt (s : Finset V) {v w : V}
    (hvw : v < w) (hv : v ∉ s) :
    orderedSign (insert v s) w = -orderedSign s w := by
  rw [orderedSign, orderedSign, Finset.filter_insert]
  simp only [hvw, ↓reduceIte]
  have hvf : v ∉ s.filter fun x => x < w := by simp [hv]
  rw [Finset.card_insert_of_notMem hvf, pow_succ]
  ring

omit [Fintype V] in
theorem orderedSign_insert_of_gt (s : Finset V) {v w : V}
    (hwv : w < v) :
    orderedSign (insert v s) w = orderedSign s w := by
  simp [orderedSign, Finset.filter_insert, not_lt.mpr (le_of_lt hwv)]

omit [Fintype V] in
theorem orderedSign_erase_of_lt (s : Finset V) {v w : V}
    (hw : w ∈ s) (hwv : w < v) :
    orderedSign s v = -orderedSign (s.erase w) v := by
  rw [orderedSign, orderedSign, Finset.filter_erase]
  have hwf : w ∈ s.filter fun x => x < v := by simp [hw, hwv]
  have hcard : (s.filter fun x => x < v).card =
      ((s.filter fun x => x < v).erase w).card + 1 := by
    rw [Finset.card_erase_of_mem hwf]
    have hpos : 0 < (s.filter fun x => x < v).card :=
      Finset.card_pos.mpr ⟨w, hwf⟩
    omega
  rw [hcard, pow_succ]
  ring

omit [Fintype V] in
theorem orderedSign_erase_of_gt (s : Finset V) {v w : V}
    (hwv : v < w) :
    orderedSign (s.erase w) v = orderedSign s v := by
  rw [orderedSign, orderedSign, Finset.filter_erase]
  have hwf : w ∉ s.filter fun x => x < v := by
    simp [not_lt.mpr (le_of_lt hwv)]
  rw [Finset.erase_eq_of_notMem hwf]

/-- The two non-apex terms associated to deleting `w` occur with opposite
incidence signs. -/
theorem orderedSign_insert_erase_cancellation (s : Finset V)
    {v w : V} (hv : v ∉ s) (hw : w ∈ s) :
    orderedSign s w * orderedSign (insert v (s.erase w)) v =
      -(orderedSign (insert v s) v * orderedSign (insert v s) w) := by
  have hvw : v ≠ w := by
    intro h
    exact hv (h ▸ hw)
  rcases lt_or_gt_of_ne hvw with hvw | hwv
  · rw [orderedSign_insert_self, orderedSign_insert_self,
      orderedSign_insert_of_lt s hvw hv,
      orderedSign_erase_of_gt s hvw]
    ring
  · rw [orderedSign_insert_self, orderedSign_insert_self,
      orderedSign_insert_of_gt s hwv,
      orderedSign_erase_of_lt s hw hwv]
    ring

omit [Fintype V] in
@[simp]
theorem incidenceSign_eq_orderedSign {n : ℕ}
    (τ : Simplex K (n + 1)) (v : V) :
    incidenceSign K τ v = orderedSign τ.1 v :=
  rfl

/-- The non-apex vertices of `insert v s` are canonically the vertices of
`s`. -/
def insertRemainderEquiv {A : Type*} [DecidableEq A]
    (s : Finset A) (v : A) (hv : v ∉ s) :
    s ≃ {x : ↥(insert v s) // x ≠ ⟨v, Finset.mem_insert_self v s⟩} where
  toFun x := ⟨⟨x.1, Finset.mem_insert_of_mem x.2⟩, by
    intro h
    have hx : x.1 = v := congrArg Subtype.val h
    exact hv (hx ▸ x.2)⟩
  invFun x := ⟨x.1.1, by
    rcases Finset.mem_insert.mp x.1.2 with hx | hx
    · exfalso
      apply x.2
      apply Subtype.ext
      exact hx
    · exact hx⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Split a sum over the vertices of `insert v s` into its apex term and the
sum over the old vertices. -/
theorem sum_insert_subtype {A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (s : Finset A) (v : A) (hv : v ∉ s) (f : ↥(insert v s) → M) :
    (∑ x : ↥(insert v s), f x) =
      f ⟨v, Finset.mem_insert_self v s⟩ +
        ∑ x : s, f ⟨x.1, Finset.mem_insert_of_mem x.2⟩ := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f
    ⟨v, Finset.mem_insert_self v s⟩]
  congr 1
  symm
  apply Fintype.sum_equiv (insertRemainderEquiv s v hv)
  intro x
  rfl

/-- Erasing a vertex preserves membership in the closed star. -/
def eraseClosedStarVertex {η : {s : Finset V // s ∈ K}} {n : ℕ}
    (τ : ClosedStarSimplex K η (n + 1)) (w : V) (hw : w ∈ τ.1.1) :
    ClosedStarSimplex K η n := by
  let e : Simplex K n := eraseVertex K τ.1 w hw
  refine ⟨e, ?_⟩
  apply (K.isRelLowerSet_faces τ.2).2
  · intro x hx
    simp only [e, eraseVertex, Finset.mem_union, Finset.mem_erase] at hx ⊢
    exact hx.elim (fun h => Or.inl h.2) Or.inr
  · exact (K.isRelLowerSet_faces η.2).1.mono
      Finset.subset_union_right

/-- Insert the chosen apex into a star simplex which does not already contain
it. -/
def insertClosedStarVertex {η : {s : Finset V // s ∈ K}} {n : ℕ}
    (v : V) (hvη : v ∈ η.1) (τ : ClosedStarSimplex K η n)
    (hvτ : v ∉ τ.1.1) : ClosedStarSimplex K η (n + 1) := by
  let s : Finset V := insert v τ.1.1
  have hsK : s ∈ K := by
    apply (K.isRelLowerSet_faces τ.2).2
    · intro x hx
      simp only [s, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_union_right _ hvη
      · exact Finset.mem_union_left _ hx
    · exact ⟨v, by simp [s]⟩
  have hcard : s.card = n + 2 := by
    rw [Finset.card_insert_of_notMem hvτ, τ.1.2.2]
  refine ⟨⟨s, hsK, hcard⟩, ?_⟩
  simpa [s, Finset.insert_union, hvη] using τ.2

omit [Fintype V] in
@[simp]
theorem insertClosedStarVertex_val {η : {s : Finset V // s ∈ K}} {n : ℕ}
    (v : V) (hvη : v ∈ η.1) (τ : ClosedStarSimplex K η n)
    (hvτ : v ∉ τ.1.1) :
    (insertClosedStarVertex K v hvη τ hvτ).1.1 = insert v τ.1.1 :=
  rfl

omit [Fintype V] in
@[simp]
theorem eraseClosedStarVertex_val {η : {s : Finset V // s ∈ K}} {n : ℕ}
    (τ : ClosedStarSimplex K η (n + 1)) (w : V) (hw : w ∈ τ.1.1) :
    (eraseClosedStarVertex K τ w hw).1.1 = τ.1.1.erase w :=
  rfl

/-- Ordered coboundary on the closed star. -/
def closedStarCoboundaryAddHom
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    ClosedStarCochain K η n G →+ ClosedStarCochain K η (n + 1) G where
  toFun c := Finsupp.equivFunOnFinite.symm fun τ =>
    ∑ w : τ.1.1,
      incidenceSign K τ.1 w.1 • c (eraseClosedStarVertex K τ w.1 w.2)
  map_zero' := by
    ext τ
    simp
  map_add' c c' := by
    ext τ
    simp [Finset.sum_add_distrib]

/-- Ordered coboundary on the closed star as a `ℤ`-linear map. -/
def closedStarCoboundary
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    ClosedStarCochain K η n G →ₗ[ℤ] ClosedStarCochain K η (n + 1) G :=
  (closedStarCoboundaryAddHom (G := G) K η n).toIntLinearMap

@[simp]
theorem closedStarCoboundary_apply
    (η : {s : Finset V // s ∈ K}) (n : ℕ)
    (c : ClosedStarCochain K η n G) (τ : ClosedStarSimplex K η (n + 1)) :
    closedStarCoboundary K η n c τ =
      ∑ w : τ.1.1,
        incidenceSign K τ.1 w.1 • c (eraseClosedStarVertex K τ w.1 w.2) :=
  rfl

/-- The cone cochain homotopy: evaluate on the simplex obtained by adjoining
the chosen apex, with its ordered incidence sign. -/
def coneHomotopyAddHom
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    ClosedStarCochain K η (n + 1) G →+ ClosedStarCochain K η n G where
  toFun c := Finsupp.equivFunOnFinite.symm fun τ =>
    if hvτ : v ∈ τ.1.1 then 0
    else
      let ιτ := insertClosedStarVertex K v hvη τ hvτ
      incidenceSign K ιτ.1 v • c ιτ
  map_zero' := by
    ext τ
    by_cases h : v ∈ τ.1.1 <;> simp_all
  map_add' c c' := by
    ext τ
    by_cases h : v ∈ τ.1.1 <;> simp [h, smul_add]

/-- The cone homotopy as a `ℤ`-linear map. -/
def coneHomotopy
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    ClosedStarCochain K η (n + 1) G →ₗ[ℤ] ClosedStarCochain K η n G :=
  (coneHomotopyAddHom (G := G) K η v hvη n).toIntLinearMap

@[simp]
theorem coneHomotopy_apply_of_mem
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (c : ClosedStarCochain K η (n + 1) G)
    (τ : ClosedStarSimplex K η n) (hvτ : v ∈ τ.1.1) :
    coneHomotopy K η v hvη n c τ = 0 := by
  simp [coneHomotopy, coneHomotopyAddHom, hvτ]

@[simp]
theorem coneHomotopy_apply_of_not_mem
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (c : ClosedStarCochain K η (n + 1) G)
    (τ : ClosedStarSimplex K η n) (hvτ : v ∉ τ.1.1) :
    coneHomotopy K η v hvη n c τ =
      incidenceSign K (insertClosedStarVertex K v hvη τ hvτ).1 v •
        c (insertClosedStarVertex K v hvη τ hvτ) := by
  simp [coneHomotopy, coneHomotopyAddHom, hvτ]

omit [Fintype V] in
theorem incidenceSign_sq {n : ℕ} (τ : Simplex K (n + 1)) (v : V) :
    incidenceSign K τ v * incidenceSign K τ v = 1 := by
  change (-1 : ℤ) ^ (τ.1.filter fun w => w < v).card *
      (-1 : ℤ) ^ (τ.1.filter fun w => w < v).card = 1
  rw [← pow_add]
  have h : (τ.1.filter fun w => w < v).card +
      (τ.1.filter fun w => w < v).card =
        2 * (τ.1.filter fun w => w < v).card := by omega
  rw [h, pow_mul]
  norm_num

theorem insertClosedStarVertex_erase_apex
    {η : {s : Finset V // s ∈ K}} {n : ℕ}
    (v : V) (hvη : v ∈ η.1) (τ : ClosedStarSimplex K η n)
    (hvτ : v ∉ τ.1.1) :
    eraseClosedStarVertex K (insertClosedStarVertex K v hvη τ hvτ) v
      (by simp) = τ := by
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.erase_insert hvτ

theorem insertClosedStarVertex_erase_apex_of_mem
    {η : {s : Finset V // s ∈ K}} {n : ℕ}
    (v : V) (hvη : v ∈ η.1) (τ : ClosedStarSimplex K η (n + 1))
    (hvτ : v ∈ τ.1.1) :
    insertClosedStarVertex K v hvη (eraseClosedStarVertex K τ v hvτ)
      (by simp) = τ := by
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.insert_erase hvτ

theorem insertClosedStarVertex_erase_comm
    {η : {s : Finset V // s ∈ K}} {n : ℕ}
    (v : V) (hvη : v ∈ η.1) (τ : ClosedStarSimplex K η (n + 1))
    (hvτ : v ∉ τ.1.1) (w : V) (hwτ : w ∈ τ.1.1) :
    insertClosedStarVertex K v hvη (eraseClosedStarVertex K τ w hwτ)
        (by exact fun h => hvτ (Finset.mem_of_mem_erase h)) =
      eraseClosedStarVertex K (insertClosedStarVertex K v hvη τ hvτ) w
        (by simp [hwτ]) := by
  apply Subtype.ext
  apply Subtype.ext
  have hvw : v ≠ w := by
    intro h
    exact hvτ (h ▸ hwτ)
  change insert v (τ.1.1.erase w) = (insert v τ.1.1).erase w
  rw [Finset.erase_insert_of_ne hvw]

/-- Positive-degree cochain contraction on the closed star:
`d h + h d = 1`. -/
theorem closedStar_contraction_positive
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1)
    (n : ℕ) (c : ClosedStarCochain K η (n + 1) G) :
    closedStarCoboundary K η n (coneHomotopy K η v hvη n c) +
        coneHomotopy K η v hvη (n + 1)
          (closedStarCoboundary K η (n + 1) c) = c := by
  ext τ
  classical
  by_cases hvτ : v ∈ τ.1.1
  · rw [Finsupp.add_apply,
      coneHomotopy_apply_of_mem K η v hvη (n + 1) _ τ hvτ,
      add_zero, closedStarCoboundary_apply]
    let apex : τ.1.1 := ⟨v, hvτ⟩
    rw [Fintype.sum_eq_single apex]
    · change incidenceSign K τ.1 v •
          coneHomotopy K η v hvη n c
            (eraseClosedStarVertex K τ v hvτ) = c τ
      have hnot : v ∉ (eraseClosedStarVertex K τ v hvτ).1.1 := by
        change v ∉ τ.1.1.erase v
        simp
      rw [coneHomotopy_apply_of_not_mem K η v hvη n _ _ hnot]
      have hins := insertClosedStarVertex_erase_apex_of_mem K v hvη τ hvτ
      rw [hins, smul_smul, incidenceSign_sq]
      simp
    · intro w hw
      have hvw : v ≠ w.1 := by
        intro h
        apply hw
        apply Subtype.ext
        exact h.symm
      have hvErase : v ∈
          (eraseClosedStarVertex K τ w.1 w.2).1.1 := by
        change v ∈ τ.1.1.erase w.1
        exact Finset.mem_erase.mpr ⟨hvw, hvτ⟩
      rw [coneHomotopy_apply_of_mem K η v hvη n _ _ hvErase]
      simp
  · let S : ClosedStarSimplex K η (n + 2) :=
      insertClosedStarVertex K v hvη τ hvτ
    have hd_expansion :
        closedStarCoboundary K η n (coneHomotopy K η v hvη n c) τ =
          ∑ w : τ.1.1,
            incidenceSign K τ.1 w.1 •
              (incidenceSign K
                  (insertClosedStarVertex K v hvη
                    (eraseClosedStarVertex K τ w.1 w.2)
                    (by exact fun h => hvτ (Finset.mem_of_mem_erase h))).1 v •
                c (insertClosedStarVertex K v hvη
                    (eraseClosedStarVertex K τ w.1 w.2)
                    (by exact fun h => hvτ (Finset.mem_of_mem_erase h)))) := by
      rw [closedStarCoboundary_apply]
      apply Fintype.sum_congr
      intro w
      rw [coneHomotopy_apply_of_not_mem]
    have hdh_expansion :
        coneHomotopy K η v hvη (n + 1)
            (closedStarCoboundary K η (n + 1) c) τ =
          incidenceSign K S.1 v •
            (∑ x : S.1.1,
              incidenceSign K S.1 x.1 •
                c (eraseClosedStarVertex K S x.1 x.2)) := by
      rw [coneHomotopy_apply_of_not_mem K η v hvη (n + 1) _ τ hvτ]
      change incidenceSign K S.1 v •
          closedStarCoboundary K η (n + 1) c S = _
      rw [closedStarCoboundary_apply]
    rw [Finsupp.add_apply, hd_expansion, hdh_expansion]
    have hsplit := sum_insert_subtype τ.1.1 v hvτ
      (fun x : ↥(insert v τ.1.1) =>
        incidenceSign K S.1 x.1 •
          c (eraseClosedStarVertex K S x.1 x.2))
    change (∑ x : S.1.1,
      incidenceSign K S.1 x.1 •
        c (eraseClosedStarVertex K S x.1 x.2)) = _ at hsplit
    rw [hsplit, smul_add]
    have hapex :
        incidenceSign K S.1 v •
            (incidenceSign K S.1 v •
              c (eraseClosedStarVertex K S v (by
                change v ∈ insert v τ.1.1
                simp))) = c τ := by
      rw [smul_smul, incidenceSign_sq, one_smul]
      simpa only [S] using
        congrArg c (insertClosedStarVertex_erase_apex K v hvη τ hvτ)
    rw [hapex]
    have hpairs :
        (∑ w : τ.1.1,
            incidenceSign K τ.1 w.1 •
              (incidenceSign K
                  (insertClosedStarVertex K v hvη
                    (eraseClosedStarVertex K τ w.1 w.2)
                    (by exact fun h => hvτ (Finset.mem_of_mem_erase h))).1 v •
                c (insertClosedStarVertex K v hvη
                    (eraseClosedStarVertex K τ w.1 w.2)
                    (by exact fun h => hvτ (Finset.mem_of_mem_erase h))))) +
          incidenceSign K S.1 v •
            (∑ w : τ.1.1,
              incidenceSign K S.1 w.1 •
                c (eraseClosedStarVertex K S w.1
                  (Finset.mem_insert_of_mem w.2))) = 0 := by
      rw [Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro w hw
      let Ew := eraseClosedStarVertex K τ w w.2
      have hvEw : v ∉ Ew.1.1 := by
        exact fun h => hvτ (Finset.mem_of_mem_erase h)
      let Iw := insertClosedStarVertex K v hvη Ew hvEw
      have hcomm : Iw = eraseClosedStarVertex K S w
          (Finset.mem_insert_of_mem w.2) := by
        exact insertClosedStarVertex_erase_comm K v hvη τ hvτ w w.2
      change incidenceSign K τ.1 w •
            (incidenceSign K Iw.1 v • c Iw) +
          incidenceSign K S.1 v •
            (incidenceSign K S.1 w •
              c (eraseClosedStarVertex K S w
                (Finset.mem_insert_of_mem w.2))) = 0
      rw [← hcomm, smul_smul, smul_smul]
      have hsign := orderedSign_insert_erase_cancellation
        τ.1.1 hvτ w.2
      change incidenceSign K τ.1 w * incidenceSign K Iw.1 v =
          -(incidenceSign K S.1 v * incidenceSign K S.1 w) at hsign
      rw [hsign, neg_smul]
      exact neg_add_cancel _
    calc
      _ = ((∑ w : τ.1.1,
              incidenceSign K τ.1 w.1 •
                (incidenceSign K
                    (insertClosedStarVertex K v hvη
                      (eraseClosedStarVertex K τ w.1 w.2)
                      (by exact fun h => hvτ (Finset.mem_of_mem_erase h))).1 v •
                  c (insertClosedStarVertex K v hvη
                      (eraseClosedStarVertex K τ w.1 w.2)
                      (by exact fun h => hvτ (Finset.mem_of_mem_erase h))))) +
            incidenceSign K S.1 v •
              (∑ w : τ.1.1,
                incidenceSign K S.1 w.1 •
                  c (eraseClosedStarVertex K S w.1
                    (Finset.mem_insert_of_mem w.2)))) + c τ := by abel
      _ = 0 + c τ := by rw [hpairs]
      _ = c τ := zero_add _

/-- Restrict a global cochain to the closed star of `η`. -/
def restrictClosedStarAddHom
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    Cochain K n G →+ ClosedStarCochain K η n G where
  toFun c := Finsupp.equivFunOnFinite.symm fun τ => c τ.1
  map_zero' := by ext τ; simp
  map_add' c c' := by ext τ; simp

/-- Restriction to a closed star as a `ℤ`-linear map. -/
def restrictClosedStar
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    Cochain K n G →ₗ[ℤ] ClosedStarCochain K η n G :=
  (restrictClosedStarAddHom (G := G) K η n).toIntLinearMap

@[simp]
theorem restrictClosedStar_apply
    (η : {s : Finset V // s ∈ K}) (n : ℕ)
    (c : Cochain K n G) (τ : ClosedStarSimplex K η n) :
    restrictClosedStar K η n c τ = c τ.1 :=
  rfl

/-- Global coboundary strictly commutes with restriction to a closed star. -/
theorem restrictClosedStar_coboundary
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    (restrictClosedStar (G := G) K η (n + 1)).comp (coboundary K n) =
      (closedStarCoboundary K η n).comp
        (restrictClosedStar (G := G) K η n) := by
  apply DFunLike.ext _ _
  intro c
  apply Finsupp.ext
  intro τ
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    restrictClosedStar_apply, coboundary_apply,
    closedStarCoboundary_apply]
  apply Fintype.sum_congr
  intro w
  rfl

/-- The chosen vertex, regarded as a degree-zero simplex in the closed star. -/
def closedStarApex
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) :
    ClosedStarSimplex K η 0 := by
  let s : Simplex K 0 := ⟨{v}, K.singleton_mem v, by simp⟩
  refine ⟨s, ?_⟩
  simpa [s, hvη] using η.2

omit [Fintype V] in
@[simp]
theorem closedStarApex_val
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) :
    (closedStarApex K η v hvη).1.1 = {v} :=
  rfl

/-- Evaluation at the cone apex (the augmentation in degree zero). -/
def closedStarAugmentation
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) :
    ClosedStarCochain K η 0 G →ₗ[ℤ] G :=
  { toFun := fun c => c (closedStarApex K η v hvη)
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro z c
      simp }

/-- Constant degree-zero cochain on the closed star. -/
def closedStarConstant
    (η : {s : Finset V // s ∈ K}) :
    G →ₗ[ℤ] ClosedStarCochain K η 0 G :=
  { toFun := fun g => Finsupp.equivFunOnFinite.symm fun _ => g
    map_add' := by intro g g'; ext τ; simp
    map_smul' := by intro z g; ext τ; simp }

@[simp]
theorem closedStarConstant_apply
    (η : {s : Finset V // s ∈ K}) (g : G)
    (τ : ClosedStarSimplex K η 0) :
    closedStarConstant K η g τ = g :=
  rfl

omit [Fintype V] in
theorem closedStarZeroSimplex_eq_apex_of_mem
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1)
    (τ : ClosedStarSimplex K η 0) (hvτ : v ∈ τ.1.1) :
    τ = closedStarApex K η v hvη := by
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp τ.1.2.2
  have hvw : v = w := by
    simpa [hw] using hvτ
  simpa [hw, hvw]

/-- Degree-zero contraction with the constant-cochain correction:
`h d = 1 - const ∘ augmentation`. -/
theorem closedStar_contraction_zero
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1)
    (c : ClosedStarCochain K η 0 G) :
    coneHomotopy K η v hvη 0 (closedStarCoboundary K η 0 c) =
      c - closedStarConstant K η (closedStarAugmentation K η v hvη c) := by
  ext τ
  classical
  by_cases hvτ : v ∈ τ.1.1
  · rw [coneHomotopy_apply_of_mem K η v hvη 0 _ τ hvτ,
      Finsupp.sub_apply, closedStarConstant_apply]
    have hτ := closedStarZeroSimplex_eq_apex_of_mem K η v hvη τ hvτ
    rw [hτ]
    exact (sub_self _).symm
  · rw [coneHomotopy_apply_of_not_mem K η v hvη 0 _ τ hvτ]
    let S : ClosedStarSimplex K η 1 :=
      insertClosedStarVertex K v hvη τ hvτ
    change incidenceSign K S.1 v • closedStarCoboundary K η 0 c S =
      (c - closedStarConstant K η
        (closedStarAugmentation K η v hvη c)) τ
    rw [closedStarCoboundary_apply, Finsupp.sub_apply,
      closedStarConstant_apply]
    have hsplit := sum_insert_subtype τ.1.1 v hvτ
      (fun x : ↥(insert v τ.1.1) =>
        incidenceSign K S.1 x.1 •
          c (eraseClosedStarVertex K S x.1 x.2))
    change (∑ x : S.1.1,
      incidenceSign K S.1 x.1 •
        c (eraseClosedStarVertex K S x.1 x.2)) = _ at hsplit
    rw [hsplit, smul_add]
    have hapex :
        incidenceSign K S.1 v •
            (incidenceSign K S.1 v •
              c (eraseClosedStarVertex K S v (by
                change v ∈ insert v τ.1.1
                simp))) = c τ := by
      rw [smul_smul, incidenceSign_sq, one_smul]
      simpa only [S] using
        congrArg c (insertClosedStarVertex_erase_apex K v hvη τ hvτ)
    rw [hapex]
    obtain ⟨w, hτw⟩ := Finset.card_eq_one.mp τ.1.2.2
    have hwτ : w ∈ τ.1.1 := by simp [hτw]
    have hvw : v ≠ w := by
      intro h
      apply hvτ
      simpa [h] using hwτ
    let ws : τ.1.1 := ⟨w, hwτ⟩
    have hrest :
        incidenceSign K S.1 v •
            (∑ x : τ.1.1,
              incidenceSign K S.1 x.1 •
                c (eraseClosedStarVertex K S x.1
                  (Finset.mem_insert_of_mem x.2))) =
          -c (closedStarApex K η v hvη) := by
      rw [Finset.smul_sum]
      rw [Fintype.sum_eq_single ws]
      · change incidenceSign K S.1 v •
            (incidenceSign K S.1 w •
              c (eraseClosedStarVertex K S w
                (Finset.mem_insert_of_mem hwτ))) = _
        rw [smul_smul]
        have herase : eraseClosedStarVertex K S w
            (Finset.mem_insert_of_mem hwτ) = closedStarApex K η v hvη := by
          apply Subtype.ext
          apply Subtype.ext
          change (insert v τ.1.1).erase w = {v}
          rw [hτw]
          rw [Finset.erase_insert_of_ne hvw, Finset.erase_singleton]
          simp
        rw [herase]
        have hsign := orderedSign_insert_erase_cancellation τ.1.1 hvτ hwτ
        have hleft : orderedSign τ.1.1 w *
            orderedSign (insert v (τ.1.1.erase w)) v = 1 := by
          rw [hτw, Finset.erase_singleton]
          change
            (-1 : ℤ) ^ (({w} : Finset V).filter (fun x => x < w)).card *
              (-1 : ℤ) ^ (({v} : Finset V).filter (fun x => x < v)).card = 1
          have hwempty :
              ({w} : Finset V).filter (fun x => x < w) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro x hx hlt
            have hxw : x = w := Finset.mem_singleton.mp hx
            subst x
            exact lt_irrefl w hlt
          have hvempty :
              ({v} : Finset V).filter (fun x => x < v) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro x hx hlt
            have hxv : x = v := Finset.mem_singleton.mp hx
            subst x
            exact lt_irrefl v hlt
          rw [hwempty, hvempty]
          norm_num
        have hprod : incidenceSign K S.1 v * incidenceSign K S.1 w = -1 := by
          change orderedSign (insert v τ.1.1) v *
              orderedSign (insert v τ.1.1) w = -1
          rw [hleft] at hsign
          linarith
        rw [hprod, neg_one_smul]
      · intro x hx
        exfalso
        apply hx
        have hxmem : x.1 ∈ ({w} : Finset V) := by simpa [hτw] using x.2
        have hxval : x.1 = w := Finset.mem_singleton.mp hxmem
        apply Subtype.ext
        exact hxval
    rw [hrest]
    change c τ + -c (closedStarApex K η v hvη) =
      c τ - c (closedStarApex K η v hvη)
    rw [sub_eq_add_neg]

/-- Every face of a simplex `σ ⊇ η` canonically belongs to the closed star of
`η`. -/
def faceInToClosedStar
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1) (n : ℕ)
    (τ : facesIn K n σ) : ClosedStarSimplex K η n := by
  refine ⟨τ.1, ?_⟩
  apply (K.isRelLowerSet_faces σ.2).2
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact τ.2 hx
    · exact hησ hx
  · exact (K.isRelLowerSet_faces τ.1.2.1).1.mono
      Finset.subset_union_left

/-- Restrict a closed-star cochain to the faces of a simplex containing the
active simplex. -/
def restrictClosedStarToSimplexAddHom
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1) (n : ℕ) :
    ClosedStarCochain K η n G →+
      GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G where
  toFun c := Finsupp.equivFunOnFinite.symm fun τ =>
    c (faceInToClosedStar K η σ hησ n τ)
  map_zero' := by ext τ; simp
  map_add' c c' := by ext τ; simp

def restrictClosedStarToSimplex
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1) (n : ℕ) :
    ClosedStarCochain K η n G →ₗ[ℤ]
      GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G :=
  (restrictClosedStarToSimplexAddHom (G := G) K η σ hησ n).toIntLinearMap

@[simp]
theorem restrictClosedStarToSimplex_apply
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1) (n : ℕ)
    (c : ClosedStarCochain K η n G) (τ : facesIn K n σ) :
    restrictClosedStarToSimplex K η σ hησ n c τ =
      c (faceInToClosedStar K η σ hησ n τ) :=
  rfl

/-- Insert the apex into a face of `σ`; containment is preserved because
`v ∈ η ⊆ σ`. -/
def insertVertexIn
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1)
    (v : V) (hvη : v ∈ η.1) {n : ℕ} (τ : facesIn K n σ)
    (hvτ : v ∉ τ.1.1) : facesIn K (n + 1) σ := by
  let I := insertClosedStarVertex K v hvη
    (faceInToClosedStar K η σ hησ n τ) hvτ
  refine ⟨I.1, ?_⟩
  intro x hx
  change x ∈ insert v τ.1.1 at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hησ hvη
  · exact τ.2 hx

omit [Fintype V] in
theorem faceInToClosedStar_insertVertexIn
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1)
    (v : V) (hvη : v ∈ η.1) {n : ℕ} (τ : facesIn K n σ)
    (hvτ : v ∉ τ.1.1) :
    faceInToClosedStar K η σ hησ (n + 1)
        (insertVertexIn K η σ hησ v hvη τ hvτ) =
      insertClosedStarVertex K v hvη
        (faceInToClosedStar K η σ hησ n τ) hvτ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Cone homotopy on the ordinary cochains of a simplex `σ ⊇ η`. -/
def simplexConeHomotopyAddHom
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1)
    (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    GeneralSphereT.PathAlgebra.Configuration (facesIn K (n + 1) σ) G →+
      GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G where
  toFun c := Finsupp.equivFunOnFinite.symm fun τ =>
    if hvτ : v ∈ τ.1.1 then 0
    else
      let I := insertVertexIn K η σ hησ v hvη τ hvτ
      incidenceSign K I.1 v • c I
  map_zero' := by
    ext τ
    by_cases h : v ∈ τ.1.1 <;> simp_all
  map_add' c c' := by
    ext τ
    by_cases h : v ∈ τ.1.1 <;> simp [h, smul_add]

def simplexConeHomotopy
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1)
    (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    GeneralSphereT.PathAlgebra.Configuration (facesIn K (n + 1) σ) G →ₗ[ℤ]
      GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G :=
  (simplexConeHomotopyAddHom (G := G) K η σ hησ v hvη n).toIntLinearMap

/-- Restriction to every simplex `σ ⊇ η` strictly commutes with the selected
cone homotopy. -/
theorem restrictClosedStarToSimplex_coneHomotopy
    (η σ : {s : Finset V // s ∈ K}) (hησ : η.1 ⊆ σ.1)
    (v : V) (hvη : v ∈ η.1) (n : ℕ) :
    (restrictClosedStarToSimplex (G := G) K η σ hησ n).comp
        (coneHomotopy K η v hvη n) =
      (simplexConeHomotopy K η σ hησ v hvη n).comp
        (restrictClosedStarToSimplex (G := G) K η σ hησ (n + 1)) := by
  apply DFunLike.ext _ _
  intro c
  apply Finsupp.ext
  intro τ
  by_cases hvτ : v ∈ τ.1.1
  · rw [LinearMap.comp_apply, LinearMap.comp_apply,
      restrictClosedStarToSimplex_apply]
    have hvstar : v ∈
        (faceInToClosedStar K η σ hησ n τ).1.1 := hvτ
    rw [coneHomotopy_apply_of_mem K η v hvη n _ _ hvstar]
    simp [simplexConeHomotopy, simplexConeHomotopyAddHom, hvτ]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply,
      restrictClosedStarToSimplex_apply,
      coneHomotopy_apply_of_not_mem K η v hvη n _ _ hvτ]
    rw [show
      (simplexConeHomotopy K η σ hησ v hvη n)
          (restrictClosedStarToSimplex K η σ hησ (n + 1) c) τ =
        incidenceSign K (insertVertexIn K η σ hησ v hvη τ hvτ).1 v •
          c (faceInToClosedStar K η σ hησ (n + 1)
            (insertVertexIn K η σ hησ v hvη τ hvτ)) by
      simp [simplexConeHomotopy, simplexConeHomotopyAddHom, hvτ]]
    rw [faceInToClosedStar_insertVertexIn]
    have hlocal :
        (insertVertexIn K η σ hησ v hvη τ hvτ).1 =
          (insertClosedStarVertex K v hvη
            (faceInToClosedStar K η σ hησ n τ) hvτ).1 := rfl
    rw [hlocal]

end GeneralSphereT.SimplicialCochain
