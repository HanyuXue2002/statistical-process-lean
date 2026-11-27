import Formalization.SimplicialIncidenceSign

set_option linter.style.header false

/-!
# The simplicial coboundary squares to zero

For each `(n+2)`-simplex, the double coboundary is indexed by ordered pairs
of distinct deleted vertices.  Swapping the two vertices preserves the final
`n`-face and reverses the total incidence sign, so the terms cancel in pairs.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

omit [Fintype V] in
private theorem mem_eraseVertex_iff {n : ℕ}
    (τ : Simplex K (n + 1)) (v : V) (hv : v ∈ τ.1) (w : V) :
    w ∈ (eraseVertex K τ v hv).1 ↔ w ∈ τ.1 ∧ w ≠ v := by
  change w ∈ τ.1.erase v ↔ _
  simp [and_comm]

/-- An ordered pair of distinct vertices, expressed in the same dependent
form as the two nested coboundary sums. -/
private abbrev DoubleDeletionIndex {n : ℕ} (τ : Simplex K (n + 2)) :=
  Σ v : τ.1, {w : V // w ∈ (eraseVertex K τ v.1 v.2).1}

private def swapDoubleDeletionIndex {n : ℕ} (τ : Simplex K (n + 2)) :
    DoubleDeletionIndex K τ → DoubleDeletionIndex K τ := fun p => by
  let v : V := p.1.1
  let w : V := p.2.1
  have hv : v ∈ τ.1 := p.1.2
  have hwErase : w ∈ (eraseVertex K τ v hv).1 := p.2.2
  have hwData := (mem_eraseVertex_iff K τ v hv w).mp hwErase
  have hw : w ∈ τ.1 := hwData.1
  have hwv : w ≠ v := hwData.2
  exact ⟨⟨w, hw⟩,
    ⟨v, (mem_eraseVertex_iff K τ w hw v).mpr ⟨hv, hwv.symm⟩⟩⟩

omit [Fintype V] in
private theorem swapDoubleDeletionIndex_ne {n : ℕ}
    (τ : Simplex K (n + 2)) (p : DoubleDeletionIndex K τ) :
    swapDoubleDeletionIndex K τ p ≠ p := by
  intro h
  have hfirst := congrArg (fun q : DoubleDeletionIndex K τ => q.1.1) h
  have hwv : p.2.1 ≠ p.1.1 :=
    ((mem_eraseVertex_iff K τ p.1.1 p.1.2 p.2.1).mp p.2.2).2
  exact hwv hfirst

omit [Fintype V] in
private theorem swapDoubleDeletionIndex_involutive {n : ℕ}
    (τ : Simplex K (n + 2)) (p : DoubleDeletionIndex K τ) :
    swapDoubleDeletionIndex K τ (swapDoubleDeletionIndex K τ p) = p := by
  rcases p with ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  rfl

omit [Fintype V] in
private theorem eraseVertex_eraseVertex_comm {n : ℕ}
    (τ : Simplex K (n + 2))
    (v w : V) (hv : v ∈ τ.1) (hw : w ∈ τ.1) (_hvw : v ≠ w)
    (hwErase : w ∈ (eraseVertex K τ v hv).1)
    (hvErase : v ∈ (eraseVertex K τ w hw).1) :
    eraseVertex K (eraseVertex K τ v hv) w hwErase =
      eraseVertex K (eraseVertex K τ w hw) v hvErase := by
  apply Subtype.ext
  change (τ.1.erase v).erase w = (τ.1.erase w).erase v
  ext x
  simp [and_left_comm]

private def doubleDeletionTerm {n : ℕ} (τ : Simplex K (n + 2))
    (c : Cochain K n G) (p : DoubleDeletionIndex K τ) : G :=
  (incidenceSign K τ p.1.1 *
      incidenceSign K (eraseVertex K τ p.1.1 p.1.2) p.2.1) •
    c (eraseVertex K (eraseVertex K τ p.1.1 p.1.2)
      p.2.1 p.2.2)

omit [Fintype V] in
private theorem doubleDeletionTerm_add_swap {n : ℕ}
    (τ : Simplex K (n + 2)) (c : Cochain K n G)
    (p : DoubleDeletionIndex K τ) :
    doubleDeletionTerm K τ c p +
      doubleDeletionTerm K τ c (swapDoubleDeletionIndex K τ p) = 0 := by
  let v : V := p.1.1
  let w : V := p.2.1
  have hv : v ∈ τ.1 := p.1.2
  have hwErase : w ∈ (eraseVertex K τ v hv).1 := p.2.2
  have hwData := (mem_eraseVertex_iff K τ v hv w).mp hwErase
  have hw : w ∈ τ.1 := hwData.1
  have hwv : w ≠ v := hwData.2
  have hvErase : v ∈ (eraseVertex K τ w hw).1 :=
    (mem_eraseVertex_iff K τ w hw v).mpr ⟨hv, hwv.symm⟩
  have herase :
      eraseVertex K (eraseVertex K τ v hv) w hwErase =
        eraseVertex K (eraseVertex K τ w hw) v hvErase :=
    eraseVertex_eraseVertex_comm K τ v w hv hw hwv.symm
      hwErase hvErase
  have hsign := incidenceSign_delete_delete K τ v w hv hw hwv.symm
  change
    (incidenceSign K τ v *
        incidenceSign K (eraseVertex K τ v hv) w) •
          c (eraseVertex K (eraseVertex K τ v hv) w hwErase) +
      (incidenceSign K τ w *
        incidenceSign K (eraseVertex K τ w hw) v) •
          c (eraseVertex K (eraseVertex K τ w hw) v hvErase) = 0
  rw [herase, hsign]
  simp

/-- Pointwise form of `d² = 0` for finite ordered simplicial cochains. -/
@[simp]
theorem coboundary_coboundary (n : ℕ) (c : Cochain K n G) :
    coboundary K (n + 1) (coboundary K n c) = 0 := by
  ext τ
  rw [coboundary_apply]
  simp_rw [coboundary_apply, Finset.smul_sum, smul_smul]
  change
    (∑ v : τ.1,
      ∑ w : (eraseVertex K τ v.1 v.2).1,
        doubleDeletionTerm K τ c ⟨v, w⟩) = 0
  rw [← Fintype.sum_sigma']
  exact Finset.sum_involution
    (s := Finset.univ)
    (f := doubleDeletionTerm K τ c)
    (fun p _ => swapDoubleDeletionIndex K τ p)
    (fun p _ => doubleDeletionTerm_add_swap K τ c p)
    (fun p _ _ => swapDoubleDeletionIndex_ne K τ p)
    (fun _ _ => Finset.mem_univ _)
    (fun p _ => swapDoubleDeletionIndex_involutive K τ p)

/-- Linear-map form of the simplicial identity `d² = 0`. -/
theorem coboundary_comp_coboundary (n : ℕ) :
    (coboundary (G := G) K (n + 1)).comp (coboundary K n) = 0 := by
  apply LinearMap.ext
  intro c
  exact coboundary_coboundary K n c

/-- Additive-map form of the simplicial identity `d² = 0`. -/
theorem coboundaryAddHom_comp_coboundaryAddHom (n : ℕ) :
    (coboundaryAddHom (G := G) K (n + 1)).comp
        (coboundaryAddHom K n) = 0 := by
  apply AddMonoidHom.ext
  intro c
  exact coboundary_coboundary K n c

end GeneralSphereT.SimplicialCochain
