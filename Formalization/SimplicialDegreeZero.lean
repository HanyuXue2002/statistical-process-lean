import Formalization.FiniteSimplicialCochain

set_option linter.style.header false

/-!
# Constant simplicial zero-cochains

The global constant zero-cochain has zero coboundary.  Consequently, changing
a zero-cochain by a global constant does not change its coboundary.  This is
the degree-zero normalization needed when the cocycle degree is one.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- The global zero-cochain with constant value `g` on every vertex. -/
def constantCochain (g : G) : Cochain K 0 G :=
  Finsupp.equivFunOnFinite.symm fun _ => g

omit [LinearOrder V] in
@[simp]
theorem constantCochain_apply (g : G) (v : Simplex K 0) :
    constantCochain K g v = g :=
  rfl

/-- A global constant zero-cochain has zero simplicial coboundary. -/
@[simp]
theorem coboundary_constantCochain (g : G) :
    coboundary K 0 (constantCochain K g) = 0 := by
  ext τ
  rw [coboundary_apply]
  simp only [constantCochain_apply]
  have hcard : τ.1.card = 2 := by
    simpa using τ.2.2
  obtain ⟨v, w, hvw, hτ⟩ := Finset.card_eq_two.mp hcard
  change
    (∑ x : τ.1,
      (fun x : V =>
        ((-1 : ℤ) ^ (τ.1.filter fun y => y < x).card) • g) x) = 0
  rw [Finset.sum_coe_sort τ.1 (fun x : V =>
    ((-1 : ℤ) ^ (τ.1.filter fun y => y < x).card) • g), hτ]
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · have hlowerV : ({v, w} : Finset V).filter (fun y => y < v) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact (lt_irrefl _ hx).elim
        · exact (not_lt_of_ge hvwlt.le hx).elim
      · intro h
        simp at h
    have hlowerW : ({v, w} : Finset V).filter (fun y => y < w) = {v} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact (lt_irrefl _ hx).elim
      · rintro rfl
        exact ⟨Or.inl rfl, hvwlt⟩
    rw [Finset.sum_pair hvw, hlowerV, hlowerW]
    simp
  · have hlowerV : ({v, w} : Finset V).filter (fun y => y < v) = {w} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact (lt_irrefl _ hx).elim
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, hwvlt⟩
    have hlowerW : ({v, w} : Finset V).filter (fun y => y < w) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact (not_lt_of_ge hwvlt.le hx).elim
        · exact (lt_irrefl _ hx).elim
      · intro h
        simp at h
    rw [Finset.sum_pair hvw, hlowerV, hlowerW]
    simp

/-- Subtracting a global constant from a zero-cochain preserves its
coboundary. -/
@[simp]
theorem coboundary_sub_constantCochain (c : Cochain K 0 G) (g : G) :
    coboundary K 0 (c - constantCochain K g) = coboundary K 0 c := by
  rw [map_sub, coboundary_constantCochain, sub_zero]

end GeneralSphereT.SimplicialCochain
