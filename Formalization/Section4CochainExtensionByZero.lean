import Formalization.SimplicialCochainPullback

set_option linter.style.header false

/-!
# Section 4: extension by zero along an ordered simplicial embedding

An ordered simplicial map in this project is injective on vertices.  Hence it
is also injective on nondegenerate simplices, and cochain pullback has the
obvious set-theoretic section: retain the coefficient on simplices in the
image and put zero elsewhere.  This is the unrestricted cochain extension
used before applying the relative cocycle-extension argument (4.7).
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

universe uV uW

variable {V : Type uV} {W : Type uW}
variable [LinearOrder V] [LinearOrder W] [Fintype V] [Fintype W]
variable {G : Type*} [AddCommGroup G]
variable {K : AbstractSimplicialComplex V}
variable {L : AbstractSimplicialComplex W}

namespace OrderedSimplicialMap

omit [Fintype V] [Fintype W] in
/-- An ordered vertex embedding induces an injection on oriented
nondegenerate simplices. -/
theorem mapSimplex_injective (F : OrderedSimplicialMap K L) (n : ℕ) :
    Function.Injective (F.mapSimplex (n := n)) := by
  intro σ τ h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  change σ.1.map F.toOrderEmbedding.toEmbedding =
    τ.1.map F.toOrderEmbedding.toEmbedding at hval
  exact Finset.map_injective F.toOrderEmbedding.toEmbedding hval

/-- Extend a cochain by zero outside the image of an ordered simplicial
embedding.  Only the section property is used; no additivity of this chosen
function is required later. -/
def extendCochainByZero (F : OrderedSimplicialMap K L) (n : ℕ) :
    Cochain K n G → Cochain L n G := by
  classical
  exact fun c => Finsupp.equivFunOnFinite.symm fun τ =>
    if h : ∃ σ : Simplex K n, F.mapSimplex σ = τ then
      c (Classical.choose h)
    else 0

@[simp]
theorem extendCochainByZero_apply_of_eq
    (F : OrderedSimplicialMap K L) (n : ℕ)
    (c : Cochain K n G) (σ : Simplex K n) :
    extendCochainByZero F n c (F.mapSimplex σ) = c σ := by
  classical
  simp only [extendCochainByZero,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  split_ifs with h
  · congr 1
    exact mapSimplex_injective F n (Classical.choose_spec h)
  · exact (h ⟨σ, rfl⟩).elim

/-- Pulling the zero extension back along the embedding recovers the original
cochain exactly. -/
@[simp]
theorem pullback_extendCochainByZero
    (F : OrderedSimplicialMap K L) (n : ℕ)
    (c : Cochain K n G) :
    F.pullback n (extendCochainByZero F n c) = c := by
  ext σ
  rw [pullback_apply, extendCochainByZero_apply_of_eq]

/-- Extension by zero preserves the zero cochain. -/
@[simp]
theorem extendCochainByZero_zero
    (F : OrderedSimplicialMap K L) (n : ℕ) :
    extendCochainByZero F n (0 : Cochain K n G) = 0 := by
  ext τ
  classical
  simp only [extendCochainByZero,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  split_ifs <;> simp

end OrderedSimplicialMap

end GeneralSphereT.SimplicialCochain
