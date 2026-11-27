import Formalization.Section4ReducedFreeSurjectivity
import Formalization.Section4DoldKanDiskContraction
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

set_option linter.style.header false

/-!
# Section 4: the homology shift in the fibre sequence

For positive degree the objectwise sequence

`0 ⟶ F(G,q) ⟶ reducedFree L(G,q) ⟶ reducedFree K(G,q) ⟶ 0`

is short exact.  Applying the alternating-face-complex functor gives the
homology connecting morphism.  Once `L(G,q)` has a genuine simplicial
contraction, the middle complex is acyclic, so this connecting morphism is an
isomorphism.  This is the precise chain-level content of (4.5).
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace GeneralSphereT.StandardModels

universe u

/-- For a simplicial abelian group, its homotopy group is represented
algebraically by the homology of the normalized Moore complex. -/
abbrev SimplicialAbelianHomotopy
    (A : SimplicialObject AddCommGrpCat.{u}) (n : ℕ) :=
  (CategoryTheory.Abelian.DoldKan.N.obj A).homology n

/-- Reduced integral homology of the underlying pointed simplicial object,
in the reduced-free alternating-chain model used in Section 4. -/
abbrev ReducedIntegralHomology
    (A : SimplicialObject AddCommGrpCat.{u}) (n : ℕ) :=
  (AlgebraicTopology.AlternatingFaceMapComplex.obj
    (reducedFree A)).homology n

/-- Normalized Moore and alternating-face homology agree. -/
def normalizedAlternatingHomologyIso
    (A : SimplicialObject AddCommGrpCat.{u}) (n : ℕ) :
    SimplicialAbelianHomotopy A n ≅
      (AlgebraicTopology.AlternatingFaceMapComplex.obj A).homology n :=
  (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := A)).toHomologyIso n

/-- The standard fibre short complex after passage to alternating face
complexes. -/
abbrev FAlternatingKernelSequence (G : AddCommGrpCat.{u}) (q : ℕ) :=
  (FKernelSequence G (q + 1)).map
    (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat)

/-- The alternating-face-complex sequence is still short exact. -/
theorem FAlternatingKernelSequence_shortExact
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    (FAlternatingKernelSequence G q).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  change
    ((FKernelSequence G (q + 1)).map
      ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat).obj
        (Opposite.op (SimplexCategory.mk n)))).ShortExact
  exact (FKernelSequence_shortExact_succ G q).map_of_exact
    ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat).obj
      (Opposite.op (SimplexCategory.mk n)))

/-- The connecting morphism
`H_{n+1}(reducedFree K) ⟶ H_n(F)` in the long exact sequence. -/
abbrev FConnectingHom (G : AddCommGrpCat.{u}) (q n : ℕ) :=
  (FAlternatingKernelSequence_shortExact G q).δ (n + 1) n (by simp)

/-- A genuine contraction of `L` makes the connecting morphism an
isomorphism. -/
theorem FConnectingHom_isIso
    (G : AddCommGrpCat.{u}) (q n : ℕ)
    (H : LSimplicialContraction G q) :
    IsIso (FConnectingHom G q n) := by
  let S := FAlternatingKernelSequence G q
  let hS : S.ShortExact := FAlternatingKernelSequence_shortExact G q
  let δ := hS.δ (n + 1) n (by simp)
  have hLsucc : IsZero (S.X₂.homology (n + 1)) := by
    exact reducedFreeL_alternating_homology_isZero_of_contraction
      G q (n + 1) H
  have hLn : IsZero (S.X₂.homology n) := by
    exact reducedFreeL_alternating_homology_isZero_of_contraction G q n H
  have hmono : Mono δ := by
    rw [(hS.homology_exact₃ (n + 1) n (by simp)).mono_g_iff]
    exact hLsucc.eq_of_src _ _
  have hepi : Epi δ := by
    rw [(hS.homology_exact₁ (n + 1) n (by simp)).epi_f_iff]
    exact hLn.eq_of_tgt _ _
  let _ : Mono δ := hmono
  let _ : Epi δ := hepi
  exact isIso_of_mono_of_epi δ

/-- Formula (4.5) at the homology-object level:
`H_n(F(G,q+1)) ≅ H_{n+1}(reducedFree K(G,q+1))`. -/
def FHomologyShiftIso
    (G : AddCommGrpCat.{u}) (q n : ℕ)
    (H : LSimplicialContraction G q) :
    (FAlternatingKernelSequence G q).X₁.homology n ≅
      (FAlternatingKernelSequence G q).X₃.homology (n + 1) := by
  let _ : IsIso (FConnectingHom G q n) :=
    FConnectingHom_isIso G q n H
  exact (asIso (FConnectingHom G q n)).symm

/-- The homotopy--homology form of (4.5):
`π_n F(G,q+1) ≅ H~_{n+1}(K(G,q+1); ℤ)`. -/
def fiberHomotopyReducedHomologyIso
    (G : AddCommGrpCat.{u}) (q n : ℕ)
    (H : LSimplicialContraction G q) :
    SimplicialAbelianHomotopy (F G (q + 1)) n ≅
      ReducedIntegralHomology (K G (q + 1)) (n + 1) :=
  (normalizedAlternatingHomologyIso (F G (q + 1)) n).trans
    (FHomologyShiftIso G q n H)

/-! ## The standard disk model

The explicit face contraction constructed for `L(G,q+1)` gives the same
homology shift without asking for a separately supplied simplicial
contraction.  This is the unconditional form used in Section 4.
-/

/-- For the standard Dold--Kan disk, the connecting morphism is an
isomorphism without any auxiliary hypothesis. -/
theorem standardFConnectingHom_isIso
    (G : AddCommGrpCat.{u}) (q n : ℕ) :
    IsIso (FConnectingHom G q n) := by
  let S := FAlternatingKernelSequence G q
  let hS : S.ShortExact := FAlternatingKernelSequence_shortExact G q
  let δ := hS.δ (n + 1) n (by simp)
  have hLsucc : IsZero (S.X₂.homology (n + 1)) := by
    exact DoldKanDiskContraction.reducedFreeLAlternating_homology_isZero
      G q (n + 1)
  have hLn : IsZero (S.X₂.homology n) := by
    exact DoldKanDiskContraction.reducedFreeLAlternating_homology_isZero
      G q n
  have hmono : Mono δ := by
    rw [(hS.homology_exact₃ (n + 1) n (by simp)).mono_g_iff]
    exact hLsucc.eq_of_src _ _
  have hepi : Epi δ := by
    rw [(hS.homology_exact₁ (n + 1) n (by simp)).epi_f_iff]
    exact hLn.eq_of_tgt _ _
  let _ : Mono δ := hmono
  let _ : Epi δ := hepi
  exact isIso_of_mono_of_epi δ

/-- Unconditional homology-object form of (4.5) for the standard models. -/
def standardFHomologyShiftIso
    (G : AddCommGrpCat.{u}) (q n : ℕ) :
    (FAlternatingKernelSequence G q).X₁.homology n ≅
      (FAlternatingKernelSequence G q).X₃.homology (n + 1) := by
  let _ : IsIso (FConnectingHom G q n) :=
    standardFConnectingHom_isIso G q n
  exact (asIso (FConnectingHom G q n)).symm

/-- The unconditional homotopy--homology statement (4.5):
`π_n F(G,q+1) ≅ H~_{n+1}(K(G,q+1); ℤ)`. -/
def standardFiberHomotopyReducedHomologyIso
    (G : AddCommGrpCat.{u}) (q n : ℕ) :
    SimplicialAbelianHomotopy (F G (q + 1)) n ≅
      ReducedIntegralHomology (K G (q + 1)) (n + 1) :=
  (normalizedAlternatingHomologyIso (F G (q + 1)) n).trans
    (standardFHomologyShiftIso G q n)

end GeneralSphereT.StandardModels
