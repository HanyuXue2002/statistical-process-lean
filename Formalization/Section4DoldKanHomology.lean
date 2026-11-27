import Formalization.Section4DoldKanModels
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.SingleHomology

set_option linter.style.header false

/-!
# Section 4: homology of the Dold--Kan models

This file mechanically verifies the two elementary chain-complex calculations
behind the standard simplicial models.

* The two-term identity complex `diskComplex G (q + 1)` is contractible.  Its
  contracting homotopy has one nonzero component, from degree `q` to degree
  `q + 1`.  Consequently all of its homology objects are zero.
* The one-term complex `sphereComplex G q` has homology `G` in degree `q` and
  zero homology in every other degree.

Transporting these statements through `normalizedKIso` and `normalizedLIso`
gives the corresponding normalized-chain conclusions for `K(G,q)` and
`L(G,q + 1)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace GeneralSphereT.StandardModels

universe u

/-- The positive-degree branch of `diskComplex`, exposed as an abbreviation so
that the contracting-homotopy calculation sees the two-term complex without
transport casts. -/
abbrev diskSuccComplex (G : AddCommGrpCat.{u}) (q : ℕ) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  HomologicalComplex.double (𝟙 G)
    (ComplexShape.down_mk (q + 1) q rfl)

/-- The contracting operator of the two-term identity complex.  Its only
nonzero component is the inverse of the differential, from degree `q` to
degree `q + 1`. -/
def diskContractingHom (G : AddCommGrpCat.{u}) (q i j : ℕ) :
    (diskSuccComplex G q).X i ⟶ (diskSuccComplex G q).X j :=
  if hi : i = q then
    if hj : j = q + 1 then
      ((diskSuccComplex G q).XIsoOfEq hi).hom ≫
        (HomologicalComplex.doubleXIso₁ (𝟙 G)
          (ComplexShape.down_mk (q + 1) q rfl) (by omega)).hom ≫
        (HomologicalComplex.doubleXIso₀ (𝟙 G)
          (ComplexShape.down_mk (q + 1) q rfl)).inv ≫
        ((diskSuccComplex G q).XIsoOfEq hj).inv
    else 0
  else 0

/-- The contracting operator is zero outside arrows of the chain-complex
shape. -/
lemma diskContractingHom_zero (G : AddCommGrpCat.{u}) (q i j : ℕ)
    (h : ¬(ComplexShape.down ℕ).Rel j i) :
    diskContractingHom G q i j = 0 := by
  rw [ComplexShape.down_Rel] at h
  simp only [diskContractingHom]
  split_ifs with hi hj
  · subst i
    subst j
    exact (h rfl).elim
  · rfl
  · rfl

/-- The null-homotopic map associated to the contracting operator is the
identity in the top degree. -/
lemma diskNullHomotopicMap_f_top (G : AddCommGrpCat.{u}) (q : ℕ) :
    (Homotopy.nullHomotopicMap (diskContractingHom G q)).f (q + 1) =
      (𝟙 (diskSuccComplex G q) :
        diskSuccComplex G q ⟶ diskSuccComplex G q).f (q + 1) := by
  have r₂₁ : (ComplexShape.down ℕ).Rel (q + 2) (q + 1) := by
    rw [ComplexShape.down_Rel]
    omega
  have r₁₀ : (ComplexShape.down ℕ).Rel (q + 1) q := by
    rw [ComplexShape.down_Rel]
  rw [Homotopy.nullHomotopicMap_f r₂₁ r₁₀]
  rw [HomologicalComplex.double_d (𝟙 G)
    (ComplexShape.down_mk (q + 1) q rfl) (by omega)]
  simp [diskContractingHom, Category.assoc]

/-- The null-homotopic map associated to the contracting operator is the
identity in the bottom degree. -/
lemma diskNullHomotopicMap_f_bottom (G : AddCommGrpCat.{u}) (q : ℕ) :
    (Homotopy.nullHomotopicMap (diskContractingHom G q)).f q =
      (𝟙 (diskSuccComplex G q) :
        diskSuccComplex G q ⟶ diskSuccComplex G q).f q := by
  by_cases hq : q = 0
  · subst q
    have r₁₀ : (ComplexShape.down ℕ).Rel 1 0 := by
      rw [ComplexShape.down_Rel]
      omega
    have hn : ∀ l : ℕ, ¬(ComplexShape.down ℕ).Rel 0 l := by
      intro l h
      rw [ComplexShape.down_Rel] at h
      omega
    rw [Homotopy.nullHomotopicMap_f_of_not_rel_left r₁₀ hn]
    rw [HomologicalComplex.double_d (𝟙 G)
      (ComplexShape.down_mk 1 0 rfl) (by omega)]
    simp [diskContractingHom, Category.assoc]
  · have hsub : q - 1 ≠ q := by omega
    have r₂₁ : (ComplexShape.down ℕ).Rel (q + 1) q := by
      rw [ComplexShape.down_Rel]
    have r₁₀ : (ComplexShape.down ℕ).Rel q (q - 1) := by
      rw [ComplexShape.down_Rel]
      omega
    rw [Homotopy.nullHomotopicMap_f r₂₁ r₁₀]
    rw [HomologicalComplex.double_d_eq_zero₀ (𝟙 G)
      (ComplexShape.down_mk (q + 1) q rfl) q (q - 1) (by omega)]
    rw [HomologicalComplex.double_d (𝟙 G)
      (ComplexShape.down_mk (q + 1) q rfl) (by omega)]
    simp [diskContractingHom, hsub, Category.assoc]

/-- The equation `d h + h d = 1` for the standard two-term disk complex. -/
lemma diskNullHomotopicMap_eq_id (G : AddCommGrpCat.{u}) (q : ℕ) :
    Homotopy.nullHomotopicMap (diskContractingHom G q) =
      𝟙 (diskSuccComplex G q) := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases htop : n = q + 1
  · subst n
    exact diskNullHomotopicMap_f_top G q
  by_cases hbottom : n = q
  · subst n
    exact diskNullHomotopicMap_f_bottom G q
  exact (HomologicalComplex.isZero_double_X (𝟙 G)
    (ComplexShape.down_mk (q + 1) q rfl) n htop hbottom).eq_of_src _ _

/-- The explicit contraction of the positive-degree disk complex. -/
def diskSuccContractingHomotopy (G : AddCommGrpCat.{u}) (q : ℕ) :
    Homotopy (𝟙 (diskSuccComplex G q)) 0 := by
  rw [← diskNullHomotopicMap_eq_id G q]
  exact Homotopy.nullHomotopy (diskContractingHom G q)
    (diskContractingHom_zero G q)

/-- `diskComplex G (q + 1)` is contractible. -/
def diskComplexContractingHomotopy (G : AddCommGrpCat.{u}) (q : ℕ) :
    Homotopy (𝟙 (diskComplex G (q + 1))) 0 := by
  change Homotopy (𝟙 (diskSuccComplex G q)) 0
  exact diskSuccContractingHomotopy G q

/-- Equivalently, the standard disk complex is chain-homotopy equivalent to
the zero complex. -/
def diskComplexHomotopyEquivZero (G : AddCommGrpCat.{u}) (q : ℕ) :
    HomotopyEquiv (diskComplex G (q + 1))
      (HomologicalComplex.zero : ChainComplex AddCommGrpCat.{u} ℕ) where
  hom := 0
  inv := 0
  homotopyHomInvId := by
    change Homotopy (0 : diskSuccComplex G q ⟶ diskSuccComplex G q)
      (𝟙 (diskSuccComplex G q))
    exact (diskSuccContractingHomotopy G q).symm
  homotopyInvHomId := Homotopy.ofEq (by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (Limits.isZero_zero AddCommGrpCat).eq_of_src _ _)

/-- Every homology object of the two-term identity complex is zero. -/
lemma diskComplex_homology_isZero (G : AddCommGrpCat.{u}) (q n : ℕ) :
    IsZero ((diskComplex G (q + 1)).homology n) := by
  rw [IsZero.iff_id_eq_zero]
  have h := (diskComplexContractingHomotopy G q).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  exact h

/-- The two-term identity complex is exact in every degree. -/
lemma diskComplex_acyclic (G : AddCommGrpCat.{u}) (q : ℕ) :
    (diskComplex G (q + 1)).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact diskComplex_homology_isZero G q n

/-- The unique nonzero homology object of `sphereComplex G q` is canonically
`G`. -/
def sphereComplex_homology_iso (G : AddCommGrpCat.{u}) (q : ℕ) :
    (sphereComplex G q).homology q ≅ G :=
  HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.down ℕ) q G

/-- The one-term sphere complex has zero homology away from degree `q`. -/
lemma sphereComplex_homology_isZero_of_ne (G : AddCommGrpCat.{u})
    (q n : ℕ) (h : n ≠ q) :
    IsZero ((sphereComplex G q).homology n) :=
  HomologicalComplex.isZero_single_obj_homology
    (ComplexShape.down ℕ) q G n h

/-- Normalized homology of `K(G,q)` in degree `q`. -/
def normalizedK_homology_iso (G : AddCommGrpCat.{u}) (q : ℕ) :
    (CategoryTheory.Abelian.DoldKan.N.obj (K G q)).homology q ≅ G :=
  HomologicalComplex.homologyMapIso (normalizedKIso G q) q ≪≫
    sphereComplex_homology_iso G q

/-- Normalized homology of `K(G,q)` vanishes away from degree `q`. -/
lemma normalizedK_homology_isZero_of_ne (G : AddCommGrpCat.{u})
    (q n : ℕ) (h : n ≠ q) :
    IsZero
      ((CategoryTheory.Abelian.DoldKan.N.obj (K G q)).homology n) :=
  (HomologicalComplex.homologyMapIso
    (normalizedKIso G q) n).isZero_iff.mpr
      (sphereComplex_homology_isZero_of_ne G q n h)

/-- Normalized `L(G,q+1)` is itself chain-homotopy equivalent to zero. -/
def normalizedLHomotopyEquivZero (G : AddCommGrpCat.{u}) (q : ℕ) :
    HomotopyEquiv
      (CategoryTheory.Abelian.DoldKan.N.obj (L G (q + 1)))
      (HomologicalComplex.zero : ChainComplex AddCommGrpCat.{u} ℕ) :=
  (HomotopyEquiv.ofIso (normalizedLIso G (q + 1))).trans
    (diskComplexHomotopyEquivZero G q)

/-- All normalized homology objects of `L(G,q+1)` vanish. -/
lemma normalizedL_homology_isZero (G : AddCommGrpCat.{u}) (q n : ℕ) :
    IsZero
      ((CategoryTheory.Abelian.DoldKan.N.obj (L G (q + 1))).homology n) :=
  (HomologicalComplex.homologyMapIso
    (normalizedLIso G (q + 1)) n).isZero_iff.mpr
      (diskComplex_homology_isZero G q n)

end GeneralSphereT.StandardModels
