import Formalization.ReducedBoundary
import Mathlib.Algebra.Homology.Double
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.Algebra.Category.Grp.Abelian

set_option linter.style.header false

/-!
# Section 4: the standard `K(G,q)` and `L(G,q)` models

The simplicial abelian groups used in Section 4 do not have to be rebuilt
simplex by simplex.  Under Dold--Kan, `K(G,q)` is the complex with `G`
concentrated in degree `q`, while `L(G,q)` is the two-term disk complex
`G --id--> G` in degrees `q` and `q-1` (and is zero when `q = 0`).

This file records those definitions and the chain map corresponding to the
simplicial coboundary `L(G,q) -> K(G,q)`.  Thus the paper's standard models
are tied directly to Mathlib's Dold--Kan equivalence, rather than introduced
through an additional abstract interface.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category

namespace GeneralSphereT.StandardModels

universe u

/-- The chain complex `G[q]`, with `G` concentrated in degree `q`. -/
abbrev sphereComplex (G : AddCommGrpCat.{u}) (q : ℕ) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  (HomologicalComplex.single AddCommGrpCat (ComplexShape.down ℕ) q).obj G

/-- The two-term disk complex in degrees `q` and `q-1`.

For `q = 0` the paper never uses `L(G,0)`; assigning the zero complex makes
the definition total without introducing a positivity proof into every type.
-/
def diskComplex (G : AddCommGrpCat.{u}) : ℕ → ChainComplex AddCommGrpCat.{u} ℕ
  | 0 => HomologicalComplex.zero
  | q + 1 =>
      HomologicalComplex.double (𝟙 G)
        (ComplexShape.down_mk (q + 1) q rfl)

@[simp]
theorem diskComplex_zero (G : AddCommGrpCat.{u}) :
    diskComplex G 0 = (HomologicalComplex.zero :
      ChainComplex AddCommGrpCat.{u} ℕ) :=
  rfl

@[simp]
theorem diskComplex_succ (G : AddCommGrpCat.{u}) (q : ℕ) :
    diskComplex G (q + 1) =
      HomologicalComplex.double (𝟙 G)
        (ComplexShape.down_mk (q + 1) q rfl) :=
  rfl

/-- The projection of the disk complex onto its top-degree sphere complex. -/
def diskToSphereSucc (G : AddCommGrpCat.{u}) (q : ℕ) :
    HomologicalComplex.double (𝟙 G)
        (ComplexShape.down_mk (q + 1) q rfl) ⟶
      sphereComplex G (q + 1) :=
  HomologicalComplex.mkHomToSingle
    (HomologicalComplex.doubleXIso₀ (𝟙 G)
      (ComplexShape.down_mk (q + 1) q rfl)).hom
    (fun i hi => by
      have hraw : q + 1 + 1 = i := by
        simpa only [ComplexShape.down_Rel] using hi
      have hi' : i = q + 2 := by omega
      subst hi'
      rw [HomologicalComplex.double_d_eq_zero₀]
      · simp
      · omega)

/-- The chain map corresponding to `d : L(G,q) -> K(G,q)`. -/
def diskToSphere (G : AddCommGrpCat.{u}) :
    (q : ℕ) → diskComplex G q ⟶ sphereComplex G q
  | 0 => 0
  | q + 1 => diskToSphereSucc G q

/-- Mathlib's Dold--Kan inverse, named locally for readability. -/
abbrev denormalize :
    ChainComplex AddCommGrpCat.{u} ℕ ⥤ SimplicialObject AddCommGrpCat.{u} :=
  CategoryTheory.Abelian.DoldKan.Γ

/-- The standard Eilenberg--Mac Lane simplicial abelian group `K(G,q)`. -/
abbrev K (G : AddCommGrpCat.{u}) (q : ℕ) :
    SimplicialObject AddCommGrpCat.{u} :=
  denormalize.obj (sphereComplex G q)

/-- The standard contractible cochain-path simplicial abelian group `L(G,q)`. -/
abbrev L (G : AddCommGrpCat.{u}) (q : ℕ) :
    SimplicialObject AddCommGrpCat.{u} :=
  denormalize.obj (diskComplex G q)

/-- The standard simplicial coboundary `L(G,q) -> K(G,q)`. -/
abbrev d (G : AddCommGrpCat.{u}) (q : ℕ) : L G q ⟶ K G q :=
  denormalize.map (diskToSphere G q)

/-- By construction, normalizing `K(G,q)` recovers the one-term complex
`G[q]`. -/
def normalizedKIso (G : AddCommGrpCat.{u}) (q : ℕ) :
    CategoryTheory.Abelian.DoldKan.N.obj (K G q) ≅ sphereComplex G q :=
  (CategoryTheory.Abelian.DoldKan.equivalence
    (A := AddCommGrpCat.{u})).counitIso.app (sphereComplex G q)

/-- By construction, normalizing `L(G,q)` recovers its two-term disk
complex.  This is the precise Dold--Kan form of the observation that `L` is
the cochain-path object. -/
def normalizedLIso (G : AddCommGrpCat.{u}) (q : ℕ) :
    CategoryTheory.Abelian.DoldKan.N.obj (L G q) ≅ diskComplex G q :=
  (CategoryTheory.Abelian.DoldKan.equivalence
    (A := AddCommGrpCat.{u})).counitIso.app (diskComplex G q)

/-- Normalization carries the simplicial map `d : L(G,q) → K(G,q)` back
to the defining projection of the two-term disk complex onto `G[q]`. -/
theorem normalized_d (G : AddCommGrpCat.{u}) (q : ℕ) :
    CategoryTheory.Abelian.DoldKan.N.map (d G q) ≫
        (normalizedKIso G q).hom =
      (normalizedLIso G q).hom ≫ diskToSphere G q := by
  exact (CategoryTheory.Abelian.DoldKan.equivalence
    (A := AddCommGrpCat.{u})).counitIso.hom.naturality
      (diskToSphere G q)

end GeneralSphereT.StandardModels
