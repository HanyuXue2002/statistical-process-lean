import Formalization.Section4DoldKanDiskContraction

set_option linter.style.header false

/-!
# Section 4: the full extra degeneracy of the Dold--Kan disk

The face identities in `Section4DoldKanDiskContraction` already give the
chain contraction needed for reduced homology.  Here we verify the remaining
compatibility with simplicial degeneracies.  This upgrades the same explicit
operator to a genuine extra degeneracy and hence to an actual simplicial
contraction, as required by the relative nullhomotopy in (4.21).
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open AlgebraicTopology.DoldKan
open SimplicialObject.Augmented

namespace GeneralSphereT.StandardModels
namespace DoldKanDiskContraction

universe u

open SSet.Augmented.StandardSimplex

/-! ## Finite-ordinal identities -/

/-- Repeating a noninitial source vertex commutes with adjoining a new
initial vertex while keeping the codomain fixed. -/
theorem σ_succ_comp_shift {n : ℕ} {Δ : SimplexCategory}
    (e : ⦋n⦌ ⟶ Δ) (i : Fin (n + 1)) :
    SimplexCategory.σ i.succ ≫ shift e =
      shift (SimplexCategory.σ i ≫ e) := by
  ext x
  cases x using Fin.cases with
  | zero =>
      simp [shift, shiftFun, SimplexCategory.σ]
      rfl
  | succ x =>
      simp [shift, shiftFun, SimplexCategory.σ]
      rfl

/-- The same identity for the raised epi index. -/
theorem σ_succ_comp_raise {n : ℕ} {Δ : SimplexCategory}
    (e : ⦋n⦌ ⟶ Δ) (i : Fin (n + 1)) :
    SimplexCategory.σ i.succ ≫ raise e =
      raise (SimplexCategory.σ i ≫ e) := by
  ext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
      simp [raise, shift, shiftFun, standardizeCodomain,
        SimplexCategory.σ, SimplexCategory.δ]

/-! ## Degeneracy naturality on Gamma summands -/

set_option backward.isDefEq.respectTransparency false in
/-- The extra operator commutes with every simplicial degeneracy on a single
Gamma summand.  Unlike a face, a degeneracy preserves surjectivity, so the
epi--mono factorization has no exceptional branch. -/
theorem cofan_inj_diskExtraS_comp_σ_succ
    (G : AddCommGrpCat.{u}) (q n r : ℕ) (i : Fin (n + 1))
    (e : ⦋n⦌ ⟶ ⦋r⦌) [Epi e] :
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj
          (SimplicialObject.Splitting.IndexSet.mk e) ≫
        diskExtraS G q n ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.σ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n⦌)).inj
            (SimplicialObject.Splitting.IndexSet.mk e) ≫
        (Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.σ i).op ≫ diskExtraS G q (n + 1) := by
  let A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌) :=
    SimplicialObject.Splitting.IndexSet.mk e
  let f : ⦋n + 1⦌ ⟶ ⦋r⦌ := SimplexCategory.σ i ≫ e
  let B : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌) :=
    SimplicialObject.Splitting.IndexSet.mk f
  change
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj A ≫ diskExtraS G q n ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.σ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.σ i).op ≫ diskExtraS G q (n + 1)
  let _ : Epi f := by
    dsimp [f]
    infer_instance
  have hdeg :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.σ i).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q) (𝟙 ⦋r⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj B := by
    simpa only [A, B, f, SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) A
        (SimplexCategory.σ i).op (e := f) (i := 𝟙 ⦋r⦌) (by
          change f ≫ 𝟙 ⦋r⦌ = SimplexCategory.σ i ≫ e
          simp [f])
  have hshift :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj (shiftIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.σ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q) (𝟙 ⦋r⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 2⦌)).inj (shiftIndex B) := by
    simpa only [A, B, f, shiftIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (shiftIndex A)
        (SimplexCategory.σ i.succ).op
        (e := shift f) (i := 𝟙 ⦋r⦌) (by
          change shift f ≫ 𝟙 ⦋r⦌ =
            SimplexCategory.σ i.succ ≫ shift e
          rw [comp_id, σ_succ_comp_shift])
  have hraise :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj (raiseIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.σ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (𝟙 ⦋r + 1⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 2⦌)).inj (raiseIndex B) := by
    simpa only [A, B, f, raiseIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (raiseIndex A)
        (SimplexCategory.σ i.succ).op
        (e := raise f) (i := 𝟙 ⦋r + 1⦌) (by
          change raise f ≫ 𝟙 ⦋r + 1⦌ =
            SimplexCategory.σ i.succ ≫ raise e
          rw [comp_id, σ_succ_comp_raise])
  rw [← Category.assoc, cofan_inj_diskExtraS, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [hshift, hraise]
  simp only [Γ₀.Obj.Termwise.mapMono_id, id_comp]
  rw [← Category.assoc, hdeg]
  simp only [Γ₀.Obj.Termwise.mapMono_id, id_comp]
  change
    dNext r (diskContractingHom G q) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 2⦌)).inj (shiftIndex B) +
        diskContractingHom G q r (r + 1) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 2⦌)).inj (raiseIndex B) =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj B ≫ diskExtraS G q (n + 1)
  exact (cofan_inj_diskExtraS G q (n + 1) B).symm

set_option backward.isDefEq.respectTransparency false in
/-- Full degeneracy compatibility of the explicit disk extra operator. -/
theorem diskExtraS_comp_σ_succ
    (G : AddCommGrpCat.{u}) (q n : ℕ) (i : Fin (n + 1)) :
    diskExtraS G q n ≫
        (Γ₀.obj (diskSuccComplex G q)).σ i.succ =
      (Γ₀.obj (diskSuccComplex G q)).σ i ≫
        diskExtraS G q (n + 1) := by
  apply (Γ₀.splitting (diskSuccComplex G q)).hom_ext'
  rintro ⟨⟨⟨r⟩⟩, ⟨e, he⟩⟩
  simpa only [SimplicialObject.σ, SimplicialObject.Splitting.IndexSet.mk]
    using cofan_inj_diskExtraS_comp_σ_succ G q n r i e

/-- The previously optional naturality package is inhabited by the explicit
finite-ordinal calculation. -/
theorem diskRemainingNaturalityData
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    RemainingNaturalityData G q where
  s_comp_sigma := diskExtraS_comp_σ_succ G q

/-- A genuine extra degeneracy on the standard Dold--Kan disk. -/
def standardDiskExtraDegeneracy
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    LExtraDegeneracy G q :=
  diskExtraDegeneracy G q (diskRemainingNaturalityData G q)

/-- The resulting actual simplicial contraction from zero to the identity. -/
def standardDiskSimplicialContraction
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    LSimplicialContraction G q :=
  diskSimplicialContraction G q (diskRemainingNaturalityData G q)

end DoldKanDiskContraction
end GeneralSphereT.StandardModels
