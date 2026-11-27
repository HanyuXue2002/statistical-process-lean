import Formalization.Section4DoldKanModels

set_option linter.style.header false

/-!
# Section 4: the explicit Dold--Kan bridge

Mathlib's inverse Dold--Kan functor is not opaque.  In simplicial degree
`Δ`, it is the finite coproduct indexed by the epimorphisms out of `Δ`:

`(Γ C)(Δ) = ⨿_{A : Splitting.IndexSet Δ} C_{len(A)}`.

This file exposes that formula for the standard models and records the two
compatibility statements needed by the paper.  The first says that `Γ` sends
a chain map to the same map on every coproduct summand.  Applied to
`diskToSphere`, this is the degreewise formula for `d : L(G,q) ⟶ K(G,q)`.
The second says that, after normalized Moore chains, this map is exactly the
two-term-complex projection used to define it.

The further identification of these coproduct coordinates with the usual
oriented cochains on a standard simplex involves a separate signed basis
change (epimorphisms versus injective faces).  Mathlib currently does not
package that basis change.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open AlgebraicTopology.DoldKan

namespace GeneralSphereT.StandardModels

universe u

/-- The explicit object used by Mathlib for `Γ C` in simplicial degree `Δ`.
Its index `A` is an epimorphism from `Δ.unop`; its summand is the chain group
in degree equal to the length of the target of that epimorphism. -/
abbrev gammaLevel (C : ChainComplex AddCommGrpCat.{u} ℕ)
    (Δ : SimplexCategoryᵒᵖ) : AddCommGrpCat.{u} :=
  Γ₀.Obj.obj₂ C Δ

/-- The inverse Dold--Kan functor is definitionally the explicit finite
coproduct `gammaLevel`. -/
def denormalizeLevelIso (C : ChainComplex AddCommGrpCat.{u} ℕ)
    (Δ : SimplexCategoryᵒᵖ) :
    (denormalize.obj C).obj Δ ≅ gammaLevel C Δ :=
  Iso.refl _

/-- In degree `Δ`, `K(G,q)` is the coproduct of the indicated groups
`(G[q])_{len(A)}`, one for every epimorphism out of `Δ.unop`. -/
def KLevelIso (G : AddCommGrpCat.{u}) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) :
    (K G q).obj Δ ≅
      Γ₀.Obj.obj₂ (sphereComplex G q) Δ :=
  Iso.refl _

/-- In degree `Δ`, `L(G,q)` is the coproduct of the indicated groups from
the two-term disk complex, one for every epimorphism out of `Δ.unop`. -/
def LLevelIso (G : AddCommGrpCat.{u}) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) :
    (L G q).obj Δ ≅
      Γ₀.Obj.obj₂ (diskComplex G q) Δ :=
  Iso.refl _

/-- The preceding formula specialized to the standard `n`-simplex.  Thus
the coordinates of an `n`-simplex of `K(G,q)` are indexed by the monotone
surjections `[n] ↠ [r]`, with coefficient group `(G[q])_r`. -/
def KStandardSimplexIso (G : AddCommGrpCat.{u}) (q n : ℕ) :
    (K G q).obj (op ⦋n⦌) ≅
      Γ₀.Obj.obj₂ (sphereComplex G q) (op ⦋n⦌) :=
  Iso.refl _

/-- The explicit `Γ` coordinates of `L(G,q)` on the standard `n`-simplex.
Only the two chain degrees of the disk complex can contribute. -/
def LStandardSimplexIso (G : AddCommGrpCat.{u}) (q n : ℕ) :
    (L G q).obj (op ⦋n⦌) ≅
      Γ₀.Obj.obj₂ (diskComplex G q) (op ⦋n⦌) :=
  Iso.refl _

/-- On each epimorphism-indexed summand, `Γ f` is literally the corresponding
component of the chain map `f`. -/
theorem denormalize_map_on_summand
    {C D : ChainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D)
    (Δ : SimplexCategoryᵒᵖ)
    (A : SimplicialObject.Splitting.IndexSet Δ) :
    ((Γ₀.splitting C).cofan Δ).inj A ≫
        (denormalize.map f).app Δ =
      f.f A.1.unop.len ≫ ((Γ₀.splitting D).cofan Δ).inj A := by
  change ((Γ₀.splitting C).cofan Δ).inj A ≫
      (Γ₀.splitting C).desc Δ
        (fun B => f.f B.1.unop.len ≫
          ((Γ₀.splitting D).cofan Δ).inj B) = _
  exact (Γ₀.splitting C).ι_desc Δ _ A

/-- The simplicial map `d : L(G,q) ⟶ K(G,q)` acts on every explicit
`Γ`-summand by the matching component of `diskToSphere`. -/
theorem d_on_gamma_summand (G : AddCommGrpCat.{u}) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ)
    (A : SimplicialObject.Splitting.IndexSet Δ) :
    ((Γ₀.splitting (diskComplex G q)).cofan Δ).inj A ≫
        (d G q).app Δ =
      (diskToSphere G q).f A.1.unop.len ≫
        ((Γ₀.splitting (sphereComplex G q)).cofan Δ).inj A := by
  exact denormalize_map_on_summand (diskToSphere G q) Δ A

/-- The same formula in the standard `n`-simplex degree. -/
theorem d_on_standard_simplex_summand (G : AddCommGrpCat.{u}) (q n : ℕ)
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    ((Γ₀.splitting (diskComplex G q)).cofan (op ⦋n⦌)).inj A ≫
        (d G q).app (op ⦋n⦌) =
      (diskToSphere G q).f A.1.unop.len ≫
        ((Γ₀.splitting (sphereComplex G q)).cofan (op ⦋n⦌)).inj A := by
  exact d_on_gamma_summand G q (op ⦋n⦌) A

/-- Componentwise form of the normalized Dold--Kan square.  This is the
coordinate-free chain-level statement that the standard simplicial
coboundary is represented by the disk-to-sphere map. -/
theorem normalized_d_degree (G : AddCommGrpCat.{u}) (q n : ℕ) :
    (CategoryTheory.Abelian.DoldKan.N.map (d G q)).f n ≫
        (normalizedKIso G q).hom.f n =
      (normalizedLIso G q).hom.f n ≫ (diskToSphere G q).f n := by
  exact congrArg (fun f => f.f n) (normalized_d G q)

end GeneralSphereT.StandardModels
