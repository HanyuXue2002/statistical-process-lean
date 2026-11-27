import Formalization.Section4DoldKanExplicitBridge

set_option linter.style.header false

/-!
# Section 4: the standard-simplex classification of the Dold--Kan disk

This packages the explicit Gamma-coordinate calculation as the exact local
statement used in the paper: a degree-`q` cochain on the standard simplex
`Δ^n` is the same thing as an `n`-simplex of `L(G,q+1)`.  Under this
identification the standard map `d : L(G,q+1) ⟶ K(G,q+1)` is ordinary
simplicial coboundary.
-/

noncomputable section

open CategoryTheory Opposite SimplexCategory Simplicial
open AlgebraicTopology.DoldKan

namespace GeneralSphereT.DoldKanExplicitBridge

universe u

/-- The local classification `C^q(Δ^n;G) ≃ L(G,q+1)_n` obtained directly
from the two active rows in the explicit Dold--Kan formula. -/
def standardCochainEquivLLevel
    (n q : ℕ) (G : Type u) [AddCommGroup G] :
    StandardCochain n q G ≃+
      ↑((StandardModels.L (AddCommGrpCat.of G) (q + 1)).obj (op ⦋n⦌)) := by
  change StandardCochain n q G ≃+
    ↑(Γ₀.Obj.obj₂ (StandardModels.diskComplex (AddCommGrpCat.of G) (q + 1))
      (op ⦋n⦌))
  exact standardCochainEquivGammaDiskCoordinates n q G |>.toAddEquiv |>.trans
    (diskGammaLevelEquivCoordinates (AddCommGrpCat.of G) n q).symm

set_option backward.isDefEq.respectTransparency false in
/-- In the local classifications, applying the genuine simplicial map `d`
to the simplex represented by `c` gives the simplex represented by `δc`. -/
theorem standardCochainEquiv_d
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (c : StandardCochain n q G) :
    sphereGammaLevelEquivCoordinates (AddCommGrpCat.of G) n (q + 1)
        ((StandardModels.d (AddCommGrpCat.of G) (q + 1)).app (op ⦋n⦌)
          (standardCochainEquivLLevel n q G c)) =
      (standardCochainEquivGammaDiskCoordinates n q G c).2 := by
  classical
  change sphereGammaLevelEquivCoordinates (AddCommGrpCat.of G) n (q + 1)
      ((StandardModels.d (AddCommGrpCat.of G) (q + 1)).app (op ⦋n⦌)
        ((diskGammaLevelEquivCoordinates (AddCommGrpCat.of G) n q).symm
          (standardCochainEquivGammaDiskCoordinates n q G c))) = _
  rw [actualD_eq_secondProjection]
  exact congrArg Prod.snd
    ((diskGammaLevelEquivCoordinates (AddCommGrpCat.of G) n q).apply_symm_apply
      (standardCochainEquivGammaDiskCoordinates n q G c))

/-- Coordinatewise, the preceding second row is precisely the ordinary
simplicial coboundary, including the incidence signs. -/
theorem standardCochainEquiv_d_apply
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (c : StandardCochain n q G) (a : AnchoredFace n (q + 1)) :
    (gammaCoordinateEquivAnchored n (q + 1) G
      (sphereGammaLevelEquivCoordinates (AddCommGrpCat.of G) n (q + 1)
        ((StandardModels.d (AddCommGrpCat.of G) (q + 1)).app (op ⦋n⦌)
          (standardCochainEquivLLevel n q G c)))) a =
      cochainFaceEmbeddingLinearEquiv n (q + 1) G
        (SimplicialCochain.coboundary (standardSimplex n) q c) a.1 := by
  rw [standardCochainEquiv_d]
  simpa [standardCochainEquivGammaDiskCoordinates,
    gammaDiskCoordinateEquivAnchored] using
      signedDisk_second_coordinate_eq_coboundary n q G c a

end GeneralSphereT.DoldKanExplicitBridge
