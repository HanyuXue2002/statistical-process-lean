import Formalization.Section4StandardSimplexLClassification
import Formalization.SimplicialCoboundarySquare

set_option linter.style.header false

/-!
# Section 4: cocycles on a standard simplex and the Dold--Kan sphere

This file complements `Section4StandardSimplexLClassification`.  The signed
anchored coordinates there identify an arbitrary cochain with

* its values on the faces containing vertex `0`, and
* the values of its coboundary on the anchored faces one degree higher.

Consequently a cocycle is determined freely by the first row.  Reindexing
that row by the active Dold--Kan summands gives the local classification

`Z^q(Δ^n;G) ≃ K(G,q)_n`.

We then prove that the genuine simplicial map
`d : L(G,q+1) ⟶ K(G,q+1)` is exactly ordinary simplicial coboundary under
the `L`-classification and this `K`-classification.
-/

noncomputable section

open CategoryTheory Opposite SimplexCategory Simplicial
open AlgebraicTopology.DoldKan

namespace GeneralSphereT.DoldKanExplicitBridge

universe u

/-- Degree-`q` cocycles on the standard simplex, in literal range--kernel
cochain notation. -/
abbrev StandardCocycle (n q : ℕ) (G : Type u) [AddCommGroup G] :=
  LinearMap.ker
    (SimplicialCochain.coboundary (G := G) (standardSimplex n) q)

/-! ## A cocycle is freely determined by its anchored values -/

/-- A cochain is a cocycle exactly when its coboundary vanishes on the
anchored faces.  The reverse implication uses `δ²=0`: the two anchored rows
of `δc` are then both zero, and the signed disk-coordinate chart is
injective. -/
theorem coboundary_eq_zero_iff_anchored
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (c : StandardCochain n q G) :
    SimplicialCochain.coboundary (standardSimplex n) q c = 0 ↔
      ∀ a : AnchoredFace n (q + 1),
        cochainFaceEmbeddingLinearEquiv n (q + 1) G
          (SimplicialCochain.coboundary (standardSimplex n) q c) a.1 = 0 := by
  constructor
  · intro hc a
    rw [hc]
    rfl
  · intro hanchored
    let dc : StandardCochain n (q + 1) G :=
      SimplicialCochain.coboundary (standardSimplex n) q c
    have hcoordinates :
        cochainEquivAnchoredDiskCoordinates n (q + 1) G
            (cochainFaceEmbeddingLinearEquiv n (q + 1) G dc) = 0 := by
      apply Prod.ext
      · funext a
        exact hanchored a
      · funext a
        change orderedCoboundary n (q + 1) G
          (cochainFaceEmbeddingLinearEquiv n (q + 1) G dc) a.1 = 0
        rw [← congrFun
          (cochainFaceEmbeddingLinearEquiv_coboundary
            n (q + 1) G dc) a.1]
        have hsq := SimplicialCochain.coboundary_coboundary
          (G := G) (standardSimplex n) q c
        change SimplicialCochain.coboundary (standardSimplex n) (q + 1) dc = 0
          at hsq
        rw [hsq]
        rfl
    have hface : cochainFaceEmbeddingLinearEquiv n (q + 1) G dc = 0 :=
      (cochainEquivAnchoredDiskCoordinates n (q + 1) G).injective <| by
        simpa using hcoordinates
    have hdc : dc = 0 :=
      (cochainFaceEmbeddingLinearEquiv n (q + 1) G).injective <| by
        simpa using hface
    exact hdc

/-- Restrict a standard-simplex cocycle to its anchored `q`-faces. -/
def standardCocycleToAnchored (n q : ℕ) (G : Type u) [AddCommGroup G] :
    StandardCocycle n q G →+ (AnchoredFace n q → G) where
  toFun z a := cochainFaceEmbeddingLinearEquiv n q G z.1 a.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Reconstruct the unique cocycle with prescribed anchored values by
putting zero in the anchored coboundary row. -/
def standardCocycleOfAnchored (n q : ℕ) (G : Type u) [AddCommGroup G]
    (b : AnchoredFace n q → G) : StandardCocycle n q G := by
  let faceCochain : FaceEmbedding n q → G :=
    fromAnchoredDiskCoordinates n q G (b, 0)
  let c : StandardCochain n q G :=
    (cochainFaceEmbeddingLinearEquiv n q G).symm faceCochain
  refine ⟨c, ?_⟩
  rw [LinearMap.mem_ker]
  apply (coboundary_eq_zero_iff_anchored n q G c).2
  intro a
  have hrows := congrArg (fun p : AnchoredDiskCoordinates n q G => p.2 a)
    (toAnchoredDiskCoordinates_fromAnchoredDiskCoordinates n q G (b, 0))
  change orderedCoboundary n q G faceCochain a.1 = 0 at hrows
  rw [cochainFaceEmbeddingLinearEquiv_coboundary n q G c]
  simpa [c, faceCochain] using hrows

@[simp]
theorem standardCocycleToAnchored_ofAnchored
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (b : AnchoredFace n q → G) :
    standardCocycleToAnchored n q G
      (standardCocycleOfAnchored n q G b) = b := by
  funext a
  have hrows := congrArg (fun p : AnchoredDiskCoordinates n q G => p.1 a)
    (toAnchoredDiskCoordinates_fromAnchoredDiskCoordinates n q G (b, 0))
  change fromAnchoredDiskCoordinates n q G (b, 0) a.1 = b a at hrows
  change cochainFaceEmbeddingLinearEquiv n q G
    ((cochainFaceEmbeddingLinearEquiv n q G).symm
      (fromAnchoredDiskCoordinates n q G (b, 0))) a.1 = b a
  rw [(cochainFaceEmbeddingLinearEquiv n q G).apply_symm_apply]
  exact hrows

@[simp]
theorem standardCocycleOfAnchored_toAnchored
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (z : StandardCocycle n q G) :
    standardCocycleOfAnchored n q G
      (standardCocycleToAnchored n q G z) = z := by
  apply Subtype.ext
  apply (cochainFaceEmbeddingLinearEquiv n q G).injective
  apply (cochainEquivAnchoredDiskCoordinates n q G).injective
  calc
    cochainEquivAnchoredDiskCoordinates n q G
        (cochainFaceEmbeddingLinearEquiv n q G
          (standardCocycleOfAnchored n q G
            (standardCocycleToAnchored n q G z)).1) =
      (standardCocycleToAnchored n q G z, 0) := by
        change cochainEquivAnchoredDiskCoordinates n q G
            (cochainFaceEmbeddingLinearEquiv n q G
              ((cochainFaceEmbeddingLinearEquiv n q G).symm
                (fromAnchoredDiskCoordinates n q G
                  (standardCocycleToAnchored n q G z, 0)))) =
          (standardCocycleToAnchored n q G z, 0)
        rw [(cochainFaceEmbeddingLinearEquiv n q G).apply_symm_apply]
        exact toAnchoredDiskCoordinates_fromAnchoredDiskCoordinates n q G
          (standardCocycleToAnchored n q G z, 0)
    _ = cochainEquivAnchoredDiskCoordinates n q G
        (cochainFaceEmbeddingLinearEquiv n q G z.1) := by
      apply Prod.ext
      · funext a
        rfl
      · funext a
        have hz :
            SimplicialCochain.coboundary (standardSimplex n) q z.1 = 0 :=
          z.2
        change 0 = orderedCoboundary n q G
          (cochainFaceEmbeddingLinearEquiv n q G z.1) a.1
        rw [← congrFun
          (cochainFaceEmbeddingLinearEquiv_coboundary n q G z.1) a.1, hz]
        rfl

/-- The elementary local classification: cocycles on `Δ^n` are freely
parametrized by their values on anchored `q`-faces. -/
def standardCocycleEquivAnchored
    (n q : ℕ) (G : Type u) [AddCommGroup G] :
    StandardCocycle n q G ≃+ (AnchoredFace n q → G) where
  toFun := standardCocycleToAnchored n q G
  invFun := standardCocycleOfAnchored n q G
  left_inv := standardCocycleOfAnchored_toAnchored n q G
  right_inv := standardCocycleToAnchored_ofAnchored n q G
  map_add' := (standardCocycleToAnchored n q G).map_add

/-! ## Identification with the actual Dold--Kan sphere -/

/-- The local classification `Z^q(Δ^n;G) ≃ K(G,q)_n`. -/
def standardCocycleEquivKLevel
    (n q : ℕ) (G : Type u) [AddCommGroup G] :
    StandardCocycle n q G ≃+
      ↑((StandardModels.K (AddCommGrpCat.of G) q).obj (op ⦋n⦌)) := by
  change StandardCocycle n q G ≃+
    ↑(Γ₀.Obj.obj₂ (StandardModels.sphereComplex (AddCommGrpCat.of G) q)
      (op ⦋n⦌))
  exact (standardCocycleEquivAnchored n q G).trans
    ((gammaCoordinateEquivAnchored n q G).symm.toAddEquiv.trans
      (sphereGammaLevelEquivCoordinates (AddCommGrpCat.of G) n q).symm)

/-- The `K`-classification reads an `n`-simplex back as the anchored values
of its representing cocycle. -/
theorem standardCocycleEquivKLevel_coordinates
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (z : StandardCocycle n q G) :
    gammaCoordinateEquivAnchored n q G
        (sphereGammaLevelEquivCoordinates (AddCommGrpCat.of G) n q
          (standardCocycleEquivKLevel n q G z)) =
      standardCocycleToAnchored n q G z := by
  change gammaCoordinateEquivAnchored n q G
      (sphereGammaLevelEquivCoordinates (AddCommGrpCat.of G) n q
        ((sphereGammaLevelEquivCoordinates (AddCommGrpCat.of G) n q).symm
          ((gammaCoordinateEquivAnchored n q G).symm
            (standardCocycleToAnchored n q G z)))) = _
  rw [(sphereGammaLevelEquivCoordinates
      (AddCommGrpCat.of G) n q).apply_symm_apply,
    (gammaCoordinateEquivAnchored n q G).apply_symm_apply]

/-- Ordinary coboundary, regarded as a cocycle one degree higher. -/
def standardCoboundaryCocycle
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (c : StandardCochain n q G) : StandardCocycle n (q + 1) G :=
  ⟨SimplicialCochain.coboundary (standardSimplex n) q c,
    SimplicialCochain.coboundary_coboundary
      (G := G) (standardSimplex n) q c⟩

set_option backward.isDefEq.respectTransparency false in
/-- Under the standard-simplex classifications, the genuine map
`d : L(G,q+1) ⟶ K(G,q+1)` is literally ordinary simplicial coboundary. -/
theorem standardClassifications_d_eq_coboundary
    (n q : ℕ) (G : Type u) [AddCommGroup G]
    (c : StandardCochain n q G) :
    (StandardModels.d (AddCommGrpCat.of G) (q + 1)).app (op ⦋n⦌)
        (standardCochainEquivLLevel n q G c) =
      standardCocycleEquivKLevel n (q + 1) G
        (standardCoboundaryCocycle n q G c) := by
  apply (sphereGammaLevelEquivCoordinates
    (AddCommGrpCat.of G) n (q + 1)).injective
  apply (gammaCoordinateEquivAnchored n (q + 1) G).injective
  ext a
  rw [standardCochainEquiv_d_apply]
  rw [standardCocycleEquivKLevel_coordinates]
  rfl

end GeneralSphereT.DoldKanExplicitBridge
