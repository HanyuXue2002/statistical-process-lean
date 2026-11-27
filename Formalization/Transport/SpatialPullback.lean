import Formalization.Transport.AffineField

noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.DoldKanExplicitBridge GeneralSphereT.SimplicialCochain GeneralSphereT.StandardModels
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (X : AbstractSimplicialComplex V) (q : ℕ)

def spatialRead (v : Cochain X q G) (xs : Fin (q+1) → V) : G :=
  affineField X q (fun i => (v,xs i))

theorem spatialRead_simplex (v : Cochain X q G) (x : (orderedComplexSSet X) _⦋q⦌) :
    spatialRead X q v x.val = (cochainEquivNormalizedCochainHom X q v)
      ((orderedComplexSSet X).ιNormalizedChainComplex (R:=integralCoefficients) x (ULift.up (1:ℤ))) := by
  classical
  by_cases hi : Function.Injective x.val
  · have hx := (mem_orderedComplexSSet_nonDegenerate_iff_injective X x).mpr hi
    let n := (⟨x,hx⟩ : (orderedComplexSSet X).nonDegenerate q)
    rw [cochainEquivNormalizedCochainHom_nonDegenerate_generator X q v n]
    have hcard : (Finset.univ.image x.val).card = q+1 := by
      rw [Finset.card_image_of_injective _ hi]
      simp
    have hs : Finset.univ.image x.val ∈ X := x.property
    have both : Finset.univ.image x.val ∈ X ∧ (Finset.univ.image x.val).card = q+1 := ⟨hs,hcard⟩
    simp only [spatialRead,affineField]
    rw [dif_pos both]
    rfl
  · have hx : x ∈ (orderedComplexSSet X).degenerate q := by
      by_contra ha
      apply hi
      apply (mem_orderedComplexSSet_nonDegenerate_iff_injective X x).mp
      exact ha
    have hcard : (Finset.univ.image x.val).card ≠ q+1 := by
      intro eq
      apply hi
      have e : (Finset.univ.image x.val).card = (Finset.univ : Finset (Fin (q+1))).card := by simpa using eq
      simpa using Finset.card_image_iff.mp e
    rw [(orderedComplexSSet X).ιNormalizedChainComplex_eq_zero _ hx]
    simp [spatialRead,affineField,hcard]

theorem spatialRead_d (v : Cochain X q G) (x : (orderedComplexSSet X) _⦋q+1⦌) :
    spatialRead X (q+1) (coboundary X q v) x.val =
      ∑ i : Fin (q+2), ((-1:ℤ)^i.val) • spatialRead X q v (fun j => x.val (i.succAbove j)) := by
  have e := (orderedComplexSSet X).ιNormalizedChainComplex_d (R:=integralCoefficients) x
  have w := congrArg (fun k => k ≫ cochainEquivNormalizedCochainHom X q v) e
  rw [Category.assoc,← cochainEquivNormalizedCochainHom_coboundary,Preadditive.sum_comp] at w
  have atOne := congrArg (fun k : integralCoefficients ⟶ AddCommGrpCat.of G => k (ULift.up (1:ℤ))) w
  dsimp only at atOne
  rw [spatialRead_simplex]
  simp only [Preadditive.zsmul_comp,ConcreteCategory.comp_apply] at atOne
  rw [atOne,addCommGrpCat_fintype_sum_apply]
  simp only [addCommGrpCat_zsmul_apply,ConcreteCategory.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (((-1:ℤ)^i.val) • ·) (spatialRead_simplex X q v ((orderedComplexSSet X).δ i x)).symm

theorem string_spatial_coboundary {p : ℕ} (v : Cochain X q G) (x : (orderedComplexSSet X) _⦋p⦌) :
    coboundary (standardSimplex p) q (stringCochain (spatialRead X q v) x.val) =
      stringCochain (spatialRead X (q+1) (coboundary X q v)) x.val := by
  apply (cochainFaceEmbeddingLinearEquiv p (q+1) G).injective
  rw [cochainFaceEmbeddingLinearEquiv_coboundary]
  funext e
  simp only [orderedCoboundary_apply,cochainFaceEmbeddingLinearEquiv_apply,stringCochain_face]
  let E : ⦋q+1⦌ ⟶ ⦋p⦌ := SimplexCategory.Hom.mk e.toOrderHom
  exact (spatialRead_d X q v ((orderedComplexSSet X).map E.op x)).symm

/-- Adding the same closed cochain to every temporal layer fixes the
classifying simplex itself, prior even to pairing with a cocycle. -/
theorem classifyingValue_closed_shift {p : ℕ} (f : Fin (p+1) → Cochain X q G)
    (x : (orderedComplexSSet X) _⦋p⦌) (z : Cochain X q G) (hz : coboundary X q z = 0) :
    classifyingValue (affineField X q) (fun i => (f i + z,x.val i)) =
      classifyingValue (affineField X q) (fun i => (f i,x.val i)) := by
  classical
  have e : stringCochain (affineField X q) (fun i => (f i + z,x.val i)) =
      stringCochain (affineField X q) (fun i => (f i,x.val i)) + stringCochain (spatialRead X q z) x.val := by
    ext t
    obtain ⟨b,rfl⟩ := (faceEmbeddingEquivSimplex p q).surjective t
    simp only [Finsupp.add_apply,stringCochain_face,spatialRead,affineField]
    split <;> simp_all
  unfold classifyingValue
  apply congrArg (standardGlobalKValue p (q+1))
  apply Subtype.ext
  change coboundary (standardSimplex p) q _ = coboundary (standardSimplex p) q _
  rw [e,map_add,string_spatial_coboundary X q z x,hz]
  have h : stringCochain (spatialRead X (q+1) (0 : Cochain X (q+1) G)) x.val = 0 := by
    ext t
    obtain ⟨b,rfl⟩ := (faceEmbeddingEquivSimplex p (q+1)).surjective t
    simp [stringCochain_face,spatialRead,affineField]
  rw [h,add_zero]

end GeneralSphereT.Transport.Prism

