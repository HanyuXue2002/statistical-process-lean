import Formalization.Section4CochainMapNaturality
import Formalization.Section4StandardSimplexConstructionCompatibility

/-! Pulling the actual Dold--Kan classifying field back to a vertex string.
A temporal vertex picks the primitive at the first vertex of a spatial face,
the Alexander--Whitney convention for the 0-cochain in (2.8). -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.DoldKanExplicitBridge GeneralSphereT.SimplicialCochain GeneralSphereT.StandardModels

universe u
variable {Y : Type u} {G : Type} [AddCommGroup G]
variable {q p m : ℕ}

def stringCochain (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y) : StandardCochain p q G :=
  (cochainFaceEmbeddingLinearEquiv p q G).symm (fun e => field (fun j => x (e j)))

theorem stringCochain_face (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y) (e : FaceEmbedding p q) :
    stringCochain field x (faceEmbeddingEquivSimplex p q e) = field (fun j => x (e j)) := by
  rw [← cochainFaceEmbeddingLinearEquiv_apply]
  unfold stringCochain
  rw [LinearEquiv.apply_symm_apply]

def faceInclusion (e : FaceEmbedding p m) : OrderedSimplicialMap (standardSimplex m) (standardSimplex p) where
  toOrderEmbedding := e
  map_mem := fun h => Finset.map_nonempty.mpr h

theorem map_face (e : FaceEmbedding p m) (b : FaceEmbedding m q) :
    (faceInclusion e).mapSimplex (faceEmbeddingEquivSimplex m q b) = faceEmbeddingEquivSimplex p q (b.trans e) := by
  apply Subtype.ext
  ext x
  change x ∈ ((Set.finite_range b).toFinset.map e.toEmbedding) ↔ x ∈ (Set.finite_range (b.trans e)).toFinset
  simp only [Finset.mem_map,Set.Finite.mem_toFinset,Set.mem_range,RelEmbedding.coe_toEmbedding,RelEmbedding.trans_apply]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨b i,⟨i,rfl⟩,rfl⟩

theorem pullback_string (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y) (e : FaceEmbedding p m) :
    (faceInclusion e).pullback q (stringCochain field x) = stringCochain field (fun i => x (e i)) := by
  ext s
  obtain ⟨b,rfl⟩ := (faceEmbeddingEquivSimplex m q).surjective s
  rw [OrderedSimplicialMap.pullback_apply,map_face,stringCochain_face,stringCochain_face]
  rfl

def classifyingValue (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y) :
    (K (AddCommGrpCat.of G) (q+1)).obj (op ⦋p⦌) :=
  standardGlobalKValue p (q+1) (standardCoboundaryCocycle p q G (stringCochain field x))

theorem classifyingValue_face (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y) (e : FaceEmbedding p m) :
    (K (AddCommGrpCat.of G) (q+1)).map (show ⦋m⦌ ⟶ ⦋p⦌ from SimplexCategory.Hom.mk e.toOrderHom).op (classifyingValue field x) =
      classifyingValue field (fun i => x (e i)) := by
  let F := faceInclusion e
  let x₀ := standardSimplexTop m
  let E : ⦋m⦌ ⟶ ⦋p⦌ := SimplexCategory.Hom.mk e.toOrderHom
  let v := stringCochain field x
  have top : F.toSSetMap.app (op ⦋m⦌) x₀ =
      (orderedComplexSSet (standardSimplex p)).map E.op (standardSimplexTop p) := by
    apply Subtype.ext
    ext i
    rfl
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cochainToLMap_pullback F q v) (op ⦋m⦌)) x₀
  change (cochainToLMap _ q v).app _ (F.toSSetMap.app _ x₀) = _ at h
  rw [top,cochainToLMap_naturality_apply] at h
  have lp : (L (AddCommGrpCat.of G) (q+1)).map E.op (standardGlobalLValue p q v) =
      standardGlobalLValue m q (stringCochain field (fun i => x (e i))) := by
    change _ = (cochainToLMap _ q _).app _ x₀
    rw [← pullback_string field x e]
    exact h
  unfold classifyingValue
  rw [← standardGlobal_d_eq_coboundary,← standardGlobal_d_eq_coboundary]
  have nat := ConcreteCategory.congr_hom ((d (AddCommGrpCat.of G) (q+1)).naturality E.op) (standardGlobalLValue p q v)
  change (d _ _).app _ ((L _ _).map E.op _) = (K _ _).map E.op ((d _ _).app _ _) at nat
  rw [← nat,lp]

variable {V : Type u} [LinearOrder V] [Fintype V]
def affineField (X : AbstractSimplicialComplex V) (q : ℕ)
    (v : Fin (q+1) → Cochain X q G × V) : G := by
  classical
  let spatial := Finset.univ.image (fun i => (v i).2)
  exact if h : spatial ∈ X ∧ spatial.card=q+1 then (v 0).1 ⟨spatial,h⟩ else 0

end GeneralSphereT.Transport.Prism

