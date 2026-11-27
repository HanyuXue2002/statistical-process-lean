import Formalization.Transport.AffineField

noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.DoldKanExplicitBridge GeneralSphereT.SimplicialCochain GeneralSphereT.StandardModels
variable {G : Type} [AddCommGroup G] {Y : Type*} {p m q : ℕ}

private abbrev simplexHom (θ : Fin (m+1) →o Fin (p+1)) : ⦋m⦌ ⟶ ⦋p⦌ := SimplexCategory.Hom.mk θ

theorem standardL_face (v : StandardCochain p q G) (e : FaceEmbedding p m) :
    (L (AddCommGrpCat.of G) (q+1)).map (simplexHom e.toOrderHom).op (standardGlobalLValue p q v) =
      standardGlobalLValue m q ((faceInclusion e).pullback q v) := by
  let F := faceInclusion e
  let E := simplexHom e.toOrderHom
  have top : F.toSSetMap.app (op ⦋m⦌) (standardSimplexTop m) =
      (orderedComplexSSet (standardSimplex p)).map E.op (standardSimplexTop p) := by
    apply Subtype.ext
    ext i
    rfl
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cochainToLMap_pullback F q v) (op ⦋m⦌)) (standardSimplexTop m)
  change (cochainToLMap _ q v).app _ (F.toSSetMap.app _ (standardSimplexTop m)) = _ at h
  rw [top,cochainToLMap_naturality_apply] at h
  exact h

theorem standardL_faces_detect {a b : (L (AddCommGrpCat.of G) (q+1)).obj (op ⦋p⦌)}
    (h : ∀ e : FaceEmbedding p q, (L (AddCommGrpCat.of G) (q+1)).map (simplexHom e.toOrderHom).op a =
      (L (AddCommGrpCat.of G) (q+1)).map (simplexHom e.toOrderHom).op b) : a=b := by
  obtain ⟨v,rfl⟩ := (standardGlobalLEquiv (G:=G) p q).surjective a
  obtain ⟨w,rfl⟩ := (standardGlobalLEquiv (G:=G) p q).surjective b
  apply congrArg (standardGlobalLEquiv (G:=G) p q)
  ext s
  obtain ⟨e,rfl⟩ := (faceEmbeddingEquivSimplex p q).surjective s
  have E := h e
  change (L _ _).map _ (standardGlobalLValue p q v) = (L _ _).map _ (standardGlobalLValue p q w) at E
  rw [standardL_face,standardL_face] at E
  have H := (standardGlobalLEquiv (G:=G) q q).injective E
  have H' := DFunLike.congr_fun H (faceEmbeddingEquivSimplex q q (OrderEmbedding.ofStrictMono id strictMono_id))
  have rid : (OrderEmbedding.ofStrictMono id strictMono_id).trans e = e := by ext i; rfl
  simpa only [OrderedSimplicialMap.pullback_apply,map_face,rid] using H'

private theorem lowL_zero (hp : m<q) (y : (L (AddCommGrpCat.of G) (q+1)).obj (op ⦋m⦌)) : y=0 := by
  obtain ⟨v,rfl⟩ := (standardGlobalLEquiv (G:=G) m q).surjective y
  have h : v=0 := by
    ext s
    have h₁ := Finset.card_le_univ s.val
    have h₂ := s.property.2
    simp only [Fintype.card_fin] at h₁
    omega
  rw [h,map_zero]

private theorem map_low_zero (θ : Fin (q+1) →o Fin (p+1)) (hn : ¬Function.Injective θ)
    (a : (L (AddCommGrpCat.of G) (q+1)).obj (op ⦋p⦌)) :
    (L (AddCommGrpCat.of G) (q+1)).map (simplexHom θ).op a = 0 := by
  cases q with
  | zero => exact False.elim (hn (fun i j _ => Fin.ext (by omega)))
  | succ q =>
    obtain ⟨i,ρ,he⟩ := SimplexCategory.eq_σ_comp_of_not_injective (simplexHom θ) hn
    rw [he,op_comp,Functor.map_comp]
    change (L _ _).map _ ((L _ _).map ρ.op a) = 0
    rw [lowL_zero (Nat.lt_succ_self q) ((L (AddCommGrpCat.of G) (q+2)).map ρ.op a),map_zero]

private theorem restrictAtDegree (field : (Fin (q+1) → Y) → G)
    (hfield : ∀ x, ¬Function.Injective x → field x = 0) (x : Fin (p+1) → Y) (θ : Fin (q+1) →o Fin (p+1)) :
    (L (AddCommGrpCat.of G) (q+1)).map (simplexHom θ).op (standardGlobalLValue p q (stringCochain field x)) =
      standardGlobalLValue q q (stringCochain field (fun i => x (θ i))) := by
  by_cases hi : Function.Injective θ
  · let e : FaceEmbedding p q := OrderEmbedding.ofStrictMono θ (θ.monotone.strictMono_of_injective hi)
    change (L _ _).map (simplexHom e.toOrderHom).op _ = _
    rw [standardL_face,pullback_string]
    rfl
  · rw [map_low_zero θ hi]
    have h : stringCochain field (fun i => x (θ i)) = 0 := by
      ext s
      obtain ⟨e,rfl⟩ := (faceEmbeddingEquivSimplex q q).surjective s
      rw [stringCochain_face]
      apply hfield
      intro inj
      apply hi
      intro a b he
      obtain ⟨i,rfl⟩ := (Finite.surjective_of_injective e.injective) a
      obtain ⟨j,rfl⟩ := (Finite.surjective_of_injective e.injective) b
      exact congrArg e (inj (congrArg x he))
    rw [h,map_zero]

theorem classifyingValue_reparam (field : (Fin (q+1) → Y) → G)
    (hfield : ∀ x, ¬Function.Injective x → field x = 0) (x : Fin (p+1) → Y) (θ : Fin (m+1) →o Fin (p+1)) :
    (K (AddCommGrpCat.of G) (q+1)).map (simplexHom θ).op (classifyingValue field x) =
      classifyingValue field (fun i => x (θ i)) := by
  have hL : (L (AddCommGrpCat.of G) (q+1)).map (simplexHom θ).op (standardGlobalLValue p q (stringCochain field x)) =
      standardGlobalLValue m q (stringCochain field (fun i => x (θ i))) := by
    apply standardL_faces_detect
    intro e
    have h := restrictAtDegree field hfield x (θ.comp e.toOrderHom)
    rw [standardL_face,pullback_string]
    change (L _ _).map (simplexHom e.toOrderHom).op ((L _ _).map (simplexHom θ).op _) = _
    exact (ConcreteCategory.congr_hom ((L (AddCommGrpCat.of G) (q+1)).map_comp
      (simplexHom θ).op (simplexHom e.toOrderHom).op) _).symm.trans h
  unfold classifyingValue
  rw [← standardGlobal_d_eq_coboundary,← standardGlobal_d_eq_coboundary]
  have nat := ConcreteCategory.congr_hom ((d (AddCommGrpCat.of G) (q+1)).naturality (simplexHom θ).op)
    (standardGlobalLValue p q (stringCochain field x))
  change (d _ _).app _ ((L _ _).map _ _) = (K _ _).map _ ((d _ _).app _ _) at nat
  rw [← nat,hL]

theorem affineField_normalized {V : Type*} [LinearOrder V] (X : AbstractSimplicialComplex V)
    (y : Fin (q+1) → Cochain X q G × V) (h : ¬Function.Injective y) : affineField X q y = 0 := by
  classical
  unfold affineField
  dsimp only
  split
  next he =>
    exfalso
    apply h
    have hcard : (Finset.univ.image (fun i => (y i).2)).card = (Finset.univ : Finset (Fin (q+1))).card := by
      simpa using he.2
    have inj : Function.Injective (fun i => (y i).2) := by simpa using Finset.card_image_iff.mp hcard
    exact fun _ _ h => inj (congrArg Prod.snd h)
  next => rfl

end GeneralSphereT.Transport.Prism

