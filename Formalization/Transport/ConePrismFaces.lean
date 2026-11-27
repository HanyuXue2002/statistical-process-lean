import Formalization.Transport.OrientedConeCycle
import Formalization.Transport.ConePrismTransgression

/-! The constant-time end of the lifted prism evaluates the literal relative
simplicial map on the oriented spatial cone. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.StandardModels GeneralSphereT.DoldKanExplicitBridge GeneralSphereT.SimplicialCochain
open GeneralSphereT.PathAlgebra FacetRestrictionData GeneralSphereT.Section4 RelativeChains
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (X : AbstractSimplicialComplex V)

def simplexOfEmbedding {p : ℕ} (e : Fin (p+1) ↪o V) (hm : Finset.univ.image e ∈ X) :
    OrderedSimplicialMap (standardSimplex p) X where
  toOrderEmbedding := e
  map_mem := fun {s} hs => (X.isRelLowerSet_faces hm).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (Finset.map_nonempty.mpr hs)

theorem constant_diskValue (q p : ℕ) (v : Cochain X q G) (x : Fin (p+1) → V) (hx : StrictMono x)
    (hm : Finset.univ.image x ∈ X) :
    diskValue (affineField X q) (fun i => (v,x i))=cochainLValue X q (op ⦋p⦌) (orderedString X x ⟨hx.monotone,hm⟩) v := by
  classical
  let e : Fin (p+1) ↪o V := OrderEmbedding.ofStrictMono x hx
  let F := simplexOfEmbedding X e hm
  have top : F.toSSetMap.app (op ⦋p⦌) (standardSimplexTop p)=orderedString X x ⟨hx.monotone,hm⟩ := rfl
  have pull : stringCochain (affineField X q) (fun i => (v,x i))=F.pullback q v := by
    ext s
    obtain ⟨b,rfl⟩ := (faceEmbeddingEquivSimplex p q).surjective s
    rw [stringCochain_face,OrderedSimplicialMap.pullback_apply]
    let t := F.mapSimplex (faceEmbeddingEquivSimplex p q b)
    have eq : Finset.univ.image (fun i => x (b i))=t.val := by
      ext y
      change y ∈ Finset.univ.image (fun i => x (b i)) ↔ y ∈ (Set.finite_range b).toFinset.map e.toEmbedding
      simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_map,Set.Finite.mem_toFinset,Set.mem_range]
      constructor
      · rintro ⟨i,rfl⟩; exact ⟨b i,⟨i,rfl⟩,rfl⟩
      · rintro ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
    unfold affineField
    dsimp only
    rw [dite_eq_left (show Finset.univ.image (fun i => x (b i)) ∈ X ∧ (Finset.univ.image (fun i => x (b i))).card=q+1 from eq ▸ t.property)]
    exact congrArg v (Subtype.ext eq)
  unfold diskValue
  rw [pull,standardGlobalLValue_apply]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (cochainToLMap_pullback F q v) (op ⦋p⦌)) (standardSimplexTop p)
  exact h.symm

local instance faceLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance faceLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance faceOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (d : ℕ)
def coneVertices (σ : Simplex X d) : Fin (d+2) → Option V :=
  Fin.cons none (fun i => some (σ.val.orderEmbOfFin σ.property.2 i))

theorem coneVertices_strict (σ : Simplex X d) : StrictMono (coneVertices X d σ) :=
  Fin.strictMono_cons.mpr ⟨fun _ => WithBot.bot_lt_coe _,(coneBottomOrderEmbedding (V:=V)).strictMono.comp (σ.val.orderEmbOfFin σ.property.2).strictMono⟩

omit [Fintype V] in
theorem coneVertices_mem (σ : Simplex X d) : Finset.univ.image (coneVertices X d σ) ∈ simplicialCone X := by
  rw [mem_simplicialCone]
  refine ⟨Finset.image_nonempty.mpr Finset.univ_nonempty,Or.inr ?_⟩
  have h : coneBaseVertices (Finset.univ.image (coneVertices X d σ))=σ.val := by
    ext v
    rw [mem_coneBaseVertices]
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi⟩
      revert hi
      refine Fin.cases (by simp [coneVertices]) (fun j h => ?_) i
      change some (σ.val.orderEmbOfFin σ.property.2 j)=some v at h
      exact (Option.some.inj h) ▸ σ.val.orderEmbOfFin_mem σ.property.2 j
    · intro hv
      obtain ⟨i,hi⟩ := (Finset.range_orderEmbOfFin σ.val σ.property.2).ge hv
      exact ⟨i.succ,congrArg some hi⟩
  exact h ▸ σ.property.1

local instance faceFintype : Fintype (Simplex X d) := Fintype.ofFinite _

theorem orientedCone_sum (coeff : Simplex X d → ℤ) :
    orientedCone X d coeff=∑ σ : Simplex X d, coeff σ • gen (List.ofFn (coneVertices X d σ)) := by
  classical
  unfold orientedCone orientedFacets
  simp only [map_sum,map_smul,vertices_gen,cons_gen,List.map_ofFn]
  apply Finset.sum_congr rfl
  intro σ _
  rw [List.ofFn_succ (f:=coneVertices X d σ)]
  rfl

end GeneralSphereT.Transport.Prism

