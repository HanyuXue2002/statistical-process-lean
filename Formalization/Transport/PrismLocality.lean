import Formalization.Transport.PhysicalPrism
import Formalization.OpenDisk.PhaseDualityAveragingSimplicial

/-! Direct control of each oriented spatial summand in the triangle integral. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra

variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q d : ℕ)

def facetValue {p : ℕ} (ω : EM G (q+1) p → Phase) (σ : Simplex X d)
    (u v w : Cochain X q G) : Phase :=
  -pullCochain (affineField X q) ω (triangleList (fun x => (u,x)) (fun x => (v,x))
    (fun x => (w,x)) (spatialVertices X d σ))

def layerLift {I : Type*} (f : I → Cochain X q G) (x : I × V) := (f x.1,x.2)

theorem facet_weights_local {I : Type*} {p : ℕ} (ω : EM G (q+1) p → Phase) (σ : Simplex X d)
    (f g : I → Cochain X q G) (eq : ∀ i, restrictCochain X q ⟨σ.val,σ.property.1⟩ (f i) =
      restrictCochain X q ⟨σ.val,σ.property.1⟩ (g i))
    (ys : List (I × V)) (hw : Stretch (spatialVertices X d σ) (ys.map Prod.snd)) :
    let χ := pullCochain (affineField X q) ω
    (χ.comp (vertices (layerLift X q f))) (gen ys) = (χ.comp (vertices (layerLift X q g))) (gen ys) := by
  classical
  let χ := pullCochain (affineField X q) ω
  let lift (f : I → Cochain X q G) := layerLift X q f

  change χ (vertices (lift f) (gen ys)) = χ (vertices (lift g) (gen ys))
  rw [vertices_gen,vertices_gen]
  simp only [χ,pullCochain,gen,evaluate_single,one_zsmul]
  by_cases h : ys.length=p+1
  · let arr : Fin (p+1) → I × V := fun i => ys.get (i.cast h.symm)
    have ha : List.ofFn arr = ys := by
      apply List.ext_getElem
      · simp [h]
      · intro i hi hi'; rw [List.getElem_ofFn]; rfl
    rw [← ha,List.map_ofFn,List.map_ofFn,homogeneous_ofFn,homogeneous_ofFn]
    apply congrArg ω
    unfold classifyingValue
    congr 2
    apply Finsupp.ext
    intro s
    obtain ⟨b,rfl⟩ := (DoldKanExplicitBridge.faceEmbeddingEquivSimplex p q).surjective s
    rw [stringCochain_face,stringCochain_face]
    let faces := Finset.univ.image (fun j => (arr (b j)).2)
    have sub : faces ⊆ σ.val := by
      intro y hy
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      have mem : (arr (b j)).2 ∈ ys.map Prod.snd := by rw [← ha,List.map_ofFn]; exact List.mem_ofFn.mpr ⟨b j,rfl⟩
      obtain ⟨k,hk⟩ := List.mem_ofFn.mp (hw.mem mem)
      rw [← hk]
      exact σ.val.orderEmbOfFin_mem σ.property.2 k
    change (if he : faces ∈ X ∧ faces.card=q+1 then f (arr (b 0)).1 ⟨faces,he⟩ else 0) =
      (if he : faces ∈ X ∧ faces.card=q+1 then g (arr (b 0)).1 ⟨faces,he⟩ else 0)
    split <;> rename_i he
    · exact DFunLike.congr_fun (eq (arr (b 0)).1) ⟨⟨faces,he⟩,sub⟩
    · rfl
  · simp [homogeneous,h]

theorem facetValue_local {p : ℕ} (ω : EM G (q+1) p → Phase) (σ : Simplex X d)
    (f g : Fin 3 → Cochain X q G) (eq : ∀ i, restrictCochain X q ⟨σ.val,σ.property.1⟩ (f i) =
      restrictCochain X q ⟨σ.val,σ.property.1⟩ (g i)) :
    facetValue X q d ω σ (f 0) (f 1) (f 2) = facetValue X q d ω σ (g 0) (g 1) (g 2) := by
  classical
  let χ := pullCochain (affineField X q) ω
  let lift (f : Fin 3 → Cochain X q G) (x : Fin 3 × V) := (f x.1,x.2)
  let lay (i : Fin 3) (x : V) := (i,x)
  have weights := facet_weights_local X q d ω σ f g eq
  have e := equal_on_walks (π:=Prod.snd) (χ.comp (vertices (lift f))) (χ.comp (vertices (lift g))) weights
    (triangle_walk (a:=lay 0) (b:=lay 1) (c:=lay 2) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (spatialVertices X d σ))
  simp only [LinearMap.comp_apply,vertices_triangle] at e
  exact congrArg Neg.neg e

theorem facetValue_shift {p : ℕ} (ω : EM G (q+1) p → Phase) (σ : Simplex X d)
    (u v w z : Cochain X q G) (hz : coboundary X q z=0) :
    facetValue X q d ω σ (u+z) (v+z) (w+z) = facetValue X q d ω σ u v w := by
  let χ := pullCochain (affineField X q) ω
  let shift := fun y : Cochain X q G × V => (y.1+z,y.2)
  let lay (u : Cochain X q G) := fun x : V => (u,x)
  have e := equal_on_walks (π:=Prod.snd) (χ.comp (vertices shift)) χ (weight_shift X q d ω z hz σ)
    (triangle_walk (a:=lay u) (b:=lay v) (c:=lay w) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (spatialVertices X d σ))
  rw [LinearMap.comp_apply,vertices_triangle] at e
  exact congrArg Neg.neg e

/-- The summand for a given spatial simplex depends only on the two
restricted moves and the restricted physical configuration. -/
theorem facetValue_physical {p : ℕ} (ω : EM G (q+1) p → Phase) (σ : Simplex X d)
    (v v' s s' t t' : Cochain X q G)
    (hs : restrictCochain X q ⟨σ.val,σ.property.1⟩ s = restrictCochain X q ⟨σ.val,σ.property.1⟩ s')
    (ht : restrictCochain X q ⟨σ.val,σ.property.1⟩ t = restrictCochain X q ⟨σ.val,σ.property.1⟩ t')
    (hv : restrictCochain X (q+1) ⟨σ.val,σ.property.1⟩ (coboundary X q v) = restrictCochain X (q+1) ⟨σ.val,σ.property.1⟩ (coboundary X q v')) :
    facetValue X q d ω σ v (v+s) (v+s+t) = facetValue X q d ω σ v' (v'+s') (v'+s'+t') := by
  let σ' : NonemptySimplex X := ⟨σ.val,σ.property.1⟩
  let r := restrictCochain (G:=G) X q σ'
  have closed : localCoboundary X q σ' (r (v'-v)) = 0 := by
    have e := DFunLike.congr_fun (restrictCochain_coboundary (G:=G) X q σ') (v'-v)
    change _ = localCoboundary X q σ' (r (v'-v)) at e
    rw [← e]
    change restrictCochain X (q+1) σ' (coboundary X q (v'-v)) = 0
    rw [map_sub,map_sub,sub_eq_zero]
    exact hv.symm
  obtain ⟨z,hz,hr⟩ := simplicial_local_closed_extension X q σ' (r (v'-v)) closed
  have he : r (v+z) = r v' := by
    change r z = r (v'-v) at hr
    rw [map_add,hr,map_sub]
    abel
  rw [← facetValue_shift X q d ω σ v (v+s) (v+s+t) z hz]
  apply facetValue_local X q d ω σ ![v+z,v+s+z,v+s+t+z] ![v',v'+s',v'+s'+t']
  have e₁ : r (v+s+z) = r (v'+s') := by
    rw [show v+s+z = v+z+s by abel,map_add r (v+z) s,map_add r v' s',he]
    exact congrArg (r v' + ·) hs
  have e₂ : r (v+s+t+z) = r (v'+s'+t') := by
    rw [show v+s+t+z = (v+s+z)+t by abel,map_add r (v+s+z) t,map_add r (v'+s') t',e₁]
    exact congrArg (r (v'+s') + ·) ht
  intro i
  fin_cases i
  · exact he
  · exact e₁
  · exact e₂

end GeneralSphereT.Transport.Prism

