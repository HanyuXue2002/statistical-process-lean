import Formalization.Transport.PrismCoboundary
import Formalization.Transport.SpatialPullback
import Formalization.Transport.PrismSupport
import Formalization.SimplicialFacetData

noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality GeneralSphereT.SimplicialCochain

variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q d : ℕ)

def spatialVertices (σ : Simplex X d) : List V := List.ofFn (fun i => σ.val.orderEmbOfFin σ.property.2 i)

theorem weight_shift_on {p : ℕ} (ω : EM G (q+1) p → Phase) (z : Cochain X q G)
    (hz : coboundary X q z=0) (σ : NonemptySimplex X) (xs : List V)
    (sorted : xs.Pairwise (· ≤ ·)) (hm : ∀ y ∈ xs, y ∈ σ.val) (ys : List (Cochain X q G × V))
    (hw : Stretch xs (ys.map Prod.snd)) :
    let ψ := pullCochain (affineField X q) ω
    let shift := fun y : Cochain X q G × V => (y.1+z,y.2)
    ψ (vertices shift (gen ys)) = ψ (gen ys) := by
  classical
  dsimp only
  rw [vertices_gen]
  simp only [pullCochain,gen,evaluate_single,one_zsmul]
  by_cases h : ys.length=p+1
  · let arr : Fin (p+1) → Cochain X q G × V := fun i => ys.get (i.cast h.symm)
    have ha : List.ofFn arr = ys := by
      apply List.ext_getElem
      · simp [h]
      · intro i hi hi'
        rw [List.getElem_ofFn]
        rfl
    rw [← ha,List.map_ofFn,homogeneous_ofFn,homogeneous_ofFn]
    let v := fun i => (arr i).2
    have hw' : Stretch xs (List.ofFn v) := by
      rw [← ha,List.map_ofFn] at hw
      exact hw
    have mono : Monotone v := by
      intro i j hij
      rcases hij.eq_or_lt with rfl|e
      · exact le_rfl
      · exact List.pairwise_ofFn.mp (hw'.pairwise sorted) e
    let vv : Fin (p+1) →o V := ⟨v,mono⟩
    have sub : orderedSimplexSupport vv ⊆ σ.val := by
      intro y hy
      obtain ⟨i,rfl⟩ := (mem_orderedSimplexSupport vv y).mp hy
      have m := hw'.mem (List.mem_ofFn.mpr ⟨i,rfl⟩)
      exact hm _ m
    let x : (orderedComplexSSet X) _⦋p⦌ := ⟨vv,(X.isRelLowerSet_faces σ.property).2 sub
      (Finset.image_nonempty.mpr Finset.univ_nonempty)⟩
    exact congrArg ω (classifyingValue_closed_shift X q (fun i => (arr i).1) x z hz)
  · simp [homogeneous,h]

theorem weight_shift {p : ℕ} (ω : EM G (q+1) p → Phase) (z : Cochain X q G)
    (hz : coboundary X q z=0) (σ : Simplex X d) (ys : List (Cochain X q G × V))
    (hw : Stretch (spatialVertices X d σ) (ys.map Prod.snd)) :
    let ψ := pullCochain (affineField X q) ω
    let shift := fun y : Cochain X q G × V => (y.1+z,y.2)
    ψ (vertices shift (gen ys)) = ψ (gen ys) := by
  apply weight_shift_on X q ω z hz ⟨σ.val,σ.property.1⟩ _ _ _ ys hw
  · exact List.pairwise_ofFn.mpr (fun _ _ h => (σ.val.orderEmbOfFin σ.property.2).monotone h.le)
  · intro y hy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
    exact σ.val.orderEmbOfFin_mem σ.property.2 i

theorem affineMultiplier_closed_shift (ω : EM G (q+1) (d+2) → Phase)
    (coeff : Simplex X d → ℤ) (t s v z : Cochain X q G) (hz : coboundary X q z=0) :
    affineMultiplier X q d ω (orientedFacets X d coeff) t s (v+z) =
      affineMultiplier X q d ω (orientedFacets X d coeff) t s v := by
  classical
  let χ := pullCochain (affineField X q) ω
  let shift := fun y : Cochain X q G × V => (y.1+z,y.2)
  let lay (v : Cochain X q G) := fun x : V => (v,x)
  have each (σ : Simplex X d) :
      χ (triangleList (lay (v+z)) (lay (v+z+s)) (lay (v+z+s+t)) (spatialVertices X d σ)) =
      χ (triangleList (lay v) (lay (v+s)) (lay (v+s+t)) (spatialVertices X d σ)) := by
    have e := equal_on_walks (π:=Prod.snd) (χ.comp (vertices shift)) χ (weight_shift X q d ω z hz σ)
      (triangle_walk (a:=lay v) (b:=lay (v+s)) (c:=lay (v+s+t)) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (spatialVertices X d σ))
    rw [LinearMap.comp_apply,vertices_triangle] at e
    simpa [shift,lay,Function.comp_def,add_assoc,add_left_comm,add_comm] using e
  unfold affineMultiplier orientedFacets
  simp only [map_sum,map_smul]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro σ _
  simp only [triangle,extend_gen]
  exact congrArg (coeff σ • ·) (each σ)

def physicalPrism (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ)
    (t s : Cochain X q G) (a : LinearMap.range (coboundary (G:=G) X q)) : Phase :=
  affineMultiplier X q d ω (orientedFacets X d coeff) t s ((facetCoboundary_surjective X q a).choose)

theorem physicalPrism_on_primitive (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ)
    (t s v : Cochain X q G) :
    physicalPrism X q d ω coeff t s (coboundaryToRange X q v) =
      affineMultiplier X q d ω (orientedFacets X d coeff) t s v := by
  let w := (facetCoboundary_surjective X q (coboundaryToRange (G:=G) X q v)).choose
  have e : coboundary X q w = coboundary X q v :=
    congrArg Subtype.val (facetCoboundary_surjective X q (coboundaryToRange (G:=G) X q v)).choose_spec
  have h := affineMultiplier_closed_shift X q d ω coeff t s v (w-v) (by simp [e])
  change affineMultiplier X q d ω _ t s w = _
  rwa [show v+(w-v)=w by abel] at h

theorem physicalPrism_assoc (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ)
    (hc : ClosedOnEM ω) (hz : boundary (orientedFacets X d coeff) = 0)
    (r t s : Cochain X q G) (a : LinearMap.range (coboundary (G:=G) X q)) :
    physicalPrism X q d ω coeff t s a + physicalPrism X q d ω coeff r (s+t) a =
      physicalPrism X q d ω coeff r t (a+coboundaryToRange X q s) + physicalPrism X q d ω coeff (t+r) s a := by
  obtain ⟨v,rfl⟩ := facetCoboundary_surjective X q a
  rw [← map_add]
  simpa only [physicalPrism_on_primitive] using affineMultiplier_assoc X q d ω hc _ hz r t s v

theorem affineEdge_closed_shift (θ : EM G (q+1) (d+1) → Phase)
    (coeff : Simplex X d → ℤ) (s v z : Cochain X q G) (hz : coboundary X q z=0) :
    affineEdge X q d θ (orientedFacets X d coeff) s (v+z) =
      affineEdge X q d θ (orientedFacets X d coeff) s v := by
  classical
  let χ := pullCochain (affineField X q) θ
  let shift := fun y : Cochain X q G × V => (y.1+z,y.2)
  let lay (u : Cochain X q G) := fun x : V => (u,x)
  have each (σ : Simplex X d) :
      χ (segmentList (lay (v+z)) (lay (v+z+s)) (spatialVertices X d σ)) =
      χ (segmentList (lay v) (lay (v+s)) (spatialVertices X d σ)) := by
    have e := equal_on_walks (π:=Prod.snd) (χ.comp (vertices shift)) χ (weight_shift X q d θ z hz σ)
      (segment_walk (a:=lay v) (b:=lay (v+s)) (fun _ => rfl) (fun _ => rfl) (spatialVertices X d σ))
    rw [LinearMap.comp_apply,vertices_segment] at e
    simpa [shift,lay,Function.comp_def,add_assoc,add_left_comm,add_comm] using e
  unfold affineEdge orientedFacets
  simp only [map_sum,map_smul]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro σ _
  simp only [segment,extend_gen]
  exact congrArg (coeff σ • ·) (each σ)

def physicalEdge (θ : EM G (q+1) (d+1) → Phase) (coeff : Simplex X d → ℤ)
    (s : Cochain X q G) (a : LinearMap.range (coboundary (G:=G) X q)) : Phase :=
  affineEdge X q d θ (orientedFacets X d coeff) s ((facetCoboundary_surjective X q a).choose)

theorem physicalEdge_on_primitive (θ : EM G (q+1) (d+1) → Phase) (coeff : Simplex X d → ℤ)
    (s v : Cochain X q G) :
    physicalEdge X q d θ coeff s (coboundaryToRange X q v) =
      affineEdge X q d θ (orientedFacets X d coeff) s v := by
  let w := (facetCoboundary_surjective X q (coboundaryToRange (G:=G) X q v)).choose
  have e : coboundary X q w = coboundary X q v :=
    congrArg Subtype.val (facetCoboundary_surjective X q (coboundaryToRange (G:=G) X q v)).choose_spec
  have h := affineEdge_closed_shift X q d θ coeff s v (w-v) (by simp [e])
  change affineEdge X q d θ _ s w = _
  rwa [show v+(w-v)=w by abel] at h

theorem physicalPrism_of_coboundary (θ : EM G (q+1) (d+1) → Phase) (coeff : Simplex X d → ℤ)
    (hc : boundary (orientedFacets X d coeff)=0)
    (t s : Cochain X q G) (a : LinearMap.range (coboundary (G:=G) X q)) :
    physicalPrism X q d (phaseDifferential θ) coeff t s a =
      physicalEdge X q d θ coeff s a + physicalEdge X q d θ coeff t (a+coboundaryToRange X q s) -
      physicalEdge X q d θ coeff (s+t) a := by
  obtain ⟨v,rfl⟩ := facetCoboundary_surjective X q a
  rw [← map_add]
  simpa only [physicalPrism_on_primitive,physicalEdge_on_primitive] using
    affineMultiplier_of_coboundary X q d θ _ hc t s v

end GeneralSphereT.Transport.Prism

