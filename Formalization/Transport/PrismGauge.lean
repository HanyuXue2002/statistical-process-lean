import Formalization.Transport.PrismMultiplier

noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra OpenDisk.PhaseDuality
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance : Fintype (Simplex X d) := Fintype.ofFinite _

private def facetEdge {p : ℕ} (θ : EM G (q+1) p → Phase) (σ : Simplex X d) (u v : Cochain X q G) : Phase :=
  -pullCochain (affineField X q) θ (segmentList (layerOf X q u) (layerOf X q v) (spatialVertices X d σ))

private theorem facetEdge_local {p : ℕ} (θ : EM G (q+1) p → Phase) (σ : Simplex X d)
    (f g : Fin 2 → Cochain X q G) (eq : ∀ i, restrictCochain X q ⟨σ.val,σ.property.1⟩ (f i) =
      restrictCochain X q ⟨σ.val,σ.property.1⟩ (g i)) :
    facetEdge X q d θ σ (f 0) (f 1) = facetEdge X q d θ σ (g 0) (g 1) := by
  let χ := pullCochain (affineField X q) θ
  let lay (i : Fin 2) (x : V) := (i,x)
  have e := equal_on_walks (π:=Prod.snd) (χ.comp (vertices (layerLift X q f))) (χ.comp (vertices (layerLift X q g)))
    (facet_weights_local X q d θ σ f g eq)
    (segment_walk (a:=lay 0) (b:=lay 1) (fun _ => rfl) (fun _ => rfl) (spatialVertices X d σ))
  simp only [LinearMap.comp_apply,vertices_segment] at e
  exact congrArg Neg.neg e

private theorem facetEdge_physical {p : ℕ} (θ : EM G (q+1) p → Phase) (σ : Simplex X d)
    (v v' s s' : Cochain X q G)
    (hs : restrictCochain X q ⟨σ.val,σ.property.1⟩ s = restrictCochain X q ⟨σ.val,σ.property.1⟩ s')
    (hv : restrictCochain X (q+1) ⟨σ.val,σ.property.1⟩ (coboundary X q v) =
      restrictCochain X (q+1) ⟨σ.val,σ.property.1⟩ (coboundary X q v')) :
    facetEdge X q d θ σ v (v+s) = facetEdge X q d θ σ v' (v'+s') := by
  let S : NonemptySimplex X := ⟨σ.val,σ.property.1⟩
  let r := restrictCochain (G:=G) X q S
  have hz : localCoboundary X q S (r (v'-v))=0 := by
    have e := DFunLike.congr_fun (restrictCochain_coboundary (G:=G) X q S) (v'-v)
    change _ = localCoboundary X q S (r (v'-v)) at e
    rw [← e]
    change restrictCochain X (q+1) S (coboundary X q (v'-v))=0
    rw [map_sub,map_sub,sub_eq_zero]
    exact hv.symm
  obtain ⟨z,hz,hr⟩ := simplicial_local_closed_extension X q S (r (v'-v)) hz
  have h₀ : r (v+z)=r v' := by change r z=r (v'-v) at hr; rw [map_add,hr,map_sub]; abel
  have h₁ : r (v+s+z)=r (v'+s') := by
    rw [show v+s+z=v+z+s by abel,map_add r (v+z) s,map_add r v' s',h₀]
    exact congrArg (r v' + ·) hs
  have hw : gen (spatialVertices X d σ) ∈ spatialChains X := by
    apply Submodule.subset_span
    refine ⟨_,S,List.pairwise_ofFn.mpr (fun _ _ h => (σ.val.orderEmbOfFin σ.property.2).monotone h.le),?_,rfl⟩
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact σ.val.orderEmbOfFin_mem σ.property.2 i
  have e := closedShift_segment X q θ v (v+s) z hz hw
  dsimp only at e
  simp only [segment,extend_gen] at e
  have es : facetEdge X q d θ σ (v+z) (v+s+z)=facetEdge X q d θ σ v (v+s) := congrArg Neg.neg e
  rw [← es]
  apply facetEdge_local X q d θ σ ![v+z,v+s+z] ![v',v'+s']
  intro i
  fin_cases i
  · exact h₀
  · exact h₁

private def edgePart (θ : EM G (q+1) (d+1) → Phase) (coeff : Simplex X d → ℤ) (σ : Simplex X d)
    (x : Cochain X q G × State (G:=G) X q) : Phase :=
  let v := liftState X q x.2
  coeff σ • facetEdge X q d θ σ v (v+x.1)

private theorem physical_edge_sum (θ : EM G (q+1) (d+1) → Phase) (coeff : Simplex X d → ℤ)
    (s : Cochain X q G) (a : State (G:=G) X q) :
    physicalEdge X q d θ coeff s a = ∑ σ, edgePart X q d θ coeff σ (s,a) := by
  unfold physicalEdge affineEdge orientedFacets
  simp only [map_sum,map_smul,segment,extend_gen,edgePart,facetEdge,smul_neg,Finset.sum_neg_distrib]
  rfl

theorem physicalEdge_localTable (θ : EM G (q+1) (d+1) → Phase) (hn : NormalizedOnEM θ) (coeff : Simplex X d → ℤ) :
    ∃ g, ∀ s a, physicalEdge X q d θ coeff s a = evaluate g (edgeRead (topFacetData (G:=G) X d q) s a) := by
  classical
  let L := topFacetData (G:=G) X d q
  let R := fun σ (x : Cochain X q G × State (G:=G) X q) => (L.primitiveRes σ x.1,L.physicalRes σ x.2)
  let B := edgePart X q d θ coeff
  have eq (σ : Simplex X d) (x y) (h : R σ x=R σ y) : B σ x=B σ y := by
    apply congrArg (coeff σ • ·)
    apply facetEdge_physical
    · exact congrArg Prod.fst h
    · rw [liftState_spec,liftState_spec]
      exact congrArg Prod.snd h
  let f := fun σ s a => if h : ∃ x, R σ x=(s,a) then B σ h.choose else 0
  apply normalized_one L _ _ f
  · intro s a
    rw [physical_edge_sum]
    apply Finset.sum_congr rfl
    intro σ _
    have h : ∃ x, R σ x=R σ (s,a) := ⟨_,rfl⟩
    change B σ (s,a) = if he : ∃ x, R σ x=R σ (s,a) then B σ he.choose else 0
    rw [dif_pos h]
    exact (eq σ h.choose (s,a) h.choose_spec).symm
  · intro a
    rw [physical_edge_sum]
    apply Finset.sum_eq_zero
    intro σ _
    simp only [edgePart,facetEdge,add_zero]
    rw [pullCochain_degenerate _ (affineField_normalized X) θ hn (segment_repeated _ _),neg_zero,smul_zero]

theorem physicalPrism_sub (ω η : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ)
    (t s : Cochain X q G) (a : State (G:=G) X q) :
    physicalPrism X q d (ω-η) coeff t s a = physicalPrism X q d ω coeff t s a - physicalPrism X q d η coeff t s a := by
  have h : pullCochain (affineField X q) (ω-η) = pullCochain (affineField X q) ω - pullCochain (affineField X q) η := by
    apply Finsupp.lhom_ext'
    intro ys
    apply LinearMap.ext_ring
    change pullCochain _ (ω-η) (gen ys) = pullCochain _ ω (gen ys) - pullCochain _ η (gen ys)
    simp only [pullCochain,gen,evaluate_single,one_zsmul,homogeneous]
    split <;> simp
  unfold physicalPrism affineMultiplier
  rw [h,LinearMap.sub_apply]
  abel

/-- Cohomologous normalized representatives give the same class under one simultaneous
facet rephasing. The rephasing comes from the segment integral of the primitive. -/
theorem prism_equivalent_of_coboundary (ω η : EM G (q+1) (d+2) → Phase) (θ : EM G (q+1) (d+1) → Phase)
    (hn : NormalizedOnEM θ) (h : η-ω=phaseDifferential θ) (coeff : Simplex X d → ℤ)
    (hz : boundary (orientedFacets X d coeff)=0) :
    Equivalent (topFacetData (G:=G) X d q) (fun x => physicalPrism X q d ω coeff x.1 x.2.1 x.2.2)
      (fun x => physicalPrism X q d η coeff x.1 x.2.1 x.2.2) := by
  obtain ⟨f,hf⟩ := physicalEdge_localTable X q d θ hn coeff
  refine ⟨f,fun t s a => ?_⟩
  simp only [← physicalPrism_sub,h,physicalPrism_of_coboundary X q d θ coeff hz,hf]

end GeneralSphereT.Transport.Prism
