import Formalization.Transport.LiftedPrismChains
import Formalization.Transport.ConePrismTransgression

/-! Vanishing of the side faces of the lifted segment for primitive cycles. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.StandardModels GeneralSphereT.DoldKanExplicitBridge GeneralSphereT.PathAlgebra FacetRestrictionData
open GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
local instance sideLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance sideLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance sideOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance sideSimplexFintype (k : ℕ) : Fintype (Simplex X k) := Fintype.ofFinite _

private def bottomLayer (u : Cochain (simplicialCone X) q G) (x : V) := (u,some x)

private theorem facet_walk_eq {I : Type} {p : ℕ} (σ : Simplex X d)
    (f g : I → Cochain (simplicialCone X) q G)
    (eq : ∀ i, restrictCochain X q ⟨σ.val,σ.property.1⟩ ((coneBottomInclusion X).pullback q (f i)) =
      restrictCochain X q ⟨σ.val,σ.property.1⟩ ((coneBottomInclusion X).pullback q (g i)))
    (ys : List (I × V)) (hw : Stretch (spatialVertices X d σ) (ys.map Prod.snd)) :
    let χ := diskChain (affineField (simplicialCone X) q) p
    χ (vertices (fun a : I × V => bottomLayer X q (f a.1) a.2) (gen ys)) =
      χ (vertices (fun a : I × V => bottomLayer X q (g a.1) a.2) (gen ys)) := by
  classical
  intro χ
  rw [vertices_gen,vertices_gen]
  by_cases h : ys.length=p+1
  · let arr : Fin (p+1) → I × V := fun i => ys.get (i.cast h.symm)
    have ha : List.ofFn arr=ys := by
      apply List.ext_getElem
      · simp [h]
      · intro i hi hi'; rw [List.getElem_ofFn]; rfl
    rw [← ha,List.map_ofFn,List.map_ofFn]
    change diskChain _ p _=diskChain _ p _
    rw [diskChain_ofFn,diskChain_ofFn]
    apply congrArg (fun a => Finsupp.single a (1:ℤ))
    apply congrArg (standardGlobalLValue p q)
    ext s
    obtain ⟨b,rfl⟩ := (faceEmbeddingEquivSimplex p q).surjective s
    rw [stringCochain_face,stringCochain_face]
    let F := coneBottomInclusion X
    let a := fun i => arr (b i)
    have red (t : I → Cochain (simplicialCone X) q G) := field_bottom X q (fun i => (t (a i).1,(a i).2))
    exact (red f).trans (Eq.trans (b:=affineField X q (fun i => (F.pullback q (g (a i).1),(a i).2))) (by
      let faces := Finset.univ.image (fun i => (a i).2)
      have sub : faces ⊆ σ.val := by
        intro y hy
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
        have mem : (a i).2 ∈ ys.map Prod.snd := by rw [← ha,List.map_ofFn]; exact List.mem_ofFn.mpr ⟨b i,rfl⟩
        obtain ⟨k,hk⟩ := List.mem_ofFn.mp (hw.mem mem)
        rw [← hk]
        exact σ.val.orderEmbOfFin_mem σ.property.2 k
      change (if he : faces ∈ X ∧ faces.card=q+1 then (F.pullback q (f (a 0).1)) ⟨faces,he⟩ else 0) =
        (if he : faces ∈ X ∧ faces.card=q+1 then (F.pullback q (g (a 0).1)) ⟨faces,he⟩ else 0)
      split <;> rename_i he
      · exact DFunLike.congr_fun (eq (a 0).1) ⟨⟨faces,he⟩,sub⟩
      · rfl) (red g).symm)
  · simp [χ,gen,diskChain,h]

private def sideFacet {p : ℕ} (σ : Simplex X d) (w : Cochain (simplicialCone X) q G) :=
  diskChain (affineField (simplicialCone X) q) p
    (segmentList (bottomLayer X q 0) (bottomLayer X q w) (spatialVertices X d σ))

private theorem sideFacet_eq {p : ℕ} (E : ConeLifts (G:=G) X q) (σ : Simplex X d)
    (u v : Cochain X q G) (eq : restrictCochain X q ⟨σ.val,σ.property.1⟩ u=restrictCochain X q ⟨σ.val,σ.property.1⟩ v) :
    sideFacet X q d (p:=p) σ (E.lift u)=sideFacet X q d σ (E.lift v) := by
  let f (v : Cochain X q G) (i : Bool) : Cochain (simplicialCone X) q G := if i then E.lift v else 0
  let lift (v : Cochain X q G) (a : Bool × V) := bottomLayer X q (f v a.1) a.2
  let op (v : Cochain X q G) := (diskChain (affineField (simplicialCone X) q) p).comp (vertices (lift v))
  have he {w : Chains (Bool × V)} (hw : w ∈ walks Prod.snd (spatialVertices X d σ)) : op u w=op v w := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨ys,hs,rfl⟩ := hw
      exact facet_walk_eq X q d σ (f u) (f v) (fun i => by cases i <;> simp [f,E.bottom,eq]) ys hs
    | zero => simp
    | add _ _ _ _ h k => simp [h,k]
    | smul _ _ _ h => simp [h]
  have e := he (segment_walk (a:=fun x => (false,x)) (b:=fun x => (true,x))
    (fun _ => rfl) (fun _ => rfl) (spatialVertices X d σ))
  simpa [op,sideFacet,lift,f,Function.comp_def,vertices_segment] using e

private theorem distribution_factors {U B M : Type} [Nonempty U] [AddCommGroup M]
    (r : U → B) (f : U → M) (hf : ∀ u v, r u=r v → f u=f v) (z : PathAlgebra.Dist U) (hz : mapDistFn r z=0) :
    Finsupp.linearCombination ℤ f z=0 := by
  classical
  let s (b : B) : U := if h : ∃ u, r u=b then h.choose else Classical.choice inferInstance
  have hs (u : U) : r (s (r u))=r u := by
    simp only [s,dite_eq_left (show ∃ v, r v=r u from ⟨u,rfl⟩)]
    exact Classical.choose_spec (show ∃ v : U, r v=r u from ⟨u,rfl⟩)
  have e : Finsupp.linearCombination ℤ f=(Finsupp.linearCombination ℤ (f ∘ s)).comp (mapDistFn r) := by
    apply Finsupp.lhom_ext'
    intro u
    apply LinearMap.ext_ring
    change Finsupp.linearCombination ℤ f (Finsupp.single u 1)=Finsupp.linearCombination ℤ (f ∘ s) (mapDistFn r (Finsupp.single u 1))
    simp only [mapDistFn_single,Finsupp.linearCombination_single,one_smul,Function.comp_apply]
    exact hf u (s (r u)) (hs u).symm
  exact (LinearMap.congr_fun e z).trans (by change Finsupp.linearCombination ℤ _ (mapDistFn r z)=0; rw [hz,map_zero])

theorem sideFacet_zero (E : ConeLifts (G:=G) X q) (p : ℕ) (σ : Simplex X d)
    (z : Zprim (facetRestrictionData (G:=G) X q)) :
    Finsupp.linearCombination ℤ (fun v => sideFacet X q d (p:=p) σ (E.lift v)) z.val.val=0 := by
  let S : NonemptySimplex X := ⟨σ.val,σ.property.1⟩
  apply distribution_factors (restrictCochain X q S) _ (sideFacet_eq X q d E σ)
  have hz := (Submodule.mem_iInf (fun i => LinearMap.ker (restrictRedDist (facetRestrictionData (G:=G) X q) i))).mp z.property.2 S
  exact congrArg Subtype.val (show restrictRedDist (facetRestrictionData (G:=G) X q) S z.val=0 from hz)

section
variable {U M N I : Type} [AddCommGroup M] [AddCommGroup N]

abbrev assemble (f : U → M) := Finsupp.linearCombination ℤ f

theorem assemble_map (h : M →ₗ[ℤ] N) (f : U → M) (z : PathAlgebra.Dist U) :
    h (assemble f z)=assemble (fun v => h (f v)) z := by
  have eq : h.comp (assemble f)=assemble (fun v => h (f v)) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    simp [assemble]
  exact LinearMap.congr_fun eq z

theorem assemble_sub (f g : U → M) (z : PathAlgebra.Dist U) :
    assemble (fun v => f v-g v) z=assemble f z-assemble g z := by
  have eq : assemble (fun v => f v-g v)=assemble f-assemble g := by ext; simp [assemble]
  exact LinearMap.congr_fun eq z

theorem assemble_constant (b : M) (z : RedDist U) : assemble (fun _ : U => b) z.val=0 := by
  have eq : assemble (fun _ : U => b)=(LinearMap.toSpanSingleton ℤ M b).comp (augmentation U) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    simp [assemble]
  exact (LinearMap.congr_fun eq z.val).trans (by change LinearMap.toSpanSingleton ℤ M b (augmentation U z.val)=0; rw [show augmentation U z.val=0 from z.property,map_zero])

theorem assemble_sum [Fintype I] (c : I → ℤ) (f : I → U → M) (z : PathAlgebra.Dist U) :
    assemble (fun v => ∑ i, c i • f i v) z=∑ i, c i • assemble (f i) z := by
  have eq : assemble (fun v => ∑ i, c i • f i v)=∑ i, c i • assemble (f i) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    simp [assemble]
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply] using LinearMap.congr_fun eq z

end

private theorem segment_map {T W Y : Type*} (a b : W → Y) (f : T → W) (xs : List T) :
    segmentList a b (xs.map f)=segmentList (a ∘ f) (b ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [segmentList,ih,List.map_map]

private theorem side_zero (E : ConeLifts (G:=G) X q) (coeff : Simplex X d → ℤ)
    (z : Zprim (facetRestrictionData (G:=G) X q)) :
    assemble (fun v => diskChain (affineField (simplicialCone X) q) (d+1)
      (segment (layerOf _ q 0) (layerOf _ q (E.lift v)) (vertices some (orientedFacets X d coeff)))) z.val.val=0 := by
  have expand (v : Cochain X q G) : diskChain (affineField (simplicialCone X) q) (d+1)
      (segment (layerOf _ q 0) (layerOf _ q (E.lift v)) (vertices some (orientedFacets X d coeff))) =
      ∑ σ : Simplex X d, coeff σ • sideFacet X q d σ (E.lift v) := by
    classical
    unfold orientedFacets
    simp only [map_sum,map_smul,vertices_gen,segment,extend_gen,segment_map]
    rfl
  simp_rw [expand]
  rw [assemble_sum]
  simp only [sideFacet_zero,smul_zero,Finset.sum_const_zero]

/-- After summing over a primitive cycle only the top end of the lifted
prism survives. The bottom end cancels by augmentation and the side faces
cancel separately on each spatial facet. -/
theorem assembled_boundary (E : ConeLifts (G:=G) X q) (coeff : Simplex X d → ℤ)
    (hz : boundary (orientedFacets X d coeff)=0) (z : Zprim (facetRestrictionData (G:=G) X q)) :
    diskBoundary (assemble (fun v => liftedSegment X q d coeff 0 (E.lift v)) z.val.val) =
      assemble (fun v => diskChain (affineField (simplicialCone X) q) (d+1)
        (vertices (layerOf _ q (E.lift v)) (orientedCone X d coeff))) z.val.val := by
  rw [assemble_map]
  simp_rw [liftedSegment_boundary X q d coeff hz]
  rw [assemble_sub,assemble_sub,assemble_constant,side_zero,sub_zero,sub_zero]

end GeneralSphereT.Transport.Prism

