import Formalization.Transport.PrismClosedCommutator
import Formalization.Section4PointedConePairCohomologyShift

noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra GeneralSphereT.DoldKanExplicitBridge
open GeneralSphereT.SimplicialCochain.OrderedSimplicialMap OpenDisk.PhaseDuality

variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
local instance : LE (Option V) := @WithBot.instLE V inferInstance
local instance : LT (Option V) := @WithBot.instLT V inferInstance
local instance : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (q d : ℕ)

theorem field_bottom (u : Fin (q+1) → Cochain (simplicialCone X) q G × V) :
    affineField (simplicialCone X) q (fun i => ((u i).1,some (u i).2)) =
      affineField X q (fun i => ((coneBottomInclusion X).pullback q (u i).1,(u i).2)) := by
  classical
  let s := Finset.univ.image (fun i => (u i).2)
  let top := Finset.univ.image (fun i => some (u i).2)
  have eq : top = s.image some := by simp only [top,s,Finset.image_image,Function.comp_def]
  have card : top.card = s.card := eq ▸ Finset.card_image_of_injective s (Option.some_injective V)
  have mem : top ∈ simplicialCone X ↔ s ∈ X := by
    rw [eq]
    convert! image_some_mem_simplicialCone_iff X s using 2
    ext o
    simp
  unfold affineField
  dsimp only
  split <;> rename_i h
  · have hs : s ∈ X ∧ s.card=q+1 := ⟨mem.mp h.1,card.symm.trans h.2⟩
    rw [dif_pos hs,pullback_apply]
    apply congrArg ((u 0).1)
    apply Subtype.ext
    change top = _
    rw [eq]
    change s.image some = s.map coneBottomOrderEmbedding.toEmbedding
    ext o
    simp only [Finset.mem_image,Finset.mem_map]
    rfl
  · have hs : ¬(s ∈ X ∧ s.card=q+1) := fun h' => h ⟨mem.mpr h'.1,card.trans h'.2⟩
    rw [dif_neg hs]

private theorem pull_bottom {p : ℕ} (ω : EM G (q+1) p → Phase)
    (w : Chains (Cochain (simplicialCone X) q G × V)) :
    pullCochain (affineField (simplicialCone X) q) ω (vertices (fun y => (y.1,some y.2)) w) =
      pullCochain (affineField X q) ω (vertices (fun y => ((coneBottomInclusion X).pullback q y.1,y.2)) w) := by
  let up := fun y : Cochain (simplicialCone X) q G × V => (y.1,some y.2)
  let down := fun y : Cochain (simplicialCone X) q G × V => ((coneBottomInclusion X).pullback q y.1,y.2)
  have eq : (pullCochain (affineField (simplicialCone X) q) ω).comp (vertices up) =
      (pullCochain (affineField X q) ω).comp (vertices down) := by
    apply Finsupp.lhom_ext'
    intro ys
    apply LinearMap.ext_ring
    change pullCochain _ ω (vertices up (gen ys)) = pullCochain _ ω (vertices down (gen ys))
    rw [vertices_gen,vertices_gen]
    simp only [pullCochain,gen,evaluate_single,one_zsmul]
    by_cases h : ys.length=p+1
    · simp only [homogeneous,List.length_map,h,dite_true]
      apply congrArg ω
      unfold classifyingValue
      congr 2
      ext s
      obtain ⟨e,rfl⟩ := (faceEmbeddingEquivSimplex p q).surjective s
      rw [stringCochain_face,stringCochain_face]
      simp only [List.get_eq_getElem,List.getElem_map]
      exact field_bottom X q (fun i => ys.get ((e i).cast h.symm))
    · simp [homogeneous,h]
  exact LinearMap.congr_fun eq w

private theorem triangle_map_spatial {W Y : Type*} (i : V → W) (a b c : W → Y) (w : Chains V) :
    triangle a b c (vertices i w) = triangle (a ∘ i) (b ∘ i) (c ∘ i) w := by
  have seg (b c : W → Y) (xs : List V) : segmentList b c (xs.map i) = segmentList (b ∘ i) (c ∘ i) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [segmentList,ih,List.map_map]
  have tri (xs : List V) : triangleList a b c (xs.map i) = triangleList (a ∘ i) (b ∘ i) (c ∘ i) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change cons (a (i x)) (segmentList b c ((x::xs).map i)) + _ = _
      rw [seg]
      simp [triangleList,ih]
  have lin : (triangle a b c).comp (vertices i) = triangle (a ∘ i) (b ∘ i) (c ∘ i) := by
    apply Finsupp.lhom_ext'
    intro xs
    apply LinearMap.ext_ring
    change triangle a b c (vertices i (gen xs)) = triangle _ _ _ (gen xs)
    simpa only [vertices_gen,triangle,extend_gen] using tri xs
  exact LinearMap.congr_fun lin w

theorem read_bottom_triangle {p : ℕ} (ω : EM G (q+1) p → Phase)
    (u v w : Cochain (simplicialCone X) q G) (z : Chains V) :
    let χ := pullCochain (affineField (simplicialCone X) q) ω
    let f := layerOf (simplicialCone X) q (G:=G)
    let r := (coneBottomInclusion X).pullback (G:=G) q
    χ (triangle (f u) (f v) (f w) (vertices some z)) =
      pullCochain (affineField X q) ω (triangle (layerOf X q (r u)) (layerOf X q (r v)) (layerOf X q (r w)) z) := by
  dsimp only
  rw [triangle_map_spatial]
  let lay := fun (u : Cochain (simplicialCone X) q G) (x : V) => (u,x)
  have E (xs : List V) := pull_bottom X q ω (triangleList (lay u) (lay v) (lay w) xs)
  simp only [vertices_triangle] at E
  have lin : (pullCochain (affineField (simplicialCone X) q) ω).comp
      (triangle ((layerOf _ q u) ∘ some) ((layerOf _ q v) ∘ some) ((layerOf _ q w) ∘ some)) =
      (pullCochain (affineField X q) ω).comp (triangle (layerOf X q ((coneBottomInclusion X).pullback q u))
        (layerOf X q ((coneBottomInclusion X).pullback q v)) (layerOf X q ((coneBottomInclusion X).pullback q w))) := by
    apply Finsupp.lhom_ext'
    intro xs
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply]
    change pullCochain _ ω (triangle _ _ _ (gen xs)) = pullCochain _ ω (triangle _ _ _ (gen xs))
    simp only [triangle,extend_gen]
    exact E xs
  exact LinearMap.congr_fun lin z

theorem cone_spatial (coeff : Simplex X d → ℤ) :
    cons none (vertices some (orientedFacets X d coeff)) ∈ spatialChains (simplicialCone X) := by
  classical
  unfold orientedFacets
  simp only [map_sum,map_smul]
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  rw [vertices_gen,cons_gen]
  let S := insert (none : Option V) (σ.val.image some)
  have hS : S ∈ simplicialCone X := by
    rw [mem_simplicialCone]
    have e : coneBaseVertices S = σ.val := by ext x; simp [S,mem_coneBaseVertices]
    exact ⟨Finset.insert_nonempty _ _,Or.inr (e ▸ σ.property.1)⟩
  apply Submodule.subset_span
  refine ⟨_,⟨S,hS⟩,?_,?_,rfl⟩
  · apply List.pairwise_cons.mpr
    refine ⟨fun x _ => WithBot.LE.bot_le _,?_⟩
    rw [List.map_ofFn]
    exact List.pairwise_ofFn.mpr fun i j h => (coneBottomOrderEmbedding (V:=V)).monotone ((σ.val.orderEmbOfFin σ.property.2).monotone h.le)
  · intro y hy
    rcases List.mem_cons.mp hy with rfl|h
    · exact Finset.mem_insert_self _ _
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (σ.val.orderEmbOfFin_mem σ.property.2 i))

/-- A closed move extends across the spatial cone whenever its reduced degree is exact. -/
theorem closed_extension (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (z : Cochain X q G) (hz : coboundary X q z=0) :
    ∃ Z : Cochain (simplicialCone X) q G, coboundary _ q Z=0 ∧ (coneBottomInclusion X).pullback q Z=z := by
  let F := coneBottomInclusion X
  cases q with
  | zero =>
    let c := constantCochain X (z (basepointSimplex X b))
    let zb : BasedZeroCochain (G:=G) X b := ⟨z-c,by change (z-c) (basepointSimplex X b)=0; simp [c]⟩
    have h : zb ∈ LinearMap.ker (basedZeroCoboundary (G:=G) X b) := by
      change coboundary X 0 (z-c)=0
      simp [c,hz]
    change LinearMap.ker _ = ⊥ at hred
    rw [hred] at h
    have e : z-c=0 := congrArg Subtype.val (show zb=0 by simpa using h)
    refine ⟨constantCochain _ (z (basepointSimplex X b)),by simp,?_⟩
    exact (show F.pullback 0 (constantCochain _ (z (basepointSimplex X b)))=c by ext; rfl).trans (sub_eq_zero.mp e).symm
  | succ n =>
    have h : z ∈ LinearMap.ker (coboundary X (n+1)) := hz
    change LinearMap.range _ = LinearMap.ker _ at hred
    rw [← hred] at h
    obtain ⟨u,rfl⟩ := h
    refine ⟨coboundary _ n (F.extendCochainByZero n u),coboundary_coboundary _ _ _,?_⟩
    have e := LinearMap.congr_fun (F.pullback_coboundary (G:=G) n) (F.extendCochainByZero n u)
    simpa only [LinearMap.comp_apply,pullback_extendCochainByZero] using e

theorem physicalPrism_zz (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (ω : EM G (q+1) (d+2) → Phase) (hc : ClosedOnEM ω) (coeff : Simplex X d → ℤ)
    (hcycle : boundary (orientedFacets X d coeff)=0) (s t : Cochain X q G)
    (a : LinearMap.range (coboundary (G:=G) X q)) (hs : coboundary X q s=0) (ht : coboundary X q t=0) :
    physicalPrism X q d ω coeff t s a = physicalPrism X q d ω coeff s t a := by
  obtain ⟨v,rfl⟩ := facetCoboundary_surjective X q a
  obtain ⟨S,hS,rS⟩ := closed_extension X q b hred s hs
  obtain ⟨T,hT,rT⟩ := closed_extension X q b hred t ht
  let F := coneBottomInclusion X
  let U := F.extendCochainByZero q v
  have e := closed_commutator_on_boundary (simplicialCone X) q ω hc U S T hS hT (cone_spatial X d coeff)
  dsimp only at e
  rw [boundary_cons,boundary_vertices,hcycle,map_zero,map_zero,sub_zero,
      read_bottom_triangle,read_bottom_triangle] at e
  simp only [map_add,rS,rT,U,F,pullback_extendCochainByZero] at e
  rw [physicalPrism_on_primitive,physicalPrism_on_primitive]
  exact congrArg Neg.neg e

end GeneralSphereT.Transport.Prism

