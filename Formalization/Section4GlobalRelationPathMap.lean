import Formalization.Section4GlobalCochainRestrictionMap
import Formalization.Section4SimplicialPathObject
import Formalization.SimplicialFacetData

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: global relation paths as genuine simplicial maps

A global normalized path of cochains can be evaluated on every simplicial
simplex.  When the global path is killed by coboundary, the evaluated path
lies in the degreewise kernel defining the tensor-free relation-path object.
The result is a genuine simplicial map, including all degeneracies.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-! ## Additive evaluation -/

/-- Evaluation of the global `L`-valued construction at one simplex is
additive in the cochain. -/
def cochainLValueHom
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    Cochain M q G →+
      (L (AddCommGrpCat.of G) (q + 1)).obj Δ where
  toFun := cochainLValue M q Δ x
  map_zero' := by
    change (cochainToLMap M q 0).app Δ x = 0
    rw [cochainToLMap_zero]
    rfl
  map_add' c c' := by
    change (cochainToLMap M q (c + c')).app Δ x =
      (cochainToLMap M q c).app Δ x +
        (cochainToLMap M q c').app Δ x
    rw [cochainToLMap_add]
    rfl

@[simp]
theorem cochainLValueHom_apply
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ)
    (c : Cochain M q G) :
    cochainLValueHom M q Δ x c = cochainLValue M q Δ x c :=
  rfl

/-- Additive evaluation commutes with every simplicial operator. -/
theorem cochainLValueHom_naturality
    (M : AbstractSimplicialComplex V) (q : ℕ)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (x : (orderedComplexSSet M).obj Δ) :
    cochainLValueHom M q Δ' ((orderedComplexSSet M).map θ x) =
      ((L (AddCommGrpCat.of G) (q + 1)).map θ).hom.comp
        (cochainLValueHom M q Δ x) := by
  apply AddMonoidHom.ext
  intro c
  exact cochainLValue_naturality M q θ x c

/-! ## Evaluating coboundaries in `K` -/

/-- A global coboundary, regarded as an actual cocycle. -/
def coboundaryRangeToCocycle
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    CoboundaryGroup (G := G) M q →+
      LinearMap.ker (coboundary (G := G) M (q + 1)) where
  toFun z := ⟨z.1, by
    rcases z.2 with ⟨c, hc⟩
    rw [← hc]
    exact coboundary_coboundary M q c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coboundaryRangeToCocycle_coe
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (z : CoboundaryGroup (G := G) M q) :
    (coboundaryRangeToCocycle M q z).1 = z.1 :=
  rfl

/-- The sphere-valued chain map associated with the zero cocycle is zero. -/
theorem cocycleSphereChainMap_zero'
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (hzero : coboundary (G := G) M q 0 = 0) :
    cocycleSphereChainMap M q 0 hzero = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q
  · subst i
    rw [cocycleSphereChainMap_f_self]
    simp
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) q (AddCommGrpCat.of G) i hi).eq_of_tgt _ _

/-- The sphere-valued chain-map construction is additive on cocycles. -/
theorem cocycleSphereChainMap_add'
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c c' : Cochain M q G)
    (hc : coboundary M q c = 0)
    (hc' : coboundary M q c' = 0)
    (hadd : coboundary M q (c + c') = 0) :
    cocycleSphereChainMap M q (c + c') hadd =
      cocycleSphereChainMap M q c hc +
        cocycleSphereChainMap M q c' hc' := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q
  · subst i
    change (cocycleSphereChainMap M q (c + c') hadd).f q =
      (cocycleSphereChainMap M q c hc).f q +
        (cocycleSphereChainMap M q c' hc').f q
    rw [cocycleSphereChainMap_f_self,
      cocycleSphereChainMap_f_self,
      cocycleSphereChainMap_f_self]
    simp only [map_add, Preadditive.add_comp]
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) q (AddCommGrpCat.of G) i hi).eq_of_tgt _ _

/-- Additivity after passing the cocycle chain map through Dold--Kan. -/
theorem cocycleToKMap_add'
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c c' : Cochain M q G)
    (hc : coboundary M q c = 0)
    (hc' : coboundary M q c' = 0)
    (hadd : coboundary M q (c + c') = 0) :
    cocycleToKMap M q (c + c') hadd =
      cocycleToKMap M q c hc + cocycleToKMap M q c' hc' := by
  unfold cocycleToKMap
  rw [cocycleSphereChainMap_add' M q c c' hc hc' hadd]
  exact simplicialMapOfNormalizedChainMap_add
    (orderedComplexSSet M)
    (cocycleSphereChainMap M q c hc)
    (cocycleSphereChainMap M q c' hc')

/-- The zero cocycle gives the zero genuine `K`-valued map. -/
theorem cocycleToKMap_zero'
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (hzero : coboundary (G := G) M q 0 = 0) :
    cocycleToKMap M q 0 hzero = 0 := by
  unfold cocycleToKMap
  rw [cocycleSphereChainMap_zero' M q hzero]
  exact simplicialMapOfNormalizedChainMap_zero (orderedComplexSSet M)

/-- The cocycle-to-sphere-chain-map construction as an additive map. -/
def cocycleSphereChainMapSubtypeAddHom'
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    LinearMap.ker (coboundary (G := G) M q) →+
      ((orderedComplexSSet M).normalizedChainComplex
          integralCoefficients ⟶
        sphereComplex (AddCommGrpCat.of G) q) where
  toFun z := cocycleSphereChainMap M q z.1
    (LinearMap.mem_ker.mp z.2)
  map_zero' := cocycleSphereChainMap_zero' M q _
  map_add' z z' := cocycleSphereChainMap_add' M q z.1 z'.1
    (LinearMap.mem_ker.mp z.2) (LinearMap.mem_ker.mp z'.2) _

/-- Evaluate a denormalized chain map on one simplex of its source. -/
def normalizedChainMapValueHom
    (X : SSet.{u}) (C : ChainComplex AddCommGrpCat.{u} ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : X.obj Δ) :
    (X.normalizedChainComplex integralCoefficients ⟶ C) →+
      (CategoryTheory.Abelian.DoldKan.Γ.obj C).obj Δ where
  toFun f := (simplicialMapOfNormalizedChainMap X f).app Δ x
  map_zero' := by
    rw [simplicialMapOfNormalizedChainMap_zero]
    rfl
  map_add' f g := by
    rw [simplicialMapOfNormalizedChainMap_add]
    rfl

/-- Evaluation of genuine `K`-valued cocycle maps is additive. -/
def cocycleKValueHom
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    LinearMap.ker (coboundary (G := G) M q) →+
      (K (AddCommGrpCat.of G) q).obj Δ :=
  (normalizedChainMapValueHom (orderedComplexSSet M)
      (sphereComplex (AddCommGrpCat.of G) q) Δ x).comp
    (cocycleSphereChainMapSubtypeAddHom' M q)

@[simp]
theorem cocycleKValueHom_apply
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ)
    (z : LinearMap.ker (coboundary (G := G) M q)) :
    cocycleKValueHom M q Δ x z =
      (cocycleToKMap M q z.1
        (LinearMap.mem_ker.mp z.2)).app Δ x :=
  rfl

set_option maxHeartbeats 2000000 in
-- Unfolding the nested Dold--Kan target during structure elaboration is costly.
/-- Coboundary with codomain restricted to the subgroup of cocycles. -/
def coboundaryToCocycle
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Cochain M q G →+
      LinearMap.ker (coboundary (G := G) M (q + 1)) where
  toFun c := ⟨coboundary M q c, coboundary_coboundary M q c⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (coboundary M q)
  map_add' c c' := by
    apply Subtype.ext
    exact map_add (coboundary M q) c c'

@[simp]
theorem coboundaryToCocycle_coe
    (M : AbstractSimplicialComplex V) (q : ℕ) (c : Cochain M q G) :
    (coboundaryToCocycle M q c).1 = coboundary M q c :=
  rfl

/-- The two restricted-codomain versions of coboundary agree after the
range is included in the cocycles. -/
theorem coboundaryToCocycle_eq_range_comp
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    coboundaryToCocycle (G := G) M q =
      (coboundaryRangeToCocycle M q).comp
        (coboundaryToRange (G := G) M q) := by
  apply AddMonoidHom.ext
  intro c
  rfl

set_option maxHeartbeats 800000 in
-- Applying the Dold--Kan natural-transformation equality is elaboration-heavy.
/-- Pointwise form of the global coboundary square after evaluation on a
simplex. -/
theorem cochainLValue_d_cocycle_apply
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ)
    (c : Cochain M q G) :
    ((d (AddCommGrpCat.of G) (q + 1)).app Δ).hom
        (cochainLValueHom M q Δ x c) =
      cocycleKValueHom M (q + 1) Δ x
        (coboundaryToCocycle M q c) := by
  simp only [cochainLValueHom_apply,
    cocycleKValueHom_apply]
  exact cochainToLMap_comp_d_apply M q c Δ x

/-- A path killed by coboundary into its range is also killed by
coboundary regarded as a cocycle. -/
theorem mapD_coboundaryToCocycle_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q))) :
    mapDNormalizedPath (coboundaryToCocycle M q) R.1 = 0 := by
  have h := mapDNormalizedPath_mapNormalizedPath
    (coboundaryToRange (G := G) M q)
    (coboundaryToCocycle M q)
    (AddMonoidHom.id (Cochain M q G))
    (AddMonoidHom.id (Cochain M q G))
    (coboundaryRangeToCocycle M q)
    (by
      rw [AddMonoidHom.comp_id]
      exact coboundaryToCocycle_eq_range_comp M q)
    R.1
  rw [mapNormalizedPath_id_apply] at h
  rw [R.2] at h
  simpa only [map_zero] using h

/-! ## The genuine global relation-path map -/

/-- Evaluating a global relation path on one simplex produces a relation
path for the standard Dold--Kan map. -/
def globalRelationPathValue
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    LinearMap.ker
      (mapDNormalizedPath
        ((d (AddCommGrpCat.of G) (q + 1)).app Δ).hom) := by
  refine ⟨mapNormalizedPath
    (cochainLValueHom M q Δ x)
    (cochainLValueHom M q Δ x) R.1, ?_⟩
  rw [LinearMap.mem_ker]
  calc
    mapDNormalizedPath
        ((d (AddCommGrpCat.of G) (q + 1)).app Δ).hom
        (mapNormalizedPath
          (cochainLValueHom M q Δ x)
          (cochainLValueHom M q Δ x) R.1) =
      mapNormalizedPath
        (cochainLValueHom M q Δ x)
        (cocycleKValueHom M (q + 1) Δ x)
        (mapDNormalizedPath (coboundaryToCocycle M q) R.1) :=
      mapDNormalizedPath_mapNormalizedPath_of_apply
        (coboundaryToCocycle M q)
        ((d (AddCommGrpCat.of G) (q + 1)).app Δ).hom
        (cochainLValueHom M q Δ x)
        (cochainLValueHom M q Δ x)
        (cocycleKValueHom M (q + 1) Δ x)
        (cochainLValue_d_cocycle_apply M q Δ x) R.1
    _ = 0 := by
      rw [mapD_coboundaryToCocycle_eq_zero M q R, map_zero]

/-- A global normalized relation path restricts to a genuine simplicial map
into the tensor-free relation-path object. -/
def globalRelationPathRestrictionMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q))) :
    orderedComplexSSet M ⟶
      underlyingSSet
        (simplicialRelationPath (d (AddCommGrpCat.of G) (q + 1))) where
  app Δ := ↾fun x ↦ globalRelationPathValue M q R Δ x
  naturality Δ Δ' θ := by
    ext x
    apply Subtype.ext
    change mapNormalizedPath
        (cochainLValueHom M q Δ'
          ((orderedComplexSSet M).map θ x))
        (cochainLValueHom M q Δ'
          ((orderedComplexSSet M).map θ x)) R.1 =
      mapNormalizedPath
        ((L (AddCommGrpCat.of G) (q + 1)).map θ).hom
        ((L (AddCommGrpCat.of G) (q + 1)).map θ).hom
        (mapNormalizedPath
          (cochainLValueHom M q Δ x)
          (cochainLValueHom M q Δ x) R.1)
    rw [mapNormalizedPath_comp_apply]
    rw [cochainLValueHom_naturality M q θ x]

@[simp]
theorem globalRelationPathRestrictionMap_app_apply
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    (globalRelationPathRestrictionMap M q R).app Δ x =
      globalRelationPathValue M q R Δ x :=
  rfl

end GeneralSphereT.SimplicialCochain
