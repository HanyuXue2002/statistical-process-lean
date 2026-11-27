import Formalization.Section4NormalizedCochainBridge
import Formalization.Section4DoldKanModels
import Formalization.Section4DoldKanProjection
import Formalization.SimplicialCoboundarySquare

set_option linter.style.header false

/-!
# Section 4: cochains as maps to the Dold--Kan sphere and disk complexes

The normalized-chain bridge turns a cocycle into a chain map to the
one-term sphere complex.  More generally, a cochain gives the bottom
component of a chain map to the two-term disk complex; its coboundary is the
top component.  These are the chain-level maps which Dold--Kan denormalizes
to the paper's `K(G,q)`- and `L(G,q+1)`-valued simplicial maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace GeneralSphereT.SimplicialCochain

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- A degree-`q` cocycle defines a chain map from normalized simplicial
chains to the complex with `G` concentrated in degree `q`. -/
def cocycleSphereChainMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c : Cochain M q G) (hc : coboundary M q c = 0) :
    (orderedComplexSSet M).normalizedChainComplex integralCoefficients ⟶
      StandardModels.sphereComplex (AddCommGrpCat.of G) q :=
  HomologicalComplex.mkHomToSingle
    (cochainEquivNormalizedCochainHom M q c)
    (fun i hi => by
      have hi' : i = q + 1 := by
        simp only [ComplexShape.down_Rel] at hi
        omega
      subst i
      rw [← cochainEquivNormalizedCochainHom_coboundary M q c, hc]
      simp)

@[simp]
theorem cocycleSphereChainMap_f_self
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c : Cochain M q G) (hc : coboundary M q c = 0) :
    (cocycleSphereChainMap M q c hc).f q =
      cochainEquivNormalizedCochainHom M q c ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) q (AddCommGrpCat.of G)).inv := by
  apply HomologicalComplex.mkHomToSingle_f

/-- A degree-`q` cochain defines a chain map to the disk complex in degrees
`q+1,q`: the bottom component is the cochain and the top component is its
coboundary. -/
def cochainDiskChainMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c : Cochain M q G) :
    (orderedComplexSSet M).normalizedChainComplex integralCoefficients ⟶
      HomologicalComplex.double (𝟙 (AddCommGrpCat.of G))
        (ComplexShape.down_mk (q + 1) q rfl) := by
  let N := (orderedComplexSSet M).normalizedChainComplex integralCoefficients
  let φ : N.X q ⟶ AddCommGrpCat.of G :=
    cochainEquivNormalizedCochainHom M q c
  let ψ : N.X (q + 1) ⟶ AddCommGrpCat.of G :=
    cochainEquivNormalizedCochainHom M (q + 1) (coboundary M q c)
  have hψ : ψ = N.d (q + 1) q ≫ φ :=
    cochainEquivNormalizedCochainHom_coboundary M q c
  let hne : q + 1 ≠ q := by omega
  refine
    { f := fun i =>
        if hi : i = q + 1 then
          (N.XIsoOfEq hi).hom ≫ ψ ≫
            (HomologicalComplex.doubleXIso₀ (𝟙 (AddCommGrpCat.of G))
              (ComplexShape.down_mk (q + 1) q rfl)).inv ≫
                eqToHom (by rw [hi])
        else if hi' : i = q then
          (N.XIsoOfEq hi').hom ≫ φ ≫
            (HomologicalComplex.doubleXIso₁ (𝟙 (AddCommGrpCat.of G))
              (ComplexShape.down_mk (q + 1) q rfl) hne).inv ≫
                eqToHom (by rw [hi'])
        else 0
      comm' i j hij := by
        have hrel : j + 1 = i := by
          simpa only [ComplexShape.down_Rel] using hij
        by_cases hi : i = q + 1
        · subst i
          have hj : j = q := by omega
          subst j
          simp [HomologicalComplex.double_d, hψ]
          <;> rfl
        · rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hi, comp_zero]
          by_cases hj : j = q + 1
          · subst j
            simp [hψ]
            rw [Category.id_comp]
            change 0 = N.d i (q + 1) ≫ N.d (q + 1) q ≫ φ ≫ _
            rw [← Category.assoc]
            rw [N.d_comp_d]
            simp
          · have hj' : j ≠ q := by
              intro hjq
              subst j
              have : i = q + 1 := by omega
              exact hi this
            simp [hj, hj'] }

@[simp]
theorem cochainDiskChainMap_f_bottom
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c : Cochain M q G) :
    (cochainDiskChainMap M q c).f q =
      cochainEquivNormalizedCochainHom M q c ≫
        (HomologicalComplex.doubleXIso₁ (𝟙 (AddCommGrpCat.of G))
          (ComplexShape.down_mk (q + 1) q rfl) (by omega)).inv := by
  simp [cochainDiskChainMap]

@[simp]
theorem cochainDiskChainMap_f_top
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c : Cochain M q G) :
    (cochainDiskChainMap M q c).f (q + 1) =
      cochainEquivNormalizedCochainHom M (q + 1) (coboundary M q c) ≫
        (HomologicalComplex.doubleXIso₀ (𝟙 (AddCommGrpCat.of G))
          (ComplexShape.down_mk (q + 1) q rfl)).inv := by
  simp [cochainDiskChainMap]

@[simp]
theorem cochainDiskChainMap_zero
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    cochainDiskChainMap (G := G) M q 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q + 1
  · subst i
    simp [cochainDiskChainMap]
  · by_cases hi' : i = q
    · subst i
      simp [cochainDiskChainMap]
    · simp [cochainDiskChainMap, hi, hi']

@[simp]
theorem cochainDiskChainMap_add
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c c' : Cochain M q G) :
    cochainDiskChainMap M q (c + c') =
      cochainDiskChainMap M q c + cochainDiskChainMap M q c' := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q + 1
  · subst i
    simp [cochainDiskChainMap, map_add, Preadditive.comp_add,
      Preadditive.add_comp]
  · by_cases hi' : i = q
    · subst i
      simp [cochainDiskChainMap, map_add, Preadditive.comp_add,
        Preadditive.add_comp]
    · simp [cochainDiskChainMap, hi, hi']

/-- Projecting the disk-valued chain map to the top sphere-valued map gives
the cocycle represented by the coboundary. -/
theorem cochainDiskChainMap_comp_diskToSphere
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c : Cochain M q G) :
    cochainDiskChainMap M q c ≫
        StandardModels.diskToSphereSucc (AddCommGrpCat.of G) q =
      cocycleSphereChainMap M (q + 1) (coboundary M q c)
        (coboundary_coboundary M q c) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q + 1
  · subst i
    rw [HomologicalComplex.comp_f, cochainDiskChainMap_f_top,
      cocycleSphereChainMap_f_self]
    rw [← cancel_mono (HomologicalComplex.singleObjXSelf
      (ComplexShape.down ℕ) (q + 1) (AddCommGrpCat.of G)).hom]
    simp only [Category.assoc]
    unfold StandardModels.diskToSphereSucc
    rw [HomologicalComplex.mkHomToSingle_f]
    simp
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) (q + 1) (AddCommGrpCat.of G) i hi).eq_of_tgt _ _

end GeneralSphereT.SimplicialCochain
