import Formalization.Section4LocalLEvaluationEquiv
import Formalization.Section4ReducedDistributionGluing

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Local reduced distributions carried by a native simplicial map

A genuine map `M ⟶ reducedFree L` gives, on every nondegenerate simplex,
a reduced distribution of local cochains.  Simplicial naturality says that
these distributions have compatible Boolean-cube coefficients.
-/

noncomputable section

open CategoryTheory Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V) (q : ℕ)

local instance nativeMapLocalSimplexColexOrder : LinearOrder (Simplex M q) :=
  LinearOrder.lift'
    (fun η : Simplex M q => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

/-- Transport local cochains from a simplex to the (propositionally equal)
support of its canonical nondegenerate representative.  Writing this as a
coordinate restriction, rather than an `Eq.rec`, keeps all later formulas
computationally transparent. -/
def facetToCanonicalEquiv (σ : NonemptySimplex M) :
    Configuration (facesIn M q σ) G ≃+
      Configuration
        (facesIn M q
          (nonDegenerateSimplexFacet M
            (nonemptySimplexNonDegenerate M σ))) G where
  toFun := (coordinateRestriction
      (facesIn M q
        (nonDegenerateSimplexFacet M
          (nonemptySimplexNonDegenerate M σ)))).comp
    (coordinateExtension (facesIn M q σ))
  invFun := (coordinateRestriction (facesIn M q σ)).comp
    (coordinateExtension
      (facesIn M q
        (nonDegenerateSimplexFacet M
          (nonemptySimplexNonDegenerate M σ))))
  left_inv a := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    ext i
    have hi : i.1 ∈ facesIn M q
        (nonDegenerateSimplexFacet M
          (nonemptySimplexNonDegenerate M σ)) := by
      rw [nonemptySimplexNonDegenerate_facet M σ]
      exact i.2
    rw [coordinateRestriction_apply,
      coordinateExtension_apply_mem _ _ hi,
      coordinateRestriction_apply,
      coordinateExtension_apply_mem _ _ i.2]
  right_inv a := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    ext i
    have hi : i.1 ∈ facesIn M q σ := by
      have hsets : facesIn M q
          (nonDegenerateSimplexFacet M
            (nonemptySimplexNonDegenerate M σ)) = facesIn M q σ :=
        congrArg (facesIn M q)
          (nonemptySimplexNonDegenerate_facet M σ)
      exact (Set.ext_iff.mp hsets i.1).mp i.2
    rw [coordinateRestriction_apply,
      coordinateExtension_apply_mem _ _ hi,
      coordinateRestriction_apply,
      coordinateExtension_apply_mem _ _ i.2]
  map_add' a b := by
    exact map_add _ _ _

/-- Local cochains on a facet are exactly its simplices in `L(G,q+1)`. -/
def facetCochainLValueEquiv (σ : NonemptySimplex M) :
    Configuration (facesIn M q σ) G ≃+
      (L (AddCommGrpCat.of G) (q + 1)).obj
        (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ))) :=
  (facetToCanonicalEquiv (G := G) M q σ).trans
    (localCochainLValueEquiv M q _
      (nonemptySimplexNonDegenerate M σ))

/-- Evaluation of a local cochain on the top simplex carried by `σ`. -/
def facetCochainLValueHom (σ : NonemptySimplex M) :
    Configuration (facesIn M q σ) G →+
      (L (AddCommGrpCat.of G) (q + 1)).obj
        (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ))) :=
  (facetCochainLValueEquiv (G := G) M q σ).toAddMonoidHom

@[simp]
theorem facetCochainLValueEquiv_apply (σ : NonemptySimplex M)
    (a : Configuration (facesIn M q σ) G) :
    facetCochainLValueEquiv M q σ a =
      facetCochainLValueHom M q σ a :=
  rfl

/-- The abstract local equivalence is the concrete extension-by-zero
evaluation used in the global construction. -/
theorem facetCochainLValueHom_apply (σ : NonemptySimplex M)
    (a : Configuration (facesIn M q σ) G) :
    facetCochainLValueHom M q σ a =
      cochainLValueHom M q _ (nonemptySimplexNonDegenerate M σ).1
        (coordinateExtension (facesIn M q σ) a) := by
  simp only [facetCochainLValueHom, facetCochainLValueEquiv,
    AddEquiv.trans_apply, facetToCanonicalEquiv,
    AddEquiv.coe_toAddMonoidHom, AddMonoidHom.coe_comp,
    Function.comp_apply, localCochainLValueEquiv_apply]
  exact localCochainLValueHom_restrict M q _
    (nonemptySimplexNonDegenerate M σ)
      (coordinateExtension (facesIn M q σ) a)

/-- Include the ordered vertices of a face `ρ` into those of `σ`. -/
def facetInclusionHom (ρ σ : NonemptySimplex M) (hρσ : ρ.1 ⊆ σ.1) :
    SimplexCategory.mk (nonemptySimplexDimension ρ) ⟶
      SimplexCategory.mk (nonemptySimplexDimension σ) := by
  let xρ := nonemptySimplexNonDegenerate M ρ
  let xσ := nonemptySimplexNonDegenerate M σ
  have hxρ : nonDegenerateSimplexFacet M xρ = ρ :=
    nonemptySimplexNonDegenerate_facet M ρ
  have hxσ : nonDegenerateSimplexFacet M xσ = σ :=
    nonemptySimplexNonDegenerate_facet M σ
  let e :
      {v : V // v ∈ (nonDegenerateSimplexFacet M xρ).1} ↪o
        {v : V // v ∈ (nonDegenerateSimplexFacet M xσ).1} :=
    { toFun := fun v => ⟨v.1, by
          rw [hxσ]
          apply hρσ
          simpa [hxρ] using v.2⟩
      inj' := fun a b h => by
        apply Subtype.ext
        have hv : (a : V) = (b : V) :=
          congrArg (fun z :
            {v : V // v ∈ (nonDegenerateSimplexFacet M xσ).1} =>
              (z : V)) h
        exact hv
      map_rel_iff' := fun {_ _} => Iff.rfl }
  exact SimplexCategory.Hom.mk
    ((nonDegenerateSimplexSupportOrderIso M xσ).symm.toOrderEmbedding.toOrderHom.comp
      (e.toOrderHom.comp
        (nonDegenerateSimplexSupportOrderIso M xρ).toOrderEmbedding.toOrderHom))

/-- The facet-inclusion operator sends the top simplex of `σ` to that of
`ρ`. -/
@[simp]
theorem orderedComplexSSet_map_facetInclusionHom
    (ρ σ : NonemptySimplex M) (hρσ : ρ.1 ⊆ σ.1) :
    (orderedComplexSSet M).map (facetInclusionHom M ρ σ hρσ).op
        (nonemptySimplexNonDegenerate M σ).1 =
      (nonemptySimplexNonDegenerate M ρ).1 := by
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  let xρ := nonemptySimplexNonDegenerate M ρ
  let xσ := nonemptySimplexNonDegenerate M σ
  have hxρ : nonDegenerateSimplexFacet M xρ = ρ :=
    nonemptySimplexNonDegenerate_facet M ρ
  have hxσ : nonDegenerateSimplexFacet M xσ = σ :=
    nonemptySimplexNonDegenerate_facet M σ
  let e :
      {v : V // v ∈ (nonDegenerateSimplexFacet M xρ).1} ↪o
        {v : V // v ∈ (nonDegenerateSimplexFacet M xσ).1} :=
    { toFun := fun v => ⟨v.1, by
          rw [hxσ]
          apply hρσ
          simpa [hxρ] using v.2⟩
      inj' := fun a b h => by
        apply Subtype.ext
        have hv : (a : V) = (b : V) :=
          congrArg (fun z :
            {v : V // v ∈ (nonDegenerateSimplexFacet M xσ).1} =>
              (z : V)) h
        exact hv
      map_rel_iff' := fun {_ _} => Iff.rfl }
  have hσ := (nonDegenerateSimplexSupportOrderIso M xσ).apply_symm_apply
    (e (nonDegenerateSimplexSupportOrderIso M xρ i))
  have hρ := nonDegenerateSimplexSupportOrderIso_apply M xρ i
  change xσ.1.1
      ((nonDegenerateSimplexSupportOrderIso M xσ).symm
        (e (nonDegenerateSimplexSupportOrderIso M xρ i))) = xρ.1.1 i
  calc
    _ = ((nonDegenerateSimplexSupportOrderIso M xσ)
          ((nonDegenerateSimplexSupportOrderIso M xσ).symm
            (e (nonDegenerateSimplexSupportOrderIso M xρ i)))).1 := by
      exact congrArg Subtype.val
        (nonDegenerateSimplexSupportOrderIso_apply M xσ _).symm
    _ = (e (nonDegenerateSimplexSupportOrderIso M xρ i)).1 :=
      congrArg Subtype.val hσ
    _ = (nonDegenerateSimplexSupportOrderIso M xρ i).1 := rfl
    _ = _ := congrArg Subtype.val hρ

/-- Restrict a local configuration on `σ` to the coordinates visible in
`ρ`. -/
def facetConfigurationRestriction (ρ σ : NonemptySimplex M) :
    Configuration (facesIn M q σ) G →+
      Configuration (facesIn M q ρ) G :=
  (coordinateRestriction (facesIn M q ρ)).comp
    (coordinateExtension (facesIn M q σ))

/-- Local evaluation commutes with restriction to a face. -/
theorem facetCochainLValueHom_restriction
    (ρ σ : NonemptySimplex M) (hρσ : ρ.1 ⊆ σ.1)
    (a : Configuration (facesIn M q σ) G) :
    facetCochainLValueHom M q ρ
        (facetConfigurationRestriction M q ρ σ a) =
      (L (AddCommGrpCat.of G) (q + 1)).map
        (facetInclusionHom M ρ σ hρσ).op
          (facetCochainLValueHom M q σ a) := by
  let c : Cochain M q G := coordinateExtension (facesIn M q σ) a
  let xρ := nonemptySimplexNonDegenerate M ρ
  let xσ := nonemptySimplexNonDegenerate M σ
  have hnat := cochainLValueHom_naturality (G := G) M q
    (facetInclusionHom M ρ σ hρσ).op xσ.1
  have hmap := orderedComplexSSet_map_facetInclusionHom M ρ σ hρσ
  rw [facetCochainLValueHom_apply, facetCochainLValueHom_apply]
  change cochainLValueHom M q _ xρ.1
      (coordinateExtension (facesIn M q ρ)
        (coordinateRestriction (facesIn M q ρ) c)) =
    (L (AddCommGrpCat.of G) (q + 1)).map _
      (cochainLValueHom M q _ xσ.1 c)
  have hlocalρ :
      cochainLValueHom M q _ xρ.1
          (coordinateExtension (facesIn M q ρ)
            (coordinateRestriction (facesIn M q ρ) c)) =
        cochainLValueHom M q _ xρ.1 c := by
    apply cochainLValue_eq_of_restrict_eq M q _ xρ
    change coordinateRestriction
        (facesIn M q (nonDegenerateSimplexFacet M xρ))
          (coordinateExtension (facesIn M q ρ)
            (coordinateRestriction (facesIn M q ρ) c)) =
      coordinateRestriction
        (facesIn M q (nonDegenerateSimplexFacet M xρ)) c
    rw [show nonDegenerateSimplexFacet M xρ = ρ by
      exact nonemptySimplexNonDegenerate_facet M ρ]
    exact coordinateRestriction_coordinateExtension
      (facesIn M q ρ) (coordinateRestriction (facesIn M q ρ) c)
  rw [hlocalρ]
  have hnatc := DFunLike.congr_fun hnat c
  have hmap' :
      (orderedComplexSSet M).map
          (facetInclusionHom M ρ σ hρσ).op xσ.1 = xρ.1 := by
    simpa only [xρ, xσ] using hmap
  rw [hmap'] at hnatc
  exact hnatc

/-- Pull the value of a native map at `σ` back through the local
classification to a reduced distribution of local cochains. -/
def nativeMapLocalDistribution
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1))))
    (σ : NonemptySimplex M) :
    RedDist (Configuration (facesIn M q σ) G) :=
  mapRedDist (facetCochainLValueEquiv (G := G) M q σ).symm.toAddMonoidHom
    (f.app (Opposite.op
      (SimplexCategory.mk (nonemptySimplexDimension σ)))
        (nonemptySimplexNonDegenerate M σ).1)

/-- Pushing the pulled-back local distribution forward again recovers the
given native value. -/
theorem mapRedDist_facetCochainLValue_nativeMapLocalDistribution
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1))))
    (σ : NonemptySimplex M) :
    mapRedDist (facetCochainLValueEquiv (G := G) M q σ).toAddMonoidHom
        (nativeMapLocalDistribution M q f σ) =
      f.app (Opposite.op
        (SimplexCategory.mk (nonemptySimplexDimension σ)))
          (nonemptySimplexNonDegenerate M σ).1 := by
  rw [nativeMapLocalDistribution,
    GeneralSphereT.StandardModels.mapRedDist_comp_apply]
  have hcomp :
      (facetCochainLValueEquiv (G := G) M q σ).toAddMonoidHom.comp
          (facetCochainLValueEquiv (G := G) M q σ).symm.toAddMonoidHom =
        AddMonoidHom.id _ := by
    ext y
    exact (facetCochainLValueEquiv (G := G) M q σ).apply_symm_apply y
  rw [hcomp]
  exact LinearMap.congr_fun
    (GeneralSphereT.StandardModels.mapRedDist_id (X :=
      (L (AddCommGrpCat.of G) (q + 1)).obj
        (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ))))) _

/-- The local distributions extracted from a native map restrict strictly
along inclusions of simplices. -/
theorem nativeMapLocalDistribution_restriction
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1))))
    (ρ σ : NonemptySimplex M) (hρσ : ρ.1 ⊆ σ.1) :
    mapRedDist (facetConfigurationRestriction M q ρ σ)
        (nativeMapLocalDistribution M q f σ) =
      nativeMapLocalDistribution M q f ρ := by
  have heval : Function.Injective
      (mapRedDist
        (facetCochainLValueEquiv (G := G) M q ρ).toAddMonoidHom) := by
    rw [mapRedDist_eq_mapRedDistFn]
    exact mapRedDistFn_injective_of_injective
      ((facetCochainLValueEquiv (G := G) M q ρ) :
        Configuration (facesIn M q ρ) G →
          (L (AddCommGrpCat.of G) (q + 1)).obj
            (Opposite.op
              (SimplexCategory.mk (nonemptySimplexDimension ρ))))
      (facetCochainLValueEquiv (G := G) M q ρ).injective
  apply heval
  rw [GeneralSphereT.StandardModels.mapRedDist_comp_apply]
  have hcomp :
      (facetCochainLValueEquiv (G := G) M q ρ).toAddMonoidHom.comp
          (facetConfigurationRestriction M q ρ σ) =
        ((L (AddCommGrpCat.of G) (q + 1)).map
          (facetInclusionHom M ρ σ hρσ).op).hom.comp
            (facetCochainLValueEquiv (G := G) M q σ).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro a
    exact facetCochainLValueHom_restriction (G := G)
      M q ρ σ hρσ a
  rw [hcomp,
    ← GeneralSphereT.StandardModels.mapRedDist_comp_apply]
  rw [mapRedDist_facetCochainLValue_nativeMapLocalDistribution,
    mapRedDist_facetCochainLValue_nativeMapLocalDistribution]
  have hnat := ConcreteCategory.congr_hom
    (f.naturality (facetInclusionHom M ρ σ hρσ).op)
      (nonemptySimplexNonDegenerate M σ).1
  change mapRedDist
      ((L (AddCommGrpCat.of G) (q + 1)).map
        (facetInclusionHom M ρ σ hρσ).op).hom
        (f.app (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ)))
            (nonemptySimplexNonDegenerate M σ).1) =
      f.app (Opposite.op
        (SimplexCategory.mk (nonemptySimplexDimension ρ)))
          (nonemptySimplexNonDegenerate M ρ).1
  rw [← reducedFree_map_apply]
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [orderedComplexSSet_map_facetInclusionHom] at hnat
  change
      f.app (Opposite.op
        (SimplexCategory.mk (nonemptySimplexDimension ρ)))
          (nonemptySimplexNonDegenerate M ρ).1 =
        (reducedFree (L (AddCommGrpCat.of G) (q + 1))).map
          (facetInclusionHom M ρ σ hρσ).op
            (f.app (Opposite.op
              (SimplexCategory.mk (nonemptySimplexDimension σ)))
                (nonemptySimplexNonDegenerate M σ).1) at hnat
  exact hnat.symm

end GeneralSphereT.SimplicialCochain
