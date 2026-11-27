import Formalization.Section4GlobalFacetVanishing
import Formalization.Section4RprimBasedNativeMap
import Formalization.Section4LiteralConeNativeCriterion

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: primitive cone extensions give native null maps

This is the forward half of (4.6).  A based primitive relation is extended
over the literal cone, its algebraic vanishing on the basepoint edge is
converted into genuine vanishing of the Dold--Kan map on that edge, and the
explicit cone contraction supplies an actual pointed nullhomotopy.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetRestrictionHom
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

local instance (priority := 10000) nativeConeForwardOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) nativeConeForwardOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) nativeConeForwardOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

omit [Fintype V] in
/-- Every vertex traversed by the basepoint trajectory is a vertex of the
distinguished cone edge. -/
theorem literalConeBaseLineMap_vertex_mem_edge
    (M : AbstractSimplicialComplex V) (b : V)
    (Delta : SimplexCategoryᵒᵖ)
    (z : ((orderedComplexBasepointSubcomplex M b : SSet) ⊗ Δ[1]).obj Delta)
    (i : Fin (Delta.unop.len + 1)) :
    ((literalConeBaseLineMap M b).app Delta z).1 i ∈
      (coneBasepointEdgeFacet M b).1 := by
  induction Delta using Opposite.rec with
  | _ Delta =>
    induction Delta using SimplexCategory.rec with
    | _ n =>
      have hb :
          (((orderedComplexBasepointSubcomplex M b).ι.app
              (Opposite.op (SimplexCategory.mk n)) z.1).1 i) = b := by
        have hι : (orderedComplexBasepointSubcomplex M b).ι =
            SSet.const (orderedComplexVertex M b) := by
          simpa only [orderedComplexBasepointSubcomplex] using
            (SSet.Subcomplex.ofSimplex_ι (orderedComplexVertex M b))
        rw [hι]
        rfl
      change
        (if SSet.stdSimplex.asOrderHom z.2 i = 0 then none
          else some
            (((orderedComplexBasepointSubcomplex M b).ι.app
              (Opposite.op (SimplexCategory.mk n)) z.1).1 i)) ∈
          (coneBasepointEdgeFacet M b).1
      rw [hb]
      by_cases ht : SSet.stdSimplex.asOrderHom z.2 i = 0
      · simp [ht, coneBasepointEdgeFacet, basepointFacet]
      · simp [ht, coneBasepointEdgeFacet, basepointFacet]

/-- The distinguished cone edge as a nondegenerate simplex of the honest
ordered-complex simplicial set. -/
def coneBasepointEdgeNonDegenerate
    (M : AbstractSimplicialComplex V) (b : V) :=
  nonemptySimplexNonDegenerate (simplicialCone M)
    (coneBasepointEdgeFacet M b)

@[simp]
theorem coneBasepointEdgeNonDegenerate_facet
    (M : AbstractSimplicialComplex V) (b : V) :
    nonDegenerateSimplexFacet (simplicialCone M)
        (coneBasepointEdgeNonDegenerate M b) =
      coneBasepointEdgeFacet M b :=
  nonemptySimplexNonDegenerate_facet (simplicialCone M)
    (coneBasepointEdgeFacet M b)

omit [Fintype V] in
/-- The initial endpoint of the basepoint trajectory is the cone apex. -/
@[reassoc]
theorem ι₀_literalConeBaseLineMap
    (M : AbstractSimplicialComplex V) (b : V) :
    SSet.ι₀ ≫ literalConeBaseLineMap M b =
      SSet.const (literalConeApex M) := by
  rw [literalConeBaseLineMap, ← Category.assoc, SSet.ι₀_comp,
    Category.assoc, ι₀_literalConeCylinderMap, SSet.comp_const]

/-- If a global cone distribution vanishes on the basepoint edge, its
genuine Dold--Kan map vanishes along the whole basepoint trajectory in the
literal cone contraction. -/
theorem literalConeBaseLineMap_comp_globalRestriction_eq_zero
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (u : RedDist (Cochain (simplicialCone M) q G))
    (hedge : mapRedDist
        (restrictCochain (G := G) (simplicialCone M) q
          (coneBasepointEdgeFacet M b)) u = 0) :
    literalConeBaseLineMap M b ≫
        globalCochainRestrictionMap (simplicialCone M) q u = 0 := by
  let x := coneBasepointEdgeNonDegenerate M b
  have hsupport :
      (nonDegenerateSimplexSupportMap (simplicialCone M) x).toSSetMap ≫
          globalCochainRestrictionMap (simplicialCone M) q u = 0 := by
    apply supportMap_comp_globalRestriction_eq_zero_of_restrict_eq_zero
      (simplicialCone M) q _ u x
    rw [show nonDegenerateSimplexFacet (simplicialCone M) x =
        coneBasepointEdgeFacet M b by
      exact coneBasepointEdgeNonDegenerate_facet M b]
    exact hedge
  ext Delta z
  let y := (literalConeBaseLineMap M b).app Delta z
  have hy_mem (i : Fin (Delta.unop.len + 1)) :
      y.1 i ∈
        (nonDegenerateSimplexFacet (simplicialCone M) x).1 := by
    rw [show nonDegenerateSimplexFacet (simplicialCone M) x =
        coneBasepointEdgeFacet M b by
      exact coneBasepointEdgeNonDegenerate_facet M b]
    exact literalConeBaseLineMap_vertex_mem_edge M b Delta z i
  let ySupport :
      (orderedComplexSSet
        (nonDegenerateSimplexSupportComplex (simplicialCone M) x)).obj Delta := by
    refine ⟨⟨fun i ↦ ⟨y.1 i, hy_mem i⟩, ?_⟩, ?_⟩
    · intro i j hij
      exact y.1.monotone hij
    · change (orderedSimplexSupport
          (⟨fun i ↦ ⟨y.1 i, hy_mem i⟩,
            by
              intro i j hij
              exact y.1.monotone hij⟩ :
            Fin (Delta.unop.len + 1) →o
              {v : Option V //
                v ∈ (nonDegenerateSimplexFacet
                  (simplicialCone M) x).1})).Nonempty
      exact Finset.image_nonempty.mpr Finset.univ_nonempty
  have hymap :
      (nonDegenerateSimplexSupportMap (simplicialCone M) x).toSSetMap.app
          Delta ySupport = y := by
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    rfl
  have hz := ConcreteCategory.congr_hom (congr_app hsupport Delta) ySupport
  change (globalCochainRestrictionMap (simplicialCone M) q u).app Delta y = 0
  rw [← hymap]
  exact hz

/-- The preceding strict vanishing lifts from `reducedFree L` to the
categorical fibre `F`. -/
theorem literalConeBaseLineMap_comp_rprimToNativeFiberMap_eq_zero
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) (simplicialCone M) q))
    (hedge : evalRprim
        (facetRestrictionData (G := G) (simplicialCone M) q)
          (coneBasepointEdgeFacet M b) r = 0) :
    literalConeBaseLineMap M b ≫
        rprimToNativeFiberMap (simplicialCone M) q r = 0 := by
  apply (cancel_mono
    (underlyingMap (Fι (AddCommGrpCat.of G) (q + 1)))).1
  rw [Category.assoc, rprimToNativeFiberMap_comp_inclusion]
  have hedge' : mapRedDist
      (restrictCochain (G := G) (simplicialCone M) q
        (coneBasepointEdgeFacet M b))
      (r : RedDist (Cochain (simplicialCone M) q G)) = 0 := by
    exact congrArg Subtype.val hedge
  rw [literalConeBaseLineMap_comp_globalRestriction_eq_zero
    M b q (r : RedDist (Cochain (simplicialCone M) q G)) hedge']
  ext Delta z
  change 0 = ((Fι (AddCommGrpCat.of G) (q + 1)).app Delta).hom 0
  exact (map_zero ((Fι (AddCommGrpCat.of G) (q + 1)).app Delta).hom).symm

omit [Fintype V] in
/-- Vanishing along the basepoint trajectory already forces vanishing at
the apex.  The only input is that the chosen basepoint subcomplex contains
its defining vertex. -/
theorem literalConeApex_comp_eq_zero_of_baseLine
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    (f : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A)
    (hbase : literalConeBaseLineMap M b ≫ f = 0) :
    SSet.const
        (X := orderedComplexSSet (simplicialCone M))
        (literalConeApex M) ≫ f = 0 := by
  have hconstBase :
      SSet.const
          (X := (orderedComplexBasepointSubcomplex M b : SSet))
          (literalConeApex M) ≫ f = 0 := by
    rw [← ι₀_literalConeBaseLineMap M b, Category.assoc, hbase]
    ext Delta z
    rfl
  let p :
      (orderedComplexBasepointSubcomplex M b : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) :=
    ⟨orderedComplexVertex M b,
      SSet.Subcomplex.mem_ofSimplex_obj (orderedComplexVertex M b)⟩
  have hapex :
      f.app (Opposite.op (SimplexCategory.mk 0)) (literalConeApex M) = 0 := by
    have hp := ConcreteCategory.congr_hom
      (congr_app hconstBase (Opposite.op (SimplexCategory.mk 0))) p
    exact hp
  rw [SSet.const_comp, hapex]
  exact GeneralSphereT.Section4.RelativeMapping.const_zeroVertex_eq_zeroMap
    (X := orderedComplexSSet (simplicialCone M)) A

/-- Extending a based primitive relation over the pointed literal cone
produces an actual pointed extension of its native fibre-valued map. -/
def PointedConeRelationExtensionData.toLiteralPointedExtension
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (E : PointedConeRelationExtensionData (G := G) M b q)
    (r : LinearMap.ker
      (simplicialBasepointRowData (G := G) M b q).evalR) :
    LiteralPointedExtension M b
      (F (AddCommGrpCat.of G) (q + 1))
      (basedRprimToNativePointedMap M b q r) := by
  let er := E.extendRelation r
  have hrestrict :
      mapRprim (coneBottomFacetHom (G := G) M q) er.1 = r.1 := by
    have h := LinearMap.congr_fun E.restrict_extend r
    exact congrArg Subtype.val h
  have hbase :
      literalConeBaseLineMap M b ≫
          rprimToNativeFiberMap (simplicialCone M) q er.1 = 0 :=
    literalConeBaseLineMap_comp_rprimToNativeFiberMap_eq_zero
      M b q er.1 er.2
  exact
    { map := rprimToNativeFiberMap (simplicialCone M) q er.1
      bottom := by
        rw [rprimToNativeFiberMap_pullback]
        exact congrArg (rprimToNativeFiberMap M q) hrestrict
      apex := literalConeApex_comp_eq_zero_of_baseLine
        M b (F (AddCommGrpCat.of G) (q + 1)) _ hbase
      baseLine := hbase }

/-- Hence every based primitive relation represents the zero native
relative homotopy class. -/
theorem PointedConeRelationExtensionData.nativePrimitive_class_eq_zero
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (E : PointedConeRelationExtensionData (G := G) M b q)
    (r : LinearMap.ker
      (simplicialBasepointRowData (G := G) M b q).evalR) :
    (basedRprimToNativePointedMap M b q r).homotopyClass =
      (0 : NativePointedMaps M b (AddCommGrpCat.of G) (q + 1)).homotopyClass :=
  (E.toLiteralPointedExtension M b q r).class_eq_zero

/-- Forward inclusion in the native form of (4.6): the image of every
based primitive relation is genuinely pointed-nullhomotopic. -/
theorem PointedConeRelationExtensionData.range_basedRprimToNativePointedMap_le_null
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (E : PointedConeRelationExtensionData (G := G) M b q) :
    LinearMap.range (basedRprimToNativePointedMap M b q) ≤
      NativeNullMaps (orderedComplexBasepointSubcomplex M b)
        (F (AddCommGrpCat.of G) (q + 1)) := by
  intro f hf
  rcases hf with ⟨r, rfl⟩
  rw [LinearMap.mem_ker]
  change (basedRprimToNativePointedMap M b q r).homotopyClass = 0
  rw [E.nativePrimitive_class_eq_zero M b q r,
    homotopyClass_zero]

end GeneralSphereT.SimplicialCochain
