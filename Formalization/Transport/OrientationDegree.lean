import Formalization.Transport.RelativeCochainExact
import Formalization.Transport.TopFacets

/-! Evaluation on a single oriented facet splits the fundamental-cycle map.
Only the spatial dimension bound and a unit coefficient enter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open CategoryTheory HomologicalComplex Opposite Simplicial OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain RelativeChains
variable {V : Type} [LinearOrder V] [Fintype V] (X : AbstractSimplicialComplex V) (d : ℕ)
local instance degLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance degLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance degOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
local instance degreeFacetFintype (k : ℕ) : Fintype (Simplex X k) := Fintype.ofFinite _
private abbrev M := simplicialCone X
private abbrev P := literalConeBottomSubcomplex X
private abbrev C := relativeComplex (M X) (P X)

omit [LinearOrder V] in
theorem face_card_bound (hp : PureInDimension X d) (σ : NonemptySimplex X) : σ.val.card≤d+1 := by
  obtain ⟨μ,hμ⟩ := exists_maximalFacet_superset X σ
  exact (Finset.card_le_card hμ).trans (hp μ).le

theorem cone_face_card_bound (hp : PureInDimension X d) (σ : NonemptySimplex (M X)) : σ.val.card≤d+2 := by
  classical
  let s := coneBaseVertices σ.val
  have hs : s.card≤d+1 := by
    rcases (mem_simplicialCone X _).mp σ.property with ⟨_,he|hX⟩
    · simp [s,he]
    · exact face_card_bound X d hp ⟨s,hX⟩
  have sub : σ.val ⊆ insert none (s.image some) := by
    rintro (_|v) h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ((mem_coneBaseVertices _ v).mpr h))
  have hle := Finset.card_le_card sub
  have hc : (s.image some).card=s.card := Finset.card_image_of_injective _ (Option.some_injective V)
  have ha := Finset.card_insert_le none (s.image some)
  omega

private def topString (σ : Simplex X d) : (orderedComplexSSet (M X)).nonDegenerate (d+1) :=
  ⟨orderedString (M X) (coneVertices X d σ) ⟨(coneVertices_strict X d σ).monotone,coneVertices_mem X d σ⟩,
    (mem_orderedComplexSSet_nonDegenerate_iff_injective _ _).mpr (coneVertices_strict X d σ).injective⟩

private def coneFacet (σ : Simplex X d) : Simplex (M X) (d+1) := nonDegenerateSimplexEquiv _ _ (topString X d σ)

private theorem coneFacet_injective : Function.Injective (coneFacet X d) := by
  intro a b h
  have e := (nonDegenerateSimplexEquiv _ _).injective h
  have eq (i : Fin (d+1)) : a.val.orderEmbOfFin a.property.2 i=b.val.orderEmbOfFin b.property.2 i :=
    Option.some.inj (congrArg (fun x : (orderedComplexSSet (M X)).nonDegenerate (d+1) => x.val.val i.succ) e)
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← a.val.range_orderEmbOfFin a.property.2,← b.val.range_orderEmbOfFin b.property.2]
  exact congrArg Set.range (funext eq)

private def facetCochain (σ : Simplex X d) : Cochain (M X) (d+1) ℤ := Finsupp.single (coneFacet X d σ) 1

private theorem facet_bottom (hp : PureInDimension X d) (σ : Simplex X d) :
    ∀ a ∈ (P X).obj (op ⦋d+1⦌), spatialRead (M X) (d+1) (facetCochain X d σ) a.val=0 := by
  rintro _ ⟨x,rfl⟩
  let c := facetCochain X d σ
  have no : (coneBottomInclusion X).pullback (d+1) c=0 := by
    ext t
    have hc := face_card_bound X d hp ⟨t.val,t.property.1⟩
    change t.val.card≤d+1 at hc
    have hdim := t.property.2
    omega
  have eq := field_bottom X (d+1) (fun i => (c,x.val i))
  change _=spatialRead X (d+1) ((coneBottomInclusion X).pullback (d+1) c) x.val at eq
  exact eq.trans (by rw [no,spatialRead_simplex,map_zero]; rfl)

def facetFunctional (σ : Simplex X d) := fromRelativeCochain (M X) (P X) (d+1) (facetCochain X d σ)

theorem facetFunctional_closed (hp : PureInDimension X d) (σ : Simplex X d) :
    (C X).d (d+2) (d+1) ≫ facetFunctional X d σ=0 := by
  apply fromRelative_closed _ _ _ _ _ (facet_bottom X d hp σ)
  ext t
  have hc := cone_face_card_bound X d hp ⟨t.val,t.property.1⟩
  change t.val.card≤d+2 at hc
  have hdim := t.property.2
  omega

theorem facetFunctional_reads (hp : PureInDimension X d) (σ : Simplex X d) (coeff : Simplex X d → ℤ) :
    facetFunctional X d σ (alternatingConeCycle X d coeff)=coeff σ := by
  classical
  rw [alternatingConeCycle,orientedCone_sum,map_sum,map_sum]
  have term (τ : Simplex X d) :
      facetFunctional X d σ (relativeRead (M X) (P X) (d+1) (gen (List.ofFn (coneVertices X d τ))))=
        if σ=τ then 1 else 0 := by
    rw [relativeRead_ofFn,relativeString,dite_eq_left (show Admissible (M X) (coneVertices X d τ) from
      ⟨(coneVertices_strict X d τ).monotone,coneVertices_mem X d τ⟩)]
    change fromRelativeCochain _ _ _ _ (symbol _ (topString X d τ).val)=_
    rw [fromRelative_symbol _ _ _ _ (facet_bottom X d hp σ),spatialRead_simplex,
      cochainEquivNormalizedCochainHom_nonDegenerate_generator]
    simp only [facetCochain,Finsupp.single_apply]
    simp only [show nonDegenerateSimplexEquiv (M X) (d+1) (topString X d τ)=coneFacet X d τ from rfl,
      (coneFacet_injective X d).eq_iff]
  simp only [map_smul,term]
  simp

end GeneralSphereT.Transport.Prism
