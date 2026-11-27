import Formalization.Transport.RelativeCochainExact

/-! Derive low-dimensional exactness for every coefficient group from the
single integral fundamental class of the relative cone. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory Opposite Simplicial OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain OrderedSimplicialMap RelativeChains
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
local instance vanishLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance vanishLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance vanishOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (d : ℕ)
variable (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
variable (hs : IsRelativeHomologySphere X d coeff hz)
private abbrev P := literalConeBottomSubcomplex X
private abbrev C := relativeComplex (simplicialCone X) (P X)

private theorem bottom_read_zero (k : ℕ) (g : (C X).X k ⟶ ModuleCat.of ℤ G) :
    (coneBottomInclusion X).pullback k (readRelative _ (P X) k g)=0 := by
  ext σ
  obtain ⟨x,rfl⟩ := (nonDegenerateSimplexEquiv X k).surjective σ
  rw [pullback_apply,← nonDegenerateSimplexEquiv_mapNonDegenerate,readRelative_at]
  change g (symbol (P X) ((literalConeBottomMap X).app _ x.val))=0
  rw [symbol_boundary _ _ (show (literalConeBottomMap X).app _ x.val ∈ (P X).obj _ from ⟨x.val,rfl⟩),map_zero]

include hs in
theorem closed_extension_of_orientation (k : ℕ) (hk : k<d) (c : Cochain X k G) (hc : coboundary X k c=0) :
    ∃ Z : Cochain (simplicialCone X) k G, coboundary _ k Z=0 ∧ (coneBottomInclusion X).pullback k Z=c := by
  let M := simplicialCone X
  let F := coneBottomInclusion X
  let u := F.extendCochainByZero k c
  let v := coboundary M k u
  have rest : F.pullback (k+1) v=0 := by
    have h := LinearMap.congr_fun (F.pullback_coboundary (G:=G) k) u
    simpa only [LinearMap.comp_apply,pullback_extendCochainByZero,u,hc] using h
  have vanish : ∀ x ∈ (P X).obj (op ⦋k+1⦌), spatialRead M (k+1) v x.val=0 := by
    rintro _ ⟨a,rfl⟩
    have h := field_bottom X (k+1) (fun i => (v,a.val i))
    change spatialRead M (k+1) v _=spatialRead X (k+1) (F.pullback (k+1) v) a.val at h
    exact h.trans (by rw [rest,spatialRead_simplex,map_zero]; rfl)
  let f := fromRelativeCochain M (P X) (k+1) v
  have closed := fromRelative_closed M (P X) (k+1) v (coboundary_coboundary M k u) vanish
  obtain ⟨g,hg⟩ := primitive_below_orientation (signedFundamental X d coeff hz) hs hk f closed
  let w := readRelative M (P X) k g
  have hw : coboundary M k w=v := (readRelative_d M (P X) k g).trans
    ((congrArg (readRelative M (P X) (k+1)) hg).trans (read_fromRelative M (P X) (k+1) v vanish))
  exact ⟨u-w,(map_sub _ _ _).trans (by rw [hw,sub_self]),
    (map_sub _ _ _).trans (by rw [bottom_read_zero,sub_zero,pullback_extendCochainByZero])⟩

private theorem closed_cone_zero (Z : Cochain (simplicialCone X) 0 G) (hZ : coboundary _ 0 Z=0) :
    ∃ a : G, Z=constantCochain _ a := by
  let M := simplicialCone X
  let η := coneApexSimplex M none
  let r := restrictClosedStar M η 0 Z
  have h : closedStarCoboundary M η 0 r=0 := by
    have e := LinearMap.congr_fun (restrictClosedStar_coboundary (G:=G) M η 0) Z
    exact e.symm.trans ((congrArg (restrictClosedStar M η 1) hZ).trans (map_zero _))
  let a := closedStarAugmentation M η none (mem_coneApexSimplex M none) r
  refine ⟨a,restrictClosedStar_apex_injective M (simplicialCone_isConeAt X) 0 ?_⟩
  rw [restrictClosedStar_constantCochain]
  have e := closedStar_contraction_zero M η none (mem_coneApexSimplex M none) r
  rw [h,map_zero] at e
  exact sub_eq_zero.mp e.symm

include hs in
/-- Integral relative sphere homology suffices for all coefficients, including
the homomorphism-valued coefficients used to choose simultaneous lifts. -/
theorem reducedExact_of_orientation (b : V) (k : ℕ) (hk : k<d) :
    ReducedCohomologyZeroAt (G:=G) X b k := by
  cases k with
  | zero =>
    apply le_antisymm _ bot_le
    intro z h
    obtain ⟨Z,hZ,rZ⟩ := closed_extension_of_orientation X d coeff hz hs 0 hk z.val h
    obtain ⟨a,rfl⟩ := closed_cone_zero X Z hZ
    have he : constantCochain X a=z.val := rZ
    have atb := DFunLike.congr_fun he (basepointSimplex X b)
    have ha : a=0 := atb.trans z.property
    apply (Submodule.mem_bot _).mpr
    apply Subtype.ext
    rw [← he,ha]
    ext
    rfl
  | succ n =>
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact coboundary_coboundary X n w
    · intro z h
      obtain ⟨Z,hZ,rZ⟩ := closed_extension_of_orientation X d coeff hz hs (n+1) hk z h
      let w := simplicialConeCocyclePrimitive X n Z
      refine ⟨(coneBottomInclusion X).pullback n w,?_⟩
      have e := LinearMap.congr_fun ((coneBottomInclusion X).pullback_coboundary (G:=G) n) w
      exact e.symm.trans ((congrArg ((coneBottomInclusion X).pullback (n+1)) (coboundary_simplicialConeCocyclePrimitive X n Z hZ)).trans rZ)

end GeneralSphereT.Transport.Prism
