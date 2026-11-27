import Formalization.Transport.SpherePrismIso
import Formalization.Transport.SphereCohomologyVanishing
import Mathlib.Algebra.Group.TransferInstance

/-! The additive classification in paper degrees 1 ≤ q ≤ d. The only
homology input concerns the integral orientation of the spatial cone pair. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]

instance normalizedEMGroup (q d : ℕ) : AddCommGroup (NormalizedEMCohomology G q d) :=
  (normalizedCharacterEquiv q d).addCommGroup

variable (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance (k : ℕ) : Fintype (Simplex X k) := Fintype.ofFinite _

instance topMultiplierGroup : AddCommGroup (TopMultiplierClasses (G:=G) X d q) :=
  (multiplierClassification (topFacetData (G:=G) X d q)).addCommGroup

/-- The source addition is pointwise addition of cocycle tables. -/
theorem normalized_mk_add (ω η τ : NormalizedCocycle G q d) (h : τ.val=ω.val+η.val) :
    (Quotient.mk _ ω : NormalizedEMCohomology G q d)+Quotient.mk _ η=Quotient.mk _ τ := by
  let e := normalizedCharacterEquiv (G:=G) q d
  apply e.injective
  refine (e.apply_symm_apply _).trans ?_
  apply LinearMap.ext
  intro y
  obtain ⟨z,rfl⟩ := emClass_surj q d y
  change evaluate ω.val z.val+evaluate η.val z.val=evaluate τ.val z.val
  rw [h]
  exact (LinearMap.congr_fun (phaseTableEquiv.map_add ω.val η.val) z.val).symm

/-- The target addition is pointwise addition of multiplier phases. -/
theorem multiplier_mk_add (m n t : SimplicialMultiplier (G:=G) X d q) (h : t.value=m.value+n.value) :
    (Quotient.mk _ m : TopMultiplierClasses (G:=G) X d q)+Quotient.mk _ n=Quotient.mk _ t := by
  let L := topFacetData (G:=G) X d q
  let e := multiplierClassification L
  apply e.injective
  refine (e.apply_symm_apply _).trans ?_
  apply LinearMap.ext
  intro y
  obtain ⟨z,rfl⟩ := (identitiesInInvariant _ _).mkQ_surjective y
  change evaluate m.value z.val+evaluate n.value z.val=evaluate t.value z.val
  rw [h]
  exact (LinearMap.congr_fun (phaseTableEquiv.map_add m.value n.value) z.val).symm

variable (b : V) (hp : PureInDimension X d) (hq : q<d)
variable (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
variable (hs : IsRelativeHomologySphere X d coeff hz)

include hq hs in
private theorem lower_of_orientation : LowerExact (G:=G) X b q := by
  cases q with
  | zero => trivial
  | succ n => exact reducedExact_of_orientation X d coeff hz hs b n (by omega)

include hp hq hs in
/-- Here q is the primitive degree, one less than the q of Eq. (2.8). -/
def orientedTriangleIso : NormalizedEMCohomology G (q+1) d ≃+ TopMultiplierClasses (G:=G) X d q := by
  let hc := reducedExact_of_orientation (G:=G) X d coeff hz hs b q hq
  let hall := reducedExact_of_orientation (G:=ShiftEvaluations (G:=G) X q) X d coeff hz hs b q hq
  let hl := lower_of_orientation (G:=G) X q d b hq coeff hz hs
  let e := spherePrismEquiv X q d b hp hc hl hall coeff hz hs
  refine { toEquiv := e, map_add' := ?_ }
  intro a a'
  let H := normalizedCharacterEquiv (G:=G) (q+1) d
  let T := multiplierClassification (topFacetData (G:=G) X d q)
  let p := prismClass X q d b hc coeff hz
  let f := integralPrism X q d b hc coeff hz
  apply T.injective
  change T (p (a+a'))=T (T.symm (T (p a)+T (p a')))
  rw [T.apply_symm_apply]
  have pair (x) : T (p x)=(H x).comp f := prism_pairing X q d b hc coeff hz x
  rw [pair,pair,pair,show H (a+a')=H a+H a' from H.apply_symm_apply _]
  rfl

@[simp] theorem orientedTriangleIso_mk (ω : NormalizedCocycle G (q+1) d) :
    orientedTriangleIso X q d b hp hq coeff hz hs (Quotient.mk _ ω)=Quotient.mk _
      (physicalPrismMultiplier X q d b (reducedExact_of_orientation X d coeff hz hs b q hq)
        ω.val ω.property.1 ω.property.2 coeff hz) := rfl

end GeneralSphereT.Transport.Prism
