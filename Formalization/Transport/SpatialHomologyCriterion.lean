import Formalization.Transport.OrientationDegree
import Mathlib.Algebra.Homology.SingleHomology

/-! Verify primitiveness of the signed generator using one oriented simplex.
The remaining homology input specifies only the groups in each degree. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain RelativeChains
private abbrev Z := ModuleCat.of ℤ ℤ

private theorem int_end_comm (a b : Z ⟶ Z) : a ≫ b=b ≫ a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have h (u : Z ⟶ Z) (m : ℤ) : u m=m*u 1 := by
    simpa only [smul_eq_mul,mul_one] using u.hom.map_smul m (1:ℤ)
  exact (h b (a 1)).trans ((mul_comm _ _).trans (h a (b 1)).symm)

private theorem quasiIso_of_split_sphere {C : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ}
    (f : ChainSphere.sphere (R:=ℤ) n ⟶ C) (g : C ⟶ ChainSphere.sphere (R:=ℤ) n) (h : f ≫ g=𝟙 _)
    (top : C.homology n ≅ Z) (off : ∀ i, i≠n → IsZero (C.homology i)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i=n
  · subst i
    let s := singleObjHomologySelfIso (.down ℕ) n Z
    let a := s.inv ≫ homologyMap f n ≫ top.hom
    let b := top.inv ≫ homologyMap g n ≫ s.hom
    have hab : a ≫ b=𝟙 _ := by simp [a,b,← homologyMap_comp_assoc,h]
    letI : IsIso a := ⟨⟨b,hab,(int_end_comm b a).trans hab⟩⟩
    have e : homologyMap f n=s.hom ≫ a ≫ top.inv := by simp [a]
    rw [e]
    infer_instance
  · have hs := isZero_single_obj_homology (.down ℕ) n Z i hi
    exact ⟨⟨0,hs.eq_of_src _ _,(off i hi).eq_of_src _ _⟩⟩

variable {V : Type} [LinearOrder V] [Fintype V] (X : AbstractSimplicialComplex V) (d : ℕ)
variable (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
abbrev coneRelative := altChains.obj (relFree (literalConeBottomSubcomplex X))

theorem orientation_of_spatial_homology (hp : PureInDimension X d) (σ : Simplex X d)
    (unit : coeff σ=1 ∨ coeff σ= -1) (top : (coneRelative X).homology (d+1) ≅ Z)
    (off : ∀ i, i≠d+1 → IsZero ((coneRelative X).homology i)) : IsRelativeHomologySphere X d coeff hz := by
  let C := coneRelative X
  let z := signedFundamental X d coeff hz
  let f := ChainSphere.mapOfCycle C (d+1) z
  let read := coeff σ • facetFunctional X d σ
  have hread : ∀ i, (ComplexShape.down ℕ).Rel i (d+1) → C.d i (d+1) ≫ read=0 := by
    intro i hi
    obtain rfl : i=d+2 := hi.symm
    change _ ≫ (coeff σ • facetFunctional X d σ)=0
    rw [Preadditive.comp_zsmul,facetFunctional_closed X d hp σ,smul_zero]
  let g := mkHomToSingle read hread
  refine quasiIso_of_split_sphere f g ?_ top off
  apply ChainSphere.evaluation_injective
  apply Subtype.ext
  have e : f.f (d+1) (ChainSphere.generator (R:=ℤ) (d+1))=z.val :=
    congrArg Subtype.val (ChainSphere.evaluation_mapOfCycle C (d+1) z)
  change g.f (d+1) (f.f (d+1) (ChainSphere.generator _))=ChainSphere.generator _
  rw [e]
  change (mkHomToSingle read hread).f (d+1) z.val=_
  rw [mkHomToSingle_f]
  apply congrArg (singleObjXSelf (.down ℕ) (d+1) Z).inv
  change coeff σ * facetFunctional X d σ (alternatingConeCycle X d coeff)=1
  rw [facetFunctional_reads X d hp σ coeff]
  rcases unit with h|h <;> rw [h] <;> decide

end GeneralSphereT.Transport.Prism
