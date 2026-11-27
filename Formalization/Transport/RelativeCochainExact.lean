import Formalization.Transport.ConeConnectingClass
import Formalization.Transport.SpatialPullback

/-! Read a relative cochain on the nondegenerate spatial simplices.
A contraction to the orientation gives primitives in every lower degree
with arbitrary abelian coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory HomologicalComplex Opposite Simplicial AlgebraicTopology OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain RelativeChains

theorem primitive_below_orientation {R : Type} [CommRing R]
    {C : ChainComplex (ModuleCat R) ℕ} [∀ i, Projective (C.X i)]
    {d k : ℕ} (z : ChainSphere.cycles C (d+1)) (hz : QuasiIso (ChainSphere.mapOfCycle C (d+1) z))
    (hk : k<d) {U : ModuleCat R} (f : C.X (k+1) ⟶ U) (hf : C.d (k+2) (k+1) ≫ f=0) :
    ∃ g : C.X k ⟶ U, C.d (k+1) k ≫ g=f := by
  let e := fundamentalSphereEquiv C (d+1) z hz
  let H := e.homotopyInvHomId.symm
  refine ⟨H.hom k (k+1) ≫ f,?_⟩
  have h := H.comm (k+1)
  have hzero : e.inv.f (k+1)=0 :=
    (isZero_single_obj_X (.down ℕ) (d+1) (ModuleCat.of R R) (k+1) (by omega)).eq_of_tgt _ _
  simp only [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,id_f,comp_f,hzero,Limits.zero_comp,add_zero] at h
  have eq := congrArg (fun t : C.X (k+1) ⟶ C.X (k+1) => t ≫ f) h
  simpa only [Category.id_comp,Preadditive.add_comp,Category.assoc,hf,Limits.comp_zero,add_zero] using eq.symm

variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (X : AbstractSimplicialComplex V) (P : (orderedComplexSSet X).Subcomplex)
abbrev relativeComplex := altChains.obj (relFree P)

omit [Fintype V] in
theorem relative_d_symbol (k : ℕ) (x : (orderedComplexSSet X) _⦋k+1⦌) :
    (relativeComplex X P).d (k+1) k (symbol P x)=∑ i : Fin (k+2), (-1:ℤ)^i.val • symbol P ((orderedComplexSSet X).δ i x) := by
  change (AlternatingFaceMapComplex.obj (relFree P)).d (k+1) k (symbol P x)=_
  rw [AlternatingFaceMapComplex.obj_d_eq]
  let ev : ((relFree P).obj (op ⦋k+1⦌) ⟶ (relFree P).obj (op ⦋k⦌)) →+ level P (op ⦋k⦌) :=
    { toFun := fun f => f (symbol P x), map_zero' := rfl, map_add' := fun _ _ => rfl }
  change ev (∑ i : Fin (k+2), (-1:ℤ)^i.val • (relFree P).δ i)=_
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (ev.map_zsmul _ _).trans (congrArg ((-1:ℤ)^i.val • ·) (restriction_symbol P _ x)))

def readRelative (k : ℕ) (f : (relativeComplex X P).X k ⟶ ModuleCat.of ℤ G) : Cochain X k G :=
  Finsupp.equivFunOnFinite.symm fun σ => f (symbol P ((nonDegenerateSimplexEquiv X k).symm σ).val)

theorem readRelative_at (k : ℕ) (f : (relativeComplex X P).X k ⟶ ModuleCat.of ℤ G)
    (x : (orderedComplexSSet X).nonDegenerate k) :
    readRelative X P k f (nonDegenerateSimplexEquiv X k x)=f (symbol P x.val) := by
  simp [readRelative]

theorem readRelative_d (k : ℕ) (f : (relativeComplex X P).X k ⟶ ModuleCat.of ℤ G) :
    coboundary X k (readRelative X P k f) = readRelative X P (k+1) ((relativeComplex X P).d (k+1) k ≫ f) := by
  ext σ
  obtain ⟨x,rfl⟩ := (nonDegenerateSimplexEquiv X (k+1)).surjective σ
  rw [coboundary_nonDegenerateSimplexEquiv,readRelative_at]
  change _=f ((relativeComplex X P).d (k+1) k (symbol P x.val))
  rw [relative_d_symbol,map_sum]
  exact Finset.sum_congr rfl (fun i _ => (congrArg ((-1:ℤ)^i.val • ·) (readRelative_at X P k f (orderedNonDegenerateFace X x i))).trans
    (f.hom.map_smul _ _).symm)

def fromRelativeCochain (k : ℕ) (c : Cochain X k G) :
    (relativeComplex X P).X k ⟶ ModuleCat.of ℤ G :=
  ModuleCat.ofHom (Finsupp.linearCombination ℤ fun x : {a : (orderedComplexSSet X) _⦋k⦌ // a ∉ P.obj _} => spatialRead X k c x.val.val)

omit [Fintype V] in
theorem fromRelative_symbol (k : ℕ) (c : Cochain X k G)
    (hc : ∀ x ∈ P.obj (op ⦋k⦌), spatialRead X k c x.val=0) (x : (orderedComplexSSet X) _⦋k⦌) :
    fromRelativeCochain X P k c (symbol P x)=spatialRead X k c x.val :=
  lift_symbol P (B:=AddCommGrpCat.of G) _ hc x

theorem read_fromRelative (k : ℕ) (c : Cochain X k G)
    (hc : ∀ x ∈ P.obj (op ⦋k⦌), spatialRead X k c x.val=0) :
    readRelative X P k (fromRelativeCochain X P k c)=c := by
  ext σ
  obtain ⟨x,rfl⟩ := (nonDegenerateSimplexEquiv X k).surjective σ
  rw [readRelative_at,fromRelative_symbol X P k c hc,spatialRead_simplex,
    cochainEquivNormalizedCochainHom_nonDegenerate_generator X k c x]

theorem fromRelative_closed (k : ℕ) (c : Cochain X k G) (h : coboundary X k c=0)
    (hc : ∀ x ∈ P.obj (op ⦋k⦌), spatialRead X k c x.val=0) :
    (relativeComplex X P).d (k+1) k ≫ fromRelativeCochain X P k c=0 := by
  let a := (relativeComplex X P).d (k+1) k ≫ fromRelativeCochain X P k c
  have symb (x : (orderedComplexSSet X) _⦋k+1⦌) : a (symbol P x)=0 := by
    change fromRelativeCochain X P k c ((relativeComplex X P).d (k+1) k (symbol P x))=0
    rw [relative_d_symbol,map_sum]
    have e := spatialRead_d X k c x
    rw [h,spatialRead_simplex,map_zero] at e
    refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) e.symm
    exact ((fromRelativeCochain X P k c).hom.map_smul _ _).trans
      (congrArg ((-1:ℤ)^i.val • ·) (fromRelative_symbol X P k c hc ((orderedComplexSSet X).δ i x)))
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change a (Finsupp.single x 1)=0
  simpa only [symbol,dif_neg x.property] using symb x.val

end GeneralSphereT.Transport.Prism
