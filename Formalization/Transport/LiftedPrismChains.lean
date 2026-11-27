import Formalization.Transport.ConePrismCharacter
import Formalization.Transport.MeasuredCycles

/-! Integral chains lifting the measured cone segment along the disk-to-sphere
map of Dold--Kan models. All identities hold before passage to homology. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.StandardModels GeneralSphereT.DoldKanExplicitBridge
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality
variable {G : Type} [AddCommGroup G] {Y : Type*} {p q : ℕ}

abbrev Disk (G : Type) [AddCommGroup G] (q p : ℕ) := (L (AddCommGrpCat.of G) (q+1)).obj (op ⦋p⦌)
def diskValue (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y) : Disk G q p :=
  standardGlobalLValue p q (stringCochain field x)

theorem diskValue_face (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y)
    {m : ℕ} (e : FaceEmbedding p m) :
    (L (AddCommGrpCat.of G) (q+1)).map (show ⦋m⦌ ⟶ ⦋p⦌ from SimplexCategory.Hom.mk e.toOrderHom).op (diskValue field x)=
      diskValue field (fun i => x (e i)) := by
  unfold diskValue
  rw [standardL_face,pullback_string]

def diskBoundary : Distribution (Disk G q (p+1)) →ₗ[ℤ] Distribution (Disk G q p) :=
  Finsupp.linearCombination ℤ fun a => ∑ i : Fin (p+2), ((-1:ℤ)^i.val) •
    Finsupp.single ((L (AddCommGrpCat.of G) (q+1)).δ i a) 1

def diskChain (field : (Fin (q+1) → Y) → G) (p : ℕ) :
    Chains Y →ₗ[ℤ] Distribution (Disk G q p) :=
  Finsupp.linearCombination ℤ fun xs => if h : xs.length=p+1 then
    Finsupp.single (diskValue field (fun i => xs.get (i.cast h.symm))) 1 else 0

theorem diskChain_ofFn (field : (Fin (q+1) → Y) → G) (x : Fin (p+1) → Y) :
    diskChain field p (gen (List.ofFn x))=Finsupp.single (diskValue field x) 1 := by
  simp only [diskChain,gen,Finsupp.linearCombination_single,one_smul,dite_eq_left (List.length_ofFn (f:=x))]
  have he : (fun i : Fin (p+1) => (List.ofFn x).get (i.cast (List.length_ofFn (f:=x)).symm))=x := by
    funext i
    simp only [List.get_eq_getElem,List.getElem_ofFn]
    rfl
  rw [he]

private theorem diskChain_other (field : (Fin (q+1) → Y) → G) {k : ℕ} (x : Fin k → Y) (h : k ≠ p+1) :
    diskChain field p (gen (List.ofFn x))=0 := by simp [diskChain,gen,h]

theorem diskChain_boundary (field : (Fin (q+1) → Y) → G) :
    diskBoundary.comp (diskChain field (p+1))=(diskChain field p).comp boundary := by
  have each (k : ℕ) (x : Fin (k+1) → Y) : diskBoundary (diskChain field (p+1) (gen (List.ofFn x)))=
      diskChain field p (boundary (gen (List.ofFn x))) := by
    rw [boundary_gen,faces_ofFn,map_sum]
    by_cases h : k=p+1
    · subst k
      rw [diskChain_ofFn]
      simp only [diskBoundary,Finsupp.linearCombination_single,one_smul,map_smul,diskChain_ofFn]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun a : Disk G q p => ((-1:ℤ)^i.val) • Finsupp.single a (1:ℤ))
        (diskValue_face field x (Fin.succAboveOrderEmb i))
    · have ne : k+1 ≠ p+2 := by omega
      simp only [diskChain_other field _ ne,map_zero,map_smul,diskChain_other field _ h,smul_zero,Finset.sum_const_zero]
  apply Finsupp.lhom_ext'
  intro xs
  apply LinearMap.ext_ring
  change diskBoundary (diskChain field (p+1) (gen xs))=diskChain field p (boundary (gen xs))
  cases xs with
  | nil => rw [boundary_gen]; simp [diskChain,gen,faces]
  | cons y ys => simpa only [LinearMap.comp_apply,List.ofFn_get] using each ys.length (y::ys).get

theorem diskChain_projects (field : (Fin (q+1) → Y) → G) :
    (mapDistFn ((d (AddCommGrpCat.of G) (q+1)).app (op ⦋p⦌))).comp (diskChain field p)=simplexChain field p := by
  apply Finsupp.lhom_ext'
  intro xs
  apply LinearMap.ext_ring
  change mapDistFn _ (diskChain field p (gen xs))=simplexChain field p (gen xs)
  simp only [diskChain,simplexChain,gen,Finsupp.linearCombination_single,one_smul]
  split
  · rw [mapDistFn_single]
    exact congrArg (fun a => Finsupp.single a (1:ℤ)) (standardGlobal_d_eq_coboundary _ _ _)
  · exact map_zero _

variable {V : Type} [LinearOrder V] [Fintype V] (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance lcLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance lcLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance lcOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance

def orientedCone (coeff : Simplex X d → ℤ) := cons none (vertices some (orientedFacets X d coeff))

def liftedSegment (coeff : Simplex X d → ℤ) (u w : Cochain (simplicialCone X) q G) :=
  diskChain (affineField (simplicialCone X) q) (d+2) (segment (layerOf _ q u) (layerOf _ q w) (orientedCone X d coeff))

theorem liftedSegment_projects (coeff : Simplex X d → ℤ) (u w : Cochain (simplicialCone X) q G)
    (ω : EM G (q+1) (d+2) → Phase) :
    evaluate ω (mapDistFn ((GeneralSphereT.StandardModels.d (AddCommGrpCat.of G) (q+1)).app _)
      (liftedSegment X q d coeff u w))=coneEdge X q d ω coeff u w := by
  unfold liftedSegment coneEdge
  exact (congrArg (evaluate ω) (LinearMap.congr_fun (diskChain_projects _) _)).trans
    (LinearMap.congr_fun (evaluate_simplexChain _ ω) _)

theorem liftedSegment_boundary (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (u w : Cochain (simplicialCone X) q G) :
    let read := diskChain (affineField (simplicialCone X) q) (d+1)
    diskBoundary (liftedSegment X q d coeff u w)=
      read (vertices (layerOf _ q w) (orientedCone X d coeff)) -
      read (vertices (layerOf _ q u) (orientedCone X d coeff)) -
      read (segment (layerOf _ q u) (layerOf _ q w) (vertices some (orientedFacets X d coeff))) := by
  intro read
  unfold liftedSegment
  rw [show ∀ z, diskBoundary (diskChain (affineField (simplicialCone X) q) (d+2) z)=read (boundary z)
    from LinearMap.congr_fun (diskChain_boundary _) ,boundary_segment]
  simp only [orientedCone,boundary_cons,boundary_vertices,hz,map_zero,sub_zero,map_sub]

end GeneralSphereT.Transport.Prism

