import Formalization.Transport.RelativeChainHomotopy
import Formalization.Transport.LiftedPrismChains
import Formalization.Section4LiteralDoubleConeDifference

/-! The signed cone on the spatial fundamental chain as an actual cycle of
the relative simplicial chains of (CX,X). -/
noncomputable section
open CategoryTheory Opposite Simplicial AlgebraicTopology
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain RelativeChains
variable {V : Type} [LinearOrder V] [Fintype V] (X : AbstractSimplicialComplex V)

def Admissible {n : ℕ} (x : Fin (n+1) → V) := Monotone x ∧ Finset.univ.image x ∈ X
def orderedString {n : ℕ} (x : Fin (n+1) → V) (h : Admissible X x) : (orderedComplexSSet X) _⦋n⦌ :=
  ⟨⟨x,h.1⟩,h.2⟩

variable (P : (orderedComplexSSet X).Subcomplex)
def relativeString {p : ℕ} (x : Fin (p+1) → V) : level P (op ⦋p⦌) := by
  classical
  exact if h : Admissible X x then symbol P (orderedString X x h) else 0

def relativeRead (p : ℕ) : Chains V →ₗ[ℤ] level P (op ⦋p⦌) :=
  Finsupp.linearCombination ℤ fun xs => if h : xs.length=p+1 then
    relativeString X P (fun i => xs.get (i.cast h.symm)) else 0

omit [Fintype V] in
theorem relativeRead_ofFn {p : ℕ} (x : Fin (p+1) → V) :
    relativeRead X P p (gen (List.ofFn x))=relativeString X P x := by
  simp only [relativeRead,gen,Finsupp.linearCombination_single,one_smul,dite_eq_left (List.length_ofFn (f:=x))]
  apply congrArg (relativeString X P)
  funext i
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

omit [Fintype V] in
private theorem relativeRead_other (p : ℕ) {k : ℕ} (x : Fin k → V) (h : k ≠ p+1) :
    relativeRead X P p (gen (List.ofFn x))=0 := by simp [relativeRead,gen,h]

omit [Fintype V] in
private theorem delta_relativeString {n : ℕ} (x : Fin (n+2) → V) (h : Admissible X x) (j : Fin (n+2)) :
    (relFree P).δ j (relativeString X P x)=relativeString X P (fun i => x (j.succAbove i)) := by
  classical
  let y := (orderedComplexSSet X).δ j (orderedString X x h)
  have hy : Admissible X (fun i => x (j.succAbove i)) := ⟨y.val.monotone,y.property⟩
  rw [relativeString,dite_eq_left h,relativeString,dite_eq_left hy]
  exact restriction_symbol P _ (orderedString X x h)

theorem relativeRead_boundary (p : ℕ) {w : Chains V} (hw : w ∈ spatialChains X) :
    (AlternatingFaceMapComplex.obj (relFree P)).d (p+1) p (relativeRead X P (p+1) w)=relativeRead X P p (boundary w) := by
  classical
  induction hw using Submodule.span_induction with
  | mem w h =>
    obtain ⟨xs,σ,mono,sub,rfl⟩ := h
    cases xs with
    | nil => rw [boundary_gen]; simp [relativeRead,gen,faces]
    | cons y ys =>
      let x : Fin (ys.length+1) → V := (y::ys).get
      have he : List.ofFn x=y::ys := List.ofFn_get _
      rw [← he,boundary_gen,faces_ofFn,map_sum]
      by_cases hk : ys.length=p+1
      · let x' : Fin ((p+1)+1) → V := fun i => x (i.cast (by omega))
        have hx : List.ofFn x' = y::ys := by
          apply List.ext_getElem
          · simp [hk]
          · intro i hi hi'; rw [List.getElem_ofFn]; rfl
        have hmono : Monotone x' := by
          intro i j hij
          rcases lt_or_eq_of_le hij with lt|rfl
          · exact List.pairwise_ofFn.mp (show (List.ofFn x').Pairwise (· ≤ ·) from hx ▸ mono) lt
          · rfl
        have hm : Admissible X x' := ⟨hmono,(X.isRelLowerSet_faces σ.property).2 (by
          intro a ha
          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
          apply sub
          rw [← hx]
          exact List.mem_ofFn.mpr ⟨i,rfl⟩) (Finset.image_nonempty.mpr Finset.univ_nonempty)⟩
        have good : (AlternatingFaceMapComplex.obj (relFree P)).d (p+1) p (relativeRead X P (p+1) (gen (List.ofFn x')))=
            relativeRead X P p (boundary (gen (List.ofFn x'))) := by
          rw [relativeRead_ofFn,AlternatingFaceMapComplex.obj_d_eq,boundary_gen,faces_ofFn,map_sum]
          let ev : ((relFree P).obj (op ⦋p+1⦌) ⟶ (relFree P).obj (op ⦋p⦌)) →+ level P (op ⦋p⦌) :=
            { toFun := fun f => f (relativeString X P x'), map_zero' := rfl, map_add' := fun _ _ => rfl }
          change ev (∑ i : Fin (p+2), (-1:ℤ)^i.val • (relFree P).δ i)=_
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_zsmul,map_smul,relativeRead_ofFn]
          exact congrArg (fun z : level P (op ⦋p⦌) => (-1:ℤ)^i.val • z) (delta_relativeString X P x' hm i)
        rw [hx,← he,boundary_gen,faces_ofFn,map_sum] at good
        exact good
      · have h' : ys.length+1 ≠ (p+1)+1 := by omega
        simp only [relativeRead_other X P _ _ h',map_zero,map_smul,relativeRead_other X P _ _ hk,smul_zero,Finset.sum_const_zero]
  | zero => simp
  | add _ _ _ _ hx hy => simp only [map_add,hx,hy]
  | smul a x _ hx =>
    simp only [map_smul]
    exact (((AlternatingFaceMapComplex.obj (relFree P)).d (p+1) p).hom.map_zsmul a _).trans
      (congrArg (fun t : level P (op ⦋p⦌) => a • t) hx)

local instance fundLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance fundLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance fundOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance

private theorem bottom_read (p : ℕ) (w : Chains V) :
    relativeRead (simplicialCone X) (literalConeBottomSubcomplex X) p (vertices some w)=0 := by
  classical
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add _ _ ha hb => simp [ha,hb]
  | single xs k =>
    have h (xs : List V) : relativeRead (simplicialCone X) (literalConeBottomSubcomplex X) p (vertices some (gen xs))=0 := by
      rw [vertices_gen]
      simp only [relativeRead,gen,Finsupp.linearCombination_single,one_smul]
      split <;> rename_i h
      · unfold relativeString
        split <;> rename_i a
        · apply symbol_boundary
          apply exists_orderedConeBottom_of_apex_not_mem
          intro hn
          obtain ⟨i,hi⟩ := (mem_orderedSimplexSupport _ _).mp hn
          change (xs.map some).get _=none at hi
          simp [List.get_eq_getElem] at hi
        · rfl
      · rfl
    have eq : Finsupp.single xs k=k • gen xs := by simp [gen]
    rw [eq,map_smul,map_smul,h,smul_zero]

def alternatingConeCycle (d : ℕ) (coeff : Simplex X d → ℤ) :=
  relativeRead (simplicialCone X) (literalConeBottomSubcomplex X) (d+1) (orientedCone X d coeff)

theorem alternatingConeCycle_closed (d : ℕ) (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    (AlternatingFaceMapComplex.obj (relFree (literalConeBottomSubcomplex X))).d (d+1) d (alternatingConeCycle X d coeff)=0 := by
  rw [alternatingConeCycle,orientedCone,relativeRead_boundary (simplicialCone X) (literalConeBottomSubcomplex X) d (cone_spatial X d coeff)]
  simp only [boundary_cons,boundary_vertices,hz,map_zero,sub_zero,bottom_read]

end GeneralSphereT.Transport.Prism

