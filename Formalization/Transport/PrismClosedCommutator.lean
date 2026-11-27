import Formalization.Transport.PhysicalPrism

/-! A bounding spatial chain and closed extensions of the two moves kill
the closed hopping commutator, by the triangle product boundary formula. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality GeneralSphereT.SimplicialCochain
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q : ℕ)

def spatialChains : Submodule ℤ (Chains V) :=
  Submodule.span ℤ {p | ∃ (xs : List V) (σ : NonemptySimplex X), xs.Pairwise (· ≤ ·) ∧
    (∀ x ∈ xs, x ∈ σ.val) ∧ p=gen xs}

def layerOf (u : Cochain X q G) (x : V) := (u,x)

theorem closedShift_segment {p : ℕ} (ω : EM G (q+1) p → Phase) (u v z : Cochain X q G)
    (hz : coboundary X q z=0) {w : Chains V} (hw : w ∈ spatialChains X) :
    let χ := pullCochain (affineField X q) ω
    χ (segment (layerOf X q (u+z)) (layerOf X q (v+z)) w) = χ (segment (layerOf X q u) (layerOf X q v) w) := by
  let χ := pullCochain (affineField X q) ω
  let shift := fun y : Cochain X q G × V => (y.1+z,y.2)
  dsimp only
  induction hw using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs,σ,hxs,hm,rfl⟩ := ha
    have e := equal_on_walks (π:=Prod.snd) (χ.comp (vertices shift)) χ (weight_shift_on X q ω z hz σ xs hxs hm)
      (segment_walk (a:=layerOf X q u) (b:=layerOf X q v) (fun _ => rfl) (fun _ => rfl) xs)
    rw [LinearMap.comp_apply,vertices_segment] at e
    change χ (segment (layerOf X q (u+z)) (layerOf X q (v+z)) (gen xs)) =
      χ (segment (layerOf X q u) (layerOf X q v) (gen xs))
    simp only [segment,extend_gen]
    exact e
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul n a _ ha => simp only [map_smul,ha]

theorem closed_commutator_on_boundary {p : ℕ} (ω : EM G (q+1) p → Phase) (hc : ClosedOnEM ω)
    (v s t : Cochain X q G) (hs : coboundary X q s=0) (ht : coboundary X q t=0)
    {w : Chains V} (hw : w ∈ spatialChains X) :
    let χ := pullCochain (affineField X q) ω
    let f := layerOf X q (G:=G)
    χ (triangle (f v) (f (v+s)) (f (v+s+t)) (boundary w)) =
      χ (triangle (f v) (f (v+t)) (f (v+t+s)) (boundary w)) := by
  let χ := pullCochain (affineField X q) ω
  let f := layerOf X q (G:=G)
  have e₁ := LinearMap.congr_fun (pullCochain_closed (affineField X q) ω hc)
    (triangle (f v) (f (v+s)) (f (v+s+t)) w)
  have e₂ := LinearMap.congr_fun (pullCochain_closed (affineField X q) ω hc)
    (triangle (f v) (f (v+t)) (f (v+t+s)) w)
  have e₃ := closedShift_segment X q ω v (v+t) s hs hw
  have e₄ := closedShift_segment X q ω v (v+s) t ht hw
  change χ (segment (f (v+s)) (f (v+t+s)) w) = χ (segment (f v) (f (v+t)) w) at e₃
  change χ (segment (f (v+t)) (f (v+s+t)) w) = χ (segment (f v) (f (v+s)) w) at e₄
  have comm : v+t+s = v+s+t := by abel
  change χ (boundary _) = 0 at e₁ e₂
  simp only [boundary_triangle,map_add,map_sub,comm] at e₁ e₂
  rw [comm] at e₃
  change χ _ = χ _
  rw [comm]
  linear_combination (norm := abel) e₁-e₂-e₃+e₄

end GeneralSphereT.Transport.Prism

