import Formalization.Transport.AffineField
import Formalization.Transport.PrismCochains

/-! The signed triangle integral of (2.8), with values in the actual
Dold--Kan Eilenberg--Mac Lane space, evaluated before quotienting primitive
configurations by closed shifts. -/
noncomputable section
open scoped BigOperators
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality GeneralSphereT.SimplicialCochain GeneralSphereT.StandardModels

variable {G : Type} [AddCommGroup G] {Y : Type*}
abbrev EM (G : Type) [AddCommGroup G] (q p : ℕ) := (K (AddCommGrpCat.of G) q).obj (op ⦋p⦌)

/-- The ordinary alternating face cocycle condition on the actual simplices of K. -/
def ClosedOnEM {q p : ℕ} (ω : EM G q p → Phase) : Prop :=
  ∀ x : EM G q (p+1), ∑ j : Fin (p+2), ((-1:ℤ)^j.val) • ω ((K (AddCommGrpCat.of G) q).δ j x) = 0

def pullCochain {q p : ℕ} (field : (Fin (q+1) → Y) → G) (ω : EM G (q+1) p → Phase) :
    Chains Y →ₗ[ℤ] Phase :=
  evaluate (homogeneous fun x : Fin (p+1) → Y => ω (classifyingValue field x))

theorem pullCochain_closed {q p : ℕ} (field : (Fin (q+1) → Y) → G) (ω : EM G (q+1) p → Phase)
    (hω : ClosedOnEM ω) : (pullCochain field ω).comp boundary = 0 := by
  apply homogeneous_closed
  intro x
  have e := hω (classifyingValue field x)
  convert e using 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => ((-1:ℤ)^j.val) • ω z)
    (classifyingValue_face field x (Fin.succAboveOrderEmb j)).symm

variable {V : Type*} [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q d : ℕ)

def orientedFacets (coeff : Simplex X d → ℤ) : Chains V := by
  classical
  letI : Fintype (Simplex X d) := Fintype.ofFinite _
  exact ∑ σ, coeff σ • gen (List.ofFn (fun i => σ.val.orderEmbOfFin σ.property.2 i))

private def layer (v : Cochain X q G) (x : V) := (v,x)

def affineMultiplier (ω : EM G (q+1) (d+2) → Phase) (z : Chains V) (t s v : Cochain X q G) : Phase :=
  -pullCochain (affineField X q) ω (triangle (layer X q v) (layer X q (v+s)) (layer X q (v+s+t)) z)

/-- Associativity of the actual triangle-prism formula on primitive states,
in arbitrary spatial and cochain degrees. -/
theorem affineMultiplier_assoc (ω : EM G (q+1) (d+2) → Phase) (hω : ClosedOnEM ω)
    (z : Chains V) (hz : boundary z=0) (r t s v : Cochain X q G) :
    affineMultiplier X q d ω z t s v + affineMultiplier X q d ω z r (s+t) v =
      affineMultiplier X q d ω z r t (v+s) + affineMultiplier X q d ω z (t+r) s v := by
  let χ := pullCochain (affineField X q) ω
  have E := temporal_cocycle χ (pullCochain_closed _ _ hω) z hz
    (layer X q v) (layer X q (v+s)) (layer X q (v+s+t)) (layer X q (v+s+t+r))
  simp only [affineMultiplier,← add_assoc]
  change _ = _ at E
  simpa only [χ,← neg_add] using congrArg Neg.neg E

end GeneralSphereT.Transport.Prism

