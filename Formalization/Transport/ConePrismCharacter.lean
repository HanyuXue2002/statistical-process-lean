import Formalization.Transport.PrismMultiplier
import Formalization.Transport.SphereComparison

/-! The representative of the primitive character computed from the actual
triangle integral. On primitives it is the segment from zero on the spatial cone. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra OpenDisk.PhaseDuality
open OrderedSimplicialMap FacetRestrictionData
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
local instance coneCharLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance coneCharLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance coneCharOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (q d : ℕ)

/-- A simultaneous choice of cone extensions equivariant under closed shifts. -/
structure ConeLifts where
  lift : Cochain X q G → Cochain (simplicialCone X) q G
  bottom : ∀ v, (coneBottomInclusion X).pullback q (lift v)=v
  zero : lift 0=0
  shift : ∀ z : LinearMap.ker (coboundary (G:=G) X q),
    ∃ Z : LinearMap.ker (coboundary (G:=G) (simplicialCone X) q), ∀ v, lift (v+z.val)=lift v+Z.val

def coneEdge (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ)
    (u w : Cochain (simplicialCone X) q G) : Phase :=
  pullCochain (affineField (simplicialCone X) q) ω
    (segment (layerOf _ q u) (layerOf _ q w) (cons none (vertices some (orientedFacets X d coeff))))

def conePrimitive (E : ConeLifts (G:=G) X q) (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ)
    (s : Cochain X q G) (a : State (G:=G) X q) : Phase :=
  let v := liftState X q a
  coneEdge X q d ω coeff (E.lift v) (E.lift (v+s))

theorem conePrimitive_on_primitive (E : ConeLifts (G:=G) X q) (ω : EM G (q+1) (d+2) → Phase)
    (coeff : Simplex X d → ℤ) (s v : Cochain X q G) :
    conePrimitive X q d E ω coeff s (coboundaryToRange X q v)=coneEdge X q d ω coeff (E.lift v) (E.lift (v+s)) := by
  let u := liftState X q (coboundaryToRange X q v)
  have hu : coboundary X q u=coboundary X q v := liftState_spec X q _
  let z : LinearMap.ker (coboundary (G:=G) X q) := ⟨u-v,by rw [LinearMap.mem_ker,map_sub,hu,sub_self]⟩
  obtain ⟨Z,hZ⟩ := E.shift z
  have e₀ : E.lift u=E.lift v+Z.val := (show v+z.val=u by dsimp [z]; abel) ▸ hZ v
  have e₁ : E.lift (u+s)=E.lift (v+s)+Z.val := (show v+s+z.val=u+s by dsimp [z]; abel) ▸ hZ (v+s)
  change coneEdge X q d ω coeff (E.lift u) (E.lift (u+s))=_
  rw [e₀,e₁]
  exact closedShift_segment (simplicialCone X) q ω _ _ Z.val Z.property (cone_spatial X d coeff)

theorem conePrimitive_curvature (E : ConeLifts (G:=G) X q) (ω : EM G (q+1) (d+2) → Phase) (hc : ClosedOnEM ω)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (t s : Cochain X q G) (a : State (G:=G) X q) :
    physicalPrism X q d ω coeff t s a = conePrimitive X q d E ω coeff s a +
      conePrimitive X q d E ω coeff t (a+coboundaryToRange X q s) - conePrimitive X q d E ω coeff (s+t) a := by
  obtain ⟨v,rfl⟩ := facetCoboundary_surjective X q a
  rw [← map_add,physicalPrism_on_primitive]
  simp only [conePrimitive_on_primitive,← add_assoc]
  let f := layerOf (simplicialCone X) q (G:=G)
  let U := E.lift v
  let W := E.lift (v+s)
  let T := E.lift (v+s+t)
  let z := orientedFacets X d coeff
  have e := LinearMap.congr_fun (pullCochain_closed (affineField (simplicialCone X) q) ω hc)
    (triangle (f U) (f W) (f T) (cons none (vertices some z)))
  change pullCochain _ ω (boundary _) = 0 at e
  rw [boundary_triangle,boundary_cons,boundary_vertices,show boundary z=0 from hz,map_zero,map_zero,sub_zero,
    map_add,map_add,map_sub,read_bottom_triangle] at e
  change _ + pullCochain (affineField X q) ω
    (triangle (layerOf X q ((coneBottomInclusion X).pullback q (E.lift v)))
      (layerOf X q ((coneBottomInclusion X).pullback q (E.lift (v+s))))
      (layerOf X q ((coneBottomInclusion X).pullback q (E.lift (v+s+t)))) z)=0 at e
  simp only [E.bottom] at e
  change -(pullCochain (affineField X q) ω (triangle (layerOf X q v) (layerOf X q (v+s)) (layerOf X q (v+s+t)) z))=coneEdge X q d ω coeff U W + coneEdge X q d ω coeff W T - coneEdge X q d ω coeff U T
  change coneEdge X q d ω coeff W T - coneEdge X q d ω coeff U T + coneEdge X q d ω coeff U W + _ = 0 at e
  linear_combination (norm := abel) -e

local instance coneCharFacets : Fintype (Simplex X d) := Fintype.ofFinite _
local instance coneCharSimplexOrder (k : ℕ) : LinearOrder (Simplex X k) := uniformSimplexColexOrder X k

/-- The comparison with T' reads a single cone segment for each primitive. -/
theorem character_on_cone (E : ConeLifts (G:=G) X q) (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (ω : EM G (q+1) (d+2) → Phase) (hc : ClosedOnEM ω) (hn : NormalizedOnEM ω)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    let L := topFacetData (G:=G) X d q
    let m := physicalPrismMultiplier X q d b hred ω hc hn coeff hz
    ∃ χ : TPrime L →ₗ[ℤ] Phase, Represents L m χ ∧ ∀ z : Zprim L,
      χ ((BprimInZprim L).mkQ z)=evaluate (fun v => coneEdge X q d ω coeff 0 (E.lift v)) z.val.val := by
  let L := topFacetData (G:=G) X d q
  let m := physicalPrismMultiplier X q d b hred ω hc hn coeff hz
  let h := conePrimitive X q d E ω coeff
  have hh : ∀ t s a, m.value (t,s,a)=h s a+h t (a+coboundaryToRange X q s)-h (s+t) a :=
    conePrimitive_curvature X q d E ω hc coeff hz
  let χ := restrictCharacter (Bprim L) (Zprim L) ⟨_,primitive_annihilates L m h hh⟩
  have hr : Represents L m χ := ⟨h,funext (fun ⟨t,s,a⟩ => hh t s a),fun _ => rfl⟩
  refine ⟨χ,hr,fun z => ?_⟩
  change evaluate (fun v => conePrimitive X q d E ω coeff v 0) z.val.val=_
  apply congrArg (fun φ : Cochain X q G → Phase => evaluate φ z.val.val)
  funext v
  simpa only [map_zero,zero_add,E.zero] using conePrimitive_on_primitive X q d E ω coeff v 0

end GeneralSphereT.Transport.Prism
