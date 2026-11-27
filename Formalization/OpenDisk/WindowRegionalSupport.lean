import Formalization.OpenDisk.NormalFormTableLocality
import Formalization.SimplicialDegreeZero
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Regional support and independent trace-component translations

This is the local geometric step in the conditional window proof. Regional
support is literal dependence only on the coordinates in `R`. A cut of the
induced facet graph has no edge across it. A closed marked phase supported in
`R` is therefore invariant under an independent constant shift on that cut.
The final lemma extracts the mixed-difference constraint used in step 3.
-/

noncomputable section
open scoped BigOperators

namespace OpenDisk.Window
open GeneralSphereT.PathAlgebra
local instance windowPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι G P Facet : Type*} [LinearOrder ι] [Fintype ι]
  [AddCommGroup G] [AddCommGroup P] [Fintype Facet]

def SupportedOn (R : Set ι) (f : Configuration ι G → P) : Prop :=
  ∀ c c', (∀ i ∈ R, c i = c' i) → f c = f c'

def regionProjection (R : Set ι) : Configuration ι G →+ Configuration ι G :=
  (coordinateExtension R).comp (coordinateRestriction R)

@[simp] theorem regionProjection_apply (R : Set ι) (c : Configuration ι G) (i : ι) :
    regionProjection R c i = if i ∈ R then c i else 0 := by
  classical
  by_cases hi : i ∈ R <;> simp [regionProjection, hi]

/-- A local function that is physically supported in `R` only reads each
facet's intersection with `R`; this is proved by putting other coordinates to zero. -/
theorem local_supported_congr (facets : Facet → Set ι)
    {f : Configuration ι G → P} (hf : AnchoredLocal facets f)
    {R : Set ι} (hR : SupportedOn R f) (c c' : Configuration ι G)
    (heq : ∀ ρ i, i ∈ facets ρ → i ∈ R → c i = c' i) : f c = f c' := by
  classical
  have hp (v : Configuration ι G) : f v = f (regionProjection R v) :=
    hR v _ (fun i hi => by simp [hi])
  obtain ⟨g,hg⟩ := hf.facetSum facets f
  rw [hp c, hp c', hg, hg]
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply congrArg (g ρ)
  ext i
  change regionProjection R c i.val = regionProjection R c' i.val
  by_cases hi : i.val ∈ R
  · simpa [hi] using heq ρ i.val i.property hi
  · simp [hi]

def constantConfiguration (g : G) : Configuration ι G :=
  Finsupp.equivFunOnFinite.symm (fun _ => g)

def regionConstant (A : Set ι) (g : G) : Configuration ι G :=
  regionProjection A (constantConfiguration g)

@[simp] theorem constantConfiguration_apply (g : G) (i : ι) :
    constantConfiguration g i = g := rfl

@[simp] theorem regionConstant_apply (A : Set ι) (g : G) (i : ι) :
    regionConstant A g i = if i ∈ A then g else 0 := by
  simp [regionConstant]

/-- A union of connected components of the graph induced on `R`. -/
def TraceCut (facets : Facet → Set ι) (R A : Set ι) : Prop :=
  A ⊆ R ∧ ∀ ρ i j, i ∈ facets ρ → j ∈ facets ρ → i ∈ R → j ∈ R →
    (i ∈ A ↔ j ∈ A)

def traceGraph (facets : Facet → Set ι) (R : Set ι) : SimpleGraph R where
  Adj i j := i ≠ j ∧ ∃ ρ, i.val ∈ facets ρ ∧ j.val ∈ facets ρ
  symm := ⟨by
    rintro i j ⟨hne,ρ,hi,hj⟩
    exact ⟨hne.symm,ρ,hj,hi⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def traceComponent (facets : Facet → Set ι) (R : Set ι) (i : R) : Set ι :=
  {j | ∃ hj : j ∈ R, (traceGraph facets R).Reachable i ⟨j,hj⟩}

theorem traceComponent_cut (facets : Facet → Set ι) (R : Set ι) (i : R) :
    TraceCut facets R (traceComponent facets R i) := by
  refine ⟨fun j hj => hj.choose, ?_⟩
  intro ρ j k hj hk hjR hkR
  have hreach : (traceGraph facets R).Reachable (⟨j,hjR⟩ : R) ⟨k,hkR⟩ := by
    by_cases heq : j = k
    · subst k; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨fun h => heq (congrArg Subtype.val h),ρ,hj,hk⟩
  constructor
  · rintro ⟨hjr,hr⟩
    exact ⟨hkR,hr.trans hreach⟩
  · rintro ⟨hkr,hr⟩
    exact ⟨hjR,hr.trans hreach.symm⟩

theorem marked_regional_closed_component_invariant (facets : Facet → Set ι)
    {R A : Set ι} (hcut : TraceCut facets R A) {i : ι} (hi : i ∈ R)
    {f : Configuration ι G → P} (hf : MarkedLocal facets {i} f)
    (hR : SupportedOn R f)
    (hclosed : ∀ g c, f (c + constantConfiguration g) = f c)
    (a : G) (c : Configuration ι G) : f (c + regionConstant A a) = f c := by
  classical
  let g : G := if i ∈ A then a else 0
  calc
    f (c + regionConstant A a) = f (c + constantConfiguration g) := by
      apply local_supported_congr (markedFacets facets {i}) hf hR
      intro ρ j hj hjR
      have hiρ : i ∈ facets ρ.val := ρ.property i (Finset.mem_singleton_self _)
      have hh := hcut.2 ρ.val i j hiρ hj hi hjR
      simp only [Finsupp.add_apply, regionConstant_apply, constantConfiguration_apply]
      rw [← hh]
    _ = f c := hclosed g c

/-- If a marked row's carrier is outside a trace component, that row does
not read a shift supported on the component, even before taking closed words. -/
theorem marked_disjoint_component_invariant (facets : Facet → Set ι)
    {R A : Set ι} (hcut : TraceCut facets R A) {i : ι} (hi : i ∈ R) (hiA : i ∉ A)
    {f : Configuration ι G → P} (hf : MarkedLocal facets {i} f)
    (a : G) (c : Configuration ι G) : f (c + regionConstant A a) = f c := by
  classical
  obtain ⟨g,hg⟩ := hf.facetSum (markedFacets facets {i}) f
  rw [hg,hg]
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply congrArg (g ρ)
  ext j
  change c j.val + regionConstant A a j.val = c j.val
  have hjA : j.val ∉ A := by
    intro hjA
    exact hiA ((hcut.2 ρ.val i j.val (ρ.property i (Finset.mem_singleton_self _))
      j.property hi (hcut.1 hjA)).2 hjA)
  simp [hjA]

/-- The literal diagonal comparison in step 3 forces the stated mixed
difference of the remaining boundary phase to vanish. -/
theorem window_comparison_mixed_difference (facets : Facet → Set ι)
    {R A : Set ι} (hcut : TraceCut facets R A) {i : ι} (hi : i ∈ R) (hiA : i ∉ A)
    (L₀ L₁ f : Configuration ι G → P)
    (h₀ : MarkedLocal facets {i} L₀) (h₁ : MarkedLocal facets {i} L₁)
    (s : Configuration ι G)
    (hinv : ∀ a c, (L₁ - L₀ + difference f s) (c + regionConstant A a) =
      (L₁ - L₀ + difference f s) c) (a : G) (c : Configuration ι G) :
    difference (difference f s) (regionConstant A a) c = 0 := by
  have h := hinv a c
  simp only [Pi.add_apply,Pi.sub_apply] at h
  rw [marked_disjoint_component_invariant facets hcut hi hiA h₀ a c,
    marked_disjoint_component_invariant facets hcut hi hiA h₁ a c] at h
  exact sub_eq_zero.mpr (add_left_cancel h)

section Simplicial
open GeneralSphereT.SimplicialCochain

variable {V : Type*} [LinearOrder V] [Fintype V] (K : AbstractSimplicialComplex V)

local instance regionalVertexOrder : LinearOrder (Simplex K 0) := by
  classical exact linearOrderOfSTO WellOrderingRel
local instance regionalFacetFintype : Fintype {s : Finset V // s ∈ K} := Fintype.ofFinite _

/-- In degree zero the independent shifts are literal vertex cochains, and
global constants are closed by the actual ordered simplicial coboundary. -/
theorem simplicial_marked_regional_component_invariant
    {R : Set (Simplex K 0)} {i : Simplex K 0} (hi : i ∈ R)
    {f : Cochain K 0 G → P} (hf : MarkedLocal (facesIn K 0) {i} f)
    (hR : SupportedOn R f) (hclosed : phaseDerivative (coboundaryToRange K 0) f = 0)
    (j : R) (a : G) (c : Cochain K 0 G) :
    f (c + regionConstant (traceComponent (facesIn K 0) R j) a) = f c := by
  apply marked_regional_closed_component_invariant (facesIn K 0)
    (traceComponent_cut _ _ j) hi hf hR
  intro g v
  let z : (coboundaryToRange (G := G) K 0).ker :=
    ⟨constantConfiguration g, Subtype.ext (coboundary_constantCochain K g)⟩
  have hz := congrArg (fun F : SymmetryPhase (coboundaryToRange K 0) P => F z v) hclosed
  exact sub_eq_zero.mp hz

end Simplicial

end OpenDisk.Window
