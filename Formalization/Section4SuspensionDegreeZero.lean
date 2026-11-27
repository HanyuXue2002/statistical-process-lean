import Formalization.Section4NativeTransgressionDegreeZero
import Formalization.Section4SuspensionCohomologyShift

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the degree-zero suspension shift

For the low endpoint `q = 1`, the degree-zero comparison on the suspension
needs `H~⁰(ΣM;G) = 0`.  This does not require a cohomology hypothesis on
`M`: the two literal cones make the suspension connected as soon as a
vertex `b : V` is available.  The proof evaluates a zero-cocycle first on
the outer-apex--vertex edges and then on the inner-apex--`b` edge.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

local instance (priority := 10000) suspensionZeroOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) suspensionZeroOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) suspensionZeroOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

local instance (priority := 10001) suspensionZeroOptionOptionLE :
    LE (Option (Option V)) :=
  @WithBot.instLE (Option V) inferInstance

local instance (priority := 10001) suspensionZeroOptionOptionLT :
    LT (Option (Option V)) :=
  @WithBot.instLT (Option V) inferInstance

local instance (priority := 10001) suspensionZeroOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

/-- A nonempty ordered suspension has vanishing reduced degree-zero
cohomology.  The parameter `b` supplies the one vertex needed to connect
the inner apex to the equator. -/
theorem doubleConeBoundary_reducedCohomologyZeroAt_zero
    (M : AbstractSimplicialComplex V) (b : V) :
    ReducedCohomologyZeroAt (G := G) (doubleConeBoundary M)
      (none : Option (Option V)) 0 := by
  change LinearMap.ker
      (basedZeroCoboundary (G := G) (doubleConeBoundary M)
        (none : Option (Option V))) = ⊥
  apply le_antisymm
  · intro c hc
    rw [Submodule.mem_bot]
    have hcycle : coboundary (doubleConeBoundary M) 0 c.1 = 0 :=
      LinearMap.mem_ker.mp hc
    have houterApex :
        c.1 (basepointSimplex (doubleConeBoundary M)
          (none : Option (Option V))) = 0 := by
      exact c.2
    let Jother := doubleConeOtherBoundaryInclusion M
    let cOther : Cochain (simplicialCone M) 0 G :=
      Jother.pullback 0 c.1
    have hcOtherCycle : coboundary (simplicialCone M) 0 cOther = 0 := by
      have hnat := LinearMap.congr_fun
        (Jother.pullback_coboundary (G := G) 0) c.1
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hcycle, map_zero]
    have hcOtherApex :
        cOther (basepointSimplex (simplicialCone M) none) = 0 := by
      change c.1 (basepointSimplex (doubleConeBoundary M)
        (none : Option (Option V))) = 0
      exact houterApex
    have hcOtherZero : cOther = 0 :=
      cone_zeroCochain_eq_zero_of_cocycle_of_apex
        M cOther hcOtherCycle hcOtherApex
    let Jinner := doubleConeInnerBoundaryInclusion M
    let cInner : Cochain (simplicialCone M) 0 G :=
      Jinner.pullback 0 c.1
    have hcInnerCycle : coboundary (simplicialCone M) 0 cInner = 0 := by
      have hnat := LinearMap.congr_fun
        (Jinner.pullback_coboundary (G := G) 0) c.1
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hcycle, map_zero]
    have hcInnerBottom :
        cInner ((coneBottomInclusion M).mapSimplex
          (basepointSimplex M b)) = 0 := by
      have hv := congrArg
        (fun z : Cochain (simplicialCone M) 0 G ↦
          z ((coneBottomInclusion M).mapSimplex
            (basepointSimplex M b))) hcOtherZero
      change c.1 (basepointSimplex (doubleConeBoundary M)
          (some (some b))) = 0 at hv
      change c.1 (basepointSimplex (doubleConeBoundary M)
        (some (some b))) = 0
      exact hv
    let P := pointedConePairInclusion M b
    let cPair : Cochain (pointedConePair M b) 0 G :=
      P.pullback 0 cInner
    have hcPairCycle : coboundary (pointedConePair M b) 0 cPair = 0 := by
      have hnat := LinearMap.congr_fun
        (P.pullback_coboundary (G := G) 0) cInner
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hcInnerCycle, map_zero]
    have hedge := congrArg
      (fun z : Cochain (pointedConePair M b) 1 G ↦
        z (pointedConePairEdgeSimplex M b)) hcPairCycle
    rw [coboundary_pointedConePair_edge_apply] at hedge
    have hpairBottom :
        cPair ((pointedConePairBottomInclusion M b).mapSimplex
          (basepointSimplex M b)) = 0 := by
      exact hcInnerBottom
    have hcInnerApex :
        cInner (basepointSimplex (simplicialCone M) none) = 0 := by
      have hpairApex :
          cPair (basepointSimplex (pointedConePair M b) none) =
            cInner (basepointSimplex (simplicialCone M) none) := by
        rfl
      rw [hpairBottom, hpairApex, zero_sub] at hedge
      exact neg_eq_zero.mp hedge
    apply Subtype.ext
    ext sigma
    have hcard : sigma.1.card = 1 := by simpa using sigma.2.2
    obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hcard
    have hsigma : sigma = basepointSimplex (doubleConeBoundary M) o := by
      apply Subtype.ext
      simpa [basepointSimplex] using ho
    rw [hsigma]
    cases o with
    | none => exact houterApex
    | some o =>
        cases o with
        | none =>
            change cInner (basepointSimplex (simplicialCone M) none) = 0
            exact hcInnerApex
        | some v =>
            have hv := congrArg
              (fun z : Cochain (simplicialCone M) 0 G ↦
                z ((coneBottomInclusion M).mapSimplex
                  (basepointSimplex M v))) hcOtherZero
            change c.1 (basepointSimplex (doubleConeBoundary M)
                (some (some v))) = 0 at hv
            exact hv
  · exact bot_le

end GeneralSphereT.SimplicialCochain
