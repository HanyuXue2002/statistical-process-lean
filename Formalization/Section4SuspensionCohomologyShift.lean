import Formalization.Section4DoubleConeCohomologyShift

set_option linter.style.header false

/-!
# Section 4: reduced cohomology of the ordinary ordered suspension

The ordinary ordered suspension used in the paper is the double-cone
boundary `doubleConeBoundary M`.  The preceding relative calculation gives

`H^{n+2}(C_w C_v M, doubleConeBoundary M; G) = 0`.

Since the ambient double cone is itself a cone, the elementary cochain
argument below turns this into

`H̃^{n+1}(doubleConeBoundary M; G) = 0`.

Everything is stated as the same explicit `range = ker` identities used by
the rest of the formalization.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) suspensionShiftOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) suspensionShiftOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) suspensionShiftOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

local instance (priority := 10001) suspensionShiftOptionOptionLE :
    LE (Option (Option V)) :=
  @WithBot.instLE (Option V) inferInstance

local instance (priority := 10001) suspensionShiftOptionOptionLT :
    LT (Option (Option V)) :=
  @WithBot.instLT (Option V) inferInstance

local instance (priority := 10001) suspensionShiftOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

/-- If the double-cone pair has zero relative cohomology in degree `n+2`,
then its boundary has zero reduced cohomology in degree `n+1`.

The basepoint is irrelevant in this positive degree, so the statement uses
the outer cone vertex `none`. -/
theorem doubleConeBoundary_reducedCohomologyZeroAt_succ_of_relative
    (n : ℕ)
    (hrel : (doubleConeBoundaryInclusion M).RelativeCohomologyZeroAtSucc
      (G := G) (n + 1)) :
    ReducedCohomologyZeroAt (G := G) (doubleConeBoundary M)
      (none : Option (Option V)) (n + 1) := by
  let Y := doubleConeBoundary M
  let Z := simplicialCone (simplicialCone M)
  let F := doubleConeBoundaryInclusion M
  change LinearMap.range (coboundary (G := G) Y n) =
    LinearMap.ker (coboundary (G := G) Y (n + 1))
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact coboundary_coboundary Y n x
  · intro c hc
    rw [LinearMap.mem_ker] at hc
    let cPlus : Cochain Z (n + 1) G := F.extendCochainByZero (n + 1) c
    let gamma : F.RelativeCochain (G := G) (n + 2) :=
      ⟨coboundary Z (n + 1) cPlus, by
        rw [LinearMap.mem_ker]
        have hnat := LinearMap.congr_fun
          (F.pullback_coboundary (G := G) (n + 1)) cPlus
        simp only [LinearMap.comp_apply] at hnat
        rw [hnat, F.pullback_extendCochainByZero, hc]⟩
    have hgammaCycle :
        F.relativeCoboundary (G := G) (n + 2) gamma = 0 := by
      apply Subtype.ext
      exact coboundary_coboundary Z (n + 1) cPlus
    have hgammaKer : gamma ∈ LinearMap.ker
        (F.relativeCoboundary (G := G) (n + 2)) :=
      hgammaCycle
    rw [← hrel] at hgammaKer
    rcases hgammaKer with ⟨a, ha⟩
    have haCoe : coboundary Z (n + 1) a.1 =
        coboundary Z (n + 1) cPlus := by
      simpa [gamma] using congrArg Subtype.val ha
    let cHat : Cochain Z (n + 1) G := cPlus - a.1
    have hcHatCycle : coboundary Z (n + 1) cHat = 0 := by
      dsimp [cHat]
      rw [map_sub, haCoe, sub_self]
    have hcHatRestriction : F.pullback (n + 1) cHat = c := by
      dsimp [cHat]
      rw [map_sub, F.pullback_extendCochainByZero, a.2, sub_zero]
    let p : Cochain Z n G :=
      simplicialConeCocyclePrimitive (G := G) (simplicialCone M) n cHat
    have hp : coboundary Z n p = cHat :=
      coboundary_simplicialConeCocyclePrimitive
        (G := G) (simplicialCone M) n cHat hcHatCycle
    refine ⟨F.pullback n p, ?_⟩
    have hnat := LinearMap.congr_fun
      (F.pullback_coboundary (G := G) n) p
    simp only [LinearMap.comp_apply] at hnat
    calc
      coboundary Y n (F.pullback n p) =
          F.pullback (n + 1) (coboundary Z n p) := hnat.symm
      _ = F.pullback (n + 1) cHat := by rw [hp]
      _ = c := hcHatRestriction

/-- The suspension shift in the exact form used by Proposition 4.3:
vanishing of `H̃^n(M;G)` implies vanishing of
`H̃^{n+1}(doubleConeBoundary M;G)`. -/
theorem doubleConeBoundary_reducedCohomologyZeroAt_succ_of_reduced
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    ReducedCohomologyZeroAt (G := G) (doubleConeBoundary M)
      (none : Option (Option V)) (n + 1) :=
  doubleConeBoundary_reducedCohomologyZeroAt_succ_of_relative
    (G := G) M n
    (doubleConeBoundaryRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

end GeneralSphereT.SimplicialCochain
