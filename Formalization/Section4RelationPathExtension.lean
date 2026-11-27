import Formalization.Section4NormalizedPathFibers
import Formalization.Section4FiberwiseExtension

set_option linter.style.header false

/-!
# Section 4: extending normalized relation paths

This file assembles the fiberwise relation section into the path extension
needed in (4.20).  The chosen cochain section on increment labels is only a
function: additivity is neither assumed nor used.  Consequently the final
construction is deliberately elementwise rather than a linear map on paths.

For a normalized path killed by `dA_*`, every nonzero increment fiber is an
element of `ker (mapRedDist dA)`.  We apply the additive `relationSection` to
that fiber, place the result over the chosen lifted increment, and add the
finitely many resulting paths.  Fiber independence proves the new path is
killed by `dZ_*`; restricting both its increment and base labels gives the
original path.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uCA uCZ uBA uBZ

variable {CA : Type uCA} {CZ : Type uCZ}
variable {BA : Type uBA} {BZ : Type uBZ}
variable [AddCommGroup CA] [AddCommGroup CZ]
variable [AddCommGroup BA] [AddCommGroup BZ]

variable {dA : CA →+ BA} {dZ : CZ →+ BZ} {res : CZ →+ CA}

/-! ## The lifted nonzero increment and its relation fiber -/

/-- A zero-preserving set-theoretic section of `res` sends a nonzero
increment to a nonzero increment. -/
def liftedNonzeroIncrement
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (r : NonzeroIncrement CA) : NonzeroIncrement CZ :=
  ⟨j r.1, by
    intro hjr
    have hj_injective : Function.Injective j := by
      intro a b hab
      rw [← hres a, ← hres b, hab]
    exact r.2 (hj_injective (hjr.trans hj0.symm))⟩

@[simp]
theorem res_liftedNonzeroIncrement
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (r : NonzeroIncrement CA) :
    res (liftedNonzeroIncrement (res := res) j hj0 hres r).1 = r.1 :=
  hres r.1

/-- A fiber of a path in `ker dA_*`, bundled as a primitive relation
distribution so that `relationSection` can be applied to it. -/
def normalizedFiberInKernel
    (p : NormalizedPath CA CA) (hp : mapDNormalizedPath dA p = 0)
    (r : NonzeroIncrement CA) : LinearMap.ker (mapRedDist dA) :=
  ⟨normalizedFiber p r, (mapDNormalizedPath_eq_zero_iff dA p).mp hp r⟩

@[simp]
theorem mapDist_relationSection_eq_zero
    (E : FiberwiseCochainLift dA dZ res)
    (u : LinearMap.ker (mapRedDist dA)) :
    mapDist dZ (E.relationSection u).1.1 = 0 := by
  exact congrArg Subtype.val (E.relationSection u).2

@[simp]
theorem mapDist_mapDistFn_lift_eq_zero
    (E : FiberwiseCochainLift dA dZ res)
    (u : LinearMap.ker (mapRedDist dA)) :
    mapDist dZ (mapDistFn E.lift u.1.1) = 0 :=
  mapDist_relationSection_eq_zero E u

@[simp]
theorem mapDist_res_relationSection
    (E : FiberwiseCochainLift dA dZ res)
    (u : LinearMap.ker (mapRedDist dA)) :
    mapDist res (E.relationSection u).1.1 = u.1.1 := by
  exact congrArg Subtype.val (E.mapRedDist_relationSection u)

/-! ## Reassembly -/

/-- The underlying finite sum obtained by extending every nonzero increment
fiber and placing it over the chosen lifted increment `j(r)`. -/
def relationPathExtensionUnderlying
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (p : NormalizedPath CA CA) (hp : mapDNormalizedPath dA p = 0) :
    Path CZ CZ :=
  ∑ r ∈ (pathFibers p.1).support,
    fiberPath (liftedNonzeroIncrement (res := res) j hj0 hres r)
      (E.relationSection (normalizedFiberInKernel p hp r)).1.1

/-- The reassembled path is base-normalized because every extended fiber is a
reduced distribution. -/
theorem baseAug_relationPathExtensionUnderlying_eq_zero
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (p : NormalizedPath CA CA) (hp : mapDNormalizedPath dA p = 0) :
    baseAug (relationPathExtensionUnderlying E j hj0 hres p hp) = 0 := by
  classical
  rw [relationPathExtensionUnderlying, map_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [baseAug_fiberPath, (E.relationSection
    (normalizedFiberInKernel p hp r)).1.2, zero_smul]

/-- The normalized relation-path extension required in (4.20). -/
def relationPathExtension
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (p : NormalizedPath CA CA) (hp : mapDNormalizedPath dA p = 0) :
    NormalizedPath CZ CZ :=
  ⟨relationPathExtensionUnderlying E j hj0 hres p hp,
    baseAug_relationPathExtensionUnderlying_eq_zero E j hj0 hres p hp⟩

/-! ## Exact kernel and restriction statements -/

/-- Applying additive maps to the bases of a single lifted fiber commutes with
reassembly, while restriction sends its increment label back to `r`. -/
theorem mapPath_res_fiberPath_lifted
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (r : NonzeroIncrement CA) (z : Dist CZ) :
    mapPath res res
        (fiberPath (liftedNonzeroIncrement (res := res) j hj0 hres r) z) =
      fiberPath r (mapDist res z) := by
  induction z using Finsupp.induction with
  | zero => simp [fiberPath]
  | single_add x n z hx hz ih =>
      rw [map_add, map_add, ih]
      simp [fiberPath]

/-- The extended normalized path lies in `ker dZ_*`.  This is the fiberwise
kernel half of (4.20). -/
theorem mapD_relationPathExtension_eq_zero
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (p : NormalizedPath CA CA) (hp : mapDNormalizedPath dA p = 0) :
    mapDNormalizedPath dZ (relationPathExtension E j hj0 hres p hp) = 0 := by
  rw [mapDNormalizedPath_eq_zero_iff]
  intro s
  apply Subtype.ext
  classical
  change mapDist dZ
      (pathFibers (relationPathExtensionUnderlying E j hj0 hres p hp) s) = 0
  have hfib :
      pathFibers (relationPathExtensionUnderlying E j hj0 hres p hp) s =
        ∑ r ∈ (pathFibers p.1).support,
          (Finsupp.single
            (liftedNonzeroIncrement (res := res) j hj0 hres r)
            (E.relationSection (normalizedFiberInKernel p hp r)).1.1) s := by
    rw [relationPathExtensionUnderlying, map_sum]
    simp only [pathFibers_fiberPath, Finsupp.finsetSum_apply]
  rw [hfib, map_sum]
  refine Finset.sum_eq_zero (fun r hr => ?_)
  by_cases hrs : liftedNonzeroIncrement (res := res) j hj0 hres r = s
  · simp only [Finsupp.single_apply, hrs]
    exact mapDist_relationSection_eq_zero E _
  · simp [hrs]

/-- Restricting both the increment and base labels of the extension recovers
the original path exactly. -/
theorem mapPath_res_res_relationPathExtension
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (p : NormalizedPath CA CA) (hp : mapDNormalizedPath dA p = 0) :
    mapPath res res (relationPathExtension E j hj0 hres p hp).1 = p.1 := by
  classical
  change mapPath res res
      (relationPathExtensionUnderlying E j hj0 hres p hp) = p.1
  rw [relationPathExtensionUnderlying, map_sum]
  simp_rw [mapPath_res_fiberPath_lifted j hj0 hres]
  simp_rw [mapDist_res_relationSection]
  change (∑ r ∈ (pathFibers p.1).support,
      fiberPath r (pathFibers p.1 r)) = p.1
  calc
    (∑ r ∈ (pathFibers p.1).support,
        fiberPath r (pathFibers p.1 r)) =
        fibersToPath (pathFibers p.1) := by
      rw [fibersToPath, Finsupp.lsum_apply]
      rfl
    _ = p.1 := fibersToPath_pathFibers p.1

/-- Elementwise form of the normalized relation-path extension theorem. -/
theorem exists_normalized_relationPathExtension
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (p : NormalizedPath CA CA) (hp : mapDNormalizedPath dA p = 0) :
    ∃ q : NormalizedPath CZ CZ,
      mapDNormalizedPath dZ q = 0 ∧ mapPath res res q.1 = p.1 :=
  ⟨relationPathExtension E j hj0 hres p hp,
    mapD_relationPathExtension_eq_zero E j hj0 hres p hp,
    mapPath_res_res_relationPathExtension E j hj0 hres p hp⟩

end GeneralSphereT.PathAlgebra
