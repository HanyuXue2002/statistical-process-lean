import Formalization.RelativeDistributionLift

set_option linter.style.header false

/-!
# Section 4: fiberwise extension of primitive relations

The algebra in Lemma 4.2 is independent of cones and cohomology.  What the
relative-cohomology argument supplies is a set-theoretic lift of each cochain
whose coboundary depends only on the original coboundary.  Applying the free
augmentation-zero group functor to such a lift gives an additive section on
primitive relation distributions.

This file isolates and proves exactly that assertion.  The later topological
input only has to construct `FiberwiseCochainLift`; it does not have to repeat
any free-group calculation.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uCA uCZ uBA uBZ

variable {CA : Type uCA} {CZ : Type uCZ}
variable {BA : Type uBA} {BZ : Type uBZ}
variable [AddCommGroup CA] [AddCommGroup CZ]
variable [AddCommGroup BA] [AddCommGroup BZ]

/-- Data furnished by the relative cochain extension argument.

`lift` need not be additive.  Its restriction is the original cochain, and
its global coboundary is a chosen function only of the old coboundary.  This
is precisely the fiberwise condition used in (4.8)--(4.9). -/
structure FiberwiseCochainLift
    (dA : CA →+ BA) (dZ : CZ →+ BZ) (res : CZ →+ CA) where
  lift : CA → CZ
  physicalLift : BA → BZ
  res_lift : ∀ c, res (lift c) = c
  d_lift : ∀ c, dZ (lift c) = physicalLift (dA c)

namespace FiberwiseCochainLift

variable {dA : CA →+ BA} {dZ : CZ →+ BZ} {res : CZ →+ CA}
variable (E : FiberwiseCochainLift dA dZ res)

/-- The free reduced-distribution lift sends primitive relations to primitive
relations, although the chosen cochain lift itself need not be additive. -/
theorem mapRedDistFn_lift_mem_ker
    (u : LinearMap.ker (mapRedDist dA)) :
    mapRedDistFn E.lift u.1 ∈ LinearMap.ker (mapRedDist dZ) := by
  rw [LinearMap.mem_ker]
  rw [mapRedDist_eq_mapRedDistFn]
  calc
    mapRedDistFn dZ (mapRedDistFn E.lift u.1) =
        mapRedDistFn (dZ ∘ E.lift) u.1 :=
      mapRedDistFn_comp_apply E.lift dZ u.1
    _ = mapRedDistFn (E.physicalLift ∘ dA) u.1 := by
      have hfun : (dZ : CZ → BZ) ∘ E.lift =
          E.physicalLift ∘ (dA : CA → BA) := by
        funext c
        exact E.d_lift c
      rw [hfun]
    _ = mapRedDistFn E.physicalLift (mapRedDistFn dA u.1) :=
      (mapRedDistFn_comp_apply dA E.physicalLift u.1).symm
    _ = mapRedDistFn E.physicalLift 0 := by
      have hdu : mapRedDistFn dA u.1 = 0 := by
        rw [← mapRedDist_eq_mapRedDistFn]
        exact u.2
      rw [hdu]
    _ = 0 := by simp

/-- The additive section on primitive relation distributions. -/
def relationSection :
    LinearMap.ker (mapRedDist dA) →ₗ[ℤ]
      LinearMap.ker (mapRedDist dZ) :=
  LinearMap.codRestrict (LinearMap.ker (mapRedDist dZ))
    ((mapRedDistFn E.lift).comp
      (LinearMap.ker (mapRedDist dA)).subtype)
    (mapRedDistFn_lift_mem_ker E)

@[simp]
theorem relationSection_coe
    (u : LinearMap.ker (mapRedDist dA)) :
    ((E.relationSection u : LinearMap.ker (mapRedDist dZ)) : RedDist CZ) =
      mapRedDistFn E.lift u.1 :=
  rfl

/-- Restricting the fiberwise relation section gives the original relation.
This is the group-homomorphic section asserted in Lemma 4.2. -/
@[simp]
theorem mapRedDist_relationSection
    (u : LinearMap.ker (mapRedDist dA)) :
    mapRedDist res (E.relationSection u).1 = u.1 := by
  rw [mapRedDist_eq_mapRedDistFn]
  calc
    mapRedDistFn res (mapRedDistFn E.lift u.1) =
        mapRedDistFn (res ∘ E.lift) u.1 :=
      mapRedDistFn_comp_apply E.lift res u.1
    _ = mapRedDistFn id u.1 := by
      have hfun : (res : CZ → CA) ∘ E.lift = id := by
        funext c
        exact E.res_lift c
      rw [hfun]
    _ = u.1 := by
      have hid : mapDistFn (id : CA → CA) = LinearMap.id := by
        ext c
        simp
      apply Subtype.ext
      exact LinearMap.congr_fun hid u.1.1

/-- Translate a fibrewise lift by its value at zero.  This harmless
normalization makes the chosen cochain lift literally zero-preserving, which
is needed when the lift is applied to increment labels of normalized paths. -/
def zeroNormalized : FiberwiseCochainLift dA dZ res where
  lift c := E.lift c - E.lift 0
  physicalLift b := E.physicalLift b - E.physicalLift 0
  res_lift c := by
    rw [map_sub, E.res_lift, E.res_lift]
    simp
  d_lift c := by
    rw [map_sub, E.d_lift, E.d_lift]
    simp

@[simp]
theorem zeroNormalized_lift_zero : E.zeroNormalized.lift 0 = 0 := by
  exact sub_self _

@[simp]
theorem zeroNormalized_res_lift (c : CA) :
    res (E.zeroNormalized.lift c) = c :=
  E.zeroNormalized.res_lift c

end FiberwiseCochainLift

end GeneralSphereT.PathAlgebra
