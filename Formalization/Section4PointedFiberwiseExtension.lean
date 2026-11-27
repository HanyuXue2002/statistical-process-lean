import Formalization.Section4FiberwiseExtension

set_option linter.style.header false

/-!
# Section 4: local conditions preserved by a fiberwise relation lift

For the pointed cone criterion, a relation based at `b` must be extended to a
relation which vanishes on the entire cone edge `C_v{b}`.  The free-group
calculation is again formal: it is enough that local restriction of the
chosen cochain lift factors, as a function, through local restriction at the
source basepoint.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uCA uCZ uBA uBZ uLA uLZ

variable {CA : Type uCA} {CZ : Type uCZ}
variable {BA : Type uBA} {BZ : Type uBZ}
variable {LA : Type uLA} {LZ : Type uLZ}
variable [AddCommGroup CA] [AddCommGroup CZ]
variable [AddCommGroup BA] [AddCommGroup BZ]
variable [AddCommGroup LA] [AddCommGroup LZ]

variable {dA : CA →+ BA} {dZ : CZ →+ BZ} {res : CZ →+ CA}

/-- If target local restriction of the selected cochain lift depends only on
source local restriction, then the induced relation section carries locally
zero primitive relations to locally zero primitive relations.  The local
factor `localLift` is only a function. -/
theorem FiberwiseCochainLift.mapRedDist_relationSection_local_eq_zero
    (E : FiberwiseCochainLift dA dZ res)
    (sourceLocal : CA →+ LA) (targetLocal : CZ →+ LZ)
    (localLift : LA → LZ)
    (local_compat : ∀ c, targetLocal (E.lift c) = localLift (sourceLocal c))
    (u : LinearMap.ker (mapRedDist dA))
    (hu : mapRedDist sourceLocal u.1 = 0) :
    mapRedDist targetLocal (E.relationSection u).1 = 0 := by
  rw [mapRedDist_eq_mapRedDistFn]
  rw [E.relationSection_coe]
  calc
    mapRedDistFn targetLocal (mapRedDistFn E.lift u.1) =
        mapRedDistFn (targetLocal ∘ E.lift) u.1 :=
      mapRedDistFn_comp_apply E.lift targetLocal u.1
    _ = mapRedDistFn (localLift ∘ sourceLocal) u.1 := by
      have hfun : (targetLocal : CZ → LZ) ∘ E.lift =
          localLift ∘ (sourceLocal : CA → LA) := by
        funext c
        exact local_compat c
      rw [hfun]
    _ = mapRedDistFn localLift (mapRedDistFn sourceLocal u.1) :=
      (mapRedDistFn_comp_apply sourceLocal localLift u.1).symm
    _ = mapRedDistFn localLift 0 := by
      have hu' : mapRedDistFn sourceLocal u.1 = 0 := by
        simpa only [← mapRedDist_eq_mapRedDistFn] using hu
      rw [hu']
    _ = 0 := by simp

end GeneralSphereT.PathAlgebra
