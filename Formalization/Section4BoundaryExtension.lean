import Formalization.Section4RelationPathExtension
import Formalization.PrimitiveQuotientFunctoriality

set_option linter.style.header false

/-!
# Section 4: extending denominator boundaries

The preceding module extends an individual normalized path killed by `dA_*`.
Here we bundle that construction on the actual kernel subtype used by the
denominator and record what happens to its primitive boundary.

The decisive identity is not a new boundary calculation.  Naturality of
`reducedBoundary` says that restricting the boundary of the extended path is
the boundary of its restriction.  Since the latter restriction is the
original relation path, the new boundary is a primitive-relation extension of
the old one.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uCA uCZ uBA uBZ

variable {CA : Type uCA} {CZ : Type uCZ}
variable {BA : Type uBA} {BZ : Type uBZ}
variable [AddCommGroup CA] [AddCommGroup CZ]
variable [AddCommGroup BA] [AddCommGroup BZ]

variable {dA : CA →+ BA} {dZ : CZ →+ BZ} {res : CZ →+ CA}

/-! ## Relation paths and their primitive boundaries -/

/-- The chosen extension of a relation path, bundled in the target kernel. -/
def extendedRelationPath
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA)) :
    LinearMap.ker (mapDNormalizedPath dZ) :=
  ⟨relationPathExtension E j hj0 hres R.1 R.2,
    mapD_relationPathExtension_eq_zero E j hj0 hres R.1 R.2⟩

@[simp]
theorem extendedRelationPath_coe
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA)) :
    (extendedRelationPath E j hj0 hres R).1 =
      relationPathExtension E j hj0 hres R.1 R.2 :=
  rfl

/-- The target relation path is killed by `dZ_*`. -/
theorem extendedRelationPath_mapD_eq_zero
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA)) :
    mapDNormalizedPath dZ (extendedRelationPath E j hj0 hres R).1 = 0 :=
  (extendedRelationPath E j hj0 hres R).2

/-- Restricting both labels of the target relation path gives the source
relation path exactly. -/
theorem mapPath_res_res_extendedRelationPath
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA)) :
    mapPath res res (extendedRelationPath E j hj0 hres R).1.1 = R.1.1 :=
  mapPath_res_res_relationPathExtension E j hj0 hres R.1 R.2

/-- The primitive boundary of any normalized relation path is itself a
primitive relation distribution. -/
def primitiveBoundaryOfRelationPath
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (R : LinearMap.ker (mapDNormalizedPath d)) :
    LinearMap.ker (mapRedDist d) :=
  ⟨primitiveReducedBoundary C R.1.1, by
    rw [LinearMap.mem_ker]
    have hpath : mapDPath d R.1.1 = 0 := congrArg Subtype.val R.2
    calc
      mapRedDist d (primitiveReducedBoundary C R.1.1) =
          configurationReducedBoundary d (mapDPath d R.1.1) :=
        LinearMap.congr_fun (mapRedDist_primitiveReducedBoundary d) R.1.1
      _ = 0 := by simp [hpath]⟩

@[simp]
theorem primitiveBoundaryOfRelationPath_coe
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (R : LinearMap.ker (mapDNormalizedPath d)) :
    (primitiveBoundaryOfRelationPath d R).1 =
      primitiveReducedBoundary C R.1.1 :=
  rfl

/-- The primitive relation obtained as the boundary of the extended relation
path. -/
def extendedPrimitiveBoundary
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA)) :
    LinearMap.ker (mapRedDist dZ) :=
  primitiveBoundaryOfRelationPath dZ
    (extendedRelationPath E j hj0 hres R)

/-- Naturality of reduced boundary proves that the new primitive relation
restricts to the old boundary. -/
theorem mapRedDist_res_extendedPrimitiveBoundary
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA)) :
    mapRedDist res (extendedPrimitiveBoundary E j hj0 hres R).1 =
      (primitiveBoundaryOfRelationPath dA R).1 := by
  change mapRedDist res
      (primitiveReducedBoundary CZ
        (extendedRelationPath E j hj0 hres R).1.1) =
    primitiveReducedBoundary CA R.1.1
  calc
    mapRedDist res
        (primitiveReducedBoundary CZ
          (extendedRelationPath E j hj0 hres R).1.1) =
        primitiveReducedBoundary CA
          (mapPath res res
            (extendedRelationPath E j hj0 hres R).1.1) :=
      LinearMap.congr_fun
        (reducedBoundary_natural
          (AddMonoidHom.id CZ) (AddMonoidHom.id CA) res res rfl)
        (extendedRelationPath E j hj0 hres R).1.1
    _ = primitiveReducedBoundary CA R.1.1 := by
      rw [mapPath_res_res_extendedRelationPath]

/-- Elementwise denominator-extension statement: the extended relation path
is in the target kernel, restricts to the original path, and its primitive
boundary is a relation extending the old primitive boundary. -/
theorem exists_extendedRelationPath_with_boundary
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA)) :
    ∃ Rtilde : LinearMap.ker (mapDNormalizedPath dZ),
      mapPath res res Rtilde.1.1 = R.1.1 ∧
      mapRedDist res (primitiveBoundaryOfRelationPath dZ Rtilde).1 =
        (primitiveBoundaryOfRelationPath dA R).1 :=
  ⟨extendedRelationPath E j hj0 hres R,
    mapPath_res_res_extendedRelationPath E j hj0 hres R,
    mapRedDist_res_extendedPrimitiveBoundary E j hj0 hres R⟩

/-! ## Optional compatible local restrictions -/

/-- If a target local restriction factors through `res` and a source local
restriction, source local vanishing is preserved by the path extension.  This
is the exact compatibility needed here; no simplicial contraction is used. -/
theorem mapPath_restrict_extendedRelationPath_eq_zero
    {K : Type*} [AddCommGroup K]
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA))
    (sourceRes : CA →+ K) (targetRes : CZ →+ K)
    (hcompat : targetRes = sourceRes.comp res)
    (hlocal : mapPath sourceRes sourceRes R.1.1 = 0) :
    mapPath targetRes targetRes
        (extendedRelationPath E j hj0 hres R).1.1 = 0 := by
  calc
    mapPath targetRes targetRes
        (extendedRelationPath E j hj0 hres R).1.1 =
        mapPath (sourceRes.comp res) (sourceRes.comp res)
          (extendedRelationPath E j hj0 hres R).1.1 := by rw [hcompat]
    _ = mapPath sourceRes sourceRes
        (mapPath res res
          (extendedRelationPath E j hj0 hres R).1.1) :=
      (mapPath_comp_apply res res sourceRes sourceRes _).symm
    _ = mapPath sourceRes sourceRes R.1.1 := by
      rw [mapPath_res_res_extendedRelationPath]
    _ = 0 := hlocal

/-- Under the same compatible local restriction, the extended primitive
boundary also restricts to zero. -/
theorem mapRedDist_restrict_extendedPrimitiveBoundary_eq_zero
    {K : Type*} [AddCommGroup K]
    (E : FiberwiseCochainLift dA dZ res)
    (j : CA → CZ) (hj0 : j 0 = 0) (hres : ∀ c, res (j c) = c)
    (R : LinearMap.ker (mapDNormalizedPath dA))
    (sourceRes : CA →+ K) (targetRes : CZ →+ K)
    (hcompat : targetRes = sourceRes.comp res)
    (hlocal : mapPath sourceRes sourceRes R.1.1 = 0) :
    mapRedDist targetRes (extendedPrimitiveBoundary E j hj0 hres R).1 = 0 := by
  change mapRedDist targetRes
      (primitiveReducedBoundary CZ
        (extendedRelationPath E j hj0 hres R).1.1) = 0
  calc
    mapRedDist targetRes
        (primitiveReducedBoundary CZ
          (extendedRelationPath E j hj0 hres R).1.1) =
        primitiveReducedBoundary K
          (mapPath targetRes targetRes
            (extendedRelationPath E j hj0 hres R).1.1) :=
      LinearMap.congr_fun
        (reducedBoundary_natural
          (AddMonoidHom.id CZ) (AddMonoidHom.id K)
          targetRes targetRes rfl)
        (extendedRelationPath E j hj0 hres R).1.1
    _ = 0 := by
      rw [mapPath_restrict_extendedRelationPath_eq_zero
        E j hj0 hres R sourceRes targetRes hcompat hlocal]
      simp

end GeneralSphereT.PathAlgebra
