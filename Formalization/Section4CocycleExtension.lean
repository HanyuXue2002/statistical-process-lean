import Formalization.Section4FiberwiseExtension

set_option linter.style.header false

/-!
# Section 4: constructing a fiberwise lift from cocycle extension

The relative-cohomology input in (4.7) is smaller than the full
`FiberwiseCochainLift` used by the free-distribution calculation.  It only
has to extend cocycles to cocycles.  Indeed, choose one cochain in every
coboundary fibre.  Any cochain is that chosen representative plus a cocycle;
extend the representative arbitrarily and the cocycle by the relative
cohomology hypothesis.

This file formalizes that elementary decomposition.  Neither chosen section
is required to be additive.  The resulting map on primitive relation
distributions is nevertheless additive because the free reduced-distribution
construction is applied fibre by fibre.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uCA uCZ uBA uBZ

variable {CA : Type uCA} {CZ : Type uCZ}
variable {BA : Type uBA} {BZ : Type uBZ}
variable [AddCommGroup CA] [AddCommGroup CZ]
variable [AddCommGroup BA] [AddCommGroup BZ]

variable {dA : CA →+ BA} {dZ : CZ →+ BZ} {res : CZ →+ CA}

/-- The precise relative-cohomology datum used in (4.7): every source
cocycle has a target cocycle extending it.  Additivity of this choice is not
needed. -/
structure CocycleExtensionData
    (dA : CA →+ BA) (dZ : CZ →+ BZ) (res : CZ →+ CA) where
  extend : dA.ker → CZ
  res_extend : ∀ z, res (extend z) = z.1
  d_extend : ∀ z, dZ (extend z) = 0

/-- A zero-preserving representative chosen in every fibre of a surjective
additive map. -/
def chosenFiberRepresentative
    (hsurj : Function.Surjective dA) (b : BA) : CA := by
  classical
  exact if hb : b = 0 then 0 else Classical.choose (hsurj b)

@[simp]
theorem chosenFiberRepresentative_zero
    (hsurj : Function.Surjective dA) :
    chosenFiberRepresentative hsurj 0 = 0 := by
  simp [chosenFiberRepresentative]

@[simp]
theorem d_chosenFiberRepresentative
    (hsurj : Function.Surjective dA) (b : BA) :
    dA (chosenFiberRepresentative hsurj b) = b := by
  by_cases hb : b = 0
  · subst b
    simp
  · simp only [chosenFiberRepresentative, hb, dite_false]
    exact Classical.choose_spec (hsurj b)

/-- The cocycle part of a cochain after subtracting the chosen representative
of its coboundary fibre. -/
def cocycleRemainder
    (hsurj : Function.Surjective dA) (c : CA) : dA.ker :=
  ⟨c - chosenFiberRepresentative hsurj (dA c), by
    rw [AddMonoidHom.mem_ker, map_sub, d_chosenFiberRepresentative,
      sub_self]⟩

@[simp]
theorem cocycleRemainder_coe
    (hsurj : Function.Surjective dA) (c : CA) :
    (cocycleRemainder hsurj c : CA) =
      c - chosenFiberRepresentative hsurj (dA c) :=
  rfl

/-- Build the fibrewise lift of Lemma 4.2 from its two elementary inputs:
an arbitrary cochain restriction section and extension of source cocycles to
target cocycles. -/
def FiberwiseCochainLift.ofCocycleExtension
    (hsurj : Function.Surjective dA)
    (cochainLift : CA → CZ)
    (res_cochainLift : ∀ c, res (cochainLift c) = c)
    (E : CocycleExtensionData dA dZ res) :
    FiberwiseCochainLift dA dZ res where
  lift c :=
    cochainLift (chosenFiberRepresentative hsurj (dA c)) +
      E.extend (cocycleRemainder hsurj c)
  physicalLift b :=
    dZ (cochainLift (chosenFiberRepresentative hsurj b))
  res_lift c := by
    rw [map_add, res_cochainLift, E.res_extend]
    simp only [cocycleRemainder_coe]
    abel
  d_lift c := by
    rw [map_add, E.d_extend, add_zero]

@[simp]
theorem FiberwiseCochainLift.ofCocycleExtension_lift
    (hsurj : Function.Surjective dA)
    (cochainLift : CA → CZ)
    (res_cochainLift : ∀ c, res (cochainLift c) = c)
    (E : CocycleExtensionData dA dZ res) (c : CA) :
    (FiberwiseCochainLift.ofCocycleExtension
      hsurj cochainLift res_cochainLift E).lift c =
      cochainLift (chosenFiberRepresentative hsurj (dA c)) +
        E.extend (cocycleRemainder hsurj c) :=
  rfl

end GeneralSphereT.PathAlgebra
