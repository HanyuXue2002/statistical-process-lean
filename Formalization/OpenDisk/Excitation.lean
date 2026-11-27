import Formalization.OpenDisk.NormalFormTableLocality

set_option linter.style.header false

/-!
# Actual excitation tables and a continuous additive lift

The target consists of the literal tables on physical configurations whose
cochain pullback obeys the commutator-locality equations.  The forgetful map
lands in that subgroup by marked locality and gauge invariance.  The normal
form constructs a continuous additive right inverse, retaining every table
entry and the full constant phase convention.
-/

noncomputable section

open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P]

/-- Linear extension of elementary tables, as an additive map. -/
def operationCharacterOfTableHom :
    (ElementaryLabel ι G → Configuration ι G → P) →+ OperationCharacter ι G P where
  toFun := operationCharacterOfTable
  map_add' := operationCharacterOfTable_add
  map_zero' := add_eq_left.mp (by simpa only [zero_add] using
    (operationCharacterOfTable_add
      (0 : ElementaryLabel ι G → Configuration ι G → P) 0).symm)

/-- All elementary operator-local tables form their actual additive subgroup. -/
def tableOperatorLocalSubgroup (facets : Facet → Set ι) (P : Type*) [AddCommGroup P] :
    AddSubgroup (ElementaryLabel ι G → Configuration ι G → P) where
  carrier := {T | TableOperatorLocal facets T}
  zero_mem' := tableOperatorLocal_of_marked facets 0
    (fun e => (markedFunctionSubgroup (P := P) facets e).zero_mem)
  add_mem' := by
    intro T U hT hU
    change TableOperatorLocal facets (T + U)
    rw [tableOperatorLocal_iff, operationCharacterOfTable_add]
    intro p hp
    change operationCharacterOfTable T p + operationCharacterOfTable U p = 0
    rw [((tableOperatorLocal_iff facets T).mp hT) hp,
      ((tableOperatorLocal_iff facets U).mp hU) hp, zero_add]
  neg_mem' := by
    intro T hT
    change TableOperatorLocal facets (-T)
    rw [tableOperatorLocal_iff]
    have hn : operationCharacterOfTable (-T) = -operationCharacterOfTable T :=
      map_neg operationCharacterOfTableHom T
    rw [hn]
    intro p hp
    change -operationCharacterOfTable T p = 0
    rw [((tableOperatorLocal_iff facets T).mp hT) hp, neg_zero]

/-- Pull an actual table back along the cochain coboundary. -/
def excitationPullback (d : Configuration ι G →+ B) :
    (ElementaryLabel ι G → B → P) →+ (ElementaryLabel ι G → Configuration ι G → P) where
  toFun θ e c := θ e (d c)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The target subgroup uses precisely operator locality on the pulled-back table. -/
def excitationPhases (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (P : Type*) [AddCommGroup P] : AddSubgroup (ElementaryLabel ι G → B → P) :=
  (tableOperatorLocalSubgroup (G := G) facets P).comap (excitationPullback d)

abbrev ExcitationPhase (facets : Facet → Set ι) (d : Configuration ι G →+ B)
    (P : Type*) [AddCommGroup P] := excitationPhases facets d P

variable (facets : Facet → Set ι) (d : Configuration ι G →+ B)
  (rep : B → Configuration ι G) (hrep : ∀ a, d (rep a) = a)

include hrep in
theorem forgetExcitation_pullback (x : LocalJointPhase facets d P) :
    excitationPullback d
      (forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x) =
      gaugeTable x.val.2 (-x.val.1) := by
  funext e c
  change forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x e (d c) = _
  rw [forgetExcitation_evaluate d elementaryStep (markedFunctionSubgroup facets) rep hrep]
  simp only [gaugeTable, phaseDifference, difference, Pi.neg_apply]
  abel

include hrep in
/-- Every actual joint datum produces an operator-local excitation table. -/
theorem forgetExcitation_mem (x : LocalJointPhase facets d P) :
    forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x ∈
      excitationPhases facets d P := by
  change TableOperatorLocal facets (excitationPullback d
    (forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x))
  rw [forgetExcitation_pullback facets d rep hrep x]
  exact (tableOperatorLocal_gauge_iff facets x.val.2 (-x.val.1)).mpr
    (tableOperatorLocal_of_marked facets x.val.2 x.property.1)

/-- The excitation forgetful map with its proved, literal locality target. -/
def localForgetExcitation : LocalJointPhase facets d P →+ ExcitationPhase facets d P where
  toFun x := ⟨forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep x,
    forgetExcitation_mem facets d rep hrep x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

variable (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)

/-- The chosen normal form has exactly the matching sign required in (5.4). -/
theorem tableNormalResidual_matching (θ : ExcitationPhase facets d P)
    (e : ElementaryLabel ι G) :
    Matching d (-tableNormalPotential facets (excitationPullback d θ.val))
      (tableNormalResidual facets (excitationPullback d θ.val) e) (elementaryStep e) := by
  have hh := matching_of_table d (-tableNormalPotential facets (excitationPullback d θ.val))
    (θ.val e) (elementaryStep e)
  convert hh using 1
  funext c
  simp only [tableNormalResidual, excitationPullback, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, phaseDifference, difference, Pi.add_apply, Pi.neg_apply, Function.comp_apply]
  abel

/-- An actual additive section, obtained from the fixed integral normal-form choices. -/
def excitationSection : ExcitationPhase facets d P →+ LocalJointPhase facets d P where
  toFun θ := ⟨(-tableNormalPotential facets (excitationPullback d θ.val),
      tableNormalResidual facets (excitationPullback d θ.val)),
    fun e => tableNormalResidual_markedLocal facets hcover (excitationPullback d θ.val)
      θ.property e,
    tableNormalResidual_matching facets d θ⟩
  map_zero' := by
    apply Subtype.ext
    have hh := map_zero (normalFormChoiceHom (G := G) (A := P) facets)
    apply Prod.ext
    · change -tableNormalPotential facets 0 = 0
      have hz : tableNormalPotential facets (0 : ElementaryLabel ι G → Configuration ι G → P) = 0 :=
        congrArg Prod.fst hh
      rw [hz, neg_zero]
    · change tableNormalResidual facets (0 : ElementaryLabel ι G → Configuration ι G → P) = 0
      exact congrArg Prod.snd hh
  map_add' θ η := by
    apply Subtype.ext
    apply Prod.ext
    · change -tableNormalPotential facets (excitationPullback d (θ.val + η.val)) = _
      rw [map_add, tableNormalPotential_add, neg_add]
      rfl
    · change tableNormalResidual facets (excitationPullback d (θ.val + η.val)) = _
      rw [map_add, tableNormalResidual_add]
      rfl

/-- Every full excitation table is recovered entry by entry by the section. -/
theorem localForgetExcitation_section (θ : ExcitationPhase facets d P) :
    localForgetExcitation facets d rep hrep (excitationSection facets d hcover θ) = θ := by
  apply Subtype.ext
  funext e a
  change tableNormalResidual facets (excitationPullback d θ.val) e (rep a) -
    difference (-tableNormalPotential facets (excitationPullback d θ.val))
      (elementaryStep e) (rep a) = θ.val e a
  simp only [tableNormalResidual, phaseDifference, difference, Pi.neg_apply]
  change θ.val e (d (rep a)) - _ - _ = θ.val e a
  rw [hrep]
  abel

include hcover in
theorem localForgetExcitation_surjective :
    Function.Surjective (localForgetExcitation (P := P) facets d rep hrep) :=
  Function.RightInverse.surjective (localForgetExcitation_section facets d rep hrep hcover)

theorem localForgetExcitation_comp_section :
    (localForgetExcitation (P := P) facets d rep hrep).comp
      (excitationSection facets d hcover) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro θ
  exact localForgetExcitation_section facets d rep hrep hcover θ

section Topology

variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_excitationPullback : Continuous (excitationPullback (P := P) d) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro c
  exact (continuous_apply (d c)).comp (continuous_apply e)

theorem continuous_localForgetExcitation :
    Continuous (localForgetExcitation (P := P) facets d rep hrep) :=
  (continuous_forgetExcitation d elementaryStep (markedFunctionSubgroup facets) rep).subtype_mk _

/-- The section is continuous in the prescribed product and subspace topologies. -/
theorem continuous_excitationSection :
    Continuous (excitationSection (P := P) facets d hcover) := by
  have hp : Continuous (fun θ : ExcitationPhase facets d P => excitationPullback d θ.val) :=
    (continuous_excitationPullback d).comp continuous_subtype_val
  exact (((continuous_tableNormalPotential facets).comp hp).neg.prodMk
    ((continuous_tableNormalResidual facets).comp hp)).subtype_mk _

end Topology

end OpenDisk
