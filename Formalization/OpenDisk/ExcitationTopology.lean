import Formalization.OpenDisk.Excitation

set_option linter.style.header false

/-!
# Closedness of the actual excitation table space

Locality is an intersection of kernels of continuous integral evaluations.
Consequently actual excitation tables form a closed additive subgroup, and
are compact whenever the coefficient group is compact.
-/

noncomputable section

open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [T2Space P]

theorem isClosed_tableOperatorLocalSubgroup (facets : Facet → Set ι) :
    IsClosed (tableOperatorLocalSubgroup (G := G) facets P :
      Set (ElementaryLabel ι G → Configuration ι G → P)) := by
  have heq : (tableOperatorLocalSubgroup (G := G) facets P :
      Set (ElementaryLabel ι G → Configuration ι G → P)) =
      ⋂ p : physicalIdentityPaths (identityRestrictionData (G := G) facets),
        {T | operationCharacterOfTable T p.val = 0} := by
    ext T
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h p
      exact ((tableOperatorLocal_iff facets T).mp h) p.property
    · intro h
      change TableOperatorLocal facets T
      rw [tableOperatorLocal_iff]
      intro p hp
      exact h ⟨p, hp⟩
  rw [heq]
  exact isClosed_iInter fun p =>
    isClosed_eq (continuous_operationCharacterOfTable p.val) continuous_const

theorem isClosed_excitationPhases (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) :
    IsClosed (excitationPhases facets d P : Set (ElementaryLabel ι G → B → P)) :=
  (isClosed_tableOperatorLocalSubgroup facets).preimage (continuous_excitationPullback d)

instance [CompactSpace P] (facets : Facet → Set ι) (d : Configuration ι G →+ B) :
    CompactSpace (ExcitationPhase facets d P) :=
  isCompact_iff_compactSpace.mp (isClosed_excitationPhases facets d).isCompact

end OpenDisk
