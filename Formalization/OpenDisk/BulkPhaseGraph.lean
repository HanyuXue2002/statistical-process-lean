import Formalization.OpenDisk.BulkPhaseCompletion

/-!
# Concrete models for the canonical-completion interface

For arbitrary additive maps `α : U → I` and `β : U → B`, closed actual
cochains are the range of `(α,β)`, closed cap cochains solve `b = β u`, and
`base(u,b) = (0,b-βu)`. This supplies every field of `Model` by proof, and
demonstrates that the completion interface is realizable.

Taking `U = G` and `α,β` to be constant cochains is precisely the algebra of
degree-zero cochains on a connected actual ball and its cone cap. The
identification of closed zero-cochains with constants on an arbitrary
connected triangulation is not asserted by this module.
-/

noncomputable section

namespace OpenDisk.BulkPhaseGraph

open BulkPhaseCompletion

variable {I U B : Type*} [AddCommGroup I] [AddCommGroup U] [AddCommGroup B]

def capDifferential (β : U →+ B) : U × B →+ B :=
  AddMonoidHom.snd U B - β.comp (AddMonoidHom.fst U B)

def capBaseInclusion : B →+ U × B :=
  (0 : B →+ U).prod (AddMonoidHom.id B)

def capSplitting (β : U →+ B) : ConePhase.Splitting (capDifferential β).ker :=
  ConePhase.splittingOfDifferential (capDifferential β) capBaseInclusion
    (by intro c; simp [capDifferential, capBaseInclusion])

@[simp] theorem capSplitting_base (β : U →+ B) (c : U × B) :
    (capSplitting β).base c = (0, c.2 - β c.1) := rfl

/-- A completely constructed split-coordinate completion model. -/
def graphModel (α : U →+ I) (β : U →+ B) : Model I U B where
  actualClosed := (α.prod β).range
  capClosed := (capDifferential β).ker
  boundaryClosed := β.range
  actual_closed := by
    intro a
    obtain ⟨u, hu⟩ := a.property
    exact ⟨u, congrArg Prod.snd hu⟩
  cap_closed := by
    intro c
    have hc : c.val.2 - β c.val.1 = 0 := c.property
    exact ⟨c.val.1, (sub_eq_zero.mp hc).symm⟩
  actual_extension := by
    intro z
    obtain ⟨u, hu⟩ := z.property
    exact ⟨⟨(α u, β u), ⟨u, rfl⟩⟩, hu⟩
  cap_extension := by
    intro z
    obtain ⟨u, hu⟩ := z.property
    refine ⟨⟨(u, β u), ?_⟩, hu⟩
    change β u - β u = 0
    exact sub_self _
  splitting := capSplitting β
  base_new_zero := fun _ => rfl
  base_zero_slice := by intro b; simp

theorem closedCap_iff (β : U →+ B) (c : U × B) :
    c ∈ (capDifferential β).ker ↔ c.2 = β c.1 := by
  change c.2 - β c.1 = 0 ↔ _
  exact sub_eq_zero

/-- The constant-cochain additive map on any vertex family. -/
def constantCochainHom (E G : Type*) [AddCommGroup G] : G →+ (E → G) where
  toFun g _ := g
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual/cap algebra for `q = 1`, for any internal and boundary vertex sets. -/
def degreeZeroModel (Internal Boundary G : Type*) [AddCommGroup G] :
    Model (Internal → G) G (Boundary → G) :=
  graphModel (constantCochainHom Internal G) (constantCochainHom Boundary G)

@[simp] theorem degreeZero_base (Internal Boundary G : Type*) [AddCommGroup G]
    (c : G × (Boundary → G)) :
    (degreeZeroModel Internal Boundary G).splitting.base c =
      (0, fun x => c.2 x - c.1) := rfl

end OpenDisk.BulkPhaseGraph
