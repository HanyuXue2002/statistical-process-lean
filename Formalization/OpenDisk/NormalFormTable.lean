import Formalization.OpenDisk.NormalFormPath
import Formalization.OpenDisk.JointLocality

set_option linter.style.header false

/-!
# Local normal form for literal elementary phase tables

No phase-character input is assumed in the exported theorem. Every table on
nonzero elementary increments is extended by zero on all other increments,
then extended linearly to the path group. The potential and residual are
globally continuous additive functions of the original table entries.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G A Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]

theorem elementaryLabel_step_injective :
    Function.Injective (elementaryStep (ι := ι) (G := G)) := by
  intro e f h
  have hi : e.val.1 = f.val.1 := by
    by_contra hne
    have heval := congrArg (fun c : Configuration ι G => c e.val.1) h
    have hz : e.val.2 = 0 := by
      simpa [elementaryStep, Finsupp.single_apply, hne, Ne.symm hne] using heval
    exact e.property hz
  have hg : e.val.2 = f.val.2 := by
    have heval := congrArg (fun c : Configuration ι G => c e.val.1) h
    simpa [elementaryStep, Finsupp.single_apply, hi] using heval
  exact Subtype.ext (Prod.ext hi hg)

/-- Extend by zero off the nonzero elementary labels, with no fusion relation. -/
def extendElementaryTable (T : ElementaryLabel ι G → Configuration ι G → A) :
    Configuration ι G → Configuration ι G → A :=
  Function.extend elementaryStep T (fun _ _ => 0)

@[simp] theorem extendElementaryTable_step
    (T : ElementaryLabel ι G → Configuration ι G → A) (e : ElementaryLabel ι G) :
    extendElementaryTable T (elementaryStep e) = T e :=
  elementaryLabel_step_injective.extend_apply T _ e

@[simp] theorem extendElementaryTable_zero
    (T : ElementaryLabel ι G → Configuration ι G → A) :
    extendElementaryTable T 0 = 0 := by
  apply Function.extend_apply'
  rintro ⟨e, he⟩
  have h := congrArg (fun c : Configuration ι G => c e.val.1) he
  exact e.property (by simpa [elementaryStep] using h)

def rawOperationCharacterOfTable (T : ElementaryLabel ι G → Configuration ι G → A) :
    RawPath (Configuration ι G) (Configuration ι G) →ₗ[ℤ] A :=
  Finsupp.linearCombination ℤ (fun p => extendElementaryTable T p.1 p.2)

@[simp] theorem rawOperationCharacterOfTable_single
    (T : ElementaryLabel ι G → Configuration ι G → A)
    (p : Configuration ι G × Configuration ι G) (n : ℤ) :
    rawOperationCharacterOfTable T (Finsupp.single p n) = n • extendElementaryTable T p.1 p.2 := by
  simp [rawOperationCharacterOfTable]

theorem zeroIncrement_le_rawOperationCharacter_ker
    (T : ElementaryLabel ι G → Configuration ι G → A) :
    zeroIncrement (Configuration ι G) (Configuration ι G) ≤
      LinearMap.ker (rawOperationCharacterOfTable T) := by
  rw [zeroIncrement, Submodule.span_le]
  rintro p ⟨c, rfl⟩
  simp

/-- Every elementary table gives an actual character on operation words. -/
def operationCharacterOfTable (T : ElementaryLabel ι G → Configuration ι G → A) :
    OperationCharacter ι G A :=
  (zeroIncrement (Configuration ι G) (Configuration ι G)).liftQ
    (rawOperationCharacterOfTable T) (zeroIncrement_le_rawOperationCharacter_ker T)

@[simp] theorem operationCharacterOfTable_edge
    (T : ElementaryLabel ι G → Configuration ι G → A) (s c : Configuration ι G) :
    operationCharacterOfTable T (edge s c) = extendElementaryTable T s c := by
  simp [operationCharacterOfTable, edge, rawEdge]

@[simp] theorem operationCharacterOfTable_elementary
    (T : ElementaryLabel ι G → Configuration ι G → A)
    (e : ElementaryLabel ι G) (c : Configuration ι G) :
    operationPhase (operationCharacterOfTable T) (elementaryStep e) c = T e c := by
  simp [operationPhase]

@[simp] theorem operationPhase_of_table
    (T : ElementaryLabel ι G → Configuration ι G → A) (e : ElementaryLabel ι G) :
    operationPhase (operationCharacterOfTable T) (elementaryStep e) = T e := by
  funext c
  exact operationCharacterOfTable_elementary T e c

/-- The precise phase equations from the report, for the elementary table itself. -/
def TableOperatorLocal (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → A) : Prop :=
  ∀ (e f : ElementaryLabel ι G) (rs : List (Configuration ι G)) c,
    NoCommonFacetList (fun ρ => coordinateRestriction (G := G) (facets ρ))
      (elementaryStep e :: elementaryStep f :: rs) →
    iteratedPhaseDifference rs
      (fun v => phaseDifference (elementaryStep e) (T f) v -
        phaseDifference (elementaryStep f) (T e) v) c = 0

theorem tableOperatorLocal_iff (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → A) :
    TableOperatorLocal facets T ↔ OperatorLocal facets (operationCharacterOfTable T) := by
  rw [operatorLocal_iff_phase_equations]
  constructor
  · intro h i g j k rs c hg hk hfac
    let e : ElementaryLabel ι G := ⟨(i, g), hg⟩
    let f : ElementaryLabel ι G := ⟨(j, k), hk⟩
    change iteratedPhaseDifference rs
      (fun v => phaseDifference (elementaryStep e)
        (operationPhase (operationCharacterOfTable T) (elementaryStep f)) v -
        phaseDifference (elementaryStep f)
          (operationPhase (operationCharacterOfTable T) (elementaryStep e)) v) c = 0
    simpa only [operationPhase_of_table] using h e f rs c hfac
  · intro h e f rs c hfac
    have hh := h e.val.1 e.val.2 f.val.1 f.val.2 rs c e.property f.property hfac
    change iteratedPhaseDifference rs
      (fun v => phaseDifference (elementaryStep e)
        (operationPhase (operationCharacterOfTable T) (elementaryStep f)) v -
        phaseDifference (elementaryStep f)
          (operationPhase (operationCharacterOfTable T) (elementaryStep e)) v) c = 0 at hh
    simpa only [operationPhase_of_table] using hh

def tableNormalPotential (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → A) : Configuration ι G → A :=
  normalPotential facets (operationCharacterOfTable T)

def tableNormalResidual (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → A)
    (e : ElementaryLabel ι G) : Configuration ι G → A := fun c =>
  T e c - phaseDifference (elementaryStep e) (tableNormalPotential facets T) c

theorem tableNormalResidual_markedLocal (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (T : ElementaryLabel ι G → Configuration ι G → A) (hT : TableOperatorLocal facets T)
    (e : ElementaryLabel ι G) : MarkedLocal facets {e.val.1} (tableNormalResidual facets T e) := by
  have hh := normalResidual_markedLocal facets hcover (operationCharacterOfTable T)
    ((tableOperatorLocal_iff facets T).mp hT) e.val.1 e.val.2 e.property
  have heq : normalResidual facets (operationCharacterOfTable T) e.val.1 e.val.2 =
      tableNormalResidual facets T e := by
    funext c
    change operationPhase (operationCharacterOfTable T) (elementaryStep e) c - _ = _
    rw [operationCharacterOfTable_elementary]
    rfl
  rwa [heq] at hh

/-- The complete phase-table statement of Theorem 5.5. -/
theorem table_local_normal_form (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (T : ElementaryLabel ι G → Configuration ι G → A) (hT : TableOperatorLocal facets T) :
    (∀ e, MarkedLocal facets {e.val.1} (tableNormalResidual facets T e)) ∧
    (∀ e c, T e c = tableNormalResidual facets T e c +
      phaseDifference (elementaryStep e) (tableNormalPotential facets T) c) := by
  exact ⟨tableNormalResidual_markedLocal facets hcover T hT,
    fun e c => (sub_add_cancel _ _).symm⟩

theorem extendElementaryTable_add
    (T U : ElementaryLabel ι G → Configuration ι G → A) :
    extendElementaryTable (T + U) = extendElementaryTable T + extendElementaryTable U := by
  classical
  funext s c
  change extendElementaryTable (T + U) s c =
    extendElementaryTable T s c + extendElementaryTable U s c
  unfold extendElementaryTable Function.extend
  by_cases h : ∃ a : ElementaryLabel ι G, elementaryStep a = s
  · simp only [dite_eq_left h, Pi.add_apply]
  · simp only [dite_eq_right h, zero_add]

theorem operationCharacterOfTable_add
    (T U : ElementaryLabel ι G → Configuration ι G → A) :
    operationCharacterOfTable (T + U) = operationCharacterOfTable T + operationCharacterOfTable U := by
  ext p
  change operationCharacterOfTable (T + U) (edge p.1 p.2) =
    (operationCharacterOfTable T + operationCharacterOfTable U) (edge p.1 p.2)
  simp [extendElementaryTable_add]

theorem tableNormalPotential_add (facets : Facet → Set ι)
    (T U : ElementaryLabel ι G → Configuration ι G → A) :
    tableNormalPotential facets (T + U) = tableNormalPotential facets T + tableNormalPotential facets U := by
  simp only [tableNormalPotential, operationCharacterOfTable_add, normalPotential_add]

theorem tableNormalResidual_add (facets : Facet → Set ι)
    (T U : ElementaryLabel ι G → Configuration ι G → A) :
    tableNormalResidual facets (T + U) = tableNormalResidual facets T + tableNormalResidual facets U := by
  funext e c
  simp only [tableNormalResidual, phaseDifference, tableNormalPotential_add, Pi.add_apply]
  abel

/-- The potential and residual are chosen by one additive map on the complete input table. -/
def normalFormChoiceHom (facets : Facet → Set ι) :
    (ElementaryLabel ι G → Configuration ι G → A) →+
      (Configuration ι G → A) × (ElementaryLabel ι G → Configuration ι G → A) where
  toFun T := (tableNormalPotential facets T, tableNormalResidual facets T)
  map_zero' := by
    apply Prod.ext
    · exact add_eq_left.mp (by simpa only [zero_add] using
        (tableNormalPotential_add facets (0 : ElementaryLabel ι G → Configuration ι G → A) 0).symm)
    · exact add_eq_left.mp (by simpa only [zero_add] using
        (tableNormalResidual_add facets (0 : ElementaryLabel ι G → Configuration ι G → A) 0).symm)
  map_add' T U := Prod.ext (tableNormalPotential_add facets T U) (tableNormalResidual_add facets T U)

section Continuity

variable [TopologicalSpace A] [IsTopologicalAddGroup A]

theorem continuous_extendElementaryTable (s c : Configuration ι G) :
    Continuous (fun T : ElementaryLabel ι G → Configuration ι G → A =>
      extendElementaryTable T s c) := by
  classical
  unfold extendElementaryTable Function.extend
  split_ifs with h
  · exact (continuous_apply c).comp (continuous_apply (Classical.choose h))
  · exact continuous_const

theorem continuous_rawOperationCharacterOfTable
    (u : RawPath (Configuration ι G) (Configuration ι G)) :
    Continuous (fun T : ElementaryLabel ι G → Configuration ι G → A =>
      rawOperationCharacterOfTable T u) := by
  classical
  induction u using Finsupp.induction with
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ :
      ElementaryLabel ι G → Configuration ι G → A => (0 : A)))
  | single_add p n u hp hn ih =>
      simp only [map_add, rawOperationCharacterOfTable_single]
      exact ((continuous_extendElementaryTable p.1 p.2).zsmul n).add ih

theorem continuous_operationCharacterOfTable
    (p : GeneralSphereT.PathAlgebra.Path (Configuration ι G) (Configuration ι G)) :
    Continuous (fun T : ElementaryLabel ι G → Configuration ι G → A =>
      operationCharacterOfTable T p) := by
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement (Configuration ι G) (Configuration ι G)) p ?_
  intro u
  exact continuous_rawOperationCharacterOfTable u

/-- The selected potential is continuous in every phase-table entry. -/
theorem continuous_tableNormalPotential (facets : Facet → Set ι) :
    Continuous (tableNormalPotential (G := G) (A := A) facets) := by
  apply continuous_pi
  intro c
  exact continuous_operationCharacterOfTable
    (rawCanonicalPath (nonfaceProjection facets (Finsupp.single c 1)))

/-- The marked-local residual is selected continuously at the same time. -/
theorem continuous_tableNormalResidual (facets : Facet → Set ι) :
    Continuous (tableNormalResidual (G := G) (A := A) facets) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro c
  change Continuous (fun T : ElementaryLabel ι G → Configuration ι G → A =>
    T e c - (tableNormalPotential facets T (c + elementaryStep e) - tableNormalPotential facets T c))
  have hp := continuous_tableNormalPotential (G := G) (A := A) facets
  have h₁ : Continuous (fun T : ElementaryLabel ι G → Configuration ι G → A => T e c) :=
    (continuous_apply c).comp (continuous_apply e)
  have h₂ : Continuous (fun T : ElementaryLabel ι G → Configuration ι G → A =>
      tableNormalPotential facets T (c + elementaryStep e)) :=
    (continuous_apply (c + elementaryStep e)).comp hp
  have h₃ : Continuous (fun T : ElementaryLabel ι G → Configuration ι G → A =>
      tableNormalPotential facets T c) := (continuous_apply c).comp hp
  exact h₁.sub (h₂.sub h₃)

/-- The simultaneous additive choice is continuous for the actual product topology. -/
theorem continuous_normalFormChoiceHom (facets : Facet → Set ι) :
    Continuous (normalFormChoiceHom (G := G) (A := A) facets) :=
  (continuous_tableNormalPotential facets).prodMk (continuous_tableNormalResidual facets)

end Continuity

end OpenDisk
