import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

set_option linter.style.header false

/-!
# The integral character duality behind Proposition 2.1

The phase group is the actual real circle, not a formal placeholder.  Its
divisibility supplies every character extension used below.  We work with
full free integer distributions, so constant phases are retained.

This file proves algebraic character duality.  It does not assert the
topological comparison or the sphere homology computation in the report.
-/

noncomputable section

open scoped BigOperators

namespace OpenDisk.PhaseDuality

/-- Additive phases, with period one. -/
abbrev Phase := AddCircle (1 : ℝ)

/-- Full integer distributions; no augmentation condition is imposed. -/
abbrev Distribution (X : Type*) := X →₀ ℤ

section Evaluation

variable {X : Type*}

/-- Evaluation of an actual phase table on an integer distribution. -/
def evaluate (φ : X → Phase) : Distribution X →ₗ[ℤ] Phase :=
  Finsupp.linearCombination ℤ φ

@[simp]
theorem evaluate_single (φ : X → Phase) (x : X) (n : ℤ) :
    evaluate φ (Finsupp.single x n) = n • φ x := by
  simp [evaluate]

/-- Arbitrary full phase tables are exactly characters of full distributions. -/
def phaseTableEquiv : (X → Phase) ≃ₗ[ℤ] (Distribution X →ₗ[ℤ] Phase) where
  toFun := evaluate
  invFun χ x := χ (Finsupp.single x 1)
  left_inv φ := by funext x; simp
  right_inv χ := by
    ext x
    simp [evaluate]
  map_add' φ ψ := by ext x; simp [evaluate, smul_add]
  map_smul' n φ := by ext x; simp [evaluate]

@[simp]
theorem phaseTableEquiv_apply (φ : X → Phase) :
    phaseTableEquiv φ = evaluate φ := rfl

/-- The basis configuration at zero still detects the global phase. -/
theorem constant_phase_detected (x : X) (t : Phase) :
    evaluate (fun _ : X => t) (Finsupp.single x 1) = t := by simp

/-- Pushforward of full distributions is a formal marginal, not a sum of
configuration values. -/
def pushforward {Y : Type*} (f : X → Y) :
    Distribution X →ₗ[ℤ] Distribution Y :=
  Finsupp.linearCombination ℤ (fun x => Finsupp.single (f x) 1)

@[simp]
theorem pushforward_single {Y : Type*} (f : X → Y) (x : X) :
    pushforward f (Finsupp.single x 1) = Finsupp.single (f x) 1 := by
  simp [pushforward]

end Evaluation

section ClosedInvariance

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]

/-- Full phase tables invariant under every closed shift `z ∈ ker d`. -/
def closedInvariant (d : C →+ B) : Submodule ℤ (C → Phase) where
  carrier := {φ | ∀ z, d z = 0 → ∀ c, φ (c + z) = φ c}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ z hz c; simp [hφ z hz c, hψ z hz c]
  smul_mem' := by intro n φ hφ z hz c; simp [hφ z hz c]

/-- Closed invariance makes evaluation independent of the primitive. -/
theorem closedInvariant_eq_of_same_image (d : C →+ B)
    {φ : C → Phase} (hφ : φ ∈ closedInvariant d) {x y : C}
    (hxy : d x = d y) : φ x = φ y := by
  have hz : d (x - y) = 0 := by simp [map_sub, hxy]
  have h := hφ (x - y) hz y
  have he : y + (x - y) = x := (add_comm _ _).trans (sub_add_cancel _ _)
  simpa only [he] using h

/-- Closed phase tables are precisely arbitrary phase tables on actual
curvatures.  The chosen section affects neither the equivalence nor any
evaluation, by `closedInvariant_eq_of_same_image`. -/
def closedPhaseTableEquiv (d : C →+ B) (hd : Function.Surjective d) :
    closedInvariant d ≃ₗ[ℤ] (B → Phase) where
  toFun φ b := φ.1 (Function.surjInv hd b)
  invFun f := ⟨fun c => f (d c), by
    intro z hz c
    simp [map_add, hz]⟩
  left_inv φ := by
    apply Subtype.ext
    funext c
    apply closedInvariant_eq_of_same_image d φ.2
    exact Function.surjInv_eq hd (d c)
  right_inv f := by
    funext b
    simp [Function.surjInv_eq]
  map_add' φ ψ := rfl
  map_smul' n φ := rfl

@[simp]
theorem closedPhaseTableEquiv_apply_image (d : C →+ B)
    (hd : Function.Surjective d) (φ : closedInvariant d) (c : C) :
    closedPhaseTableEquiv d hd φ (d c) = φ.1 c :=
  closedInvariant_eq_of_same_image d φ.2 (Function.surjInv_eq hd (d c))

/-- Complete closed-invariant tables are the characters of the full
integer distribution group on curvatures. -/
def closedPhaseCharacterEquiv (d : C →+ B) (hd : Function.Surjective d) :
    closedInvariant d ≃ₗ[ℤ] (Distribution B →ₗ[ℤ] Phase) :=
  (closedPhaseTableEquiv d hd).trans phaseTableEquiv

end ClosedInvariance

section Annihilators

variable {D E : Type*} [AddCommGroup D] [AddCommGroup E]

/-- Characters that vanish on a specified integer submodule. -/
def annihilator (N : Submodule ℤ D) : Submodule ℤ (D →ₗ[ℤ] Phase) where
  carrier := {χ | ∀ x ∈ N, χ x = 0}
  zero_mem' := by simp
  add_mem' := by intro χ ψ hχ hψ x hx; simp [hχ x hx, hψ x hx]
  smul_mem' := by intro n χ hχ x hx; simp [hχ x hx]

@[simp]
theorem mem_annihilator (N : Submodule ℤ D) (χ : D →ₗ[ℤ] Phase) :
    χ ∈ annihilator N ↔ ∀ x ∈ N, χ x = 0 := Iff.rfl

/-- Every real-circle character of a subgroup extends to the ambient group.
The extension is supplied by the proved divisibility of `ℝ/ℤ`. -/
theorem extend_character (N : Submodule ℤ D) (χ : N →ₗ[ℤ] Phase) :
    ∃ ψ : D →ₗ[ℤ] Phase, ψ.comp N.subtype = χ :=
  (Module.Baer.of_divisible Phase).extension_property N.subtype
    Subtype.val_injective χ

/-- A character annihilates a map's kernel exactly when it comes by
pullback from a character of the entire target, not just the image. -/
theorem annihilates_kernel_iff (m : D →ₗ[ℤ] E) (χ : D →ₗ[ℤ] Phase) :
    χ ∈ annihilator (LinearMap.ker m) ↔
      ∃ ψ : E →ₗ[ℤ] Phase, ψ.comp m = χ := by
  constructor
  · intro hχ
    let qχ : (D ⧸ LinearMap.ker m) →ₗ[ℤ] Phase :=
      (LinearMap.ker m).liftQ χ hχ
    let rχ : LinearMap.range m →ₗ[ℤ] Phase :=
      qχ.comp m.quotKerEquivRange.symm.toLinearMap
    obtain ⟨ψ, hψ⟩ := extend_character (LinearMap.range m) rχ
    refine ⟨ψ, ?_⟩
    ext x
    have hx := LinearMap.congr_fun hψ ⟨m x, LinearMap.mem_range_self m x⟩
    change ψ (m x) = qχ (m.quotKerEquivRange.symm ⟨m x, _⟩) at hx
    have he := m.quotKerEquivRange_symm_apply_image x (LinearMap.mem_range_self m x)
    exact hx.trans (congrArg qχ he)
  · rintro ⟨ψ, rfl⟩ x hx
    simp [LinearMap.mem_ker.mp hx]

variable (J N : Submodule ℤ D) (hJN : J ≤ N)

/-- The identity subgroup as a submodule of the invariant distributions. -/
def identitiesInInvariant : Submodule ℤ N := J.comap N.subtype

/-- The literal integral quotient `N/J`. -/
abbrev IntegralQuotient := N ⧸ identitiesInInvariant J N

/-- Restrict a character annihilating `J` to the quotient `N/J`. -/
def restrictCharacter :
    annihilator J →ₗ[ℤ] (IntegralQuotient J N →ₗ[ℤ] Phase) where
  toFun χ := (identitiesInInvariant J N).liftQ
    (χ.1.comp N.subtype) (by intro x hx; exact χ.2 x.1 hx)
  map_add' χ ψ := by
    ext x
    rfl
  map_smul' n χ := by
    ext x
    rfl

@[simp]
theorem restrictCharacter_mk (χ : annihilator J) (x : N) :
    restrictCharacter J N χ ((identitiesInInvariant J N).mkQ x) = χ.1 x := rfl

/-- Restriction onto the integral quotient is surjective. -/
theorem restrictCharacter_surjective (hJN : J ≤ N) :
    Function.Surjective (restrictCharacter J N) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := extend_character N
    (χ.comp (identitiesInInvariant J N).mkQ)
  have hψJ : ψ ∈ annihilator J := by
    intro x hx
    have h := LinearMap.congr_fun hψ ⟨x, hJN hx⟩
    have hxJ : (⟨x, hJN hx⟩ : N) ∈ identitiesInInvariant J N := hx
    have hzero : (identitiesInInvariant J N).mkQ ⟨x, hJN hx⟩ = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hxJ
    change ψ x = χ ((identitiesInInvariant J N).mkQ ⟨x, hJN hx⟩) at h
    rw [hzero, map_zero] at h
    exact h
  refine ⟨⟨ψ, hψJ⟩, ?_⟩
  ext x
  exact LinearMap.congr_fun hψ x

/-- The denominator on phase tables: characters annihilating all of `N`. -/
def localCharacters : Submodule ℤ (annihilator J) :=
  (annihilator N).comap (annihilator J).subtype

theorem ker_restrictCharacter :
    LinearMap.ker (restrictCharacter J N) = localCharacters J N := by
  ext χ
  constructor
  · intro hχ
    change ∀ x ∈ N, χ.1 x = 0
    intro x hx
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hχ)
      ((identitiesInInvariant J N).mkQ ⟨x, hx⟩)
    exact h
  · intro hχ
    apply LinearMap.mem_ker.mpr
    ext x
    exact hχ x.1 x.2

/-- Algebraic form of Proposition 2.1: the phase-table quotient is the
real-circle character group of the integral invariant quotient. -/
def phaseQuotientEquiv :
    (annihilator J ⧸ localCharacters J N) ≃ₗ[ℤ]
      (IntegralQuotient J N →ₗ[ℤ] Phase) :=
  (Submodule.quotEquivOfEq _ _ (ker_restrictCharacter J N).symm).trans
    ((restrictCharacter J N).quotKerEquivOfSurjective
      (restrictCharacter_surjective J N hJN))

end Annihilators

section FacetMarginals

variable {D : Type*} [AddCommGroup D]
variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)]

/-- The annihilator of all formal marginal kernels is exactly a sum of
facet characters.  Injectivity of the real circle removes any possible
integral obstruction to extending a character from the marginal image. -/
theorem annihilates_marginals_iff (m : ∀ i, D →ₗ[ℤ] E i)
    (χ : D →ₗ[ℤ] Phase) :
    χ ∈ annihilator (⨅ i, LinearMap.ker (m i)) ↔
      ∃ ψ : ∀ i, E i →ₗ[ℤ] Phase, ∀ x, χ x = ∑ i, ψ i (m i x) := by
  classical
  have hk : LinearMap.ker (LinearMap.pi m) = ⨅ i, LinearMap.ker (m i) := by
    ext x
    simp [LinearMap.mem_ker, funext_iff]
  constructor
  · intro hχ
    rw [← hk] at hχ
    obtain ⟨ψ, hψ⟩ := (annihilates_kernel_iff (LinearMap.pi m) χ).mp hχ
    refine ⟨fun i => ψ.comp (LinearMap.single ℤ E i), fun x => ?_⟩
    rw [← LinearMap.congr_fun hψ x]
    change ψ (fun i => m i x) = ∑ i, ψ (Pi.single i (m i x))
    rw [← map_sum, Finset.univ_sum_single]
  · rintro ⟨ψ, hψ⟩ x hx
    rw [hψ x]
    apply Finset.sum_eq_zero
    intro i _
    have hi := (Submodule.mem_iInf (fun j => LinearMap.ker (m j))).mp hx i
    simp [LinearMap.mem_ker.mp hi]

variable {X : Type*} {Y : ι → Type*}

/-- For actual phase tables, annihilating the common formal-marginal
kernel is precisely the facet-sum form appearing in equation (1.13). -/
theorem evaluation_annihilates_marginals_iff
    (r : ∀ i, X → Y i) (φ : X → Phase) :
    evaluate φ ∈ annihilator (⨅ i, LinearMap.ker (pushforward (r i))) ↔
      ∃ k : ∀ i, Y i → Phase, ∀ x, φ x = ∑ i, k i (r i x) := by
  classical
  rw [annihilates_marginals_iff]
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨fun i y => ψ i (Finsupp.single y 1), fun x => ?_⟩
    simpa using hψ (Finsupp.single x 1)
  · rintro ⟨k, hk⟩
    refine ⟨fun i => evaluate (k i), fun u => ?_⟩
    have h : evaluate φ = ∑ i, (evaluate (k i)).comp (pushforward (r i)) := by
      ext x
      simpa using hk x
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply] using LinearMap.congr_fun h u

end FacetMarginals

end OpenDisk.PhaseDuality
