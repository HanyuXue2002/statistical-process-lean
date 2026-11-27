import Formalization.OpenDisk.WindowClosedWords
import Formalization.OpenDisk.WindowRegionalSupport
import Formalization.OpenDisk.WordOperators

/-!
# Legal hopping blocks and the regional window invariant

These results allow arbitrarily many legal phase rows with the same increment.
No fusion relation identifying those rows is imposed. A closed same-carrier
block and a two-letter swap defect are genuinely marked, closed, and supported
in the region whenever their actual conjugated operators are supported there.
-/

noncomputable section
namespace OpenDisk.Window
open GeneralSphereT.PathAlgebra

variable {ι G B Facet : Type*} [LinearOrder ι] [Fintype ι] [AddCommGroup G]
  [AddCommGroup B] [Fintype Facet]

theorem phaseFusion_matching (d : Configuration ι G →+ B)
    (β L M : Configuration ι G → CirclePhase) (s t : Configuration ι G)
    (hL : Matching d β L s) (hM : Matching d β M t) :
    Matching d β (fun c => L c + M (c+s)) (s+t) := by
  intro z c
  calc
    difference (fun c => L c + M (c+s)) z c =
        difference L z c + difference M z (c+s) := by
      simp only [difference]
      rw [show c + z + s = c+s+z by abel]
      abel
    _ = difference (difference β z) s c + difference (difference β z) t (c+s) := by
      rw [hL,hM]
    _ = difference (difference β z) (s+t) c := by
      simp only [difference,add_assoc]
      abel

theorem hoppingWord_matching (d : Configuration ι G →+ B)
    (β : Configuration ι G → CirclePhase) (word : List (HoppingStep (Configuration ι G)))
    (h : ∀ a ∈ word, Matching d β a.1 a.2) :
    Matching d β (hoppingWordPhase word) (hoppingWordIncrement word) := by
  induction word with
  | nil => intro z c; simp [hoppingWordPhase,hoppingWordIncrement,difference]
  | cons a word ih =>
      exact phaseFusion_matching d β a.1 (hoppingWordPhase word) a.2
        (hoppingWordIncrement word) (h a List.mem_cons_self)
        (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem hoppingWord_closed_phase (d : Configuration ι G →+ B)
    (β : Configuration ι G → CirclePhase) (word : List (HoppingStep (Configuration ι G)))
    (h : ∀ a ∈ word, Matching d β a.1 a.2) (hc : hoppingWordIncrement word = 0) :
    phaseDerivative d (hoppingWordPhase word) = 0 := by
  ext z c
  have hh := hoppingWord_matching d β word h z c
  rw [hc,difference_zero] at hh
  exact hh

theorem hoppingWord_supported {R : Set ι} (word : List (HoppingStep (Configuration ι G)))
    (h : ∀ a ∈ word, SupportedOn R a.1) : SupportedOn R (hoppingWordPhase word) := by
  induction word with
  | nil => intro c c' heq; rfl
  | cons a word ih =>
      intro c c' heq
      have h₁ := h a List.mem_cons_self c c' heq
      have h₂ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) (c+a.2) (c'+a.2)
        (fun i hi => by simp [heq i hi])
      exact congrArg₂ (· + ·) h₁ h₂

theorem hoppingWord_sameCarrier_marked (facets : Facet → Set ι) (i : ι)
    (word : List (HoppingStep (Configuration ι G)))
    (h : ∀ a ∈ word, MarkedLocal facets {i} a.1) :
    MarkedLocal facets {i} (hoppingWordPhase word) := by
  induction word with
  | nil => exact (localFunctionSubgroup (G := G) (markedFacets facets {i}) CirclePhase).zero_mem
  | cons a word ih =>
      have ht := translate_local (markedFacets facets {i})
        (ih (fun b hb => h b (List.mem_cons_of_mem _ hb))) a.2
      have heq : hoppingWordPhase (a::word) = a.1 + (fun c => hoppingWordPhase word (a.2+c)) := by
        funext c; simp [hoppingWordPhase,add_comm]
      rw [heq]
      exact (localFunctionSubgroup (G := G) (markedFacets facets {i}) CirclePhase).add_mem
        (h a List.mem_cons_self) ht

def gaugeHoppingStep (φ : Configuration ι G → CirclePhase)
    (a : HoppingStep (Configuration ι G)) : HoppingStep (Configuration ι G) :=
  (a.1 + difference φ a.2,a.2)

@[simp] theorem gauge_word_increment (φ : Configuration ι G → CirclePhase)
    (word : List (HoppingStep (Configuration ι G))) :
    hoppingWordIncrement (word.map (gaugeHoppingStep φ)) = hoppingWordIncrement word := by
  induction word <;> simp [hoppingWordIncrement,gaugeHoppingStep,*]

theorem gauge_word_phase (φ : Configuration ι G → CirclePhase)
    (word : List (HoppingStep (Configuration ι G))) (c : Configuration ι G) :
    hoppingWordPhase (word.map (gaugeHoppingStep φ)) c =
      hoppingWordPhase word c + difference φ (hoppingWordIncrement word) c := by
  induction word generalizing c with
  | nil => simp [hoppingWordPhase,hoppingWordIncrement]
  | cons a word ih =>
      simp only [List.map_cons,hoppingWordPhase,gaugeHoppingStep,Pi.add_apply,
        hoppingWordIncrement,ih,difference,add_assoc]
      abel

theorem closed_word_gauge_cancels (φ : Configuration ι G → CirclePhase)
    (word : List (HoppingStep (Configuration ι G))) (hc : hoppingWordIncrement word = 0) :
    hoppingWordPhase (word.map (gaugeHoppingStep φ)) = hoppingWordPhase word := by
  funext c
  simp [gauge_word_phase,hc]

theorem square_marked (facets : Facet → Set ι)
    {L M : Configuration ι G → CirclePhase} {i j : ι}
    (hL : MarkedLocal facets {i} L) (hM : MarkedLocal facets {j} M) (g h : G) :
    MarkedLocal facets {i}
      (fun c => difference M (Finsupp.single i g) c - difference L (Finsupp.single j h) c) := by
  exact (localFunctionSubgroup (G := G) (markedFacets facets {i}) CirclePhase).sub_mem
    (derivative_marked facets (marked_local hM) i g)
    (difference_local (markedFacets facets {i}) hL _)

theorem square_closed (d : Configuration ι G →+ B)
    (β L M : Configuration ι G → CirclePhase) (s t : Configuration ι G)
    (hL : Matching d β L s) (hM : Matching d β M t) :
    phaseDerivative d (fun c => difference M s c - difference L t c) = 0 := by
  ext z c
  change difference (difference M s - difference L t) z c = 0
  rw [difference_sub,difference_comm M s z,difference_comm L t z]
  have hm : difference M z = difference (difference β z) t := funext (hM z)
  have hl : difference L z = difference (difference β z) s := funext (hL z)
  rw [hm,hl,difference_comm (difference β z) t s,sub_self]

theorem square_supported_of_gauge {R : Set ι} (φ L M : Configuration ι G → CirclePhase)
    (s t : Configuration ι G) (hL : SupportedOn R (L+difference φ s))
    (hM : SupportedOn R (M+difference φ t)) :
    SupportedOn R (fun c => difference M s c - difference L t c) := by
  have hg (c : Configuration ι G) :
      difference (M+difference φ t) s c - difference (L+difference φ s) t c =
        difference M s c - difference L t c := by
    simp only [difference_add]
    rw [difference_comm φ t s]
    abel
  intro c c' heq
  rw [← hg c,← hg c']
  have hm₀ := hM c c' heq
  have hm₁ := hM (c+s) (c'+s) (fun i hi => by simp [heq i hi])
  have hl₀ := hL c c' heq
  have hl₁ := hL (c+t) (c'+t) (fun i hi => by simp [heq i hi])
  simp only [difference,hm₀,hm₁,hl₀,hl₁]

end OpenDisk.Window
