import Formalization.Transport.Multiplier

/-! Splitting over the vacuum orbit using only (ZZ) and divisibility of ℝ/ℤ. -/
noncomputable section
namespace GeneralSphereT.Transport
open OpenDisk.PhaseDuality GeneralSphereT.PathAlgebra
variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {F : Type*} [Fintype F] {S A : F → Type*}
variable [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B}
variable {L : FacetRestrictionData (Facet := F) (CAt := S) (BAt := A) d}

@[ext] private structure Extension (m : Multiplier L) where
  closed : d.ker
  phase : Phase

private instance (m : Multiplier L) : Add (Extension m) :=
  ⟨fun x y => ⟨x.closed+y.closed,x.phase+y.phase+m.value (y.closed,x.closed,0)⟩⟩
private instance (m : Multiplier L) : Zero (Extension m) := ⟨⟨0,0⟩⟩
private instance (m : Multiplier L) : Neg (Extension m) :=
  ⟨fun x => ⟨-x.closed,-x.phase-m.value (x.closed,(-x.closed : d.ker),0)⟩⟩

private instance (m : Multiplier L) : AddCommGroup (Extension m) where
  zero_add x := by
    apply Extension.ext
    · exact zero_add _
    · change 0+x.phase+m.value (x.closed,0,0)=x.phase
      simp
  add_zero x := by
    apply Extension.ext
    · exact add_zero _
    · change x.phase+0+m.value (0,x.closed,0)=x.phase
      simp
  add_assoc x y z := by
    apply Extension.ext
    · exact add_assoc _ _ _
    · have h := m.assoc z.closed y.closed x.closed 0
      simp only [AddMonoidHom.mem_ker.mp x.closed.property,add_zero] at h
      change x.phase+y.phase+m.value (y.closed,x.closed,0)+z.phase+
        m.value (z.closed,(x.closed:C)+y.closed,0) = _
      change _ = x.phase+(y.phase+z.phase+m.value (z.closed,y.closed,0))+
        m.value ((y.closed:C)+z.closed,x.closed,0)
      linear_combination (norm := abel) h
  neg_add_cancel x := by
    apply Extension.ext
    · exact neg_add_cancel _
    · change -x.phase - m.value (x.closed,(-x.closed : d.ker),0) +
        x.phase + m.value (x.closed,(-x.closed : d.ker),0) = 0
      abel
  add_comm x y := by
    apply Extension.ext
    · exact add_comm _ _
    · change x.phase+y.phase+m.value (y.closed,x.closed,0) =
        y.phase+x.phase+m.value (x.closed,y.closed,0)
      rw [add_comm x.phase y.phase,m.zz x.closed y.closed 0 x.closed.property y.closed.property]
  nsmul := nsmulRec
  zsmul := zsmulRec

private def includePhase (m : Multiplier L) : Phase →ₗ[ℤ] Extension m :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun p => ⟨0,p⟩
    map_zero' := rfl
    map_add' := fun p q => by
      apply Extension.ext
      · exact (zero_add _).symm
      · change p+q=p+q+m.value (0,0,0)
        simp }

private theorem split_closed (m : Multiplier L) :
    ∃ γ : d.ker → Phase, ∀ z w, γ z + γ w - γ (z+w) = m.value (w,z,0) := by
  have hinj : Function.Injective (includePhase m) := fun _ _ h => congrArg Extension.phase h
  obtain ⟨π,hπ⟩ := (Module.Baer.of_divisible Phase).extension_property
    (includePhase m) hinj (LinearMap.id : Phase →ₗ[ℤ] Phase)
  have retraction (p : Phase) : π (⟨0,p⟩ : Extension m) = p := LinearMap.congr_fun hπ p
  refine ⟨fun z => π ⟨z,0⟩, fun z w => ?_⟩
  have e : (⟨z,0⟩ : Extension m) + ⟨w,0⟩ =
      ⟨z+w,0⟩ + (⟨0,m.value (w,z,0)⟩ : Extension m) := by
    apply Extension.ext
    · exact (add_zero _).symm
    · change 0+0+m.value (w,z,0) = 0+m.value (w,z,0)+m.value (0,(z:C)+w,0)
      simp
  have h := congrArg π e
  simp only [map_add,retraction] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

/-- On the transitive vacuum orbit the multiplier has a single (possibly
nonlocal) primitive table. The hypotheses include precisely the closed
commutator law, rather than a choice of splitting on its stabilizer. -/
theorem exists_global_primitive (m : Multiplier L) (hd : Function.Surjective d) :
    ∃ h : C → B → Phase, ∀ t s a, m.value (t,s,a) =
      h s a + h t (a+d s) - h (s+t) a := by
  choose u hu using hd
  obtain ⟨γ,hγ⟩ := split_closed m
  let z (s : C) (a : B) : d.ker :=
    ⟨u a+s-u (a+d s), by simp [map_sub,map_add,hu]⟩
  refine ⟨fun s a => m.value (s,u a,0) - m.value (u (a+d s),z s a,0) + γ (z s a),?_⟩
  intro t s a
  have hb : a+d (s+t) = a+d s+d t := by rw [map_add,add_assoc]
  have h₁ := m.assoc t s (u a) 0
  rw [hu,zero_add] at h₁
  have h₂ := m.assoc t (u (a+d s)) (z s a) 0
  have h₃ := m.assoc (u (a+d s+d t)) (z t (a+d s)) (z s a) 0
  have hc : d (z s a) = 0 := (z s a).property
  simp only [hc,add_zero] at h₂ h₃
  have A₁ : (z s a : C)+u (a+d s) = u a+s := sub_add_cancel _ _
  have A₂ : (z t (a+d s) : C)+u (a+d s+d t) = u (a+d s)+t := sub_add_cancel _ _
  have A₃ : z s a+z t (a+d s) = z (s+t) a := by
    apply Subtype.ext
    change u a+s-u (a+d s)+(u (a+d s)+t-u (a+d s+d t))=u a+(s+t)-u (a+d (s+t))
    rw [hb]; abel
  have A₄ : (z s a : C)+(z t (a+d s):C)=(z (s+t) a:C) := congrArg Subtype.val A₃
  rw [A₁] at h₂
  rw [A₂,A₄] at h₃
  have h₄ := hγ (z s a) (z t (a+d s))
  rw [A₃] at h₄
  dsimp only
  rw [hb]
  linear_combination (norm := abel) -h₁ + h₂ - h₃ - h₄

end GeneralSphereT.Transport

