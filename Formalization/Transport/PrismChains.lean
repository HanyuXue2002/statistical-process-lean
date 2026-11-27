import Formalization.Transport.Multiplier

/-! Oriented staircase triangulations of the interval, triangle and
tetrahedron times a spatial simplex.  Chains on vertex lists include the
empty simplex. Consecutive equal vertices may subsequently be killed by a
normalized cochain. The spatial degree is arbitrary. -/
noncomputable section
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality
variable {X Y : Type*}
abbrev Chains (X : Type*) := Distribution (List X)
def gen (xs : List X) : Chains X := Finsupp.single xs 1
def extend (h : List X → Chains Y) : Chains X →ₗ[ℤ] Chains Y := Finsupp.linearCombination ℤ h
@[simp] theorem extend_gen (h : List X → Chains Y) (xs : List X) : extend h (gen xs) = h xs := by
  simp [extend,gen]

def cons (x : X) : Chains X →ₗ[ℤ] Chains X := extend (fun xs => gen (x::xs))
@[simp] theorem cons_gen (x : X) (xs : List X) : cons x (gen xs) = gen (x::xs) := extend_gen _ _

def faces : List X → Chains X
  | [] => 0
  | x::xs => gen xs - cons x (faces xs)
def boundary : Chains X →ₗ[ℤ] Chains X := extend faces
@[simp] theorem boundary_gen (xs : List X) : boundary (gen xs) = faces xs := extend_gen _ _

private theorem on_generators {f g : Chains X →ₗ[ℤ] Chains Y} (h : ∀ xs, f (gen xs) = g (gen xs)) :
    f=g := by
  apply Finsupp.lhom_ext'
  intro xs
  apply LinearMap.ext_ring
  exact h xs

theorem boundary_cons (x : X) (c : Chains X) : boundary (cons x c) = c - cons x (boundary c) := by
  have eq : boundary.comp (cons x) = LinearMap.id - (cons x).comp boundary := by
    apply on_generators
    intro xs
    simp [faces]
  exact LinearMap.congr_fun eq c

def vertices (f : X → Y) : Chains X →ₗ[ℤ] Chains Y := extend (fun xs => gen (xs.map f))
@[simp] theorem vertices_gen (f : X → Y) (xs : List X) :
    vertices f (gen xs) = gen (xs.map f) := extend_gen _ _
theorem vertices_cons (f : X → Y) (x : X) (c : Chains X) :
    vertices f (cons x c) = cons (f x) (vertices f c) := by
  have eq : (vertices f).comp (cons x) = (cons (f x)).comp (vertices f) := by
    apply on_generators
    intro xs
    simp
  exact LinearMap.congr_fun eq c

theorem boundary_vertices (f : X → Y) (z : Chains X) : boundary (vertices f z) = vertices f (boundary z) := by
  have eq : boundary.comp (vertices f) = (vertices f).comp boundary := by
    apply on_generators
    intro xs
    change boundary (vertices f (gen xs)) = vertices f (boundary (gen xs))
    induction xs with
    | nil => simp [faces]
    | cons x xs ih =>
      simp only [vertices_gen,boundary_gen] at ih
      simp [faces,vertices_cons,ih]
  exact LinearMap.congr_fun eq z

/-- Each vertical step occurs at a spatial vertex. Moving a spatial step
before k vertical steps contributes the shuffle sign (-1)^k. -/
def segmentList (a b : X → Y) : List X → Chains Y
  | [] => 0
  | x::xs => cons (a x) (gen ((x::xs).map b)) - cons (a x) (segmentList a b xs)
def segment (a b : X → Y) := extend (segmentList a b)

def triangleList (a b c : X → Y) : List X → Chains Y
  | [] => 0
  | x::xs => cons (a x) (segmentList b c (x::xs)) + cons (a x) (triangleList a b c xs)
def triangle (a b c : X → Y) := extend (triangleList a b c)

def tetraList (a b c d : X → Y) : List X → Chains Y
  | [] => 0
  | x::xs => cons (a x) (triangleList b c d (x::xs)) - cons (a x) (tetraList a b c d xs)
def tetra (a b c d : X → Y) := extend (tetraList a b c d)

theorem segment_cons (a b : X → Y) (x : X) (z : Chains X) :
    segment a b (cons x z) = cons (a x) (cons (b x) (vertices b z)) - cons (a x) (segment a b z) := by
  have eq : (segment a b).comp (cons x) =
      (cons (a x)).comp ((cons (b x)).comp (vertices b)) - (cons (a x)).comp (segment a b) := by
    apply on_generators
    intro xs
    simp [segment,segmentList]
  exact LinearMap.congr_fun eq z

theorem triangle_cons (a b c : X → Y) (x : X) (z : Chains X) :
    triangle a b c (cons x z) = cons (a x) (segment b c (cons x z)) + cons (a x) (triangle a b c z) := by
  have eq : (triangle a b c).comp (cons x) =
      (cons (a x)).comp ((segment b c).comp (cons x)) + (cons (a x)).comp (triangle a b c) := by
    apply on_generators
    intro xs
    simp [segment,triangle,triangleList]
  exact LinearMap.congr_fun eq z

theorem tetra_cons (a b c d : X → Y) (x : X) (z : Chains X) :
    tetra a b c d (cons x z) = cons (a x) (triangle b c d (cons x z)) - cons (a x) (tetra a b c d z) := by
  have eq : (tetra a b c d).comp (cons x) =
      (cons (a x)).comp ((triangle b c d).comp (cons x)) - (cons (a x)).comp (tetra a b c d) := by
    apply on_generators
    intro xs
    simp [tetra,tetraList,triangle]
  exact LinearMap.congr_fun eq z

theorem boundary_segment (a b : X → Y) (z : Chains X) :
    boundary (segment a b z) = vertices b z - vertices a z - segment a b (boundary z) := by
  have E : boundary.comp (segment a b) = vertices b - vertices a - (segment a b).comp boundary := by
    apply on_generators
    intro xs
    change boundary (segment a b (gen xs)) = vertices b _ - vertices a _ - segment a b (boundary (gen xs))
    induction xs with
    | nil => simp [segment,segmentList,faces]
    | cons x xs ih =>
      rw [← cons_gen]
      simp only [segment_cons,map_sub,boundary_cons,vertices_cons,boundary_vertices,ih]
      abel
  exact LinearMap.congr_fun E z

set_option maxHeartbeats 1200000 in
theorem boundary_triangle (a b c : X → Y) (z : Chains X) :
    boundary (triangle a b c z) = segment b c z - segment a c z + segment a b z + triangle a b c (boundary z) := by
  have E : boundary.comp (triangle a b c) =
      segment b c - segment a c + segment a b + (triangle a b c).comp boundary := by
    apply on_generators
    intro xs
    change boundary (triangle a b c (gen xs)) = segment b c _ - segment a c _ + segment a b _ + triangle a b c (boundary (gen xs))
    induction xs with
    | nil => simp [triangle,triangleList,segment,segmentList,faces]
    | cons x xs ih =>
      rw [← cons_gen]
      rw [triangle_cons,map_add,boundary_cons,boundary_cons,boundary_segment,ih]
      simp only [boundary_cons,vertices_cons,map_sub,map_add]
      rw [segment_cons a c,segment_cons a b,triangle_cons]
      try simp only [map_sub,map_add]
      abel
  exact LinearMap.congr_fun E z

set_option maxHeartbeats 1200000 in
theorem boundary_tetra (a b c d : X → Y) (z : Chains X) :
    boundary (tetra a b c d z) =
      triangle b c d z - triangle a c d z + triangle a b d z - triangle a b c z - tetra a b c d (boundary z) := by
  have E : boundary.comp (tetra a b c d) =
      triangle b c d - triangle a c d + triangle a b d - triangle a b c - (tetra a b c d).comp boundary := by
    apply on_generators
    intro xs
    change boundary (tetra a b c d (gen xs)) = triangle b c d _ - triangle a c d _ + triangle a b d _ -
      triangle a b c _ - tetra a b c d (boundary (gen xs))
    induction xs with
    | nil => simp [tetra,tetraList,triangle,triangleList,faces]
    | cons x xs ih =>
      rw [← cons_gen]
      rw [tetra_cons,map_sub,boundary_cons,boundary_cons,boundary_triangle,ih]
      simp only [boundary_cons,map_sub,map_add]
      rw [triangle_cons a c d,triangle_cons a b d,triangle_cons a b c,tetra_cons]
      try simp only [map_sub,map_add]
      abel
  exact LinearMap.congr_fun E z

/-- Pairing a spatial cycle with the four temporal faces of a tetrahedron
gives zero for every cocycle on the target. -/
theorem temporal_cocycle (ω : Chains Y →ₗ[ℤ] Phase) (closed : ω.comp boundary = 0)
    (z : Chains X) (hz : boundary z = 0) (a b c d : X → Y) :
    ω (triangle a b c z) + ω (triangle a c d z) =
      ω (triangle b c d z) + ω (triangle a b d z) := by
  have E := LinearMap.congr_fun closed (tetra a b c d z)
  simp only [LinearMap.comp_apply,LinearMap.zero_apply,boundary_tetra,hz,map_zero,map_sub,map_add] at E
  linear_combination (norm := abel) -E

/-- Evaluating a coboundary on the actual triangle product gives the same
one-edge rephasing at all three sides, including the minus sign of (2.8). -/
theorem temporal_coboundary (θ : Chains Y →ₗ[ℤ] Phase) (z : Chains X)
    (hz : boundary z=0) (a b c : X → Y) :
    -(θ.comp boundary) (triangle a b c z) =
      (-θ (segment a b z)) + (-θ (segment b c z)) - (-θ (segment a c z)) := by
  simp only [LinearMap.comp_apply,boundary_triangle,hz,map_zero,add_zero,map_add,map_sub]
  abel

end GeneralSphereT.Transport.Prism

