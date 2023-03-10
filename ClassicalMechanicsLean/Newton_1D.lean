import Mathlib 
import ClassicalMechanicsLean.JetSpace_1D


namespace Newton1

--Newton mechanics in ℝ 

/-! Should include hypothesis in the definition of Particle without error.
-/

structure Particle where
  m : ℝ 
  x : Jet.SmoothFunction 1 
  v : Jet.SmoothFunction 1
  --{h : Vector.cons (v.asFunc) Vector.nil = Vector.get x.grad ⟨0, Nat.zero_lt_succ 0⟩}

/-! We then define particle's velocity and acccelaration as given below
-/

def Particle.a (z : Particle) : (ℝ → ℝ) := 
  fun (t : ℝ) => z.v.grad ⟨[t], rfl⟩ 

def Particle.p (z : Particle) : (Jet.SmoothFunction 1) := 
  ⟨fun (t : ℝ^1) => ((z.m)*(z.v.asFunc t)),
   fun (t : ℝ^1) =>
     let result := (Jet.Vector.dot (Vector.cons (z.m) Vector.nil) (z.v.grad t))
     ⟨[result], rfl⟩⟩

structure System (n : ℕ) := 
  particles : Vector Particle n
  Fext : Vector (ℝ → ℝ) n 

/-! Sum of mass of particles in a system
-/

def System.m {n : ℕ} (S : System n) : ℝ :=
  S.particles.map Particle.m |>.toList.sum

/- Initial attempt to define System.m

  match S.particles.toList with
  | [] => 0
  | head :: tail =>
    have h₁ : Nat.succ (List.length tail) = n := by
      trans 
      · apply List.length_cons
      · simp
    have h₂ : n-1 = List.length tail :=
      Nat.pred_eq_of_eq_succ h₁.symm
    head.m + (mSys ⟨⟨tail, h₂.symm⟩, S.Fext⟩)
-/


/-! Sum of momentum of particles in a system
-/

def System.p {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) :=
  ⟨fun t => S.particles.map (fun p => p.m * p.v.asFunc t) |>.toList.sum,
   fun t => S.particles.map (fun p => ⟨[p.m * p.a t], rfl⟩) |>.toList.sum⟩

/-! Velocity and accelaration of centre of mass of a system is defined below
-/

def System.vcom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  ⟨fun t => S.particles.map (fun p => p.v.asFunc t) |>.toList.sum, 
   fun t => S.particles.map (fun p => p.v.grad t) |>.toList.sum⟩ 

/-! Initial attempt at defining velocity of centre of mass

  match S.particles.toList with
  | [] => 0
  | head :: tail =>
    have h₁ : Nat.succ (List.length tail) = n := by
      trans 
      · apply List.length_cons
      · simp
    have h₂ : n-1 = List.length tail :=
      Nat.pred_eq_of_eq_succ h₁.symm
    ⟨ fun (t : ℝ^1) =>
        (((head.m)*(head.v.asFunc t) + (vcom ⟨⟨tail, h₂.symm⟩, S.Fext⟩).asFunc t)/mSys S)
    , fun (t : ℝ^1) =>
        let first : ℝ := (head.m)*((head.v.grad t) : ℝ)
        let second : ℝ := ((vcom ⟨⟨tail, h₂.symm⟩, S.Fext⟩).grad t)
        show ℝ from first + second⟩
  | [] => ⟨0, 0⟩
-/

def System.acom {n : ℕ} (S : System n) : (ℝ → ℝ) :=
  fun (t : ℝ) => (S.vcom.grad ⟨[t], rfl⟩) 

/-! We give two of the most fundmental laws of Newton mechanics
-/  

structure NewtonianSystem  (n : ℕ) extends System n where
  Second_Law : (Fext.toList.sum = fun (t) => m * toSystem.acom t)
  Conservation_of_Momentum : (Fext.toList.sum = ZeroVector) → (toSystem.p.asFunc = 0)

/-! We define the kinetic energy of a particle
-/

def half : ℝ := (1/2 : ℚ)
def Particle.Ek (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*(((z.v.asFunc ⟨[t], rfl⟩) : ℝ)^2)*(half)

/-! We define the potential energy of a particle
-/




end Newton1