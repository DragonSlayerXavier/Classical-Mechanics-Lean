import Mathlib 
import ClassicalMechanicsLean.JetSpace_1D
import ClassicalMechanicsLean.Integral_1D


namespace Newton1

/-# Newton mechanics in ℝ 
-/


/--
A particle is defined as a structure with mass, position, velocity and an external force acting on it.
-/
structure Particle where
  m : ℝ 
  x : Jet.SmoothFunction 1 
  v : Jet.SmoothFunction 1
  F : ℝ^1 → ℝ

/--
Acceleration of a particle is defined as the gradient of its velocity at a given time.
-/
def Particle.a (z : Particle) : (ℝ → ℝ) := 
  fun (t : ℝ) => z.v.grad ⟨[t], rfl⟩ 

/--Momentum of a particle is the product of its mass and velocity-/
def Particle.p (z : Particle) : (Jet.SmoothFunction 1) := 
  ⟨fun (t : ℝ^1) => ((z.m)*(z.v.asFunc t)),
   fun (t : ℝ^1) =>
     let result := (Jet.Vector.dot (Vector.cons (z.m) Vector.nil) (z.v.grad t))
     ⟨[result], rfl⟩⟩

/--A system is a vector of particles.-/
structure System (n : ℕ) := 
  particles : Vector Particle n

/-- Total mass of particles in a system
-/
def System.m {n : ℕ} (S : System n) : ℝ :=
  S.particles.map Particle.m |>.toList.sum

/--
The total external force acting on the system is the sum of the forces acting on the particles.
-/
def System.Fext {n : ℕ} (S : System n) : ℝ^1 → ℝ :=
  S.particles.map Particle.F |>.toList.sum

/-- Sum of momentum of particles in a system
-/
def System.p {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) :=
  ⟨fun t => S.particles.map (fun p => p.m * p.v.asFunc t) |>.toList.sum,
   fun t => S.particles.map (fun p => ⟨[p.m * p.a t], rfl⟩) |>.toList.sum⟩

/--The velocity of the system's centre of mass-/
noncomputable def System.vcom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  ⟨fun t => S.p.asFunc t / S.m, fun t => Vector.cons (S.p.grad t / S.m) Vector.nil⟩ 

/--The acceleration of the system's centre of mass is the gradient of the velocity of the same.-/
noncomputable def System.acom {n : ℕ} (S : System n) : (ℝ → ℝ) :=
  fun (t : ℝ) => (S.vcom.grad ⟨[t], rfl⟩) 

/--
A Newtonian System is one with the second law and conservation of momentum.
-/
structure NewtonianSystem  (n : ℕ) extends System n where
  Second_Law : fun (x : ℝ^1) => toSystem.particles.map (fun p => p.F x) |>.toList.sum = fun (x : ℝ^1) => m * toSystem.acom x
  Conservation_of_Momentum : (toSystem.Fext = 0) → (toSystem.p.grad = 0)


/--The value 1/2 as a real-/
def half : ℝ := (1/2 : ℚ)

/--The kinetic energy of a particle.-/
def Particle.Ek (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*(((z.v.asFunc ⟨[t], rfl⟩) : ℝ)^2)*(half)

/-- The potential energy of a particle
-/

def Particle.Ep (a b : ℝ) (z : Particle) [int : Integrable (z.F : (ℝ → ℝ))] : ℝ := 
  int.integral a b
  
--theorem Particle.Work_Energy_theorem (a b : ℝ) (z : Particle) 





end Newton1