import Mathlib 
import ClassicalMechanicsLean.JetSpace_nD


namespace Newton_nD

--Newton mechanics in ℝ 

/-! Should include hypothesis in the definition of Particle without error.
-/

local infixl:arg (priority := high) "^" => Vector

/--
A particle is defined to be a structre with mass, position, velocity and a force acting on it.
-/
structure Particle (n : ℕ) where
  m : ℝ 
  x : SmoothFunction 1 n 
  v : SmoothFunction 1 n
  F : ℝ^n → ℝ^n 

/--
The acceleration of the particle is defined to be the gradient of the velocity with respect to time.
It is a vector, represented by a column matrix. 
-/
def Particle.a {n : ℕ} (z : Particle n) : (ℝ → Matrix' n 1 ℝ) := 
  fun (t : ℝ) => (z.v.grad ⟨[t], rfl⟩)

/--
The momentum of a particle is a SmoothFunction.
It is defined to be the mass times velocity of the given particle.
-/
def Particle.p {n : ℕ} (z : Particle n) : (SmoothFunction 1 n) := 
  ⟨fun (t : ℝ^1) => ((z.v.asFunc t).map ((z.m)*·)),
   fun (t : ℝ^1) => ((z.a (t[0])).map ((z.m)*·)),
   sorry
  ⟩

/--
System of n particles is defined to be a vector
-/
structure System (n : ℕ) (m : ℕ) := 
  particles : Vector (Particle n) m

/-- Sum of mass of particles in a system
-/

def System.m {n : ℕ} {m : ℕ} (S : System n m) : ℝ :=
  S.particles.map Particle.m |>.toList.sum

/--The total external force acting on a system
-/

def System.F {n : ℕ} {m : ℕ} (S : System n m) : (ℝ^n → ℝ^n) :=
  fun (x : ℝ^n) => S.particles.map (fun  z => z.F x) |>.toList.sum

/-- Sum of momentum of particles in a system
-/

def System.p {n : ℕ} {m : ℕ} (S : System n m) : (SmoothFunction 1 n) :=
  ⟨fun t => S.particles.map (fun z => (z.v.asFunc t).map ((z.m)*·)) |>.toList.sum,
   fun t => S.particles.map (fun z => ((z.a (t[0])).map ((z.m)*·)))|>.toList.sum, sorry⟩

/--
Velocity of the Centre of Mass of a system
Declaration uses sorry due to lack of proof of existence of the gradient.
-/
noncomputable def System.vcom {n : ℕ} {m : ℕ} (S : System n m) : (SmoothFunction 1 n) := 
  ⟨fun t => S.particles.map (fun z => (1/S.m)•(z.v.asFunc t)) |>.toList.sum, 
   fun t => S.particles.map (fun z => (1/S.m)•(z.v.grad t)) |>.toList.sum,
   sorry⟩ 

/--
Acceleration of the Centre of Mass of a system.
-/
noncomputable def System.acom {n : ℕ} {m : ℕ} (S : System n m) : (ℝ → Matrix' n 1 ℝ) :=
  fun t => S.particles.map (fun z => (1/S.m)•(z.v.grad t)) |>.toList.sum

/--A Newtonian System follows Newton's second law and has conservation of momentum-/
structure NewtonianSystem (n : ℕ) (m : ℕ) extends System n m where 
  Second_Law : (fun (x : ℝ^n) => fun (t : ℝ) => Matrix'.col (toSystem.F x)) = (fun x: ℝ^n => (fun t : ℝ => ((toSystem.m)•(toSystem.acom t))))
  Conservation_of_Momentum :=  (toSystem.F = 0) → (toSystem.p.grad = 0)


/--The value 1/2 as a real number-/
def half : ℝ := (1/2 : ℚ)

/--The Kinetic Energy of a particle.-/
def Particle.Ek {n : ℕ} (z : Particle n) : (ℝ → ℝ) :=
  fun (t : ℝ) => (Vector.map₂ (· * ·) (z.v.asFunc ⟨[t], rfl⟩) (z.v.asFunc ⟨[t], rfl⟩)).toList.sum * (z.m) * (half)

/-! We define the potential energy of a particle
-/




end Newton_nD