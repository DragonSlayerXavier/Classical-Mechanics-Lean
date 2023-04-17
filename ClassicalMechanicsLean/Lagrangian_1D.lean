import Mathlib 
import ClassicalMechanicsLean.JetSpace_1D
import ClassicalMechanicsLean.Integral_1D
import ClassicalMechanicsLean.Newton_1D

namespace Lagrange1

/-
## Lagrangian Mechanics in 1D
-/

/--
A particle in the Lagrangian system has the same properties as one in the Newtonian system with
one additional property: Potential Energy.
-/
structure Particle extends Newton1.Particle where
  V : Jet.SmoothFunction 1

/--The value 1/2 as a real-/
def half : ℝ := (1/2 : ℚ )

/--Velocity of the particle, raised to the power n-/
def Particle.v_pow (z : Particle) (n : ℕ) : Jet.SmoothFunction 1 :=
  ⟨fun (t : ℝ^1) => ((z.v.asFunc t) : ℝ)^n,
   fun t => ⟨[(n : ℝ) * ((z.v.asFunc t) : ℝ)* ((z.v.asFunc t) : ℝ)], rfl⟩⟩

/--Kinetic energy of the particle-/
def Particle.Ek (z : Particle) : Jet.SmoothFunction 1 :=
  ⟨fun (t : ℝ^1) => ((Jet.SmoothFunction.const 1 z.m).asFunc t)*((z.v_pow 2).asFunc t)*((Jet.SmoothFunction.const 1 half).asFunc t),
   fun (t : ℝ^1) => ⟨[((Jet.SmoothFunction.const 1 z.m).asFunc t)*(((z.v_pow 2).grad t) : ℝ)*((Jet.SmoothFunction.const 1 half).asFunc t)], rfl⟩
  ⟩

/--The Lagrangian of a particle-/
def Particle.L (z : Particle) : Jet.SmoothFunction 1 := z.Ek - z.V

/--Integral of the Lagrangian over time is called action-/
def Particle.Action (z : Particle) [int : Integrable z.L]: (ℝ → ℝ)  :=
  fun (t : ℝ) => (int.integral 0 t)

/--The lagrangian differentiated wrt velocity-/
def Particle.Deriv_L_v (z : Particle) : Jet.SmoothFunction 1 :=
  ⟨fun (t : ℝ^1) => (z.m)*(z.v.asFunc t), 
   fun (t : ℝ^1) => ⟨[(z.m)*((z.v.grad t) : ℝ)], rfl⟩
  ⟩
/--The Lagrangian differentiated wrt position-/
def Particle.Deriv_L_x (z : Particle) : ℝ^1 → ℝ :=
  fun (x : ℝ^1) => (z.m)*(z.V.grad x)

/--A Langrangian System is one which follows the Euler-Lagrange Equation-/
structure LagrangianSystem extends Particle where 
  EulerLagrange_Equation : (fun (z : Particle) => ((fun (x : ℝ^1) => ⟨[z.Deriv_L_x x], rfl⟩))) = (fun (z : Particle) => (fun t => (z.Deriv_L_v.grad t)))

