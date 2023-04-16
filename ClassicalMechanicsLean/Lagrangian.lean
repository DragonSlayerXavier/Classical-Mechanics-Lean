import Mathlib 
import ClassicalMechanicsLean.JetSpace_1D
import ClassicalMechanicsLean.Integral
--import ClassicalMechanicsLean.Newton_1D

namespace Lagrange1

/-
## Lagrangian Mechanics in 1D
-/

structure Particle where
  m : ℝ 
  x : Jet.SmoothFunction 1 
  v : Jet.SmoothFunction 1
  V : Jet.SmoothFunction 1

def half : ℝ := (1/2 : ℚ )

def prod_half (n : ℕ) : ℝ := ((n : ℚ) * (1/2 : ℚ))

def two_prod_half : 1 = prod_half 2 := by
 simp[prod_half]

def Particle.Ek (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*(((z.v.asFunc ⟨[t], rfl⟩) : ℝ)^2)*(half)

def Particle.L (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.Ek t) - ((z.V.asFunc ⟨[t], rfl⟩) : ℝ)

def Particle.Action (z : Particle) [int : Integrable z.L]: (ℝ → ℝ)  :=
  fun (t : ℝ) => (int.integral 0 t)

def Particle.Ek'_v (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*((z.v.asFunc ⟨[t], rfl⟩) : ℝ)

def Particle.Ek'_v_t (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*((z.v.grad ⟨[t], rfl⟩) : ℝ)

structure LagrangianSystem extends Particle where 
  EulerLagrange_Equation : fun (z : Particle) => ((fun (x : ℝ^1) => z.V.grad x) : (ℝ^1 → ℝ)) = ((fun t => z.Ek'_v_t t): (ℝ^1 → ℝ))
