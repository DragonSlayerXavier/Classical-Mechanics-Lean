import Mathlib 
import ClassicalMechanicsLean.JetSpace_1D
import ClassicalMechanicsLean.Integral
import ClassicalMechanicsLean.Newton_1D

namespace Lagrange1

/-
## Lagrangian Mechanics in 1D
-/

structure Particle extends Newton1.Particle where
  V : Jet.SmoothFunction 1

def half : ℝ := (1/2 : ℚ )

def prod_half (n : ℕ) : ℝ := ((n : ℚ) * (1/2 : ℚ))

def two_prod_half : 1 = prod_half 2 := by
 simp[prod_half]

def Particle.v_pow (z : Particle) (n : ℕ) : Jet.SmoothFunction 1 :=
  ⟨fun (t : ℝ^1) => ((z.v.asFunc t) : ℝ)^n,
   fun t => ⟨[(n : ℝ) * ((z.v.asFunc t) : ℝ)* ((z.v.asFunc t) : ℝ)], rfl⟩⟩

def Particle.Ek (z : Particle) : Jet.SmoothFunction 1 :=
  ⟨fun (t : ℝ^1) => ((Jet.SmoothFunction.const 1 z.m).asFunc t)*((z.v_pow 2).asFunc t)*((Jet.SmoothFunction.const 1 half).asFunc t),
   fun (t : ℝ^1) => ⟨[((Jet.SmoothFunction.const 1 z.m).asFunc t)*(((z.v_pow 2).grad t) : ℝ)*((Jet.SmoothFunction.const 1 half).asFunc t)], rfl⟩
  ⟩

def Particle.L (z : Particle) : Jet.SmoothFunction 1 := z.Ek - z.V


def Particle.Action (z : Particle) [int : Integrable z.L]: (ℝ → ℝ)  :=
  fun (t : ℝ) => (int.integral 0 t)

def Particle.Ek'_v (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*((z.v.asFunc ⟨[t], rfl⟩) : ℝ)

def Particle.Ek'_v_t (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*((z.v.grad ⟨[t], rfl⟩) : ℝ)

structure LagrangianSystem extends Particle where 
  EulerLagrange_Equation : (fun (z : Particle) => ((fun (x : ℝ) => z.V.grad ⟨[x],rfl⟩))) = (fun (z : Particle) => (fun t => ⟨[z.Ek'_v_t t],rfl⟩))

