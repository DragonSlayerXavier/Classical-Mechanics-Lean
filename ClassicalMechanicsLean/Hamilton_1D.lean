import mathlib 
import ClassicalMechanicsLean.JetSpace_1D
import ClassicalMechanicsLean.Newton_1D

namespace Hamilton1

structure Particle extends Newton1.Particle where 
  Hamiltonian : ℝ → ℝ → ℝ



end Hamilton1