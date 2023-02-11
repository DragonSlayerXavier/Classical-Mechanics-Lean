import Mathlib

namespace Newton

variable {m : ℝ} {F : ℝ} {x : ℝ} {t : ℝ}

def v : ℝ := diff x t

def a : ℝ := diff v t

def p : ℝ := m * v

def F : ℝ := m * a

axiom m_pos : 0 < m

axiom conservation_of_momentum : F = 0 → p = p

axiom second_law : F = m * a

theorem first_law : F = 0 → v = v := by simp [F, v, a, p, conservation_of_momentum, second_law]

end Newton