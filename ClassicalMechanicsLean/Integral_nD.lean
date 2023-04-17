import Mathlib 
import ClassicalMechanicsLean.JetSpace_nD

/-!
# Formal Calculus
We introduce formal structures for integration and differentiation. Properties should be added to make these mathematically sound. But correctness can be ensured temporarily by making sure individual definitions are correct.
## Formal Integrals
-/

notation(priority:=high) x:85 "^" y:85 => Vector x y

/--
Integrability of `f`, i.e., given an interval `[a, b]`, we can compute the integral of `f` over that interval. Additivity over intervals is also required.
-/
class Integrable {n: ℕ} (f: (ℝ^n) → ℝ) where
  integral (a b : (ℝ^n)) : ℝ  
  interval_union (a b c : (ℝ^n)) :
    integral a c = integral a b + integral b c

/-- The integral of a function, with the typeclass derived -/
def integral (f: ℝ^n → ℝ)[int : Integrable f]
  (a b : ℝ^n ) :=
  int.integral a b

/-- The integral over a single point is zero, proved as an illustration. -/
theorem integral_point(f: ℝ^n → ℝ)[int : Integrable f]
  (a : ℝ^n ) : integral f a a = 0 := by
    unfold integral
    have l := int.interval_union a a a
    simp  at l
    assumption

/--

-/
theorem integral_flip (f : ℝ^n → ℝ) [int : Integrable f]
  (a b : ℝ^n) : integral f a b = - integral f b a := by
    unfold integral
    have lem1 : int.integral a b + int.integral b a = 0 := by
      trans
      · rw [<- int.interval_union a b a]
      · apply integral_point f a 
    have lem2 : int.integral a b = 0 - int.integral b a := by
      apply eq_zero_sub_of_add_eq_zero_left lem1 
    simp at lem2
    apply lem2

instance fundThm {n : ℕ} {m : ℕ} (f: Jet.SmoothFunction n m) :
  Integrable (f.grad) where
  integral (a b) := f.value b - f.value a
  interval_union (a b c) := by
    simp [integral]