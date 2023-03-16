import Mathlib
import ClassicalMechanicsLean.JetSpace_1D
/-!
# Formal Calculus
We introduce formal structures for integration and differentiation. Properties should be added to make these mathematically sound. But correctness can be ensured temporarily by making sure individual definitions are correct.
## Formal Integrals
-/

/--
Integrability of `f`, i.e., given an interval `[a, b]`, we can compute the integral of `f` over that interval. Additivity over intervals is also required.
-/
class Integrable (f: ℝ → ℝ) where
  integral (a b : ℝ) : ℝ  
  interval_union (a b c : ℝ) :
    integral a c = integral a b + integral b c

/-- The integral of a function, with the typeclass derived -/
def integral (f: ℝ → ℝ)[int : Integrable f]
  (a b : ℝ ) :=
  int.integral a b

/-- The integral over a single point is zero, proved as an illustration. -/
theorem integral_point(f: ℝ → ℝ)[int : Integrable f]
  (a : ℝ ) : integral f a a = 0 := by
    unfold integral
    have l := int.interval_union a a a
    simp  at l
    assumption

/-!
As an exercise, prove that flip ends of an interval gives the negative of the integral.
-/

theorem integral_flip (f : ℝ → ℝ) [int : Integrable f]
  (a b : ℝ ) : integral f a b = - integral f b a := by
    unfold integral
    have l := int.interval_union a b b
    have lem1 : int.integral a b + int.integral b a = 0 := by
      trans
      · rw [<- int.interval_union a b a]
      · apply integral_point f a 
    have lem2 : int.integral a b = 0 - int.integral b a := by
      apply eq_zero_sub_of_add_eq_zero_left lem1 
    simp at lem2
    apply lem2
    

/-!
## Formal Derivatives
We define so called __one-jets__ as a value and a derivative at a point. A differentiable function has values a one-jet at each point.
-/

/--
A _one-jet_ is a value and a derivative at a point.
-/
structure OneJet where
  value : ℝ
  derivative : ℝ

/--
A differentiable function is a function that has a one-jet at each point.
-/
structure SmoothFunction where
  jet: ℝ → OneJet 

/--
Derivative of a smooth function, i.e., the derivative of the one-jet at a point.
-/
def Jet.SmoothFunction.derivative (f: Jet.SmoothFunction 1) : ℝ → ℝ := 
  fun x => f.grad (Vector.cons x Vector.nil) 

/-- 
The value of a smooth function, i.e., the value of the one-jet at a point.
-/
def Jet.SmoothFunction.value (f: Jet.SmoothFunction 1) : ℝ → ℝ := 
  fun x => f.asFunc (Vector.cons x Vector.nil)

/--
Integrable functions can be obtained from smooth functions via the fundamental theorem of calculus.
-/
instance fundThm (f: Jet.SmoothFunction 1) :
  Integrable (f.derivative) where
  integral (a b) := f.value b - f.value a
  interval_union (a b c) := by
    simp [integral]

/-!
## Constructions of smooth functions
To use the above we need to construct a few smooth functions
-/

namespace SmoothFunction

/--
Constant functions as smooth functions.
-/
def constant (c : ℝ) : SmoothFunction := 
  ⟨fun _ ↦ ⟨c, 0⟩⟩

/--
Sum of smooth functions.
-/
def sum (f g : Jet.SmoothFunction 1) : Jet.SmoothFunction 1 := 
  ⟨fun x => f.value x + g.value x, fun x => Vector.cons (f.derivative x + g.derivative x) Vector.nil⟩

/--
Product of smooth functions using Liebnitz rule.
-/
def prod (f g : Jet.SmoothFunction 1) : Jet.SmoothFunction 1 :=
  ⟨fun x => f.value x * g.value x, fun x => Vector.cons (f.derivative x * g.value x + f.value x * g.derivative x) Vector.nil⟩

/--
Product of a scalar and a smooth function.
-/
def scalarProd (c : ℝ) (f : Jet.SmoothFunction 1) : Jet.SmoothFunction 1 :=
  ⟨fun x => c * f.value x, fun x => Vector.cons (c * f.derivative x) Vector.nil⟩

/-- Addition operation on smooth functions -/
instance : Add (Jet.SmoothFunction 1) := ⟨sum⟩
/-- Multiplication operation on smooth functions -/
instance : Mul (Jet.SmoothFunction 1) := ⟨prod⟩
/-- Scalar multiplication for smooth functions -/
instance : SMul ℝ (Jet.SmoothFunction 1) := ⟨scalarProd⟩

/-!
This gives polynomial functions as a special case. As an exercise, prove that smooth functions form a Ring (indeed an Algebra over ℝ).
We will define some polynomials as smooth functions as an example.
-/

/- Can we use extends here -/

theorem Jet.SmoothFunction.add.comm (f g : Jet.SmoothFunction 1) : f + g = g + f := by
  have lem1 : (fun x => f.asFunc x + g.asFunc x) = (fun x => g.asFunc x + f.asFunc x) := by
    apply add_comm
  have lem2 : (fun x => f.grad x + g.grad x) = (fun x => g.grad x + f.grad x) := by
    sorry
    --apply add_comm
  sorry 

theorem Jet.smoothfunction.add.assoc (f g h : Jet.SmoothFunction 1) : (f + g) + h = f + (g + h) := by
  have lem1 : (fun x => (f.asFunc x + g.asFunc x) + h.asFunc x) = (fun x => f.asFunc x + (g.asFunc x + h.asFunc x)) := by
    apply add_assoc
  have lem2 : (fun x => (f.grad x + g.grad x) + h.grad x) = (fun x => f.grad x + (g.grad x + h.grad x)) := by
    sorry
  sorry

theorem Jet.smoothfunction.add.zero (f : Jet.SmoothFunction 1) : f + 0 = f := by
  have lem1 : (fun x => f.asFunc x + 0) = (fun x => f.asFunc x) := by
    apply add_zero
  have lem2 : (fun x => f.grad x + 0) = (fun x => f.grad x) := by
    sorry
    --simp[Jet.SmoothFunction.add]
  sorry

/-- The coordinate function -/
def x : Jet.SmoothFunction 1 := ⟨fun x => x, fun x => ⟨[1], rfl⟩⟩

/-- The power function for a smooth function (automatic if ring is proved) -/
def pow (f: Jet.SmoothFunction 1): ℕ →  Jet.SmoothFunction 1
| 0 => Jet.SmoothFunction.const 1 1
| n + 1 => f * (pow f n)

instance : HPow (Jet.SmoothFunction 1) ℕ (Jet.SmoothFunction 1)  := ⟨pow⟩ 

instance : Coe ℝ SmoothFunction := ⟨constant⟩

/-- A polynomial. We can have cleaner notation but the goal is to illustrate the construction -/
def poly_example := (Jet.SmoothFunction.const 1 2) * x+ (Jet.SmoothFunction.const 1 3) * x^3 + (Jet.SmoothFunction.const 1 7)


end SmoothFunction