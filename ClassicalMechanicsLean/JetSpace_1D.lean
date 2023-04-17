import Mathlib

/-!
# Jet Spaces

These consist of the value of a function at a point, and the value of its gradient at that point. Smooth functions are functions on jet spaces.
-/

noncomputable example : Field ℝ := inferInstance

namespace Jet

universe u

/-- Notation ℝ^n etc -/
instance : HPow (Type u) ℕ (Type u) := ⟨fun k n ↦ Vector k n⟩ 


structure Jet (n : ℕ) where 
  value : ℝ 
  gradient : ℝ ^ n


instance  {n : ℕ } : Add  (ℝ ^ n) := ⟨fun v₁ v₂ => 
  Vector.map₂ (· + ·) v₁ v₂⟩

#check Vector.map₂

/--Addition of Jets is addition of their values and gradients-/
instance addJets {n: ℕ} : Add (Jet n) := 
    ⟨fun j₁ j₂ => ⟨j₁.value + j₂.value, j₁.gradient + j₂.gradient⟩⟩

/--Scalar Multiplication of ℝ^n-/
instance scMul {n : ℕ } : SMul ℝ  (ℝ ^ n) := 
  ⟨fun c v => v.map (c * ·)⟩

/--Scalar Multiplication of Jets-/
instance scMulJets {n : ℕ } : SMul ℝ (Jet n) :=
  ⟨fun c j => ⟨c * j.value, c • j.gradient⟩⟩

/--Dot product of two vectors-/
def Vector.dot {n: ℕ}(v₁ v₂ : ℝ ^ n) : ℝ := 
  (Vector.map₂ (· * ·) v₁ v₂).toList.sum

/--Product rule of derivatives-/
instance liebnitz {n: ℕ} : Mul (Jet n) :=
  ⟨fun j₁ j₂ => ⟨j₁.value * j₂.value, j₁.value • j₂.gradient + j₂.value • j₁.gradient⟩⟩


/-- Should be replaced by an actual definition eventually -/
opaque hasGradAt {n: ℕ} (f : ℝ ^ n → ℝ)(x : ℝ ^n) : Prop 

/-- A function `ℝ^n → ℝ` with its gradient-/
structure SmoothFunction (n : ℕ) where
  asFunc : ℝ ^ n → ℝ
  grad : ℝ ^ n  → ℝ ^ n 

instance : CoeFun (SmoothFunction n) (fun _ => ℝ^n → ℝ) where
  coe := SmoothFunction.asFunc

/-- 
The value of gradient is determined by the function.
Hence if the functional value is same at all points, so are the gradients.
Hence, we only need to prove equality of the functions to show equality.
This is axiomatized.
 -/
axiom gradient_determined {n: ℕ} (f g : SmoothFunction n) : 
    f.asFunc = g.asFunc → f = g

/--The zero vector, defined inductively-/
def zeroVector {n : ℕ} : ℝ ^ n := match n with 
  | 0 => Vector.nil
  | n + 1 => Vector.cons 0 (zeroVector : ℝ ^ n)

instance {n: ℕ} : Zero (ℝ ^ n) := ⟨zeroVector⟩

def consVector {n : ℕ} (c : ℝ) : ℝ ^ n := match n with 
  | 0 => Vector.nil
  | n + 1 => Vector.cons c (zeroVector : ℝ ^ n)

/--A constant SmoothFunction has a constant value and zero gradient-/
def SmoothFunction.const (n : ℕ) (c : ℝ) : SmoothFunction n := 
  ⟨fun _ => c, fun _ => 0⟩

/---/
def Vector.coord (i n : ℕ) : (i < n) →  ℝ ^ n :=
  fun h => 
  match i, n, h with 
  | 0, k + 1, _ => 
    Vector.cons 1 (zeroVector : ℝ ^ k)
  | i + 1, k + 1, pf => 
     let tail : ℝ ^ k := Vector.coord i k (Nat.le_of_succ_le_succ pf) 
     Vector.cons 0 tail

/-- The coordinate functions -/

def SmoothFunction.coord (i n : ℕ) (h : i < n) : SmoothFunction n := 
  ⟨fun v : Vector ℝ n => v.get ⟨i, h⟩, fun _ => 0⟩

instance : Coe  (ℝ ^ 1) ℝ  := ⟨fun v => v.get ⟨0, Nat.zero_lt_succ 0⟩⟩

/-- Composition with a smooth function `ℝ → ℝ` with chain rule for derivative -/

def SmoothFunction.comp {n: ℕ} (g : SmoothFunction 1) (f : SmoothFunction n)  : SmoothFunction n := 
  ⟨fun v => g.asFunc ⟨[f.asFunc v], rfl⟩, fun v => 
    let g' : ℝ := g.grad (⟨[f.asFunc v], rfl⟩ )
    let f' := f.grad v
    g' • f'⟩


infix:65 " ∘ " => SmoothFunction.comp

/--Addition of the components of a vector-/
def addVec {n : ℕ} (v1 : ℝ^n) : ℝ := 
  v1.toList.sum

instance : Coe (ℝ^1 → ℝ) (ℝ → ℝ) := ⟨(fun (f : ℝ^(1 : ℕ) → ℝ) => (fun (x : ℝ) => f ⟨[x], rfl⟩))⟩

instance : Coe (ℝ^1 → ℝ^1) (ℝ → ℝ) := ⟨(fun (f : ℝ^(1 : ℕ) → ℝ^(1 : ℕ)) => (fun (x : ℝ) => f ⟨[x], rfl⟩))⟩
