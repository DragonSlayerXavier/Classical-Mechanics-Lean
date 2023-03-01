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

instance addJets {n: ℕ} : Add (Jet n) := 
    ⟨fun j₁ j₂ => ⟨j₁.value + j₂.value, j₁.gradient + j₂.gradient⟩⟩

instance scMul {n : ℕ } : SMul ℝ  (ℝ ^ n) := 
  ⟨fun c v => v.map (c * ·)⟩

instance scMulJets {n : ℕ } : SMul ℝ (Jet n) :=
  ⟨fun c j => ⟨c * j.value, c • j.gradient⟩⟩

def Vector.dot {n: ℕ}(v₁ v₂ : ℝ ^ n) : ℝ := 
  (Vector.map₂ (· * ·) v₁ v₂).toList.sum

instance liebnitz {n: ℕ} : Mul (Jet n) :=
  ⟨fun j₁ j₂ => ⟨j₁.value * j₂.value, j₁.value • j₂.gradient + j₂.value • j₁.gradient⟩⟩

/-- Should be replaced by an actual definition eventually -/
opaque hasGradAt {n: ℕ} (f : ℝ ^ n → ℝ)(x : ℝ ^n) : Prop 

/-- A function `ℝ^n → ℝ` with its gradient, the commented out condition should be added-/
structure SmoothFunction (n : ℕ) where
  asFunc : ℝ ^ n → ℝ
  grad : ℝ ^ n  → ℝ ^ n
  --hasGradAt : ∀ x, hasGradAt jetMap x

instance : CoeFun (SmoothFunction n) (fun _ => ℝ^n → ℝ) where
  coe := SmoothFunction.asFunc

/-- Should be proved as a theorem -/
axiom gradient_determined {n: ℕ} (f g : SmoothFunction n) : 
    f.asFunc = g.asFunc → f = g

def zeroVector {n : ℕ} : ℝ ^ n := match n with 
  | 0 => Vector.nil
  | n + 1 => Vector.cons 0 (zeroVector : ℝ ^ n)

instance {n: ℕ} : Zero (ℝ ^ n) := ⟨zeroVector⟩

def consVector {n : ℕ} (c : ℝ) : ℝ ^ n := match n with 
  | 0 => Vector.nil
  | n + 1 => Vector.cons c (zeroVector : ℝ ^ n)

def Jet.const (n : ℕ) (c : ℝ) : Jet n := 
  ⟨c, zeroVector⟩

def SmoothFunction.const (n : ℕ) (c : ℝ) : SmoothFunction n := 
  ⟨fun _ => c, fun _ => 0⟩

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

-- instance : Coe  ℝ  (ℝ ^ 1) := ⟨fun c => Vector.cons c Vector.nil⟩
/- instance (l : List ℝ) (n : outParam ℕ)
         (h : outParam (l.length = n) := by rfl)
    : CoeDep (List ℝ) l (ℝ^n) where
  coe := ⟨l, h⟩ -/

instance : Coe  (ℝ ^ 1) ℝ  := ⟨fun v => v.get ⟨0, Nat.zero_lt_succ 0⟩⟩

/-- Composition with a smooth function `ℝ → ℝ` with chain rule for derivative -/
def SmoothFunction.comp {n: ℕ} (g : SmoothFunction 1) (f : SmoothFunction n)  : SmoothFunction n := 
  ⟨fun v => g.asFunc ⟨[f.asFunc v], rfl⟩, fun v => 
    let g' : ℝ  := g.grad ⟨[f.asFunc v], rfl⟩
    let f' := f.grad v
    g' •  f'⟩

infix:65 " ∘ " => SmoothFunction.comp

def addVec {n : ℕ} (v1 : ℝ^n) : ℝ := 
  v1.toList.sum
