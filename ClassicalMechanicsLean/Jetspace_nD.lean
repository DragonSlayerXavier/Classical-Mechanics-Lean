import Mathlib.Data.Matrix.Basic
import Mathlib

open scoped Matrix

/-!
# Jet Spaces

These consist of the value of a function at a point, and the value of its gradient at that point. Smooth functions are functions on jet spaces.
-/

/- - Notation ℝ^n etc -/
-- instance : HPow (Type u) ℕ (Type u) := ⟨fun k n ↦ Vector k n⟩

-- abbrev Vector α n := Fin n → α

local infixl:arg (priority := high) "^" => Vector

abbrev Matrix' (m n : ℕ) α :=  _root_.Matrix (Fin m) (Fin n) α
 #check Matrix

/-
structure Jet (n : ℕ) (m : ℕ) where 
  value : ℝ ^ m
  gradient : Jet.Matrix m n ℝ

namespace Jet

-- instance : AddCommGroup (Jet n m) where

protected def add {n m : ℕ} : Jet n m → Jet n m → Jet nm
| ⟨val₁, grad₁⟩, ⟨val₂, grad₂⟩ => ⟨val₁ + val₂, grad₁ + grad₂⟩

protected noncomputable def smul {n m : ℕ} (c : ℝ) : Jet n m → Jet n m
| ⟨val, grad⟩ => ⟨c • val, c • grad⟩ -/



instance : GetElem (α ^ n) Nat α (fun _ i => i < n) where
  getElem v i h := v.get ⟨i, h⟩
#check fun n (v : ℝ ^ n) (i : ℕ) (_ : i < n) => v[i]

instance : Coe ℝ ℝ^1 := ⟨fun c => Vector.cons c Vector.nil⟩
-- instance : Coe ℝ^1 ℝ  := ⟨fun v => v[0]⟩

/- instance (l : List ℝ) (n : outParam ℕ)
         (h : outParam (l.length = n) := by rfl)
    : CoeDep (List ℝ) l (ℝ^n) where
  coe := ⟨l, h⟩ -/

namespace Vector

--TODO VERY IMPORTANT
instance : AddCommGroup ℝ^n where
  add := Vector.map₂ (· + ·)
  add_assoc := sorry
  add_comm := sorry
  zero := sorry
  zero_add := sorry
  add_zero := sorry
  neg := sorry
  add_left_neg := sorry

instance : Module ℝ ℝ^n where
  smul := sorry
  smul_add := sorry
  add_smul := sorry
  mul_smul := sorry
  one_smul := sorry
  smul_zero := sorry
  zero_smul := sorry

def dotProduct : {n : ℕ} → ℝ ^ n → ℝ ^ n → ℝ :=
-- (Vector.map₂ (· * ·) v₁ v₂).toList.sum
/- | 0, _, _ => 0
| n+1, v₁, v₂ => v₁[0] * v₂[0] + Vector.dot (n := n) v₁.tail v₂.tail -/
  (·.get ⬝ᵥ ·.get)

def stdBasis {n : ℕ} (i : ℕ) : (i < n) →  ℝ ^ n :=
  fun h => 
  match i, n, h with 
  | 0, k + 1, _ =>
    Vector.cons 1 (0 : ℝ^k)
  | i + 1, k + 1, pf => 
    let tail : ℝ ^ k := Vector.stdBasis i (Nat.le_of_succ_le_succ pf) 
    Vector.cons 0 tail

end Vector

def Matrix'.row {n : ℕ} (v : α^n) : Matrix' 1 n α := 
  fun _ j => v[j]

def Matrix'.col {n : ℕ} (v : α^n) : Matrix' n 1 α := 
  fun i _ => v[i]

instance : Coe α^n (Matrix' 1 n α) := ⟨Matrix'.row⟩
instance : Coe α^n (Matrix' n 1 α) := ⟨Matrix'.col⟩

/-- Should be replaced by an actual definition eventually -/
def HasGradAt {n : ℕ} (f : ℝ^n → ℝ^m) (x : ℝ^n) (grad : Matrix' m n ℝ): Prop := 
  by sorry

/-- A function `ℝ^n → ℝ^m` with its gradient. -/
structure SmoothFunction (n : ℕ) (m : ℕ) where
  asFunc : ℝ ^ n → ℝ ^ m
  grad : ℝ ^ n  → Matrix' m n ℝ
  hasGradAt : ∀ x : ℝ^n, HasGradAt asFunc x (grad x)

namespace SmoothFunction

instance : CoeFun (SmoothFunction n m) (fun _ => ℝ^n → ℝ^m) where
  coe := SmoothFunction.asFunc

/-- Should be proved as a theorem -/
@[ext]
axiom ext {n : ℕ} {m : ℕ} (f g : SmoothFunction n m) : 
    f.asFunc = g.asFunc → f = g

/- def consVector {n : ℕ} (c : ℝ) : ℝ ^ n := match n with 
  | 0 => Vector.nil
  | n + 1 => Vector.cons c (zeroVector : ℝ ^ n) -/

def ofConst (c : ℝ^m) : SmoothFunction n m :=
  ⟨fun _ => c, fun _ => 0, sorry⟩

instance : Coe ℝ^m (SmoothFunction n m) where
  coe := .ofConst

def coord {n : ℕ} (i : ℕ) (h : i < n) : SmoothFunction n 1 := 
  ⟨fun v : ℝ^n => v[i], fun _ => Vector.stdBasis i h, sorry⟩

protected def add : SmoothFunction n m → SmoothFunction n m → SmoothFunction n m
| ⟨f₁, grad₁, h₁⟩, ⟨f₂, grad₂, h₂⟩ => 
  ⟨fun v => f₁ v + f₂ v, fun v => grad₁ v + grad₂ v,
   sorry⟩

protected def neg : SmoothFunction n m → SmoothFunction n m
| ⟨f, grad, h⟩ => ⟨fun v => - f v, fun v => - grad v, sorry⟩

protected noncomputable def smul : SmoothFunction n 1 → SmoothFunction n m → SmoothFunction n m
| ⟨f₁, grad₁, h₁⟩, ⟨f₂, grad₂, h₂⟩ => 
  ⟨fun v => (f₁ v)[0] • f₂ v,
   fun v => f₂ v ⬝ grad₁ v + (f₁ v)[0] • grad₂ v,
   sorry⟩

instance : AddCommGroup (SmoothFunction n m) where
  add := SmoothFunction.add
  add_assoc := by intros; ext1; ext1 v; apply add_assoc
  add_comm := by intros; ext1; ext1 v; apply add_comm
  zero := .ofConst 0
  zero_add := by intros; ext1; ext1 v; apply zero_add
  add_zero := by intros; ext1; ext1 v; apply add_zero
  neg := SmoothFunction.neg
  add_left_neg := by intros; ext1; ext1 v; apply add_left_neg

noncomputable instance : Module ℝ (SmoothFunction n m) where
  smul c f := SmoothFunction.smul c f
  smul_add := by intros; ext1; ext1 v; apply smul_add
  add_smul := by intros; ext1; ext1 v; apply add_smul
  mul_smul := by intros; ext1; ext1 v; apply mul_smul
  one_smul := by intros; ext1; ext1 v; apply one_smul
  smul_zero := by intros; ext1; ext1 v; apply smul_zero
  zero_smul := by intros; ext1; ext1 v; apply zero_smul

end SmoothFunction

/- protected def dotProduct : SmoothFunction n m → SmoothFunction n m → SmoothFunction n 1
| ⟨f₁, grad₁, h₁⟩, ⟨f₂, grad₂, h₂⟩ => 
  ⟨fun v => Vector.dotProduct (f₁ v) (f₂ v),
   fun v => sorry,
   sorry⟩ -/

/-- Composition with a smooth function `ℝ → ℝ` with chain rule for derivative -/
def comp {n: ℕ} {l : ℕ} {m : ℕ} (g : SmoothFunction m l) (f : SmoothFunction n m)  : SmoothFunction n l := 
  ⟨g ∘ f,
   fun v => Matrix.mul (g.grad (f v)) (f.grad v),
   sorry⟩

infixr:65 " ∘ " => SmoothFunction.comp
