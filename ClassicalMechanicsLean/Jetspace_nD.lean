import Mathlib.Data.Matrix.Basic
import Mathlib

open scoped Matrix

/-!
# Jet Spaces

These consist of the value of a function at a point, and the value of its gradient at that point. Smooth functions are functions on jet spaces.
-/

/-! ## Matrix 

We are defining the matrix as a list of lists, and then defining the matrix operations on this list of lists. -/

/-- A matrix is a function from two finite types to a type `α`. 
-/

abbrev Matrix' (m n : ℕ) α :=  _root_.Matrix (Fin m) (Fin n) α
 #check Matrix 


/-! ## Vector
  We use mathlib4 definition of Vector, a list restricted to a certain length. 
-/

local infixl:arg (priority := high) "^" => Vector

/-- Array notation for vectors
-/

instance : GetElem (α ^ n) Nat α (fun _ i => i < n) where
  getElem v i h := v.get ⟨i, h⟩

#check fun n (v : ℝ ^ n) (i : ℕ) (_ : i < n) => v[i]

/-- Coersion instance from `ℝ` to `ℝ^1`
-/

instance : Coe ℝ ℝ^1 := ⟨fun c => Vector.cons c Vector.nil⟩

/-! From here on, we only consider vectors of type ℝ. 
-/

namespace Vector

/-- Component wise addition of vectors
-/
def add {n : ℕ} : ℝ ^ n → ℝ ^ n → ℝ ^ n := 
  fun v₁ v₂ => v₁.map₂ (· + ·) v₂

instance : Add (ℝ ^ n) := ⟨Vector.add⟩

/-- Component wise scalar multiplication of vectors
-/
def smul {n : ℕ} (c : ℝ) : ℝ ^ n → ℝ ^ n := 
  fun v => v.map (c * ·)

/-- Zero vector
-/
def zero {n : ℕ} : ℝ ^ n := 
match n with 
  | 0 => Vector.nil
  | n + 1 => Vector.cons 0 (zero : ℝ ^ n)

/-- Additive inverse of a vector
-/
def neg {n : ℕ} : ℝ ^ n → ℝ ^ n := 
  fun v => v.map (fun x => -x)

instance : Neg (ℝ ^ n) := ⟨Vector.neg⟩

end Vector

/-- The addition of two vectors is the same as the addition of the corresponding components
-/

theorem Vector.add_get {n : ℕ} (v₁ v₂ : ℝ ^ n) (i : ℕ) (h : i < n) : 
  (v₁ + v₂).get ⟨i, h⟩  = v₁.get ⟨i ,h⟩ + v₂.get ⟨i, h⟩ := by
  have : (v₁ + v₂) = Vector.add v₁ v₂ := by
    rfl
  rw [this, Vector.add, Vector.map₂]
  simp [Vector.add, Vector.get_eq_get, List.zipWith]
  let ⟨l₁, ineq₁⟩ := v₁
  let ⟨l₂, ineq₂⟩ := v₂
  match c:n,l₁, l₂, i, h with
  | 0, _, _, _ ,_ => 
    simp
  | _+1, h₁::_, h₂::_, 0, _ =>
    simp [c]
  | n+1, h₁::t₁, h₂::t₂, i+1, pf =>
    simp

/-- The value of the zero vector is zero at every component
-/

theorem Vector.zero_get {n : ℕ} (i : ℕ) (h : i < n) :
  (zero : ℝ ^ n).get ⟨i, h⟩ = 0 := by
  simp[Vector.zero]
  match c:n, i, h with
  | 0, _, _ =>
    contradiction
  | k+1, 0, j  =>
    simp [c]
    simp [zero]
  | n+1, i+1, pf =>
    have zt : (zero : ℝ^ (n + 1)).tail = zero := by
      rfl
    let ih := Vector.zero_get i (Nat.lt_of_succ_lt_succ pf)
    let lm := Vector.get_tail_succ (zero : ℝ^ (n + 1)) ⟨i, Nat.lt_of_succ_lt_succ pf⟩
    rw [zt] at lm
    rw [lm] at ih
    exact ih

/-- The value of the additive inverse of a vector is the additive inverse of the value at every component
-/

theorem Vector.neg_get {n : ℕ} (v : ℝ ^ n) (i : ℕ) (h : i < n) : 
  (-v).get ⟨i, h⟩ = -v.get ⟨i, h⟩ := by
  let ⟨l, ineq⟩ := v
  have lem: Vector.neg v = -v := by
    rfl
  match c:n, i, h with
  | 0, _, _ => 
    contradiction
  | n+1, 0, h  =>
    simp [c, lem]
    simp [neg]
    sorry
  | n+1, i+1, pf =>
    simp [Vector.neg, Vector.get_eq_get, Vector.cons, Vector.tail] 
    sorry

/-- Define an instance of abelian group structure on ℝ^n 
-/

instance : AddCommGroup ℝ^n where
  add := Vector.add
  add_assoc := by
    intro a b c
    ext ⟨m, ineq⟩
    simp [Vector.add_get, add_assoc]
  add_comm := by
    intro v₁ v₂
    ext ⟨m, ineq⟩
    simp[Vector.add_get, add_comm]
  zero := Vector.zero
  zero_add := by 
    intro v  
    ext ⟨m, ineq⟩
    simp [Vector.add_get, Vector.zero_get]
    apply Vector.zero_get
  add_zero := by
    intro a
    ext ⟨m, ineq⟩
    simp [Vector.add_get, Vector.zero_get]
    apply Vector.zero_get
  neg := Vector.neg
  add_left_neg := by
    intro a
    ext ⟨m, ineq⟩
    simp [Vector.add_get, Vector.neg_get, add_left_neg, Vector.zero, Vector.add, Vector.neg]
    show 0 = Vector.get Vector.zero { val := m, isLt := ineq }
    rw[Vector.zero_get]
    
/-- Define a vector space structure on ℝ^n over ℝ
Left uncompleted due to lack of time
-/

instance : Module ℝ ℝ^n where
  smul := Vector.smul
  smul_add := by 
    intro a x y
    ext ⟨m, ineq⟩
    sorry
  add_smul := sorry
  mul_smul := sorry
  one_smul := sorry
  smul_zero := sorry
  zero_smul := sorry

/-- Dot product of two vectors
-/
def dotProduct : {n : ℕ} → ℝ ^ n → ℝ ^ n → ℝ :=
  (·.get ⬝ᵥ ·.get)

/-- The standard basis over ℝ^n
-/
def Vector.stdBasis {n : ℕ} (i : ℕ) : (i < n) →  ℝ ^ n :=
  fun h => 
  match i, n, h with 
  | 0, k + 1, _ =>
    Vector.cons 1 (0 : ℝ^k)
  | i + 1, k + 1, pf => 
    let tail : ℝ ^ k := Vector.stdBasis i (Nat.le_of_succ_le_succ pf) 
    Vector.cons 0 tail


/-- Vector form of row matrix
-/
def Matrix'.row {n : ℕ} (v : α^n) : Matrix' 1 n α := 
  fun _ j => v[j]

/-- Vector form of column matrix
-/
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

/-- A constant SmoothFunction
-/
def ofConst (c : ℝ^m) : SmoothFunction n m :=
  ⟨fun _ => c, fun _ => 0, sorry⟩

instance : Coe ℝ^m (SmoothFunction n m) where
  coe := .ofConst

def coord {n : ℕ} (i : ℕ) (h : i < n) : SmoothFunction n 1 := 
  ⟨fun v : ℝ^n => v[i], fun _ => Vector.stdBasis i h, sorry⟩

/-- Addition of two SmoothFunctions
-/
protected def add : SmoothFunction n m → SmoothFunction n m → SmoothFunction n m
| ⟨f₁, grad₁, h₁⟩, ⟨f₂, grad₂, h₂⟩ => 
  ⟨fun v => f₁ v + f₂ v, fun v => grad₁ v + grad₂ v,
   sorry⟩

/-- Negation of a SmoothFunction
-/
protected def neg : SmoothFunction n m → SmoothFunction n m
| ⟨f, grad, h⟩ => ⟨fun v => - f v, fun v => - grad v, sorry⟩

/-- Scalar multiplication of a SmoothFunction 
-/
protected noncomputable def smul : SmoothFunction n 1 → SmoothFunction n m → SmoothFunction n m
| ⟨f₁, grad₁, h₁⟩, ⟨f₂, grad₂, h₂⟩ => 
  ⟨fun v => (f₁ v)[0] • f₂ v,
   fun v => f₂ v ⬝ grad₁ v + (f₁ v)[0] • grad₂ v,
   sorry⟩

/-- Define an instance of abelian group structure on SmoothFunction
-/
instance : AddCommGroup (SmoothFunction n m) where
  add := SmoothFunction.add
  add_assoc := by intros; ext1; ext1 v; apply add_assoc
  add_comm := by intros; ext1; ext1 v; apply add_comm
  zero := .ofConst 0
  zero_add := by intros; ext1; ext1 v; apply zero_add
  add_zero := by intros; ext1; ext1 v; apply add_zero
  neg := SmoothFunction.neg
  add_left_neg := by intros; ext1; ext1 v; apply add_left_neg

/-- Define an instance of vector space of SmoothFunction over ℝ
-/
noncomputable instance : Module ℝ (SmoothFunction n m) where
  smul c f := SmoothFunction.smul c f
  smul_add := by intros; ext1; ext1 v; apply smul_add
  add_smul := by intros; ext1; ext1 v; apply add_smul
  mul_smul := by intros; ext1; ext1 v; apply mul_smul
  one_smul := by intros; ext1; ext1 v; apply one_smul
  smul_zero := by intros; ext1; ext1 v; apply smul_zero
  zero_smul := by intros; ext1; ext1 v; apply zero_smul

end SmoothFunction

/-- Composition with a smooth function `ℝ → ℝ` with chain rule for derivative -/

def comp {n: ℕ} {l : ℕ} {m : ℕ} (g : SmoothFunction m l) (f : SmoothFunction n m)  : SmoothFunction n l := 
  ⟨g ∘ f,
   fun v => Matrix.mul (g.grad (f v)) (f.grad v),
   sorry⟩

infixr:65 " ∘ " => SmoothFunction.comp
