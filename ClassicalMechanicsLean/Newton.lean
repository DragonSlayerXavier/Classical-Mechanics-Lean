import Mathlib 
import ClassicalMechanicsLean.JetSpace


namespace Newton1

--Newton mechanics in ℝ 

/-! Uniform accelarated motion : This can be extended to non-uniformly accelarated motion too. 
   The only reason we have considered 
-/

/-! Should include hypothesis in the definition of Particle without error.
-/
structure Particle where
  m : ℝ 
  x : Jet.SmoothFunction 1
  v : Jet.SmoothFunction 1
  --{h : v.asFunc = x.grad}

/-! Unsure of how to define gradient of 'a' here
-/
def a (z : Particle) : (Jet.SmoothFunction 1) := 
  ⟨fun (t : ℝ^1) => z.v.grad t, 0⟩  

/-! Coe ℝ (ℝ ^ 1) is not working below. 
-/
def p (z : Particle) : (Jet.SmoothFunction 1) := 
  ⟨fun (t : ℝ^1) => ((z.m)*(z.v.asFunc t)), fun (t : ℝ^1) => (Jet.Vector.dot (Vector.cons (z.m) Vector.nil) (z.v.grad t))⟩

structure System (n : ℕ) := 
  VecPar : Vector (Particle) n
  Fext : Jet.SmoothFunction 1

/-! 
-/
def mSys {n : ℕ} (S : System n) : ℝ := 
  let l := (S.VecPar).toList
  match l with
  | head :: tail => 
    have h1 : S.VecPar.length = n := by
      simp 
    have h2 : List.length l = n := by
      simp  
    have h3 : List.length (head::tail) = n := by
      sorry
    have h : (List.length tail = n-1) := by
      sorry
    head.m + (mSys ⟨⟨tail, h⟩, S.Fext⟩)
  | [] => 0

def pSys {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  let l := S.VecPar.toList 
  match l with 
  | head :: tail => 
    have h1 : S.VecPar.length = n := by
      simp 
    have h2 : List.length l = n := by
      simp  
    have h3 : List.length (head::tail) = n := by
      sorry
    have h : (List.length tail = n-1) := by
      sorry
    (p(head).asFunc)*(head.m) + pSys ⟨⟨tail, h⟩, S.Fext⟩
  |[] => ⟨0, 0⟩ 

def acom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  let l := (S.VecPar).toList 
  match l with 
  | head :: tail 
    => ⟨fun (t : ℝ^1) => (((head.m)*(a(head).asFunc t)) + (mSys )*(acom(tail).asFunc t))/n, a(head).grad + acom(tail).grad⟩ 

def F (z : Particle) : (Jet.SmoothFunction 1) := 
  ⟨fun (t : ℝ^1) => (z.m)*((a z).asFunc t), fun (t : ℝ^1) => (Jet.Vector.dot (Vector.cons (z.m) Vector.nil) ((a z).grad t))⟩

axiom SecondLaw {n : ℕ} (S : System n) : S.Fext = ⟨fun (t : ℝ^1) => (mSys S)*((acom S).asFunc t), fun (t : ℝ^1) => (mSys S)*(((acom S).grad t).get ⟨0, Nat.zero_lt_succ 0⟩)⟩ 

axiom ConsMom {n : ℕ} (S : System n) : (S.Fext.asFunc = 0) → ((pSys S).grad = 0)




/-!

def m : ℝ := sorry

def x : SmoothFunction := sorry

def v : Jet.Jet 1 := sorry

def a : Jet.Jet 1 := sorry

theorem v_def : v.value = x.grad := sorry

--def v : Jet 1 := sorry

def p : Jet  := ⟨m*v.value, Vector.dot v.gradient (consVector m)⟩ 

def F : ℝ := m * a

axiom m_pos : 0 < m

axiom conservation_of_momentum : F = 0 → p = p

axiom second_law : F = m * a

theorem first_law : F = 0 → v = v := by simp [F, v, a, p, conservation_of_momentum, second_law]

-/

end Newton1