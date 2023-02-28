import Mathlib 
import ClassicalMechanicsLean.JetSpace


namespace Newton1

--Newton mechanics in ℝ 

/-! Should include hypothesis in the definition of Particle without error.
-/
structure Particle where
  m : ℝ 
  x : Jet.SmoothFunction 1
  v : Jet.SmoothFunction 1
  --{h : Vector.cons (v.asFunc) Vector.nil = Vector.get x.grad ⟨0, Nat.zero_lt_succ 0⟩}

/-! Unsure of how to define gradient of 'a' here
-/
def a (z : Particle) : (ℝ → ℝ) := 
  fun (t : ℝ) => z.v.grad t 

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
    have h2 : List.length l = n := by
      simp  
  match l with
  | head :: tail => 
    have h3 : List.length (head::tail) = n := by
      apply h2   
    have h4 : List.length (head::tail) = Nat.succ (List.length tail) := by
      apply List.length_cons 
    have h5 : Nat.succ (List.length tail) = n := by
      trans 
      · apply h4
      · apply h3
    have h7 : n = Nat.succ (List.length tail) := by
      apply h5.symm
    have h8 : n-1 = List.length tail := by
      apply Nat.pred_eq_of_eq_succ h7
    have h : List.length tail = n-1 := by
      apply h8.symm 
    head.m + (mSys ⟨⟨tail, h⟩, S.Fext⟩)
  | [] => 0

def pSys {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  let l := S.VecPar.toList 
  have h2 : List.length l = n := by
    simp  
  match l with 
  | head :: tail => 
    have h3 : List.length (head::tail) = n := by
      apply h2   
    have h4 : List.length (head::tail) = Nat.succ (List.length tail) := by
      apply List.length_cons 
    have h5 : Nat.succ (List.length tail) = n := by
      trans 
      · apply h4
      · apply h3
    have h7 : n = Nat.succ (List.length tail) := by
      apply h5.symm
    have h8 : n-1 = List.length tail := by
      apply Nat.pred_eq_of_eq_succ h7
    have h : List.length tail = n-1 := by
      apply h8.symm 
    ⟨fun (t : ℝ^1) => (p head).asFunc t + (pSys ⟨⟨tail, h⟩, S.Fext⟩).asFunc t, (p head).grad + (pSys ⟨⟨tail, h⟩, S.Fext⟩).grad⟩
  | [] => ⟨0, 0⟩ 

def vcom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  let l := S.VecPar.toList
  have h2 : List.length l = n := by
    simp  
  match l with 
  | head :: tail => 
    have h3 : List.length (head::tail) = n := by
      apply h2   
    have h4 : List.length (head::tail) = Nat.succ (List.length tail) := by
      apply List.length_cons 
    have h5 : Nat.succ (List.length tail) = n := by
      trans 
      · apply h4
      · apply h3
    have h7 : n = Nat.succ (List.length tail) := by
      apply h5.symm
    have h8 : n-1 = List.length tail := by
      apply Nat.pred_eq_of_eq_succ h7
    have h : List.length tail = n-1 := by
      apply h8.symm 
    ⟨fun (t : ℝ^1) => (((head.m)*(head.v.asFunc t) + (vcom ⟨⟨tail, h⟩, S.Fext⟩).asFunc t)/mSys S), fun (t : ℝ^1) => (head.m)*(head.v.grad t)/--! .get ⟨0, Nat.zero_lt_succ 0⟩-/ + (vcom ⟨⟨tail, h⟩, S.Fext⟩).grad t⟩
  | [] => ⟨0, 0⟩

def acom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  
axiom SecondLaw {n : ℕ} (S : System n) : S.Fext = ⟨fun (t : ℝ^1) => (mSys S)*((acom S).asFunc t), fun (t : ℝ^1) => (mSys S)*(((acom S).grad t).get ⟨0, Nat.zero_lt_succ 0⟩)⟩ 

axiom Conservation_of_Momentum {n : ℕ} (S : System n) : (S.Fext.asFunc = 0) → ((pSys S).grad = 0)




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