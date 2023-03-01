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
def Particle.a (z : Particle) : (ℝ → ℝ) := 
  fun (t : ℝ) => z.v.grad ⟨[t], rfl⟩ 

/-! Coe ℝ (ℝ ^ 1) is not working below. 
-/
def Particle.p (z : Particle) : (Jet.SmoothFunction 1) := 
  ⟨fun (t : ℝ^1) => ((z.m)*(z.v.asFunc t)),
   fun (t : ℝ^1) =>
     let result := (Jet.Vector.dot (Vector.cons (z.m) Vector.nil) (z.v.grad t))
     ⟨[result], rfl⟩⟩

structure System (n : ℕ) := 
  particles : Vector Particle n
  Fext : Jet.SmoothFunction 1

/-! 
-/
def System.m {n : ℕ} (S : System n) : ℝ :=
  S.particles.map Particle.m |>.toList.sum
  /-
  match S.particles.toList with
  | [] => 0
  | head :: tail =>
    have h₁ : Nat.succ (List.length tail) = n := by
      trans 
      · apply List.length_cons
      · simp
    have h₂ : n-1 = List.length tail :=
      Nat.pred_eq_of_eq_succ h₁.symm
    head.m + (mSys ⟨⟨tail, h₂.symm⟩, S.Fext⟩)
  -/


def System.p {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) :=
  ⟨fun t => S.particles.map (fun p => p.m * p.v t) |>.toList.sum,
   fun t => S.particles.map (fun p => ⟨[p.m * p.a t], rfl⟩) |>.toList.sum⟩
  /-
  let l := S.particles.toList
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
    ⟨fun (t : ℝ^1) => (p head).asFunc t + (pSys ⟨⟨tail, h⟩, S.Fext⟩).asFunc t,
     (p head).grad + (pSys ⟨⟨tail, h⟩, S.Fext⟩).grad⟩
  | [] => ⟨0, 0⟩ 
  -/

def vcom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  let l := S.particles.toList
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
    ⟨ fun (t : ℝ^1) =>
        (((head.m)*(head.v.asFunc t) + (vcom ⟨⟨tail, h⟩, S.Fext⟩).asFunc t)/mSys S)
    , fun (t : ℝ^1) =>
        let first : ℝ := (head.m)*((head.v.grad t) : ℝ)
        let second : ℝ := ((vcom ⟨⟨tail, h⟩, S.Fext⟩).grad t)
        show ℝ from first + second⟩
  | [] => ⟨0, 0⟩

def acom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  
axiom SecondLaw {n : ℕ} (S : System n) : S.Fext = ⟨fun (t : ℝ^1) => (mSys S)*((acom S).asFunc t), fun (t : ℝ^1) => (mSys S)*(((acom S).grad t).get ⟨0, Nat.zero_lt_succ 0⟩)⟩ 

axiom Conservation_of_Momentum {n : ℕ} (S : System n) : (S.Fext.asFunc = 0) → ((pSys S).grad = 0)



end Newton1