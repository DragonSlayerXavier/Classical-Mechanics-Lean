import Mathlib 
import ClassicalMechanicsLean.JetSpace_nD


namespace Newton_nD

--Newton mechanics in ℝ 

/-! Should include hypothesis in the definition of Particle without error.
-/

structure Particle (n : ℕ) where
  m : ℝ 
  x : Jet.SmoothFunction 1 n 
  v : Jet.SmoothFunction 1 n
  --{h : Vector.cons (v.asFunc) Vector.nil = Vector.get x.grad ⟨0, Nat.zero_lt_succ 0⟩}

/-! We then define particle's velocity and acccelaration as given below
-/

def Particle.a {n : ℕ} (z : Particle n) : (ℝ → ℝ^n) := 
  fun (t : ℝ) => z.v.grad ⟨[t], rfl⟩ ⟨[t], rfl⟩

def Particle.p {n : ℕ} (z : Particle n) : (Jet.SmoothFunction 1 n) := 
  ⟨fun (t : ℝ^1) => ((z.v.asFunc t).map ((z.m)*·)),
   fun (t : ℝ^1) =>
     let result₁ (c : ℝ^1) : ℝ^n := (((z.v.grad t c).map ((z.m)*·)) : ℝ ^ n)
     result₁
  ⟩

structure System (n : ℕ) (m : ℕ) := 
  particles : Vector (Particle n) m
  Fext : ℝ → ℝ^n 

/-! Sum of mass of particles in a system
-/

def System.m {n : ℕ} {m : ℕ} (S : System n m) : ℝ :=
  S.particles.map Particle.m |>.toList.sum

/- Initial attempt to define System.m

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


/-! Sum of momentum of particles in a system
-/

def System.p {n : ℕ} {m : ℕ} (S : System n m) : (Jet.SmoothFunction 1 n) :=
  ⟨fun t => S.particles.map (fun z => (z.v.asFunc t).map ((z.m)*·)) |>.toList.sum,
   fun t => S.particles.map (fun z => 
   let result₂ (c: ℝ^1) : ℝ^n := ((z.a (t : ℝ)).map ((z.m)*·) : ℝ^n)
   result₂)
   |>.toList.sum⟩

/-! Velocity and accelaration of centre of mass of a system is defined below
-/

def System.vcom {n : ℕ} {m : ℕ} (S : System n m) : (Jet.SmoothFunction 1 n) := 
  ⟨fun t => S.particles.map (fun p => p.v.asFunc t) |>.toList.sum, 
   fun t => S.particles.map (fun p => p.v.grad t) |>.toList.sum⟩ 

/-! Initial attempt at defining velocity of centre of mass

  match S.particles.toList with
  | [] => 0
  | head :: tail =>
    have h₁ : Nat.succ (List.length tail) = n := by
      trans 
      · apply List.length_cons
      · simp
    have h₂ : n-1 = List.length tail :=
      Nat.pred_eq_of_eq_succ h₁.symm
    ⟨ fun (t : ℝ^1) =>
        (((head.m)*(head.v.asFunc t) + (vcom ⟨⟨tail, h₂.symm⟩, S.Fext⟩).asFunc t)/mSys S)
    , fun (t : ℝ^1) =>
        let first : ℝ := (head.m)*((head.v.grad t) : ℝ)
        let second : ℝ := ((vcom ⟨⟨tail, h₂.symm⟩, S.Fext⟩).grad t)
        show ℝ from first + second⟩
  | [] => ⟨0, 0⟩
-/

def System.acom {n : ℕ} {m : ℕ} (S : System n m) : (ℝ → ℝ^n) :=
  fun (t : ℝ) => (S.vcom.grad ⟨[t], rfl⟩ ⟨[t], rfl⟩) 

/-! We give two of the most fundmental laws of Newton mechanics
-/  
axiom Second_Law {n : ℕ} {m : ℕ} (S : System n m) : 
  S.Fext = fun (t) => (S.acom t).map (S.m*·)

axiom Conservation_of_Momentum {n : ℕ} {m : ℕ} (S : System n m) :
  (S.Fext = 0) → (S.p.asFunc = 0)

/-! We define the kinetic energy of a particle
-/

def half : ℝ := (1/2 : ℚ)
def Particle.Ek {n : ℕ} (z : Particle n) : (ℝ → ℝ) :=
  fun (t : ℝ) => (Vector.map₂ (· * ·) (z.v.asFunc ⟨[t], rfl⟩) (z.v.asFunc ⟨[t], rfl⟩)).toList.sum * (z.m) * (half)

/-! We define the potential energy of a particle
-/




end Newton_nD