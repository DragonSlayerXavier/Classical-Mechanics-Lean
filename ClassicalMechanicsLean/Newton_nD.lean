import Mathlib 
import ClassicalMechanicsLean.JetSpace_nD


namespace Newton_nD

--Newton mechanics in ℝ 

/-! Should include hypothesis in the definition of Particle without error.
-/

local infixl:arg (priority := high) "^" => Vector

structure Particle (n : ℕ) where
  m : ℝ 
  x : SmoothFunction 1 n 
  v : SmoothFunction 1 n
  F : ℝ^n → ℝ^n 
  --{h : Vector.cons (v.asFunc) Vector.nil = Vector.get x.grad ⟨0, Nat.zero_lt_succ 0⟩}

/-! We then define particle's velocity and acccelaration as given below
-/

def Particle.a {n : ℕ} (z : Particle n) : (ℝ → Matrix' n 1 ℝ) := 
  fun (t : ℝ) => (z.v.grad ⟨[t], rfl⟩)

def Particle.p {n : ℕ} (z : Particle n) : (SmoothFunction 1 n) := 
  ⟨fun (t : ℝ^1) => ((z.v.asFunc t).map ((z.m)*·)),
   fun (t : ℝ^1) => ((z.a (t[0])).map ((z.m)*·)),
   sorry
  ⟩

structure System (n : ℕ) (m : ℕ) := 
  particles : Vector (Particle n) m

/-! Sum of mass of particles in a system
-/

def System.m {n : ℕ} {m : ℕ} (S : System n m) : ℝ :=
  S.particles.map Particle.m |>.toList.sum

/--Fext of a system
-/

def System.F {n : ℕ} {m : ℕ} (S : System n m) : (ℝ^n → ℝ^n) :=
  fun (x : ℝ^n) => S.particles.map (fun  z => z.F x) |>.toList.sum

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

def System.p {n : ℕ} {m : ℕ} (S : System n m) : (SmoothFunction 1 n) :=
  ⟨fun t => S.particles.map (fun z => (z.v.asFunc t).map ((z.m)*·)) |>.toList.sum,
   fun t => S.particles.map (fun z => ((z.a (t[0])).map ((z.m)*·)))|>.toList.sum, sorry⟩

/-! Velocity and accelaration of centre of mass of a system is defined below
-/

noncomputable def System.vcom {n : ℕ} {m : ℕ} (S : System n m) : (SmoothFunction 1 n) := 
  ⟨fun t => S.particles.map (fun z => (1/S.m)•(z.v.asFunc t)) |>.toList.sum, 
   fun t => S.particles.map (fun z => (1/S.m)•(z.v.grad t)) |>.toList.sum,
   sorry⟩ 

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

noncomputable def System.acom {n : ℕ} {m : ℕ} (S : System n m) : (ℝ → Matrix' n 1 ℝ) :=
  fun t => S.particles.map (fun z => (1/S.m)•(z.v.grad t)) |>.toList.sum

/-! We give two of the most fundmental laws of Newton mechanics
-/  

structure NewtonianSystem (n : ℕ) (m : ℕ) extends System n m where 
  Second_Law : (fun (x : ℝ^n) => fun (t : ℝ) => Matrix'.col (toSystem.F x)) = (fun x: ℝ^n => (fun t : ℝ => ((toSystem.m)•(toSystem.acom t))))
  Conservation_of_Momentum :=  (toSystem.F = 0) → (toSystem.p.grad = 0)


/-! We define the kinetic energy of a particle
-/

def half : ℝ := (1/2 : ℚ)
def Particle.Ek {n : ℕ} (z : Particle n) : (ℝ → ℝ) :=
  fun (t : ℝ) => (Vector.map₂ (· * ·) (z.v.asFunc ⟨[t], rfl⟩) (z.v.asFunc ⟨[t], rfl⟩)).toList.sum * (z.m) * (half)

/-! We define the potential energy of a particle
-/




end Newton_nD