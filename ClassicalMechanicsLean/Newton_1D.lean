import Mathlib 
import ClassicalMechanicsLean.JetSpace_1D
import ClassicalMechanicsLean.Integral


namespace Newton1

/-# Newton mechanics in ℝ 
-/

/-! Should include hypothesis in the definition of Particle without error.
-/

structure Particle where
  m : ℝ 
  x : Jet.SmoothFunction 1 
  v : Jet.SmoothFunction 1
  F : ℝ^1 → ℝ
  --{h : Vector.cons (v.asFunc) Vector.nil = Vector.get x.grad ⟨0, Nat.zero_lt_succ 0⟩}

/-! We then define particle's velocity and acccelaration as given below
-/

def Particle.a (z : Particle) : (ℝ → ℝ) := 
  fun (t : ℝ) => z.v.grad ⟨[t], rfl⟩ 

def Particle.p (z : Particle) : (Jet.SmoothFunction 1) := 
  ⟨fun (t : ℝ^1) => ((z.m)*(z.v.asFunc t)),
   fun (t : ℝ^1) =>
     let result := (Jet.Vector.dot (Vector.cons (z.m) Vector.nil) (z.v.grad t))
     ⟨[result], rfl⟩⟩

structure System (n : ℕ) := 
  particles : Vector Particle n

/-! Sum of mass of particles in a system
-/

def System.m {n : ℕ} (S : System n) : ℝ :=
  S.particles.map Particle.m |>.toList.sum

def System.Fext {n : ℕ} (S : System n) : ℝ^1 → ℝ :=
  S.particles.map Particle.F |>.toList.sum

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

def System.p {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) :=
  ⟨fun t => S.particles.map (fun p => p.m * p.v.asFunc t) |>.toList.sum,
   fun t => S.particles.map (fun p => ⟨[p.m * p.a t], rfl⟩) |>.toList.sum⟩

/-! Velocity and accelaration of centre of mass of a system is defined below
-/

noncomputable def System.vcom {n : ℕ} (S : System n) : (Jet.SmoothFunction 1) := 
  ⟨fun t => S.p.asFunc t / S.m, fun t => Vector.cons (S.p.grad t / S.m) Vector.nil⟩ 

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

noncomputable def System.acom {n : ℕ} (S : System n) : (ℝ → ℝ) :=
  fun (t : ℝ) => (S.vcom.grad ⟨[t], rfl⟩) 

/-- We give two of the most fundmental laws of Newton mechanics
-/  

structure NewtonianSystem  (n : ℕ) extends System n where
  Second_Law : fun (x : ℝ^1) => toSystem.particles.map (fun p => p.F x) |>.toList.sum = fun (x : ℝ^1) => m * toSystem.acom x
  Conservation_of_Momentum : (toSystem.Fext = 0) → (toSystem.p.grad = 0)


/-- Third Law of Newton mechanics
-/

def hi := 0

/-- We define the kinetic energy of a particle
-/

def half : ℝ := (1/2 : ℚ)

def Particle.Ek (z : Particle) : (ℝ → ℝ) :=
  fun (t : ℝ) => (z.m)*(((z.v.asFunc ⟨[t], rfl⟩) : ℝ)^2)*(half)

/-! We define the potential energy of a particle
-/

def Particle.Ep (a b : ℝ) (z : Particle) [int : Integrable (z.F : (ℝ → ℝ))] : ℝ := 
  int.integral a b
  
--theorem Particle.Work_Energy_theorem (a b : ℝ) (z : Particle) 





end Newton1