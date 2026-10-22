/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedHorner

namespace Gebendorfer.RadenkovicGutman.NestedArithmetic
open NestedHorner
set_option maxHeartbeats 0

/-- Exact convolution, retaining every parameter coordinate. -/
def productRows {n : ℕ} (f : Poly n → Poly n → Poly n) :
    Poly (n+1) → Poly (n+1) → Poly (n+1)
  | [], _ => []
  | c :: p, q => add (q.map (f c)) (zero n :: productRows f p q)

def mul : {n : ℕ} → Poly n → Poly n → Poly n
  | 0, p, q => p*q
  | _+1, p, q => productRows mul p q

def constant : (n : ℕ) → ℚ → Poly n
  | 0, c => c
  | n+1, c => [constant n c]

def coordinate : (n : ℕ) → Fin n → Poly n
  | 0, i => Fin.elim0 i
  | n+1, i => if h : i.val=0 then [zero n, constant n 1]
      else [coordinate n ⟨i.val-1, by omega⟩]

def power {n : ℕ} (p : Poly n) : ℕ → Poly n
  | 0 => constant n 1
  | k+1 => mul p (power p k)

noncomputable section

theorem eval_productRows {n : ℕ} (f : Poly n → Poly n → Poly n)
    (hf : ∀ p q x, eval (f p q) x=eval p x*eval q x)
    (p q : Poly (n+1)) (x : Fin (n+1) → ℝ) :
    eval (productRows f p q) x=eval p x*eval q x := by
  have hm (c : Poly n) (q : Poly (n+1)) :
      eval (q.map (f c)) x=eval c (fun i => x i.succ)*eval q x := by
    induction q with
    | nil => simp
    | cons d q ih =>
      simp only [List.map_cons, eval_cons, hf, ih]
      ring
  induction p with
  | nil => simp [productRows]
  | cons c p ih =>
    rw [productRows, eval_add, hm, eval_cons, eval_zero, ih, eval_cons]
    ring

theorem eval_mul {n : ℕ} (p q : Poly n) (x : Fin n → ℝ) :
    eval (mul p q) x=eval p x*eval q x := by
  induction n with
  | zero => simp [mul, eval]
  | succ n ih => exact eval_productRows _ ih p q x

theorem eval_constant (n : ℕ) (c : ℚ) (x : Fin n → ℝ) :
    eval (constant n c) x=(c : ℝ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [constant, ih]

theorem eval_coordinate (n : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    eval (coordinate n i) x=x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    by_cases h : i.val=0
    · have hi : i=0 := Fin.ext h
      subst i
      simp [coordinate, eval_constant]
    · simp only [coordinate, dif_neg h, eval_cons, eval_nil, mul_zero, add_zero]
      rw [ih]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

theorem eval_power {n : ℕ} (p : Poly n) (k : ℕ) (x : Fin n → ℝ) :
    eval (power p k) x=eval p x^k := by
  induction k with
  | zero => simp [power, eval_constant]
  | succ k ih => rw [power, eval_mul, ih]; ring

end

/-- A computable polynomial program; every closed equality can be checked
in the kernel without evaluating noncomputable real polynomial instances. -/
inductive Expr (n : ℕ)
  | rational : ℚ → Expr n
  | indet : Fin n → Expr n
  | plus : Expr n → Expr n → Expr n
  | times : Expr n → Expr n → Expr n
  | scaled : ℚ → Expr n → Expr n
  | pow : Expr n → ℕ → Expr n

def compile {n : ℕ} : Expr n → Poly n
  | .rational c => constant n c
  | .indet i => coordinate n i
  | .plus a b => add (compile a) (compile b)
  | .times a b => mul (compile a) (compile b)
  | .scaled c a => scale c (compile a)
  | .pow a k => power (compile a) k

noncomputable def value {n : ℕ} : Expr n → (Fin n → ℝ) → ℝ
  | .rational c, _ => c
  | .indet i, x => x i
  | .plus a b, x => value a x+value b x
  | .times a b, x => value a x*value b x
  | .scaled c a, x => c*value a x
  | .pow a k, x => value a x^k

theorem compile_sound {n : ℕ} (e : Expr n) (x : Fin n → ℝ) :
    eval (compile e) x=value e x := by
  induction e with
  | rational c => exact eval_constant n c x
  | indet i => exact eval_coordinate n i x
  | plus a b ha hb => rw [compile, eval_add, ha, hb]; rfl
  | times a b ha hb => rw [compile, eval_mul, ha, hb]; rfl
  | scaled c a ha => rw [compile, eval_scale, ha]; rfl
  | pow a k ha => rw [compile, eval_power, ha]; rfl

def polyDecidableEq : (n : ℕ) → DecidableEq (Poly n)
  | 0 => inferInstance
  | n+1 => by
    letI : DecidableEq (Poly n) := polyDecidableEq n
    exact inferInstance

def accepts {n : ℕ} (e : Expr n) (p : Poly n) : Bool :=
  letI : DecidableEq (Poly n) := polyDecidableEq n
  decide (compile e=p)

noncomputable section
theorem accepts_sound {n : ℕ} (e : Expr n) (p : Poly n)
    (h : accepts e p=true) (x : Fin n → ℝ) : eval p x=value e x := by
  let : DecidableEq (Poly n) := polyDecidableEq n
  have hp : compile e=p := of_decide_eq_true h
  rw [← hp]
  exact compile_sound e x

#print axioms eval_productRows
#print axioms eval_mul
#print axioms eval_constant
#print axioms eval_coordinate
#print axioms eval_power
#print axioms compile_sound
#print axioms accepts_sound
end
end Gebendorfer.RadenkovicGutman.NestedArithmetic
