/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPathRecurrence
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Complex.Basic

namespace Gebendorfer.RadenkovicGutman.PolynomialPathMap
noncomputable section
open PathRecurrence Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem map_num_den {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) (n : ℕ) :
    f (num z n)=num (f z) n ∧ f (den z n)=den (f z) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · simp only [num_succ,map_sub,ih.1,ih.2]
    · simp only [den_succ,map_sub,map_mul,map_one,ih.1,ih.2]

theorem map_num {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) (n : ℕ) : f (num z n)=num (f z) n :=
  (map_num_den f z n).1
theorem map_den {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) (n : ℕ) : f (den z n)=den (f z) n :=
  (map_num_den f z n).2

def pointPoly (x : ℚ) : ℚ[X] := Polynomial.C x+Polynomial.X
def numPoly (x : ℚ) (n : ℕ) : ℚ[X] := num (pointPoly x) n
def denPoly (x : ℚ) (n : ℕ) : ℚ[X] := den (pointPoly x) n

noncomputable def evaluator (y : ℝ) : ℚ[X] →+* ℂ :=
  Polynomial.eval₂RingHom (Rat.castHom ℂ) ((y : ℂ)*Complex.I)

theorem eval_point (x : ℚ) (y : ℝ) :
    evaluator y (pointPoly x)=(x : ℂ)+(y : ℂ)*Complex.I := by
  simp [evaluator,pointPoly]

theorem eval_num (x : ℚ) (y : ℝ) (n : ℕ) :
    evaluator y (numPoly x n)=num ((x : ℂ)+(y : ℂ)*Complex.I) n := by
  change evaluator y (num (pointPoly x) n)=_
  rw [map_num,eval_point]

theorem eval_den (x : ℚ) (y : ℝ) (n : ℕ) :
    evaluator y (denPoly x n)=den ((x : ℂ)+(y : ℂ)*Complex.I) n := by
  change evaluator y (den (pointPoly x) n)=_
  rw [map_den,eval_point]

def ofList : List ℚ → ℚ[X]
  | [] => 0
  | c :: p => Polynomial.C c+Polynomial.X*ofList p

def pathAccepts (x : ℚ) (n : ℕ) (ns ds : List ℚ) : Bool :=
  decide (ofList ns=numPoly x n ∧ ofList ds=denPoly x n)

/-- Closed rational polynomial equalities give the actual recurrence at every
ordinate; floating evaluation and sampled polynomial identities are unnecessary. -/
theorem pathAccepts_sound (x : ℚ) (n : ℕ) (ns ds : List ℚ)
    (h : pathAccepts x n ns ds=true) (y : ℝ) :
    evaluator y (ofList ns)=num ((x : ℂ)+(y : ℂ)*Complex.I) n ∧
      evaluator y (ofList ds)=den ((x : ℂ)+(y : ℂ)*Complex.I) n := by
  have hh : ofList ns=numPoly x n ∧ ofList ds=denPoly x n := of_decide_eq_true h
  constructor
  · rw [hh.1]
    exact eval_num x y n
  · rw [hh.2]
    exact eval_den x y n

theorem mean14_path1 : pathAccepts (13/7) 1 [1] [13/7,1]=true := by
  rw [pathAccepts,decide_eq_true_eq]
  constructor
  all_goals apply Polynomial.funext
  all_goals intro t
  all_goals norm_num [ofList,numPoly,denPoly,pointPoly,num,den,state]
theorem mean14_path2 : pathAccepts (13/7) 2 [6/7,1] [-13/49,12/7,1]=true := by
  rw [pathAccepts,decide_eq_true_eq]
  constructor
  all_goals apply Polynomial.funext
  all_goals intro t
  all_goals norm_num [ofList,numPoly,denPoly,pointPoly,num,den,state]
  all_goals ring

#print axioms map_num_den
#print axioms eval_point
#print axioms eval_num
#print axioms eval_den
#print axioms pathAccepts_sound
#print axioms mean14_path1
#print axioms mean14_path2
end
end Gebendorfer.RadenkovicGutman.PolynomialPathMap
