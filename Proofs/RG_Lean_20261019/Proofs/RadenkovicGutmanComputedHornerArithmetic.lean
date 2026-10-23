/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastGeneralPathCertificates
import Proofs.RadenkovicGutmanRationalPolynomialIntegral
import Proofs.RadenkovicGutmanGeneralPathPolynomialPayments

/-! Computable polynomial programs with generic kernel proofs for normalization,
affine substitution, exact primitives, payments, and positive rays. -/
namespace Gebendorfer.RadenkovicGutman.ComputedHornerArithmetic
open Polynomial PolynomialPathMap
abbrev Poly := HornerCertificates.Poly
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def trimZeros : Poly → Poly
  | [] => []
  | c :: p =>
      let q := trimZeros p
      if c=0 ∧ q=[] then [] else c :: q

theorem ofList_trim (p : Poly) : ofList (trimZeros p)=ofList p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      dsimp only [trimZeros]
      split
      · rename_i h
        have hp : ofList p=0 := by simpa only [h.2,ofList] using ih.symm
        simp only [ofList,h.1,map_zero,hp,mul_zero,add_zero]
      · change C c+X*ofList (trimZeros p)=C c+X*ofList p
        rw [ih]

def plus (p q : Poly) : Poly := trimZeros (HornerCertificates.add p q)
def scaled (c : ℚ) (p : Poly) : Poly := trimZeros (HornerCertificates.scale c p)
def times (p q : Poly) : Poly := trimZeros (HornerArithmetic.mul p q)
def difference (p q : Poly) : Poly := plus p (scaled (-1) q)
def square (p : Poly) : Poly := times p p

theorem ofList_plus (p q : Poly) : ofList (plus p q)=ofList p+ofList q := by
  rw [plus,ofList_trim,FastGeneralPathCertificates.ofList_add]
theorem ofList_scaled (c : ℚ) (p : Poly) : ofList (scaled c p)=C c*ofList p := by
  rw [scaled,ofList_trim,FastGeneralPathCertificates.ofList_scale]
theorem ofList_times (p q : Poly) : ofList (times p q)=ofList p*ofList q := by
  rw [times,ofList_trim,FastGeneralPathCertificates.ofList_mul]
theorem ofList_difference (p q : Poly) : ofList (difference p q)=ofList p-ofList q := by
  simp only [difference,ofList_plus,ofList_scaled,map_neg,map_one,neg_one_mul,sub_eq_add_neg]
theorem ofList_square (p : Poly) : ofList (square p)=(ofList p)^2 := by
  simp only [square,ofList_times,pow_two]

def compose : Poly → Poly → Poly
  | [], _ => []
  | c :: p, q => plus [c] (times q (compose p q))
def affine (p : Poly) (a w : ℚ) : Poly := compose p [a,w]

theorem ofList_compose (p q : Poly) :
    ofList (compose p q)=(ofList p).comp (ofList q) := by
  induction p with
  | nil => simp [compose,ofList]
  | cons c p ih =>
      simp only [compose,ofList_plus,ofList_times,ofList,ih,Polynomial.add_comp,
        Polynomial.mul_comp,Polynomial.C_comp,Polynomial.X_comp,mul_zero,add_zero]

theorem eval_ofList (p : Poly) (x : ℚ) : (ofList p).eval x=CheckedRoots.eval p x := by
  induction p with
  | nil => simp [ofList,CheckedRoots.eval]
  | cons c p ih => simp [ofList,CheckedRoots.eval,ih]

theorem affine_evaluation (p : Poly) (a w x : ℚ) :
    CheckedRoots.eval (affine p a w) x=CheckedRoots.eval p (a+w*x) := by
  have h := congrArg (fun r : ℚ[X] => r.eval x) (ofList_compose p [a,w])
  simp only [eval_ofList,Polynomial.eval_comp] at h
  simpa only [affine,CheckedRoots.eval,mul_zero,add_zero,mul_comm] using h

theorem affine_check (M : ℕ) (p : Poly) (a w : ℚ)
    (hlen : p.length≤M+1 ∧ (affine p a w).length≤M+1) :
    HornerCertificates.affineCheck M p (affine p a w) a w=true := by
  rw [HornerCertificates.affineCheck,decide_eq_true_eq]
  refine ⟨hlen.1,hlen.2,?_⟩
  intro k
  exact affine_evaluation p a w (k.val : ℚ)

def integrateFrom : ℕ → Poly → Poly
  | _, [] => []
  | n, c :: p => (c/((n : ℚ)+1)) :: integrateFrom (n+1) p
def primitive (p : Poly) : Poly := 0 :: integrateFrom 0 p
def unitIntegral (p : Poly) : ℚ :=
  CheckedRoots.eval (primitive p) 1-CheckedRoots.eval (primitive p) 0

theorem weighted_derivative (p : Poly) (n : ℕ) :
    C ((n : ℚ)+1)*ofList (integrateFrom n p)+
      X*(ofList (integrateFrom n p)).derivative=ofList p := by
  induction p generalizing n with
  | nil => simp [integrateFrom,ofList]
  | cons c p ih =>
      have hn : (n : ℚ)+1≠0 := by positivity
      have hqc : ((n : ℚ)+1)*(c/((n : ℚ)+1))=c := by field_simp [hn]
      have hq := congrArg (fun r : ℚ => (C r : ℚ[X])) hqc
      rw [map_mul] at hq
      have ht := ih (n+1)
      change C ((n : ℚ)+1)*(C (c/((n : ℚ)+1))+X*ofList (integrateFrom (n+1) p))+
        X*(C (c/((n : ℚ)+1))+X*ofList (integrateFrom (n+1) p)).derivative=
          C c+X*ofList p
      simp only [Polynomial.derivative_add,Polynomial.derivative_C,Polynomial.derivative_mul,
        Polynomial.derivative_X,zero_add,one_mul]
      simp only [Nat.cast_add,Nat.cast_one,map_add,map_one] at hq ht ⊢
      linear_combination X*ht+hq

theorem primitive_derivative (p : Poly) : (ofList (primitive p)).derivative=ofList p := by
  have h := weighted_derivative p 0
  simpa only [primitive,ofList,Polynomial.derivative_add,Polynomial.derivative_C,
    Polynomial.derivative_mul,Polynomial.derivative_X,zero_add,one_mul,
    Nat.cast_zero,zero_add,map_one] using h

theorem primitive_checked (p : Poly) :
    RationalPolynomialIntegral.accepts p (primitive p) 0 1 (unitIntegral p)=true := by
  rw [RationalPolynomialIntegral.accepts,decide_eq_true_eq]
  exact ⟨primitive_derivative p,by simp only [unitIntegral,eval_ofList]⟩

def paymentList (L : Poly) (c R : ℚ) : Poly :=
  let z := difference (scaled (1/c) L) [1]
  plus [R] (scaled (1/2) (difference
    (plus (difference z (scaled (1/2) (square z))) (scaled (1/3) (times (square z) z)))
    (scaled (1/4) (square (square z)))))

theorem paymentList_sound (L : Poly) (c R : ℚ) :
    ofList (paymentList L c R)=GeneralPathPolynomialPayments.paymentPolynomial (ofList L) c R := by
  simp only [paymentList,ofList_plus,ofList_scaled,ofList_difference,ofList_times,
    ofList_square,ofList,map_one,mul_zero,add_zero,GeneralPathPolynomialPayments.paymentPolynomial]
  ring

def nonnegative (p : Poly) : Bool := p.all (fun c => decide (0≤c))

theorem nonnegative_evaluation (p : Poly) (hc : nonnegative p=true) (x : ℝ) (hx : 0≤x) :
    0≤HornerCertificates.evaluate p x := by
  induction p with
  | nil => simp only [HornerCertificates.evaluate_nil,le_refl]
  | cons c p ih =>
      have hh : decide (0≤c)=true ∧ nonnegative p=true := by
        simpa only [nonnegative,List.all_cons,Bool.and_eq_true] using hc
      have hcr : (0 : ℝ)≤c := by exact_mod_cast (of_decide_eq_true hh.1 : (0 : ℚ)≤c)
      rw [HornerCertificates.evaluate_cons]
      exact add_nonneg hcr (mul_nonneg hx (ih hh.2))

theorem positive_evaluation (p : Poly) (hc : nonnegative p=true)
    (hp : 0<p.headD 0) (x : ℝ) (hx : 0≤x) : 0<HornerCertificates.evaluate p x := by
  cases p with
  | nil => simp only [List.headD_nil,lt_self_iff_false] at hp
  | cons c p =>
      have hh : decide (0≤c)=true ∧ nonnegative p=true := by
        simpa only [nonnegative,List.all_cons,Bool.and_eq_true] using hc
      have hcr : (0 : ℝ)<c := by exact_mod_cast hp
      rw [HornerCertificates.evaluate_cons]
      exact add_pos_of_pos_of_nonneg hcr (mul_nonneg hx (nonnegative_evaluation p hh.2 x hx))

#print axioms ofList_trim
#print axioms ofList_compose
#print axioms affine_check
#print axioms primitive_derivative
#print axioms primitive_checked
#print axioms paymentList_sound
#print axioms nonnegative_evaluation
#print axioms positive_evaluation
end Gebendorfer.RadenkovicGutman.ComputedHornerArithmetic
