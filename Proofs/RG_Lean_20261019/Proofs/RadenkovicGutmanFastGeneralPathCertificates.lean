/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanHornerArithmetic
import Proofs.RadenkovicGutmanGeneralPathPolynomials
import Proofs.RadenkovicGutmanRationalMobiusPolynomials

/-! Computable rational list identities for arbitrary original mean shifts and
finite arm lengths. The soundness results prove the complete existing polynomial
contracts for every ordinate. -/
namespace Gebendorfer.RadenkovicGutman.FastGeneralPathCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial PolynomialPathMap
abbrev Poly := HornerCertificates.Poly

def minus (p q : Poly) : Poly := HornerCertificates.add p (HornerCertificates.scale (-1) q)
def square (p : Poly) : Poly := HornerArithmetic.mul p p

theorem ofList_add (p q : Poly) :
    ofList (HornerCertificates.add p q) = ofList p + ofList q := by
  induction p generalizing q with
  | nil => simp [HornerCertificates.add,ofList]
  | cons c p ih =>
      cases q with
      | nil => simp [HornerCertificates.add,ofList]
      | cons d q =>
          simp only [HornerCertificates.add,ofList,map_add,ih]
          ring

theorem ofList_scale (c : ℚ) (p : Poly) :
    ofList (HornerCertificates.scale c p) = C c * ofList p := by
  induction p with
  | nil => simp [HornerCertificates.scale,ofList]
  | cons d p ih =>
      change C (c*d)+X*ofList (HornerCertificates.scale c p) =
        C c*(C d+X*ofList p)
      rw [map_mul,ih]
      ring

theorem ofList_mul (p q : Poly) :
    ofList (HornerArithmetic.mul p q) = ofList p * ofList q := by
  induction p with
  | nil => simp [HornerArithmetic.mul,ofList]
  | cons c p ih =>
      change ofList (HornerCertificates.add (HornerCertificates.scale c q)
        (0 :: HornerArithmetic.mul p q)) = (C c+X*ofList p)*ofList q
      rw [ofList_add,ofList_scale,ofList,ih]
      simp only [map_zero,zero_add]
      ring

theorem ofList_minus (p q : Poly) : ofList (minus p q) = ofList p-ofList q := by
  simp only [minus,ofList_add,ofList_scale,map_neg,map_one,neg_one_mul,sub_eq_add_neg]

theorem ofList_square (p : Poly) : ofList (square p) = (ofList p)^2 := by
  simp only [square,ofList_mul,pow_two]

def zeroCheck : Poly → Bool
  | [] => true
  | c :: p => decide (c=0) && zeroCheck p

theorem zeroCheck_sound (p : Poly) (hc : zeroCheck p=true) : ofList p=0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      have hh : decide (c=0)=true ∧ zeroCheck p=true := by
        simpa only [zeroCheck,Bool.and_eq_true] using hc
      have he : c=0 := of_decide_eq_true hh.1
      simp only [ofList,he,map_zero,ih hh.2,mul_zero,add_zero]

def coefficientCheck (p q : Poly) : Bool := zeroCheck (minus p q)

theorem coefficientCheck_sound (p q : Poly) (hc : coefficientCheck p q=true) : ofList p=ofList q := by
  have h := zeroCheck_sound (minus p q) hc
  rw [ofList_minus] at h
  exact sub_eq_zero.mp h

def pathState (x : ℚ) : ℕ → Poly × Poly
  | 0 => ([-1],[])
  | n+1 =>
      let a := (pathState x n).1
      let b := (pathState x n).2
      (minus b a,minus (HornerArithmetic.mul [x-1,1] b) (HornerArithmetic.mul [x,1] a))
def numList (x : ℚ) (n : ℕ) : Poly := (pathState x n).1
def denList (x : ℚ) (n : ℕ) : Poly := (pathState x n).2

theorem pathState_sound (x : ℚ) (n : ℕ) :
    ofList (pathState x n).1=numPoly x n ∧ ofList (pathState x n).2=denPoly x n := by
  induction n with
  | zero =>
      simp [pathState,ofList,numPoly,denPoly,PathRecurrence.num,PathRecurrence.den,PathRecurrence.state]
  | succ n ih =>
      constructor
      · change ofList (minus (pathState x n).2 (pathState x n).1)=numPoly x (n+1)
        rw [ofList_minus,ih.2,ih.1]
        simp only [numPoly,denPoly,PathRecurrence.num_succ]
      · change ofList (minus (HornerArithmetic.mul [x-1,1] (pathState x n).2)
          (HornerArithmetic.mul [x,1] (pathState x n).1))=denPoly x (n+1)
        rw [ofList_minus,ofList_mul,ofList_mul,ih.2,ih.1]
        simp only [ofList,map_sub,map_one,mul_zero,add_zero,mul_one,
          numPoly,denPoly,PathRecurrence.den_succ,pointPoly]
        ring

theorem numList_sound (x : ℚ) (n : ℕ) : ofList (numList x n)=numPoly x n :=
  (pathState_sound x n).1
theorem denList_sound (x : ℚ) (n : ℕ) : ofList (denList x n)=denPoly x n :=
  (pathState_sound x n).2

def sourceSlopeList (x : ℚ) (p q : ℕ) : Poly :=
  HornerArithmetic.mul (minus (denList x (p+1)) (numList x (p+1)))
    (minus (denList x (q+1)) (numList x (q+1)))
def sourceOffsetList (x : ℚ) (p q : ℕ) : Poly :=
  minus (minus (HornerCertificates.scale 2 (HornerArithmetic.mul (denList x (p+1)) (denList x (q+1))))
    (HornerArithmetic.mul (numList x (p+1)) (denList x (q+1))))
    (HornerArithmetic.mul (numList x (q+1)) (denList x (p+1)))
def fusedSlopeList (x : ℚ) (p q : ℕ) : Poly :=
  minus (denList x (p+q+2)) (numList x (p+q+2))
def centerList (x : ℚ) : Poly := [-1,2*(x-1),2]
def scaleList : Poly := [0,2]
def sourceCenterList (x : ℚ) (p q : ℕ) : Poly :=
  minus (HornerArithmetic.mul (sourceSlopeList x p q) (centerList x))
    (HornerArithmetic.mul scaleList (sourceOffsetList x p q))
def fusedCenterList (x : ℚ) (p q : ℕ) : Poly :=
  minus (HornerArithmetic.mul (fusedSlopeList x p q) (centerList x))
    (HornerArithmetic.mul scaleList (denList x (p+q+2)))

theorem sourceSlopeList_sound (x : ℚ) (p q : ℕ) :
    ofList (sourceSlopeList x p q)=GeneralPathPolynomials.sourceSlope x p q := by
  simp only [sourceSlopeList,ofList_mul,ofList_minus,numList_sound,denList_sound,
    GeneralPathPolynomials.sourceSlope]
theorem sourceOffsetList_sound (x : ℚ) (p q : ℕ) :
    ofList (sourceOffsetList x p q)=GeneralPathPolynomials.sourceOffset x p q := by
  simp only [sourceOffsetList,ofList_minus,ofList_scale,ofList_mul,numList_sound,denList_sound,
    GeneralPathPolynomials.sourceOffset,map_ofNat]
  ring
theorem fusedSlopeList_sound (x : ℚ) (p q : ℕ) :
    ofList (fusedSlopeList x p q)=GeneralPathPolynomials.fusedSlope x p q := by
  simp only [fusedSlopeList,ofList_minus,numList_sound,denList_sound,GeneralPathPolynomials.fusedSlope]
theorem centerList_sound (x : ℚ) : ofList (centerList x)=GeneralPathPolynomials.centerPoly x := by
  simp only [centerList,ofList,map_neg,map_sub,map_mul,map_one,map_ofNat,mul_zero,add_zero,
    GeneralPathPolynomials.centerPoly]
  ring
theorem scaleList_sound : ofList scaleList=GeneralPathPolynomials.scalePoly := by
  norm_num [scaleList,ofList,GeneralPathPolynomials.scalePoly,Polynomial.C_ofNat] <;> ring
theorem sourceCenterList_sound (x : ℚ) (p q : ℕ) :
    ofList (sourceCenterList x p q)=GeneralPathPolynomials.sourceCenter x p q := by
  simp only [sourceCenterList,ofList_minus,ofList_mul,sourceSlopeList_sound,
    centerList_sound,scaleList_sound,sourceOffsetList_sound,GeneralPathPolynomials.sourceCenter]
theorem fusedCenterList_sound (x : ℚ) (p q : ℕ) :
    ofList (fusedCenterList x p q)=GeneralPathPolynomials.fusedCenter x p q := by
  simp only [fusedCenterList,ofList_minus,ofList_mul,fusedSlopeList_sound,
    centerList_sound,scaleList_sound,denList_sound,GeneralPathPolynomials.fusedCenter,GeneralPathPolynomials.fusedOffset]

def pathChecks (x : ℚ) (p q : ℕ) (a b c e : Poly) : Bool :=
  decide (coefficientCheck a (sourceSlopeList x p q)=true ∧ coefficientCheck b (sourceCenterList x p q)=true ∧
    coefficientCheck c (fusedSlopeList x p q)=true ∧ coefficientCheck e (fusedCenterList x p q)=true)

theorem path_sound (x : ℚ) (p q : ℕ) (a b c e : Poly) (hc : pathChecks x p q a b c e=true) :
    GeneralPathPolynomials.accepts x p q a b c e=true := by
  obtain ⟨ha,hb,hc,he⟩ := of_decide_eq_true hc
  rw [GeneralPathPolynomials.accepts,decide_eq_true_eq]
  exact ⟨(coefficientCheck_sound _ _ ha).trans (sourceSlopeList_sound x p q),
    (coefficientCheck_sound _ _ hb).trans (sourceCenterList_sound x p q),
    (coefficientCheck_sound _ _ hc).trans (fusedSlopeList_sound x p q),
    (coefficientCheck_sound _ _ he).trans (fusedCenterList_sound x p q)⟩

def partLists : Poly → Poly × Poly
  | [] => ([],[])
  | c :: p => (minus [c] (0 :: (partLists p).2),0 :: (partLists p).1)

theorem partLists_sound (p : Poly) :
    ofList (partLists p).1=(RationalComplexPolynomial.parts p).1 ∧
      ofList (partLists p).2=(RationalComplexPolynomial.parts p).2 := by
  induction p with
  | nil => exact ⟨rfl,rfl⟩
  | cons c p ih =>
      constructor <;>
        simp only [partLists,RationalComplexPolynomial.parts,ofList_minus,ofList,map_zero,
          mul_zero,add_zero,zero_add,ih.1,ih.2]

theorem partReal_sound (p : Poly) : ofList (partLists p).1=(RationalComplexPolynomial.parts p).1 :=
  (partLists_sound p).1
theorem partImag_sound (p : Poly) : ofList (partLists p).2=(RationalComplexPolynomial.parts p).2 :=
  (partLists_sound p).2

def normList (p : Poly) : Poly :=
  HornerCertificates.add (square (partLists p).1) (square (partLists p).2)
theorem normList_sound (p : Poly) : ofList (normList p)=RationalComplexPolynomial.normPolynomial p := by
  simp only [normList,ofList_add,ofList_square,partReal_sound,partImag_sound,
    RationalComplexPolynomial.normPolynomial]

def UList (a b c e : Poly) : Poly :=
  let ar := (partLists a).1; let ai := (partLists a).2
  let br := (partLists b).1; let bi := (partLists b).2
  let cr := (partLists c).1; let ci := (partLists c).2
  let er := (partLists e).1; let ei := (partLists e).2
  HornerCertificates.add
    (square (minus (minus (HornerCertificates.add (HornerArithmetic.mul br er) (HornerArithmetic.mul bi ei))
      (HornerArithmetic.mul ar cr)) (HornerArithmetic.mul ai ci)))
    (square (HornerCertificates.add (minus (minus (HornerArithmetic.mul bi er) (HornerArithmetic.mul br ei))
      (HornerArithmetic.mul ai cr)) (HornerArithmetic.mul ar ci)))
def VList (a b c e : Poly) : Poly :=
  let ar := (partLists a).1; let ai := (partLists a).2
  let br := (partLists b).1; let bi := (partLists b).2
  let cr := (partLists c).1; let ci := (partLists c).2
  let er := (partLists e).1; let ei := (partLists e).2
  HornerCertificates.add
    (square (HornerCertificates.add (minus (minus (HornerArithmetic.mul ar er) (HornerArithmetic.mul ai ei))
      (HornerArithmetic.mul br cr)) (HornerArithmetic.mul bi ci)))
    (square (minus (minus (HornerCertificates.add (HornerArithmetic.mul ar ei) (HornerArithmetic.mul ai er))
      (HornerArithmetic.mul br ci)) (HornerArithmetic.mul bi cr)))
def NList (a b : Poly) : Poly := minus (normList b) (normList a)
def EList (c e : Poly) : Poly := minus (normList e) (normList c)
def JList (a b : Poly) : Poly := square (NList a b)

theorem UList_sound (a b c e : Poly) : ofList (UList a b c e)=RationalMobiusPolynomials.U a b c e := by
  simp only [UList,ofList_add,ofList_square,ofList_minus,ofList_mul,partReal_sound,
    partImag_sound,RationalMobiusPolynomials.U]
theorem VList_sound (a b c e : Poly) : ofList (VList a b c e)=RationalMobiusPolynomials.V a b c e := by
  simp only [VList,ofList_add,ofList_square,ofList_minus,ofList_mul,partReal_sound,
    partImag_sound,RationalMobiusPolynomials.V]
theorem NList_sound (a b : Poly) : ofList (NList a b)=RationalMobiusPolynomials.N a b := by
  simp only [NList,ofList_minus,normList_sound,RationalMobiusPolynomials.N]
theorem EList_sound (c e : Poly) : ofList (EList c e)=RationalMobiusPolynomials.E c e := by
  simp only [EList,ofList_minus,normList_sound,RationalMobiusPolynomials.E]
theorem JList_sound (a b : Poly) : ofList (JList a b)=RationalMobiusPolynomials.J a b := by
  simp only [JList,ofList_square,NList_sound,RationalMobiusPolynomials.J]

def normChecks (a b c e u v j n ee : Poly) : Bool :=
  decide (coefficientCheck u (UList a b c e)=true ∧ coefficientCheck v (VList a b c e)=true ∧
    coefficientCheck j (JList a b)=true ∧ coefficientCheck n (NList a b)=true ∧ coefficientCheck ee (EList c e)=true)

theorem norms_sound (a b c e u v j n ee : Poly) (hc : normChecks a b c e u v j n ee=true) :
    RationalMobiusPolynomials.accepts a b c e u v j n ee=true := by
  obtain ⟨hu,hv,hj,hn,he⟩ := of_decide_eq_true hc
  rw [RationalMobiusPolynomials.accepts,decide_eq_true_eq]
  exact ⟨(coefficientCheck_sound _ _ hu).trans (UList_sound a b c e),
    (coefficientCheck_sound _ _ hv).trans (VList_sound a b c e),
    (coefficientCheck_sound _ _ hj).trans (JList_sound a b),
    (coefficientCheck_sound _ _ hn).trans (NList_sound a b),
    (coefficientCheck_sound _ _ he).trans (EList_sound c e)⟩

#print axioms coefficientCheck_sound
#print axioms pathState_sound
#print axioms path_sound
#print axioms partLists_sound
#print axioms norms_sound
end Gebendorfer.RadenkovicGutman.FastGeneralPathCertificates
