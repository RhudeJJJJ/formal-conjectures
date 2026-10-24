/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSemanticPolynomialPaymentCell
import Proofs.RadenkovicGutmanIntegerOuterTerms

namespace Gebendorfer.RadenkovicGutman.IntegerPolynomialPaymentCell
open Set
abbrev IP := NestedInteger.Poly 1
abbrev Witness := ComputedPolynomialCell.Witness
abbrev Data := ComputedGeneralPathData.Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

noncomputable def value (p : IP) (t : ℝ) : ℝ :=
  NestedHorner.eval (NestedInteger.castPoly 1 p) (fun _ => t)

theorem value_cast (p : IP) (x : Fin 1 → ℝ) :
    NestedHorner.eval (NestedInteger.castPoly 1 p) x=
      HornerCertificates.evaluate (NestedInteger.castPoly 1 p) (x 0) := by
  induction p with
  | nil =>
      change (0 : ℝ)=HornerCertificates.evaluate [] (x 0)
      exact (HornerCertificates.evaluate_nil (x 0)).symm
  | cons c p ih =>
      calc
        _ = ((c : ℚ) : ℝ)+x 0*NestedHorner.eval (NestedInteger.castPoly 1 p) x := rfl
        _ = ((c : ℚ) : ℝ)+x 0*HornerCertificates.evaluate (NestedInteger.castPoly 1 p) (x 0) := by rw [ih]
        _ = _ := (HornerCertificates.evaluate_cons (c : ℚ) (NestedInteger.castPoly 1 p) (x 0)).symm

theorem value_cons (c : ℤ) (p : IP) (t : ℝ) :
    value (c::p) t=(c : ℝ)+t*value p t := by
  change ((c : ℚ) : ℝ)+t*value p t=_
  push_cast
  rfl

theorem value_add (p q : IP) (t : ℝ) :
    value (NestedInteger.add p q) t=value p t+value q t := by
  exact (congrArg (fun z => NestedHorner.eval z (fun _ => t))
    (NestedInteger.cast_add p q)).trans (NestedHorner.eval_add _ _ _)

theorem value_scale (c : ℤ) (p : IP) (t : ℝ) :
    value (NestedInteger.scale c p) t=(c : ℝ)*value p t := by
  dsimp [value]
  rw [NestedInteger.cast_scale,NestedHorner.eval_scale]
  push_cast
  rfl

@[simp] theorem value_singleton (c : ℤ) (t : ℝ) : value [c] t=(c : ℝ) := by
  simp [value,NestedInteger.castPoly,NestedHorner.eval]

def times : IP → IP → IP
  | [],_ => []
  | c::p,q => NestedInteger.add (NestedInteger.scale c q) (0::times p q)

theorem value_times (p q : IP) (t : ℝ) : value (times p q) t=value p t*value q t := by
  induction p with
  | nil => simp [times,value,NestedInteger.castPoly,NestedHorner.eval]
  | cons c p ih =>
      rw [times,value_add,value_scale]
      rw [value_cons,value_cons,Int.cast_zero,zero_add,ih]
      ring

def zeroCheck (p : List ℚ) : Bool := p.all (fun c => decide (c=0))

theorem zero_sound (p : List ℚ) (h : zeroCheck p=true) (t : ℝ) :
    HornerCertificates.evaluate p t=0 := by
  induction p with
  | nil => exact HornerCertificates.evaluate_nil t
  | cons c p ih =>
      have hh : decide (c=0)=true ∧ zeroCheck p=true := by
        simpa only [zeroCheck,List.all_cons,Bool.and_eq_true] using h
      rw [HornerCertificates.evaluate_cons,of_decide_eq_true hh.1,ih hh.2]
      simp

def bindingCheck (D : ℤ) (a : IP) (p : List ℚ) : Bool :=
  zeroCheck (HornerCertificates.add (NestedInteger.castPoly 1 a)
    (HornerCertificates.scale (-(D : ℚ)) p))

theorem binding_sound (D : ℤ) (a : IP) (p : List ℚ)
    (h : bindingCheck D a p=true) (t : ℝ) :
    value a t=(D : ℝ)*HornerCertificates.evaluate p t := by
  have hz := zero_sound _ h t
  rw [HornerCertificates.evaluate_add,HornerCertificates.evaluate_scale] at hz
  change NestedHorner.eval _ _=_
  rw [value_cast]
  push_cast at hz
  linarith only [hz]

def affine (p : IP) (A B T : ℤ) : IP :=
  NestedInteger.scale T (IntegerOuterTerms.transform A B T 0 p)

theorem affine_value (p : IP) (A B T : ℤ) (hT : T≠0) (t : ℝ) :
    value (affine p A B T) t=(T : ℝ)^p.length*
      value p (((A : ℝ)+(B : ℝ)*t)/(T : ℝ)) := by
  have h := IntegerOuterTerms.eval_from A B T hT 0 p (fun _ => t)
  change value (NestedInteger.scale T (IntegerOuterTerms.transform A B T 0 p)) t=_
  rw [value_scale]
  simp only [pow_zero,one_mul] at h
  rw [value_cast] at h
  rw [value_cast] at h
  simpa only [value,value_cast,Fin.cons_zero] using h

structure Source where
  den : ℤ
  length : ℕ
  poly : Fin 5 → IP

def sourceChecks (d : Data) (s : Source) : Bool :=
  decide (0<s.den ∧ ∀ i, (s.poly i).length=s.length ∧
    bindingCheck s.den (s.poly i) (ComputedPolynomialCell.source d i)=true)

structure Geometry where
  left : ℤ
  width : ℤ
  den : ℤ
  localDen : ℤ
  lowerC : ℤ
  s : IP
  L : IP
  transformed : Fin 5 → IP

def floorPoly (p : IP) (c : ℤ) : IP := NestedInteger.add p [-c]

theorem value_floor (p : IP) (c : ℤ) (t : ℝ) :
    value (floorPoly p c) t=value p t-(c : ℝ) := by
  rw [floorPoly,value_add]
  rw [value_singleton,Int.cast_neg]
  ring

def margin (g : Geometry) : IP :=
  NestedInteger.add (NestedInteger.scale (g.localDen^2) (times g.s (g.transformed 2)))
    (NestedInteger.scale (-1) (times g.L (times (NestedInteger.add g.s [g.localDen])
      (NestedInteger.add (times g.s (g.transformed 0))
        (NestedInteger.scale g.localDen (g.transformed 1))))))

def positive (p : IP) : Bool := NestedInteger.accepts 1 (fun _ => p.length) p

theorem positive_sound (p : IP) (h : positive p=true) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0≤value p t := NestedInteger.accepts_sound 1 _ p h (fun _ => t) (fun _ => ht)

def checks (s : Source) (w : Witness) (g : Geometry) : Bool :=
  decide (0<w.a ∧ w.a<w.b ∧ 0<w.c ∧ 0<g.den ∧ 0<g.localDen ∧
    (g.left : ℚ)/(g.den : ℚ)=w.a ∧ (g.width : ℚ)/(g.den : ℚ)=w.b-w.a ∧
    (g.lowerC : ℚ)=(g.localDen : ℚ)*w.c ∧
    bindingCheck g.localDen g.s w.s=true ∧ bindingCheck g.localDen g.L w.L=true ∧
    (∀ i, g.transformed i=affine (s.poly i) g.left g.width g.den) ∧
    positive (floorPoly g.s 1)=true ∧ positive (floorPoly g.L g.lowerC)=true ∧
    positive (floorPoly (g.transformed 3) 1)=true ∧
    positive (floorPoly (g.transformed 4) 1)=true ∧ positive (margin g)=true)

noncomputable section
theorem conditions (d : Data) (s : Source) (w : Witness) (g : Geometry)
    (hs : sourceChecks d s=true) (hc : checks s w g=true) :
    SemanticPolynomialPaymentCell.Conditions d w := by
  obtain ⟨hD,hsrc⟩ := of_decide_eq_true hs
  obtain ⟨ha,hab,hc0,hT,hDS,hA,hB,hC,hS,hL,htrans,hsp,hlp,hnp,hep,hmp⟩ :=
    of_decide_eq_true hc
  refine ⟨ha,hab,hc0,?_⟩
  intro t ht
  let DS : ℝ := g.localDen
  let DG : ℝ := (g.den : ℝ)^s.length*(s.den : ℝ)
  have hDSr : 0<DS := by dsimp [DS]; exact_mod_cast hDS
  have hDGr : 0<DG := mul_pos (pow_pos (by exact_mod_cast hT) _) (by exact_mod_cast hD)
  have hAr : (g.left : ℝ)/(g.den : ℝ)=(w.a : ℝ) := by exact_mod_cast hA
  have hBr : (g.width : ℝ)/(g.den : ℝ)=((w.b-w.a : ℚ) : ℝ) := by exact_mod_cast hB
  have hloc : ((g.left : ℝ)+(g.width : ℝ)*t)/(g.den : ℝ)=
      SemanticPolynomialPaymentCell.location w t := by
    calc
      _ = (g.left : ℝ)/(g.den : ℝ)+((g.width : ℝ)/(g.den : ℝ))*t := by ring
      _ = _ := by rw [hAr,hBr]; rfl
  have hv (i : Fin 5) : value (g.transformed i) t=
      DG*HornerCertificates.evaluate (ComputedPolynomialCell.source d i)
        (SemanticPolynomialPaymentCell.location w t) := by
    rw [htrans i,affine_value _ _ _ _ hT.ne' t,(hsrc i).1,hloc,
      binding_sound _ _ _ (hsrc i).2]
    ring
  have hsv : value g.s t=DS*HornerCertificates.evaluate w.s t := binding_sound _ _ _ hS t
  have hlv : value g.L t=DS*HornerCertificates.evaluate w.L t := binding_sound _ _ _ hL t
  have hCr : (g.lowerC : ℝ)=DS*(w.c : ℝ) := by dsimp [DS]; exact_mod_cast hC
  have hS0 := positive_sound _ hsp t ht
  have hL0 := positive_sound _ hlp t ht
  have hN0 := positive_sound _ hnp t ht
  have hE0 := positive_sound _ hep t ht
  rw [value_floor,Int.cast_one] at hS0 hN0 hE0
  rw [value_floor] at hL0
  rw [hsv] at hS0
  rw [hlv,hCr] at hL0
  rw [hv 3] at hN0
  rw [hv 4] at hE0
  have hsr : 0<HornerCertificates.evaluate w.s t := by nlinarith only [hS0,hDSr]
  have hlr : (w.c : ℝ)≤HornerCertificates.evaluate w.L t := by nlinarith only [hL0,hDSr]
  have hnr : 0<HornerCertificates.evaluate d.N (SemanticPolynomialPaymentCell.location w t) := by
    change 0≤DG*HornerCertificates.evaluate d.N _-1 at hN0
    nlinarith only [hN0,hDGr]
  have her : 0<HornerCertificates.evaluate d.E (SemanticPolynomialPaymentCell.location w t) := by
    change 0≤DG*HornerCertificates.evaluate d.E _-1 at hE0
    nlinarith only [hE0,hDGr]
  refine ⟨hsr,hlr,hnr,her,?_⟩
  have hm := positive_sound _ hmp t ht
  simp only [margin,value_add,value_scale,value_times,
    Int.cast_neg,Int.cast_one,Int.cast_pow,hsv,hlv,hv] at hm
  rw [value_singleton] at hm
  change 0≤DS^2*(DS*HornerCertificates.evaluate w.s t*
    (DG*HornerCertificates.evaluate d.J (SemanticPolynomialPaymentCell.location w t)))+
    -1*(DS*HornerCertificates.evaluate w.L t*((DS*HornerCertificates.evaluate w.s t+DS)*
      (DS*HornerCertificates.evaluate w.s t*
        (DG*HornerCertificates.evaluate d.U (SemanticPolynomialPaymentCell.location w t))+
        DS*(DG*HornerCertificates.evaluate d.V (SemanticPolynomialPaymentCell.location w t))))) at hm
  have hm' : 0≤DS^3*DG*(HornerCertificates.evaluate w.s t*
      HornerCertificates.evaluate d.J (SemanticPolynomialPaymentCell.location w t)-
      HornerCertificates.evaluate w.L t*
        ((HornerCertificates.evaluate w.s t+(HornerCertificates.evaluate w.s t)^2)*
          HornerCertificates.evaluate d.U (SemanticPolynomialPaymentCell.location w t)+
          (HornerCertificates.evaluate w.s t+1)*
            HornerCertificates.evaluate d.V (SemanticPolynomialPaymentCell.location w t))) := by
    convert hm using 1 <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hm' (mul_pos (pow_pos hDSr _) hDGr))

#print axioms binding_sound
#print axioms affine_value
#print axioms positive_sound
#print axioms conditions
end
end Gebendorfer.RadenkovicGutman.IntegerPolynomialPaymentCell
