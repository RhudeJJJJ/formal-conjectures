/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedGeneralPathData
import Proofs.RadenkovicGutmanFastPolynomialPaymentCell

/-! Compact data use the proved coefficient programs and affine identities.
The original fast-cell theorem still supplies the actual-matrix integral bound. -/
namespace Gebendorfer.RadenkovicGutman.ComputedPolynomialCell
open Set MeasureTheory
open scoped Classical
abbrev Poly := HornerCertificates.Poly
abbrev Data := ComputedGeneralPathData.Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

structure Witness where
  a : ℚ
  b : ℚ
  s : Poly
  L : Poly
  c : ℚ
  R : ℚ
  total : ℚ
  k : ℕ
  n : ℕ
  sFloor : ℚ
  nFloor : ℚ
  eFloor : ℚ

def source (d : Data) : Fin 5 → Poly := ![d.U,d.V,d.J,d.N,d.E]
def affineSource (d : Data) (w : Witness) (i : Fin 5) : Poly :=
  ComputedHornerArithmetic.affine (source d i) w.a (w.b-w.a)
def sourceDegree (d : Data) (w : Witness) : ℕ :=
  Finset.univ.sup (fun i : Fin 5 => max (source d i).length (affineSource d w i).length)

def geometry (d : Data) (w : Witness) : FastPolynomialPaymentCell.Geometry :=
  {U:=affineSource d w 0,V:=affineSource d w 1,J:=affineSource d w 2,
   N:=affineSource d w 3,E:=affineSource d w 4,
   sFloor:=w.sFloor,nFloor:=w.nFloor,eFloor:=w.eFloor,sourceDegree:=sourceDegree d w}

def cell (d : Data) (w : Witness) : PolynomialPaymentCell.Cell :=
  let g := geometry d w
  let pay := ComputedHornerArithmetic.paymentList w.L w.c w.R
  {a:=w.a,b:=w.b,s:=w.s,L:=w.L,pay:=pay,
   primitive:=ComputedHornerArithmetic.primitive pay,c:=w.c,R:=w.R,
   unitIntegral:=ComputedHornerArithmetic.unitIntegral pay,total:=w.total,k:=w.k,n:=w.n,
   comparisonDegree:=(HornerArithmetic.normMargin w.s w.L g.U g.V g.J).length,
   nDegree:=(HornerArithmetic.floorMargin g.N g.nFloor).length,
   eDegree:=(HornerArithmetic.floorMargin g.E g.eFloor).length,
   sCoefficients:=fun _ => 0,lowerCoefficients:=fun _ => 0,
   comparisonCoefficients:=fun _ => 0,nCoefficients:=fun _ => 0,eCoefficients:=fun _ => 0}

def checks (d : Data) (w : Witness) : Bool :=
  let g := geometry d w
  let z := cell d w
  decide (0<w.a ∧ w.a<w.b ∧ 0<w.c ∧ 0<w.sFloor ∧ 0<w.nFloor ∧ 0<w.eFloor ∧
    HornerCertificates.accepts 2 (HornerArithmetic.floorMargin w.s w.sFloor)=true ∧
    HornerCertificates.accepts 4 (HornerArithmetic.floorMargin w.L w.c)=true ∧
    HornerCertificates.accepts z.nDegree (HornerArithmetic.floorMargin g.N g.nFloor)=true ∧
    HornerCertificates.accepts z.eDegree (HornerArithmetic.floorMargin g.E g.eFloor)=true ∧
    HornerCertificates.accepts z.comparisonDegree (HornerArithmetic.normMargin w.s w.L g.U g.V g.J)=true ∧
    RationalLog.accepts w.c w.R w.k w.n=true ∧ w.total≤(w.b-w.a)*z.unitIntegral)

theorem affine_source_checked (d : Data) (w : Witness) (i : Fin 5) :
    HornerCertificates.affineCheck (sourceDegree d w) (source d i) (affineSource d w i)
      w.a (w.b-w.a)=true := by
  apply ComputedHornerArithmetic.affine_check
  have hm : max (source d i).length (affineSource d w i).length≤sourceDegree d w :=
    Finset.le_sup (f := fun j : Fin 5 => max (source d j).length (affineSource d w j).length)
      (Finset.mem_univ i)
  exact ⟨(Nat.le_max_left _ _).trans (hm.trans (Nat.le_succ _)),
    (Nat.le_max_right _ _).trans (hm.trans (Nat.le_succ _))⟩

theorem geometry_checked (d : Data) (w : Witness) (hc : checks d w=true) :
    FastPolynomialPaymentCell.accepts d.U d.V d.J d.N d.E (cell d w) (geometry d w)=true := by
  obtain ⟨ha,hab,hc0,hsF,hnF,heF,hs,hl,hn,he,hp,_hlog,_hbudget⟩ := of_decide_eq_true hc
  rw [FastPolynomialPaymentCell.accepts,decide_eq_true_eq]
  exact ⟨ha,hab,hc0,hsF,hnF,heF,affine_source_checked d w 0,affine_source_checked d w 1,
    affine_source_checked d w 2,affine_source_checked d w 3,affine_source_checked d w 4,
    hs,hl,hn,he,hp⟩

theorem payment_checked (d : Data) (w : Witness) (hc : checks d w=true) :
    PolynomialPaymentCell.paymentAccepts (cell d w)=true := by
  obtain ⟨_ha,_hab,_hc0,_hsF,_hnF,_heF,_hs,_hl,_hn,_he,_hp,_hlog,hbudget⟩ := of_decide_eq_true hc
  rw [PolynomialPaymentCell.paymentAccepts,decide_eq_true_eq]
  exact ⟨ComputedHornerArithmetic.paymentList_sound w.L w.c w.R,hbudget⟩

theorem logarithm_checked (d : Data) (w : Witness) (hc : checks d w=true) :
    RationalLog.accepts w.c w.R w.k w.n=true := by
  obtain ⟨_ha,_hab,_hc0,_hsF,_hnF,_heF,_hs,_hl,_hn,_he,_hp,hlog,_hbudget⟩ := of_decide_eq_true hc
  exact hlog

theorem primitive_checked (d : Data) (w : Witness) :
    RationalPolynomialIntegral.accepts (cell d w).pay (cell d w).primitive 0 1 (cell d w).unitIntegral=true :=
  ComputedHornerArithmetic.primitive_checked (ComputedHornerArithmetic.paymentList w.L w.c w.R)

noncomputable section

theorem actual_integral_lower (x : ℚ) (p q : ℕ) (d : Data)
    (hpath : GeneralPathPolynomials.accepts x p q d.a d.b d.c d.e=true)
    (hpoly : RationalMobiusPolynomials.accepts d.a d.b d.c d.e d.U d.V d.J d.N d.E=true)
    (w : Witness) (hc : checks d w=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (w.total : ℝ)≤∫ y : ℝ in (w.a : ℝ)..(w.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
        (CoreQuotient.fused G u p q) x y := by
  have hdata := of_decide_eq_true hc
  have ha : (0 : ℝ)≤w.a := by exact_mod_cast hdata.1.le
  have hab : (w.a : ℝ)≤w.b := by exact_mod_cast hdata.2.1.le
  have hf := TailIntegral.interval_integrable_of_Ioi
    (ActualFusionIntegral.logarithm_integrable G u p q (x : ℝ)) ha hab
  exact FastPolynomialPaymentCell.actual_integral_lower x p q d.a d.b d.c d.e d.U d.V d.J d.N d.E
    hpath hpoly (cell d w) (geometry d w) (geometry_checked d w hc) (payment_checked d w hc)
    (logarithm_checked d w hc) (primitive_checked d w) G u hd hf

theorem computed_actual_integral (x : ℚ) (p q : ℕ) (w : Witness)
    (hc : checks (ComputedGeneralPathData.build x p q) w=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (w.total : ℝ)≤∫ y : ℝ in (w.a : ℝ)..(w.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
        (CoreQuotient.fused G u p q) x y :=
  actual_integral_lower x p q _ (ComputedGeneralPathData.path_checked x p q)
    (ComputedGeneralPathData.norms_checked x p q) w hc G u hd

theorem computed_actual_integral_swapped (x : ℚ) (p q : ℕ) (w : Witness)
    (hc : checks (ComputedGeneralPathData.build x p q) w=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (w.total : ℝ)≤∫ y : ℝ in (w.a : ℝ)..(w.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u q p)
        (CoreQuotient.fused G u q p) x y :=
  actual_integral_lower x q p _ (ComputedGeneralPathData.path_swapped x p q)
    (ComputedGeneralPathData.norms_checked x p q) w hc G u hd

#print axioms affine_source_checked
#print axioms geometry_checked
#print axioms payment_checked
#print axioms primitive_checked
#print axioms actual_integral_lower
#print axioms computed_actual_integral
#print axioms computed_actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.ComputedPolynomialCell
