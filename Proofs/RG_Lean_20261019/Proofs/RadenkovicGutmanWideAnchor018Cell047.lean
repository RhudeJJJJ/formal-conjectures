/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor018Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor018Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (674097/34359738368)
  b := (202229/8589934592)
  s := [(4397947788437/4398046511104),(-39487653/4398046511104),(-1974017/2199023255552)]
  L := [(4788036069341/288230376151711744),(5745493494227/864691128455135232),(287247274837/432345564227567616),(-663653/54043195528445952),(-16585/27021597764222976)]
  c := (1197009017335/72057594037927936)
  R := (-110053950356019/20000000000000)
  total := (-2122343353/100000000000000)
  k := 16
  n := 32
  sFloor := (2198952176375/4398046511104)
  nFloor := (814529828461/18446744073709551616)
  eFloor := (550327564037/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=674097,width:=134819,den:=34359738368,localDen:=864691128455135232,lowerC:=14364108208020,s:=[864671718789021696,-7763588481024,-776215068672],L:=[14364108208023,5745493494227,574494549674,-10618448,-530720],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor018Source.source.poly i) 674097 134819 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor018Source.source witness geometry=true := by
  unfold IntegerPolynomialPaymentCell.checks
  rw [decide_eq_true_eq]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by intro i; rfl,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem budget : SemanticPolynomialPaymentCell.Budget witness := by
  unfold SemanticPolynomialPaymentCell.Budget
  decide +kernel
theorem logarithm_checked : RationalLog.accepts witness.c witness.R witness.k witness.n=true := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 27) (CoreQuotient.fused G u 9 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 27 WideAnchor018Source.data
    WideAnchor018Source.path_checked WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 9) (CoreQuotient.fused G u 27 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 9 WideAnchor018Source.data
    WideAnchor018Source.path_swapped WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor018Cell047
