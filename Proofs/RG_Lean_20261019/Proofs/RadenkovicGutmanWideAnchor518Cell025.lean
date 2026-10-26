/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor518Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor518Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1562959/4398046511104)
  b := (937775/2199023255552)
  s := [(2199023255545/2199023255552),(-1/2199023255552),(-1/1099511627776)]
  L := [(696582443584086513463618147/680564733841876926926749214863536422912),(5939403941333/14507109835375550096474112),(296969436965/7253554917687775048237056),(19/906694364710971881029632),(-5/453347182355485940514816)]
  c := (618689493933/604462909807314587353088)
  R := (-690193947644273/50000000000000)
  total := (-974448193/1000000000000000)
  k := 40
  n := 32
  sFloor := (1099511627771/2199023255552)
  nFloor := (1130929069037/604462909807314587353088)
  eFloor := (829512433581/302231454903657293676544)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1562959,width:=312591,den:=4398046511104,localDen:=2041694201525630780780247644590609268736,lowerC:=2089747330751024659301400576,s:=[2041694201519131595573999398147388866560,-928455029464035206174343168,-1856910058928070412348686336],L:=[2089747330752259540390854441,835896793030942315169972224,83589465353500000035799040,42784196460019712,-22517998136852480],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor518Source.source.poly i) 1562959 312591 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor518Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_checked WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_swapped WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor518Cell025
