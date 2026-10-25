/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor254Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor254Cell002
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1509949/281474976710656)
  b := (905969/140737488355328)
  s := [(4398046511103/4398046511104)]
  L := [(128082586171913306931541683/5444517870735015415413993718908291383296),(1456126561487/154742504910672534362390528),(72806135183/77371252455336267181195264),(1/2417851639229258349412352),(-1/4835703278458516698824704)]
  c := (455040755909/19342813113834066795298816)
  R := (-1569035517086157/100000000000000)
  total := (-130729/7812500000000)
  k := 46
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1376722824163/618970019642690137449562112)
  eFloor := (1240360443177/618970019642690137449562112)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1509949,width:=301989,den:=281474976710656,localDen:=5444517870735015415413993718908291383296,lowerC:=128082586171885076615266304,s:=[5444517870733777475374708338633392259072],L:=[128082586171913306931541683,51232898747790115874013184,5123276301256949353152512,2251799813685248,-1125899906842624],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor254Source.source.poly i) 1509949 301989 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor254Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 31) (CoreQuotient.fused G u 0 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 31 WideAnchor254Source.data
    WideAnchor254Source.path_checked WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 0) (CoreQuotient.fused G u 31 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 0 WideAnchor254Source.data
    WideAnchor254Source.path_swapped WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor254Cell002
