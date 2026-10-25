/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor370Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor370Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (584323/17592186044416)
  b := (1402375/35184372088832)
  s := [(4398046511103/4398046511104)]
  L := [(57537680905772958134401761/2722258935367507707706996859454145691648),(7849525673695/928455029464035206174343168),(392475947695/464227514732017603087171584),(29/58028439341502200385896448),(-7/29014219670751100192948224)]
  c := (1635319248003/77371252455336267181195264)
  R := (-1574389918411031/100000000000000)
  total := (-10396371/100000000000000)
  k := 46
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (28806276299/1208925819614629174706176)
  eFloor := (1265761417105/38685626227668133590597632)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1168646,width:=233729,den:=35184372088832,localDen:=8166776806102523123120990578362437074944,lowerC:=172613042717299465663807488,s:=[8166776806100666213062062507950088388608],L:=[172613042717318874403205283,69045158006031139796418560,6904509889808922962821120,4081387162304512,-1970324836974592],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor370Source.source.poly i) 1168646 233729 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor370Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 10) (CoreQuotient.fused G u 2 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 10 WideAnchor370Source.data
    WideAnchor370Source.path_checked WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 2) (CoreQuotient.fused G u 10 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 2 WideAnchor370Source.data
    WideAnchor370Source.path_swapped WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor370Cell012
