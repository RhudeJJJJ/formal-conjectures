/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor028Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor028Cell069
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (581469/536870912)
  b := (1395525/1073741824)
  s := [(4020721302045/4398046511104),(-264276260185/8796093022208),(-5158842535/4398046511104)]
  L := [(627555716665424212417/9444732965739290427392),(5114057455871/211106232532992),(55685392547/35184372088832),(-1759546793/13194139533312),(3710049/2199023255552)]
  c := (1168913611519/17592186044416)
  R := (-16946125302627/12500000000000)
  total := (-137673652903/500000000000000)
  k := 4
  n := 32
  sFloor := (485428041177/1099511627776)
  nFloor := (190394392571/1125899906842624)
  eFloor := (2006683377/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1162938,width:=232587,den:=1073741824,localDen:=28334198897217871282176,lowerC:=1882667149996257705984,s:=[25903299747920719380480,-851293420952821432320,-33235589959558103040],L:=[1882667149996272637251,686397172588465881088,44843801222678839296,-3778597965858340864,47803617364672512],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor028Source.source.poly i) 1162938 232587 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor028Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 37) (CoreQuotient.fused G u 9 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 37 WideAnchor028Source.data
    WideAnchor028Source.path_checked WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 9) (CoreQuotient.fused G u 37 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 9 WideAnchor028Source.data
    WideAnchor028Source.path_swapped WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor028Cell069
