/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor393Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor393Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1562959/4398046511104)
  b := (937775/2199023255552)
  s := [(549755813887/549755813888),(-5/4398046511104),(1/2199023255552)]
  L := [(14804919759243424001049985235/10889035741470030830827987437816582766592),(1314937658303/2417851639229258349412352),(65746714631/1208925819614629174706176),(1/37778931862957161709568),(-1/75557863725914323419136)]
  c := (1643676279443/1208925819614629174706176)
  R := (-85386931131053/6250000000000)
  total := (-482178841/500000000000000)
  k := 40
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (1797675485921/604462909807314587353088)
  eFloor := (1141996837919/604462909807314587353088)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1562959,width:=312591,den:=4398046511104,localDen:=10889035741470030830827987437816582766592,lowerC:=14804919759234436109179027456,s:=[10889035741450223790199421353418196779008,-12379400392853802748991242240,4951760157141521099596496896],L:=[14804919759243424001049985235,5921952747948823395631628288,592193759026011874841853952,288230376151711744,-144115188075855872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor393Source.source.poly i) 1562959 312591 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor393Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_checked WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_swapped WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor393Cell025
