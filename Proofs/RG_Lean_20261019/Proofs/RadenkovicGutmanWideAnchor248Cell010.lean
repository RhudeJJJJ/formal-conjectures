/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor248Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor248Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1623121/70368744177664)
  b := (60867/2199023255552)
  s := [(4398046511103/4398046511104)]
  L := [(211309091630332593698716973/43556142965880123323311949751266331066368),(1201148680305/618970019642690137449562112),(180171636013/928455029464035206174343168),(1/38685626227668133590597632),(-1/58028439341502200385896448)]
  c := (1501441400579/309485009821345068724781056)
  R := (-82398762982301/5000000000000)
  total := (-75591503/1000000000000000)
  k := 48
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (893156857723/77371252455336267181195264)
  eFloor := (913353969107/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1623121,width:=324623,den:=70368744177664,localDen:=130668428897640369969935849253798993199104,lowerC:=633927274890583126610804736,s:=[130668428897610659408993000127201414217728],L:=[633927274890997781096150919,253569972611163798173122560,25356903525339982425227264,3377699720527872,-2251799813685248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor248Source.source.poly i) 1623121 324623 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor248Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 0 2 WideAnchor248Source.data
    WideAnchor248Source.path_checked WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 0 WideAnchor248Source.data
    WideAnchor248Source.path_swapped WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor248Cell010
