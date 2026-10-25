/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor251Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor251Cell106
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241489/262144)
  b := (1159147/1048576)
  s := [(5267920446437/35184372088832),(-25307236615/549755813888),(33696822571/4398046511104)]
  L := [(167218527503446176515/147573952589676412928),(947999698447/13194139533312),(-152290927813/6597069766656),(3160923161/824633720832),(-155396579/412316860416)]
  c := (1245875116463/1099511627776)
  R := (3124302032877/50000000000000)
  total := (13841723401719/1000000000000000)
  k := 0
  n := 32
  sFloor := (979457970911/17592186044416)
  nFloor := (1098911243299/4294967296)
  eFloor := (1434448037991/8589934592)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=965956,width:=193191,den:=1048576,localDen:=442721857769029238784,lowerC:=501655582510197768192,s:=[66285779400517484544,-20380078802542264320,3392033224724054016],L:=[501655582510338529545,31809591417560367104,-10220071163036434432,1697007700207992832,-166855806178820096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor251Source.source.poly i) 965956 193191 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor251Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 2 WideAnchor251Source.data
    WideAnchor251Source.path_checked WideAnchor251Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor251Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 0 WideAnchor251Source.data
    WideAnchor251Source.path_swapped WideAnchor251Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor251Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor251Cell106
