/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor508Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor508Cell059
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (375643/2147483648)
  b := (901543/4294967296)
  s := [(4397931048679/4398046511104),(-23090877/2199023255552),(-1154105/1099511627776)]
  L := [(48458448555725366474216158583/5192296858534827628530496329220096),(3227805075629/864691128455135232),(161355691735/432345564227567616),(-429295/27021597764222976),(-21445/27021597764222976)]
  c := (84062008319/9007199254740992)
  R := (-2262105471083/390625000000)
  total := (-99657765479/500000000000000)
  k := 17
  n := 32
  sFloor := (549735031313/1099511627776)
  nFloor := (69993956703/36028797018963968)
  eFloor := (196896098065/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=751286,width:=150257,den:=4294967296,localDen:=15576890575604482885591488987660288,lowerC:=145375345667122150981307990016,s:=[15576481633690094747945041750130688,-163565375407298376994639577088,-16350320309136815668057866240],L:=[145375345667176099422648475749,58146966943309440238732967936,5813451465374836969680404480,-247471718660098186280960,-12362200833146916700160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor508Source.source.poly i) 751286 150257 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor508Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 38) (CoreQuotient.fused G u 4 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 38 WideAnchor508Source.data
    WideAnchor508Source.path_checked WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 4) (CoreQuotient.fused G u 38 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 4 WideAnchor508Source.data
    WideAnchor508Source.path_swapped WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor508Cell059
