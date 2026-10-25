/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor245Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor245Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (775127/65536)
  b := (116269/8192)
  s := [(2663505473515/9007199254740992),(-3015309377787/18014398509481984),(395692504345/9007199254740992)]
  L := [(299112130252186716765/295147905179352825856),(-1415432369/274877906944),(2408529683/1649267441664),(-11763857/34359738368),(5305453/103079215104)]
  c := (554951811017/549755813888)
  R := (94070780889/20000000000000)
  total := (13252082509991/1000000000000000)
  k := 0
  n := 32
  sFloor := (775771644483/9007199254740992)
  nFloor := 10248760512379990568800016510598151342330444801864673642941606002688
  eFloor := 10106950934473225339796387143292410152654697744138345352937504505856
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=775127,width:=155025,den:=65536,localDen:=885443715538058477568,lowerC:=893812454690245312512,s:=[261833242068418560,-148208486536986624,38898155947130880],L:=[897336390756560150295,-4559426800916103168,1293069527491280896,-303152286538924032,45573494250930176],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor245Source.source.poly i) 775127 155025 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor245Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 27) (CoreQuotient.fused G u 0 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 27 WideAnchor245Source.data
    WideAnchor245Source.path_checked WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 0) (CoreQuotient.fused G u 27 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 0 WideAnchor245Source.data
    WideAnchor245Source.path_swapped WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor245Cell120
