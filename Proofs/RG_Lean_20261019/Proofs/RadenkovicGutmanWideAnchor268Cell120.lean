/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor268Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor268Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (775127/65536)
  b := (116269/8192)
  s := [(2663505473515/9007199254740992),(-3015309377787/18014398509481984),(395692504345/9007199254740992)]
  L := [(299112130449546402071/295147905179352825856),(-1415432369/274877906944),(2408529683/1649267441664),(-11763857/34359738368),(5305453/103079215104)]
  c := (1109903622769/1099511627776)
  R := (117588484389/25000000000000)
  total := (13252083292059/1000000000000000)
  k := 0
  n := 32
  sFloor := (775771644483/9007199254740992)
  nFloor := 39223506297027107156505485959259325449321239150855047144681471475764085338013177038899876723623335034880
  eFloor := 38680780289801164870113676717110031033125755410453616965920286980510116478326342889801204518985901539328
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=775127,width:=155025,den:=65536,localDen:=885443715538058477568,lowerC:=893812455282145492992,s:=[261833242068418560,-148208486536986624,38898155947130880],L:=[897336391348639206213,-4559426800916103168,1293069527491280896,-303152286538924032,45573494250930176],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor268Source.source.poly i) 775127 155025 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor268Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 44) (CoreQuotient.fused G u 0 44) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 44 WideAnchor268Source.data
    WideAnchor268Source.path_checked WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 44 0) (CoreQuotient.fused G u 44 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 44 0 WideAnchor268Source.data
    WideAnchor268Source.path_swapped WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor268Cell120
