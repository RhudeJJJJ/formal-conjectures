/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor023Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor023Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(2177581263633/2199023255552),(-8448159521/4398046511104),(-196502339/2199023255552)]
  L := [(102345153294078365970421/19342813113834066795298816),(589586280217/562949953421312),(42400109801/844424930131968),(-7390793/35184372088832),(-237041/52776558133248)]
  c := (1489317994769/281474976710656)
  R := (-262086262870477/100000000000000)
  total := (-5411216367/31250000000000)
  k := 8
  n := 32
  sFloor := (2173160681533/4398046511104)
  nFloor := (393368310171/9007199254740992)
  eFloor := (728466432263/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=58028439341502200385896448,lowerC:=307035459882103395581952,s:=[57462622074999331715284992,-111466195519752269463552,-5185358558776352833536],L:=[307035459882235097911263,60774091000855362797568,2913713359073665089536,-12189394262978199552,-260629335759650816],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor023Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor023Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 32) (CoreQuotient.fused G u 9 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 32 SymbolicAnchor023Source.data
    SymbolicAnchor023Source.path_checked SymbolicAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor023Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 9) (CoreQuotient.fused G u 32 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 9 SymbolicAnchor023Source.data
    SymbolicAnchor023Source.path_swapped SymbolicAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor023Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor023Cell127
