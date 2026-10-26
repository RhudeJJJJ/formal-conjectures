/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor540Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor540Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1118005/2097152)
  b := (670803/1048576)
  s := [(6339931414641/35184372088832),(-214043385847/8796093022208),(4843971947/4398046511104)]
  L := [(34844851429729869391/36893488147419103232),(905281635221/13194139533312),(-31374635221/6597069766656),(-493764479/824633720832),(58930033/412316860416)]
  c := (259614373965/274877906944)
  R := (-1428241784239/50000000000000)
  total := (-622974000839/500000000000000)
  k := 1
  n := 32
  sFloor := (1380627411707/17592186044416)
  nFloor := (1092943493849/1048576)
  eFloor := (1607675996913/2097152)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1118005,width:=223601,den:=2097152,localDen:=110680464442257309696,lowerC:=104534554289173954560,s:=[19943699769115803648,-2693289088294846464,121902545479139328],L:=[104534554289189608173,7594052767467962368,-526379032023924736,-66271946538483712,15818910280450048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor540Source.source.poly i) 1118005 223601 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor540Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 18) (CoreQuotient.fused G u 5 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 18 WideAnchor540Source.data
    WideAnchor540Source.path_checked WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 5) (CoreQuotient.fused G u 18 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 5 WideAnchor540Source.data
    WideAnchor540Source.path_swapped WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor540Cell103
