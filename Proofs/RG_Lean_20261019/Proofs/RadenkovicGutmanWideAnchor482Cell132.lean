/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor482Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor482Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (863885/8192)
  b := (518331/4096)
  s := [(1965476241735/4611686018427387904),(-4507343039949/18446744073709551616),(597838206611/9223372036854775808)]
  L := [(37785691586617565548807/37778931862957161709568),(-313833653/4398046511104),(139814327/6597069766656),(-1431697/274877906944),(334741/412316860416)]
  c := (4295501451/4294967296)
  R := (1554498993/25000000000000)
  total := (393248813273/250000000000000)
  k := 0
  n := 32
  sFloor := (1137559585053/9223372036854775808)
  nFloor := 1679696246843907793689538138273799665212792810624218540165219444923251150343372800
  eFloor := 1679394322521962934743312528651948359958726693661724915306985330307414354275860480
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=863885,width:=172777,den:=8192,localDen:=113336795588871485128704,lowerC:=113350891020076317671424,s:=[48303544116879360,-27693115637446656,7346235882835968],L:=[113357074759852696646421,-8087431656115273728,2401991847908999168,-590312812107005952,92012905448341504],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor482Source.source.poly i) 863885 172777 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor482Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 12) (CoreQuotient.fused G u 4 12) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 12 WideAnchor482Source.data
    WideAnchor482Source.path_checked WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 4) (CoreQuotient.fused G u 12 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 12 4 WideAnchor482Source.data
    WideAnchor482Source.path_swapped WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor482Cell132
