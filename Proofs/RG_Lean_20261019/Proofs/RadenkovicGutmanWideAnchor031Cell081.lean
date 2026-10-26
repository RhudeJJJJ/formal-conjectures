/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor031Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor031Cell081
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (162013/16777216)
  b := (388831/33554432)
  s := [(2183625089203/2199023255552),(-12209213431/4398046511104),(-580641183/2199023255552)]
  L := [(426741432871340896639191/154742504910672534362390528),(7438682854393/6755399441055744),(123093722691/1125899906842624),(-67012159/422212465065984),(-599047/70368744177664)]
  c := (1552476288893/562949953421312)
  R := (-294666973482733/100000000000000)
  total := (-5510351674301/1000000000000000)
  k := 9
  n := 32
  sFloor := (272117480163/549755813888)
  nFloor := (481420786939/140737488355328)
  eFloor := (1226682099145/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=324026,width:=64805,den:=33554432,localDen:=464227514732017603087171584,lowerC:=1280224298613289544318976,s:=[460976865846163916640485376,-1288720524804807538507776,-122576972596629561409536],L:=[1280224298614022689917573,511182393358941838901248,50753617276870858899456,-73680648022874128384,-3951954852505976832],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor031Source.source.poly i) 324026 64805 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor031Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 10) (CoreQuotient.fused G u 10 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 10 WideAnchor031Source.data
    WideAnchor031Source.path_checked WideAnchor031Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor031Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 10) (CoreQuotient.fused G u 10 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 10 WideAnchor031Source.data
    WideAnchor031Source.path_swapped WideAnchor031Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor031Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor031Cell081
