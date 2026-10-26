/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor518Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor518Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1006419/17179869184)
  b := (603851/8589934592)
  s := [(4398046152221/4398046511104),(-35889/1099511627776),(-897/274877906944)]
  L := [(147878478857913498541763877475/5316911983139663491615228241121378304),(2462661627943/221360928884514619392),(20522099829/18446744073709551616),(167/13835058055282163712),(1/1152921504606846976)]
  c := (513056537733/18446744073709551616)
  R := (-217472095872327/25000000000000)
  total := (-100819787119/1000000000000000)
  k := 26
  n := 32
  sFloor := (549755749289/1099511627776)
  nFloor := (468919093477/9223372036854775808)
  eFloor := (343942164703/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1006419,width:=201283,den:=17179869184,localDen:=15950735949418990474845684723364134912,lowerC:=443635436573632439154225709056,s:=[15950734647830215712574798405134450688,-520645664881793117412359405568,-52051510089327473746149113856],L:=[443635436573740495625291632425,177453471839099421756277915648,17745277659406947778799075328,192537891269343444992,13835058055282163712],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor518Source.source.poly i) 1006419 201283 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor518Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_checked WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_swapped WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor518Cell053
