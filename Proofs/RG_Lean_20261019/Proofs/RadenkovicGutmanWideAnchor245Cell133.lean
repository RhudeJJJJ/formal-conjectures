/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor245Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor245Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (518331/4096)
  b := 128
  s := [(4550556842977/18446744073709551616),(-156840209079/18446744073709551616),(1751850149/9223372036854775808)]
  L := [(1238094011912615032947456723/1237940039285380274899124224),(-1568301/549755813888),(53955/1099511627776),(-13/17179869184),(1/68719476736)]
  c := (1099645299477/1099511627776)
  R := (6078315717/100000000000000)
  total := (44706713093/500000000000000)
  k := 0
  n := 32
  sFloor := (1099305083549/9223372036854775808)
  nFloor := 43857008076224628415555401126011778495619020538550008945512346470548731718559275550493503947405125756386828231264388107048664956928
  eFloor := 43851532268210249729282354085733527041830374621159486038800605443423583004905822002874356834209798295792414160357925080604428206080
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=518331,width:=5957,den:=4096,localDen:=1237940039285380274899124224,lowerC:=1238090540241083669988507648,s:=[305382700299612848128,-10525368260814176256,235129346795241472],L:=[1238094011912615032947456723,-3531499899602388123648,60747929473693777920,-936748722493063168,18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor245Source.source.poly i) 518331 5957 4096
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
end Gebendorfer.RadenkovicGutman.WideAnchor245Cell133
