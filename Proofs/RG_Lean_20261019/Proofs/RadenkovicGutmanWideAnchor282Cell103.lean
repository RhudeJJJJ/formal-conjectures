/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor282Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor282Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1118005/2097152)
  b := (670803/1048576)
  s := [(2353537323105/8796093022208),(-883763872509/17592186044416),(48188444609/8796093022208)]
  L := [(283932905323816275839/295147905179352825856),(348328363039/3298534883328),(-49180881731/3298534883328),(243751553/206158430208),(-16996993/206158430208)]
  c := (2115464995233/2199023255552)
  R := (-1936932139681/100000000000000)
  total := (51796784361/100000000000000)
  k := 1
  n := 32
  sFloor := (1959843831459/17592186044416)
  nFloor := (504746098633/1073741824)
  eFloor := (1212703492939/4294967296)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1118005,width:=223601,den:=2097152,localDen:=885443715538058477568,lowerC:=851798715971112271872,s:=[236914824202766254080,-44481292146239864832,4850807663455371264],L:=[851798715971448827517,93503682970107510784,-13201892413943054336,1046904948484210688,-73001529065340928],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor282Source.source.poly i) 1118005 223601 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor282Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 8 WideAnchor282Source.data
    WideAnchor282Source.path_checked WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 0 WideAnchor282Source.data
    WideAnchor282Source.path_swapped WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor282Cell103
