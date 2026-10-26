/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor518Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor518Cell101
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1552785/4194304)
  b := (931671/2097152)
  s := [(2671825292479/8796093022208),(-275283080331/4398046511104),(41148863319/4398046511104)]
  L := [(97416318483615846851/147573952589676412928),(830756899207/6597069766656),(-25059463069/1649267441664),(165960073/206158430208),(2121241/25769803776)]
  c := (1451616264635/2199023255552)
  R := (-2595848038183/12500000000000)
  total := (-384063461933/31250000000000)
  k := 1
  n := 32
  sFloor := (1101778429227/8796093022208)
  nFloor := (606980171599/17179869184)
  eFloor := (982091486729/34359738368)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1552785,width:=310557,den:=4194304,localDen:=442721857769029238784,lowerC:=292248955450734673920,s:=[134477370138550075392,-27710902199151230976,4142180208344039424],L:=[292248955450847540553,55751151765944270848,-6726848396042174464,356396542988386304,36442642887737344],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor518Source.source.poly i) 1552785 310557 4194304
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
end Gebendorfer.RadenkovicGutman.WideAnchor518Cell101
