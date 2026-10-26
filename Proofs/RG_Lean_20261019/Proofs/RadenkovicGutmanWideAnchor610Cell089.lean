/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor610Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor610Cell089
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (43539/1048576)
  b := (1671897/33554432)
  s := [(4064752085399/4398046511104),(-120556646159/4398046511104),(-776717685/549755813888)]
  L := [(757735381324687976027/37778931862957161709568),(7056833973265/844424930131968),(132825610643/140737488355328),(671235389/52776558133248),(-14336527/8796093022208)]
  c := (1411392132425/70368744177664)
  R := (-195458632228277/100000000000000)
  total := (-15418981687859/1000000000000000)
  k := 6
  n := 32
  sFloor := (123061928055/274877906944)
  nFloor := (568007706787/17592186044416)
  eFloor := (278830565803/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1393248,width:=278649,den:=33554432,localDen:=113336795588871485128704,lowerC:=2273206143973903564800,s:=[104747863638819024666624,-3106721115410094096384,-160126898654391828480],L:=[2273206143974063928081,947152222764841041920,106965310084296474624,1441467021836419072,-184724743809662976],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor610Source.source.poly i) 1393248 278649 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor610Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 8) (CoreQuotient.fused G u 6 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 6 8 WideAnchor610Source.data
    WideAnchor610Source.path_checked WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 6) (CoreQuotient.fused G u 8 6) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 6 WideAnchor610Source.data
    WideAnchor610Source.path_swapped WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor610Cell089
