/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor256Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor256Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(1804039708069/18014398509481984),(-513996706607/9007199254740992),(271312010739/18014398509481984)]
  L := [(148552450861464223817/147573952589676412928),(-34131361163/13194139533312),(1647982641/2199023255552),(-148175059/824633720832),(3779147/137438953472)]
  c := (276153596417/274877906944)
  R := (46301953493/20000000000000)
  total := (4710948490377/500000000000000)
  k := 0
  n := 32
  sFloor := (523679152797/18014398509481984)
  nFloor := 33425409006503480612994495587144441955569773136971170493120506406765662866321259024714039296
  eFloor := 33198588878682274828527515394707260228990991168208130559750314836500243271709198661791514624
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=442721857769029238784,lowerC:=444776499481424166912,s:=[44336079865503744,-25263966123147264,6667763975921664],L:=[445657352584392671451,-1145258437211324416,331782728787689472,-79550879060983808,12173484578832384],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor256Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor256Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 33) (CoreQuotient.fused G u 0 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 33 WideAnchor256Source.data
    WideAnchor256Source.path_checked WideAnchor256Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor256Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 0) (CoreQuotient.fused G u 33 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 0 WideAnchor256Source.data
    WideAnchor256Source.path_swapped WideAnchor256Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor256Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor256Cell122
