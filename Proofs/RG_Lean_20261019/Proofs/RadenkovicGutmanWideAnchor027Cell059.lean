/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor027Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor027Cell059
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (375643/2147483648)
  b := (901543/4294967296)
  s := [(4394534856487/4398046511104),(-701497043/2199023255552),(-34844167/1099511627776)]
  L := [(2165554910445906686964647/4951760157141521099596496896),(4722973195823/27021597764222976),(235355924903/13510798882111488),(-19772759/1688849860263936),(-487559/844424930131968)]
  c := (246195089681/562949953421312)
  R := (-386741087068541/100000000000000)
  total := (-66011550151/500000000000000)
  k := 12
  n := 32
  sFloor := (1098248121433/2199023255552)
  nFloor := (937559999301/288230376151711744)
  eFloor := (1712438034913/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=751286,width:=150257,den:=4294967296,localDen:=14855280471424563298789490688,lowerC:=6496664731334750653906944,s:=[14843419156606131987403505664,-4738892732184457214164992,-470772532551706000490496],L:=[6496664731337720060893941,2596481973240881766989824,258776576096823544905728,-173923027469700431872,-8577228635629420544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor027Source.source.poly i) 751286 150257 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor027Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 36) (CoreQuotient.fused G u 9 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 36 WideAnchor027Source.data
    WideAnchor027Source.path_checked WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 9) (CoreQuotient.fused G u 36 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 9 WideAnchor027Source.data
    WideAnchor027Source.path_swapped WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor027Cell059
