/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor244Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor244Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (624031/4194304)
  b := (748837/4194304)
  s := [(4737449767945/8796093022208),(-318553136063/8796093022208),(11611370587/4398046511104)]
  L := [(239336639034646246397/590295810358705651712),(3191541325601/52776558133248),(-69913913695/26388279066624),(1343336875/3298534883328),(-87744857/1649267441664)]
  c := (445799229731/1099511627776)
  R := (-5642204327103/12500000000000)
  total := (-99194319991/8000000000000)
  k := 2
  n := 32
  sFloor := (17352028801/68719476736)
  nFloor := (583887162261/34359738368)
  eFloor := (431875726211/34359738368)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=624031,width:=124806,den:=4194304,localDen:=1770887431076116955136,lowerC:=718009917103738454016,s:=[953774616551557693440,-64133217254476087296,4675355337459499008],L:=[718009917103938739191,107090356385068613632,-4691843325865492480,721198493204480000,-94215322801799168],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor244Source.source.poly i) 624031 124806 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor244Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 26) (CoreQuotient.fused G u 0 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 26 WideAnchor244Source.data
    WideAnchor244Source.path_checked WideAnchor244Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor244Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 0) (CoreQuotient.fused G u 26 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 0 WideAnchor244Source.data
    WideAnchor244Source.path_swapped WideAnchor244Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor244Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor244Cell096
