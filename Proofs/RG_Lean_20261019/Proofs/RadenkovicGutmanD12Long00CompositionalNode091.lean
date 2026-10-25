/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,432],[0,432]],[[0,0,0],[0,0,0],[0,0]],[[0,3888,6480],[3888,20736,1944],[6480,1944]],[[0,0,0],[0,0,0],[0,0]],[[69984,241704,50328],[241704,156384,2616],[50328,2616]],[[0,0,0],[0,0,0],[0,0]],[[2437776,2278368,156024],[2278368,471456,1392],[156024,1392]],[[0,0,0],[0,0,0],[0,0]],[[25279776,9914112,253440],[9914112,749952,312],[253440,312]],[[0,0,0],[0,0,0],[0,0]],[[135800064,25208880,237624],[25208880,694752,24],[237624,24]],[[0,0,0],[0,0],[0]],[[455257152,41449680,133200],[41449680,388800],[133200]],[[0,0,0],[0,0],[0]],[[1043183376,46438848,44520],[46438848,131424],[44520]],[[0,0,0],[0,0],[0]],[[1721065728,36442176,8448],[36442176,25728],[8448]],[[0,0,0],[0,0],[0]],[[2110718688,20265768,792],[20265768,2592],[792]],[[0,0,0],[0,0],[0]],[[1962799536,7975656,24],[7975656,96],[24]],[[0,0],[0]],[[1400094096,2187384],[2187384]],[[0,0],[0]],[[770000400,403776],[403776]],[[0,0],[0]],[[326260032,46872],[46872]],[[0,0],[0]],[[105781152,2976],[2976]],[[0,0],[0]],[[25872240,72],[72]],[[0]],[[4657824]],[[0]],[[592608]],[[0]],[[49680]],[[0]],[[2400]],[[0]],[[48]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
