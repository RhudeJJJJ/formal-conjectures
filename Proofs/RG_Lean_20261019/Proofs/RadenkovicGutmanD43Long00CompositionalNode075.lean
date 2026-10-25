/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode033
import Proofs.RadenkovicGutmanD43Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1849]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,33282],[0,33282]],[[0,0,0],[0,0,0],[0,0]],[[-149769,0,149769],[0,599076,88752],[149769,88752]],[[0,0,0],[0,0,0],[0,0]],[[-2595996,2695842,798768],[2695842,3195072,81356],[798768,81356]],[[0,0,0],[0,0,0],[0,0]],[[-7937757,21566736,1797228],[21566736,7188912,29584],[1797228,29584]],[[0,0,0],[0,0,0],[0,0]],[[37719600,77280804,2218800],[77280804,8875200,3698],[2218800,3698]],[[0,0,0],[0,0],[0]],[[359488127,163747440,1638214],[163747440,6552856],[1638214]],[[0,0,0],[0,0],[0]],[[1327034696,228148110,739600],[228148110,2958400],[739600]],[[0,0,0],[0,0],[0]],[[3031572326,219927456,199692],[219927456,798768],[199692]],[[0,0,0],[0,0],[0]],[[4827761188,150271928,29584],[150271928,118336],[29584]],[[0,0,0],[0,0],[0]],[[5647237988,73309152,1849],[73309152,7396],[1849]],[[0,0],[0]],[[4985148068,25349790],[25349790]],[[0,0],[0]],[[3367310048,6064720],[6064720]],[[0,0],[0]],[[1749375880,954084],[954084]],[[0,0],[0]],[[697574079,88752],[88752]],[[0,0],[0]],[[211496016,3698],[3698]],[[0]],[[47848422]],[[0]],[[7817572]],[[0]],[[870879]],[[0]],[[59168]],[[0]],[[1849]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
